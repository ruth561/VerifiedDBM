// #![feature(proc_macro_hygiene)]
// #![feature(stmt_expr_attributes)]

mod dbm;
mod down;

// use ::std::ops::Add;
// use ::std::option::Option;
// use ::std::clone::Clone;
// use ::std::marker::Copy;
// use ::std::cmp::Ordering;
// use ::std::cmp::Ord;
// use ::std::cmp::PartialOrd;

use creusot_contracts::*;
use textplots::{Chart, Plot, Shape};

use crate::dbm::*;

const BOUND: i64 = 100000;    // 各制約の値はこの値を超えることはない。
const INF: i64 = i64::MAX;          // 無限を表す値
const MAX_NODE: usize = 100000;

const xidx: usize = 1;
const yidx: usize = 2;

#[trusted] // trustedをつけるとビルドエラーがでなくなる
fn print_dbm(dbm: &Vec<Vec<i64>>) {
    println!("=== print_dbm ===");
    for row in dbm {
        print!("[ ");
        for elem in row {
            if *elem == INF {
                print!("INF, ");
            } else {
                print!("{:3}, ", elem);
            }
        }
        println!("]");
    }
}

// 
// 3変数のケースのみに対応
// x, y in [-1.0, 6.0]の範囲の領域を図示する
#[trusted]
#[requires(dbm@.len() == 3)]
#[requires(is_canonical(dbm.deep_model(), dbm@.len()))]
fn print_clock_region(dbm: &Vec<Vec<i64>>) {
    let n = dbm.len();

    let mut data = Vec::new();
    for x in -10..60 {
        for y in -10..60 {
            if 0 - x <= dbm[0][xidx] &&
               0 - y <= dbm[0][yidx] &&
               x - 0 <= dbm[xidx][0] &&
               y - 0 <= dbm[yidx][0] &&
               x - y <= dbm[xidx][yidx] &&
               y - x <= dbm[yidx][xidx] {
                data.push((x as f32, y as f32));
            }
        }
    }

    println!("\n============== CLOCK REGION ==============\n");
    Chart::new_with_y_range(70, 70, -10.0, 60.0, -10.0, 60.0)
        .lineplot(&Shape::Points(&data))
        .display();
}

#[trusted]
fn main() {
    let mut dbm = get_dbm();
    let n = dbm.len();
    print_dbm(&dbm);
    println!("This is DBM ? {}", check_is_dbm(&dbm));
    println!("This is canonical form DBM ? {}", check_is_canonical(&dbm));

    if check_is_canonical(&dbm) {
        print_clock_region(&dbm);
    }

    let mut rl = rustyline::DefaultEditor::new().unwrap();
    while true {
        print_dbm(&dbm);
        print_clock_region(&dbm);
        println!("");
        println!(" 1. up");
        println!(" 2. down");
        println!(" 3. free");
        println!(" 4. reset");
        println!(" q. exit");
        println!("");
        match rl.readline("> ") {
            Ok(s) => {
                if &s == "1" {
                    println!("[*] UP");
                    up(&mut dbm, n);
                } else if &s == "2" {
                    println!("[*] DOWN");
                    down::down(&mut dbm, n);
                } else if &s == "3 x" {
                    println!("[*] FREE x");
                    free(&mut dbm, n, xidx);
                } else if &s == "3 y" {
                    println!("[*] FREE y");
                    free(&mut dbm, n, yidx);
                } else if &s[0..3] == "4 x" {
                    if let Ok(m) = i64::from_str_radix(&s[4..], 10) {
                        println!("[*] RESET x {m}");
                        reset(&mut dbm, n, xidx, m);
                    } else {
                        println!("failed to parse int.");
                    }
                } else if &s[0..3] == "4 y" {
                    if let Ok(m) = i64::from_str_radix(&s[4..], 10) {
                        println!("[*] RESET y {m}");
                        reset(&mut dbm, n, yidx, m);
                    } else {
                        println!("failed to parse int.");
                    }
                } else if &s == "q" {
                    println!("Exit..");
                    break;
                } else {
                    println!("Invalid input: {s}");
                }
            },
            Err(_) => println!("No input"),
        }

    }
}

// [[  0, ---, ... , ---],
//  [INF,   0, ... , ---],
//  [INF, ---, ... , ---],
//  ...
//  [INF, ---, ... ,   0]]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(is_canonical(d.deep_model(), n@))]
#[ensures(forall<i:Int> 1 <= i && i < n@ ==> (^d).deep_model()[i][0] == INF@)]
#[ensures(d.deep_model()[0][0] == (^d).deep_model()[0][0])]
#[ensures(forall<i:Int, j:Int> 0 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == (^d).deep_model()[i][j])]
#[ensures(is_canonical((^d).deep_model(), n@))]
fn up(d: &mut Vec<Vec<i64>>, n: usize) {
    let d_old = snapshot! { d };
    #[invariant(is_dbm(d.deep_model(), n@))]    
    #[invariant(forall<i:Int> 1 <= i && i < 1 + produced.len() ==> d.deep_model()[i][0] == INF@)]
    #[invariant(d.deep_model()[0][0] == d_old.deep_model()[0][0])]
    #[invariant(forall<i:Int, j:Int> 0 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j])]
    for x in 1..n {
        proof_assert! { forall<i:Int, j:Int> 0 <= i && i < n@ && 1 <= j && j < n@ ==> (x@, 0) != (i, j) };
        d[x][0] = INF;
    }
}

// Seqの最小値を返す関数
// min{ v[l], v[l+1], ... , v[u-1] }
//
// ！！！ensures節できちんと数学的な性質も証明しているので安心！！！
#[logic]
#[variant(u - l)]
#[requires(0 <= l && l < u && u <= s.len())] // この条件から「少なくとも1つの要素は持っている」が言える
#[ensures(forall<i:Int> l <= i && i < u ==> result <= s[i])]
#[ensures(exists<i:Int> l <= i && i < u &&  result == s[i])]
fn min_seq_int(s: Seq<Int>, l: Int, u: Int) -> Int {
    pearlite! {
        if l+1 == u { // 要素数がちょうど1のとき
            s[l]
        } else { // 要素数が2以上のとき
            s[u-1].min(min_seq_int(s, l, u-1))
        }
    }
}

#[logic]
#[requires(0 < s.len())]
#[ensures(forall<i:Int> 0 <= i && i < s.len() ==> result <= s[i])]
#[ensures(exists<i:Int> 0 <= i && i < s.len() &&  result == s[i])]
fn min_seq(s: Seq<Int>) -> Int {
    pearlite! { min_seq_int(s, 0, s.len()) }
}

// ベクトルvの最小値を返す関数
// つまり min{ v[0], v[1], ... , v[n-1] } を返す関数
#[requires(0 < v@.len())]
#[ensures(result@ == min_seq(v.deep_model()))]
fn min_vec(v: &Vec<i64>, x: i64) -> i64 {
    let mut ans = v[0];
    #[invariant(ans@ == min_seq_int(v.deep_model(), 0, 1+produced.len()))]
    for i in 1..v.len() {
        if v[i] < ans {
            ans = v[i];
        }
    }
    ans
}

// x==2 のケース
// [[  d00, ---,   d00, ... , ---],
//  [  d10, ---,   d10, ... , ---],
//  [  INF, INF,     0, ... , INF],
//  ...
//  [dn-10, ---, dn-10, ... , ---]]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(1 <= x@ && x@ < n@)] // ゼロを書き換えるような使い方はしない
#[requires(is_canonical(d.deep_model(), n@))]
#[ensures(forall<i:Int, j:Int> // x行にもx列にもない場所は変化しない
    0 <= i && i < n@ && i != x@ &&
    0 <= j && j < n@ && j != x@ ==>
    (^d).deep_model()[i][j] == d.deep_model()[i][j]
)]
#[ensures(forall<i:Int> // x列とx行の変化
    0 <= i && i < n@ && i != x@ ==>
    (^d).deep_model()[x@][i] == INF@ && (^d).deep_model()[i][x@] == d.deep_model()[i][0])]
#[ensures((^d).deep_model()[x@][x@] == d.deep_model()[x@][x@])]
#[ensures(is_canonical((^d).deep_model(), n@))]
fn free(d: &mut Vec<Vec<i64>>, n: usize, x: usize) {
    let d_old = snapshot! { d };

    // コメントアウトしている部分は `is_dbm` の中身を展開したもの。
    // 展開しなくても頑張れば証明が通るが（時間かかる）、is_dbmを展開したほうが証明が少し早く完了するかも？
    #[invariant(is_dbm(d.deep_model(), n@))]
    // #[invariant((2 <= n@))]
    // #[invariant(d@.len() == n@)]
    // #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i].len() == n@)]
    // #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][i] == 0)]
    // #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[0][i] <= 0)]
    // #[invariant(forall<i:Int> 0 <= i && i < n@ ==> 0 <= d.deep_model()[i][0])]
    // #[invariant(forall<i:Int, j:Int>
    //     0 <= i && i < n@ &&
    //     0 <= j && j < n@ ==>
    //     (-BOUND@ < d.deep_model()[i][j] && d.deep_model()[i][j] < BOUND@) || d.deep_model()[i][j] == INF@)]
    #[invariant(forall<i:Int, j:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= j && j < n@ && j != x@ ==>
        d.deep_model()[i][j] == d_old.deep_model()[i][j]
    )]
    #[invariant(forall<i:Int>
        0 <= i && i < produced.len() && i != x@ ==>
        d.deep_model()[x@][i] == INF@ && d.deep_model()[i][x@] == d.deep_model()[i][0])]
    #[invariant(d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@])]
    for i in 0..n {
        if i != x {
            d[x][i] = INF;
            d[i][x] = d[i][0];
        }
    }

    proof_assert! {
        forall<i:Int, j:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ ==>
            d.deep_model()[i][j] == d_old.deep_model()[i][j]
    };

    proof_assert! {
        forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            d.deep_model()[x@][i] == INF@ &&
            d.deep_model()[i][x@] == d.deep_model()[i][0]
    };

    proof_assert! {
        d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@]
    }

    // i==x && j==x && k!=x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // i==x && j!=x && k==x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            0 <= j && j < n@ && j != x@ &&
            k == x@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // i==x && j!=x && k!=x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // i==x のケースすべて
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            0 <= j && j < n@ &&
            0 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };

    // i!=xのケース
    // i!=x && j==x && k==x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            j == x@ &&
            k == x@ ==>
            d.deep_model()[k][j] == 0 &&
            d.deep_model()[i][j] == d.deep_model()[i][0] &&
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // i!=x && j!=x && k==x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ &&
            k == x@ ==>
            d.deep_model()[i][j] == INF@ ==> d.deep_model()[k][j] == INF@ &&
            d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][k] + d.deep_model()[k][j] &&
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // i!=x && j==x && k!=x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            d.deep_model()[i][j] == d.deep_model()[i][0] &&
            d.deep_model()[k][j] == d.deep_model()[k][0] &&
            triangle_inequality(d.deep_model(), n@, i, 0, k) &&
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // i!=x && j!=x && k!=x
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    };
}

#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(1 <= x@ && x@ < n@)] // ゼロを書き換えるような使い方はしない
#[requires(0 <= m@ && m@ < BOUND@)] // 更新する時刻は上限を超えない範囲であり、しかも正の値となる
#[requires(is_canonical(d.deep_model(), n@))]
fn reset(d: &mut Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    let d_old = snapshot! { d };

    // #[invariant(is_dbm(d.deep_model(), n@))]
    #[invariant((2 <= n@))]
    #[invariant(d@.len() == n@)]
    #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i].len() == n@)]
    #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][i] == 0)]
    #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[0][i] <= 0)]
    #[invariant(forall<i:Int> 0 <= i && i < n@ ==> 0 <= d.deep_model()[i][0])]
    #[invariant(forall<i:Int, j:Int>
        0 <= i && i < n@ &&
        0 <= j && j < n@ ==>
        (-BOUND@ < d.deep_model()[i][j] && d.deep_model()[i][j] < BOUND@) || d.deep_model()[i][j] == INF@)]
    #[invariant(forall<i:Int, j:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= j && j < n@ && j != x@ ==>
        d.deep_model()[i][j] == d_old.deep_model()[i][j])]
    // d[0][i] + mの想定される範囲としては（mが正なので）(-BOUND, BOUND), [BOUND, INF), [INF, INF]
    // ここが問題になっているみたい、、、
    #[invariant(forall<i:Int>
        0 <= i && i < produced.len() && i != x@ ==>
        (d.deep_model()[0][i] + m@ >= BOUND@ ==> d.deep_model()[x@][i] == INF@) &&
        (d.deep_model()[0][i] + m@ <  BOUND@ ==> d.deep_model()[x@][i] == d.deep_model()[0][i] + m@)
    )]
    #[invariant(forall<i:Int>
        0 <= i && i < produced.len() && i != x@ ==>
        (d.deep_model()[i][0] == INF@         ==> d.deep_model()[i][x@] == INF@) &&
        (d.deep_model()[i][0] - m@ <= -BOUND@ ==> d.deep_model()[i][x@] == -BOUND@ + 1) &&
        (-BOUND@ < d.deep_model()[i][0] - m@ && d.deep_model()[i][0] - m@ < BOUND@ ==> d.deep_model()[i][x@] == d.deep_model()[i][0] - m@)
    )]
    #[invariant(d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@])]
    for i in 0..n {
        if i != x {
            if d[0][i] == INF || BOUND <= d[0][i] + m {
                d[x][i] = INF;
            } else {
                proof_assert! { d.deep_model()[0][i@] + m@ < BOUND@ };
                d[x][i] = d[0][i] + m;
            }
    
            if d[i][0] == INF {
                d[i][x] = INF;
            } else if d[i][0] - m <= -BOUND {
                d[i][x] = -BOUND + 1;
            } else {
                proof_assert! { -BOUND@ < d.deep_model()[i@][0] - m@ && d.deep_model()[i@][0] - m@ < BOUND@ };
                d[i][x] = d[i][0] - m;
            }
        }
    }

    proof_assert! {
        forall<i:Int, j:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ ==>
            d.deep_model()[i][j] == d_old.deep_model()[i][j]
    };
    proof_assert! {
        forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d.deep_model()[0][i] + m@ >= BOUND@ ==> d.deep_model()[x@][i] == INF@) &&
            (d.deep_model()[0][i] + m@ <  BOUND@ ==> d.deep_model()[x@][i] == d.deep_model()[0][i] + m@)
    };
    proof_assert! {
        forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d.deep_model()[i][0] == INF@         ==> d.deep_model()[i][x@] == INF@) &&
            (d.deep_model()[i][0] - m@ <= -BOUND@ ==> d.deep_model()[i][x@] == -BOUND@ + 1) &&
            (-BOUND@ < d.deep_model()[i][0] - m@ && d.deep_model()[i][0] - m@ < BOUND@ ==> d.deep_model()[i][x@] == d.deep_model()[i][0] - m@)
    };
    proof_assert! {
        d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@]
    }

    // i==x && j==x && k!=x
    // ここむり！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            (d.deep_model()[x@][k] >= d.deep_model()[0][k] + m@) &&
            (d.deep_model()[k][x@] >= d.deep_model()[k][0] - m@) &&
            (d.deep_model()[i][j] == d.deep_model()[0][0]) &&
            (d.deep_model()[0][k] + d.deep_model()[k][0] <= d.deep_model()[x@][k] + d.deep_model()[k][x@]) &&
            triangle_inequality(d.deep_model(), n@, 0, k, 0) &&
            (d.deep_model()[i][j] == 0) &&
            triangle_inequality(d.deep_model(), n@, 0, 0, k) &&
            (d.deep_model()[0][0] != INF@)
            // (d.deep_model()[0][0] != INF@ ==> d.deep_model()[0][0] <= d.deep_model()[0][k] + d.deep_model()[k][0]) // これが言えないのがなんでかわからん、、。Creusotが悪い可能性もあるので、ちょっと先に進めない、、。
            // (d.deep_model()[0][0] <= d.deep_model()[0][k] + d.deep_model()[k][0])
            // (d.deep_model()[i][j] <= d.deep_model()[0][k] + d.deep_model()[k][0])
            // (d.deep_model()[i][j] != INF@ ==> d.deep_model()[0][0] <= d.deep_model()[0][k] + d.deep_model()[k][0])
            // <= d.deep_model()[x@][k] + d.deep_model()[k][x@])
            // (d.deep_model()[i][j] == INF@ ==> false)
            // triangle_inequality(d.deep_model(), n@, i, j, k)
    };
    // 以降もそれぞれ場合分けしながらどうにか証明していく、、
    // // i==x && j!=x && k==x
    //
    // // i==x && j!=x && k!=x
    // 
    // // i==x のケースすべて
    //

    // // i!=xのケース
    // // i!=x && j==x && k==x
    // 
    // // i!=x && j!=x && k==x
    // 
    // // i!=x && j==x && k!=x
    // 
    // // i!=x && j!=x && k!=x
    // 
}




















































// [[0, 0, 0],
//  [5, 0, 1],
//  [3, 0, 0]] 
// はcanonical formではないが、
// [[0, 0, 0],
//  [4, 0, 1],
//  [3, 0, 0]] 
// はcanonical formとなることをチェック
// ※ 具体的なケースを渡すには、requires節のようにして渡す必要がある。
#[requires(is_dbm(v.deep_model(), 3))]
#[requires(v.deep_model()[0][0] == 0 && v.deep_model()[0][1] == 0 && v.deep_model()[0][2] == 0)]
#[requires(v.deep_model()[1][0] == 5 && v.deep_model()[1][1] == 0 && v.deep_model()[1][2] == 1)]
#[requires(v.deep_model()[2][0] == 3 && v.deep_model()[2][1] == 0 && v.deep_model()[2][2] == 0)]
#[ensures(is_canonical((^v).deep_model(), (^v)@.len()))]
fn test(v: &mut Vec<Vec<i32>>) {
    proof_assert! { v@.len() == 3 };
    proof_assert! { is_dbm(v.deep_model(), v@.len()) };
    proof_assert! { !is_canonical(v.deep_model(), v@.len()) };
    v[1][0] = 4;
}
