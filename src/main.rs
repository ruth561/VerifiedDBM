// #![feature(proc_macro_hygiene)]
// #![feature(stmt_expr_attributes)]

mod dbm;
mod down;
mod up;
mod free;

use creusot_contracts::*;
use textplots::{Chart, Plot, Shape};

use crate::dbm::*;

const BOUND: i64 = 100000; // 各制約の値はこの値を超えることはない。
const INF: i64 = i64::MAX; // 無限を表す値
const MAX_NODE: usize = 100000; // グラフの最大ノード数

const XIDX: usize = 1; // テストケース用
const YIDX: usize = 2; // テストケース用

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
            if 0 - x <= dbm[0][XIDX] &&
               0 - y <= dbm[0][YIDX] &&
               x - 0 <= dbm[XIDX][0] &&
               y - 0 <= dbm[YIDX][0] &&
               x - y <= dbm[XIDX][YIDX] &&
               y - x <= dbm[YIDX][XIDX] {
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
    loop {
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
                    up::up(&mut dbm, n);
                } else if &s == "2" {
                    println!("[*] DOWN");
                    down::down(&mut dbm, n);
                } else if &s == "3 x" {
                    println!("[*] FREE x");
                    free::free(&mut dbm, n, XIDX);
                } else if &s == "3 y" {
                    println!("[*] FREE y");
                    free::free(&mut dbm, n, YIDX);
                } else if &s[0..3] == "4 x" {
                    if let Ok(m) = i64::from_str_radix(&s[4..], 10) {
                        println!("[*] RESET x {m}");
                        reset(&mut dbm, n, XIDX, m);
                    } else {
                        println!("failed to parse int.");
                    }
                } else if &s[0..3] == "4 y" {
                    if let Ok(m) = i64::from_str_radix(&s[4..], 10) {
                        println!("[*] RESET y {m}");
                        reset(&mut dbm, n, YIDX, m);
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
