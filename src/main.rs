// #![feature(proc_macro_hygiene)]
// #![feature(stmt_expr_attributes)]

// use ::std::ops::Add;
// use ::std::option::Option;
// use ::std::clone::Clone;
// use ::std::marker::Copy;
// use ::std::cmp::Ordering;
// use ::std::cmp::Ord;
// use ::std::cmp::PartialOrd;

use creusot_contracts::*;
use textplots::{Chart, Plot, Shape};

const BOUND: i64 = 100000;    // 各制約の値はこの値を超えることはない。
const INF: i64 = i64::MAX;          // 無限を表す値
const MAX_NODE: usize = 100000;

const xidx: usize = 1;
const yidx: usize = 2;


#[trusted]
#[ensures(is_canonical(result.deep_model(), result@.len()))]
fn get_dbm() -> Vec<Vec<i64>> {
    let mut dbm = Vec::new();
    let mut row0 = Vec::new();
    let mut row1 = Vec::new();
    let mut row2 = Vec::new();
    row0.push( 0); row0.push(-10); row0.push( 0);
    row1.push(30); row1.push(  0); row1.push(20);
    row2.push(20); row2.push(  0); row2.push( 0);
    dbm.push(row0);
    dbm.push(row1);
    dbm.push(row2);
    dbm
}

// 引数で渡された2次元配列がDBMかどうか（is_dbmという述語に含まれているかどうか）を判定する関数。
// 証明済み！
#[ensures(result == is_dbm(dbm.deep_model(), dbm@.len()))]
fn check_is_dbm(dbm: &Vec<Vec<i64>>) -> bool {
    let n = dbm.len();
    if n < 2 {
        return false;
    }

    #[invariant(forall<i:Int> 0 <= i && i < produced.len() ==> dbm.deep_model()[i].len() == n@)]
    for i in 0..n {
        if dbm[i].len() != n {
            return false;
        }
    }

    #[invariant(forall<i:Int> 0 <= i && i < produced.len() ==> dbm.deep_model()[0][i] <= 0)]
    #[invariant(forall<i:Int> 0 <= i && i < produced.len() ==> dbm.deep_model()[i][0] >= 0)]
    #[invariant(forall<i:Int> 0 <= i && i < produced.len() ==> dbm.deep_model()[i][i] == 0)]
    for i in 0..n {
        if dbm[0][i] > 0 || dbm[i][0] < 0 || dbm[i][i] != 0 {
            return false;
        }
    }

    #[invariant(forall<i:Int, j:Int> 0 <= i && i < produced.len() && 0 <= j && j < n@ ==> (-BOUND@ < dbm.deep_model()[i][j] && dbm.deep_model()[i][j] < BOUND@) || dbm.deep_model()[i][j] == INF@)]
    for x in 0..n {
        #[invariant(forall<i:Int, j:Int> 0 <= i && i < x@ && 0 <= j && j < n@ ==> (-BOUND@ < dbm.deep_model()[i][j] && dbm.deep_model()[i][j] < BOUND@) || dbm.deep_model()[i][j] == INF@)]
        #[invariant(forall<i:Int, j:Int> i == x@ && 0 <= j && j < produced.len() ==> (-BOUND@ < dbm.deep_model()[i][j] && dbm.deep_model()[i][j] < BOUND@) || dbm.deep_model()[i][j] == INF@)]
        for y in 0..n {
            if dbm[x][y] <= -BOUND || (BOUND <= dbm[x][y] && dbm[x][y] < INF) || INF < dbm[x][y] {
                return false;
            }
        }
    }

    return true;
}

// 引数で渡された2次元配列がcanonical formのDBMであるかどうかを判定する関数。
// 証明済み！
// （ワーシャルフロイドでも証明してみたい、、、）
#[ensures(result == is_canonical(dbm.deep_model(), dbm@.len()))]
fn check_is_canonical(dbm: &Vec<Vec<i64>>) -> bool {
    if !check_is_dbm(dbm) {
        return false;
    }

    let n = dbm.len();
    #[invariant(forall<i:Int, j:Int, k:Int>
        0 <= i && i < produced.len() &&
        0 <= j && j < n@ &&
        0 <= k && k < n@ ==>
        triangle_inequality(dbm.deep_model(), n@, i, j, k)
    )]
    for x in 0..n {
        #[invariant(forall<i:Int, j:Int, k:Int>
            0 <= i && i < x@ &&
            0 <= j && j < n@ &&
            0 <= k && k < n@ ==>
            triangle_inequality(dbm.deep_model(), n@, i, j, k)
        )]
        #[invariant(forall<i:Int, j:Int, k:Int>
            i == x@ &&
            0 <= j && j < produced.len() &&
            0 <= k && k < n@ ==>
            triangle_inequality(dbm.deep_model(), n@, i, j, k)
        )]
        for y in 0..n {
            #[invariant(forall<i:Int, j:Int, k:Int>
                0 <= i && i < x@ &&
                0 <= j && j < n@ &&
                0 <= k && k < n@ ==>
                triangle_inequality(dbm.deep_model(), n@, i, j, k)
            )]
            #[invariant(forall<i:Int, j:Int, k:Int>
                i == x@ &&
                0 <= j && j < y@ &&
                0 <= k && k < n@ ==>
                triangle_inequality(dbm.deep_model(), n@, i, j, k)
            )]
            #[invariant(forall<i:Int, j:Int, k:Int>
                i == x@ &&
                j == y@ &&
                0 <= k && k < produced.len() ==>
                triangle_inequality(dbm.deep_model(), n@, i, j, k)
            )]
            for z in 0..n {
                // 三角不等式
                if dbm[x][y] == INF {
                    if dbm[x][z] != INF && dbm[z][y] != INF {
                        proof_assert! { !(dbm.deep_model()[x@][y@] == INF@ ==> dbm.deep_model()[x@][z@] == INF@ || dbm.deep_model()[z@][y@] == INF@) };
                        proof_assert! { !is_canonical(dbm.deep_model(), n@) };
                        return false;
                    }
                } else { // dbm[x][y] != INF
                    if dbm[x][z] == INF || dbm[z][y] == INF {
                        continue;
                    }
                    // -BOUND < dbm[x][y], dbm[x][z], dbm[z][y] < BOUND
                    if dbm[x][y] > dbm[x][z] + dbm[z][y] {
                        proof_assert! { !(dbm.deep_model()[x@][y@] != INF@ ==> dbm.deep_model()[x@][y@] <= dbm.deep_model()[x@][z@] + dbm.deep_model()[z@][y@]) };
                        proof_assert! { !is_canonical(dbm.deep_model(), n@) };
                        return false;
                    }
                }
            }
        }
    }

    proof_assert! { is_canonical(dbm.deep_model(), n@) };

    true
}

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
                    down(&mut dbm, n);
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

/// ここから証明

#[logic]
fn validx(n: Int, i: Int, j: Int, k: Int) -> bool {
    pearlite! {
        0 <= i && i < n &&
        0 <= j && j < n &&
        0 <= k && k < n
    }
}

// 与えられた行列の形が nxn であること
// 対角成分がすべて0であること
// 各clockの値は正の値であること、つまりD[0][i]の値は非正であること
//   - これは「0 - x[i] <= D[0][i]」のような制約として解釈されるため、
//     「-D[0][i] <= x[i]」のような制約となることからわかる。
// 各clockの値が正の値であることから、もう1つの制約D[i][0]が非負ということも分かる
//   - これは「x[i] - 0 <= D[i][0]」のような制約と解釈されるため、D[i][0]が負の値だと、clockが負の値になってしまう。
// 各制約の値はBOUNDよりも小さいようにする（もしくはINF）。
// D[i][i]の値は常に0とする（論文ではD[0][0]が負の時にinvalidとしているが、ここではinvalidなものはすべてはじく）
#[predicate]
fn is_dbm(dbm: Seq<Seq<Int>>, n: Int) -> bool {
    pearlite! {
        (2 <= n) &&
        (dbm.len() == n) &&
        (forall<i:Int> 0 <= i && i < n ==> dbm[i].len() == n) &&
        (forall<i:Int> 0 <= i && i < n ==> dbm[i][i] == 0) &&
        (forall<i:Int> 0 <= i && i < n ==> dbm[0][i] <= 0) &&
        (forall<i:Int> 0 <= i && i < n ==> 0 <= dbm[i][0]) &&
        (forall<i:Int, j:Int>
            0 <= i && i < n &&
            0 <= j && j < n ==>
            (-BOUND@ < dbm[i][j] && dbm[i][j] < BOUND@) || dbm[i][j] == INF@)
    }
}

// canonical性は2-stepのpathが1-stepのpathよりも短くならない、という性質でよい。
// なぜなら、
#[predicate]
fn is_canonical(dbm: Seq<Seq<Int>>, n: Int) -> bool {
    pearlite! {
        is_dbm(dbm, n) &&
        (forall<i:Int, j:Int, k:Int>
            0 <= i && i < n &&
            0 <= j && j < n &&
            0 <= k && k < n ==>
            triangle_inequality(dbm, n, i, j, k))
    }
}

// 三角不等式
// DBMではINF(=i64::MAX)を使用しているため、三角不等式はすこし変形する必要がある。
#[predicate]
#[requires(is_dbm(dbm, n))]
#[requires(0 <= i && i < n)]
#[requires(0 <= j && j < n)]
#[requires(0 <= k && k < n)]
fn triangle_inequality(dbm: Seq<Seq<Int>>, n: Int, i: Int, j: Int, k: Int) -> bool {
    pearlite! {
        (dbm[i][j] != INF@ ==> -BOUND@ < dbm[i][j] && dbm[i][j] < BOUND@) &&
        (dbm[i][k] != INF@ ==> -BOUND@ < dbm[i][k] && dbm[i][k] < BOUND@) &&
        (dbm[k][j] != INF@ ==> -BOUND@ < dbm[k][j] && dbm[k][j] < BOUND@) &&
        (dbm[i][j] == INF@ ==> dbm[i][k] == INF@ || dbm[k][j] == INF@) &&
        (dbm[i][j] != INF@ ==> dbm[i][j] <= dbm[i][k] + dbm[k][j])
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

// - n: the size of matrix
// - i: the number of column
// - l: low
// - u: upper
// - x: default value
//
// - result: min{ x, d[l][i], d[l+1][i], ... , d[u-1][i] }
#[logic]
#[variant(u - l)]
#[requires(is_dbm(d, n))]
#[requires(0 <= i && i <  n)] // column
#[requires(0 <= l && l <= u && u <= n)] // row range (=[l, u)) 
#[ensures(result <= x && forall<j:Int> l <= j && j < u ==> result <= d[j][i])]
#[ensures(result == x || exists<j:Int> l <= j && j < u &&  result == d[j][i])]
fn min_col_int_log(d: Seq<Seq<Int>>, n: Int, i: Int, l:Int, u: Int, x: Int) -> Int {
    pearlite! {
        if l == u { // 要素数0のとき
            x
        } else { // l < u
            proof_assert! { l < u };
            d[u - 1][i].min(min_col_int_log(d, n, i, l, u-1, x))
        }
    }
}

// DBMの第i行目の最小値を返す関数
// つまり min{ d[0][i], d[1][i], ... , d[n-1][i] } を返す
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(0 <= i@ && i@ <  n@)] // column
#[requires(0 <= l@ && l@ <= u@ && u@ <= n@)] // row range (=[l, u)) 
#[ensures(result@ == min_col_int_log(d.deep_model(), n@, i@, l@, u@, x@))]
fn min_col_int(d: &Vec<Vec<i64>>, n: usize, i: usize, l: usize, u: usize, x: i64) -> i64 {
    let mut ans = x;
    #[invariant(ans@ == min_col_int_log(d.deep_model(), n@, i@, l@, l@+produced.len(), x@))]
    for j in l..u {
        if d[j][i] < ans {
            ans = d[j][i];
        }
    }
    ans
}

// i!=0 && j!=0 && k==0のケースで使用する補題
#[requires(is_canonical(d.deep_model(), n@))]
#[ensures(forall<j:Int> 1 <= j && j < n@ ==> d.deep_model()[0][j] <= 0)]
#[ensures(forall<j:Int, l:Int> 1 <= j && j < n@ && 1 <= l && l < n@ ==> d.deep_model()[0][j] <= d.deep_model()[l][j])]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        1 <= i && i < n@ &&
        1 <= j && j < n@ &&
        k == 0 ==>
        triangle_inequality(d.deep_model(), n@, i, j, 0) &&
        (d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][0] + d.deep_model()[0][j])
)]
fn lem_for_down(d: &Vec<Vec<i64>>, n: usize) {
    proof_assert! {
        forall<j:Int, l:Int>
            1 <= j && j < n@ &&
            1 <= l && l < n@ ==>
            triangle_inequality(d.deep_model(), n@, 0, j, l) &&
            (d.deep_model()[0][j] != INF@ ==> d.deep_model()[0][j] <= d.deep_model()[0][l] + d.deep_model()[l][j])
    }
    proof_assert! {
        forall<j:Int, l:Int>
            1 <= j && j < n@ &&
            1 <= l && l < n@ ==>
            d.deep_model()[0][j] != INF@ &&
            d.deep_model()[0][j] <= d.deep_model()[0][l] + d.deep_model()[l][j]
            // d.deep_model()[0][j] <= d.deep_model()[l][j]
    }
}

// downの処理の前後におけるDBMの関係性を示す述語
// 3つの領域に分けて値の変動を記憶している
#[predicate]
fn down_precondition(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) -> bool {
    pearlite! {
        (forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][0] == d_old.deep_model()[i][0]) &&
        (forall<i:Int> 1 <= i && i < n@ ==> d.deep_model()[0][i] == min_col_int_log(d_old.deep_model(), n@, i, 1, n@, 0)) &&
        (forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j])
    }
}

// i==0 && j!=0 && k!=0 && d[0][k]==0
#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        1 <= j && j < n@ &&
        1 <= k && k < n@ &&
        d.deep_model()[0][k] == 0 ==>
        d.deep_model()[0][j] <= d.deep_model()[k][j] &&
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_011_0(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {}

// requiresに指定する条件は必要最低限に留める
#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<j:Int, k:Int>
        1 <= j && j < n@ &&
        1 <= k && k < n@ ==>
        (forall<l:Int>
            1 <= l && l < n@ ==>
            triangle_inequality(d.deep_model(), n@, l, j, k))
)]
fn lem_for_lem_for_down_011_1(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    lem_for_down_111(d, d_old, n);
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        1 <= j && j < n@ &&
        1 <= k && k < n@ &&
        d.deep_model()[0][k] != 0 ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_011_1(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    lem_for_lem_for_down_011_1(&d, &d_old, n);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            1 <= j && j < n@ &&
            1 <= k && k < n@ &&
            d.deep_model()[0][k] != 0 ==>
            (exists<l:Int>
                1 <= l && l < n@ &&
                d.deep_model()[0][k] == d.deep_model()[l][k] &&
                triangle_inequality(d.deep_model(), n@, l, j, k) &&
                d.deep_model()[0][j] <= d.deep_model()[l][j] &&
                triangle_inequality(d.deep_model(), n@, i, j, k))
    }
    
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        1 <= j && j < n@ &&
        1 <= k && k < n@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_011(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    lem_for_down_011_0(&d, &d_old, n);
    lem_for_down_011_1(&d, &d_old, n);
}

// downで使われる補題（番号はi,j,kが0か0でないかを意味しており、今回はi!=0, j!=0, k!=0のケースに関する補題）
#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            1 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_111(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            1 <= k && k < n@ ==>
            d.deep_model()[i][j] == d_old.deep_model()[i][j] &&
            d.deep_model()[i][k] == d_old.deep_model()[i][k] &&
            d.deep_model()[k][j] == d_old.deep_model()[k][j] &&
            triangle_inequality(d_old.deep_model(), n@, i, j, k)
    }
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            1 <= k && k < n@ ==>
            (d.deep_model()[i][j] == INF@ ==> d.deep_model()[i][k] == INF@ || d.deep_model()[k][j] == INF@) &&
            (d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][k] + d.deep_model()[k][j])
    }
}

// #[requires(is_canonical(d_old.deep_model(), n@))]
// #[requires(is_dbm(d.deep_model(), n@))]
// #[requires(down_precondition(d, d_old, n))]
// #[ensures(
//     forall<i:Int, j:Int, k:Int>
//             1 <= i && i < n@ &&
//             j == 0 &&
//             1 <= k && k < n@ ==>
//             triangle_inequality(d.deep_model(), n@, i, j, k)
// )]
// fn lem_for_down_101(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        1 <= i && i < n@ &&
        j == 0 &&
        k == 0 ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_100(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {}



#[requires(forall<i:Int, j:Int, k:Int> 1<=i && i<n@ && j==0         && k==0         ==> triangle_inequality(d.deep_model(), n@, i, j, k))]
#[requires(forall<i:Int, j:Int, k:Int> 1<=i && i<n@ && j==0         && 1<=k && k<n@ ==> triangle_inequality(d.deep_model(), n@, i, j, k))]
#[requires(forall<i:Int, j:Int, k:Int> 1<=i && i<n@ && 1<=j && j<n@ && k==0         ==> triangle_inequality(d.deep_model(), n@, i, j, k))]
#[requires(forall<i:Int, j:Int, k:Int> 1<=i && i<n@ && 1<=j && j<n@ && 1<=k && k<n@ ==> triangle_inequality(d.deep_model(), n@, i, j, k))]
#[ ensures(forall<i:Int, j:Int, k:Int> 1<=i && i<n@ && 0<=j && j<n@ && 0<=k && k<n@ ==> triangle_inequality(d.deep_model(), n@, i, j, k))]
fn lem_for_down2(d: &Vec<Vec<i64>>, n: usize) {}

// [[  0,  m2, ... ,  mn], mi = min{0, x2i, x3i, ..., xni}
//  [---, x22, ... , x2n],
//  [---, x32, ... , x3n],
//  ...
//  [---, xn2, ... , xnn]]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(is_canonical(d.deep_model(), n@))]
fn down(d: &mut Vec<Vec<i64>>, n: usize) {
    let d_old = snapshot! { d };

    // invariantの制約は3ブロックに分けて考える。
    // AとCは変化しない部分
    // [[  A,  B, ... ,  B],
    //  [  A,  C, ... ,  C],
    //  [  A,  C, ... ,  C],
    //    ...
    //  [  A,  C, ... ,  C]]
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
    #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][0] == d_old.deep_model()[i][0])] // A
    #[invariant(forall<i:Int> 1 <= i && i < 1+produced.len() ==> d.deep_model()[0][i] == min_col_int_log(d_old.deep_model(), n@, i, 1, n@, 0))] // B
    #[invariant(forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j])] // C
    for i in 1..n {
        d[0][i] = min_col_int(&d, n, i, 1, n, 0);
    }

    // proof_assert! {
    //     is_canonical(d_old.deep_model(), n@)
    // };

    // おそらく当たり前だけど一応確認のためにassertしてるやつ
    proof_assert! { forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][0] == d_old.deep_model()[i][0] };
    proof_assert! { forall<i:Int> 1 <= i && i < n@ ==> d.deep_model()[0][i] == min_col_int_log(d_old.deep_model(), n@, i, 1, n@, 0) };
    proof_assert! { forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j] };

    // proof_assert! { forall<i:Int> 1 <= i && i < n@ ==> d.deep_model()[0][i] <= 0 }; // これはis_dbmから直ちに言える？
    // proof_assert! { forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[0][i] <= d.deep_model()[j][i] };

    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         1 <= i && i < n@ &&
    //         1 <= j && j < n@ &&
    //         1 <= k && k < n@ ==>
    //         triangle_inequality(d.deep_model(), n@, i, j, k)
    // };

    // ここが通るときと通らないときがある、、
    // 該当箇所で新しくSplit VCを選択するとなぜか通るときがある、、
    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         0 < i && i < n@ &&
    //         0 < j && j < n@ &&
    //         0 < k && k < n@ ==>
    //         d_mid.deep_model()[i][j] == d_old.deep_model()[i][j] &&
    //         d_mid.deep_model()[j][k] == d_old.deep_model()[j][k] &&
    //         d_mid.deep_model()[i][k] == d_old.deep_model()[i][k]
    // };
    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         0 < i && i < n@ &&
    //         0 < j && j < n@ &&
    //         0 < k && k < n@ ==>
    //         triangle_inequality(d_mid.deep_model(), n@, i, j, k)
    // };

    // 場合分け

    // i==0
    //   i==0 && j!=0 && k!=0
    //     i==0 && j!=0 && k!=0 && d[0][k]==0
    lem_for_down_011(&d, &d_old, n);
    //     i==0 && j!=0 && k!=0 && d[0][k]!=0
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            1 <= j && j < n@ &&
            1 <= k && k < n@ &&
            d.deep_model()[0][k] != 0 ==>
            (exists<l:Int>
                1 <= l && l < n@ &&
                d.deep_model()[0][k] == d.deep_model()[l][k] &&
                triangle_inequality(d.deep_model(), n@, l, j, k) &&
                d.deep_model()[0][j] <= d.deep_model()[l][j] &&
                triangle_inequality(d.deep_model(), n@, i, j, k))
    };
    //   i==0 && j==0 && k!=0
    //     i==0 && j==0 && k!=0 && d[0][k] == 0
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            j == 0 &&
            1 <= k && k < n@ &&
            d.deep_model()[0][k] == 0 ==>
            d.deep_model()[k][0] >= 0 &&
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }
    //     i==0 && j==0 && k!=0 && d[0][k] != 0
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            j == 0 &&
            1 <= k && k < n@ &&
            d.deep_model()[0][k] != 0 ==>
            (exists<l:Int>
                1 <= l && l < n@ &&
                d.deep_model()[0][k] == d.deep_model()[l][k] &&
                triangle_inequality(d.deep_model(), n@, l, 0, k) &&
                (d.deep_model()[l][0] == INF@ ==> d.deep_model()[l][k] == INF@ || d.deep_model()[k][0] == INF@) &&
                (d.deep_model()[l][0] != INF@ ==> d.deep_model()[l][0] <= d.deep_model()[l][k] + d.deep_model()[k][0]) &&
                0 <= d.deep_model()[l][0] &&
                (d.deep_model()[l][0] == INF@ ==> 0 <= d.deep_model()[l][k] + d.deep_model()[k][0]) &&
                (d.deep_model()[l][0] != INF@ ==> 0 <= d.deep_model()[l][k] + d.deep_model()[k][0]) &&
                0 <= d.deep_model()[l][k] + d.deep_model()[k][0]
            )
    };
    proof_assert! { // proof_assertを分割すると証明器への負担が小さくなる。
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            j == 0 &&
            1 <= k && k < n@ &&
            d.deep_model()[0][k] != 0 ==>
            (exists<l:Int>
                1 <= l && l < n@ &&
                d.deep_model()[0][k] == d.deep_model()[l][k] &&
                0 <= d.deep_model()[l][k] + d.deep_model()[k][0] &&
                0 <= d.deep_model()[0][k] + d.deep_model()[k][0] &&
                triangle_inequality(d.deep_model(), n@, i, j, k)
            )
    };
    //   i==0 && j!=0 && k==0
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            1 <= j && j < n@ &&
            k == 0 ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }

    // i==0のケースを一旦まとめる
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == 0 &&
            0 <= j && j < n@ &&
            0 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }
    
    // i!=0
    //   i!=0 && j==0
    //     i!=0 && j==0 && k==0
    lem_for_down_100(&d, &d_old, n);
    //   i!=0 && j!=0 && k!=0
    lem_for_down_111(&d, &d_old, n);
    //     i!=0 && j==0 && k!=0
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            j == 0 &&
            1 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }
    //   i!=0 && j!=0 && k==0
    lem_for_down(&d_old, n); // なぜか補題にしないと証明できないやつ（やってることはかなり簡単なのになんでできないのか、、？）
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            k == 0 ==>
            d_old.deep_model()[0][j] <= 0 &&
            (forall<l:Int> 1 <= l && l < n@ ==> d_old.deep_model()[0][j] <= d.deep_model()[l][j]) &&
            d_old.deep_model()[0][j] <= d.deep_model()[0][j] // すばらしい！！！（この補題は割と重そうなのでproof_assertを分ける）
    }
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            k == 0 ==>
            d_old.deep_model()[0][j] <= d.deep_model()[0][j] &&
            (d_old.deep_model()[i][j] != INF@ ==> d_old.deep_model()[i][j] <= d_old.deep_model()[i][0] + d_old.deep_model()[0][j]) &&
            d.deep_model()[i][j] == d_old.deep_model()[i][j] &&
            d.deep_model()[i][0] == d_old.deep_model()[i][0] &&
            (d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][0] + d_old.deep_model()[0][j]) &&
            (d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][0] + d.deep_model()[0][j]) &&
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }

    lem_for_down2(&d, n);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            0 <= j && j < n@ &&
            0 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }

    // i!=0 && 
    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         1 <= i && i < n@ &&
    //         1 <= j && j < n@ &&
    //         k == 0 ==>
    //         triangle_inequality(d_old.deep_model(), n@, i, j, 0) &&
    //         d_old.deep_model()[0][j] != INF@ &&
    //         (forall<l:Int>
    //             1 <= l && l < n@ ==>
    //             d_old.deep_model()[0][l] <= 0 &&
    //             d_old.deep_model()[0][j] <= d_old.deep_model()[0][l] + d_old.deep_model()[l][j] &&
    //             d_old.deep_model()[0][j] <= d_old.deep_model()[l][j]
    //         ) &&
    //         d_old.deep_model()[0][j] <= d.deep_model()[0][j]
            
    // }
    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         i == 0 &&
    //         1 <= j && j < n@ &&
    //         1 <= k && k < n@ &&
    //         d.deep_model()[0][k] != 0 ==>
    //         exists<l:Int>
    //             0 < l && l < n@ &&
    //             d.deep_model()[0][k] == d.deep_model()[l][k] &&
    //             d.deep_model()[0][j] <= d.deep_model()[l][j] &&
    //             triangle_inequality(d.deep_model(), n@, l, j, k) && // e_{l,j} <= e_{l,k} + e_{k,j}
    //             // d[l][j] <= d[0][k] + d[k][j] から d[l0[j] <= d[0][k] + d[k][j] を言いたい
    //             (d.deep_model()[0][j] == INF@ ==> d.deep_model()[l][j] == INF@) &&
    //             (d.deep_model()[l][j] == INF@ ==> d.deep_model()[0][k] == INF@ || d.deep_model()[k][j] == INF@) && // the case of INF
    //             (d.deep_model()[0][j] == INF@ ==> ((d.deep_model()[l][j] == INF@) && (d.deep_model()[0][k] == INF@ || d.deep_model()[k][j] == INF@))) &&
    //             (d.deep_model()[0][j] == INF@ ==> (((d.deep_model()[l][j] == INF@) && (d.deep_model()[0][k] == INF@ || d.deep_model()[k][j] == INF@))  ==> (d.deep_model()[0][k] == INF@ || d.deep_model()[k][j] == INF@)))
    // };

    // lem_for_down(d, n);

    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         0 < j && j < n@ &&
    //         0 < k && k < n@ &&
    //         d.deep_model()[0][k] != 0 ==>
    //         d.deep_model()[0][j] == INF@ ==> ((d.deep_model()[0][k] == INF@ || d.deep_model()[k][j] == INF@))
    // };

    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         0 < j && j < n@ &&
    //         0 < k && k < n@ &&
    //         d.deep_model()[0][k] != 0 ==>
    //         exists<l:Int>
    //             0 < l && l < n@ &&
    //             d.deep_model()[0][k] == d.deep_model()[l][k] &&
    //             triangle_inequality(d.deep_model(), n@, l, j, k) && // e_{l,j} <= e_{l,k} + e_{k,j}
    //             d.deep_model()[0][j] <= d.deep_model()[l][j] &&
    //             // d[l][j] <= d[0][k] + d[k][j] から d[l0[j] <= d[0][k] + d[k][j] を言いたい
    //             (d.deep_model()[l][j] != INF@ ==> d.deep_model()[l][j] <= d.deep_model()[0][k] + d.deep_model()[k][j]) && // the case of not INF
    //             (d.deep_model()[l][j] != INF@ ==> d.deep_model()[0][j] <= d.deep_model()[0][k] + d.deep_model()[k][j]) &&
    //             (d.deep_model()[l][j] != INF@ ==> d.deep_model()[0][j] != INF@)
    // };

    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         0 < j && j < n@ &&
    //         0 < k && k < n@ ==>
    //         (exists<l:Int>
    //             triangle_inequality(d_mid.deep_model(), n@, l, j, k) && // e_{l,j} <= e_{l,k} + e_{k,j}
    //             d.deep_model()[0][j] <= d.deep_model()[l][j])
    // };
    // proof_assert! {
    //     forall<i:Int, j:Int, k:Int>
    //         0 < j && j < n@ &&
    //         0 < k && k < n@ ==>
    //         (exists<l:Int>
    //             d.deep_model()[0][k] == d.deep_model()[l][k] &&
    //             triangle_inequality(d_mid.deep_model(), n@, l, j, k) && // e_{l,j} <= e_{l,k} + e_{k,j}
    //             d.deep_model()[0][j] <= d.deep_model()[l][j])
    // };


    // proof_assert! { is_canonical(d.deep_model(), n@) }; // これが最終目標
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
