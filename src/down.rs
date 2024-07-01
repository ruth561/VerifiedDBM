use creusot_contracts::*;
use crate::{BOUND, INF, MAX_NODE};
use crate::dbm::*;

// 行列の特定の列における最小値を計算するlogic関数
// - n: the size of matrix
// - i: the number of column
// - l: low
// - u: upper
// - x: default value
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

// DBMの第i列目の最小値を返す関数。
// xは初期値を指定する（つまり、その範囲内の最小値よりもxの方が小さければ、xが返される）。
// lとuで行の範囲を指定することができる。もし、列全体の最小値を得たければ、min_col(d, n, i, 0, n, i64::MAX)のようにする。
// このように実装しているのは、downの実装に便利だからである。証明を簡潔にかけるようにした。
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

// downの処理の前後におけるDBMの関係性を示す述語
// 以下の3つの領域に分けて値の変動を記憶している
// [[  A,  B, ... ,  B],
//  [  A,  C, ... ,  C],
//  [  A,  C, ... ,  C],
//    ...
//  [  A,  C, ... ,  C]]
// downの処理の前後で値が変化しないのはAとC
// Bの領域は値が変化する。変化する先の値は、0とその列の最小値の小さい方となっている
#[predicate]
fn down_precondition(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) -> bool {
    pearlite! {
        (forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][0] == d_old.deep_model()[i][0]) &&
        (forall<i:Int> 1 <= i && i < n@ ==> d.deep_model()[0][i] == min_col_int_log(d_old.deep_model(), n@, i, 1, n@, 0)) &&
        (forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j])
    }
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        j == 0 &&
        k == 0 ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_000(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        j == 0 &&
        1 <= k && k < n@ &&
        d.deep_model()[0][k] == 0 ==>
        d.deep_model()[k][0] >= 0 &&
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_001_0(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        j == 0 &&
        1 <= k && k < n@ &&
        d.deep_model()[0][k] != 0 ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_001_1(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
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
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        j == 0 &&
        1 <= k && k < n@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_001(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    lem_for_down_001_0(&d, &d_old, n);
    lem_for_down_001_1(&d, &d_old, n);
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == 0 &&
        1 <= j && j < n@ &&
        k == 0 ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_010(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {}

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

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            j == 0 &&
            1 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_101(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            j == 0 &&
            1 <= k && k < n@ ==>
            d.deep_model()[i][j] == d_old.deep_model()[i][j] &&
            d.deep_model()[i][k] == d_old.deep_model()[i][k] &&
            d.deep_model()[k][j] == d_old.deep_model()[k][j]
    }
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            j == 0 &&
            1 <= k && k < n@ ==>
            triangle_inequality(d_old.deep_model(), n@, i, j, k) &&
            (d_old.deep_model()[i][j] == INF@ ==> d_old.deep_model()[i][k] == INF@ || d_old.deep_model()[k][j] == INF@) &&
            (d_old.deep_model()[i][j] != INF@ ==> d_old.deep_model()[i][j] <= d_old.deep_model()[i][k] + d_old.deep_model()[k][j])
    }
}

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
fn lem_for_lem_for_down_110(d: &Vec<Vec<i64>>, n: usize) {
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

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(down_precondition(d, d_old, n))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            k == 0 ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_down_110(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) {
    lem_for_lem_for_down_110(&d_old, n); // なぜか補題にしないと証明できないやつ（やってることはかなり簡単なのになんでできないのか、、？）
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
}

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
            d.deep_model()[k][j] == d_old.deep_model()[k][j]
    }
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            1 <= i && i < n@ &&
            1 <= j && j < n@ &&
            1 <= k && k < n@ ==>
            triangle_inequality(d_old.deep_model(), n@, i, j, k) &&
            (d.deep_model()[i][j] == INF@ ==> d.deep_model()[i][k] == INF@ || d.deep_model()[k][j] == INF@) &&
            (d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][k] + d.deep_model()[k][j])
    }
}

// [[  0,  m2, ... ,  mn], mi = min{0, x2i, x3i, ..., xni}
//  [---, x22, ... , x2n],
//  [---, x32, ... , x3n],
//  ...
//  [---, xn2, ... , xnn]]
#[open]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(is_canonical(d.deep_model(), n@))]
#[ ensures(is_canonical((^d).deep_model(), n@))]
pub fn down(d: &mut Vec<Vec<i64>>, n: usize) {
    let d_old = snapshot! { d };

    // invariantの制約は3ブロックに分けて考える。
    // AとCは変化しない部分
    // [[  A,  B, ... ,  B],
    //  [  A,  C, ... ,  C],
    //  [  A,  C, ... ,  C],
    //    ...
    //  [  A,  C, ... ,  C]]
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
    #[invariant(forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][0] == d_old.deep_model()[i][0])] // A
    #[invariant(forall<i:Int> 1 <= i && i < 1+produced.len() ==> d.deep_model()[0][i] == min_col_int_log(d_old.deep_model(), n@, i, 1, n@, 0))] // B
    #[invariant(forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j])] // C
    for i in 1..n {
        d[0][i] = min_col_int(&d, n, i, 1, n, 0);
    }

    // おそらく当たり前だけど一応確認のためにassertしてるやつ
    proof_assert! { forall<i:Int> 0 <= i && i < n@ ==> d.deep_model()[i][0] == d_old.deep_model()[i][0] };
    proof_assert! { forall<i:Int> 1 <= i && i < n@ ==> d.deep_model()[0][i] == min_col_int_log(d_old.deep_model(), n@, i, 1, n@, 0) };
    proof_assert! { forall<i:Int, j:Int> 1 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == d_old.deep_model()[i][j] };

    // (i, j, k)が0かどうかで場合分け
    pearlite! { lem_for_down_000(&d, &d_old, n) }; // i==0 && j==0 && k==0
    pearlite! { lem_for_down_001(&d, &d_old, n) }; // i==0 && j==0 && k!=0
    pearlite! { lem_for_down_010(&d, &d_old, n) }; // i==0 && j!=0 && k==0
    pearlite! { lem_for_down_011(&d, &d_old, n) }; // i==0 && j!=0 && k!=0
    pearlite! { lem_for_down_100(&d, &d_old, n) }; // i!=0 && j==0 && k==0
    pearlite! { lem_for_down_101(&d, &d_old, n) }; // i!=0 && j==0 && k!=0
    pearlite! { lem_for_down_110(&d, &d_old, n) }; // i!=0 && j!=0 && k==0
    pearlite! { lem_for_down_111(&d, &d_old, n) }; // i!=0 && j!=0 && k!=0

    // 三角不等式をすべての組に対して証明できた
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ &&
            0 <= j && j < n@ &&
            0 <= k && k < n@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }
}
