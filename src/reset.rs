use creusot_contracts::*;
use crate::{BOUND, INF, MAX_NODE};
use crate::dbm::*;

// resetの処理の前後におけるDBMの関係性を示す述語
// x行とx列の値が更新され、それ以外の値はd_oldのまま
// [[---, ???, ... , ---],
//  [???,   0, ... , ???],
//  [---, ???, ... , ---],
//    ...
//  [---, ???, ... , ---]]
// 変化に関しては、x行目は
#[predicate]
fn reset_precondition(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) -> bool {
    pearlite! {
        (forall<i:Int, j:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ ==>
            d.deep_model()[i][j] == d_old.deep_model()[i][j]) &&
        (forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d_old.deep_model()[0][i] == INF@ ==> d.deep_model()[x@][i] == INF@) &&
            (d_old.deep_model()[0][i] != INF@ ==> d.deep_model()[x@][i] == d_old.deep_model()[0][i] + m@)) &&
        (forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d_old.deep_model()[i][0] == INF@ ==> d.deep_model()[i][x@] == INF@) &&
            (d_old.deep_model()[i][0] != INF@ ==> d.deep_model()[i][x@] == d_old.deep_model()[i][0] - m@)) &&
        d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@]
    }
}

// 値の更新とは逆方向の補題
// つまり、もとの更新は
//     d_old.deep_model()[0][k] == INF@ ==> d.deep_model()[x@][k] == INF@
// であったが、ここでは逆の
//     d.deep_model()[x@][k] == INF@ ==> d_old.deep_model()[0][k] == INF@
// を証明している。いくつかのケースで便利な補題。
#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<k:Int>
        0 <= k && k < n@ && k != x@ ==>
        d.deep_model()[x@][k] == INF@ ==> d_old.deep_model()[0][k] == INF@ &&
        d.deep_model()[x@][k] != INF@ ==> d_old.deep_model()[0][k] != INF@
)]
fn lem_for_all(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == x@ &&
        j == x@ &&
        k == x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_000(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == x@ &&
        j == x@ &&
        0 <= k && k < n@ && k != x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_001(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d_old.deep_model(), n@, 0, 0, k) &&
            d_old.deep_model()[0][0] <= d_old.deep_model()[0][k] + d_old.deep_model()[k][0]
    };
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == x@ &&
        0 <= j && j < n@ && j != x@ &&
        k == x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_010(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {}


#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[ensures(
    forall<j:Int, k:Int>
        0 <= j && j < n@ && j != x@ &&
        0 <= k && k < n@ && k != x@ ==>
        d_old.deep_model()[0][j] != INF@ ==> d_old.deep_model()[0][j] <= d_old.deep_model()[0][k] + d_old.deep_model()[k][j]
)]
fn lem_for_lem_for_reset_011(d_old: &Vec<Vec<i64>>, n: usize, x: usize) {
    proof_assert! {
        forall<j:Int, k:Int>
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d_old.deep_model(), n@, 0, j, k) &&
            (d_old.deep_model()[0][j] != INF@ ==> d_old.deep_model()[0][j] <= d_old.deep_model()[0][k] + d_old.deep_model()[k][j])
    };
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        i == x@ &&
        0 <= j && j < n@ && j != x@ &&
        0 <= k && k < n@ && k != x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_011(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    lem_for_all(&d, &d_old, n, x, m);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            (d.deep_model()[x@][j] == INF@ ==> d_old.deep_model()[0][j] == INF@) &&
            (d_old.deep_model()[0][j] == INF@ ==> d_old.deep_model()[0][k] == INF@ || d_old.deep_model()[k][j] == INF@) &&
            (d_old.deep_model()[0][k] == INF@ ==> d.deep_model()[x@][k] == INF@) &&
            (d.deep_model()[x@][j] == INF@ ==> d.deep_model()[x@][k] == INF@ || d_old.deep_model()[k][j] == INF@)
    }
    lem_for_lem_for_reset_011(&d_old, n, x);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            i == x@ &&
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            (d.deep_model()[x@][j] != INF@ ==> d_old.deep_model()[0][j] != INF@) &&
            (d_old.deep_model()[0][j] != INF@ ==> d_old.deep_model()[0][j] <= d_old.deep_model()[0][k] + d_old.deep_model()[k][j]) &&
            (d_old.deep_model()[0][j] != INF@ ==> d.deep_model()[x@][j] == d_old.deep_model()[0][j] + m@) &&
            (d_old.deep_model()[0][k] != INF@ ==> d.deep_model()[x@][k] == d_old.deep_model()[0][k] + m@) &&
            (d.deep_model()[x@][j] != INF@ ==> d.deep_model()[x@][j] <= d.deep_model()[x@][k] + d.deep_model()[k][j])
    }
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        0 <= i && i < n@ && i != x@ &&
        j == x@ &&
        k == x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_100(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[ensures(
    forall<i:Int, k:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= k && k < n@ && k != x@ ==>
        triangle_inequality(d_old.deep_model(), n@, i, 0, k)
)]
fn lem_for_lem_for_reset_101(d_old: &Vec<Vec<i64>>, n: usize, x: usize) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        0 <= i && i < n@ && i != x@ &&
        j == x@ &&
        0 <= k && k < n@ && k != x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_101(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    lem_for_lem_for_reset_101(&d_old, n, x);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d_old.deep_model(), n@, i, 0, k) &&
            (d_old.deep_model()[i][0] == INF@ ==> d_old.deep_model()[i][k] == INF@ || d_old.deep_model()[k][0] == INF@)
    }
    lem_for_all(&d, &d_old, n, x, m);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            (d.deep_model()[i][x@] == INF@ ==> d_old.deep_model()[i][0] == INF@) &&
            (d_old.deep_model()[i][0] == INF@ ==> d_old.deep_model()[i][k] == INF@ || d_old.deep_model()[k][0] == INF@) &&
            (d_old.deep_model()[k][0] == INF@ ==> d.deep_model()[k][x@] == INF@) &&
            (d.deep_model()[i][x@] == INF@ ==> d.deep_model()[i][k] == INF@ || d.deep_model()[k][x@] == INF@)
    }
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            j == x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d_old.deep_model(), n@, i, 0, k) &&
            (d_old.deep_model()[i][0] != INF@ ==> d_old.deep_model()[i][0] <= d_old.deep_model()[i][k] + d_old.deep_model()[k][0]) &&
            (d_old.deep_model()[i][0] != INF@ ==> d.deep_model()[i][x@] == d_old.deep_model()[i][0] - m@) &&
            (d_old.deep_model()[k][0] != INF@ ==> d.deep_model()[k][x@] == d_old.deep_model()[k][0] - m@) &&
            (d_old.deep_model()[i][0] != INF@ ==> d.deep_model()[i][x@] <= d_old.deep_model()[i][k] + d.deep_model()[k][x@]) &&
            (d.deep_model()[i][x@] != INF@ ==> d_old.deep_model()[i][0] != INF@) &&
            (d.deep_model()[i][x@] != INF@ ==> d.deep_model()[i][x@] <= d.deep_model()[i][k] + d.deep_model()[k][x@])
    }
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[ensures(
    forall<i:Int, j:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= j && j < n@ && j != x@ ==>
        triangle_inequality(d_old.deep_model(), n@, i, j, 0) &&
        (d_old.deep_model()[i][j] == INF@ ==> d_old.deep_model()[i][0] == INF@ || d_old.deep_model()[0][j] == INF@) &&
        (d_old.deep_model()[i][j] != INF@ ==> d_old.deep_model()[i][j] <= d_old.deep_model()[i][0] + d_old.deep_model()[0][j])
)]
fn lem_for_lem_for_reset_110(d_old: &Vec<Vec<i64>>, n: usize, x: usize) {}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= j && j < n@ && j != x@ &&
        k == x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_110(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ &&
            k == x@ ==>
            (d_old.deep_model()[i][0] == INF@ ==> d.deep_model()[i][x@] == INF@) &&
            (d_old.deep_model()[i][0] != INF@ ==> d.deep_model()[i][x@] == d_old.deep_model()[i][0] - m@) &&
            (d_old.deep_model()[0][j] == INF@ ==> d.deep_model()[x@][j] == INF@) &&
            (d_old.deep_model()[0][j] != INF@ ==> d.deep_model()[x@][j] == d_old.deep_model()[0][j] + m@)
    }
    lem_for_lem_for_reset_110(&d_old, n, x);
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ &&
            k == x@ ==>
            (d_old.deep_model()[i][j] == INF@ ==> d_old.deep_model()[i][0] == INF@ || d_old.deep_model()[0][j] == INF@) &&
            (d.deep_model()[i][j] == INF@ ==> d.deep_model()[i][x@] == INF@ || d.deep_model()[x@][j] == INF@) &&
            (d_old.deep_model()[i][j] != INF@ ==> d_old.deep_model()[i][j] <= d_old.deep_model()[i][0] + d_old.deep_model()[0][j]) &&
            (d.deep_model()[i][j] != INF@ ==> d.deep_model()[i][j] <= d.deep_model()[i][x@] + d.deep_model()[x@][j])
    }
}

#[requires(is_canonical(d_old.deep_model(), n@))]
#[requires(is_dbm(d.deep_model(), n@))]
#[requires(1 <= x@ && x@ < n@)]
#[requires(0 <= m@ && m@ < BOUND@)]
#[requires(reset_precondition(d, d_old, n, x, m))]
#[ensures(
    forall<i:Int, j:Int, k:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= j && j < n@ && j != x@ &&
        0 <= k && k < n@ && k != x@ ==>
        triangle_inequality(d.deep_model(), n@, i, j, k)
)]
fn lem_for_reset_111(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d_old.deep_model(), n@, i, j, k) &&
            d.deep_model()[i][j] == d_old.deep_model()[i][j] &&
            d.deep_model()[i][k] == d_old.deep_model()[i][k] &&
            d.deep_model()[k][j] == d_old.deep_model()[k][j]
    }
}

// 処理に失敗したらfalseを返す。例えば、処理の途中でオーバーフローが起きそうなときなど。
// 正常に処理が完了すればtrueを返す。
#[open]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(1 <= x@ && x@ < n@)] // ゼロを書き換えるような使い方はしない
#[requires(0 <= m@ && m@ < BOUND@)] // 更新する時刻は上限を超えない範囲であり、しかも正の値となる
#[requires(is_canonical(d.deep_model(), n@))]
#[ensures(
    forall<i:Int, j:Int>
        0 <= i && i < n@ && i != x@ &&
        0 <= j && j < n@ && j != x@ ==>
        (^d).deep_model()[i][j] == (*d).deep_model()[i][j]
)]
#[ensures(
    forall<i:Int>
        0 <= i && i < n@ && i != x@ ==>
        ((*d).deep_model()[0][i] == INF@ ==> (^d).deep_model()[x@][i] == INF@) &&
        ((*d).deep_model()[0][i] != INF@ ==> (^d).deep_model()[x@][i] == (*d).deep_model()[0][i] + m@) &&
        ((*d).deep_model()[i][0] == INF@ ==> (^d).deep_model()[i][x@] == INF@) &&
        ((*d).deep_model()[i][0] != INF@ ==> (^d).deep_model()[i][x@] == (*d).deep_model()[i][0] - m@)
)]
#[ensures((^d).deep_model()[x@][x@] == (*d).deep_model()[x@][x@])]
#[ensures(is_canonical((^d).deep_model(), n@))]
pub fn reset(d: &mut Vec<Vec<i64>>, n: usize, x: usize, m: i64) {
    let d_old = snapshot! { d };

    // #[invariant(is_dbm(d.deep_model(), n@))]
    #[invariant(2 <= n@)]
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
        d.deep_model()[i][j] == d_old.deep_model()[i][j]
    )]
    // d[0][i] + mの想定される範囲としては（mが正なので）(-BOUND, BOUND), [BOUND, INF), [INF, INF]
    // ここが問題になっているみたい、、、
    #[invariant(forall<i:Int>
        0 <= i && i < produced.len() && i != x@ ==>
        (d_old.deep_model()[0][i] == INF@ ==> d.deep_model()[x@][i] == INF@) &&
        (d_old.deep_model()[0][i] != INF@ ==> d.deep_model()[x@][i] == d_old.deep_model()[0][i] + m@)
    )]
    #[invariant(forall<i:Int>
        0 <= i && i < produced.len() && i != x@ ==>
        (d_old.deep_model()[i][0] == INF@ ==> d.deep_model()[i][x@] == INF@) &&
        (d_old.deep_model()[i][0] != INF@ ==> d.deep_model()[i][x@] == d_old.deep_model()[i][0] - m@)
    )]
    #[invariant(d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@])]
    for i in 0..n {
        if i != x {
            if d[0][i] == INF {
                d[x][i] = INF;
            } else {
                // this condition holds, and overflow can't be caused.
                proof_assert! { -BOUND@ < d.deep_model()[0][i@] && d.deep_model()[0][i@] <= 0 };
                d[x][i] = d[0][i] + m;
            }
    
            if d[i][0] == INF {
                d[i][x] = INF;
            } else {
                // this condition holds, and overflow can't be caused.
                proof_assert! { 0 <= d.deep_model()[i@][0] && d.deep_model()[i@][0] < BOUND@ };
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
            (d_old.deep_model()[0][i] == INF@ ==> d.deep_model()[x@][i] == INF@) &&
            (d_old.deep_model()[0][i] != INF@ ==> d.deep_model()[x@][i] == d_old.deep_model()[0][i] + m@)
    };
    proof_assert! {
        forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d_old.deep_model()[i][0] == INF@ ==> d.deep_model()[i][x@] == INF@) &&
            (d_old.deep_model()[i][0] != INF@ ==> d.deep_model()[i][x@] == d_old.deep_model()[i][0] - m@)
    };
    proof_assert! {
        d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@]
    }

    // (i, j, k)が0かどうかで場合分け
    pearlite! { lem_for_reset_000(&d, &d_old, n, x, m) }; // i==x && j==x && k==x
    pearlite! { lem_for_reset_001(&d, &d_old, n, x, m) }; // i==x && j==x && k!=x
    pearlite! { lem_for_reset_010(&d, &d_old, n, x, m) }; // i==x && j!=x && k==x
    pearlite! { lem_for_reset_011(&d, &d_old, n, x, m) }; // i==x && j!=x && k!=x
    pearlite! { lem_for_reset_100(&d, &d_old, n, x, m) }; // i!=x && j==x && k==x
    pearlite! { lem_for_reset_101(&d, &d_old, n, x, m) }; // i!=x && j==x && k!=x
    pearlite! { lem_for_reset_110(&d, &d_old, n, x, m) }; // i!=x && j!=x && k==x
    pearlite! { lem_for_reset_111(&d, &d_old, n, x, m) }; // i!=x && j!=x && k!=x

    proof_assert! {
        forall<i:Int, j:Int, k:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ &&
            0 <= k && k < n@ && k != x@ ==>
            triangle_inequality(d.deep_model(), n@, i, j, k)
    }

}
