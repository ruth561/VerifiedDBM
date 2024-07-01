use creusot_contracts::*;
use crate::{BOUND, INF, MAX_NODE};
use crate::dbm::*;

// x==2 のケース
// [[  d00, ---,   d00, ... , ---],
//  [  d10, ---,   d10, ... , ---],
//  [  INF, INF,     0, ... , INF],
//  ...
//  [  dn0, ---,   dn0, ... , ---]]
#[open]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(1 <= x@ && x@ < n@)] // zero clockを書き換えるような使い方はしない
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
pub fn free(d: &mut Vec<Vec<i64>>, n: usize, x: usize) {
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

    // i==xのケース
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
