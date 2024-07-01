use creusot_contracts::*;
use crate::{BOUND, INF, MAX_NODE};
use crate::dbm::*;

// 第0列の1行目からn行目までをINFで初期化する操作
// [[---, ---, ... , ---],
//  [INF, ---, ... , ---],
//  [INF, ---, ... , ---],
//  ...
//  [INF, ---, ... , ---]]
#[open]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(is_canonical(d.deep_model(), n@))]
#[ensures(forall<i:Int> 1 <= i && i < n@ ==> (^d).deep_model()[i][0] == INF@)]
#[ensures(d.deep_model()[0][0] == (^d).deep_model()[0][0])]
#[ensures(forall<i:Int, j:Int> 0 <= i && i < n@ && 1 <= j && j < n@ ==> d.deep_model()[i][j] == (^d).deep_model()[i][j])]
#[ensures(is_canonical((^d).deep_model(), n@))]
pub fn up(d: &mut Vec<Vec<i64>>, n: usize) {
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
