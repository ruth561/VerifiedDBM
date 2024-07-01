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
fn reset_precondition(d: &Vec<Vec<i64>>, d_old: &Vec<Vec<i64>>, n: usize) -> bool {
    pearlite! {
        (forall<i:Int, j:Int>
            0 <= i && i < n@ && i != x@ &&
            0 <= j && j < n@ && j != x@ ==>
            d.deep_model()[i][j] == d_old.deep_model()[i][j]) &&
        (forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d.deep_model()[0][i] + m@ >= BOUND@ ==> d.deep_model()[x@][i] == INF@) &&
            (d.deep_model()[0][i] + m@ <  BOUND@ ==> d.deep_model()[x@][i] == d.deep_model()[0][i] + m@)) &&
        (forall<i:Int>
            0 <= i && i < n@ && i != x@ ==>
            (d.deep_model()[i][0] == INF@         ==> d.deep_model()[i][x@] == INF@) &&
            (d.deep_model()[i][0] - m@ <= -BOUND@ ==> d.deep_model()[i][x@] == -BOUND@ + 1) &&
            (-BOUND@ < d.deep_model()[i][0] - m@ && d.deep_model()[i][0] - m@ < BOUND@ ==> d.deep_model()[i][x@] == d.deep_model()[i][0] - m@)) &&
        d.deep_model()[x@][x@] == d_old.deep_model()[x@][x@]
    }
}


#[open]
#[requires(2 <= n@ && n@ < MAX_NODE@)]
#[requires(1 <= x@ && x@ < n@)] // ゼロを書き換えるような使い方はしない
#[requires(0 <= m@ && m@ < BOUND@)] // 更新する時刻は上限を超えない範囲であり、しかも正の値となる
#[requires(is_canonical(d.deep_model(), n@))]
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
