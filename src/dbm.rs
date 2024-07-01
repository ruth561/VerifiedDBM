use creusot_contracts::*;
use crate::{BOUND, INF};

#[logic]
#[open]
pub fn validx(n: Int, i: Int, j: Int, k: Int) -> bool {
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
#[open]
pub fn is_dbm(dbm: Seq<Seq<Int>>, n: Int) -> bool {
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
#[open]
pub fn is_canonical(dbm: Seq<Seq<Int>>, n: Int) -> bool {
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
#[open]
#[requires(is_dbm(dbm, n))]
#[requires(0 <= i && i < n)]
#[requires(0 <= j && j < n)]
#[requires(0 <= k && k < n)]
pub fn triangle_inequality(dbm: Seq<Seq<Int>>, n: Int, i: Int, j: Int, k: Int) -> bool {
    pearlite! {
        (dbm[i][j] != INF@ ==> -BOUND@ < dbm[i][j] && dbm[i][j] < BOUND@) &&
        (dbm[i][k] != INF@ ==> -BOUND@ < dbm[i][k] && dbm[i][k] < BOUND@) &&
        (dbm[k][j] != INF@ ==> -BOUND@ < dbm[k][j] && dbm[k][j] < BOUND@) &&
        (dbm[i][j] == INF@ ==> dbm[i][k] == INF@ || dbm[k][j] == INF@) &&
        (dbm[i][j] != INF@ ==> dbm[i][j] <= dbm[i][k] + dbm[k][j])
    }
}

// === utility ===

#[open]
#[trusted]
#[ensures(is_canonical(result.deep_model(), result@.len()))]
pub fn get_dbm() -> Vec<Vec<i64>> {
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
#[open]
#[ensures(result == is_dbm(dbm.deep_model(), dbm@.len()))]
pub fn check_is_dbm(dbm: &Vec<Vec<i64>>) -> bool {
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
#[open]
#[ensures(result == is_canonical(dbm.deep_model(), dbm@.len()))]
pub fn check_is_canonical(dbm: &Vec<Vec<i64>>) -> bool {
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
