import Lax455465Proofs.RamArithmetic
import Lax455465Proofs.LayeredLpFlat

namespace Lax455465Proofs.RamLayeredIndices
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def column : Com :=
  .seq (.assign "short.offset" (.sub (.var "lp.j") (.lit 1)))
  (.seq (.assign "short.arcCommodity" (.div (.var "short.offset") (.var "short.layerArcs")))
  (.seq (.assign "short.arcRest" (.sub (.var "short.offset") (.mul (.var "short.arcCommodity") (.var "short.layerArcs"))))
  (.seq (.assign "short.arcLayer" (.div (.var "short.arcRest") (.var "lp.n2")))
  (.seq (.assign "short.arcEdge" (.sub (.var "short.arcRest") (.mul (.var "short.arcLayer") (.var "lp.n2"))))
  (.seq (.assign "short.arcSource" (.div (.var "short.arcEdge") (.var "lp.n")))
    (.assign "short.arcTarget" (.sub (.var "short.arcEdge") (.mul (.var "short.arcSource") (.var "lp.n")))))))))

theorem column_spec (B n n2 H j : ℕ) (h1 : 1 < B)
    (hn : n < B) (hn2 : n2 < B) (hH : H < B) (hj : j < B) :
    Spec B (fun σ => σ.vars "lp.n"=n ∧ σ.vars "lp.n2"=n2 ∧ σ.vars "short.layerArcs"=H ∧ σ.vars "lp.j"=j)
      column (fun _ τ =>
        τ.vars "short.arcCommodity"=(j-1)/H ∧ τ.vars "short.arcRest"=(j-1)%H ∧
        τ.vars "short.arcLayer"=((j-1)%H)/n2 ∧ τ.vars "short.arcEdge"=((j-1)%H)%n2 ∧
        τ.vars "short.arcSource"=(((j-1)%H)%n2)/n ∧ τ.vars "short.arcTarget"=(((j-1)%H)%n2)%n) 34 := by
  have ho : j-1 < B := (Nat.sub_le _ _).trans_lt hj
  have hac : (j-1)/H < B := (Nat.div_le_self _ _).trans_lt ho
  have hacp : (j-1)/H*H < B := (Nat.div_mul_le_self _ _).trans_lt ho
  have har : (j-1)%H < B := (Nat.mod_le _ _).trans_lt ho
  have hk : ((j-1)%H)/n2 < B := (Nat.div_le_self _ _).trans_lt har
  have hkp : ((j-1)%H)/n2*n2 < B := (Nat.div_mul_le_self _ _).trans_lt har
  have he : ((j-1)%H)%n2 < B := (Nat.mod_le _ _).trans_lt har
  have hu : (((j-1)%H)%n2)/n < B := (Nat.div_le_self _ _).trans_lt he
  have hup : (((j-1)%H)%n2)/n*n < B := (Nat.div_mul_le_self _ _).trans_lt he
  have hv : (((j-1)%H)%n2)%n < B := (Nat.mod_le _ _).trans_lt he
  rintro σ ⟨hσn,hσn2,hσH,hσj⟩
  run_vcg
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

def row : Com :=
  .seq (.assign "short.rowOffset" (.sub (.var "lp.i") (.var "lp.n2")))
  (.seq (.assign "short.rowSign" (.div (.var "short.rowOffset") (.var "short.balances")))
  (.seq (.assign "short.rowBalance" (.sub (.var "short.rowOffset") (.mul (.var "short.rowSign") (.var "short.balances"))))
  (.seq (.assign "short.rowCommodity" (.div (.var "short.rowBalance") (.var "short.layerVertices")))
  (.seq (.assign "short.rowRest" (.sub (.var "short.rowBalance") (.mul (.var "short.rowCommodity") (.var "short.layerVertices"))))
  (.seq (.assign "short.rowLayer" (.div (.var "short.rowRest") (.var "lp.n")))
  (.seq (.assign "short.rowVertex" (.sub (.var "short.rowRest") (.mul (.var "short.rowLayer") (.var "lp.n"))))
  (.seq (.assign "short.s" (.div (.var "short.rowCommodity") (.var "lp.n")))
    (.assign "short.t" (.sub (.var "short.rowCommodity") (.mul (.var "short.s") (.var "lp.n")))))))))))

theorem row_spec (B n n2 H M i : ℕ) (hn : n < B) (hn2 : n2 < B)
    (hH : H < B) (hM : M < B) (hi : i < B) :
    Spec B (fun σ => σ.vars "lp.n"=n ∧ σ.vars "lp.n2"=n2 ∧
      σ.vars "short.layerVertices"=H ∧ σ.vars "short.balances"=M ∧ σ.vars "lp.i"=i)
      row (fun _ τ =>
        τ.vars "short.rowSign"=(i-n2)/M ∧ τ.vars "short.rowBalance"=(i-n2)%M ∧
        τ.vars "short.rowCommodity"=((i-n2)%M)/H ∧ τ.vars "short.rowRest"=((i-n2)%M)%H ∧
        τ.vars "short.rowLayer"=(((i-n2)%M)%H)/n ∧ τ.vars "short.rowVertex"=(((i-n2)%M)%H)%n ∧
        τ.vars "short.s"=(((i-n2)%M)/H)/n ∧ τ.vars "short.t"=(((i-n2)%M)/H)%n) 44 := by
  have ho : i-n2 < B := (Nat.sub_le _ _).trans_lt hi
  have hf : (i-n2)/M < B := (Nat.div_le_self _ _).trans_lt ho
  have hfp : (i-n2)/M*M < B := (Nat.div_mul_le_self _ _).trans_lt ho
  have hb : (i-n2)%M < B := (Nat.mod_le _ _).trans_lt ho
  have hc : ((i-n2)%M)/H < B := (Nat.div_le_self _ _).trans_lt hb
  have hcp : ((i-n2)%M)/H*H < B := (Nat.div_mul_le_self _ _).trans_lt hb
  have hr : ((i-n2)%M)%H < B := (Nat.mod_le _ _).trans_lt hb
  have hk : (((i-n2)%M)%H)/n < B := (Nat.div_le_self _ _).trans_lt hr
  have hkp : (((i-n2)%M)%H)/n*n < B := (Nat.div_mul_le_self _ _).trans_lt hr
  have hu : (((i-n2)%M)%H)%n < B := (Nat.mod_le _ _).trans_lt hr
  have hs : (((i-n2)%M)/H)/n < B := (Nat.div_le_self _ _).trans_lt hc
  have hsp : (((i-n2)%M)/H)/n*n < B := (Nat.div_mul_le_self _ _).trans_lt hc
  have ht : (((i-n2)%M)/H)%n < B := (Nat.mod_le _ _).trans_lt hc
  rintro σ ⟨hσn,hσn2,hσH,hσM,hσi⟩
  run_vcg
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

end Lax455465Proofs.RamLayeredIndices
