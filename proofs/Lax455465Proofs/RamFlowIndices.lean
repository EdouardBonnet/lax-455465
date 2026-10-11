import Lax455465Proofs.RamArithmetic

namespace Lax455465Proofs.RamFlowIndices

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def column : Com := .seq (.assign "lp.offset" (.sub (.var "lp.j") (.lit 1)))
  (.seq (.assign "lp.arcCommodity" (.div (.var "lp.offset") (.var "lp.n2")))
    (.seq (.assign "lp.arc" (.sub (.var "lp.offset")
      (.mul (.var "lp.arcCommodity") (.var "lp.n2"))))
      (.seq (.assign "lp.arcSource" (.div (.var "lp.arc") (.var "lp.n")))
        (.assign "lp.arcTarget" (.sub (.var "lp.arc")
          (.mul (.var "lp.arcSource") (.var "lp.n")))))))

theorem column_spec (B n n2 j : ℕ) (h1 : 1 < B) (hn : n < B) (hn2 : n2 < B) (hj : j < B) :
    Spec B (fun σ => σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n2 ∧ σ.vars "lp.j" = j) column
      (fun _ τ => τ.vars "lp.arcCommodity" = (j-1)/n2 ∧ τ.vars "lp.arc" = (j-1)%n2 ∧
        τ.vars "lp.arcSource" = ((j-1)%n2)/n ∧ τ.vars "lp.arcTarget" = ((j-1)%n2)%n) 24 := by
  have ho : j-1 < B := (Nat.sub_le _ _).trans_lt hj
  have hac : (j-1)/n2 < B := (Nat.div_le_self _ _).trans_lt ho
  have hacp : (j-1)/n2*n2 < B := (Nat.div_mul_le_self _ _).trans_lt ho
  have har : (j-1)%n2 < B := (Nat.mod_le _ _).trans_lt ho
  have has : ((j-1)%n2)/n < B := (Nat.div_le_self _ _).trans_lt har
  have hasp : ((j-1)%n2)/n*n < B := (Nat.div_mul_le_self _ _).trans_lt har
  have hat : ((j-1)%n2)%n < B := (Nat.mod_le _ _).trans_lt har
  rintro σ ⟨hσn,hσn2,hσj⟩
  run_vcg
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

def row : Com := .seq (.assign "lp.balanceOffset" (.sub (.var "lp.i") (.var "lp.n2")))
  (.seq (.assign "lp.sign" (.div (.var "lp.balanceOffset") (.var "lp.n3")))
    (.seq (.assign "lp.balance" (.sub (.var "lp.balanceOffset") (.mul (.var "lp.sign") (.var "lp.n3"))))
      (.seq (.assign "lp.commodity" (.div (.var "lp.balance") (.var "lp.n")))
        (.seq (.assign "lp.u" (.sub (.var "lp.balance") (.mul (.var "lp.commodity") (.var "lp.n"))))
          (.seq (.assign "lp.s" (.div (.var "lp.commodity") (.var "lp.n")))
            (.assign "lp.t" (.sub (.var "lp.commodity") (.mul (.var "lp.s") (.var "lp.n")))))))))

theorem row_spec (B n n2 n3 i : ℕ) (hn : n < B) (hn2 : n2 < B) (hn3 : n3 < B) (hi : i < B) :
    Spec B (fun σ => σ.vars "lp.n" = n ∧ σ.vars "lp.n2" = n2 ∧ σ.vars "lp.n3" = n3 ∧
      σ.vars "lp.i" = i) row
      (fun _ τ => τ.vars "lp.sign" = (i-n2)/n3 ∧ τ.vars "lp.balance" = (i-n2)%n3 ∧
        τ.vars "lp.commodity" = ((i-n2)%n3)/n ∧ τ.vars "lp.u" = ((i-n2)%n3)%n ∧
        τ.vars "lp.s" = (((i-n2)%n3)/n)/n ∧ τ.vars "lp.t" = (((i-n2)%n3)/n)%n) 34 := by
  have ho : i-n2 < B := (Nat.sub_le _ _).trans_lt hi
  have hf : (i-n2)/n3 < B := (Nat.div_le_self _ _).trans_lt ho
  have hfp : (i-n2)/n3*n3 < B := (Nat.div_mul_le_self _ _).trans_lt ho
  have hb : (i-n2)%n3 < B := (Nat.mod_le _ _).trans_lt ho
  have hc : ((i-n2)%n3)/n < B := (Nat.div_le_self _ _).trans_lt hb
  have hcp : ((i-n2)%n3)/n*n < B := (Nat.div_mul_le_self _ _).trans_lt hb
  have hu : ((i-n2)%n3)%n < B := (Nat.mod_le _ _).trans_lt hb
  have hs : (((i-n2)%n3)/n)/n < B := (Nat.div_le_self _ _).trans_lt hc
  have hsp : (((i-n2)%n3)/n)/n*n < B := (Nat.div_mul_le_self _ _).trans_lt hc
  have ht : (((i-n2)%n3)/n)%n < B := (Nat.mod_le _ _).trans_lt hc
  rintro σ ⟨hσn,hσn2,hσn3,hσi⟩
  run_vcg
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

end Lax455465Proofs.RamFlowIndices
