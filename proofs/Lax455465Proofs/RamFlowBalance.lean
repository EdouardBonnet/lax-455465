import Lax455465Proofs.RamFlowDemand
import Lax455465Proofs.RamFlowUnits
import Lax455465Proofs.FlowLpFlat

namespace Lax455465Proofs.RamFlowBalance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP FlowLpIndices
open scoped NNRat

def command : Com := .ite (.eq (.var "lp.j") (.lit 0)) RamFlowDemand.command RamFlowUnits.arc

/-- Actual retained runtime indices, not supplied mathematical witnesses. -/
def Ready {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (s t u : Fin n) (v : Variable n) (σ : Env) : Prop :=
  Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
    σ.vars "lp.s" = s.val ∧ σ.vars "lp.t" = t.val ∧ σ.vars "lp.u" = u.val ∧
    σ.vars "lp.commodity" = (edgeIndex n (s,t)).val ∧
    σ.vars "lp.j" = (variableIndex n v).val ∧
    σ.vars "lp.arcCommodity" = ((variableIndex n v).val-1)/(n*n) ∧
    σ.vars "lp.arcSource" = (((variableIndex n v).val-1)%(n*n))/n ∧
    σ.vars "lp.arcTarget" = (((variableIndex n v).val-1)%(n*n))%n

private theorem demand_eq {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (s t u : Fin n) :
    RamFlowDemand.value s.val t.val u.val ((I.weight s : ℚ)*(I.weight t : ℚ)) =
      -DirectedFlowLP.divergence I s t u := by
  by_cases hst : s=t
  · subst t; simp [RamFlowDemand.value,DirectedFlowLP.divergence]
  · have hst' : s.val ≠ t.val := fun h => hst (Fin.ext h)
    by_cases hus : u=s
    · subst u
      have hst'' : ¬s=t := hst
      simp [RamFlowDemand.value,DirectedFlowLP.divergence,hst,hst']
    · have hus' : u.val ≠ s.val := fun h => hus (Fin.ext h)
      by_cases hut : u=t
      · subst u; simp [RamFlowDemand.value,DirectedFlowLP.divergence,hst,hst',hus,hus']
      · have hut' : u.val ≠ t.val := fun h => hut (Fin.ext h)
        simp [RamFlowDemand.value,DirectedFlowLP.divergence,hst,hst',hus,hus',hut,hut']

/-- Native evaluation of any conservation-row coefficient, including
zero demands and self-loops. The subsequent row-sign command supplies its
paired negative row. -/
theorem command_spec (B M : ℕ) {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (s t u : Fin n) (v : Variable n) (hB : 2*M^2+3 < B)
    (hni : 2*n+1 < B) (hn2 : n*n < B) (hv : (variableIndex n v).val < B)
    (hnum : ∀ z, (I.weight z).num ≤ M) (hden : ∀ z, (I.weight z).den ≤ M) :
    Spec B (Ready I s t u v) command
      (fun _ τ => FractionOutput (DirectedFlowLP.balanceCoefficient I ((s,t),u) v) τ)
      (36*(M*M).size+124) := by
  have h1 : 1 < B := by nlinarith
  have hu : u.val < B := by have := u.isLt; omega
  have hs : s.val < B := by have := s.isLt; omega
  have ht : t.val < B := by have := t.isLt; omega
  have hcommodity : (edgeIndex n (s,t)).val < B := (edgeIndex n (s,t)).isLt.trans hn2
  rintro σ ⟨hp,hσs,hσt,hσu,hσcommodity,hσj,hσac,hσas,hσat⟩
  cases v with
  | inl v =>
    have hj0 : σ.vars "lp.j" = 0 := hσj.trans (value_variable v)
    have hcond : (Cond.eq (.var "lp.j") (.lit 0)).evalB B σ = some true := by
      rw [evalB_condEq_iff]
      exact ⟨0,0,by rw [evalB_var_iff]; simp [hj0]; omega,evalB_lit (by omega),by decide⟩
    have hprod := RamFlowDemand.command_spec B M (List.ofFn I.weight) s.val t.val u.val
      (by simp) (by simp) hu hB
      (by have := s.isLt; omega) (by have := t.isLt; omega)
      (by simpa using hnum s) (by simpa using hden s) (by simpa using hnum t) (by simpa using hden t)
    obtain ⟨τ,hr,hpost⟩ := hprod σ ⟨hp,hσs,hσt,hσu⟩
    have hdprod : (I.weight s).den*(I.weight t).den ≤ M*M := Nat.mul_le_mul (hden s) (hden t)
    have hsz := Nat.size_le_size hdprod
    refine ⟨τ,(Run.ite_true hcond hr).mono (by simp only [Cond.size,Expr.size,List.getElem_ofFn,Fin.eta]; omega), ?_⟩
    simpa only [List.getElem_ofFn,demand_eq,DirectedFlowLP.balanceCoefficient] using hpost
  | inr a =>
    rcases a with ⟨⟨s',t'⟩,⟨u',v'⟩⟩
    have hjpos : (variableIndex n (.inr ((s',t'),(u',v')))).val ≠ 0 := by rw [arc_variable]; omega
    have hcond : (Cond.eq (.var "lp.j") (.lit 0)).evalB B σ = some false := by
      rw [evalB_condEq_iff]
      exact ⟨(variableIndex n (.inr ((s',t'),(u',v')))).val,0,
        by rw [evalB_var_iff]; exact ⟨hσj.symm,hσj ▸ hv⟩,evalB_lit (by omega),by simp [hjpos]⟩
    have hac : σ.vars "lp.arcCommodity" = (edgeIndex n (s',t')).val := by rwa [arc_div] at hσac
    have has : σ.vars "lp.arcSource" = u'.val := by rwa [arc_mod,edge_div] at hσas
    have hat : σ.vars "lp.arcTarget" = v'.val := by rwa [arc_mod,edge_mod] at hσat
    obtain ⟨τ,hr,hpost⟩ := RamFlowUnits.arc_spec B (edgeIndex n (s',t')).val
      (edgeIndex n (s,t)).val u'.val v'.val u.val h1 ((edgeIndex n (s',t')).isLt.trans hn2)
      hcommodity (by have := u'.isLt; omega) (by have := v'.isLt; omega) hu σ
        ⟨hac,hσcommodity,has,hat,hσu⟩
    refine ⟨τ,(Run.ite_false hcond hr).mono (by simp [Cond.size,Expr.size]), ?_⟩
    simpa only [RamFlowUnits.arcValue,DirectedFlowLP.balanceCoefficient,Fin.val_inj,
      (edgeIndex n).apply_eq_iff_eq] using hpost

end Lax455465Proofs.RamFlowBalance
