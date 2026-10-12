import Lax455465Proofs.UniformCutBounds
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.NNRat.BigOperators

open scoped BigOperators NNRat NNReal
namespace Lax455465Proofs.ShortRationalParameters
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ShortPathFlow
open CutSweeps UniformCutBounds

def maximum {n : ℕ} (I : RationalInstance n) : ℚ≥0 :=
  Finset.univ.sup fun v => ∑ u,I.capacity v u

theorem row_le {n : ℕ} (I : RationalInstance n) (v : Fin n) :
    (∑ u,(I.capacity v u : ℚ)) ≤ (maximum I : ℚ) := by
  have hh : (∑ u,I.capacity v u) ≤ maximum I :=
    Finset.le_sup (f := fun v => ∑ u,I.capacity v u) (Finset.mem_univ v)
  exact_mod_cast hh

theorem maximum_cast {n : ℕ} (I : RationalInstance n) (hn : 0 < n) :
    (maximum I : ℝ≥0)=maxIncidentCapacity I.network := by
  let C : Set ℝ≥0 := {r | ∃ v : Fin n,(∑ u,I.network.capacity v u)=r}
  have hCfin : C.Finite := by
    exact Set.finite_range (fun v : Fin n => ∑ u,I.network.capacity v u)
  let v₀ : Fin n := ⟨0,hn⟩
  have hCne : C.Nonempty := ⟨∑ u,I.network.capacity v₀ u,v₀,rfl⟩
  apply le_antisymm
  · obtain ⟨v,_,hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin n))
      ⟨v₀,Finset.mem_univ _⟩ (fun v => ∑ u,I.capacity v u)
    have hsum : (maximum I : ℝ≥0)=∑ u,I.network.capacity v u := by
      change ((Finset.univ.sup (fun v => ∑ u,I.capacity v u) : ℚ≥0) : ℝ≥0)=_
      rw [hv]
      simp [RationalInstance.network,NNRat.cast_sum]
    rw [hsum]
    exact le_csSup hCfin.bddAbove (show (∑ u,I.network.capacity v u)∈C from ⟨v,rfl⟩)
  · apply csSup_le hCne
    rintro r ⟨v,rfl⟩
    have hh := row_le I v
    change (∑ u,(I.capacity v u : ℝ≥0)) ≤ _
    exact_mod_cast hh

/-- The public real infimum is attained by a rational cut ratio. This
parameter is used only in the analysis, never computed by cut enumeration. -/
theorem exists_sparsest {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) : ∃ s : ℚ,(s : ℝ)=(sparsestCut I.network I.weights : ℝ) ∧ CutLower I s := by
  let C : Set ℝ≥0 := {r | ∃ S : Finset (Fin n),AdmissibleCut I.weights S ∧ ratioCost I.network I.weights S=r}
  have hCfin : C.Finite := (Set.finite_range (ratioCost I.network I.weights)).subset (by
    rintro r ⟨S,_,rfl⟩
    exact ⟨S,rfl⟩)
  let v : Fin n := ⟨0,by omega⟩
  have hCne : C.Nonempty := ⟨ratioCost I.network I.weights {v},{v},
    (admissibleQ_iff I {v}).mp (singleton_admissible I hw hn v),rfl⟩
  obtain ⟨S,hS,he⟩ := hCne.csInf_mem hCfin
  have hs : (ratioQ I S : ℝ)=(sparsestCut I.network I.weights : ℝ) := by
    rw [ratioQ_cast]
    exact congrArg (fun q : ℝ≥0 => (q : ℝ)) he
  refine ⟨ratioQ I S,hs,?_⟩
  intro T hT
  have hh := sparsest_le I T hT
  rw [←hs] at hh
  exact_mod_cast hh

/-- Positive expansion gives q=Cmax/(n S) ≥ 1/2 and positive maximum capacity. -/
theorem normalized_expansion {n : ℕ} (I : RationalInstance n) (hw : ∀ v,I.weight v=1)
    (hn : 2 ≤ n) (s : ℚ) (hs : 0 < s) (hcut : CutLower I s) :
    0 < (maximum I : ℚ) ∧
      1/2 ≤ (maximum I : ℚ)/((n : ℚ)*s) ∧
      ((maximum I : ℚ)/((n : ℚ)*s))*n*s=(maximum I : ℚ) := by
  have hh := expansion_bound I hw hn s (maximum I : ℚ) hcut (row_le I)
  have hnq : (2 : ℚ) ≤ n := by exact_mod_cast hn
  have hns : 0 < (n : ℚ)*s := by positivity
  refine ⟨?_,?_,?_⟩
  · have : 0 < s*((n : ℚ)-1) := mul_pos hs (by linarith)
    linarith
  · apply (le_div_iff₀ hns).mpr
    nlinarith
  · field_simp

end Lax455465Proofs.ShortRationalParameters
