import Lax455465Proofs.RegionSelection
import Lax455465Proofs.RamFind
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import Mathlib.Data.NNRat.Defs

namespace Lax455465Proofs.RootData
open scoped NNRat

def predicate (qs : List ℚ≥0) (i : ℕ) : Bool := decide (0 < (qs.getD i 0).num)

theorem map_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem predicate_at {n : ℕ} (weights : Fin n → ℚ≥0) (v : Fin n) :
    predicate (List.ofFn weights) v.val = decide (0 < (weights v : ℚ)) := by
  unfold predicate
  rw [List.getD_eq_get (List.ofFn weights) 0 (⟨v.val,by simpa using v.isLt⟩ : Fin (List.ofFn weights).length)]
  simp only [List.get_eq_getElem,List.getElem_ofFn,Fin.eta]
  congr 1
  rw [NNRat.num_pos]
  exact propext NNRat.coe_lt_coe.symm

/-- The native first-positive-coordinate scan selects precisely the root
chosen by the deterministic residual region loop. -/
theorem first_eq {n : ℕ} (weights : Fin n → ℚ≥0) :
    RamFind.first (predicate (List.ofFn weights)) n =
      (RegionSelection.chooseRoot (fun v => (weights v : ℚ))).map Fin.val := by
  rw [RamFind.first,←map_finRange n,List.find?_map]
  unfold RegionSelection.chooseRoot
  congr 1
  apply List.find?_congr
  intro v hv
  exact predicate_at weights v

end Lax455465Proofs.RootData
