import Lax455465Proofs.RegionSelection
import Lax455465Proofs.WordSize
import Mathlib.Data.List.FinRange
import Mathlib.Data.NNRat.Defs

namespace Lax455465Proofs.SupportData
open scoped NNRat

def positive (q : ℚ≥0) : Bool := decide (0<q.num)
def count (qs : List ℚ≥0) : ℕ := qs.countP positive

theorem count_le (qs : List ℚ≥0) : count qs ≤ qs.length := List.countP_le_length

theorem count_step (qs : List ℚ≥0) (i : ℕ) (hi : i<qs.length) :
    count (qs.take (i+1)) = count (qs.take i) + if 0<qs[i].num then 1 else 0 := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [count,List.countP_append,List.countP_cons,List.countP_nil,Nat.zero_add,positive,decide_eq_true_eq]

theorem count_support {n : ℕ} (weights : Fin n → ℚ≥0) :
    count (List.ofFn weights) = (RegionSelection.support (fun v => (weights v : ℚ))).card := by
  have hmap : (List.finRange n).map weights = List.ofFn weights := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [count,←hmap,List.countP_map]
  have hp : (fun v => positive (weights v)) = (fun v => decide (0<(weights v : ℚ))) := by
    funext v
    simp only [positive,NNRat.num_pos]
    congr 1
  simp only [Function.comp_def]
  rw [hp,← List.Nodup.card_eq_countP (List.nodup_finRange n)]
  simp [RegionSelection.support]

theorem size_log (p : ℕ) (hp : 0<p) : p.size = Nat.log2 p+1 := by
  have hu : p<2^(Nat.log2 p+1) := by
    simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two p
  have hupper : p.size≤Nat.log2 p+1 := Nat.size_le.mpr hu
  have hlow : 2^Nat.log2 p≤p := by
    simpa only [Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (ne_of_gt hp)
  have hsize : p<2^p.size := Nat.size_le.mp le_rfl
  have hnot : ¬p.size≤Nat.log2 p := by
    intro h
    exact (not_le_of_gt hsize) ((Nat.pow_le_pow_right (by decide : 1≤2) h).trans hlow)
  omega

end Lax455465Proofs.SupportData
