import Lax455465Proofs.RamUnsignedBuffer
import Lax455465Proofs.FlowLpIndices
import Lax455465Proofs.RationalDistances

namespace Lax455465Proofs.MetricMatrix

open DirectedFlowLP
open scoped NNRat

abbrev Matrix (n : ℕ) := Fin n → Fin n → ℚ≥0

def values {n : ℕ} (d : Matrix n) : List ℚ≥0 :=
  List.ofFn fun e : Fin (n*n) => d ((edgeIndex n).symm e).1 ((edgeIndex n).symm e).2

@[simp] theorem length_values {n : ℕ} (d : Matrix n) : (values d).length = n*n := List.length_ofFn

theorem value_at {n : ℕ} (d : Matrix n) (u v : Fin n) :
    (values d)[(edgeIndex n (u,v)).val]'(by simpa only [length_values] using (edgeIndex n (u,v)).isLt) = d u v := by
  simp only [values,List.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

def step {n : ℕ} (d : Matrix n) (p : Fin n) : Matrix n :=
  fun u v => min (d u v) (d u p+d p v)

def rational {n : ℕ} (d : Matrix n) : RationalDistances.Distance n := fun u v => (d u v : ℚ)

theorem rational_step {n : ℕ} (d : Matrix n) (p : Fin n) :
    rational (step d p) = RationalDistances.step (rational d) p := by
  funext u v
  simp only [rational,step,RationalDistances.step,NNRat.coe_min,NNRat.coe_add]

def iterate {n : ℕ} (d : Matrix n) : List (Fin n) → Matrix n
  | [] => d
  | p :: ps => iterate (step d p) ps

theorem iterate_append {n : ℕ} (d : Matrix n) (ps qs : List (Fin n)) :
    iterate d (ps ++ qs) = iterate (iterate d ps) qs := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => exact ih (step d p)

def afterPivots {n : ℕ} (d : Matrix n) (k : ℕ) : Matrix n :=
  iterate d ((List.finRange n).take k)

theorem prefix_zero {n : ℕ} (d : Matrix n) : afterPivots d 0 = d := rfl

theorem prefix_succ {n : ℕ} (d : Matrix n) (k : ℕ) (hk : k < n) :
    afterPivots d (k+1) = step (afterPivots d k) (⟨k,hk⟩ : Fin n) := by
  have hi : k < (List.finRange n).length := by simpa using hk
  simp only [afterPivots,List.take_succ_eq_append_getElem hi,iterate_append,iterate,List.getElem_finRange]
  congr 1

theorem rational_iterate {n : ℕ} (d : Matrix n) (ps : List (Fin n)) :
    rational (iterate d ps) = RationalDistances.iterate (rational d) ps := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih => simpa only [iterate,RationalDistances.iterate,rational_step] using ih (step d p)

end Lax455465Proofs.MetricMatrix

