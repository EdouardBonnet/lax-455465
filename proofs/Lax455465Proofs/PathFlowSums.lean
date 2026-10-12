import Lax455465Proofs.RealPathFlow

open scoped BigOperators NNReal
namespace Lax455465Proofs.PathFlowSums
open Lax455465.ConcurrentFlow
open PathCertificateInterpretation (arcLoad_add routed_add)

theorem isPathFlow_add {n : ℕ} {F G : PathFlow n} (hF : IsPathFlow F) (hG : IsPathFlow G) :
    IsPathFlow (F+G) := by
  intro xs hxs
  rcases Finset.mem_union.mp (Finsupp.support_add hxs) with h | h
  · exact hF xs h
  · exact hG xs h

theorem isPathFlow_sum {n : ℕ} {ι : Type*} (S : Finset ι) (F : ι → PathFlow n)
    (h : ∀ i ∈ S, IsPathFlow (F i)) : IsPathFlow (∑ i ∈ S, F i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [IsPathFlow]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact isPathFlow_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem arcLoad_sum {n : ℕ} {ι : Type*} (S : Finset ι) (F : ι → PathFlow n) (u v : Fin n) :
    arcLoad (∑ i ∈ S, F i) u v = ∑ i ∈ S, arcLoad (F i) u v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [arcLoad]
  | @insert i S hi ih => rw [Finset.sum_insert hi, arcLoad_add, ih, Finset.sum_insert hi]

theorem routed_sum {n : ℕ} {ι : Type*} (S : Finset ι) (F : ι → PathFlow n) (s t : Fin n) :
    routed (∑ i ∈ S, F i) s t = ∑ i ∈ S, routed (F i) s t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [routed]
  | @insert i S hi ih => rw [Finset.sum_insert hi, routed_add, ih, Finset.sum_insert hi]

end Lax455465Proofs.PathFlowSums
