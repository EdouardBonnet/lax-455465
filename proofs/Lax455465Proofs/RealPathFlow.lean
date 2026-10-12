import Lax455465Proofs.RealFlowDecomposition
import Lax455465Proofs.PathCertificateInterpretation

open scoped BigOperators NNReal
namespace Lax455465Proofs.RealPathFlow
open Lax455465.ConcurrentFlow RealFlowDecomposition
open PathCertificateInterpretation (arcLoad_add arcLoad_single routed_add routed_single)

noncomputable def flow {n : ℕ} : Records (Fin n) → PathFlow n
  | [] => 0
  | r :: rs => Finsupp.single r.1 r.2.toNNReal + flow rs

theorem arcLoad_cast {n : ℕ} (rs : Records (Fin n)) (h : ∀ r ∈ rs, 0 ≤ r.2) (u v : Fin n) :
    (arcLoad (flow rs) u v : ℝ) = load rs u v := by
  induction rs with
  | nil => simp [flow, arcLoad, load]
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht : ∀ r' ∈ rs, 0 ≤ r'.2 := fun r' hr' => h r' (by simp [hr'])
    rw [flow, arcLoad_add, arcLoad_single]
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast,
      Real.coe_toNNReal _ hr, ih ht, load_cons, RealPathCounting.count, PathSimplification.arcs]

theorem routed_self {n : ℕ} {s t : Fin n} {rs : Records (Fin n)}
    (h : Valid s t rs) : (routed (flow rs) s t : ℝ) = mass rs := by
  induction rs with
  | nil => simp [flow, routed, mass]
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht : Valid s t rs := fun r' hr' => h r' (by simp [hr'])
    rw [flow, routed_add, routed_single, if_pos ⟨hr.2.1, hr.2.2.1⟩]
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hr.1.le, ih ht, mass_cons]

theorem support_mem {n : ℕ} (rs : Records (Fin n)) (xs : List (Fin n))
    (h : xs ∈ (flow rs).support) : ∃ r ∈ rs, r.1 = xs := by
  induction rs with
  | nil => simp [flow] at h
  | cons r rs ih =>
    rcases Finset.mem_union.mp (Finsupp.support_add h) with hh | hh
    · have he : xs = r.1 := Finset.mem_singleton.mp (Finsupp.support_single_subset hh)
      exact ⟨r, by simp, he.symm⟩
    · obtain ⟨r', hr', he⟩ := ih hh
      exact ⟨r', by simp [hr'], he⟩

theorem isPathFlow {n : ℕ} {s t : Fin n} (hst : s ≠ t) {rs : Records (Fin n)}
    (h : Valid s t rs) : IsPathFlow (flow rs) := by
  intro xs hxs
  obtain ⟨r, hr, rfl⟩ := support_mem rs xs hxs
  have hh := h r hr
  refine ⟨?_, hh.2.2.2⟩
  cases he : r.1 with
  | nil => simp [he] at hh
  | cons u xs =>
    cases xs with
    | nil =>
      have hs : u = s := by simpa [he] using hh.2.1
      have ht : u = t := by simpa [he] using hh.2.2.1
      exact (hst (hs.symm.trans ht)).elim
    | cons v xs => simp [he]

end Lax455465Proofs.RealPathFlow
