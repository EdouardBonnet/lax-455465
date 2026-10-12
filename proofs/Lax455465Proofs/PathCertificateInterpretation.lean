import Lax455465Proofs.LayeredFlowRecords
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.NNRat.BigOperators

open scoped BigOperators NNRat NNReal
namespace Lax455465Proofs.PathCertificateInterpretation
open Lax455465.RationalEncoding Lax455465.ProductNetwork Lax455465.ConcurrentFlow
open Lax455465.ShortPathFlow AcyclicFlowDecomposition

def certificate {n : ℕ} (f : ℚ) (rs : Records (Fin n)) : FlowCertificate n where
  value := f.toNNRat
  paths := rs.map fun r => (r.1,r.2.toNNRat)

noncomputable def flow {n : ℕ} : Records (Fin n) → PathFlow n
  | [] => 0
  | r::rs => Finsupp.single r.1 (r.2.toNNRat : ℝ≥0)+flow rs

theorem foldl_flow {n : ℕ} (rs : Records (Fin n)) (F : PathFlow n) :
    (rs.map fun r => (r.1,r.2.toNNRat)).foldl
      (fun F r => F+Finsupp.single r.1 (r.2 : ℝ≥0)) F=F+flow rs := by
  induction rs generalizing F with
  | nil => simp [flow]
  | cons r rs ih => simp [flow,ih,add_assoc]

theorem certificate_flow {n : ℕ} (f : ℚ) (rs : Records (Fin n)) :
    (certificate f rs).flow=flow rs := by
  simpa [certificate,FlowCertificate.flow] using foldl_flow rs 0

theorem amount_cast (q : ℚ) (hq : 0 ≤ q) : ((q.toNNRat : ℝ≥0) : ℝ)=(q : ℝ) := by
  change (q.toNNRat : ℝ)=(q : ℝ)
  rw [←Rat.cast_nnratCast,Rat.coe_toNNRat q hq]

theorem arcLoad_add {n : ℕ} (F G : PathFlow n) (u v : Fin n) :
    arcLoad (F+G) u v=arcLoad F u v+arcLoad G u v := by
  simpa only [arcLoad,Finsupp.sum] using
    (Finsupp.sum_add_index' (f := F) (g := G)
      (h := fun xs (w : ℝ≥0) => w*((xs.zip xs.tail).count (u,v) : ℝ≥0))
      (fun _ => by simp) (fun _ _ _ => add_mul _ _ _))

theorem routed_add {n : ℕ} (F G : PathFlow n) (s t : Fin n) :
    routed (F+G) s t=routed F s t+routed G s t := by
  change (F+G).sum (fun xs w => if xs.head?=some s ∧ xs.getLast?=some t then w else 0)=_
  rw [Finsupp.sum_add_index']
  · rfl
  · intro xs
    split_ifs <;> rfl
  · intro xs a b
    split_ifs <;> simp

theorem arcLoad_single {n : ℕ} (xs : List (Fin n)) (w : ℝ≥0) (u v : Fin n) :
    arcLoad (Finsupp.single xs w) u v=w*((xs.zip xs.tail).count (u,v) : ℝ≥0) := by
  simpa only [arcLoad,Finsupp.sum] using
    (Finsupp.sum_single_index (a := xs) (b := w)
      (h := fun ys (w : ℝ≥0) => w*((ys.zip ys.tail).count (u,v) : ℝ≥0)) (by simp))

theorem routed_single {n : ℕ} (xs : List (Fin n)) (w : ℝ≥0) (s t : Fin n) :
    routed (Finsupp.single xs w) s t=if xs.head?=some s ∧ xs.getLast?=some t then w else 0 := by
  change (Finsupp.single xs w).sum
    (fun ys z => if ys.head?=some s ∧ ys.getLast?=some t then z else 0)=_
  exact Finsupp.sum_single_index (by split_ifs <;> rfl)

theorem arcLoad_cast {n : ℕ} (rs : Records (Fin n)) (h : ∀ r∈rs,0 ≤ r.2) (u v : Fin n) :
    (arcLoad (flow rs) u v : ℝ)=(load rs u v : ℝ) := by
  induction rs with
  | nil => simp [flow,arcLoad]
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht : ∀ r'∈rs,0 ≤ r'.2 := fun r' hr' => h r' (by simp [hr'])
    rw [flow,arcLoad_add,arcLoad_single]
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,amount_cast r.2 hr,
      ih ht,load_cons,Rat.cast_add,Rat.cast_mul,PathCounting.count,Rat.cast_natCast,PathSimplification.arcs]

theorem routed_cast {n : ℕ} (rs : Records (Fin n)) (h : ∀ r∈rs,0 ≤ r.2) (s t : Fin n) :
    (routed (flow rs) s t : ℝ)=(PathRecordArithmetic.routed rs s t : ℝ) := by
  induction rs with
  | nil => simp [flow,routed]
  | cons r rs ih =>
    have hr := h r (by simp)
    have ht : ∀ r'∈rs,0 ≤ r'.2 := fun r' hr' => h r' (by simp [hr'])
    rw [flow,routed_add,routed_single]
    simp only [NNReal.coe_add,ih ht,PathRecordArithmetic.routed_cons,Rat.cast_add]
    split_ifs <;> simp [amount_cast r.2 hr]

theorem support_mem {n : ℕ} (rs : Records (Fin n)) (xs : List (Fin n))
    (h : xs∈(flow rs).support) : ∃ r∈rs,r.1=xs := by
  induction rs with
  | nil => simp [flow] at h
  | cons r rs ih =>
    have hh := Finsupp.support_add h
    rcases Finset.mem_union.mp hh with hh | hh
    · have he : xs=r.1 := Finset.mem_singleton.mp (Finsupp.support_single_subset hh)
      exact ⟨r,by simp,he.symm⟩
    · obtain ⟨r',hr',he⟩ := ih hh
      exact ⟨r',by simp [hr'],he⟩

/-- Rational record checks imply exactly the public real-valued flow and
support-length predicates, with duplicate records correctly added together. -/
theorem correct {n L : ℕ} (I : RationalInstance n) (f : ℚ) (hf : 0 ≤ f)
    (rs : Records (Fin n))
    (hvalid : ∀ r∈rs,0 ≤ r.2 ∧ 2 ≤ r.1.length ∧ r.1.Nodup ∧ r.1.length ≤ L+1)
    (hcap : ∀ u v,load rs u v+load rs v u ≤ (I.capacity u v : ℚ))
    (hdemand : ∀ s t,s ≠ t → f/2 ≤ PathRecordArithmetic.routed rs s t) :
    IsConcurrentFlow .undirected I.network (uniformWeight n)
      ((certificate f rs).value : ℝ≥0) (certificate f rs).flow ∧
    HasPathLengthAtMost (certificate f rs).flow (L : ℝ) := by
  have hpos : ∀ r∈rs,0 ≤ r.2 := fun r hr => (hvalid r hr).1
  rw [certificate_flow]
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro xs hxs
    obtain ⟨r,hr,rfl⟩ := support_mem rs xs hxs
    exact ⟨(hvalid r hr).2.1,(hvalid r hr).2.2.1⟩
  · intro u v
    apply NNReal.coe_le_coe.mp
    change (arcLoad (flow rs) u v : ℝ)+(arcLoad (flow rs) v u : ℝ) ≤ (I.capacity u v : ℝ)
    rw [arcLoad_cast rs hpos,arcLoad_cast rs hpos]
    exact_mod_cast hcap u v
  · intro s t hst
    apply NNReal.coe_le_coe.mp
    simp only [pairDemand,uniformWeight,one_mul,NNReal.coe_mul,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,
      certificate,amount_cast f hf,routed_cast rs hpos]
    have hh := hdemand s t hst
    have hh' : (f : ℝ)/2 ≤ (PathRecordArithmetic.routed rs s t : ℝ) := by exact_mod_cast hh
    simpa only [one_mul,div_eq_mul_inv] using hh'
  · intro xs hxs
    obtain ⟨r,hr,rfl⟩ := support_mem rs xs hxs
    have hh : r.1.length-1 ≤ L := by have := (hvalid r hr).2.2.2; omega
    exact_mod_cast hh

end Lax455465Proofs.PathCertificateInterpretation
