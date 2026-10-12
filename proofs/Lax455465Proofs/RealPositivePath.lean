import Lax455465Proofs.PathCounting
import Mathlib.Logic.Relation

open scoped BigOperators
namespace Lax455465Proofs.RealPositivePath
open PathSimplification
variable {α : Type*} [Fintype α] [DecidableEq α]

def Balance (g : α → α → ℝ) (s t : α) (a : ℝ) : Prop :=
  ∀ u, (∑ v, g u v) - (∑ v, g v u) =
    (if u = s then a else 0) - (if u = t then a else 0)

/-- Conservation forces a positive-flow route even when the flow contains cycles. -/
theorem reachable (g : α → α → ℝ) (hg : ∀ u v, 0 ≤ g u v)
    (s t : α) (a : ℝ) (ha : 0 < a) (hbal : Balance g s t a) :
    Relation.ReflTransGen (fun u v => 0 < g u v) s t := by
  classical
  by_contra ht
  let R : Finset α := Finset.univ.filter fun u =>
    Relation.ReflTransGen (fun u v => 0 < g u v) s u
  have hmem (u : α) : u ∈ R ↔ Relation.ReflTransGen (fun u v => 0 < g u v) s u := by
    simp [R]
  have hsR : s ∈ R := (hmem s).mpr .refl
  have htR : t ∉ R := fun h => ht ((hmem t).mp h)
  have houtzero : ∀ u ∈ R, ∀ v ∉ R, g u v = 0 := by
    intro u hu v hv
    have hn : ¬ 0 < g u v := fun hp => hv ((hmem v).mpr (((hmem u).mp hu).tail hp))
    exact le_antisymm (le_of_not_gt hn) (hg u v)
  have hout : (∑ u ∈ R, ∑ v, g u v) = ∑ u ∈ R, ∑ v ∈ R, g u v := by
    apply Finset.sum_congr rfl
    intro u hu
    exact (Finset.sum_subset (Finset.subset_univ R) (fun v _ hv => houtzero u hu v hv)).symm
  have hin : (∑ u ∈ R, ∑ v ∈ R, g u v) ≤ ∑ u ∈ R, ∑ v, g v u := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro u hu
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun v _ _ => hg v u)
  have hsum := Finset.sum_congr (s₁ := R) (s₂ := R) rfl (fun u _ => hbal u)
  simp only [Finset.sum_sub_distrib] at hsum
  have hsource : (∑ u ∈ R, if u = s then a else 0) = a := by simp [hsR]
  have htarget : (∑ u ∈ R, if u = t then a else 0) = 0 := by simp [htR]
  rw [hsource, htarget, sub_zero, hout] at hsum
  linarith

omit [Fintype α] [DecidableEq α] in
theorem walk_of_reachable (g : α → α → ℝ) {s t : α}
    (h : Relation.ReflTransGen (fun u v => 0 < g u v) s t) :
    ∃ xs : List α, xs.head? = some s ∧ xs.getLast? = some t ∧
      ∀ e ∈ arcs xs, 0 < g e.1 e.2 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[t], rfl, rfl, by simp⟩
  | @head u v huv hvt ih =>
    obtain ⟨xs, hs, ht, he⟩ := ih
    cases xs with
    | nil => simp at hs
    | cons v' xs =>
      have hv : v' = v := by simpa using hs
      subst v'
      refine ⟨u :: v :: xs, rfl, by simpa using ht, ?_⟩
      intro e he'
      rcases (by simpa only [arcs_cons_cons, List.mem_cons] using he' : e = (u,v) ∨ e ∈ arcs (v::xs)) with rfl | he'
      · exact huv
      · exact he e he'

/-- A finite nonnegative flow of positive value contains a positive simple path. -/
theorem exists_path (g : α → α → ℝ) (hg : ∀ u v, 0 ≤ g u v)
    (s t : α) (hst : s ≠ t) (a : ℝ) (ha : 0 < a) (hbal : Balance g s t a) :
    ∃ xs : List α, xs.head? = some s ∧ xs.getLast? = some t ∧ xs.Nodup ∧
      2 ≤ xs.length ∧ ∀ e ∈ arcs xs, 0 < g e.1 e.2 := by
  obtain ⟨xs, hs, ht, he⟩ := walk_of_reachable g (reachable g hg s t a ha hbal)
  obtain ⟨hlen, hn, hs', ht'⟩ := distinct_endpoints hst hs ht
  exact ⟨simplify xs, hs', ht', hn, hlen, fun e h => he e ((arcs_sublist xs).subset h)⟩

end Lax455465Proofs.RealPositivePath
