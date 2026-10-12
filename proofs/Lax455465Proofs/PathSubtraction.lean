import Lax455465Proofs.AcyclicFlowPath
import Lax455465Proofs.PathCounting

open scoped BigOperators
namespace Lax455465Proofs.PathSubtraction
open PathSimplification AcyclicFlowPath
variable {α : Type*} [Fintype α] [DecidableEq α]

def residual (g : α → α → ℚ) (xs : List α) (w : ℚ) (u v : α) : ℚ :=
  g u v-w*PathCounting.count xs u v

def support (g : α → α → ℚ) : Finset (α×α) :=
  Finset.univ.filter fun e => 0 < g e.1 e.2

theorem residual_le (g : α → α → ℚ) (xs : List α) (w : ℚ) (hw : 0 ≤ w) (u v : α) :
    residual g xs w u v ≤ g u v := by
  unfold residual
  exact sub_le_self _ (mul_nonneg hw (PathCounting.nonnegative xs u v))

theorem residual_nonnegative (g : α → α → ℚ) (hg : ∀ u v,0 ≤ g u v)
    (xs : List α) (hn : xs.Nodup) (w : ℚ)
    (hw : ∀ e∈arcs xs,w ≤ g e.1 e.2) : ∀ u v,0 ≤ residual g xs w u v := by
  intro u v
  rw [residual,PathCounting.count_eq hn]
  by_cases he : (u,v)∈arcs xs
  · simp only [if_pos he,mul_one]
    exact sub_nonneg.mpr (hw (u,v) he)
  · simp only [if_neg he,mul_zero,sub_zero]
    exact hg u v

theorem residual_balance (g : α → α → ℚ) (s t : α) (a : ℚ)
    (hg : Balance g s t a) (xs : List α)
    (hs : xs.head?=some s) (ht : xs.getLast?=some t) (w : ℚ) :
    Balance (residual g xs w) s t (a-w) := by
  intro u
  simp only [residual,Finset.sum_sub_distrib,←Finset.mul_sum]
  have hp := PathCounting.balance hs ht u
  have hb := hg u
  have hpw := congrArg (fun z : ℚ => w*z) hp
  split_ifs at hpw hb ⊢ <;> nlinarith [hpw]

theorem support_subset (g : α → α → ℚ) (xs : List α) (w : ℚ) (hw : 0 ≤ w) :
    support (residual g xs w) ⊆ support g := by
  intro e he
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
  exact he.trans_le (residual_le g xs w hw e.1 e.2)

theorem support_decreases (g : α → α → ℚ) (xs : List α) (hn : xs.Nodup)
    (w : ℚ) (hw : 0 < w) (e : α×α) (he : e∈arcs xs) (hge : g e.1 e.2=w) :
    (support (residual g xs w)).card < (support g).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨support_subset g xs w hw.le,?_⟩
  intro hsame
  have hmem : e∈support g := by simp [support,hge,hw]
  rw [←hsame] at hmem
  have hz : residual g xs w e.1 e.2=0 := by
    rw [residual,PathCounting.count_eq hn,if_pos he,hge]
    ring
  simp [support,hz] at hmem

/-- Taking the minimum residual edge capacity either finishes the requested
amount or eliminates at least one positive arc. -/
theorem exists_amount (g : α → α → ℚ) (xs : List α)
    (hx : 2 ≤ xs.length) (hpos : ∀ e∈arcs xs,0 < g e.1 e.2) (a : ℚ) (ha : 0 < a) :
    ∃ w,0 < w ∧ w ≤ a ∧ (∀ e∈arcs xs,w ≤ g e.1 e.2) ∧
      (w=a ∨ ∃ e∈arcs xs,g e.1 e.2=w) := by
  have hne : (arcs xs).toFinset.Nonempty := by
    cases xs with
    | nil => simp at hx
    | cons u xs =>
      cases xs with
      | nil => simp at hx
      | cons v xs => exact ⟨(u,v),by simp⟩
  let b := (arcs xs).toFinset.inf' hne (fun e => g e.1 e.2)
  obtain ⟨e,he,heq⟩ := Finset.exists_mem_eq_inf' hne (fun e => g e.1 e.2)
  have hb : 0 < b := by rw [show b=g e.1 e.2 from heq]; exact hpos e (List.mem_toFinset.mp he)
  refine ⟨min a b,lt_min ha hb,min_le_left _ _,?_,?_⟩
  · intro e he
    exact (min_le_right _ _).trans (Finset.inf'_le _ (List.mem_toFinset.mpr he))
  · by_cases hab : a ≤ b
    · exact Or.inl (min_eq_left hab)
    · exact Or.inr ⟨e,List.mem_toFinset.mp he,by rw [min_eq_right (le_of_not_ge hab)]; exact heq.symm⟩

end Lax455465Proofs.PathSubtraction
