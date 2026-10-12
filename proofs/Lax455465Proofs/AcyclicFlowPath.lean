import Lax455465Proofs.PathSimplification

open scoped BigOperators
namespace Lax455465Proofs.AcyclicFlowPath
open PathSimplification
variable {α : Type*} [Fintype α] [DecidableEq α]

def Balance (g : α → α → ℚ) (s t : α) (a : ℚ) : Prop :=
  ∀ u,(∑ v,g u v)-(∑ v,g v u)=(if u=s then a else 0)-(if u=t then a else 0)

/-- A finite nonnegative acyclic flow with positive supply contains a
positive source-to-target path. The ranking is used only to prove termination. -/
theorem exists_walk (g : α → α → ℚ) (hpos : ∀ u v,0 ≤ g u v)
    (rank : α → ℕ) (N : ℕ) (hrank : ∀ u,rank u ≤ N)
    (hstep : ∀ u v,0 < g u v → rank u < rank v)
    (s t : α) (hst : s ≠ t) (a : ℚ) (ha : 0 < a) (hbal : Balance g s t a) :
    ∃ xs : List α,xs.head?=some s ∧ xs.getLast?=some t ∧
      ∀ e∈arcs xs,0 < g e.1 e.2 := by
  have aux : ∀ m u,N-rank u=m → (0 < ∑ v,g u v) →
      ∃ xs : List α,xs.head?=some u ∧ xs.getLast?=some t ∧
        ∀ e∈arcs xs,0 < g e.1 e.2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro u hu hout
      by_cases hut : u=t
      · subst u
        exact ⟨[t],rfl,rfl,by simp⟩
      obtain ⟨v,hv⟩ : ∃ v,0 < g u v := by
        by_contra! hh
        have hn : (∑ v,g u v) ≤ 0 := Finset.sum_nonpos fun v _ => hh v
        linarith
      by_cases hvt : v=t
      · subst v
        refine ⟨[u,t],rfl,rfl,?_⟩
        simpa using hv
      have hin : 0 < ∑ w,g w v := lt_of_lt_of_le hv
        (Finset.single_le_sum (fun w _ => hpos w v) (Finset.mem_univ u))
      have houtv : 0 < ∑ w,g v w := by
        have hb := hbal v
        rw [if_neg hvt] at hb
        split_ifs at hb <;> linarith
      have hmeasure : N-rank v < m := by have := hstep u v hv; have := hrank v; omega
      obtain ⟨xs,hxs,hxt,hxe⟩ := ih (N-rank v) hmeasure v rfl houtv
      cases xs with
      | nil => simp at hxs
      | cons v' xs =>
        have he : v'=v := by simpa using hxs
        subst v'
        refine ⟨u::v::xs,rfl,by simpa using hxt,?_⟩
        intro e he
        simp only [arcs_cons_cons,List.mem_cons] at he
        rcases he with rfl | he
        · exact hv
        · exact hxe e he
  have hout : 0 < ∑ v,g s v := by
    have hb := hbal s
    simp only [ite_true,eq_self,if_neg hst] at hb
    have hin : 0 ≤ ∑ v,g v s := Finset.sum_nonneg fun v _ => hpos v s
    linarith
  exact aux (N-rank s) s rfl hout

/-- The positive walk can be made simple without adding any arc. -/
theorem exists_path (g : α → α → ℚ) (hpos : ∀ u v,0 ≤ g u v)
    (rank : α → ℕ) (N : ℕ) (hrank : ∀ u,rank u ≤ N)
    (hstep : ∀ u v,0 < g u v → rank u < rank v)
    (s t : α) (hst : s ≠ t) (a : ℚ) (ha : 0 < a) (hbal : Balance g s t a) :
    ∃ xs : List α,xs.head?=some s ∧ xs.getLast?=some t ∧ xs.Nodup ∧
      2 ≤ xs.length ∧ ∀ e∈arcs xs,0 < g e.1 e.2 := by
  obtain ⟨xs,hs,ht,he⟩ := exists_walk g hpos rank N hrank hstep s t hst a ha hbal
  obtain ⟨hlen,hnodup,hs',ht'⟩ := distinct_endpoints hst hs ht
  exact ⟨simplify xs,hs',ht',hnodup,hlen,fun e h => he e ((arcs_sublist xs).subset h)⟩

end Lax455465Proofs.AcyclicFlowPath
