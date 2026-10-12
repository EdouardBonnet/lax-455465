import Lax455465Proofs.BoundedDistances
import Lax455465Proofs.PathSimplification

namespace Lax455465Proofs.RouteSimplification
open BoundedDistances PathSimplification

def cost {n : ℕ} (ell : Length n) (xs : List (Fin n)) : ℚ :=
  ((arcs xs).map fun e => ell e.1 e.2).sum

@[simp] theorem cost_nil {n : ℕ} (ell : Length n) : cost ell []=0 := rfl
@[simp] theorem cost_singleton {n : ℕ} (ell : Length n) (a : Fin n) : cost ell [a]=0 := rfl
@[simp] theorem cost_cons_cons {n : ℕ} (ell : Length n) (a b : Fin n) (xs : List (Fin n)) :
    cost ell (a::b::xs)=ell a b+cost ell (b::xs) := rfl

theorem arcs_append_after {α : Type*} {xs : List α} {v : α}
    (hx : xs.getLast?=some v) (ys : List α) :
    arcs (xs++ys)=arcs xs++arcs (v::ys) := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    cases xs with
    | nil =>
      have ha : a=v := by simpa using hx
      subst a
      simp
    | cons b xs =>
      simp only [List.getLast?_cons_cons] at hx
      simpa using ih hx

theorem cost_append_after {n : ℕ} (ell : Length n) {xs : List (Fin n)} {v : Fin n}
    (hx : xs.getLast?=some v) (ys : List (Fin n)) :
    cost ell (xs++ys)=cost ell xs+cost ell (v::ys) := by
  simp [cost,arcs_append_after hx]

/-- Every route can be recorded as a vertex list, with its exact cost and hop count. -/
theorem to_list {n : ℕ} {ell : Length n} {s t : Fin n} {k : ℕ} {c : ℚ}
    (hr : Route ell s t k c) :
    ∃ xs : List (Fin n),xs.head?=some s ∧ xs.getLast?=some t ∧
      xs.length=k+1 ∧ cost ell xs=c := by
  induction hr with
  | refl v => exact ⟨[v],rfl,rfl,rfl,rfl⟩
  | @edge u v hne => exact ⟨[u,v],rfl,rfl,rfl,by simp⟩
  | @trans u v w a b x y h₁ h₂ ih₁ ih₂ =>
    obtain ⟨xs,hxs,hxt,hxl,hxc⟩ := ih₁
    obtain ⟨ys,hys,hyt,hyl,hyc⟩ := ih₂
    cases ys with
    | nil => simp at hys
    | cons v' ys =>
      have hv : v'=v := by simpa using hys
      subst v'
      refine ⟨xs++ys,?_,?_,?_,?_⟩
      · cases xs <;> simp_all
      · cases ys with
        | nil => simpa using hxt.trans hyt
        | cons w' ys => simpa using hyt
      · simp only [List.length_append,List.length_cons] at hyl ⊢
        omega
      · rw [cost_append_after ell hxt,hxc,hyc]

/-- A simple vertex list induces a route with one hop per consecutive pair. -/
theorem of_list {n : ℕ} (ell : Length n) {xs : List (Fin n)} {s t : Fin n}
    (hs : xs.head?=some s) (ht : xs.getLast?=some t) (hnodup : xs.Nodup) :
    Route ell s t (xs.length-1) (cost ell xs) := by
  induction xs generalizing s with
  | nil => simp at hs
  | cons a xs ih =>
    have ha : a=s := by simpa using hs
    subst a
    cases xs with
    | nil =>
      have hst : s=t := by simpa using ht
      subst t
      exact .refl s
    | cons b xs =>
      have hsb : s ≠ b := by
        have hh := (List.nodup_cons.mp hnodup).1
        simpa using fun h : s=b => hh (by simp [h])
      have htail := ih rfl (by simpa using ht) (List.nodup_cons.mp hnodup).2
      simpa [Nat.add_comm] using (Route.edge (ell := ell) hsb).trans htail

theorem simplify_cost_le {n : ℕ} (ell : Length n) (hell : ∀ u v,0 ≤ ell u v)
    (xs : List (Fin n)) : cost ell (simplify xs) ≤ cost ell xs := by
  apply ((arcs_sublist xs).map (fun e => ell e.1 e.2)).sum_le_sum
  intro c hc
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hc
  exact hell _ _

/-- Cycle erasure never increases cost or hop count and leaves at most n−1 edges. -/
theorem shorten {n : ℕ} {ell : Length n} (hell : ∀ u v,0 ≤ ell u v)
    {s t : Fin n} {k : ℕ} {c : ℚ} (hr : Route ell s t k c) :
    ∃ k' ≤ min k (n-1),∃ c' ≤ c,Route ell s t k' c' := by
  obtain ⟨xs,hs,ht,hl,hc⟩ := to_list hr
  refine ⟨(simplify xs).length-1,?_,cost ell (simplify xs),?_,?_⟩
  · have hh := length_le xs
    have hn := length_le_card xs
    simp only [Fintype.card_fin] at hn
    omega
  · exact (simplify_cost_le ell hell xs).trans_eq hc
  · exact of_list ell (by simpa using hs) (by simpa using ht) (nodup xs)

end Lax455465Proofs.RouteSimplification
