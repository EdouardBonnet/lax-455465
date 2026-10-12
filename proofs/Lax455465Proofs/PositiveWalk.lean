import Lax455465Proofs.LoopErasure
import Lax455465Proofs.LayeredPositivePath

namespace Lax455465Proofs.PositiveWalk
open List PathSimplification LayeredFlowLP LayeredGraphFlow

/-- The last vertex of a nontrivial positive walk has a positive incoming arc. -/
theorem incoming {α : Type*} [DecidableEq α] (g : α → α → ℚ)
    (xs : List α) (t : α) (hlen : 2≤xs.length)
    (hlast : xs.getLast?=some t) (hpos : ∀ e∈arcs xs,0<g e.1 e.2) :
    ∃ p,0<g p t := by
  obtain ⟨ys,rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hy : ys≠[] := by intro he; subst ys; simp at hlen
  let p := ys.getLast hy
  have hp : ys.getLast?=some p := List.getLast?_eq_some_getLast hy
  have he : (p,t)∈arcs (ys++[t]) := by
    rw [LoopErasure.arcs_append ys t p hp]
    simp
  exact ⟨p,hpos (p,t) he⟩

/-- Layer labels uniquely identify positions in the raw walk. -/
def Levels {n L : ℕ} (xs : List (Vertex n L)) : Prop :=
  xs.map (fun p => p.1.val)=List.range xs.length

theorem levels_singleton {n L : ℕ} (s : Fin n) : Levels ([(0,s)] : List (Vertex n L)) := rfl

theorem levels_append {n L : ℕ} {xs : List (Vertex n L)} (h : Levels xs)
    (p : Vertex n L) (hp : p.1.val=xs.length) : Levels (xs++[p]) := by
  simp only [Levels,List.map_append,List.map_cons,List.map_nil,List.length_append,List.length_singleton]
  rw [h,hp,List.range_succ]

theorem nodup {n L : ℕ} {xs : List (Vertex n L)} (h : Levels xs) : xs.Nodup := by
  have hh : (xs.map (fun p => p.1.val)).Nodup := by rw [h]; exact List.nodup_range
  exact hh.of_map

theorem positive_append {α : Type*} [DecidableEq α] (g : α → α → ℚ)
    (xs : List α) (u v : α) (hu : xs.getLast?=some u)
    (hxs : ∀ e∈arcs xs,0<g e.1 e.2) (hv : 0<g u v) :
    ∀ e∈arcs (xs++[v]),0<g e.1 e.2 := by
  rw [LoopErasure.arcs_append xs v u hu]
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hxs e he
  · simp only [List.mem_singleton] at he
    subst e
    exact hv

end Lax455465Proofs.PositiveWalk
