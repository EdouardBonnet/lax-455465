import Lax455465Proofs.PositiveWalk

namespace Lax455465Proofs.LayeredWalkState
open LayeredFlowLP LayeredGraphFlow PathSimplification List
open scoped NNRat

def arc {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0) (a : Arc n L) : ℚ :=
  qs (variableIndex n L (.inr a))

/-- Mathematical invariant for the raw layered walk and its simple physical stack. -/
structure Walk {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) (xs : List (Vertex n L)) (p : Vertex n L) (ys : List (Fin n)) : Prop where
  length : xs.length=p.1.val+1
  levels : PositiveWalk.Levels xs
  head : xs.head?=some (0,st.1)
  last : xs.getLast?=some p
  positive : ∀ e∈arcs xs,0<graph (arc qs) st e.1 e.2
  simple : ys.Nodup
  simpleHead : ys.head?=some st.1
  simpleLast : ys.getLast?=some p.2
  simpleArcs : List.Sublist (arcs ys) (arcs (xs.map Prod.snd))
  simpleLength : ys.length≤xs.length

open List

theorem initial {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0) (st : Edge n) :
    Walk qs st [(0,st.1)] (0,st.1) [st.1] := by
  constructor <;> simp [PositiveWalk.Levels,arcs]

theorem successor {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) {xs : List (Vertex n L)} {p : Vertex n L} {ys : List (Fin n)}
    (h : Walk qs st xs p ys) (hk : p.1.val<L) (a : ℚ) (ha : 0<a)
    (hb : AcyclicFlowPath.Balance (graph (arc qs) st) (0,st.1) (Fin.last L,st.2) a) :
    ∃ v : Fin n,0<qs (variableIndex n L (.inr (st,(⟨p.1.val,hk⟩,(p.2,v))))) := by
  let k : Fin L := ⟨p.1.val,hk⟩
  have hp : p=(k.castSucc,p.2) := Prod.ext (Fin.ext rfl) rfl
  have hr : p=(0,st.1) ∨ ∃ q : Vertex n L,0<graph (arc qs) st q p := by
    by_cases hz : p.1.val=0
    · have hlen : xs.length=1 := by rw [h.length,hz]
      obtain ⟨q,hq⟩ := List.length_eq_one_iff.mp hlen
      have hh : q=(0,st.1) := by simpa only [hq,List.head?_singleton,Option.some.injEq] using h.head
      have hl : q=p := by simpa only [hq,List.getLast?_singleton,Option.some.injEq] using h.last
      exact Or.inl (hl.symm.trans hh)
    · exact Or.inr (PositiveWalk.incoming _ xs p (by rw [h.length]; omega) h.last h.positive)
  obtain ⟨v,hv⟩ := LayeredPositivePath.exists_successor (arc qs) (fun a => NNRat.coe_nonneg _) st.1 st.2 a ha hb
    k p.2 (by simpa only [←hp] using hr)
  exact ⟨v,by exact_mod_cast hv⟩

theorem extend {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) {xs : List (Vertex n L)} {p : Vertex n L} {ys : List (Fin n)}
    (h : Walk qs st xs p ys) (hk : p.1.val<L) (v : Fin n)
    (hv : 0<qs (variableIndex n L (.inr (st,(⟨p.1.val,hk⟩,(p.2,v)))))) :
    let q : Vertex n L := ((⟨p.1.val,hk⟩ : Fin L).succ,v)
    Walk qs st (xs++[q]) q (LoopErasure.append ys v) := by
  dsimp only
  let k : Fin L := ⟨p.1.val,hk⟩
  let q : Vertex n L := (k.succ,v)
  have hp : p=(k.castSucc,p.2) := Prod.ext (Fin.ext rfl) rfl
  have hxp : (xs.map Prod.snd).getLast?=some p.2 := by simpa using congrArg (Option.map Prod.snd) h.last
  have hxs : xs≠[] := by
    intro he
    have hh := h.length
    simp [he] at hh
  have hys : ys≠[] := by
    intro he
    have hh := h.simpleHead
    simp [he] at hh
  refine ⟨?_,PositiveWalk.levels_append h.levels q (by change p.1.val+1=xs.length; exact h.length.symm),?_,?_,?_,
    LoopErasure.nodup h.simple v,?_,LoopErasure.last ys v,?_,?_⟩
  · simp only [List.length_append,List.length_singleton,h.length]
    rfl
  · rw [List.head?_append,h.head]
    rfl
  · simp [q]
  · apply PositiveWalk.positive_append _ xs p q h.last h.positive
    rw [hp,LayeredPositivePath.edge_eq]
    exact_mod_cast hv
  · exact (LoopErasure.head ys v hys).trans h.simpleHead
  · simpa only [List.map_append,List.map_cons,List.map_nil] using
      LoopErasure.arcs_sublist (xs.map Prod.snd) ys p.2 v hxp h.simpleLast h.simpleArcs
  · have hh := LoopErasure.length ys v
    have hle := h.simpleLength
    simp only [List.length_append,List.length_singleton]
    omega

theorem target {n L : ℕ} (qs : Fin (1+(n*n)*(L*(n*n))) → ℚ≥0)
    (st : Edge n) {xs : List (Vertex n L)} {p : Vertex n L} {ys : List (Fin n)}
    (h : Walk qs st xs p ys) (hL : 1≤L) (hp : p.1.val=L) (a : ℚ) (ha : 0≤a)
    (hb : AcyclicFlowPath.Balance (graph (arc qs) st) (0,st.1) (Fin.last L,st.2) a) : p.2=st.2 := by
  have he : p=(Fin.last L,p.2) := Prod.ext (Fin.ext hp) rfl
  apply LayeredPositivePath.target (arc qs) (fun a => NNRat.coe_nonneg _) st.1 st.2 p.2 a ha hb
  simpa only [←he] using PositiveWalk.incoming _ xs p (by rw [h.length,hp]; omega) h.last h.positive

end Lax455465Proofs.LayeredWalkState
