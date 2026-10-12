import Lax455465Proofs.LayeredSweepGraph

namespace Lax455465Proofs.LayeredWalkVector
open LayeredFlowLP LayeredGraphFlow LayeredWalkState LayeredPathSweep
open scoped NNRat

/-- The runtime walk determines its physical vertex at every layer. -/
theorem representation {n L : ℕ} {xs : List (Vertex n L)}
    (hlen : xs.length=L+1) (hlevels : PositiveWalk.Levels xs) :
    ∃ path : Fin (L+1) → Fin n, xs=LayeredSweepGraph.raw path := by
  let path : Fin (L+1) → Fin n := fun i => (xs[i.val]'(by omega)).2
  refine ⟨path,?_⟩
  apply List.ext_getElem
  · simp [LayeredSweepGraph.raw,hlen]
  · intro i hi hj
    have hlev : xs[i].1.val=i := by
      have hh := congrArg (fun ys : List ℕ => ys[i]?) hlevels
      simpa only [List.getElem?_map,List.getElem?_eq_getElem hi,
        Option.map_some,List.getElem?_range hi,Option.some.injEq] using hh
    simp only [LayeredSweepGraph.raw,List.getElem_ofFn]
    exact Prod.ext (Fin.ext hlev) rfl

/-- Recover a fixed-length path from the proved native traversal, retaining
the simple stack and the actual positivity and endpoint guarantees. -/
theorem completed {n L : ℕ} (q : Coordinate n L → ℚ≥0) (st : Edge n)
    {xs : List (Vertex n L)} {ys : List (Fin n)}
    (h : Walk q st xs (Fin.last L,st.2) ys) :
    ∃ path : Fin (L+1) → Fin n,
      xs=LayeredSweepGraph.raw path ∧ path 0=st.1 ∧ path (Fin.last L)=st.2 ∧
      ∀ k : Fin L, 0<q (edge st path k) := by
  obtain ⟨path,hxs⟩ := representation (by simpa using h.length) h.levels
  refine ⟨path,hxs,?_,?_,?_⟩
  · have hh := h.head
    simpa only [hxs,LayeredSweepGraph.raw_head,Option.some.injEq,Prod.mk.injEq,true_and] using hh
  · have hh := h.last
    simpa only [hxs,LayeredSweepGraph.raw_last,Option.some.injEq,Prod.mk.injEq,true_and] using hh
  · intro k
    have hm : ((k.castSucc,path k.castSucc),(k.succ,path k.succ))∈PathSimplification.arcs xs := by
      rw [hxs,LayeredSweepGraph.raw,AdjacentOfFn.arcs]
      exact List.mem_ofFn.mpr ⟨k,rfl⟩
    have hp := h.positive _ hm
    rw [LayeredPositivePath.edge_eq] at hp
    exact_mod_cast hp

end Lax455465Proofs.LayeredWalkVector
