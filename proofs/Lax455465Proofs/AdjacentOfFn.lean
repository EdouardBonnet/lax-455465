import Lax455465Proofs.PathCounting

namespace Lax455465Proofs.AdjacentOfFn
open PathSimplification

/-- Adjacent pairs in a finite vector, in their actual coordinate order. -/
theorem arcs {α : Type*} {L : ℕ} (f : Fin (L+1) → α) :
    PathSimplification.arcs (List.ofFn f)=List.ofFn (fun k : Fin L => (f k.castSucc,f k.succ)) := by
  apply List.ext_getElem
  · simp only [PathSimplification.arcs,List.length_zip,List.length_tail,List.length_ofFn]
    omega
  · intro i hi hj
    simp only [PathSimplification.arcs,List.getElem_zip,List.getElem_tail,List.getElem_ofFn]
    rfl

end Lax455465Proofs.AdjacentOfFn
