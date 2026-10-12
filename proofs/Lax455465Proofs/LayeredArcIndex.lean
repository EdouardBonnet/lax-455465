import Lax455465Proofs.LayeredLpIndices

namespace Lax455465Proofs.LayeredArcIndex
open LayeredFlowLP

def index (n L st k u v : ℕ) : ℕ := 1+st*(L*(n*n))+k*(n*n)+u*n+v

theorem value {n L : ℕ} (st : Edge n) (k : Fin L) (u v : Fin n) :
    (variableIndex n L (.inr (st,(k,(u,v))))).val=
      index n L (DirectedFlowLP.edgeIndex n st).val k.val u.val v.val := by
  simp only [LayeredLpIndices.arc_variable,index]
  simp [arcIndex,DirectedFlowLP.edgeIndex,finProdFinEquiv]
  ring

theorem bound {n L : ℕ} (st : Edge n) (k : Fin L) (u v : Fin n) :
    index n L (DirectedFlowLP.edgeIndex n st).val k.val u.val v.val<1+(n*n)*(L*(n*n)) := by
  rw [←value]
  exact (variableIndex n L (.inr (st,(k,(u,v))))).isLt

end Lax455465Proofs.LayeredArcIndex
