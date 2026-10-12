import Lax455465Proofs.LayeredFlowBounds
import Lax455465Proofs.LayeredLpIndices
import Lax109476.RationalEncoding

namespace Lax455465Proofs.LayeredOptimalCertificate
open LayeredFlowLP LayeredFlowDual LayeredFlowFeasibility
open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding

/-- Every valid certificate for a layered LP is an optimal primal-dual pair.
This applies to the actual certificate emitted by the fixed registered solver. -/
theorem optimal {n L : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (hn : 2 ≤ n)
    (certificate : Certificate (n*n+2*((n*n)*((L+1)*n))) (1+(n*n)*(L*(n*n))))
    (hvalid : IsValidCertificate (program I L) certificate) :
    ∃ (f : ℚ) (x : Arc n L → ℚ) (y : Dual n L),
      certificate=.optimal (vector f x) y ∧ Feasible I f x ∧
      DualFeasible (program I L) y ∧ f=dualValue (program I L) y := by
  cases certificate with
  | optimal z y =>
    rcases hvalid with ⟨hz,hy,hval⟩
    let f := z (variableIndex n L (.inl 0))
    let x := fun a => z (variableIndex n L (.inr a))
    have hrepr : vector f x=z := vector_representation z
    refine ⟨f,x,y,by rw [hrepr],?_,hy,?_⟩
    · rw [←hrepr,feasible_iff] at hz
      exact hz
    · rw [←hrepr,objective_value] at hval
      exact hval
  | infeasible y => exact False.elim (LayeredFlowBounds.no_infeasibility_certificate I y hvalid)
  | unbounded z d => exact False.elim (LayeredFlowBounds.no_improving_direction I hn d hvalid.2)

theorem vector_zero {n L : ℕ} (f : ℚ) (x : Arc n L → ℚ) :
    vector f x ⟨0,by omega⟩=f := by
  have hi : variableIndex n L (.inl 0)=⟨0,by omega⟩ :=
    Fin.ext (LayeredLpIndices.value_variable 0)
  rw [←hi]
  simp [vector]

/-- The first rational in an optimal output is the common flow value. -/
theorem encoding_head {n L : ℕ} (f : ℚ) (x : Arc n L → ℚ) (y : Dual n L) :
    ∃ tail : List ℕ,
      encodeCertificate (.optimal (vector f x) y)=[0]++(encodeRational f++tail) := by
  let z : Fin ((n*n)*(L*(n*n))+1) → ℚ := fun i => vector f x ⟨i.val,by omega⟩
  have hz : List.ofFn (vector f x)=List.ofFn z := by
    apply List.ext_getElem
    · simp only [List.length_ofFn]; omega
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [encodeCertificate,encodeVector,hz,List.ofFn_succ,List.flatMap_cons]
  have hz0 : z 0=f := vector_zero f x
  rw [hz0]
  exact ⟨(List.ofFn fun i => z i.succ).flatMap encodeRational++encodeVector y,
    by simp only [List.append_assoc]⟩

end Lax455465Proofs.LayeredOptimalCertificate
