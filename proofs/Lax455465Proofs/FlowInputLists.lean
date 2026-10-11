import Lax455465Proofs.RamFlowData
import Lax455465Proofs.FlowLpIndices

namespace Lax455465Proofs.FlowInputLists

open DirectedFlowLP FlowLpIndices RamFlowData

/-- The canonical capacity vector uses exactly the public row-major order. -/
theorem capacity_flat {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) :
    capacities I = (List.ofFn fun u => List.ofFn (I.capacity u)).flatten := by
  unfold capacities
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext u
  apply congrArg List.ofFn
  funext v
  have huv : u.val*n+v.val < n*n := calc
    _ < (u.val+1)*n := by rw [Nat.add_mul,Nat.one_mul]; exact Nat.add_lt_add_left v.isLt _
    _ ≤ n*n := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr u.isLt)
  have he : (⟨u.val*n+v.val,huv⟩ : Fin (n*n)) = edgeIndex n (u,v) := by
    apply Fin.ext
    rw [edge_value]
  rw [he]
  simp only [Equiv.symm_apply_apply]

/-- The original input is a header and two canonical unsigned vectors. -/
theorem input_eq {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind)
    (I : Lax455465.RationalEncoding.RationalInstance n) :
    Lax455465.RationalEncoding.encodeInput kind I =
      [match kind with | .undirected => 0 | .directed => 1,n] ++
        (RamUnsignedBuffer.encode (List.ofFn I.weight) ++ RamUnsignedBuffer.encode (capacities I)) := by
  simp only [Lax455465.RationalEncoding.encodeInput,RamUnsignedBuffer.encode,capacity_flat,List.append_assoc]
  rfl

end Lax455465Proofs.FlowInputLists
