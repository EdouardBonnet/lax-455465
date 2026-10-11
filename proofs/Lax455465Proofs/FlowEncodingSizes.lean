import Lax455465Proofs.RamFlowLp

namespace Lax455465Proofs.FlowEncodingSizes

open Lax109476.LinearProgram Lax109476.RationalEncoding

theorem program_length {m n : ℕ} (P : Program ℚ m n) :
    (encodeProgram P).length = 2+3*(m*n+m+n) := by
  unfold encodeProgram
  rw [←FlowLpMatrixList.values_eq]
  change ([m,n] ++ RamVectorEncoding.encode (FlowLpMatrixList.values P) ++
    RamVectorEncoding.encode (List.ofFn P.b) ++ RamVectorEncoding.encode (List.ofFn P.c)).length = _
  simp only [List.length_append,List.length_cons,List.length_nil,RamVectorEncoding.length_encode,
    FlowLpMatrixList.values,List.length_ofFn]
  ring

theorem flow_length {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) :
    (encodeProgram (DirectedFlowLP.program I)).length = RamFlowLp.wordLength n := program_length _

end Lax455465Proofs.FlowEncodingSizes
