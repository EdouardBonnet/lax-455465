import Lax455465Proofs.FlowLpFlat

namespace Lax455465Proofs.FlowLpEncoding

open DirectedFlowLP Lax109476.RationalEncoding

/-- Dense LP input obtained by ordinary numerical loops, with no inverse
finite-type equivalences at runtime. -/
def word (weight capacity : ℕ → ℚ) (n : ℕ) : List ℕ :=
  let m := n*n + 2*((n*n)*n)
  let v := 1+(n*n)*(n*n)
  [m,v] ++ ((List.range m).map fun row =>
      (List.range v).map (FlowLpFlat.coefficient weight n row)).flatten.flatMap encodeRational ++
    ((List.range m).map (FlowLpFlat.rowBound capacity n)).flatMap encodeRational ++
    ((List.range v).map FlowLpFlat.objective).flatMap encodeRational

private theorem range_map {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

/-- The word emitted by the flat construction is precisely the public
encoding of the LP used in the flow and duality proofs, also when n=0. -/
theorem word_eq {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n)
    (weight capacity : ℕ → ℚ)
    (hw : ∀ v : Fin n, weight v.val = (I.weight v : ℚ))
    (hc : ∀ u v : Fin n, capacity (edgeIndex n (u,v)).val = (I.capacity u v : ℚ)) :
    word weight capacity n = encodeProgram (program I) := by
  have hA : ∀ i : Fin (n*n+2*((n*n)*n)),
      (List.range (1+(n*n)*(n*n))).map (FlowLpFlat.coefficient weight n i.val) =
        List.ofFn ((program I).A i) := by
    intro i
    rw [range_map]
    congr 1
    funext j
    exact FlowLpFlat.coefficient_at I weight hw i j
  have hrows : ((List.range (n*n+2*((n*n)*n))).map fun row =>
      (List.range (1+(n*n)*(n*n))).map (FlowLpFlat.coefficient weight n row)) =
        List.ofFn (fun i => List.ofFn ((program I).A i)) := by
    rw [range_map]
    congr 1
    funext i
    exact hA i
  have hb : (List.range (n*n+2*((n*n)*n))).map (FlowLpFlat.rowBound capacity n) =
      List.ofFn ((program I).b) := by
    rw [range_map]
    congr 1
    funext i
    simpa only [program,Equiv.apply_symm_apply] using
      FlowLpFlat.rowBound_eq I capacity hc ((rowIndex n).symm i)
  have hc' : (List.range (1+(n*n)*(n*n))).map FlowLpFlat.objective =
      List.ofFn ((program I).c) := by
    rw [range_map]
    congr 1
    funext j
    simpa only [program,Equiv.apply_symm_apply] using
      FlowLpFlat.objective_eq ((variableIndex n).symm j)
  simp only [word,encodeProgram,encodeVector,hrows,hb,hc']

end Lax455465Proofs.FlowLpEncoding
