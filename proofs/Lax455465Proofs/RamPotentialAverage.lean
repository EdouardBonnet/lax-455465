import Lax455465Proofs.LargePotentialData
import Lax455465Proofs.RamSetPotential

namespace Lax455465Proofs.RamPotentialAverage
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionContext
open Lax455465.RationalEncoding LargePotentialData
open scoped NNRat

def name (toSet : Bool) : String := if toSet then "potential.toAvg" else "potential.fromAvg"
def command (toSet : Bool) : Com := .seq (.assign "sum.count" (.var "metric.n"))
  (.seq (RamProductSum.command "flow.weights" (RamSetPotential.targetArray toSet)) (save (name toSet)))
def cost (n M : ℕ) : ℕ := (72*(M^2).size+224)*n+22

theorem command_spec (B M : ℕ) {n : ℕ} (I : RationalInstance n) (toSet : Bool)
    (d : MetricMatrix.Matrix n) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hB : 2*M^2+3<B) (hvertex : 2*n+2<B)
    (hw : ∀ v,LpInputSize.Height M (I.weight v : ℚ)) (hd : ∀ u v,LpInputSize.Height M (d u v : ℚ))
    (hp : ∀ q∈products I toSet d S hS,LpInputSize.Height M (q : ℚ))
    (hprefix : ∀ i,LpInputSize.Height M ((((products I toSet d S hS).take i).sum : ℚ≥0) : ℚ)) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧
      Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ ∧
      Prefix (RamUnsignedBuffer.encode (vector toSet d S hS)) (RamSetPotential.targetArray toSet) σ)
      (command toSet) (fun _ τ => Stored (name toSet) (average I toSet d S hS) τ) (cost n M) := by
  have hMB : M<B := by nlinarith
  have hweights : ∀ q∈List.ofFn I.weight,LpInputSize.Height M (q : ℚ) := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact hw v
  have hvalues : ∀ q∈vector toSet d S hS,LpInputSize.Height M (q : ℚ) := by
    intro q hq; obtain ⟨v,rfl⟩ := List.mem_ofFn.mp hq; exact SetDistanceData.height toSet d S hS M hd v
  have havg : LpInputSize.Height M (average I toSet d S hS : ℚ) := by
    simpa only [List.take_length,average] using hprefix (products I toSet d S hS).length
  rintro σ ⟨hn,hweightsσ,hvaluesσ⟩
  let ν := σ.setVar "sum.count" n
  have rc : Run B (.assign "sum.count" (.var "metric.n")) σ ν 2 :=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega : n<B)⟩)
  obtain ⟨μ,rs,ps⟩ := RamProductSum.command_spec B M "flow.weights" (RamSetPotential.targetArray toSet)
    (List.ofFn I.weight) (vector toSet d S hS) (by simp [vector]) hB (by simpa using hvertex)
    (fun q hq => num_bound (hweights q hq)) (fun q hq => den_bound (hweights q hq))
    (fun q hq => num_bound (hvalues q hq)) (fun q hq => den_bound (hvalues q hq))
    (fun q hq => num_bound (hp q hq)) (fun q hq => den_bound (hp q hq))
    (fun i => num_bound (hprefix i)) (fun i => den_bound (hprefix i)) ν
    ⟨by simp [ν],hweightsσ,hvaluesσ⟩
  obtain ⟨τ,rv,pv⟩ := save_spec B (name toSet) (average I toSet d S hS)
    ((num_bound havg).trans_lt hMB) ((den_bound havg).trans_lt hMB) (by cases toSet <;> decide) μ ps.2
  exact ⟨τ,(rc.seq (rs.seq rv)).mono (by simp only [List.length_ofFn,cost]; omega),pv⟩

end Lax455465Proofs.RamPotentialAverage
