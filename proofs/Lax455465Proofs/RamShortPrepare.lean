import Lax455465Proofs.RamShortScan
import Lax455465Proofs.RamIncidentBounds

namespace Lax455465Proofs.RamShortPrepare
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open LayeredFlowLP LayeredFlowDual LayeredFlowFeasibility RamShortContext RamLayeredSource
open Lax455465.RationalEncoding Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

/-- Buffer sizes record available address space, without initializing
solver data or providing advice to the fixed RAM command. -/
structure Input {n : ℕ} (I : RationalInstance n) (words time : ℕ) (σ : Env) : Prop where
  source : Source I σ
  lpRoom : words < (σ.arrs "lp.word").length
  inputRoom : words < (σ.arrs "vm.input").length
  addressRoom : time < (σ.arrs "vm.addresses").length
  valueRoom : time < (σ.arrs "vm.values").length
  outputRoom : time < (σ.arrs "vm.output").length

def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq RamIncidentMaximum.command (RamShortScan.command p coefficients)

noncomputable def timeBound (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ) : Polynomial ℕ :=
  RamShortScan.timeBound p coefficients TB+Polynomial.C 512*(Polynomial.X+Polynomial.C 1)^4

/-- The capacity maximum, every stopping decision, and the selected primal
certificate are now computed from source capacities by one native command. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (coefficients : List ℕ),
      ∀ {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n),2 ≤ n →
        ∃ (f : ℕ → ℚ≥0) (x : ∀ L,Arc n L → ℚ) (y : ∀ L,Dual n L),
          (∀ L,Feasible I (f L : ℚ) (x L) ∧
            Lax109476.LinearProgram.DualFeasible (program I L) (y L) ∧
            (f L : ℚ)=Lax109476.LinearProgram.dualValue (program I L) (y L)) ∧
          (∀ L,FitsInWords (WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I L))))
            (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f L : ℚ) (x L)) (y L)))) ∧
          ∀ W : ℕ,(RamShortScan.wordBound p WB TB).eval (bitSize (encodeInput kind I)) ≤ W →
            let S := LayeredLpSize.sizeBound.eval (bitSize (encodeInput kind I))
            let R := ShortRationalParameters.maximum I
            let L := ShortLayerSelection.select n (R : ℚ) (fun k => (f k : ℚ))
            Spec (2^W) (Input I S (TB.eval S)) (command p coefficients)
              (fun _ τ => Context I R S (TB.eval S) τ ∧ RamLayeredData.Data I L τ ∧
                Prefix (Lax109476.RationalEncoding.encodeCertificate (.optimal (vector (f L : ℚ) (x L)) (y L)))
                  "vm.output" τ)
              ((timeBound p coefficients TB).eval (bitSize (encodeInput kind I))) := by
  obtain ⟨p,WB,TB,coefficients,hscan⟩ := RamShortScan.exists_program
  refine ⟨p,WB,TB,coefficients,?_⟩
  intro n kind I hn
  obtain ⟨f,x,y,hmath,hfit,hrun⟩ := hscan kind I hn
  refine ⟨f,x,y,hmath,hfit,?_⟩
  intro W hW
  dsimp only
  let b := bitSize (encodeInput kind I)
  let S := LayeredLpSize.sizeBound.eval b
  let M := 2^((b+1)^2)
  have hnbit : n≤b := LpInputSize.input_dimension kind I
  have hwidth : 18*(b+1)^2+4≤W := by
    simp only [RamShortScan.wordBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_comp] at hW
    change _≤W at hW
    dsimp only [b]
    omega
  obtain ⟨hB,hindex⟩ := RamIncidentBounds.fits b n W hnbit hwidth
  have hcap := RamIncidentBounds.capacity_height kind I
  have hp := ShortInputBounds.row_prefix kind I
  intro σ hσ
  obtain ⟨ν,rr,pr⟩ := RamIncidentMaximum.command_spec (2^W) M I (Nat.succ_le_of_lt (Nat.two_pow_pos _)) hB hindex
    (fun u v => (hcap u v).1) (fun u v => (hcap u v).2)
    (fun v i => by simpa only [NNRat.natAbs_num_coe] using (hp v i).1)
    (fun v i => by simpa only [NNRat.den_coe] using (hp v i).2) σ hσ.source
  have hctx : Context I (ShortRationalParameters.maximum I) S (TB.eval S) ν := by
    refine ⟨pr.1,pr.2,?_,?_,?_,?_,?_⟩
    · simpa only [RamFrames.run_array_length rr "lp.word"] using hσ.lpRoom
    · simpa only [RamFrames.run_array_length rr "vm.input"] using hσ.inputRoom
    · simpa only [RamFrames.run_array_length rr "vm.addresses"] using hσ.addressRoom
    · simpa only [RamFrames.run_array_length rr "vm.values"] using hσ.valueRoom
    · simpa only [RamFrames.run_array_length rr "vm.output"] using hσ.outputRoom
  obtain ⟨τ,rs,ps⟩ := hrun W hW ν hctx
  refine ⟨τ,(rr.seq rs).mono ?_,ps⟩
  have hc := RamIncidentBounds.cost n b hnbit
  simp only [timeBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  dsimp only [M,b] at hc ⊢
  omega

end Lax455465Proofs.RamShortPrepare
