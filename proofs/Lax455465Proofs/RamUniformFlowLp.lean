import Lax455465Proofs.RamFlowHostWidth

namespace Lax455465Proofs.RamUniformFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP RamFlowData
open Lax455465.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open scoped NNRat

/-- Uniform native flow-LP component: one fixed command and polynomial
instruction and word bounds, chosen before all input dimensions and data.
Reserved array extents are proof bookkeeping, not initialized oracle data. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime : Polynomial ℕ),
      ∀ {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n),
        ∃ certificate : Certificate (rows n) (columns n),
          IsValidCertificate (program I) certificate ∧
          ∀ W : ℕ, wordBound.eval (bitSize (encodeInput kind I)) ≤ W →
            Spec (2^W) (fun σ => Data I σ ∧ RamFlowLp.wordLength n < (σ.arrs "lp.word").length ∧
              (Lax109476.RationalEncoding.encodeProgram (program I)).length < (σ.arrs "vm.input").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.addresses").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.values").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I))) < (σ.arrs "vm.output").length)
              c (fun _ τ => Prefix (Lax109476.RationalEncoding.encodeCertificate certificate) "vm.output" τ ∧
                τ.vars "vm.outputLength" = (Lax109476.RationalEncoding.encodeCertificate certificate).length ∧
                τ.vars "vm.running" = 0) (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨p,WB,TB,coefficients,hsolve⟩ := RamFlowLpSolver.exists_program
  refine ⟨RamFlowLpSolver.command p coefficients,RamFlowSolverBounds.timeBound p coefficients TB,
    RamFlowHostWidth.wordBound p WB TB,TB,?_⟩
  intro n kind I
  obtain ⟨certificate,hvalid,hcorrect⟩ := hsolve I
  refine ⟨certificate,hvalid,?_⟩
  intro W hW
  let L := bitSize (encodeInput kind I)
  let M := 2^L
  obtain ⟨hbuildFits,hinvokeFits⟩ := RamFlowHostWidth.sufficient p WB TB kind I W hW
  have hnum : ∀ z, (I.weight z).num ≤ M := fun z => by
    simpa only [NNRat.natAbs_num_coe] using (LpInputSize.weight_height kind I z).1
  have hden : ∀ z, (I.weight z).den ≤ M := fun z => by
    simpa only [NNRat.den_coe] using (LpInputSize.weight_height kind I z).2
  have hcapnum : ∀ u v, (I.capacity u v).num ≤ M := fun u v => by
    simpa only [NNRat.natAbs_num_coe] using (LpInputSize.capacity_height kind I u v).1
  have hcapden : ∀ u v, (I.capacity u v).den ≤ M := fun u v => by
    simpa only [NNRat.den_coe] using (LpInputSize.capacity_height kind I u v).2
  have hbounded := hcorrect (2^W) M hbuildFits hinvokeFits hnum hden hcapnum hcapden
  intro σ hpre
  obtain ⟨τ,hrun,hpost⟩ := hbounded σ hpre
  exact ⟨τ,hrun.mono (RamFlowSolverBounds.cost_bound p coefficients TB kind I),hpost⟩

end Lax455465Proofs.RamUniformFlowLp
