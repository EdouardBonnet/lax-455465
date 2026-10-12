import Lax455465Proofs.RamLayeredHostWidth
import Lax455465Proofs.RamLayeredScope

namespace Lax455465Proofs.RamUniformLayeredLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState LayeredFlowLP LayeredLpFlat RamLayeredData
open Lax455465.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

/-- Uniform native flow-LP component: one fixed command and polynomial
instruction and word bounds, chosen before all input dimensions and data.
Reserved array extents are proof bookkeeping, not initialized oracle data. -/
theorem exists_program :
    ∃ (c : Com) (timeBound wordBound sourceTime sourceWord : Polynomial ℕ),
      c.NoWrite ∧ ∀ {n : ℕ} (kind : Lax455465.ProductNetwork.EdgeKind) (I : RationalInstance n) (layers : ℕ), 2 ≤ n → layers ≤ n →
        ∃ certificate : Certificate (rows n layers) (columns n layers),
          IsValidCertificate (program I layers) certificate ∧
          FitsInWords (sourceWord.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))))
            (Lax109476.RationalEncoding.encodeCertificate certificate) ∧
          ∀ W : ℕ, wordBound.eval (bitSize (encodeInput kind I)) ≤ W →
            Spec (2^W) (fun σ => Data I layers σ ∧ LayeredLpSize.wordLength n layers < (σ.arrs "lp.word").length ∧
              (Lax109476.RationalEncoding.encodeProgram (program I layers)).length < (σ.arrs "vm.input").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))) < (σ.arrs "vm.addresses").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))) < (σ.arrs "vm.values").length ∧
              sourceTime.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))) < (σ.arrs "vm.output").length)
              c (fun σ τ => Data I layers τ ∧
                τ.vars "flow.kind" = σ.vars "flow.kind" ∧
                (∀ x ∈ Lax109476.RationalEncoding.encodeCertificate certificate, x < 2^W) ∧ Prefix (Lax109476.RationalEncoding.encodeCertificate certificate) "vm.output" τ ∧
                τ.vars "vm.outputLength" = (Lax109476.RationalEncoding.encodeCertificate certificate).length ∧
                τ.vars "vm.running" = 0) (timeBound.eval (bitSize (encodeInput kind I))) := by
  obtain ⟨p,WB,TB,coefficients,hsolve⟩ := RamLayeredLpSolver.exists_program
  refine ⟨RamLayeredLpSolver.command p coefficients,RamLayeredSolverBounds.timeBound p coefficients TB,
    RamLayeredHostWidth.wordBound p WB TB,TB,WB,RamLayeredScope.solver_nowrite p coefficients,?_⟩
  intro n kind I layers hn hlayers
  obtain ⟨certificate,hvalid,hfit,hcorrect⟩ := hsolve I layers
  refine ⟨certificate,hvalid,hfit,?_⟩
  intro W hW
  let L := bitSize (encodeInput kind I)
  let M := 2^L
  obtain ⟨hbuildFits,hinvokeFits⟩ := RamLayeredHostWidth.sufficient p WB TB kind I layers hn hlayers W hW
  have hcapnum : ∀ u v, (I.capacity u v).num ≤ M := fun u v => by
    simpa only [NNRat.natAbs_num_coe] using (LpInputSize.capacity_height kind I u v).1
  have hcapden : ∀ u v, (I.capacity u v).den ≤ M := fun u v => by
    simpa only [NNRat.den_coe] using (LpInputSize.capacity_height kind I u v).2
  have hbounded := hcorrect (2^W) M hbuildFits hinvokeFits hcapnum hcapden
  intro σ hpre
  obtain ⟨τ,hrun,hpost⟩ := hbounded σ hpre
  exact ⟨τ,hrun.mono (RamLayeredSolverBounds.cost_bound p coefficients TB kind I layers hlayers),
    RamLayeredScope.solver_data hrun I hpre.1,
    hrun.frame_var "flow.kind" (by
      have hb : "flow.kind" ∉ RamLayeredLp.command.wvars := by decide
      have hi := RamLpPrivateScope.invocation_vars p coefficients "flow.kind" (by decide)
      exact fun h => (List.mem_append.mp h).elim hb hi),
    fun x hx => lt_trans (hfit x hx) (by
      obtain ⟨_,_,hv,_,_⟩ := hinvokeFits
      nlinarith [Nat.two_pow_pos (WB.eval (bitSize (Lax109476.RationalEncoding.encodeProgram (program I layers))))]),hpost⟩

end Lax455465Proofs.RamUniformLayeredLp
