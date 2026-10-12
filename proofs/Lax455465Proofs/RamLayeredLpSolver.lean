import Lax455465Proofs.RamLayeredLp
import Lax455465Proofs.RamFlowLpSolver
import Lax455465Proofs.RegisteredLpInvocation

namespace Lax455465Proofs.RamLayeredLpSolver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState LayeredFlowLP LayeredLpFlat RamLayeredData
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open scoped NNRat

/-- One fixed native construction and black-box solver invocation. -/
def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq RamLayeredLp.command (RegisteredLpInvocation.command p coefficients)

def BuildFits (B M n L : ℕ) : Prop :=
  1 ≤ M ∧ M < B ∧ shapeSize n L < B ∧ 2*(n*n)+1 < B ∧ LayeredLpSize.wordLength n L+3 < B

abbrev InvokeFits := RamFlowLpSolver.InvokeFits
abbrev invocationCost := RamFlowLpSolver.invocationCost

/-- Runtime LP construction and execution are connected: the output is
an actual valid certificate for the exact flow LP, with one fixed program
chosen before the graph order or its rational coefficients. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (coefficients : List ℕ),
      ∀ {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n) (L : ℕ),
        ∃ certificate : Certificate (rows n L) (columns n L),
          IsValidCertificate (program I L) certificate ∧
          FitsInWords (WB.eval (bitSize (encodeProgram (program I L)))) (encodeCertificate certificate) ∧
          ∀ (B M : ℕ), BuildFits B M n L →
            InvokeFits B p WB TB (bitSize (encodeProgram (program I L))) →
            (∀ u v, (I.capacity u v).num ≤ M) → (∀ u v, (I.capacity u v).den ≤ M) →
            Spec B (fun σ => Data I L σ ∧ LayeredLpSize.wordLength n L < (σ.arrs "lp.word").length ∧
              (encodeProgram (program I L)).length < (σ.arrs "vm.input").length ∧
              TB.eval (bitSize (encodeProgram (program I L))) < (σ.arrs "vm.addresses").length ∧
              TB.eval (bitSize (encodeProgram (program I L))) < (σ.arrs "vm.values").length ∧
              TB.eval (bitSize (encodeProgram (program I L))) < (σ.arrs "vm.output").length)
              (command p coefficients)
              (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ ∧
                τ.vars "vm.outputLength" = (encodeCertificate certificate).length ∧ τ.vars "vm.running" = 0)
              (RamLayeredLp.cost n L+invocationCost p coefficients TB
                (bitSize (encodeProgram (program I L))) (encodeProgram (program I L)).length) := by
  obtain ⟨p,WB,TB,coefficients,hcoeff,hinvoke⟩ := RegisteredLpInvocation.exists_program
  refine ⟨p,WB,TB,coefficients,?_⟩
  intro n I L
  obtain ⟨certificate,hvalid,hfit,hsolve⟩ := hinvoke (rows n L) (columns n L) (program I L)
  refine ⟨certificate,hvalid,fun x hx => hfit x (List.mem_append_right _ hx),?_⟩
  rintro B M ⟨hM,hMB,hB,hcapindex,hlen⟩
    ⟨hsize,hpoly,hvirtual,htime,hallow⟩ hcapnum hcapden
  rintro σ ⟨hdata,hroom,hinputRoom,hA,hV,hO⟩
  obtain ⟨ν,hbuild,hbuilt⟩ := RamLayeredLp.command_spec B M I hM hMB hB hcapindex hlen
    hcapnum hcapden σ ⟨hdata,hroom⟩
  have hinputν : (encodeProgram (program I L)).length < (ν.arrs "vm.input").length := by
    rwa [RamFrames.run_array_length hbuild "vm.input"]
  have hAν : TB.eval (bitSize (encodeProgram (program I L))) < (ν.arrs "vm.addresses").length := by
    rwa [RamFrames.run_array_length hbuild "vm.addresses"]
  have hVν : TB.eval (bitSize (encodeProgram (program I L))) < (ν.arrs "vm.values").length := by
    rwa [RamFrames.run_array_length hbuild "vm.values"]
  have hOν : TB.eval (bitSize (encodeProgram (program I L))) < (ν.arrs "vm.output").length := by
    rwa [RamFrames.run_array_length hbuild "vm.output"]
  obtain ⟨τ,hrun,hpost⟩ := hsolve B hsize hpoly hvirtual htime hallow ν
    ⟨hbuilt.2.1,hbuilt.2.2,hinputν,hAν,hVν,hOν⟩
  exact ⟨τ,hbuild.seq hrun,hpost⟩

end Lax455465Proofs.RamLayeredLpSolver
