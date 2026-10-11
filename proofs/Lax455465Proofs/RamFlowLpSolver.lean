import Lax455465Proofs.RamFlowLp
import Lax455465Proofs.RegisteredLpInvocation

namespace Lax455465Proofs.RamFlowLpSolver

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP RamFlowData
open Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open scoped NNRat

/-- One fixed native construction and black-box solver invocation. -/
def command (p : Lax808846.Ram.Program) (coefficients : List ℕ) : Com :=
  .seq RamFlowLp.command (RegisteredLpInvocation.command p coefficients)

def BuildFits (B M n : ℕ) : Prop :=
  1 ≤ M ∧ 2*M^2+3 < B ∧ 2*n+1 < B ∧ n*n < B ∧ (n*n)*n < B ∧
    rows n < B ∧ columns n < B ∧ rows n*columns n < B ∧ 2*(n*n)+1 < B ∧ RamFlowLp.wordLength n+3 < B

def InvokeFits (B : ℕ) (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (s : ℕ) : Prop :=
  s+1 < B ∧ WB.eval (s+1) < B ∧ 2*(2^WB.eval s)^2+3 < B ∧ TB.eval s+1 < B ∧
    RamVirtualConstants.allowance p < B

def invocationCost (p : Lax808846.Ram.Program) (coefficients : List ℕ) (TB : Polynomial ℕ)
    (s len : ℕ) : ℕ :=
  ((12*s+39)*len+6*coefficients.length+29)+((TB.eval s+1)*(4*p.length+32*TB.eval s+104)+18)

/-- Runtime LP construction and execution are connected: the output is
an actual valid certificate for the exact flow LP, with one fixed program
chosen before the graph order or its rational coefficients. -/
theorem exists_program :
    ∃ (p : Lax808846.Ram.Program) (WB TB : Polynomial ℕ) (coefficients : List ℕ),
      ∀ {n : ℕ} (I : Lax455465.RationalEncoding.RationalInstance n),
        ∃ certificate : Certificate (rows n) (columns n),
          IsValidCertificate (program I) certificate ∧
          ∀ (B M : ℕ), BuildFits B M n →
            InvokeFits B p WB TB (bitSize (encodeProgram (program I))) →
            (∀ z, (I.weight z).num ≤ M) → (∀ z, (I.weight z).den ≤ M) →
            (∀ u v, (I.capacity u v).num ≤ M) → (∀ u v, (I.capacity u v).den ≤ M) →
            Spec B (fun σ => Data I σ ∧ RamFlowLp.wordLength n < (σ.arrs "lp.word").length ∧
              (encodeProgram (program I)).length < (σ.arrs "vm.input").length ∧
              TB.eval (bitSize (encodeProgram (program I))) < (σ.arrs "vm.addresses").length ∧
              TB.eval (bitSize (encodeProgram (program I))) < (σ.arrs "vm.values").length ∧
              TB.eval (bitSize (encodeProgram (program I))) < (σ.arrs "vm.output").length)
              (command p coefficients)
              (fun _ τ => Prefix (encodeCertificate certificate) "vm.output" τ ∧
                τ.vars "vm.outputLength" = (encodeCertificate certificate).length ∧ τ.vars "vm.running" = 0)
              (RamFlowLp.cost n M+invocationCost p coefficients TB
                (bitSize (encodeProgram (program I))) (encodeProgram (program I)).length) := by
  obtain ⟨p,WB,TB,coefficients,hcoeff,hinvoke⟩ := RegisteredLpInvocation.exists_program
  refine ⟨p,WB,TB,coefficients,?_⟩
  intro n I
  obtain ⟨certificate,hvalid,hfit,hsolve⟩ := hinvoke (rows n) (columns n) (program I)
  refine ⟨certificate,hvalid,?_⟩
  rintro B M ⟨hM,hB,hni,hn2,hn3,hr,hc,hm,hcapindex,hlen⟩
    ⟨hsize,hpoly,hvirtual,htime,hallow⟩ hnum hden hcapnum hcapden
  rintro σ ⟨hdata,hroom,hinputRoom,hA,hV,hO⟩
  obtain ⟨ν,hbuild,hbuilt⟩ := RamFlowLp.command_spec B M I hM hB hni hn2 hn3 hr hc hm hcapindex hlen
    hnum hden hcapnum hcapden σ ⟨hdata,hroom⟩
  have hinputν : (encodeProgram (program I)).length < (ν.arrs "vm.input").length := by
    rwa [RamFrames.run_array_length hbuild "vm.input"]
  have hAν : TB.eval (bitSize (encodeProgram (program I))) < (ν.arrs "vm.addresses").length := by
    rwa [RamFrames.run_array_length hbuild "vm.addresses"]
  have hVν : TB.eval (bitSize (encodeProgram (program I))) < (ν.arrs "vm.values").length := by
    rwa [RamFrames.run_array_length hbuild "vm.values"]
  have hOν : TB.eval (bitSize (encodeProgram (program I))) < (ν.arrs "vm.output").length := by
    rwa [RamFrames.run_array_length hbuild "vm.output"]
  obtain ⟨τ,hrun,hpost⟩ := hsolve B hsize hpoly hvirtual htime hallow ν
    ⟨hbuilt.2.1,hbuilt.2.2,hinputν,hAν,hVν,hOν⟩
  exact ⟨τ,hbuild.seq hrun,hpost⟩

end Lax455465Proofs.RamFlowLpSolver
