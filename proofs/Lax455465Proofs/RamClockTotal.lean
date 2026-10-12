import Lax455465Proofs.RamClockInput
import Lax455465Proofs.RamClockPrepare
import Lax455465Proofs.RamClockedExecution
import Lax455465Proofs.RamAutomaticLayout

namespace Lax455465Proofs.RamClockTotal
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The timeout and virtual word width are computed by fixed Horner
programs from the input's actual binary size. -/
def command (p : Lax808846.Ram.Program) (wc tc : List ℕ) : Com :=
  .seq RamClockInput.command (.seq (RamClockPrepare.boundedCommand wc tc) (RamClockedExecution.outputCommand p))

def cost (p : Lax808846.Ram.Program) (wc tc : List ℕ) (xs : List ℕ) : ℕ :=
  let L := bitSize xs
  let N := RamPolynomial.value tc L
  (12*L+63)*xs.length+6*wc.length+6*tc.length+(4*p.length+32*N+123)*N+74

def Room (xs : List ℕ) (N : ℕ) (σ : Env) : Prop :=
  xs.length ≤ (σ.arrs "input.data").length ∧ xs.length ≤ (σ.arrs "lp.word").length ∧
    xs.length < (σ.arrs "vm.input").length ∧ RamClockedLoop.Room N σ

theorem room_frame {B K N : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K) {xs : List ℕ}
    (h : Room xs N σ) : Room xs N τ := by
  exact ⟨by rw [RamFrames.run_array_length rr]; exact h.1,
    by rw [RamFrames.run_array_length rr]; exact h.2.1,
    by rw [RamFrames.run_array_length rr]; exact h.2.2.1,RamClockedLoop.room_frame rr h.2.2.2⟩

theorem prepare_noWrite (wc tc : List ℕ) : (RamClockPrepare.boundedCommand wc tc).NoWrite :=
  ⟨RamLpNoWrite.prepare wc,RamLpNoWrite.polynomial tc,trivial⟩

/-- Total execution on every input word, including encodings on which the
source program fails to terminate. The emitted output is the precise state
of the source after the computed clock allowance. -/
theorem command_spec (B : ℕ) (p : Lax808846.Ram.Program) (wc tc xs : List ℕ)
    (hB : 2*(2^(RamPolynomial.value wc (bitSize xs)))^2+3 < B)
    (hN : RamPolynomial.value tc (bitSize xs)+1 < B)
    (hallow : RamVirtualConstants.allowance p < B)
    (hlen : xs.length+1 < B) (hsize : bitSize xs+1 < B) (hwords : ∀ a∈xs,a < B)
    (hwidth : RamPolynomial.value wc (bitSize xs+1) < B)
    (htime : RamPolynomial.value tc (bitSize xs+1) < B) :
    Spec B (fun σ => σ.inp=xs.length::xs ∧ Room xs (RamPolynomial.value tc (bitSize xs)) σ ∧ σ.out=[])
      (command p wc tc) (fun _ τ => τ.out=
        (SparseClock.run (RamPolynomial.value wc (bitSize xs)) p (RamPolynomial.value tc (bitSize xs))
          (SparseRam.init (xs.length::xs))).out) (cost p wc tc xs) := by
  rintro σ ⟨hinp,hroom,hout⟩
  obtain ⟨ν,r1,p1⟩ := RamClockInput.command_spec B xs (by omega) (by omega) hwords σ
    ⟨hinp,hroom.1,hroom.2.1⟩
  have hroomν := room_frame r1 hroom
  obtain ⟨μ,r2,p2⟩ := RamClockPrepare.bounded_spec B wc tc xs (by omega) hlen hsize hwords hwidth htime ν
    ⟨p1.1,p1.2,hroomν.2.2.1⟩
  have hroomμ := room_frame r2 hroomν
  have houtμ : μ.out=[] := (r2.out_eq (prepare_noWrite wc tc)).trans ((r1.out_eq (by decide)).trans hout)
  have hp : p.length+1 < B := (RamVirtualConstants.length_bound p).trans hallow
  have hlit : ∀ i∈p,RamVirtualInstruction.LiteralsFit (B-1) i := fun i hi =>
    RamVirtualTraceBounds.literals_mono i (RamVirtualConstants.literals_fit p i hi) (by omega)
  obtain ⟨τ,r3,p3⟩ := RamClockedExecution.output_spec B (RamPolynomial.value wc (bitSize xs))
    (RamPolynomial.value tc (bitSize xs)) p (xs.length::xs) [] hB hN hp hlit (by simpa using hlen)
    (by intro a ha; simp only [List.mem_cons] at ha; rcases ha with rfl | ha; omega; exact hwords a ha) μ
    ⟨⟨p2.1,p2.2.1,by simpa using p2.2.2.1,p2.2.2.2,hroomμ.2.2.2⟩,houtμ⟩
  exact ⟨τ,(r1.seq (r2.seq r3)).mono (by dsimp [cost,RamClockedLoop.cost]; nlinarith),
    by simpa only [List.nil_append] using p3⟩

end Lax455465Proofs.RamClockTotal
