import Lax455465Proofs.RamClockedLoop
import Lax455465Proofs.RamEmitWords
import Lax455465Proofs.RamLpNoWrite

namespace Lax455465Proofs.RamClockedExecution
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamVirtualCore RamVirtualInstruction

def boot : Com := .seq RamWordOps.modulus RamVirtualProgram.initCommand
def command (p : Lax808846.Ram.Program) : Com := .seq boot (RamClockedLoop.command p)

theorem command_spec (B w N : ℕ) (p : Lax808846.Ram.Program) (input : List ℕ)
    (hB : 2*(2^w)^2+3 < B) (hN : N+1 < B) (hp : p.length+1 < B)
    (hlit : ∀ i∈p,LiteralsFit (B-1) i) (hinput : input.length < B) (hwords : ∀ a∈input,a < B) :
    Spec B (fun σ => σ.vars "vm.width"=w ∧ Prefix input "vm.input" σ ∧
      σ.vars "vm.inputLength"=input.length ∧ σ.vars "clock.remaining"=N ∧ RamClockedLoop.Room N σ)
      (command p) (fun _ τ => Represents w (SparseClock.run w p N (SparseRam.init input)) τ)
      (RamClockedLoop.cost p N N+14) := by
  rintro σ ⟨hw,hin,hlen,hcount,hroom⟩
  have hM : 2^w < B := by nlinarith [Nat.two_pow_pos w]
  obtain ⟨ν,r1,p1⟩ := RamWordOps.modulus_spec B w hM σ hw
  obtain ⟨μ,r2,p2⟩ := RamVirtualState.init_spec B w input (by omega) ν
    ⟨p1,(r1.frame_var _ (by decide)).trans hw,
      by simpa only [Prefix,r1.frame_arr "vm.input" (by decide)] using hin,
      (r1.frame_var _ (by decide)).trans hlen⟩
  have rr := r1.seq r2
  obtain ⟨τ,r3,p3⟩ := RamClockedLoop.command_spec B w N N p (SparseRam.init input) hB hN le_rfl hp hlit
    (by simp [SparseBounds.MemoryWords,SparseRam.init]) hinput hwords (by simp [SparseRam.init]; omega)
    (by simp [SparseRam.init]) (by simp [SparseRam.init]) μ
    ⟨p2.1,(rr.frame_var _ (by decide)).trans hcount,RamClockedLoop.room_frame rr hroom⟩
  exact ⟨τ,(rr.seq r3).mono (by omega),p3.1⟩

def emit : Com := .seq (.assign "emit.count" (.var "vm.outputLength")) (RamEmitWords.command "vm.output" 1)
def outputCommand (p : Lax808846.Ram.Program) : Com := .seq (command p) emit

theorem emit_spec (B w N : ℕ) (s : SparseRam.SparseState) (front : List ℕ)
    (h1 : 1 < B) (hN : N+1 < B) (hM : 2^w < B) (hlen : s.out.length ≤ N)
    (hwords : SparseClock.OutputWords w s) :
    Spec B (fun σ => Represents w s σ ∧ σ.out=front) emit
      (fun _ τ => τ.out=front++s.out) (13*N+8) := by
  rintro σ ⟨hrep,hout⟩
  let ν := σ.setVar "emit.count" s.out.length
  have hc := hrep.2.2.2.2.2.2
  have r1 : Run B (.assign "emit.count" (.var "vm.outputLength")) σ ν 2 := Run.assign (by
    rw [evalB_var_iff]; exact ⟨hc.symm,hc ▸ (by omega : s.out.length < B)⟩)
  obtain ⟨τ,r2,p2⟩ := RamEmitWords.command_spec B "vm.output" 1 s.out front h1 h1
    (by omega) (by omega) (fun a ha => (hwords a ha).trans hM) ν
    ⟨by intro i hi; simpa only [Nat.one_mul,ν,arrs_setVar] using hrep.2.2.2.2.2.1 i hi,
      by simp [ν],hout⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩


theorem noWrite (p : Lax808846.Ram.Program) : (command p).NoWrite := by
  constructor
  · decide
  · change True ∧ (RamVirtualProgram.dispatch p 0).NoWrite ∧ True
    exact ⟨trivial,RamLpNoWrite.dispatch p 0,trivial⟩

theorem output_spec (B w N : ℕ) (p : Lax808846.Ram.Program) (input front : List ℕ)
    (hB : 2*(2^w)^2+3 < B) (hN : N+1 < B) (hp : p.length+1 < B)
    (hlit : ∀ i∈p,LiteralsFit (B-1) i) (hinput : input.length < B) (hwords : ∀ a∈input,a < B) :
    Spec B (fun σ => (σ.vars "vm.width"=w ∧ Prefix input "vm.input" σ ∧
      σ.vars "vm.inputLength"=input.length ∧ σ.vars "clock.remaining"=N ∧ RamClockedLoop.Room N σ) ∧ σ.out=front)
      (outputCommand p) (fun _ τ => τ.out=front++(SparseClock.run w p N (SparseRam.init input)).out)
      (RamClockedLoop.cost p N N+13*N+22) := by
  rintro σ ⟨hσ,hout⟩
  obtain ⟨ν,r1,p1⟩ := command_spec B w N p input hB hN hp hlit hinput hwords σ hσ
  have hM : 2^w < B := by nlinarith [Nat.two_pow_pos w]
  have hlen : (SparseClock.run w p N (SparseRam.init input)).out.length ≤ N := by
    simpa only [SparseRam.init,List.length_nil,Nat.zero_add] using SparseClock.run_output_length w p N (SparseRam.init input)
  have houtput := SparseClock.run_output_words w p N (SparseRam.init input) (by simp [SparseClock.OutputWords,SparseRam.init])
  obtain ⟨τ,r2,p2⟩ := emit_spec B w N _ front (by omega) hN hM hlen houtput ν
    ⟨p1,(r1.out_eq (noWrite p)).trans hout⟩
  exact ⟨τ,(r1.seq r2).mono (by omega),p2⟩

end Lax455465Proofs.RamClockedExecution
