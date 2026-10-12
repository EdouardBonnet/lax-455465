import Lax455465Proofs.SparseClock
import Lax455465Proofs.RamVirtualDispatch
import Lax455465Proofs.RamFrames

namespace Lax455465Proofs.RamClockedLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamVirtualCore RamVirtualInstruction

def body (p : Lax808846.Ram.Program) : Com := .seq (.assign "vm.running" (.lit 1))
  (.seq (RamVirtualProgram.dispatch p 0) (.assign "clock.remaining" (.sub (.var "clock.remaining") (.lit 1))))
def command (p : Lax808846.Ram.Program) : Com := .while (.lt (.lit 0) (.var "clock.remaining")) (body p)
def cost (p : Lax808846.Ram.Program) (N k : ℕ) : ℕ := (4*p.length+32*N+110)*k+4

theorem instruction_frame (i : Lax808846.Ram.Instr) : "clock.remaining" ∉ (RamVirtualProgram.instruction i).wvars := by
  cases i <;> dsimp [RamVirtualProgram.instruction,RamVirtualProgram.writeBack,RamVirtualProgram.increment,
    RamVirtualProgram.operands,RamVirtualProgram.binary,RamVirtualProgram.stop,RamSparseRead.read,RamSparseRead.write,
    RamSparseMemory.lookup,RamSparseMemory.scanStep,RamSparseMemory.put,RamWordOps.binary,RamWordOps.reduce,
    RamWordOps.shift,RamWordOps.complement,Com.wvars] <;> decide

theorem dispatch_frame (p : List Lax808846.Ram.Instr) (offset : ℕ) :
    "clock.remaining" ∉ (RamVirtualProgram.dispatch p offset).wvars := by
  induction p generalizing offset with
  | nil => simp [RamVirtualProgram.dispatch,RamVirtualProgram.stop,Com.wvars]
  | cons i rest ih =>
    simp only [RamVirtualProgram.dispatch,Com.wvars,List.mem_append,not_or]
    exact ⟨instruction_frame i,ih (offset+1)⟩

def Room (N : ℕ) (σ : Env) : Prop :=
  N < (σ.arrs "vm.addresses").length ∧ N < (σ.arrs "vm.values").length ∧ N < (σ.arrs "vm.output").length

theorem room_frame {B K N : ℕ} {c : Com} {σ τ : Env} (rr : Run B c σ τ K) (h : Room N σ) : Room N τ := by
  simpa only [Room,RamFrames.run_array_length rr] using h

set_option maxHeartbeats 1600000 in
/-- Execute exactly the runtime clock allowance, freezing the simulated
state after a halt. The source program may fail to halt: termination of this
native loop requires no source-execution witness. -/
theorem command_spec (B w N k : ℕ) (p : Lax808846.Ram.Program) (s : SparseRam.SparseState)
    (hB : 2*(2^w)^2+3 < B) (hN : N+1 < B) (hk : k ≤ N)
    (hp : p.length+1 < B) (hlit : ∀ i∈p,LiteralsFit (B-1) i)
    (hwords : SparseBounds.MemoryWords w s.memory)
    (hinput : s.input.length < B) (hinputWords : ∀ x∈s.input,x < B)
    (hpc : s.pc+1 < B) (hm : s.memory.length+k ≤ N) (ho : s.out.length+k ≤ N) :
    Spec B (fun σ => Represents w s σ ∧ σ.vars "clock.remaining"=k ∧ Room N σ) (command p)
      (fun _ τ => Represents w (SparseClock.run w p k s) τ ∧ τ.vars "clock.remaining"=0 ∧ Room N τ) (cost p N k) := by
  have h1 : 1 < B := by omega
  induction k generalizing s with
  | zero =>
    rintro σ ⟨hrep,hclock,hroom⟩
    have hc : (Cond.lt (.lit 0) (.var "clock.remaining")).evalB B σ=some false := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hclock ▸ (by omega : 0 < B))),hclock]
      rfl
    exact ⟨σ,Run.while_false hc,hrep,hclock,hroom⟩
  | succ k ih =>
    rintro σ ⟨hrep,hclock,hroom⟩
    have hc : (Cond.lt (.lit 0) (.var "clock.remaining")).evalB B σ=some true := by
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hclock ▸ (by omega : k+1 < B))),hclock]
      simp
    let ν := σ.setVar "vm.running" 1
    have r1 : Run B (.assign "vm.running" (.lit 1)) σ ν 2 := Run.assign (evalB_lit h1)
    have hrepν : Represents w s ν := by
      simpa only [Represents,Core,Tapes,RamSparseRead.Representation,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hrep
    obtain ⟨μ,r2,p2⟩ := RamVirtualDispatch.dispatch_spec B w s p 0 hB
      (fun i hi => RamVirtualTraceBounds.literals_mono i (hlit i hi) (by omega)) (by omega)
      hwords hinput hinputWords hpc (by omega) (by omega) ν
      ⟨hrepν,by simp [ν],by dsimp [ν]; exact lt_of_le_of_lt (by omega) hroom.1,
        by dsimp [ν]; exact lt_of_le_of_lt (by omega) hroom.2.1,
        by dsimp [ν]; exact lt_of_le_of_lt (by omega) hroom.2.2⟩
    have hnext : Represents w (SparseClock.next w p s) μ := by
      rw [RamVirtualDispatch.result_zero] at p2
      cases hs : SparseRam.step w p s <;>
        simp only [SparseClock.next,hs,Option.getD_none,Option.getD_some] at p2 ⊢ <;> exact p2.1
    have hclockμ : μ.vars "clock.remaining"=k+1 := (r2.frame_var _ (dispatch_frame p 0)).trans (by simpa [ν] using hclock)
    let ξ := μ.setVar "clock.remaining" k
    have r3 : Run B (.assign "clock.remaining" (.sub (.var "clock.remaining") (.lit 1))) μ ξ 4 := by
      have he := evalB_bin (op := .sub)
        (show (Expr.var "clock.remaining").evalB B μ=some (k+1) from by
          rw [evalB_var_iff]; exact ⟨hclockμ.symm,hclockμ ▸ (by omega : k+1 < B)⟩)
        (evalB_lit h1) (by dsimp [Bop.apply]; omega)
      exact Run.assign (by simpa only [Bop.apply,Nat.add_sub_cancel] using he)
    have hrepξ : Represents w (SparseClock.next w p s) ξ := by
      simpa only [Represents,Core,Tapes,RamSparseRead.Representation,Prefix,ξ,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hnext
    have hroomξ := room_frame (r1.seq (r2.seq r3)) hroom
    obtain ⟨τ,r4,p4⟩ := ih (SparseClock.next w p s) (by omega)
      (SparseClock.next_words w p s hwords) (by rwa [SparseClock.next_input])
      (by simpa only [SparseClock.next_input] using hinputWords)
      (SparseClock.next_pc B w p s hp hlit hpc)
      (by have := SparseClock.next_memory w p s; omega) (by have := SparseClock.next_output w p s; omega)
      ξ ⟨hrepξ,by simp [ξ],hroomξ⟩
    obtain ⟨a,ha,ra⟩ := r1.seq (r2.seq r3)
    obtain ⟨b,hb,rb⟩ := r4
    refine ⟨τ,⟨4+a+b,?_,BigStepB.while_true hc ra rb⟩,p4⟩
    have hmN : s.memory.length ≤ N := by omega
    dsimp [cost] at hb ⊢
    nlinarith

end Lax455465Proofs.RamClockedLoop
