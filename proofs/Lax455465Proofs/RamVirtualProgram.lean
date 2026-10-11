import Lax455465Proofs.RamWordOps
import Lax455465Proofs.RamSparseRead

namespace Lax455465Proofs.RamVirtualProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Reduction to the chosen virtual word width uses native division and
truncated subtraction, rather than the host's implicit word modulus. -/
def remainder (e : Expr) : Expr := .sub e
  (.mul (.div e (.var "vm.modulus")) (.var "vm.modulus"))

theorem evalB_remainder {B M value : ℕ} {σ : Env} {e : Expr}
    (he : e.evalB B σ = some value) (hM : σ.vars "vm.modulus" = M)
    (hMB : M < B) (hv : value < B) :
    (remainder e).evalB B σ = some (value % M) := by
  have hmod : (Expr.var "vm.modulus").evalB B σ = some M := by
    rw [evalB_var_iff]
    exact ⟨hM.symm, hM ▸ hMB⟩
  have hd := (Nat.div_le_self value M).trans_lt hv
  have hp := (Nat.div_mul_le_self value M).trans_lt hv
  have hs := (Nat.sub_le value (value / M * M)).trans_lt hv
  have hdiv := evalB_bin (op := .div) he hmod hd
  have hmul := evalB_bin (op := .mul) hdiv hmod hp
  have hsub := evalB_bin (op := .sub) he hmul hs
  change (remainder e).evalB B σ = some (value - value / M * M) at hsub
  simpa only [Nat.mod_def, Nat.mul_comm] using hsub

def increment : Com := .assign "vm.pc" (.add (.var "vm.pc") (.lit 1))

def writeBack (target value : Expr) : Com := .seq
  (.assign "vm.target" (remainder target))
  (.seq (.assign "vm.result" (remainder value))
    (.seq RamSparseRead.write increment))

def operands (left right : ℕ) (body : Com) : Com := .seq
  (RamSparseRead.read "vm.left" (remainder (.lit left)))
  (.seq (RamSparseRead.read "vm.right" (remainder (.lit right))) body)

def binary (op : Bop) (target left right : ℕ) : Com := operands left right
  (.seq (RamWordOps.binary op) (writeBack (.lit target) (.var "vm.result")))

def stop : Com := .assign "vm.running" (.lit 0)

/-- A fixed native command for each virtual instruction. Virtual input and
output occupy separate host buffers; their tape operations do not consume
the host input or prematurely emit an LP certificate as the LR output. -/
def instruction : Lax808846.Ram.Instr → Com
  | .set a value => writeBack (.lit a) (.lit value)
  | .load a b => .seq (RamSparseRead.read "vm.left" (remainder (.lit b)))
      (.seq (RamSparseRead.read "vm.result" (remainder (.var "vm.left")))
        (writeBack (.lit a) (.var "vm.result")))
  | .store a b => .seq (RamSparseRead.read "vm.target" (remainder (.lit a)))
      (.seq (RamSparseRead.read "vm.result" (remainder (.lit b)))
        (writeBack (.var "vm.target") (.var "vm.result")))
  | .add a b c => binary .add a b c
  | .sub a b c => binary .sub a b c
  | .mul a b c => binary .mul a b c
  | .div a b c => binary .div a b c
  | .and a b c => binary .and a b c
  | .shiftl a b c => operands b c
      (.seq RamWordOps.shift (writeBack (.lit a) (.var "vm.result")))
  | .not a b => .seq (RamSparseRead.read "vm.left" (remainder (.lit b)))
      (.seq RamWordOps.complement (writeBack (.lit a) (.var "vm.result")))
  | .jump label => .assign "vm.pc" (.lit label)
  | .jzero a label => .seq (RamSparseRead.read "vm.left" (remainder (.lit a)))
      (.ite (.eq (.var "vm.left") (.lit 0)) (.assign "vm.pc" (.lit label)) increment)
  | .jeof label => .ite (.eq (.var "vm.cursor") (.var "vm.inputLength"))
      (.assign "vm.pc" (.lit label)) increment
  | .inputLength a => writeBack (.lit a) (.var "vm.inputLength")
  | .inputLoad a b => .seq (RamSparseRead.read "vm.left" (remainder (.lit b)))
      (.seq (.ite (.lt (.var "vm.left") (.var "vm.inputLength"))
        (.assign "vm.result" (.get "vm.input" (.var "vm.left")))
        (.assign "vm.result" (.lit 0)))
        (writeBack (.lit a) (.var "vm.result")))
  | .halt => stop
  | .read a => .ite (.lt (.var "vm.cursor") (.var "vm.inputLength"))
      (.seq (.seq (.assign "vm.result" (.get "vm.input" (.var "vm.cursor")))
        (.assign "vm.cursor" (.add (.var "vm.cursor") (.lit 1))))
        (writeBack (.lit a) (.var "vm.result"))) stop
  | .write a => .seq (RamSparseRead.read "vm.left" (remainder (.lit a)))
      (.seq (.store "vm.output" (.var "vm.outputLength") (remainder (.var "vm.left")))
        (.seq (.assign "vm.outputLength" (.add (.var "vm.outputLength") (.lit 1))) increment))

/-- Program instructions are fixed at elaboration, and only the virtual
program counter is runtime data. Falling outside the source program halts. -/
def dispatch : List Lax808846.Ram.Instr → ℕ → Com
  | [], _ => stop
  | i :: rest, offset => .ite (.eq (.var "vm.pc") (.lit offset))
      (instruction i) (dispatch rest (offset + 1))

def initCommand : Com := .seq (.assign "vm.pc" (.lit 0))
  (.seq (.assign "vm.count" (.lit 0))
    (.seq (.assign "vm.cursor" (.lit 0))
      (.seq (.assign "vm.outputLength" (.lit 0)) (.assign "vm.running" (.lit 1)))))

/-- The one fixed native host command for a black-box registered RAM
program. It executes through separate virtual-memory and tape buffers. -/
def execute (p : Lax808846.Ram.Program) : Com :=
  .seq RamWordOps.modulus (.seq initCommand
    (.while (.lt (.lit 0) (.var "vm.running")) (dispatch p 0)))

end Lax455465Proofs.RamVirtualProgram
