import Lax808846Proofs.Compile
import Lax808846.Ram
import Std.Data.HashMap

/-! Shared harness for executing the compiled registered word RAM.
`none` means fuel exhaustion or termination without the compiler's explicit halt. A successful check therefore verifies
both the output and termination within the stated instruction allowance.
The test programs read their inputs from the standard zero-memory state.
-/
open Lax808846Proofs.Imp Lax808846Proofs.Compile
namespace Checks

def expressionNames : Expr → List String × List String
  | .lit _ => ([], [])
  | .var x => ([x], [])
  | .get a i => let old := expressionNames i; (old.1, a :: old.2)
  | .bin _ e f => let a := expressionNames e; let b := expressionNames f; (a.1 ++ b.1, a.2 ++ b.2)

def conditionNames : Cond → List String × List String
  | .eq e f | .lt e f => let a := expressionNames e; let b := expressionNames f; (a.1 ++ b.1, a.2 ++ b.2)

def commandNames : Com → List String × List String
  | .skip => ([], [])
  | .assign x e => let a := expressionNames e; (x :: a.1, a.2)
  | .store x i e => let a := expressionNames i; let b := expressionNames e; (a.1 ++ b.1, x :: (a.2 ++ b.2))
  | .seq c d => let a := commandNames c; let b := commandNames d; (a.1 ++ b.1, a.2 ++ b.2)
  | .ite b c d => let a := conditionNames b; let x := commandNames c; let y := commandNames d;
      (a.1 ++ x.1 ++ y.1, a.2 ++ x.2 ++ y.2)
  | .while b c => let a := conditionNames b; let x := commandNames c; (a.1 ++ x.1, a.2 ++ x.2)
  | .read x => ([x], [])
  | .write e => expressionNames e

def runToHalt (width : ℕ) (p : Lax808846.Ram.Program) :
    ℕ → Lax808846.Ram.State → Option (List ℕ)
  | 0, _ => none
  | fuel + 1, s => match Lax808846.Ram.step width p s with
    | none => match p[s.pc]? with
      | some .halt => some s.out
      | _ => none
    | some t => runToHalt width p fuel t

def executeCompiled (layout : Layout) (width fuel : ℕ)
    (command : Com) (input : List ℕ) : Option (List ℕ) :=
  runToHalt width (compileProgram layout command) fuel
    (Lax808846.Ram.initState input)

/-- The memory cell changed by an instruction, read from the old state.
All actual arithmetic, input, output, and control use the registered effect. -/
def writtenAddress (width : ℕ) (i : Lax808846.Ram.Instr) (s : Lax808846.Ram.State) : Option ℕ :=
  match i with
  | .set a _ | .load a _ | .add a _ _ | .sub a _ _ | .mul a _ _
  | .div a _ _ | .and a _ _ | .shiftl a _ _ | .not a _ | .read a
  | .inputLength a | .inputLoad a _ => some (a % 2^width)
  | .store a _ => some (s.mem (a % 2^width) % 2^width)
  | _ => none

/-- Cache the exact registered memory effect after each instruction.
This avoids accumulating nested function updates during larger component
checks; instruction semantics remain `Lax808846.Ram.Instr.effect`. -/
def runToHaltCached (width : ℕ) (p : Array Lax808846.Ram.Instr) :
    ℕ → Std.HashMap ℕ ℕ → Lax808846.Ram.State → Option (List ℕ)
  | 0, _, _ => none
  | fuel+1, memory, s => match p[s.pc]? with
    | none => none
    | some i => match i.effect width s with
      | none => match i with
        | .halt => some s.out
        | _ => none
      | some t =>
        let next := match writtenAddress width i s with
          | none => memory
          | some a => memory.insert a (t.mem a)
        runToHaltCached width p fuel next {t with mem := fun a => next.getD a 0}

def executeCompiledCached (layout : Layout) (width fuel : ℕ)
    (command : Com) (input : List ℕ) : Option (List ℕ) :=
  runToHaltCached width (compileProgram layout command).toArray fuel {}
    (Lax808846.Ram.initState input)

end Checks
