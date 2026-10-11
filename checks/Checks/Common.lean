import Lax808846Proofs.Compile
import Lax808846.Ram

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

end Checks
