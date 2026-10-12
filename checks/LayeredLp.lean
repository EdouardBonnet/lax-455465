import Lax455465Proofs.RamLayeredLp
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
open scoped NNRat
namespace Checks.LayeredLp
open Checks
set_option maxRecDepth 32768

def sequence (cs : List Com) : Com := cs.foldr Com.seq .skip

def command : Com := sequence [.read "lp.n",.read "short.layer",
  .assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")),
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "lp.n2")))
    (sequence [.read "test.word",.store "flow.capacities" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))]),
  RamLayeredData.dimensions,RamLayeredLp.command,
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.var "lp.position"))
    (sequence [.write (.get "lp.word" (.var "test.i")),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]

def layout : Layout := let names := commandNames command
  ⟨names.1.eraseDups,names.2.eraseDups,8192⟩
def execute (xs : List ℕ) := executeCompiledCached layout 128 20000000 command xs

def empty : Lax455465.RationalEncoding.RationalInstance 0 where
  capacity _ _ := 0
  loopless _ := rfl
  weight _ := 1

def singleton : Lax455465.RationalEncoding.RationalInstance 1 where
  capacity _ _ := 0
  loopless _ := rfl
  weight _ := 1

def pair : Lax455465.RationalEncoding.RationalInstance 2 where
  capacity u v := if u=v then 0 else 3/2
  loopless v := by simp
  weight _ := 1

-- Every emitted word is compared with the exact typed layered LP encoding.
-- This covers zero dimensions, half-unit demands, shared capacities,
-- waiting arcs, both balance signs, and more than one layer.
#guard execute [0,0] == some (Lax109476.RationalEncoding.encodeProgram (LayeredFlowLP.program empty 0))
#guard execute [1,1,0,1] == some (Lax109476.RationalEncoding.encodeProgram (LayeredFlowLP.program singleton 1))
#guard execute [2,1,0,1,3,2,3,2,0,1] == some (Lax109476.RationalEncoding.encodeProgram (LayeredFlowLP.program pair 1))
#guard execute [2,2,0,1,3,2,3,2,0,1] == some (Lax109476.RationalEncoding.encodeProgram (LayeredFlowLP.program pair 2))

end Checks.LayeredLp
