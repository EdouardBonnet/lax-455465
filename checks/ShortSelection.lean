import Lax455465Proofs.RamShortSelection
import Lax455465Proofs.RamShortTrial
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.ShortSelection
open Checks
set_option maxRecDepth 16384

def sequence (cs : List Com) : Com := cs.foldr Com.seq .skip

-- The harness supplies exact LP values to isolate the verified threshold
-- and selection components; it does not replace solver calls in the proof.
def trial : Com := sequence [
  .assign "short.layer" (.add (.var "find.i") (.lit 1)),
  RamUnsignedBuffer.read "test.values" "find.i",RamShortTest.command,RamShortTrial.fallback]
def command : Com := sequence [.read "lp.n",.read "short.maximum.n",.read "short.maximum.d",
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.sub (.var "lp.n") (.lit 1))))
    (sequence [.read "test.word",.store "test.values" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))]),
  RamShortSelection.command trial,.write (.var "short.layer")]
def layout : Layout := let names := commandNames command
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) := executeCompiledCached layout 128 1000000 command xs

-- Success at the first, second, and final budgets, then the forced fallback.
#guard execute [4,10,1,1,1,1,2,1,2] == some [1]
#guard execute [4,10,1,1,10,1,2,1,2] == some [2]
#guard execute [4,10,1,1,10,1,10,1,2] == some [3]
#guard execute [4,10,1,1,100,1,100,1,100] == some [3]
-- Exact equality succeeds; zero capacities also succeed at the first budget.
#guard execute [3,1,3,1,36,0,1] == some [1]
#guard execute [3,0,1,0,1,0,1] == some [1]
#guard execute [2,10,1,0,1] == some [1]

end Checks.ShortSelection
