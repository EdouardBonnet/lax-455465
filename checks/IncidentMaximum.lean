import Lax455465Proofs.RamIncidentMaximum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.IncidentMaximum
open Checks
set_option maxRecDepth 16384

def sequence (cs : List Com) : Com := cs.foldr Com.seq .skip

def command : Com := sequence [.read "lp.n",
  .assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")),.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "lp.n2")))
    (sequence [.read "test.word",.store "flow.capacities" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))]),
  RamIncidentMaximum.command,.write (.var "short.maximum.n"),.write (.var "short.maximum.d")]
def layout : Layout := let names := commandNames command
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) := executeCompiledCached layout 128 3000000 command xs

#guard execute [0] == some [0,1]
#guard execute [1,0,1] == some [0,1]
#guard execute [2,0,1,0,1,0,1,0,1] == some [0,1]
#guard execute [2,0,1,3,2,3,2,0,1] == some [3,2]
-- Asymmetric input checks that the actual row maximum is selected.
#guard execute [2,0,1,3,2,7,3,0,1] == some [7,3]
-- The final row wins; exact normalization must retain denominator twelve.
#guard execute [3,0,1,1,2,2,3,1,2,0,1,3,4,2,3,3,4,0,1] == some [17,12]

end Checks.IncidentMaximum
