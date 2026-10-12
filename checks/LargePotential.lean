import Lax455465Proofs.RamLargePotential
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.LargePotential
open Checks
set_option maxRecDepth 8192

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def potentialCommand : Com := sequence [.read "metric.n",
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "metric.old" (.mul (.lit 2) (.mul (.var "metric.n") (.var "metric.n"))),
  readArray "region.inMask" (.mul (.lit 2) (.var "metric.n")),
  readArray "region.outMask" (.mul (.lit 2) (.var "metric.n")),RamLargePotential.command,
  .write (.var "cut.reversed"),.write (.var "potential.fromAvg.n"),.write (.var "potential.fromAvg.d"),
  .write (.var "potential.toAvg.n"),.write (.var "potential.toAvg.d"),
  .assign "test.i" (.lit 0),.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.write (.get "cut.potential" (.var "test.i")),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def layout : Layout := let names := commandNames potentialCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled layout 128 10000000 potentialCommand xs
def encodeNaturals (xs : List ℕ) : List ℕ := xs.flatMap fun x => [x,1]

-- Input: n, original weights, row-major distances, in-mask, out-mask.
-- Output: reversed, from-average, to-average, and the chosen unsigned vector.
#guard execute ([2]++encodeNaturals [1,1,0,1,4,0,1,0,1,0]) == some [1,1,1,4,1,0,1,4,1]
#guard execute ([2]++encodeNaturals [1,1,0,1,4,0,0,1,0,1]) == some [0,4,1,1,1,4,1,0,1]
#guard execute ([3]++encodeNaturals [1,1,1,0,2,5,7,0,3,4,6,0,1,0,1,1,0,1]) == some [1,2,1,3,1,0,1,3,1,0,1]
#guard execute ([3]++encodeNaturals [0,0,1,0,2,5,7,0,3,4,6,0,0,0,1,1,0,0]) == some [0,5,1,0,1,0,1,2,1,5,1]
-- Equal averages retain the from-set potential, including the all-zero case.
#guard execute ([2]++encodeNaturals [1,1,0,3,3,0,1,0,1,0]) == some [0,3,1,3,1,0,1,3,1]
#guard execute ([2]++encodeNaturals [1,1,0,1,4,0,1,1,1,1]) == some [0,0,1,0,1,0,1,0,1]
#guard execute [2,1,2,2,3,0,1,1,5,4,7,0,1,1,1,0,1,1,1,0,1] == some [1,2,15,8,21,0,1,4,7]

end Checks.LargePotential
