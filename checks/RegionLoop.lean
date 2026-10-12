import Lax455465Proofs.RamRegionLoop
import Lax455465Proofs.RamMetricCost
import Lax455465Proofs.RamRoundingInit
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RegionLoop
open Checks
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def writePair (name : String) : Com := sequence [.write (.var (name++".n")),.write (.var (name++".d"))]
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def writeArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.write (.get name (.var "test.i")),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]

def loopCommand : Com := sequence [.read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.capacities" (.mul (.lit 2) (.var "metric.n2")),
  readArray "metric.old" (.mul (.lit 2) (.var "metric.n2")),
  RamMetricCost.command,RamRoundingInit.command,RamRegionLoop.command,
  .write (.var "region.phase"),.write (.var "round.support"),.write (.var "loop.i"),
  .write (.var "history.pos"),writeArray "region.history" (.var "history.pos"),
  writeArray "region.active" (.mul (.lit 2) (.var "metric.n")),
  .ite (.eq (.var "region.phase") (.lit 1))
    (sequence [.write (.var "region.root"),writePair "region.radius",.write (.var "region.outward")]) .skip]

def loopLayout : Layout := let names := commandNames loopCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled loopLayout 128 20000000 loopCommand xs

-- Only the graph arrays and a metric are supplied. The cost, support,
-- budgets, root, radii, residuals and every branch bit are computed by RAM.
#guard execute [2,1,1,2,1,0,1,2,3,5,7,0,1,0,1,1,2,1,1,0,1] ==
  some [1,2,3,4,0,1,216,1,0,1,1,1,1,1,216,1]
#guard execute [2,1,1,1,1,0,1,1,1,1,1,0,1,0,1,1,1,1,1,0,1] ==
  some [2,2,3,8,0,1,96,1,1,1,96,1,0,1,0,1]
#guard execute [1,1,1,0,1,0,1] == some [1,1,2,0,1,1,0,1,16,1]
#guard execute [0] == some [2,0,1,0]

end Checks.RegionLoop
