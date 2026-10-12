import Lax455465Proofs.RamMetricRounding
import Lax455465Proofs.RamMetricCost
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.MetricRounding
open Checks
set_option maxRecDepth 16384

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def testCommand : Com := sequence [.read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.capacities" (.mul (.lit 2) (.var "metric.n2")),
  readArray "metric.old" (.mul (.lit 2) (.var "metric.n2")),RamMetricCost.command,RamMetricRounding.command,
  .write (.var "region.phase"),.write (.var "best.found"),.write (.var "best.value.n"),.write (.var "best.value.d"),
  .assign "test.i" (.lit 0),.while (.lt (.var "test.i") (.var "metric.n"))
    (sequence [.write (.get "cut.flags" (.mul (.lit 2) (.var "test.i"))),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def layout : Layout := let names := commandNames testCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled layout 128 50000000 testCommand xs
def encodeNaturals (xs : List ℕ) : List ℕ := xs.flatMap fun x => [x,1]

-- Only original weights, capacities, and a metric are supplied. Cost,
-- all constants, regions, branch selection, and the final cut are computed.
-- Two separated vertices exhaust the small-region history (phase 2).
#guard execute ([2]++encodeNaturals [1,1, 0,1,1,0, 0,1,1,0]) == some [2,1,1,1,1,0]
-- A zero-distance cluster triggers the large-ball branch (phase 1).
#guard execute ([3]++encodeNaturals [1,1,1, 0,0,3,0,0,5,7,11,0, 0,0,1,0,0,1,1,1,0]) == some [1,1,4,1,1,1,0]
-- Zero metric cost takes the pair-search branch without running region growth.
#guard execute ([2]++encodeNaturals [1,1, 0,0,0,0, 0,1,1,0]) == some [0,1,0,1,1,0]

end Checks.MetricRounding
