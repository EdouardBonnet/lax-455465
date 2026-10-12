import Lax455465Proofs.RamLargeCut
import Lax455465Proofs.RamArraySum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.LargeCut
open Checks
set_option maxRecDepth 8192

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def cutCommand : Com := sequence [.read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.capacities" (.mul (.lit 2) (.var "metric.n2")),
  readArray "metric.old" (.mul (.lit 2) (.var "metric.n2")),
  readArray "region.inMask" (.mul (.lit 2) (.var "metric.n")),
  readArray "region.outMask" (.mul (.lit 2) (.var "metric.n")),
  .assign "sum.count" (.var "metric.n"),RamArraySum.command "flow.weights",RamUnsignedScalar.save "round.total",
  RamLargeCut.command,.write (.var "best.found"),.write (.var "cut.reversed"),
  .write (.var "best.value.n"),.write (.var "best.value.d"),
  .assign "test.i" (.lit 0),.while (.lt (.var "test.i") (.var "metric.n"))
    (sequence [.write (.get "cut.flags" (.mul (.lit 2) (.var "test.i"))),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def layout : Layout := let names := commandNames cutCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled layout 128 10000000 cutCommand xs
def encodeNaturals (xs : List ℕ) : List ℕ := xs.flatMap fun x => [x,1]
def capacities : List ℕ := [0,0,3,0,0,5,7,11,0]
def symmetricMetric : List ℕ := [0,0,1,0,0,1,1,1,0]
def directedMetric : List ℕ := [0,0,1,0,0,1,2,2,0]
def balls : List ℕ := [1,1,0,1,1,0]

-- End-to-end large-ball branch, from original weights/capacities, the computed
-- metric, and two ball masks. Output is found, reversed, ratio, and shore bits.
-- Both balls have at least two thirds of total weight in these examples.
#guard execute ([3]++encodeNaturals ([1,1,1]++capacities++symmetricMetric++balls)) == some [1,0,4,1,1,1,0]
#guard execute ([3]++encodeNaturals ([1,1,1]++capacities++directedMetric++balls)) == some [1,1,9,1,0,0,1]
#guard execute ([3]++encodeNaturals ([2,1,1]++capacities++directedMetric++balls)) == some [1,1,6,1,0,0,1]
#guard execute ([3]++encodeNaturals ([1,1,1]++[0,0,0,0,0,0,0,0,0]++symmetricMetric++balls)) == some [1,0,0,1,1,1,0]

end Checks.LargeCut
