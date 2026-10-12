import Lax455465Proofs.RamHistoryCut
import Lax455465Proofs.RamArraySum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.HistoryCut
open Checks
set_option maxRecDepth 8192

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def writeVector (name : String) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.var "metric.n"))
    (sequence [.write (.get name (.mul (.lit 2) (.var "test.i"))),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def input : Com := sequence [.read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  .read "history.pos",readArray "region.history" (.var "history.pos"),
  readArray "metric.old" (.mul (.lit 2) (.var "metric.n2"))]
def potentialCommand : Com := sequence [input,RamHistoryPotential.command,
  .write (.var "cut.count"),.write (.var "cut.reversed"),writeVector "cut.potential"]
def cutCommand : Com := sequence [input,
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.capacities" (.mul (.lit 2) (.var "metric.n2")),
  .assign "sum.count" (.var "metric.n"),RamArraySum.command "flow.weights",RamUnsignedScalar.save "round.total",
  RamHistoryCut.command,.write (.var "best.found"),.write (.var "best.value.n"),.write (.var "best.value.d"),
  writeVector "cut.flags"]
def layout (cmd : Com) : Layout := let names := commandNames cmd
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (cmd : Com) (xs : List ℕ) : Option (List ℕ) := executeCompiled (layout cmd) 128 15000000 cmd xs
def encodeNaturals (xs : List ℕ) : List ℕ := xs.flatMap fun x => [x,1]
def metric : List ℕ := [0,1,1,1, 1,0,1,1, 1,1,0,1, 1,1,1,0]
def history : List ℕ := [0,1,1,1, 1,1,1,0, 2,1,1,1]
def capacities : List ℕ := [0,1,8,0, 0,0,0,0, 0,1,0,0, 0,0,0,0]

-- Unit radius means strict singleton balls. Inward blocks precede the
-- unremoved vertex; outward blocks follow it in reverse creation order.
#guard execute potentialCommand ([4,12]++history++encodeNaturals metric) == some [4,1,6,1,4,3]
#guard execute potentialCommand ([4,12]++[0,1,1,0, 1,1,1,1, 2,1,1,0]++encodeNaturals metric) == some [4,1,0,5,2,3]
-- Overlapping balls use the earliest containing region, regardless of later records.
#guard execute potentialCommand ([4,12]++[0,2,1,1, 1,1,1,0, 2,1,1,1]++encodeNaturals metric) == some [4,1,6,6,6,6]
-- Empty history, zero dimensions, and an empty strict zero-radius ball.
#guard execute potentialCommand ([4,0]++encodeNaturals metric) == some [4,1,0,0,0,0]
#guard execute potentialCommand [0,0] == some [0,1]
#guard execute potentialCommand ([4,4]++[0,0,1,1]++encodeNaturals metric) == some [4,1,1,1,1,1]
-- Exact fractional comparisons: radius one half retains only the root.
#guard execute potentialCommand ([4,4]++[2,1,2,0]++encodeNaturals metric) == some [4,1,1,1,0,1]
-- Full branch: the best upper threshold is {0,2}, with directed ratio 1/2.
#guard execute cutCommand ([4,12]++history++encodeNaturals (metric++[1,1,1,1]++capacities)) == some [1,1,2,1,0,1,0]
-- Changing orientations selects {1}, whose outgoing capacity is zero.
#guard execute cutCommand ([4,12]++[0,1,1,0, 1,1,1,1, 2,1,1,0]++
  encodeNaturals (metric++[1,1,1,1]++capacities)) == some [1,0,1,0,1,0,0]

end Checks.HistoryCut
