import Lax455465Proofs.RamZeroCut
import Lax455465Proofs.RamArraySum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.ZeroCut
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
  .assign "sum.count" (.var "metric.n"),RamArraySum.command "flow.weights",RamUnsignedScalar.save "round.total",
  RamZeroCut.command,.write (.var "find.result"),.write (.var "best.found"),
  .write (.var "best.value.n"),.write (.var "best.value.d"),
  .assign "test.i" (.lit 0),.while (.lt (.var "test.i") (.var "metric.n"))
    (sequence [.write (.get "cut.flags" (.mul (.lit 2) (.var "test.i"))),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def layout : Layout := let names := commandNames cutCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled layout 128 10000000 cutCommand xs
def encodeNaturals (xs : List ℕ) : List ℕ := xs.flatMap fun x => [x,1]

-- Input: n, original weights, row-major capacities, row-major distances.
-- Output: positive-pair index, found, exact cut ratio, and shore bits.
#guard execute ([2]++encodeNaturals [1,1,0,0,3,0,0,1,0,0]) == some [1,1,0,1,1,0]
#guard execute ([2]++encodeNaturals [1,1,0,3,0,0,0,0,1,0]) == some [2,1,0,1,0,1]
-- Vertex 0 has positive weight but only zero outgoing distances; the actual
-- search must continue to vertex 1 to obtain a separated potential.
#guard execute ([3]++encodeNaturals [1,1,1,0,3,5,0,0,0,7,11,0,0,0,0,1,0,1,0,0,0]) == some [3,1,0,1,0,1,0]
-- A positive distance incident with a zero-weight transit vertex is skipped.
#guard execute ([3]++encodeNaturals [0,1,1,0,0,0,0,0,0,0,0,0,0,1,1,1,0,1,1,1,0]) == some [5,1,0,1,0,1,0]
#guard execute [2,1,2,1,3,0,1,0,1,5,11,0,1,0,1,2,7,0,1,0,1] == some [1,1,0,1,1,0]

end Checks.ZeroCut
