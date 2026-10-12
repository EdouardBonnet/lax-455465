import Lax455465Proofs.RamPotentialSweep
import Lax455465Proofs.RamArraySum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.PotentialSweep
open Checks
set_option maxRecDepth 8192

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def sweepCommand : Com := sequence [.read "metric.n",.read "cut.reversed",
  .assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),.assign "cut.count" (.var "metric.n"),
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.capacities" (.mul (.lit 2) (.var "metric.n2")),
  readArray "cut.potential" (.mul (.lit 2) (.var "metric.n")),
  .assign "sum.count" (.var "metric.n"),RamArraySum.command "flow.weights",RamUnsignedScalar.save "round.total",
  RamPotentialSweep.command,.write (.var "best.found"),
  .ite (.eq (.var "best.found") (.lit 1))
    (sequence [.write (.var "best.index"),.write (.var "best.value.n"),.write (.var "best.value.d"),
      .assign "test.i" (.lit 0),.while (.lt (.var "test.i") (.var "metric.n"))
        (sequence [.write (.get "cut.flags" (.mul (.lit 2) (.var "test.i"))),
          .assign "test.i" (.add (.var "test.i") (.lit 1))])]) .skip]
def sweepLayout : Layout := let names := commandNames sweepCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled sweepLayout 128 5000000 sweepCommand xs

-- Each input is n, reversed, n weights, n² row-major capacities, n potentials;
-- every rational is its canonical numerator/denominator pair. Output is
-- found, followed (when found) by index, exact ratio, and n shore bits.
def graph2 : List ℕ := [1,1,2,1,0,1,2,3,5,7,0,1]
#guard execute ([2,0]++graph2++[0,1,1,1]) == some [1,0,1,3,1,0]
#guard execute ([2,1]++graph2++[0,1,1,1]) == some [1,1,5,14,0,1]
#guard execute ([2,0]++graph2++[1,2,1,2]) == some [0]

def encodeNaturals (xs : List ℕ) : List ℕ := xs.flatMap fun x => [x,1]
def chain (a b : ℕ) : List ℕ := encodeNaturals [1,1,1,0,a,0,0,0,b,0,0,0,0,1,2]
-- Retain an early optimum, accept a later improvement, and retain the first tie.
-- The last threshold is the invalid full shore in all three cases, so these
-- checks also require restoring the winning mask after finishing the scan.
#guard execute ([3,0]++chain 1 8) == some [1,0,1,2,1,0,0]
#guard execute ([3,0]++chain 8 1) == some [1,1,1,2,1,1,0]
#guard execute ([3,0]++chain 1 1) == some [1,0,1,2,1,0,0]
#guard execute ([3,1]++chain 1 8) == some [1,1,0,1,0,1,1]
-- A zero-weight transit vertex makes the first proper shore inadmissible.
#guard execute ([3,0]++encodeNaturals [0,1,1,0,0,0,0,0,3,0,0,0,0,1,2]) == some [1,1,3,1,1,1,0]
#guard execute [0,0] == some [0]
#guard execute [1,0,1,1,0,1,0,1] == some [0]

end Checks.PotentialSweep
