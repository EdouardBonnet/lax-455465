import Lax455465Proofs.RamCutScore
import Lax455465Proofs.RamArraySum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.CutScore
open Checks
set_option maxRecDepth 4096

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def writePair (name : String) : Com := sequence [.write (.var (name++".n")),.write (.var (name++".d"))]
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def scoreCommand : Com := sequence [.read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  readArray "flow.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.capacities" (.mul (.lit 2) (.var "metric.n2")),
  readArray "cut.flags" (.mul (.lit 2) (.var "metric.n")),
  .assign "sum.count" (.var "metric.n"),RamArraySum.command "flow.weights",RamUnsignedScalar.save "round.total",
  RamCutScore.command,writePair "cut.capacity",writePair "cut.mass",writePair "cut.other",writePair "cut.demand",
  writePair "cut.ratio",.write (.var "cut.valid")]
def scoreLayout : Layout := let names := commandNames scoreCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled scoreLayout 128 3000000 scoreCommand xs

def graph2 : List ℕ := [2,1,1,2,1,0,1,2,3,5,7,0,1]
#guard execute (graph2++[1,1,0,1]) == some [2,3,1,1,2,1,2,1,1,3,1]
#guard execute (graph2++[0,1,1,1]) == some [5,7,2,1,1,1,2,1,5,14,1]
#guard execute (graph2++[0,1,0,1]) == some [0,1,0,1,3,1,0,1,0,1,0]
#guard execute (graph2++[1,1,1,1]) == some [0,1,3,1,0,1,0,1,0,1,0]
#guard execute [2,1,2,1,3,0,1,2,3,5,7,0,1,1,1,0,1] == some [2,3,1,2,1,3,1,6,4,1,1]
def graph3 : List ℕ := [3,0,1,1,1,2,1,0,1,7,11,1,3,5,7,0,1,1,5,2,7,3,5,0,1]
#guard execute (graph3++[1,1,1,1,0,1]) == some [8,15,1,1,2,1,2,1,4,15,1]
#guard execute (graph3++[1,1,0,1,0,1]) == some [32,33,0,1,3,1,0,1,0,1,0]
#guard execute [0] == some [0,1,0,1,0,1,0,1,0,1,0]
#guard execute [1,2,3,0,1,1,1] == some [0,1,2,3,0,1,0,1,0,1,0]

end Checks.CutScore
