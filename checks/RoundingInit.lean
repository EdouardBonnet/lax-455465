import Lax455465Proofs.RamRoundingInit
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RoundingInit
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def writePair (name : String) : Com := sequence [.write (.var (name++".n")),.write (.var (name++".d"))]

def initCommand : Com := sequence [
  .read "metric.n",.read "round.cost.n",.read "round.cost.d",.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.read "test.word",.store "flow.weights" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))]),RamRoundingInit.command,
  .write (.var "round.support"),.write (.var "round.steps"),writePair "round.total",
  writePair "round.seed",writePair "round.delta",writePair "round.slope",writePair "round.gridStep"]

def initLayout : Layout := let names := commandNames initCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled initLayout 128 3000000 initCommand xs

-- The support and all constants are computed from the supplied weight
-- buffer; no total mass or support count is supplied as an extra input.
#guard execute [3,5,7,1,2,0,1,1,1] == some [2,6,3,2,5,14,1,9,54,1,1,54]
#guard execute [4,13,5,1,3,1,1,1,1,0,1] == some [3,6,7,3,13,15,9,196,392,3,3,392]
#guard execute [4,0,1,1,1,1,1,1,1,1,1] == some [4,8,4,1,0,1,1,64,512,1,1,512]
#guard execute [1,1,1,2,3] == some [1,4,2,3,1,1,9,16,64,9,9,64]
#guard execute [2,1,2^40,1,2,1,2] == some [2,6,1,1,1,2^41,1,4,24,1,1,24]

end Checks.RoundingInit
