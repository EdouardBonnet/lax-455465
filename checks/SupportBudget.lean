import Lax455465Proofs.RamSupport
import Lax455465Proofs.RamGridBudget
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.SupportBudget
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip

def supportCommand : Com := sequence [
  .read "metric.n",.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.read "test.word",.store "flow.weights" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))]),
  RamSupport.command,
  .ite (.lt (.lit 0) (.var "round.support")) RamGridBudget.command (.assign "round.steps" (.lit 0)),
  .write (.var "round.support"),.write (.var "round.steps")]

def supportLayout : Layout := let names := commandNames supportCommand
  ⟨names.1.eraseDups,names.2.eraseDups,1024⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled supportLayout 128 5000000 supportCommand xs

#guard execute [0] == some [0,0]
#guard execute [3,0,1,0,1,0,1] == some [0,0]
#guard execute [3,0,1,1,3,0,1] == some [1,4]
#guard execute [5,0,1,2,3,0,1,4,5,0,1] == some [2,6]
#guard execute [4,1,3,1,5,1,7,0,1] == some [3,6]
#guard execute [4,1,1,1,3,1,5,1,7] == some [4,8]
#guard execute ([17] ++ (List.replicate 17 [1,1]).flatten) == some [17,12]
#guard execute [2,2^40+1,2^40,0,1] == some [1,4]

end Checks.SupportBudget
