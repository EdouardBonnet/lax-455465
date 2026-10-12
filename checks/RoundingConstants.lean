import Lax455465Proofs.RamRoundingConstants
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RoundingConstants
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def writePair (name : String) : Com := sequence [.write (.var (name++".n")),.write (.var (name++".d"))]

def constantsCommand : Com := sequence [
  .read "round.support",.read "round.steps",.read "round.cost.n",.read "round.cost.d",
  .read "round.total.n",.read "round.total.d",RamRoundingConstants.command,
  writePair "round.seed",writePair "round.delta",writePair "round.slope",writePair "round.gridStep"]

def constantsLayout : Layout := let names := commandNames constantsCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled constantsLayout 128 1000000 constantsCommand xs

#guard execute [2,6,5,7,3,2] == some [5,14,1,9,54,1,1,54]
#guard execute [3,6,13,5,7,3] == some [13,15,9,196,392,3,3,392]
#guard execute [4,8,0,1,2,1] == some [0,1,1,16,128,1,1,128]
-- Zero reciprocal branches are total, even though the main region-growth
-- theorem uses a positive mass and support of at least two.
#guard execute [0,4,1,1,0,1] == some [0,1,0,1,0,1,0,1]
#guard execute [17,12,1,2^40,1,1] == some [1,17*2^40,1,4,48,1,1,48]

end Checks.RoundingConstants
