import Lax455465Proofs.RamRadiusCandidates
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RadiusCandidates
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip

def readVector (array : String) : Com := sequence [
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.read "test.word",.store array (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]

def radiusCommand : Com := sequence [
  .read "metric.n",.read "round.steps",.read "round.delta.n",.read "round.delta.d",
  .read "round.gridStep.n",.read "round.gridStep.d",readVector "region.out",readVector "region.in",
  RamRadiusCandidates.command,.write (.var "radius.count"),.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "radius.count")))
    (sequence [.assign "test.word" (.get "region.radii" (.var "test.i")),.write (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]

def radiusLayout : Layout := let names := commandNames radiusCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled radiusLayout 128 1000000 radiusCommand xs

-- Empty graph: the grid still contains both endpoints and the middle point.
#guard execute [0,2,1,2,1,4] == some [3,0,1,1,4,1,2]
-- Unsorted events, clipping above delta, and repeated grid/event radii.
#guard execute [2,2,1,2,1,4,0,1,3,4,1,3,2,1] == some [7,0,1,1,4,1,2,0,1,1,2,1,3,1,2]
-- The coefficient program also covers a zero grid budget exactly.
#guard execute [1,0,1,2,0,1,1,4,1,1] == some [3,0,1,1,4,1,2]
#guard execute [1,1,0,1,0,1,7,3,2,1] == some [4,0,1,0,1,0,1,0,1]
#guard execute [1,3,2,5,2,15,1,7,1,2] == some [6,0,1,2,15,4,15,2,5,1,7,2,5]
#guard execute [0,1,1,2^40+1,1,2^40+1] == some [2,0,1,1,2^40+1]

end Checks.RadiusCandidates
