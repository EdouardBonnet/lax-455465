import Lax455465Proofs.RamLargeThreshold
import Lax455465Proofs.RamRegionLarge
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RegionLarge
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readPair (name : String) : Com := sequence [.read (name++".n"),.read (name++".d")]
def largeCommand : Com := sequence [readPair "round.total",readPair "region.outMass",readPair "region.inMass",
  RamLargeThreshold.command,RamRegionLarge.command,.write (.var "round.largeThreshold.n"),
  .write (.var "round.largeThreshold.d"),.write (.var "region.large")]
def largeLayout : Layout := let names := commandNames largeCommand
  ⟨names.1.eraseDups,names.2.eraseDups,64⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled largeLayout 128 1000000 largeCommand xs

#guard execute [3,1,2,1,2,1] == some [2,1,1]
#guard execute [3,1,3,1,2,1] == some [2,1,1]
#guard execute [3,1,2,1,3,1] == some [2,1,1]
#guard execute [3,1,1,1,2,1] == some [2,1,0]
#guard execute [3,1,2,1,1,1] == some [2,1,0]
#guard execute [7,3,14,9,14,9] == some [14,9,1]
#guard execute [7,3,14,9,3,2] == some [14,9,0]
#guard execute [0,1,0,1,0,1] == some [0,1,1]

end Checks.RegionLarge
