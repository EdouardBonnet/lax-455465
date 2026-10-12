import Lax455465Proofs.RamActiveRemove
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.ActiveRemove
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def writeArray (name : String) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.write (.get name (.var "test.i")),.assign "test.i" (.add (.var "test.i") (.lit 1))])]
def removeCommand : Com := sequence [.read "metric.n",.read "region.outward",
  readArray "region.active",readArray "region.outMask",readArray "region.inMask",RamActiveRemove.command,
  writeArray "region.active",writeArray "region.outMask",writeArray "region.inMask"]
def removeLayout : Layout := let names := commandNames removeCommand
  ⟨names.1.eraseDups,names.2.eraseDups,128⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled removeLayout 128 1000000 removeCommand xs

-- Different out/in balls, an already inactive vertex, and a surviving
-- transit vertex. The original ball masks must also survive the copy.
def active : List ℕ := [1,1,1,1,0,1,1,1]
def outward : List ℕ := [1,1,0,1,1,1,0,1]
def inward : List ℕ := [0,1,1,1,0,1,0,1]
#guard execute ([4,1]++active++outward++inward) == some ([0,1,1,1,0,1,1,1]++outward++inward)
#guard execute ([4,0]++active++outward++inward) == some ([1,1,0,1,0,1,1,1]++outward++inward)
#guard execute [0,1] == some []
#guard execute [1,1,1,1,1,1,0,1] == some [0,1,1,1,0,1]
#guard execute [1,0,1,1,1,1,0,1] == some [1,1,1,1,0,1]

end Checks.ActiveRemove
