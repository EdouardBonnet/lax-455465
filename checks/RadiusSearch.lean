import Lax455465Proofs.RamSelectedRegion
import Checks.Common

set_option maxRecDepth 4096
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RadiusSearch
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip

def readVector (array count : String) : Com := sequence [
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (sequence [.read "test.word",.store array (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def writePair (name : String) : Com := sequence [.write (.var (name++".n")),.write (.var (name++".d"))]

def searchCommand : Com := sequence [
  .read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  .read "round.seed.n",.read "round.seed.d",.read "round.slope.n",.read "round.slope.d",
  readVector "region.weights" "metric.n",readVector "region.out" "metric.n",readVector "region.in" "metric.n",
  readVector "region.capacities" "metric.n2",readVector "metric.old" "metric.n2",
  .read "find.count",readVector "region.radii" "find.count",RamSelectedRegion.command,
  .write (.var "find.found"),.write (.var "find.result"),
  .ite (.eq (.var "find.found") (.lit 1))
    (sequence [writePair "region.radius",
      .write (.var "region.outward"),writePair "region.boundary",writePair "region.volume"]) .skip]

def searchLayout : Layout := let names := commandNames searchCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled searchLayout 128 10000000 searchCommand xs

-- Zero is rejected before the first successful positive radius is recorded.
#guard execute [0,1,5,0,1,3,0,1,1,2,1,1] == some [1,1,1,2,1,0,1,1,5]
#guard execute [0,1,5,1,1,2,0,1,0,1] == some [0,0]
#guard execute [0,1,5,1,1,0] == some [0,0]

def edges : List ℕ := [0,1,2,3,5,7,0,1,0,1,3,2,2,1,0,1]
def inwardDistances : List ℕ := [1,1,2,1,0,1,1,2,0,1,1,1]
def outwardDistances : List ℕ := [1,1,2,1,0,1,1,1,0,1,1,2]
-- One failed positive query followed by a full-ball success; the selected
-- payload is restored from the recorded candidate before it is emitted.
#guard execute ([2,1,5,9,13] ++ outwardDistances ++ edges ++ [3,0,1,1,1,2,1]) == some [1,2,2,1,1,0,1,67,35]
#guard execute ([2,1,5,1,1] ++ inwardDistances ++ edges ++ [3,0,1,1,1,1,2]) == some [1,1,1,1,0,5,7,32,35]
#guard execute ([2,1,5,1,2] ++ inwardDistances ++ edges ++ [2,0,1,1,1]) == some [0,0]

end Checks.RadiusSearch
