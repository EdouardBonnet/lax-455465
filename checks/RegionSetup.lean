import Lax455465Proofs.RamRegionSetup
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.RegionSetup
open Checks
set_option maxRecDepth 4096

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readPair (name : String) : Com := sequence [.read (name++".n"),.read (name++".d")]
def writePair (name : String) : Com := sequence [.write (.var (name++".n")),.write (.var (name++".d"))]
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]

def setupCommand : Com := sequence [.read "metric.n",.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")),
  .read "region.root",.read "round.steps",readPair "round.seed",readPair "round.slope",readPair "round.delta",readPair "round.gridStep",
  readArray "region.weights" (.mul (.lit 2) (.var "metric.n")),
  readArray "region.capacities" (.mul (.lit 2) (.var "metric.n2")),
  readArray "metric.old" (.mul (.lit 2) (.var "metric.n2")),RamRegionSetup.command,
  .write (.var "find.found"),.write (.var "find.result"),
  .ite (.eq (.var "find.found") (.lit 1))
    (sequence [writePair "region.radius",.write (.var "region.outward"),writePair "region.outMass",writePair "region.inMass",
      writePair "region.boundary",writePair "region.volume"]) .skip]

def setupLayout : Layout := let names := commandNames setupCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled setupLayout 128 5000000 setupCommand xs

def graph : List ℕ := [1,1,2,1,0,1,2,3,5,7,0,1,0,1,1,2,1,1,0,1]
#guard execute ([2,0,2,1,5,1,1,1,1,1,2]++graph) == some [1,2,1,1,0,3,1,1,1,5,7,32,35]
#guard execute ([2,0,2,1,5,2,1,1,1,1,2]++graph) == some [1,1,1,2,1,1,1,1,1,2,3,8,15]
#guard execute ([2,0,2,1,5,1,2,1,1,1,2]++graph) == some [0,0]
#guard execute ([2,1,2,1,5,2,1,1,1,1,2]++graph) == some [1,1,1,2,1,2,1,2,1,5,7,39,70]
#guard execute ([2,1,2,1,5,1,1,1,1,1,2]++graph) == some [1,2,1,1,1,2,1,3,1,5,7,32,35]
#guard execute [1,0,1,1,5,0,1,1,1,1,1,1,1,0,1,0,1] == some [1,1,1,1,1,1,1,1,1,0,1,1,5]
#guard execute [1,0,0,1,5,0,1,1,1,0,1,1,1,0,1,0,1] == some [0,0]

end Checks.RegionSetup
