import Lax455465Proofs.RamSetDistances
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.SetDistances
open Checks
set_option maxRecDepth 8192

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def distanceCommand (toSet : Bool) : Com := sequence [.read "metric.n",.assign "cut.count" (.var "metric.n"),
  readArray "metric.old" (.mul (.lit 2) (.mul (.var "metric.n") (.var "metric.n"))),
  readArray "potential.set" (.mul (.lit 2) (.var "metric.n")),RamSetDistances.command toSet,
  .assign "test.i" (.lit 0),.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.write (.get "potential.values" (.var "test.i")),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def layout (toSet : Bool) : Layout := let names := commandNames (distanceCommand toSet)
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (toSet : Bool) (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled (layout toSet) 128 5000000 (distanceCommand toSet) xs

-- Input: n, n² canonical matrix entries, n canonical zero/one set flags.
-- Output: all n canonical distances, preserving directed orientation.
def matrix3 : List ℕ := [3,0,1,2,1,5,1,7,1,0,1,3,1,4,1,6,1,0,1]
#guard execute false (matrix3++[1,1,0,1,1,1]) == some [0,1,2,1,0,1]
#guard execute true (matrix3++[1,1,0,1,1,1]) == some [0,1,3,1,0,1]
#guard execute false (matrix3++[1,1,0,1,0,1]) == some [0,1,2,1,5,1]
#guard execute true (matrix3++[1,1,0,1,0,1]) == some [0,1,7,1,4,1]
#guard execute false (matrix3++[1,1,1,1,1,1]) == some [0,1,0,1,0,1]
#guard execute true (matrix3++[0,1,0,1,1,1]) == some [5,1,3,1,0,1]
#guard execute false [3,0,1,2,7,5,7,1,1,0,1,3,7,4,7,6,7,0,1,1,1,0,1,1,1] == some [0,1,2,7,0,1]
#guard execute true [1,0,1,1,1] == some [0,1]

end Checks.SetDistances
