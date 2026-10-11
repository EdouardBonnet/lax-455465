import Lax455465Proofs.RamRoot
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.Root
open Checks

def readWeights : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (.seq (.read "test.word") (.seq (.store "region.weights" (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def queryCommand : Com := .seq (.read "metric.n") (.seq readWeights (.seq RamRoot.command
  (.seq (.write (.var "find.found")) (.write (.var "find.result")))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 1000000 queryCommand xs

#guard execute [0] == some [0,0]
#guard execute [1,0,1] == some [0,0]
#guard execute [3,0,1,0,1,0,1] == some [0,0]
#guard execute [3,7,3,1,2,9,7] == some [1,0]
#guard execute [3,0,1,1,2,9,7] == some [1,1]
#guard execute [3,0,1,0,1,9,7] == some [1,2]
#guard execute [2,0,1,2^24+1,2^24] == some [1,1]

end Checks.Root
