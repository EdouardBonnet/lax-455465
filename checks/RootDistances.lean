import Lax455465Proofs.RamRootDistances
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.RootDistances
open Checks

def readMatrix : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.mul (.var "metric.n") (.var "metric.n"))))
    (.seq (.read "test.word") (.seq (.store "metric.old" (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def writeVector (array : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (.seq (.write (.get array (.var "test.i"))) (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "metric.n") (.seq (.read "region.root")
  (.seq readMatrix (.seq (RamRootDistances.command true) (.seq (RamRootDistances.command false)
    (.seq (writeVector "region.out") (writeVector "region.in"))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 500000 queryCommand xs

-- One vertex, then both orientations of an asymmetric two-vertex metric.
#guard execute [1,0,0,1] == some [0,1,0,1]
#guard execute [2,0,0,1,2,3,7,4,0,1] == some [0,1,2,3,0,1,7,4]
#guard execute [2,1,0,1,2,3,7,4,0,1] == some [7,4,0,1,2,3,0,1]

-- The middle root reads its row and column without swapping endpoints.
#guard execute [3,1,0,1,1,2,2,3,3,4,0,1,5,6,6,7,7,8,0,1] ==
  some [3,4,0,1,5,6,1,2,0,1,7,8]

end Checks.RootDistances
