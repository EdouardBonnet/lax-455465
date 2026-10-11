import Lax455465Proofs.RamFloydWarshall
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.FloydWarshall
open Checks

def readWords : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.var "metric.words"))
    (.seq (.read "test.word")
      (.seq (.store "metric.old" (.var "test.i") (.var "test.word"))
        (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def emitWords : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.var "metric.words"))
    (.seq (.write (.get "metric.old" (.var "test.i")))
      (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "metric.n")
  (.seq (.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")))
    (.seq (.assign "metric.words" (.mul (.lit 2) (.var "metric.n2")))
      (.seq readWords (.seq RamFloydWarshall.command emitWords))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 1000000 queryCommand xs

-- No vertices and a single zero diagonal: both terminate correctly.
#guard execute [0] == some []
#guard execute [1,0,1] == some [0,1]

-- Asymmetric integral lengths; improvements require different pivots.
#guard execute [3,0,1,1,1,10,1,10,1,0,1,2,1,3,1,10,1,0,1] ==
  some [0,1,1,1,3,1,5,1,0,1,2,1,3,1,4,1,0,1]

-- Exact fractions, including 1/3 + 1/6 and 1/2 + 1/3.
#guard execute [3,0,1,1,3,9,1,8,1,0,1,1,6,1,2,7,1,0,1] ==
  some [0,1,1,3,1,2,2,3,0,1,1,6,1,2,5,6,0,1]

end Checks.FloydWarshall
