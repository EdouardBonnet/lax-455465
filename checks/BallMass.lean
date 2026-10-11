import Lax455465Proofs.RamBallMass
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.BallMass
open Checks

def readVector (array : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def writeMask : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (.seq (.write (.get "region.outMask" (.var "test.i"))) (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "metric.n") (.seq (.read "region.radius.n") (.seq (.read "region.radius.d")
  (.seq (readVector "region.weights") (.seq (readVector "region.out")
    (.seq (RamBallMass.command true) (.seq writeMask
      (.seq (.write (.var "region.outMass.n")) (.write (.var "region.outMass.d")))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 2000000 queryCommand xs

-- Empty graph and empty strict ball at radius zero.
#guard execute [0,1,1] == some [0,1]
#guard execute [2,0,1,1,1,7,3,0,1,1,2] == some [0,1,0,1,0,1]

-- A threshold-equal vertex is excluded; the other two masses add exactly.
#guard execute [3,1,1,1,2,7,3,2,1,0,1,1,1,3,4] == some [1,1,0,1,1,1,5,2]

-- Zero-weight vertices retain their geometric membership.
#guard execute [3,2,3,0,1,5,7,9,2,1,3,2,3,1,2] == some [1,1,0,1,1,1,9,2]

-- All vertices enter once the radius exceeds every distance.
#guard execute [2,3,1,1,3,2,3,1,1,2,1] == some [1,1,1,1,1,1]

end Checks.BallMass
