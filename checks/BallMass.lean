import Lax455465Proofs.RamBallMask
import Lax455465Proofs.RamMaskedSum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.BallMass
open Checks

def readVector (array : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "ball.count")))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def writeMask : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "ball.count")))
    (.seq (.write (.get "region.mask" (.var "test.i"))) (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "ball.count") (.seq (.read "region.radius.n") (.seq (.read "region.radius.d")
  (.seq (readVector "flow.weights") (.seq (readVector "region.distance")
    (.seq (RamBallMask.command "region.distance" "region.mask") (.seq (.assign "sum.count" (.var "ball.count"))
      (.seq (RamMaskedSum.command "flow.weights" "region.mask")
        (.seq writeMask (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))))))))))

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
