import Lax455465Proofs.RamRegionDirection
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.RegionDirection
open Checks

def readVector (array : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def queryCommand : Com := .seq (.read "metric.n")
  (.seq (.read "region.radius.n") (.seq (.read "region.radius.d")
    (.seq (readVector "region.weights") (.seq (readVector "region.out") (.seq (readVector "region.in")
      (.seq (RamBallMass.command true) (.seq (RamBallMass.command false) (.seq RamRegionDirection.command
        (.seq (.write (.var "region.outward"))
          (.seq (.write (.var "region.outMass.n")) (.seq (.write (.var "region.outMass.d"))
            (.seq (.write (.var "region.inMass.n")) (.write (.var "region.inMass.d"))))))))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 3000000 queryCommand xs

-- Empty balls and equal masses resolve outward.
#guard execute [0,1,1] == some [1,0,1,0,1]
#guard execute [2,0,1,1,1,2,1,0,1,1,1,0,1,1,2] == some [1,0,1,0,1]
#guard execute [2,1,1,1,1,2,1,0,1,1,2,0,1,1,2] == some [1,3,1,3,1]

-- Either orientation may have the smaller residual mass. A vertex exactly
-- at the radius is excluded by the native ball-mask commands.
#guard execute [2,1,1,1,1,2,1,0,1,1,1,0,1,1,2] == some [1,1,1,3,1]
#guard execute [2,1,1,1,1,2,1,0,1,1,2,0,1,1,1] == some [0,3,1,1,1]

-- Fractional weights and a zero-weight transit vertex.
#guard execute [3,1,1,0,1,1,2,7,3,0,1,1,2,1,1,0,1,1,1,1,2] == some [1,1,2,7,3]

end Checks.RegionDirection
