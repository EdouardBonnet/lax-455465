import Lax455465Proofs.RamBoundary
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.Boundary
open Checks

def readVector (array count : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def queryCommand (outward : Bool) : Com := .seq (.read "metric.n")
  (.seq (.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")))
    (.seq (.read "region.radius.n") (.seq (.read "region.radius.d")
      (.seq (readVector "region.weights" "metric.n")
        (.seq (readVector (RamRootDistances.array outward) "metric.n")
          (.seq (readVector "region.capacities" "metric.n2")
            (.seq (RamBallMass.command outward) (.seq (RamBoundary.command outward)
              (.seq (.write (.var (RamBallMass.massName outward ++ ".n")))
                (.seq (.write (.var (RamBallMass.massName outward ++ ".d")))
                  (.seq (.write (.var "region.boundary.n")) (.write (.var "region.boundary.d")))))))))))))

def queryLayout (outward : Bool) : Layout := let names := commandNames (queryCommand outward)
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (outward : Bool) (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled (queryLayout outward) 128 3000000 (queryCommand outward) xs

-- Empty graph, in both directions.
#guard execute true [0,1,1] == some [0,1,0,1]
#guard execute false [0,1,1] == some [0,1,0,1]

-- The middle vertex is exactly at the radius. Outward and inward
-- boundaries differ on an asymmetric capacity matrix.
def asymmetric : List ℕ := [3,1,1,1,2,7,3,2,1,0,1,1,1,3,4,
  0,1,2,1,3,1,5,1,0,1,7,1,11,1,13,1,0,1]
#guard execute true asymmetric == some [5,2,15,1]
#guard execute false asymmetric == some [5,2,12,1]

-- The empty ball and the whole graph have zero boundary.
#guard execute true [2,0,1,1,1,7,3,0,1,1,2,0,1,2,3,5,7,0,1] == some [0,1,0,1]
#guard execute false [2,3,1,1,1,7,3,0,1,1,2,0,1,2,3,5,7,0,1] == some [10,3,0,1]

-- Fractional capacities are normalized by the actual summation command.
#guard execute true [2,1,1,0,1,9,2,0,1,1,1,0,1,2,3,5,7,0,1] == some [0,1,2,3]
#guard execute false [2,1,1,0,1,9,2,0,1,1,1,0,1,2,3,5,7,0,1] == some [0,1,5,7]

end Checks.Boundary
