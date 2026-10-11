import Lax455465Proofs.RamRegionQuery
import Checks.Common

set_option maxRecDepth 4096

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.RegionQuery
open Checks

def readVector (array count : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def writePair (name : String) : Com := .seq (.write (.var (name ++ ".n"))) (.write (.var (name ++ ".d")))

def queryCommand : Com := .seq (.read "metric.n")
  (.seq (.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")))
    (.seq (.read "region.radius.n") (.seq (.read "region.radius.d")
      (.seq (.read "round.seed.n") (.seq (.read "round.seed.d")
        (.seq (.read "round.slope.n") (.seq (.read "round.slope.d")
          (.seq (readVector "region.weights" "metric.n")
            (.seq (readVector "region.out" "metric.n") (.seq (readVector "region.in" "metric.n")
              (.seq (readVector "region.capacities" "metric.n2") (.seq (readVector "metric.old" "metric.n2")
                (.seq RamRegionQuery.command (.seq (.write (.var "find.ok"))
                  (.seq (.write (.var "region.outward")) (.seq (writePair "region.boundary")
                    (.seq (writePair "region.volume") (.seq (writePair "region.outMass") (writePair "region.inMass")))))))))))))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 5000000 queryCommand xs

-- The component query is total on empty dimensions and still requires a
-- positive radius, even if the boundary inequality holds at zero.
#guard execute [0,1,1,1,5,0,1] == some [1,1,0,1,1,5,0,1,0,1]
#guard execute [0,0,1,1,5,1,1] == some [0,1,0,1,1,5,0,1,0,1]

def edges : List ℕ := [0,1,2,3,5,7,0,1,0,1,3,2,2,1,0,1]
def inwardDistances : List ℕ := [1,1,2,1,0,1,1,2,0,1,1,1]
def outwardDistances : List ℕ := [1,1,2,1,0,1,1,1,0,1,1,2]

-- The selected inward ball has smaller mass. These exercise acceptance,
-- rejection, and equality at the exact volume-growth threshold.
#guard execute ([2,1,1,1,5,1,1] ++ inwardDistances ++ edges) == some [1,0,5,7,32,35,3,1,1,1]
#guard execute ([2,1,1,1,5,1,2] ++ inwardDistances ++ edges) == some [0,0,5,7,32,35,3,1,1,1]
#guard execute ([2,1,1,1,5,25,32] ++ inwardDistances ++ edges) == some [1,0,5,7,32,35,3,1,1,1]

-- The outward branch also accepts equality and rejects a smaller slope.
#guard execute ([2,1,1,1,5,10,13] ++ outwardDistances ++ edges) == some [1,1,2,3,13,15,1,1,3,1]
#guard execute ([2,1,1,1,5,9,13] ++ outwardDistances ++ edges) == some [0,1,2,3,13,15,1,1,3,1]
#guard execute ([2,0,1,1,5,1,1] ++ outwardDistances ++ edges) == some [0,1,0,1,1,5,0,1,0,1]

end Checks.RegionQuery
