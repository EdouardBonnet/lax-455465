import Lax455465Proofs.RamVolume
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.Volume
open Checks

def readVector (array count : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def queryCommand (outward : Bool) : Com := .seq (.read "metric.n")
  (.seq (.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")))
    (.seq (.read "region.radius.n") (.seq (.read "region.radius.d")
      (.seq (.read "round.seed.n") (.seq (.read "round.seed.d")
        (.seq (readVector "region.capacities" "metric.n2")
          (.seq (readVector "metric.old" "metric.n2")
            (.seq (readVector (RamRootDistances.array outward) "metric.n")
              (.seq (RamVolume.command outward)
                (.seq (.write (.var "region.volume.n")) (.write (.var "region.volume.d"))))))))))))

def queryLayout (outward : Bool) : Layout := let names := commandNames (queryCommand outward)
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (outward : Bool) (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled (queryLayout outward) 128 3000000 (queryCommand outward) xs

-- No edges leave exactly the seed, including zero-dimensional inputs.
#guard execute true [0,1,1,17,11] == some [17,11]
#guard execute false [0,0,1,0,1] == some [0,1]
#guard execute true [1,1,1,17,11,0,1,0,1,0,1] == some [17,11]

-- The original row-major capacities are transposed mathematically for an
-- inward volume. The runtime base index changes to the head coordinate.
def edges : List ℕ := [0,1,2,3,5,7,0,1,0,1,3,2,2,1,0,1]
#guard execute true ([2,1,1,1,5] ++ edges ++ [0,1,1,2]) == some [257,210]
#guard execute false ([2,1,1,1,5] ++ edges ++ [0,1,1,2]) == some [131,105]

-- Before all tail events, only the seed remains; beyond all edge lengths,
-- both orientations saturate at the complete length cost.
#guard execute true ([2,0,1,1,5] ++ edges ++ [0,1,1,2]) == some [1,5]
#guard execute true ([2,3,1,1,5] ++ edges ++ [0,1,1,2]) == some [92,35]
#guard execute false ([2,3,1,1,5] ++ edges ++ [0,1,1,2]) == some [92,35]

-- A base exactly at the radius contributes zero.
#guard execute true ([2,1,1,1,5] ++ edges ++ [0,1,1,1]) == some [13,15]
#guard execute false ([2,1,1,1,5] ++ edges ++ [0,1,1,1]) == some [32,35]

-- Larger rational words are normalized through clipping and multiplication.
#guard execute true [1,1,1,0,1,2^24+1,2^24,3,2,0,1] == some [2^24+1,2^24]

end Checks.Volume
