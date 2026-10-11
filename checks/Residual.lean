import Lax455465Proofs.RamResidual
import Lax455465Proofs.RamActiveInit
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.Residual
open Checks

def readVector (array count : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def writeVector (array count : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (.seq (.write (.get array (.var "test.i"))) (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand (activateAll : Bool) : Com := .seq (.read "metric.n")
  (.seq (.assign "metric.n2" (.mul (.var "metric.n") (.var "metric.n")))
    (.seq (readVector "flow.weights" "metric.n")
      (.seq (readVector "flow.capacities" "metric.n2")
        (.seq (if activateAll then RamActiveInit.command else readVector "region.active" "metric.n")
          (.seq RamResidual.command (.seq (writeVector "region.weights" "metric.n")
            (writeVector "region.capacities" "metric.n2")))))))

def queryLayout (activateAll : Bool) : Layout := let names := commandNames (queryCommand activateAll)
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (activateAll : Bool) (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled (queryLayout activateAll) 128 3000000 (queryCommand activateAll) xs

#guard execute false [0] == some []
#guard execute true [0] == some []

-- Both endpoints are needed for a residual arc, even if one endpoint
-- carries zero demand. Initialization keeps all transit vertices active.
def graph : List ℕ := [2,0,1,7,3,0,1,2,3,5,7,0,1]
#guard execute true graph == some [0,1,7,3,0,1,2,3,5,7,0,1]
#guard execute false (graph ++ [0,1,1,1]) == some [0,1,7,3,0,1,0,1,0,1,0,1]
#guard execute false (graph ++ [1,1,0,1]) == some [0,1,0,1,0,1,0,1,0,1,0,1]
#guard execute false (graph ++ [1,1,1,1]) == some [0,1,7,3,0,1,2,3,5,7,0,1]

-- An internal arc is retained exactly, while every incident arc to the
-- removed vertex is disabled in either orientation.
#guard execute false [3,1,2,7,3,2,1,0,1,2,1,3,2,5,3,0,1,7,4,11,5,13,6,0,1,
  1,1,0,1,1,1] == some [1,2,0,1,2,1,0,1,0,1,3,2,0,1,0,1,0,1,11,5,0,1,0,1]

end Checks.Residual
