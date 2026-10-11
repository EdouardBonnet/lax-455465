import Lax455465Proofs.RamEdgePortion
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.EdgePortion
open Checks

def queryCommand : Com := .seq (.read "portion.length.n") (.seq (.read "portion.length.d")
  (.seq (.read "portion.base.n") (.seq (.read "portion.base.d")
    (.seq (.read "portion.radius.n") (.seq (.read "portion.radius.d")
      (.seq RamEdgePortion.command (.seq (.write (.var "rat.n")) (.write (.var "rat.d")))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 500000 queryCommand xs

-- The ball radius is before the tail, exactly at it, or partway along the edge.
#guard execute [3,2,4,3,1,2] == some [0,1]
#guard execute [3,2,4,3,4,3] == some [0,1]
#guard execute [3,2,4,3,7,3] == some [1,1]

-- The edge saturates at its full length after the head event.
#guard execute [3,2,4,3,17,6] == some [3,2]
#guard execute [3,2,4,3,11,3] == some [3,2]

-- Zero lengths and zero radii remain canonical.
#guard execute [0,1,0,1,5,7] == some [0,1]
#guard execute [1048577,1048576,0,1,0,1] == some [0,1]

end Checks.EdgePortion
