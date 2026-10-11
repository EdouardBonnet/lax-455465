import Lax455465Proofs.RamProductVector
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.ProductVector
open Checks

def readVector (array : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "product.count")))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def writeVector : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "product.count")))
    (.seq (.write (.get "product.output" (.var "test.i"))) (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "product.count") (.seq (readVector "product.left")
  (.seq (readVector "product.right") (.seq (RamProductVector.command "product.left" "product.right" "product.output") writeVector)))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled queryLayout 128 2000000 queryCommand xs

#guard execute [0] == some []
-- Intersect the actual zero/one masks.
#guard execute [3,1,1,0,1,1,1,1,1,1,1,0,1] == some [1,1,0,1,0,1]
-- Apply an active-vertex mask to rational weights.
#guard execute [3,1,2,7,3,2,1,1,1,0,1,1,1] == some [1,2,0,1,2,1]
-- Exact scaling, including normalization after multiplication.
#guard execute [2,7,3,1099511627777,1048576,3,7,1,2] == some [1,1,1099511627777,2097152]

end Checks.ProductVector
