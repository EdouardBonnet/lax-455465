import Lax455465Proofs.RamMinPlus
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.MinPlus
open Checks

def readWords : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "test.count")))
    (.seq (.read "test.word")
      (.seq (.store "metric.old" (.var "test.i") (.var "test.word"))
        (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def queryCommand : Com := .seq (.read "test.count") (.seq (.read "metric.a")
  (.seq (.read "metric.b") (.seq (.read "metric.c") (.seq readWords
    (.seq RamMinPlus.command (.seq (.write (.var "rat.n")) (.write (.var "rat.d"))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 300000 queryCommand xs

-- The direct value wins: min(1/3, 2/3 + 1/2) = 1/3.
#guard execute [3,0,1,2,1,3,2,3,1,2] == some [1,3]

-- The pivot legs win and are reduced: min(7, 1/3 + 1/6) = 1/2.
#guard execute [3,0,1,2,7,1,1,3,1,6] == some [1,2]

-- Equality, including repeated addresses, retains the exact value.
#guard execute [3,0,1,2,1,2,1,3,1,6] == some [1,2]
#guard execute [2,0,0,1,0,1,0,1] == some [0,1]

-- Zero legs improve a positive distance to zero.
#guard execute [3,0,1,2,1048577,1,0,1,0,1] == some [0,1]

end Checks.MinPlus
