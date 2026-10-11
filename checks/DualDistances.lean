import Lax455465Proofs.RamDualDistances
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.DualDistances
open Checks

def readWords : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "test.rows")))
    (.seq (.read "test.word")
      (.seq (.store "flow.dual" (.var "test.i") (.var "test.word"))
        (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def emitWords : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "lp.n2")))
    (.seq (.write (.get "metric.old" (.var "test.i")))
      (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "lp.n")
  (.seq (.assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")))
    (.seq (.assign "test.rows" (.add (.var "lp.n2")
      (.mul (.lit 2) (.mul (.var "lp.n2") (.var "lp.n")))))
      (.seq readWords (.seq RamDualDistances.command emitWords))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 1500000 queryCommand xs

def zeros (k : ℕ) : List ℕ := (List.replicate k [0,1]).flatten

-- Empty network and a nonzero single diagonal multiplier.
#guard execute [0] == some []
#guard execute ([1,7,3] ++ zeros 2) == some [0,1]

-- Ignore both diagonal multipliers while retaining asymmetric off-diagonal lengths.
#guard execute ([2,999,1,2,3,7,4,888,1] ++ zeros 16) ==
  some [0,1,2,3,7,4,0,1]

-- Read actual multiplier rows, zero the diagonal, then compute all distances.
#guard execute ([3,7,4,1,3,9,1,8,1,9,8,1,6,1,2,7,1,13,9] ++ zeros 54) ==
  some [0,1,1,3,1,2,2,3,0,1,1,6,1,2,5,6,0,1]

end Checks.DualDistances
