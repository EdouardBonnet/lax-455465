import Lax455465Proofs.RamTruncatedSubtract
import Lax455465Proofs.RamUnsignedSum
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.RegionArithmetic
open Checks

def subtraction : Com := .seq (.read "left.n") (.seq (.read "left.d")
  (.seq (.read "right.n") (.seq (.read "right.d")
    (.seq (.assign "left.s" (.lit 0)) (.seq (.assign "right.s" (.lit 0)) RamTruncatedSubtract.command)))))

def summand : Com := .seq (.read "rat.n") (.seq (.read "rat.d") (.assign "rat.s" (.lit 0)))

def summation : Com := .seq (.read "test.count") (RamUnsignedSum.command "test.i" "test.count" summand)

def queryCommand : Com := .seq (.read "test.kind")
  (.seq (.ite (.eq (.var "test.kind") (.lit 0)) subtraction summation)
    (.seq (.write (.var "rat.n")) (.write (.var "rat.d"))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 500000 queryCommand xs

-- A positive clipped difference is reduced exactly.
#guard execute [0,2,3,1,2] == some [1,6]

-- Negative and equal differences produce canonical zero.
#guard execute [0,1,3,2,3] == some [0,1]
#guard execute [0,1048577,1048576,1048577,1048576] == some [0,1]

-- The actual accumulator handles an empty list and changing denominators.
#guard execute [1,0] == some [0,1]
#guard execute [1,3,1,3,1,6,7,8] == some [11,8]

-- Large numerators, a zero summand, and a final gcd reduction.
#guard execute [1,3,1099511627777,1048576,0,1,1,1048576] == some [549755813889,524288]

end Checks.RegionArithmetic
