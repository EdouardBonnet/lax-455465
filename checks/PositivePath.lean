import Lax455465Proofs.RamPositivePath
import Lax455465Proofs.RamLayeredData
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.PositivePath
open Checks
set_option maxRecDepth 16384

def sequence (cs : List Com) : Com := cs.foldr Com.seq .skip

def readArray (array : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store array (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def emitArray (array length : String) : Com := sequence [.write (.var length),.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.var length)) (sequence [.write (.get array (.var "test.i")),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]

def command : Com := sequence [.read "lp.n",.read "short.layer",.read "short.commodity",
  .assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")),RamLayeredData.dimensions,
  .assign "short.source" (.div (.var "short.commodity") (.var "lp.n")),
  readArray "flow.primal" (.mul (.lit 2) (.var "lp.columns")),RamPositivePath.command,
  emitArray "short.raw" "short.rawLength",emitArray "short.simple" "short.simpleLength"]
def layout : Layout := let names := commandNames command
  ⟨names.1.eraseDups,names.2.eraseDups,1024⟩
def execute (xs : List ℕ) := executeCompiledCached layout 128 3000000 command xs

def coordinates (n L : ℕ) (positive : List ℕ) : List ℕ :=
  (List.range (1+(n*n)*(L*(n*n)))).flatMap fun i =>
    if i=0 then [1,1] else if i∈positive then [1,2] else [0,1]

-- Direct and reverse single-edge commodities read distinct LP coordinates.
#guard execute ([2,1,1]++coordinates 2 1 [6]) == some [2,0,1,2,0,1]
#guard execute ([2,1,2]++coordinates 2 1 [11]) == some [2,1,0,2,1,0]
-- The repeated source is erased while the complete layered walk is retained.
#guard execute ([3,3,2]++coordinates 3 3 [56,67,75]) == some [4,0,1,0,2,2,0,2]
-- Waiting steps are also removed from the physical certificate path.
#guard execute ([3,3,2]++coordinates 3 3 [55,65,78]) == some [4,0,0,1,2,3,0,1,2]

end Checks.PositivePath
