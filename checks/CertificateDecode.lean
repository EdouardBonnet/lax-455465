import Lax455465Proofs.RamOptimalDecode
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.CertificateDecode
open Checks

def readWords : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.var "test.length"))
    (.seq (.read "test.word")
      (.seq (.store "vm.output" (.var "test.i") (.var "test.word"))
        (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def emitWords (a count : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var count)))
    (.seq (.write (.get a (.var "test.i")))
      (.assign "test.i" (.add (.var "test.i") (.lit 1)))))

def queryCommand : Com := .seq (.read "lp.columns") (.seq (.read "lp.rows")
  (.seq (.read "test.length") (.seq readWords
    (.seq RamOptimalDecode.command
      (.seq (emitWords "flow.primal" "lp.columns")
        (.seq (emitWords "flow.dual" "lp.rows") (.write (.var "cert.cursor"))))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 200000 queryCommand xs

/- The actual compiled decoder receives a tag and canonical signed LP
coordinates, and emits unsigned coordinate pairs plus the final cursor. -/
#guard execute [3,2,16,0,0,13,8,0,0,1,0,7,1,0,2,3,0,11,1] ==
  some [13,8,0,1,7,1,2,3,11,1,16]

-- Empty dual vector, as in the zero-order flow LP.
#guard execute [1,0,4,0,0,0,1] == some [0,1,4]

-- Both loops are empty: no accidental buffer read or cursor advance.
#guard execute [0,0,1,0] == some [1]

-- Large integer and a small fraction are retained exactly.
#guard execute [1,1,7,0,0,1048577,1,0,1,1048576] ==
  some [1048577,1,1,1048576,7]

end Checks.CertificateDecode
