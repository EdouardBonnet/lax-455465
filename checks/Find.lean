import Lax455465Proofs.RamFind
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.Find
open Checks

def queryCommand : Com := .seq (.read "find.count") (.seq (RamFind.command (.read "find.ok"))
  (.seq (.write (.var "find.found")) (.write (.var "find.result"))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled queryLayout 128 100000 queryCommand xs

#guard execute [0] == some [0,0]
#guard execute [3,0,0,0] == some [0,0]
#guard execute [4,0,0,1,0] == some [1,2]
#guard execute [4,1,1,1,1] == some [1,0]
#guard execute [4,0,0,0,1] == some [1,3]

end Checks.Find
