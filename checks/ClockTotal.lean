import Lax455465Proofs.RamClockTotal
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.ClockTotal
open Checks
set_option maxRecDepth 16384

/-- Execute the full wrapper after compilation to the registered RAM.
The physical tape contains the usual length prefix. -/
def executeAt (host : ℕ) (p : Lax808846.Ram.Program) (wc tc xs : List ℕ) : Option (List ℕ) :=
  let c := RamClockTotal.command p wc tc
  let names := Checks.commandNames c
  let layout : Layout := ⟨names.1.eraseDups,names.2.eraseDups,256⟩
  executeCompiled layout host 5000000 c (xs.length::xs)

def execute := executeAt 128

-- Zero clock, nontermination, and a truncated computation with live output.
#guard execute [.set 0 17,.write 0,.halt] [8] [0] [] == some []
#guard execute [.jump 0] [8] [6] [] == some []
#guard execute [.set 0 3,.write 0,.jump 1] [8] [6] [] == some [3,3,3]
-- Explicit halt, out-of-range counter, and exhausted reads all freeze the
-- source state; the host still terminates at its explicit compiled halt.
#guard execute [.set 0 17,.write 0,.halt] [8] [6] [] == some [17]
#guard execute [.set 0 17,.write 0,.jump 500] [8] [6] [] == some [17]
#guard execute [.read 0,.read 1,.write 1] [8] [6] [] == some []
-- The virtual input includes its length prefix, and arbitrary logical words
-- are accepted without requiring a valid graph encoding.
#guard execute [.read 0,.read 1,.write 0,.write 1] [8] [6] [77] == some [1,77]
-- Virtual wraparound is independent of the host word width.
#guard execute [.set 0 17,.write 0,.halt] [2] [6] [] == some [1]
#guard executeAt 256 [.set 0 17,.write 0,.halt] [2] [6] [] == some [1]
-- Horner clock evaluation uses binary size: bitSize [3] = 3 and
-- bitSize [9] = 5, so the same program makes one or two writes respectively.
#guard execute [.set 0 3,.write 0,.jump 1] [8] [0,1] [3] == some [3]
#guard execute [.set 0 3,.write 0,.jump 1] [8] [0,1] [9] == some [3,3]

end Checks.ClockTotal
