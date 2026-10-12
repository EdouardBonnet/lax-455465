import Checks.Common

namespace Checks.CachedMemory
open Checks Lax808846.Ram

def program : Program := [.set 0 7,.set 1 3,.add 2 0 1,.sub 3 0 1,.mul 4 0 1,.div 5 0 1,
  .and 6 0 1,.shiftl 7 0 1,.not 8 0,.set 9 20,.store 9 2,.load 10 9,
  .read 11,.inputLength 12,.set 13 1,.inputLoad 14 13,.write 10,.write 11,.write 12,.write 14,
  .jzero 3 23,.jeof 23,.jump 24,.write 8,.halt]
def reference (w : ℕ) (xs : List ℕ) := runToHalt w program 1000 (initState xs)
def cached (w : ℕ) (xs : List ℕ) := runToHaltCached w program.toArray 1000 {} (initState xs)

-- Compare the cached execution with the registered step interpreter across
-- direct and indirect writes, arithmetic, indexed/sequential input, jumps,
-- explicit halt, and wrapping addresses at small word widths.
#guard cached 0 [5,6] == reference 0 [5,6]
#guard cached 1 [5,6] == reference 1 [5,6]
#guard cached 3 [5,6] == reference 3 [5,6]
#guard cached 8 [5,6] == reference 8 [5,6]
#guard cached 8 [] == reference 8 []
#guard cached 8 [5] == reference 8 [5]

end Checks.CachedMemory
