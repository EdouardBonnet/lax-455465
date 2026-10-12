import Lax455465Proofs.RamThresholdMask
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.ThresholdMask
open Checks

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip
def run (reversed : Bool) : Com := sequence [.read "metric.n",.read "cut.threshold.n",.read "cut.threshold.d",
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.read "test.word",.store "cut.potential" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))]),RamThresholdMask.command reversed,
  .assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n")))
    (sequence [.write (.get "cut.flags" (.var "test.i")),.assign "test.i" (.add (.var "test.i") (.lit 1))])]
def layout (reversed : Bool) : Layout := let names := commandNames (run reversed)
  ⟨names.1.eraseDups,names.2.eraseDups,128⟩
def execute (reversed : Bool) (xs : List ℕ) : Option (List ℕ) := executeCompiled (layout reversed) 128 1000000 (run reversed) xs

-- Equality is included in both directions. Duplicate potentials and exact
-- fractional thresholds exercise the shores used by positive and negative sweeps.
#guard execute false [4,1,2,0,1,1,2,1,1,1,2] == some [1,1,1,1,0,1,1,1]
#guard execute true [4,1,2,0,1,1,2,1,1,1,2] == some [0,1,1,1,1,1,1,1]
#guard execute false [2,0,1,0,1,1,1] == some [1,1,0,1]
#guard execute true [2,0,1,0,1,1,1] == some [1,1,1,1]
#guard execute false [0,1,1] == some []
#guard execute true [1,1,2^40,1,2^40] == some [1,1]

end Checks.ThresholdMask
