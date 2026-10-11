import Lax455465Proofs.RamMetricCost
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs

namespace Checks.MetricCost
open Checks

def readMatrix (array : String) : Com := .seq (.assign "test.i" (.lit 0))
  (.while (.lt (.var "test.i") (.mul (.lit 2) (.var "metric.n2")))
    (.seq (.read "test.word") (.seq (.store array (.var "test.i") (.var "test.word"))
      (.assign "test.i" (.add (.var "test.i") (.lit 1))))))

def queryCommand : Com := .seq (.read "test.n") (.seq (.assign "metric.n2" (.mul (.var "test.n") (.var "test.n")))
  (.seq (readMatrix "flow.capacities") (.seq (readMatrix "metric.old")
    (.seq RamMetricCost.command (.seq (.write (.var "round.cost.n")) (.write (.var "round.cost.d")))))))

def queryLayout : Layout := let names := commandNames queryCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩

def execute (xs : List ℕ) : Option (List ℕ) :=
  executeCompiled queryLayout 128 2000000 queryCommand xs

-- Empty and zero-cost metrics use the same actual accumulation loop.
#guard execute [0] == some [0,1]
#guard execute [1,0,1,0,1] == some [0,1]
#guard execute [2,0,1,1,1,5,2,0,1,0,1,0,1,0,1,0,1] == some [0,1]

-- Asymmetric capacities and distances contribute in their ordered direction.
#guard execute [2,0,1,1,1,5,2,0,1,0,1,7,3,3,5,0,1] == some [23,6]

-- Nine entries, changing denominators, and reduction across successive sums.
#guard execute [3,0,1,1,1,2,1,3,1,0,1,4,1,5,1,6,1,0,1,
  0,1,1,2,1,3,1,4,0,1,1,5,1,6,1,7,0,1] == some [617,140]

end Checks.MetricCost
