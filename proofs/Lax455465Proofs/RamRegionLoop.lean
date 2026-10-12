import Lax455465Proofs.RamResidual
import Lax455465Proofs.RamRoot
import Lax455465Proofs.RamRegionChoice
import Lax455465Proofs.RamRegionBranch
import Lax455465Proofs.RamLargeThreshold
import Lax455465Proofs.RamActiveInit

set_option maxRecDepth 4096
namespace Lax455465Proofs.RamRegionLoop
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Save the runtime root before the candidate-radius finder reuses its
index registers. No root, radius or decision is supplied as extra input. -/
def foundRoot : Com := .seq (.assign "region.root" (.var "find.result"))
  (.seq RamRegionSetup.command (.ite (.eq (.var "find.found") (.lit 1))
    RamRegionBranch.command (.assign "region.phase" (.lit 3))))

def iteration : Com := .seq (.seq RamResidual.command RamRoot.command)
  (.ite (.eq (.var "find.found") (.lit 1)) foundRoot (.assign "region.phase" (.lit 2)))

/-- Phase zero grows another region, phase one freezes a large-ball witness,
phase two records exhaustion, and phase three records an unsuccessful search.
The latter is excluded on the mathematical algorithm's valid inputs. -/
def step : Com := .seq (.ite (.eq (.var "region.phase") (.lit 0)) iteration .skip)
  (.assign "loop.i" (.add (.var "loop.i") (.lit 1)))

/-- A fixed native loop takes at most the original positive-support budget
of active iterations, with one final exhaustion check. It recomputes every
residual array from the original input rather than multiplying old rationals. -/
def command : Com := .seq RamLargeThreshold.command (.seq RamActiveInit.command
  (.seq (.assign "history.pos" (.lit 0)) (.seq (.assign "region.phase" (.lit 0))
    (.seq (.assign "loop.limit" (.add (.var "round.support") (.lit 1)))
      (.seq (.assign "loop.i" (.lit 0))
        (.while (.lt (.var "loop.i") (.var "loop.limit")) step))))))

end Lax455465Proofs.RamRegionLoop
