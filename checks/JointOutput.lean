import Lax455465Proofs.RamJointOutput
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.JointOutput
open Checks
set_option maxRecDepth 16384

def sequence (commands : List Com) : Com := commands.foldr Com.seq .skip

def readArray (name : String) (count : Expr) : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") count) (sequence [.read "test.word",.store name (.var "test.i") (.var "test.word"),
    .assign "test.i" (.add (.var "test.i") (.lit 1))])]

-- Input: edge-model tag, vertex count, primal-coordinate count, the
-- canonical rational cut flags, and the canonical primal coordinates.
def testCommand : Com := sequence [.read "flow.kind",.read "metric.n",.read "lp.columns",
  readArray "cut.flags" (.mul (.lit 2) (.var "metric.n")),
  readArray "flow.primal" (.mul (.lit 2) (.var "lp.columns")),RamJointOutput.command]
def layout : Layout := let names := commandNames testCommand
  ⟨names.1.eraseDups,names.2.eraseDups,256⟩
def execute (xs : List ℕ) : Option (List ℕ) := executeCompiled layout 128 5000000 testCommand xs

def zeros (n : ℕ) : List ℕ := (List.replicate n [0,1]).flatten
-- Two vertices: one value coordinate followed by sixteen arc coordinates.
def primal : List ℕ := [3,5, 2,3, 0,1, 5,7]++zeros 13
def undirected : List ℕ := [3,5, 1,3, 0,1, 5,14]++zeros 13

-- Directed coordinates are unchanged; flags emit one word per vertex.
#guard execute ([1,2,17, 1,1,0,1]++primal) == some ([1,0]++primal)
#guard execute ([1,2,17, 0,1,1,1]++primal) == some ([0,1]++primal)
-- Only arc coordinates are halved. Reduction handles even numerators and zero.
#guard execute ([0,2,17, 1,1,0,1]++primal) == some ([1,0]++undirected)
#guard execute ([0,2,17, 0,1,1,1]++primal) == some ([0,1]++undirected)
-- The all-zero vector retains canonical denominator one in both models.
#guard execute ([0,2,17, 1,1,0,1]++zeros 17) == some ([1,0]++zeros 17)
#guard execute ([1,2,17, 1,1,0,1]++zeros 17) == some ([1,0]++zeros 17)
-- Boundary dimensions exercise the writer, independent of solver preconditions.
#guard execute [0,1,2, 1,1, 7,9, 3,4] == some [1,7,9,3,8]
#guard execute [0,0,1, 7,9] == some [7,9]

end Checks.JointOutput
