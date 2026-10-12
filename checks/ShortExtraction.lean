import Lax455465Proofs.RamShortExtraction
import Lax455465Proofs.RamLayeredData
import Checks.Common

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax455465Proofs
namespace Checks.ShortExtraction
open Checks
set_option maxRecDepth 16384

def sequence (cs : List Com) : Com := cs.foldr Com.seq .skip
def readPrimal : Com := sequence [.assign "test.i" (.lit 0),
  .while (.lt (.var "test.i") (.mul (.lit 2) (.var "lp.columns")))
    (sequence [.read "test.word",.store "flow.primal" (.var "test.i") (.var "test.word"),
      .assign "test.i" (.add (.var "test.i") (.lit 1))])]
def command : Com := sequence [.read "lp.n",.read "short.layer",
  .assign "lp.n2" (.mul (.var "lp.n") (.var "lp.n")),RamLayeredData.dimensions,
  readPrimal,RamShortExtraction.command]
def layout : Layout := let names:=commandNames command
  ⟨names.1.eraseDups,names.2.eraseDups,4096⟩
def execute (xs : List ℕ) := executeCompiledCached layout 128 10000000 command xs
def index (n L st k u v : ℕ) := 1+st*(L*(n*n))+k*(n*n)+u*n+v
def coordinates (n L : ℕ) (f : List ℕ) (positive : List (ℕ×List ℕ)) : List ℕ :=
  (List.range (1+(n*n)*(L*(n*n)))).flatMap fun i =>
    if i=0 then f else ((positive.find? fun p => p.1=i).map Prod.snd).getD [0,1]
def record (s t numerator denominator : ℕ) : List ℕ := [2,s,t,numerator,denominator]

-- Exact header, both ordered commodities, and canonical zero output.
#guard execute ([2,1]++coordinates 2 1 [2,1] [(6,[1,1]),(11,[1,1])]) ==
  some ([2,1,2]++record 0 1 1 1++record 1 0 1 1)
#guard execute ([2,1]++coordinates 2 1 [0,1] []) == some [0,1,0]

def waits (n L : ℕ) : List (ℕ×List ℕ) :=
  (List.range (n*n)).flatMap fun st => let s:=st/n; let t:=st%n
    if s=t then [] else (List.range L).map fun k =>
      (index n L st k s (if k+1=L then t else s),[1,2])
def expected (n : ℕ) : List ℕ := [1,1,n*(n-1)]++
  (List.range (n*n)).flatMap fun st => if st/n=st%n then [] else record (st/n) (st%n) 1 2
-- Waiting arcs disappear from each of six emitted physical paths.
#guard execute ([3,2]++coordinates 3 2 [1,1] (waits 3 2)) == some (expected 3)
-- One commodity has two bottlenecks and requires two distinct records.
def splitPaths : List (ℕ×List ℕ) := (waits 3 2).filter (fun p => p.1≠index 3 2 2 0 0 0 ∧ p.1≠index 3 2 2 1 0 2) ++
  [(index 3 2 2 0 0 0,[1,4]),(index 3 2 2 1 0 2,[1,4]),
   (index 3 2 2 0 0 1,[1,4]),(index 3 2 2 1 1 2,[1,4])]
def splitExpected : List ℕ := [1,1,7]++record 0 1 1 2++record 0 2 1 4++[3,0,1,2,1,4]++
  record 1 0 1 2++record 1 2 1 2++record 2 0 1 2++record 2 1 1 2
#guard execute ([3,2]++coordinates 3 2 [1,1] splitPaths) == some splitExpected

end Checks.ShortExtraction
