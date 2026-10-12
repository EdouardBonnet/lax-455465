import Lax455465Proofs.RamShortPrepare

namespace Lax455465Proofs.RamShortNoWrite
open Lax808846Proofs.Imp

theorem trial (p : Lax808846.Ram.Program) (coefficients : List ℕ) :
    (RamShortTrial.command p coefficients).NoWrite :=
  ⟨by decide,by decide,RamLayeredScope.solver_nowrite p coefficients,by decide,by decide,by decide⟩

theorem find (c : Com) (hc : c.NoWrite) : (RamFind.command c).NoWrite := by
  exact ⟨by decide,by decide,⟨⟨hc,by decide,by decide⟩,by decide⟩,by decide⟩

theorem scan (p : Lax808846.Ram.Program) (coefficients : List ℕ) :
    (RamShortScan.command p coefficients).NoWrite :=
  ⟨⟨by decide,find _ (trial p coefficients),by decide⟩,by decide,RamLayeredScope.solver_nowrite p coefficients⟩

theorem prepare (p : Lax808846.Ram.Program) (coefficients : List ℕ) :
    (RamShortPrepare.command p coefficients).NoWrite := ⟨by decide,scan p coefficients⟩

end Lax455465Proofs.RamShortNoWrite
