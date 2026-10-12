import Lax455465Proofs.RamHistoryEntry
import Lax455465Proofs.RamArrayScalar
import Lax455465Proofs.RamScalarComparison
import Lax455465Proofs.RamFind
import Lax455465Proofs.MetricMatrix
import Lax455465Proofs.RamRegionContext

set_option maxRecDepth 8192
namespace Lax455465Proofs.RamHistoryTest
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar RamRegionRecord RamRegionContext
open Lax455465.RationalEncoding DirectedFlowLP FlowLpIndices
open scoped NNRat

def pair {n : ℕ} (e : Entry n) (v : Fin n) : Fin n × Fin n :=
  if e.outward then (e.root,v) else (v,e.root)

def Context {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n) (σ : Env) : Prop :=
  σ.vars "metric.n"=n ∧ σ.vars "find.count"=history.length ∧ σ.vars "history.vertex"=v.val ∧
    Prefix (RamUnsignedBuffer.encode (MetricMatrix.values d)) "metric.old" σ ∧
    Prefix (words history) "region.history" σ

theorem frame {B K : ℕ} {cmd : Com} {σ τ : Env} (rr : Run B cmd σ τ K)
    {n : ℕ} {d : MetricMatrix.Matrix n} {history : List (Entry n)} {v : Fin n} (h : Context d history v σ)
    (hx : ∀ x∈["metric.n","find.count","history.vertex"],x∉cmd.wvars)
    (ha : ∀ a∈["metric.old","region.history"],a∉cmd.warrs) : Context d history v τ := by
  simpa only [Context,Prefix,rr.frame_var "metric.n" (hx _ (by simp)),rr.frame_var "find.count" (hx _ (by simp)),
    rr.frame_var "history.vertex" (hx _ (by simp)),rr.frame_arr "metric.old" (ha _ (by simp)),
    rr.frame_arr "region.history" (ha _ (by simp))] using h

def address : Com := .ite (.eq (.var "history.outward") (.lit 1))
  (.assign "history.edge" (.add (.mul (.var "history.root") (.var "metric.n")) (.var "history.vertex")))
  (.assign "history.edge" (.add (.mul (.var "history.vertex") (.var "metric.n")) (.var "history.root")))
def flag : Com := .ite (.eq (.var "cmp.le") (.lit 0)) (.assign "find.ok" (.lit 1)) (.assign "find.ok" (.lit 0))
def command : Com := .seq RamHistoryEntry.command (.seq address
  (.seq (RamArrayScalar.command "metric.old" "history.edge" "history.distance")
    (.seq (RamScalarComparison.command "history.radius" "history.distance") flag)))

theorem address_spec (B : ℕ) {n : ℕ} (e : Entry n) (v : Fin n) (h1 : 1 < B) (hn : n < B) (hn2 : n*n < B) :
    Spec B (fun σ => σ.vars "metric.n"=n ∧ σ.vars "history.vertex"=v.val ∧ RamHistoryEntry.Output e σ) address
      (fun _ τ => τ.vars "history.edge"=(edgeIndex n (pair e v)).val) 10 := by
  have hrv : (edgeIndex n (e.root,v)).val < B := (edgeIndex n (e.root,v)).isLt.trans hn2
  have hvr : (edgeIndex n (v,e.root)).val < B := (edgeIndex n (v,e.root)).isLt.trans hn2
  rw [edge_value] at hrv hvr
  have hr : e.root.val < B := e.root.isLt.trans hn
  have hv : v.val < B := v.isLt.trans hn
  have hrn : e.root.val*n < B := by omega
  have hvn : v.val*n < B := by omega
  rintro σ ⟨hnσ,hvσ,hrσ,hqσ,hoσ⟩
  cases he : e.outward <;> run_vcg <;> simp_all [pair,edge_value] <;> omega

theorem flag_spec (B : ℕ) (a b : ℚ≥0) (h1 : 1 < B) :
    Spec B (fun σ => σ.vars "cmp.le"=(if (a : ℚ) ≤ (b : ℚ) then 1 else 0)) flag
      (fun _ τ => τ.vars "find.ok"=(if b < a then 1 else 0)) 6 := by
  intro σ hσ
  by_cases h : (a : ℚ) ≤ (b : ℚ) <;> run_vcg <;> simp_all <;> omega

/-- Test membership in the directed open ball stored in a runtime record. -/
theorem command_spec (B M : ℕ) {n : ℕ} (d : MetricMatrix.Matrix n) (history : List (Entry n)) (v : Fin n)
    (i : ℕ) (hi : i < history.length) (hB : 2*M^2+3 < B) (h4 : 4 < B)
    (hlen : 4*history.length < B) (hindex : 2*(n*n)+2 < B) (hn : n < B)
    (hd : ∀ u w, LpInputSize.Height M (d u w : ℚ))
    (hr : ∀ e∈history, LpInputSize.Height M (e.radius : ℚ)) :
    Spec B (fun σ => Context d history v σ ∧ σ.vars "find.i"=i) command
      (fun _ τ => Context d history v τ ∧
        τ.vars "find.ok"=(if d (pair history[i] v).1 (pair history[i] v).2 < history[i].radius then 1 else 0)) 120 := by
  have hMB : M < B := by nlinarith
  let e := history[i]
  let uv := pair e v
  have her := hr e (List.getElem_mem hi)
  have hed := hd uv.1 uv.2
  have hdist : (MetricMatrix.values d)[(edgeIndex n uv).val]'(by simpa using (edgeIndex n uv).isLt)=d uv.1 uv.2 := MetricMatrix.value_at d uv.1 uv.2
  rintro σ ⟨hσ,hiσ⟩
  obtain ⟨σ1,r1,p1⟩ := RamHistoryEntry.command_spec B history i hi h4 hlen hn
    ((num_bound her).trans_lt hMB) ((den_bound her).trans_lt hMB) σ ⟨hσ.2.2.2.2,hiσ⟩
  have h1 := frame r1 hσ (by decide) (by decide)
  obtain ⟨σ2,r2,p2⟩ := address_spec B e v (by omega) hn (by omega) σ1 ⟨h1.1,h1.2.2.1,p1⟩
  have h2 := frame r2 h1 (by decide) (by decide)
  obtain ⟨σ3,r3,p3⟩ := RamArrayScalar.command_spec B "metric.old" "history.edge" "history.distance"
    (MetricMatrix.values d) (edgeIndex n uv).val (by simpa using (edgeIndex n uv).isLt) (by omega)
    (by have := (edgeIndex n uv).isLt; omega)
    (by rw [hdist]; exact (num_bound hed).trans_lt hMB)
    (by rw [hdist]; exact (den_bound hed).trans_lt hMB) (by decide) (by decide) σ2 ⟨h2.2.2.2.1,p2⟩
  have hrad := RamRoundingConstants.storedFrame (r2.seq r3) p1.2.1 (by decide) (by decide)
  obtain ⟨σ4,r4,p4⟩ := RamScalarComparison.command_spec B M e.radius (d uv.1 uv.2) "history.radius" "history.distance"
    hB (num_bound her) (den_bound her) (num_bound hed) (den_bound hed) (by decide) (by decide) (by decide) σ3
    ⟨hrad,by simpa only [hdist] using p3⟩
  obtain ⟨τ,r5,p5⟩ := flag_spec B e.radius (d uv.1 uv.2) (by omega) σ4 p4
  have rr := r1.seq (r2.seq (r3.seq (r4.seq r5)))
  exact ⟨τ,rr,frame rr hσ (by decide) (by decide),p5⟩

end Lax455465Proofs.RamHistoryTest
