import HigherDimLQGContinuity.MomentsW1.ScaleBound
import HigherDimLQGContinuity.MomentsW1.BadScaleMoment
import HigherDimLQGContinuity.MomentsW1.CoarseMoment

/-! Per-edge and segment costs from the fine statuses and coarse envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set HigherDimLFPP HigherDimLFPP.Perc
open scoped ENNReal
open HigherDimLFPP.DGZ (latPt obox cbox SiteClosed lfppDistOn_le_of_not_siteClosed)
open HigherDimLQGMetric.DGZ

variable {d : ℕ}

theorem wnGood_edge_cost {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ξ R Q CZ : ℝ} (hξ : 0 ≤ ξ)
    {q : ℝ≥0∞} {k n : ℕ} {ω : Ω}
    (hfinite : wnZRext (d := d) R Q CZ H ω ≠ ⊤)
    {z z' : Zd d}
    (hgood : z ∈ wnGood P H ξ R q k n ω)
    (hreg : z ∈ wnRegion R k)
    (hbox : obox (latPt ((2 : ℝ)⁻¹ ^ k) z) (2*(2 : ℝ)⁻¹ ^ k) ⊆
      cbox (0 : Rd d) (R+5)) (hadj : LAdj z z') :
    lfppDistOn ξ (fun u => H n u ω)
      (obox (latPt ((2 : ℝ)⁻¹ ^ k) z) (2*(2 : ℝ)⁻¹ ^ k))
      (latPt ((2 : ℝ)⁻¹ ^ k) z) (latPt ((2 : ℝ)⁻¹ ^ k) z') ≤
      Real.exp (ξ*(Q*k*Real.log 2+CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) *
        ((2 : ℝ)⁻¹ ^ k * aQ P H ξ (n-k) q) := by
  let V : Set (Rd d) := obox (latPt ((2 : ℝ)⁻¹ ^ k) z) (2*(2 : ℝ)⁻¹ ^ k)
  let B : ℝ := Q*k*Real.log 2+CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω
  have hcont : ∀ m ω, Continuous (fun u => H m u ω) := fun m => (hH.band m).continuous
  have hφ : Continuous (fun u => H n u ω) := hcont n ω
  have hψ : Continuous (fun u => H n u ω-H k u ω) := hφ.sub (hcont k ω)
  have hweight : ∀ u ∈ V,
      Real.exp (ξ*H n u ω) ≤ Real.exp (ξ*B)*Real.exp (ξ*(H n u ω-H k u ω)) := by
    intro u hu
    have hfield := wnZR_bound hcont R Q CZ ω hfinite k u (hbox hu)
    have hξfield := mul_le_mul_of_nonneg_left hfield hξ
    rw [← Real.exp_add, Real.exp_le_exp]
    dsimp [B]
    nlinarith
  have hcmp := lfppDistOn_le_mul_of_exp_le hφ hψ
    (Real.exp_pos _).le hweight
    (V := V) (x := latPt ((2 : ℝ)⁻¹ ^ k) z)
    (y := latPt ((2 : ℝ)⁻¹ ^ k) z')
  have hsite : ¬ SiteClosed ξ (fun u => H n u ω-H k u ω)
      ((2 : ℝ)⁻¹ ^ k) (aQ P H ξ (n-k) q) (R+3) z := by
    intro hs
    apply hgood
    exact ⟨hreg, hs⟩
  have hreg' : ∀ i, |latPt ((2 : ℝ)⁻¹ ^ k) z i| ≤ R+3 :=
    fun i => (hreg i).le
  have hfine := lfppDistOn_le_of_not_siteClosed hsite hreg' hadj
  exact hcmp.trans (mul_le_mul_of_nonneg_left hfine (Real.exp_pos _).le)

theorem wnSeg_cost {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ξ R Q CZ : ℝ} (hξ : 0 ≤ ξ)
    {n : ℕ} {ω : Ω} (hfinite : wnZRext (d := d) R Q CZ H ω ≠ ⊤)
    {u : Rd d} (hu : u ∈ cbox (0 : Rd d) (R+5)) :
    Real.exp (ξ*H n u ω) ≤
      Real.exp (ξ*(Q*n*Real.log 2+CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) := by
  have hcont : ∀ m ω, Continuous (fun z => H m z ω) := fun m => (hH.band m).continuous
  have hfield := wnZR_bound hcont R Q CZ ω hfinite n u hu
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hfield hξ)

theorem wnBox_subset_coarse {R ρ : ℝ} (_hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {w : Rd d} (hw : w ∈ cbox (0 : Rd d) (R+1)) :
    obox w ρ ⊆ cbox (0 : Rd d) (R+5) := by
  intro u hu i
  have hwi : |w i| ≤ R+1 := by simpa using hw i
  have hui := hu i
  have htri := abs_add_le (u i-w i) (w i)
  have heq : (u i-w i)+w i = u i := by ring
  rw [heq] at htri
  simpa using (show |u i| ≤ R+5 by linarith)

theorem wnBox_region {R ρ : ℝ} (_hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {w : Rd d} (hw : w ∈ cbox (0 : Rd d) (R+1))
    {k : ℕ} {z : Zd d}
    (hcell : obox (latPt ((2 : ℝ)⁻¹ ^ k) z) (2*(2 : ℝ)⁻¹ ^ k) ⊆ obox w ρ) :
    z ∈ wnRegion R k := by
  have hcenter : latPt ((2 : ℝ)⁻¹ ^ k) z ∈ obox w ρ :=
    hcell (HigherDimLFPP.DGZ.mem_obox_self _ (by positivity))
  intro i
  have hwi : |w i| ≤ R+1 := by simpa using hw i
  have hci := hcenter i
  have htri := abs_add_le (latPt ((2 : ℝ)⁻¹ ^ k) z i-w i) (w i)
  have heq : (latPt ((2 : ℝ)⁻¹ ^ k) z i-w i)+w i =
      latPt ((2 : ℝ)⁻¹ ^ k) z i := by ring
  rw [heq] at htri
  linarith

/-- Coarse-weighted cost of an open fine edge. -/
def wnEdgeCost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ℕ → Rd d → Ω → ℝ) (ξ R Q CZ : ℝ) (q : ℝ≥0∞)
    (n : ℕ) (ω : Ω) (k : ℕ) : ℝ :=
  Real.exp (ξ*(Q*k*Real.log 2+CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω)) *
    ((2 : ℝ)⁻¹ ^ k * aQ P H ξ (n-k) q)

/-- Coarse-weighted terminal segment weight. -/
def wnSegmentCost {Ω : Type*} [MeasurableSpace Ω]
    (H : ℕ → Rd d → Ω → ℝ) (ξ R Q CZ : ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (ξ*(Q*n*Real.log 2+CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω))

end HigherDimLQGContinuity
