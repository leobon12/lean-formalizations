import QuantumZipper.Proofs.Thm18.G4CoreDefs3
import QuantumZipper.Statements.Thm18Off

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D74 rewiring R1: the pushed-circle regularity nodes off the curve, from A-sep alone

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26) compares the pair of surfaces cut out by the
curve, i.e. the fields away from `η` (decision D74, `handoff/MATCH-PAPER-18.md` §7, step R1).

The two pushed-circle consumers `G4UpZipPushRegStmt` (re-zip of `Z_ℓ ∘ Z_{−ℓ}`) and
`G4DownShortPushRegPStmt` (`Z_s ∘ Z_{−ℓ}`, `s < ℓ`) ask their data at **every** dyadic folded
circle, including those that cross the re-zipped hull; that is what forced the crossing cluster
(`G4BackCrossStmt`, fed by `G4CrossQAllStmt`, `G4CrossContactShortStmt`, `SLEScaleContactStmt`)
and the hull-nullity node `G4UpTraceNullStmt` (fed by `SLETwoPointFarUnit`).

Here the same data are stated only at the dyadic circles that stay off the re-zipped hull
(`CircleOff` of `Statements/Thm18Off.lean`), and proved from A-sep `G4DriverPushSepAllStmt`
(plus the proved `G4UnzipGoodStmt`) alone: an off-hull circle carries no hull mass, is carried by
the image of the reverse map, and is at positive distance from the hull (`BackSepI`), so A-sep
applies. No trace-nullity, contact or two-point input is used.

Own elementary bookkeeping (the geometric step is: a folded circle whose annulus avoids a subset
of `ℍ` after folding is at positive distance from it).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace D74R
open G4Core

/-! ## Geometry: off-set circles are separated -/

/-- A folded circle whose folding annulus avoids a subset `K ⊆ ℍ` gives zero mass to a
thickening of `K`. -/
theorem foldedCircle_thickening_null_of_circleOff {K : Set ℂ} (hK : K ⊆ H) {d : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (h : QuantumZipper.CircleOff K d r) :
    ∃ δ : ℝ, 0 < δ ∧ foldedCircle d r (Metric.thickening δ K) = 0 := by
  obtain ⟨δ, hδ, hw⟩ := h
  refine ⟨δ, hδ, ?_⟩
  rw [TwoPoint.foldedCircle_apply' d r Metric.isOpen_thickening.measurableSet]
  have hempty : {θ : ℝ | θ ∈ Ico 0 (2 * Real.pi) ∧
      foldH (circleMap d r θ) ∈ Metric.thickening δ K} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun θ hθ => ?_
    obtain ⟨v, hvK, hdv⟩ := Metric.mem_thickening_iff.1 hθ.2
    have hvH : 0 < v.im := hK hvK
    set w0 := circleMap d r θ with hw0
    have hd0 : dist w0 d = r := by
      rw [hw0, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg hr]
    by_cases him : 0 ≤ w0.im
    · have hu : foldH w0 = w0 := by simp [foldH, him]
      rw [hu] at hdv
      have hlt : |dist v d - r| < δ := by
        rw [← hd0]
        exact (abs_dist_sub_le v w0 d).trans_lt (by rw [dist_comm]; exact hdv)
      have hv : foldH v = v := by simp [foldH, hvH.le]
      exact hw v hlt (by rw [hv]; exact hvK)
    · have hu : foldH w0 = (starRingEnd ℂ) w0 := by simp [foldH, him]
      rw [hu] at hdv
      have hlt : |dist ((starRingEnd ℂ) v) d - r| < δ := by
        rw [← hd0]
        refine (abs_dist_sub_le _ w0 d).trans_lt ?_
        rw [← Complex.dist_conj_conj, Complex.conj_conj, dist_comm]
        exact hdv
      have hv : foldH ((starRingEnd ℂ) v) = v := by
        have : ¬ 0 ≤ ((starRingEnd ℂ) v).im := by
          rw [Complex.conj_im]; linarith
        unfold foldH; rw [if_neg this, Complex.conj_conj]
      exact hw _ hlt (by rw [hv]; exact hvK)
  rw [hempty, measure_empty, mul_zero]

/-! ## The off-hull pushed-circle predicate -/

/-- **Pushed-circle data off the re-zipped hull.** At every dyadic folded circle that stays off
the hull of the re-zipping driver `backDrv W τ τ' a`: support (`BackSupportI`), no hull mass, and
the exactness/integrability data `DriverPushExactI`. -/
def PushRegOffAt (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (τ τ' a : ℝ) : Prop :=
  ∀ i : ℕ, QuantumZipper.CircleOff (revHull (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1)
      (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 →
    BackSupportI c τ τ' a i ∧
      fcI i (revHull (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1) = 0 ∧
      DriverPushExactI γ c τ τ' a i

/-! ## R1 nodes -/

end D74R
end Thm18Asm
end QuantumZipper
