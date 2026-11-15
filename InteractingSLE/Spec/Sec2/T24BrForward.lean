import InteractingSLE.Spec.Sec2.T24BrDescent
import InteractingSLE.Spec.Ito.Filtration

/-!
# Theorem 2.4: the forward bridge at a protected curve stopping time

This conditional helper composes the landed Itô theorem with localized filtration
descent. The localizing sequence and adaptedness of the protected means are separate
obligations; no source-facing theorem is replaced by this helper.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'} {π : Ω' → Ω} {𝓕' : Filtration ℝ≥0 mΩ'}

/-- The Itô martingale at a protected curve stopping time is a curve-filtration martingale. -/
theorem martingale_couplingMean_curveFiltration_of_protection
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω' → ℝ} {ζ : Ω' → ℝ≥0∞}
    {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    (hπ : MeasurePreserving π Q P)
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω))
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓕' (fun t ω => W t (π ω))
      (fun i t ω => VL i t (π ω)) (fun i t ω => VR i t (π ω)) B ζ)
    (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation (Filtration.natural η hη) P)
      fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ} (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂Q, (σ (π ω) : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => W s.toNNReal (π ω)) z (σ (π ω)) u) ∧
      δ ≤ (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal (π ω)) (σ (π ω)) z).im ∧
      (σ (π ω) : ℝ) ≤ N ∧ ∀ s ≤ σ (π ω),
        |W s (π ω)| ≤ R ∧ |B s ω| ≤ R ∧
          (∀ i, |VL i s (π ω)| ≤ R) ∧ ∀ i, |VR i s (π ω)| ≤ R)
    (U : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (U ω s))
    (hXa : StronglyAdapted (usualAugmentation (Filtration.natural η hη) P)
      (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω)
        (min t (σ ω) : ℝ≥0) (U ω (min t (σ ω))) z)) :
    Martingale (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω)
      (min t (σ ω) : ℝ≥0) (U ω (min t (σ ω))) z)
      (usualAugmentation (Filtration.natural η hη) P) P := by
  have hσζ : ∀ᵐ ω ∂Q, (σ (π ω) : ℝ≥0∞) ≤ ζ ω := hσp.mono fun _ h => h.1.le
  have hσ' := isStoppingTime_curve_pullback_before hη hπ hE.2.1 hgen hσ hσζ
  obtain ⟨M, hM, he⟩ := Ito.exists_martingale_couplingMean_usualAugmentation hE hκ hz
    hσ' hδ hσp (fun ω t => U (π ω) t) (fun ω s => hu (π ω) s)
  apply martingale_curveFiltration_of_stopped_pullback hη hπ hE.2.1 hgen hσ hσζ hXa
    (Eventually.of_forall fun ω s t hs ht => ?_) hM
    (fun t => he.mono fun ω h => (h t).symm)
  rw [min_eq_right (WithTop.coe_le_coe.1 hs), min_eq_right (WithTop.coe_le_coe.1 ht)]

end InteractingSLE.Sec2.T24Bridge
