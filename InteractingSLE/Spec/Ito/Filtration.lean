import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Ito.Martingale
import InteractingSLE.Spec.Ito.Bracket
import InteractingSLE.Spec.Ito.TwoPoint
import InteractingSLE.Spec.Ito.LogMap

/-!
# (3.15)–(3.17) in the usual augmentation

Packet PROVE-T11-ITO2 (Specification §3.3 L496–L513). The results of PROVE-T11-ITO (`exists_martingale_coordObs`,
`exists_martingale_couplingMean` (**(3.15)**), `exists_martingale_couplingMean_sq`,
`exists_martingale_couplingMean_mul_B`, `exists_martingale_couplingMean_mul_add_greenH` (**(3.17)**),
`exists_martingale_log_fwdMap`) hold for protected stopping times of `nullAugmented 𝓕 P` and give martingales of that
filtration. Here they are restated for the source's filtration, the usual augmentation `usualAugmentation 𝓕 P`
(right-continuous and complete): protected stopping times of `usualAugmentation 𝓕 P`, martingales of
`usualAugmentation 𝓕 P`. The proofs apply the landed results to the evolution on the usual augmentation
(`isIntegratedSLEEvolution_usualAugmentation`), whose null augmentation is itself (`nullAugmented_usualAugmentation`).

Every stopping time of the frozen `drivingFiltration` is a stopping time of `usualAugmentation 𝓕 P`
(`isStoppingTime_usualAugmentation_of_drivingFiltration`), so these results apply to the stopping times of Theorem 1.1.
The protection hypotheses are discharged by the localizing sequences of `Spec/Ito/Exhaust.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

theorem isStoppingTime_nullAugmented_usualAugmentation {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) τ) :
    IsStoppingTime (nullAugmented (usualAugmentation 𝓕 P) P) τ := by
  rwa [nullAugmented_usualAugmentation]

theorem martingale_usualAugmentation_of_nullAugmented {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M (nullAugmented (usualAugmentation 𝓕 P) P) P) :
    Martingale M (usualAugmentation 𝓕 P) P := by
  rwa [nullAugmented_usualAugmentation] at hM

/-- **Itô's formula for the Loewner coordinates** (`exists_martingale_coordObs`) at a protected stopping time of the
usual augmentation, with a martingale of the usual augmentation. -/
theorem exists_martingale_coordObs_usualAugmentation
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {z : ℂ} (hz : 0 < z.im)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    {δ R N : ℝ} (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    {Φ : Coord nL nR × ℝ → ℝ} (hΦ : ContDiffOn ℝ 3 Φ (obsRegion κ)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = Φ (coordProc κ z W VL VR B (min t (σ ω)) ω, B (min t (σ ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen Φ
          (coordProc κ z W VL VR B s.toNNReal ω, B s.toNNReal ω)
          (densityAt z ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s) := by
  obtain ⟨M, hM, h⟩ := exists_martingale_coordObs (isIntegratedSLEEvolution_usualAugmentation hE) hz
    (isStoppingTime_nullAugmented_usualAugmentation hσ) hδ hσp hΦ
  exact ⟨M, martingale_usualAugmentation_of_nullAugmented hM, h⟩

/-- **(3.15)** in the usual augmentation: at a protected stopping time `σ` of `usualAugmentation 𝓕 P`, the mean
`𝔥_{t∧σ}(z)` agrees almost surely, at every time, with a martingale of `usualAugmentation 𝓕 P`. -/
theorem exists_martingale_couplingMean_usualAugmentation
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
        (u ω (min t (σ ω))) z := by
  obtain ⟨M, hM, h⟩ := exists_martingale_couplingMean (isIntegratedSLEEvolution_usualAugmentation hE) hκ hz
    (isStoppingTime_nullAugmented_usualAugmentation hσ) hδ hσp u hu
  exact ⟨M, martingale_usualAugmentation_of_nullAugmented hM, h⟩

/-- `d⟨𝔥(z)⟩_t = Im(2/f_t(z))² dt` in the usual augmentation (`exists_martingale_couplingMean_sq`). -/
theorem exists_martingale_couplingMean_sq_usualAugmentation
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) z ^ 2 -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          ((2 / QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) ^ 2 := by
  obtain ⟨M, hM, h⟩ := exists_martingale_couplingMean_sq (isIntegratedSLEEvolution_usualAugmentation hE) hκ
    hz (isStoppingTime_nullAugmented_usualAugmentation hσ) hδ hσp u hu
  exact ⟨M, martingale_usualAugmentation_of_nullAugmented hM, h⟩

/-- `d⟨𝔥(z), B⟩_t = Im(2/f_t(z)) dt` in the usual augmentation (`exists_martingale_couplingMean_mul_B`). -/
theorem exists_martingale_couplingMean_mul_B_usualAugmentation
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) z * B (min t (σ ω)) ω -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          (2 / QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im := by
  obtain ⟨M, hM, h⟩ := exists_martingale_couplingMean_mul_B (isIntegratedSLEEvolution_usualAugmentation hE)
    hκ hz (isStoppingTime_nullAugmented_usualAugmentation hσ) hδ hσp u hu
  exact ⟨M, martingale_usualAugmentation_of_nullAugmented hM, h⟩

/-- **(3.17)** in the usual augmentation (`exists_martingale_couplingMean_mul_add_greenH`). -/
theorem exists_martingale_couplingMean_mul_add_greenH_usualAugmentation
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {y z : ℂ}
    (hy : 0 < y.im) (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) y (σ ω) u) ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) y).im ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      (∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) ∧
      ∀ s ≤ σ ω, ε ≤ ‖QuantumZipper.fwdMap (rpath (W · ω)) s y -
        QuantumZipper.fwdMap (rpath (W · ω)) s z‖)
    (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
          (u ω (min t (σ ω))) y *
          couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0)
            (u ω (min t (σ ω))) z +
        QuantumZipper.greenH
          (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) y)
          (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z) := by
  obtain ⟨M, hM, h⟩ := exists_martingale_couplingMean_mul_add_greenH
    (isIntegratedSLEEvolution_usualAugmentation hE) hκ hy hz
    (isStoppingTime_nullAugmented_usualAugmentation hσ) hδ hε hσp u hu
  exact ⟨M, martingale_usualAugmentation_of_nullAugmented hM, h⟩

/-- **The Itô derivative of `log f_t(z)`** in the usual augmentation (`exists_martingale_log_fwdMap`). -/
theorem exists_martingale_log_fwdMap_usualAugmentation
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) {z : ℂ}
    (hz : 0 < z.im) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0)) {δ R N : ℝ}
    (hδ : 0 < δ)
    (hσp : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
      (∃ u, QuantumZipper.IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
      δ ≤ (QuantumZipper.fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
      ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R) :
    (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = Real.log ‖QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z‖ -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          ((4 - κ) / (2 * QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
            (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
              QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).re) ∧
    (∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = Complex.arg (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) (min t (σ ω) : ℝ≥0) z) -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
          ((4 - κ) / (2 * QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z ^ 2) -
            (driftAt ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s : ℂ) /
              QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im) := by
  obtain ⟨⟨M₁, hM₁, h₁⟩, ⟨M₂, hM₂, h₂⟩⟩ := exists_martingale_log_fwdMap
    (isIntegratedSLEEvolution_usualAugmentation hE) hκ hz
    (isStoppingTime_nullAugmented_usualAugmentation hσ) hδ hσp
  exact ⟨⟨M₁, martingale_usualAugmentation_of_nullAugmented hM₁, h₁⟩,
    ⟨M₂, martingale_usualAugmentation_of_nullAugmented hM₂, h₂⟩⟩

end Ito

end InteractingSLE
