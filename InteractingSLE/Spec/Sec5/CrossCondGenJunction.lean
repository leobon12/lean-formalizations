/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenEntrance
import InteractingSLE.Spec.Sec5.CrossCondThetaImg

/-!
# The contact-word entrance with the general-angle junction weights

Packet PROVE-CROSSCOND-GEN. Specialize the contact-word converse to the actual angle-dependent
junction weights already derived from the exposed counterflow-side heights in `CrossCondThetaImg`.
All original labels survive in `jwL` and `jwR`, even after their force coordinates merge.
The image-mean martingale property and the construction of the contact image word remain inputs.
At `θ = π/2` the weights are exactly R57's corrected `cL6`, `cR6`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu.ImgDrv MartChar Sec7.Aux117 Word49 Theta

/-- Adding the left junction retains every original weight. -/
theorem jwL_original {n : ℕ} (θ κ : ℝ) (ρ : Fin n → ℝ) (i : Fin n) :
    jwL (cLT θ) κ ρ i.castSucc = ρ i := Fin.snoc_castSucc _ _ _

/-- Adding the right junction retains every original weight. -/
theorem jwR_original {n : ℕ} (θ κ : ℝ) (ρ : Fin n → ℝ) (i : Fin n) :
    jwR (cRT θ) κ ρ i.castSucc = ρ i := Fin.snoc_castSucc _ _ _

/-- The left far total depends on the angle, including after mergers of original labels. -/
theorem sum_jwL {n : ℕ} (θ κ : ℝ) (ρ : Fin n → ℝ) :
    ∑ i, jwL (cLT θ) κ ρ i = (3 / 2 + θ / π) * (κ / 2 - 2) := by
  rw [Fin.sum_univ_castSucc]
  simp only [jwL, Fin.snoc_castSucc, Fin.snoc_last, cLT]
  ring

/-- The right far total has the reflected angle dependence. -/
theorem sum_jwR {n : ℕ} (θ κ : ℝ) (ρ : Fin n → ℝ) :
    ∑ i, jwR (cRT θ) κ ρ i = (3 / 2 - θ / π) * (κ / 2 - 2) := by
  rw [Fin.sum_univ_castSucc]
  simp only [jwR, Fin.snoc_castSucc, Fin.snoc_last, cRT]
  ring

/-- The general contact-word entrance with the source's junction weights.
`hImageMartingales` is the precise analytic input still needed from cross-conditioning. -/
theorem exists_isWordEntrance_junctions {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {nL nR : ℕ} {κ θ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓖 : Filtration ℝ≥0 mΩ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0} {σ : ℕ → Ω → ℝ≥0}
    (hκ : 0 < κ) (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓖 0] s)
    (hK : IsContactWord W VL VR T) (hWa : StronglyAdapted 𝓖 W)
    (hVLa : ∀ i, StronglyAdapted 𝓖 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓖 (VR j))
    (hσ : ∀ n, IsStoppingTime 𝓖 fun ω => (σ n ω : WithTop ℝ≥0))
    (hσm : ∀ ω, Monotone (σ · ω)) (hσT : ∀ n ω, (σ n ω : WithTop ℝ≥0) < T ω)
    (hσlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) < T ω → ∃ n, u ≤ σ n ω)
    (hImageMartingales : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) W VL VR z)) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → Ω × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration 𝓖 𝓦) Bi (P.prod P₀) ∧
      (∀ p, Continuous fun t => Bi t p) ∧
      ∀ᵐ p ∂(P.prod P₀),
        IsWordEntrance κ (fun i => VL i 0 p.1) (fun j => VR j 0 p.1)
          (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
          (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1) (Bi · p)
          (min (T p.1 : ℝ≥0∞) (thresholdTime (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
            (W · p.1) (fun i t => VL i t p.1) (fun j t => VR j t p.1))) :=
  hK.exists_isWordEntrance_threshold hκ hnull hWa hVLa hVRa hσ hσm hσT hσlim hImageMartingales

end InteractingSLE.Sec5.CrossCond.Gen
