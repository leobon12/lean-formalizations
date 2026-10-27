import MatedCRTHarmonic.GMSCM.L46TGeometry
import MatedCRTHarmonic.GMS4b.L46TTransfer

/-!
# The Cameron–Martin comparison on L46T's observation disk

The source fields are pulled back by `z ↦ z-z₀`, where
`z₀=w+(1-ρ)/2`. The target is the normalized whole-plane GFF version of
the zero-cone on `l46tObservation ρ w`, with the original independent IG
field. The density has some exponent above one.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set TopologicalSpace Metric LQGMetric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

/-- The exact `GMS4c.LocalFieldLawComparison` structure on the observation
region named by L46T, using measurable versions of the frozen cone fields.
The a.e. identities identify those versions with the actual frozen fields. -/
theorem IsMatingOfTreesCoupling.exists_l46tLocalFieldLawComparison
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    let z₀ : ℂ := w + (((1 - ρ) / 2 : ℝ) : ℂ)
    ∃ (hγm h₀m : Ω → DistC),
      Measurable hγm ∧
      (fun ω => coneField (X ω)
        (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω))) =ᵐ[P] hγm ∧
      IsNormalizedWPGFF h₀m P ∧
      (fun ω => restrictTo (GMS4b.l46tObservation ρ w) (coneField (X₀ ω)
        (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω)))) =ᵐ[P]
        (fun ω => restrictTo (GMS4b.l46tObservation ρ w) (h₀m ω)) ∧
      ∃ p q : ℝ, 1 < p ∧
        Nonempty (GMS4c.LocalFieldLawComparison (GMS4b.l46tObservation ρ w) P P
          (GMS4b.l46tTranslatedField z₀ hγm)
          (GMS4b.l46tTranslatedField z₀ hIG₀)
          h₀m hIG₀ p q) := by
  let s : ℝ := 1 - ρ
  let a : ℝ := s / 4
  let b : ℝ := s / 2
  let z₀ : ℂ := w + ((b : ℝ) : ℂ)
  let t : ℂ := -z₀
  let W : Opens ℂ := ⟨ball w a, isOpen_ball⟩
  let V : Opens ℂ := ⟨ball w b, isOpen_ball⟩
  obtain ⟨hK, hCone, hWV, hKW, hKV, hadm, hne, hV₁, hVR, hWunit⟩ :=
    l46t_affine_geometry hρ w hw
  have hres := IsMatingOfTreesCoupling.exists_affineZeroConeComparison hC hγ
    W V t hK hCone hWV hKW hKV hadm hne hV₁ hVR hWunit
  exact hres

/-- The measurable-version adapter changes neither restricted pair law.
The source pushforward is `h ↦ affineComp 1 (-z₀) h`, while the target field
is observed without an affine change. -/
theorem l46t_raw_pair_maps_eq_versions
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {hγm h₀m : Ω → DistC} {ρ : ℝ} (w : ℂ)
    (hγae : (fun ω => coneField (X ω)
      (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω))) =ᵐ[P] hγm)
    (h₀ae : (fun ω => restrictTo (GMS4b.l46tObservation ρ w)
      (coneField (X₀ ω)
        (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω)))) =ᵐ[P]
      fun ω => restrictTo (GMS4b.l46tObservation ρ w) (h₀m ω)) :
    let z₀ : ℂ := w + (((1 - ρ) / 2 : ℝ) : ℂ)
    P.map (GMS4c.localFieldPair (GMS4b.l46tObservation ρ w)
      (GMS4b.l46tTranslatedField z₀ (fun ω => coneField (X ω)
        (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω))))
      (GMS4b.l46tTranslatedField z₀ hIG₀)) =
      P.map (GMS4c.localFieldPair (GMS4b.l46tObservation ρ w)
        (GMS4b.l46tTranslatedField z₀ hγm)
        (GMS4b.l46tTranslatedField z₀ hIG₀)) ∧
    P.map (GMS4c.localFieldPair (GMS4b.l46tObservation ρ w)
      (fun ω => coneField (X₀ ω)
        (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω))) hIG₀) =
      P.map (GMS4c.localFieldPair (GMS4b.l46tObservation ρ w) h₀m hIG₀) := by
  constructor
  · apply Measure.map_congr
    filter_upwards [hγae] with ω hω
    simp only [GMS4c.localFieldPair, GMS4b.l46tTranslatedField]
    rw [hω]
  · apply Measure.map_congr
    filter_upwards [h₀ae] with ω hω
    exact Prod.ext hω rfl

/-- Formula (4.16) for the *raw* frozen pair laws on L46T's disk. The
measurable-version comparison above supplies the density, and the two
pushforward identities remove the versions from the law and moment claims. -/
theorem IsMatingOfTreesCoupling.exists_l46tRawPairDensity
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
    {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) ρ) :
    let W := GMS4b.l46tObservation ρ w
    let z₀ : ℂ := w + (((1 - ρ) / 2 : ℝ) : ℂ)
    let rawγ : Ω → DistC := fun ω => coneField (X ω)
      (coneRadial γ γ (fun s => B s ω) (fun s => B' s ω))
    let raw₀ : Ω → DistC := fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω))
    ∃ p q : ℝ, 1 < p ∧ ∃ D : GMS4c.LocalFieldPair W → ℝ≥0∞,
      Measurable D ∧
      P.map (GMS4c.localFieldPair W raw₀ hIG₀) =
        (P.map (GMS4c.localFieldPair W
          (GMS4b.l46tTranslatedField z₀ rawγ)
          (GMS4b.l46tTranslatedField z₀ hIG₀))).withDensity D ∧
      ∫⁻ x, D x ^ p ∂(P.map (GMS4c.localFieldPair W
        (GMS4b.l46tTranslatedField z₀ rawγ)
        (GMS4b.l46tTranslatedField z₀ hIG₀))) < ⊤ ∧
      p.HolderConjugate q := by
  obtain ⟨hγm, h₀m, hγmeas, hγae, h₀norm, h₀ae,
    p, q, hp, ⟨C⟩⟩ :=
    IsMatingOfTreesCoupling.exists_l46tLocalFieldLawComparison hC hγ hρ w hw
  obtain ⟨hSource, hTarget⟩ := l46t_raw_pair_maps_eq_versions w hγae h₀ae
  refine ⟨p, q, hp, C.density, C.density_measurable, ?_, ?_, C.conjugate⟩
  · rw [hTarget, hSource]
    exact C.law_eq
  · rw [hSource]
    exact C.moment_finite

end MatedCRTHarmonic.GMSCM
