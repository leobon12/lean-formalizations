import MatedCRTHarmonic.GMS4b.L46TTransfer
import MatedCRTHarmonic.GMS4b.L46TModel
import MatedCRTHarmonic.GMS4b.L46TZeroInputs
import MatedCRTHarmonic.GMCUpper.AreaRecord
import MatedCRTHarmonic.GMS4.Prop48

/-!
# Measurable-version comparison for the raw zero-cone cell model

The local comparison compares measurable field representatives. Their almost-sure identities
transport the joint density and local event reconstruction to the raw coupling
without changing its inner-degree or Proposition 4.5 event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.MatedCRT

/-- One global measurable representative of the frozen zero-cone field. -/
def l46tZeroConeFieldVersion
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm) :
    Ω → LQGMetric.DistC :=
  (GMS4.aemeasurable_prop48ZeroConeField D).mk
    (fun ω => coneField (X₀ ω)
      (coneRadial γ 0 (fun s => B₀ s ω) (fun s => B₀' s ω)))

theorem l46tZeroConeFieldVersion_measurable
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm) :
    Measurable (l46tZeroConeFieldVersion D) :=
  (GMS4.aemeasurable_prop48ZeroConeField D).measurable_mk

theorem l46tZeroConeFieldVersion_ae_eq_raw
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    (l46tZeroConeCellModel D hγ).field =ᵐ[P] l46tZeroConeFieldVersion D := by
  simpa only [l46tZeroConeCellModel, l46tZeroConeFieldVersion] using
    (GMS4.aemeasurable_prop48ZeroConeField D).ae_eq_mk

/-- A measurable-version producer supplies both named raw transfer inputs.
The two field versions and two phase versions are identified with the actual
frozen data almost surely. -/
def l46t_zeroCone_rawInputs_of_versions
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field}
    {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hS hT : Ω → LQGMetric.DistC) (uS uT : Ω → ℝ)
    (hSae : (MoTInput.cellModelOfCoupling D hγ).field =ᵐ[P] hS)
    (hTae : (l46tZeroConeCellModel D hγ).field =ᵐ[P] hT)
    (huSae : T =ᵐ[P] uS) (huTae : T =ᵐ[P] uT)
    (hcmp : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      Σ p q : ℝ, L46TPhaseLawComparison (l46tObservation ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS
        hT hIG₀ uT p q)
    (hlocal : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstruction (l46tObservation ρ w) (l46tLocalRegion ρ w)
        P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS
        hT hIG₀ uT
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
        (l46tZeroConeCellModel D hγ).curve
        (ball w ((1 - ρ) / 16)) ε k ζ) :
    (∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      Σ p q : ℝ, L46TPhaseLawComparison (l46tObservation ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
          (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeCellModel D hγ).field hIG₀ T p q) ×
    (∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      ∀ (k : ℕ) (ζ ε : ℝ), ε ∈ Ioo (0 : ℝ) 1 →
      L46TLocalReconstruction (l46tObservation ρ w) (l46tLocalRegion ρ w)
        P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
          (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeCellModel D hγ).field hIG₀ T
        (fun ω => l46tTranslateCurve (w + ((1 - ρ) / 2 : ℝ)) (η ω))
        (l46tZeroConeCellModel D hγ).curve
        (ball w ((1 - ρ) / 16)) ε k ζ) := by
  have hs (ρ : ℝ) (w : ℂ) :
      l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
          (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T =ᵐ[P]
      l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hS)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) uS := by
    apply l46t_localFieldPhase_congr
    · filter_upwards [hSae] with ω hω
      simp [l46tTranslatedField, hω]
    · exact Filter.EventuallyEq.rfl
    · exact huSae
  have ht (ρ : ℝ) (w : ℂ) :
      l46tLocalFieldPhase (l46tObservation ρ w)
        (l46tZeroConeCellModel D hγ).field hIG₀ T =ᵐ[P]
      l46tLocalFieldPhase (l46tObservation ρ w) hT hIG₀ uT :=
    l46t_localFieldPhase_congr _ hTae Filter.EventuallyEq.rfl huTae
  constructor
  · intro ρ hρ w hw
    obtain ⟨p, q, hc⟩ := hcmp ρ hρ w hw
    exact ⟨p, q, l46t_phaseComparison_congr hc (hs ρ w) (ht ρ w)⟩
  · intro ρ hρ w hw k ζ ε hε
    exact l46t_localReconstruction_congr (hlocal ρ hρ w hw k ζ ε hε)
      (hs ρ w) (ht ρ w)

end MatedCRTHarmonic.GMS4b
