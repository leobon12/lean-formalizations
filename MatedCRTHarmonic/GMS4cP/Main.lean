import MatedCRTHarmonic.GMS4cP.IGHalf

/-!
# summary theorems

Source: [18] Lemmas 4.3, 4.6 and (4.16) (`1968–2019`,
`2070–2116`).

* `l43pZeroConeConfigInput_of_area`: the configuration form of measurable [18] Lemma 4.3 on the transfer's disks follows
  from its **area half** alone; the IG half is `l43pZeroConeIGInput_holds` (proved from the bundle).
* `l43p_zeroCone_innerDegreeBoundPolylog_of_area`: the polylogarithmic [18] Lemma 4.6 on the frozen zero-cone
  model from the transfer's (4.16) comparison and the area half.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : NNReal → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Measurable [18] Lemma 4.3 (configuration form) from its area half.** -/
theorem l43pZeroConeConfigInput_of_area
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ρ : ℝ} (hρ : ρ < 1) (w : ℂ)
    (hA : L43PZeroConeAreaInput D hγ ρ w) : L43PZeroConeConfigInput D hγ ρ w :=
  l43pZeroConeConfigInput_of_parts D hγ hρ w hA (l43pZeroConeIGInput_holds D hρ w)

/-- **[18] Lemma 4.6 (polylogarithmic) for the zero-quantum cone** from the transfer's (4.16) comparison and the area
half of measurable Lemma 4.3. -/
theorem l43p_zeroCone_innerDegreeBoundPolylog_of_area
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hcmp : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ,
      Σ p q : ℝ, L46TPhaseLawComparison (l46tObservation ρ w) P P
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ))
          (MoTInput.cellModelOfCoupling D hγ).field)
        (l46tTranslatedField (w + ((1 - ρ) / 2 : ℝ)) hIG₀) T
        (l46tZeroConeCellModel D hγ).field hIG₀ T p q)
    (hA : ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ w ∈ closedBall (0 : ℂ) ρ, L43PZeroConeAreaInput D hγ ρ w) :
    ∃ k : ℕ, InnerDegreeBoundPolylog (l46tZeroConeCellModel D hγ) (2 * k) :=
  l43p_zeroCone_innerDegreeBoundPolylog D hγ hcmp fun ρ hρ w hw =>
    l43pZeroConeConfigInput_of_area D hγ hρ.2 w (hA ρ hρ w hw)

end MatedCRTHarmonic.GMS4cP
