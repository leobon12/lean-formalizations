import MatedCRTHarmonic.GMS4c.LocalConfiguration
import MatedCRTHarmonic.GMS4.Prop410

/-!
# The local field-law transfer in [18] Lemma 4.6

The source's (4.16) compares the pair of field restrictions to a disk under the
gamma-cone law and the whole-plane/zero-cone law. `LocalFieldLawComparison` is the
single named Cameron–Martin comparison input: the target law has a density with
an `L^p` moment. Its producer is GMSCM, not DMS Lemma A.10.
The Hölder step reuses `GMS4.withDensity_event_le_holder`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4c

/-- The two field restrictions used by [18] (4.16), on a common open disk. -/
abbrev LocalFieldPair (V : TopologicalSpace.Opens ℂ) : Type := DistOn V × DistOn V

/-- The observable `(h|_V, h^IG|_V)`. -/
def localFieldPair {Ω : Type*} (V : TopologicalSpace.Opens ℂ)
    (h hIG : Ω → DistC) (ω : Ω) : LocalFieldPair V :=
  (restrictTo V (h ω), restrictTo V (hIG ω))

theorem measurable_localFieldPair {Ω : Type*} [MeasurableSpace Ω]
    (V : TopologicalSpace.Opens ℂ) {h hIG : Ω → DistC}
    (hh : Measurable h) (hhIG : Measurable hIG) :
    Measurable (localFieldPair V h hIG) :=
  ((measurable_restrictTo V).comp hh).prodMk ((measurable_restrictTo V).comp hhIG)

/-- The local Radon–Nikodym comparison required by [18] (4.16), for the specified
pair of restricted fields under the gamma-cone and target laws. Producer: GMSCM
(Cameron–Martin), together with independence of the IG field. This does not quantify over arbitrary
unrelated `CellModel`s. -/
structure LocalFieldLawComparison {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V : TopologicalSpace.Opens ℂ)
    (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → DistC) (h₀ hIG₀ : Ω₀ → DistC)
    (p q : ℝ) where
  gamma_measurable : Measurable (localFieldPair V hγ hIGγ)
  target_measurable : Measurable (localFieldPair V h₀ hIG₀)
  density : LocalFieldPair V → ℝ≥0∞
  density_measurable : Measurable density
  law_eq : P₀.map (localFieldPair V h₀ hIG₀) =
    (Pγ.map (localFieldPair V hγ hIGγ)).withDensity density
  moment_finite : ∫⁻ x, density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ)) < ⊤
  conjugate : p.HolderConjugate q

/-- Measurable local field events transfer from the gamma-cone law to the
whole-plane/zero-cone law with the Hölder exponent of (4.16). -/
theorem local_badEvent_le_holder {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC}
    {p q : ℝ} (hcmp : LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q)
    {A : Set (LocalFieldPair V)} (hA : MeasurableSet A) :
    P₀ ((localFieldPair V h₀ hIG₀) ⁻¹' A) ≤
      (∫⁻ x, hcmp.density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ))) ^ (1 / p) *
        (Pγ ((localFieldPair V hγ hIGγ) ⁻¹' A)) ^ (1 / q) := by
  rw [← Measure.map_apply hcmp.target_measurable hA,
    ← Measure.map_apply hcmp.gamma_measurable hA, hcmp.law_eq]
  exact GMS4.withDensity_event_le_holder
    (Pγ.map (localFieldPair V hγ hIGγ)) hcmp.density
    hcmp.density_measurable.aemeasurable hA hcmp.conjugate

/-- Formula (4.16) with the exponent written as `1 - 1/p`. -/
theorem local_badEvent_le_holder_one_sub {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC}
    {p q : ℝ} (hcmp : LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q)
    {A : Set (LocalFieldPair V)} (hA : MeasurableSet A) :
    P₀ ((localFieldPair V h₀ hIG₀) ⁻¹' A) ≤
      (∫⁻ x, hcmp.density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ))) ^ (1 / p) *
        (Pγ ((localFieldPair V hγ hIGγ) ⁻¹' A)) ^ (1 - 1 / p) := by
  convert local_badEvent_le_holder hcmp hA using 1
  rw [show 1 / q = 1 - 1 / p by
    simpa only [one_div] using hcmp.conjugate.one_sub_inv.symm]

/-- Any gamma-cone bound `δ` for the same local field event transfers with exponent `1/q`. -/
theorem local_badEvent_le_of_gamma_bound {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC}
    {p q : ℝ} (hcmp : LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q)
    {A : Set (LocalFieldPair V)} (hA : MeasurableSet A) {δ : ℝ≥0∞}
    (hγbad : Pγ ((localFieldPair V hγ hIGγ) ⁻¹' A) ≤ δ) :
    P₀ ((localFieldPair V h₀ hIG₀) ⁻¹' A) ≤
      (∫⁻ x, hcmp.density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ))) ^ (1 / p) *
        δ ^ (1 / q) := by
  refine (local_badEvent_le_holder hcmp hA).trans ?_
  gcongr
  exact hcmp.conjugate.symm.one_div_nonneg

/-- The Cameron–Martin moment bound makes the Hölder prefactor finite. -/
theorem local_holder_constant_finite {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC}
    {p q : ℝ} (hcmp : LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q) :
    (∫⁻ x, hcmp.density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ))) ^ (1 / p) < ⊤ := by
  exact ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr hcmp.conjugate.pos.le) hcmp.moment_finite.ne

/-- Apply (4.16) to a bad event of a reconstructed local configuration. The
configuration may use a smaller open set `U` than the field observation disk `V`:
frozen S7 reconstructs excursions into `U` from the IG field on a thickening of `U`.
The measurable reconstruction and the bad-event set are the two conclusions
still required from the concrete proof of [18] Lemma 4.3. -/
theorem local_configuration_badEvent_le_holder {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC}
    {p q : ℝ} (hcmp : LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q)
    (U : TopologicalSpace.Opens ℂ) (reconstruct : LocalFieldPair V → LocalConfiguration U)
    (hreconstruct : Measurable reconstruct) (bad : Set (LocalConfiguration U))
    (hbad : MeasurableSet bad) :
    P₀ {ω | reconstruct (localFieldPair V h₀ hIG₀ ω) ∈ bad} ≤
      (∫⁻ x, hcmp.density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ))) ^ (1 / p) *
        (Pγ {ω | reconstruct (localFieldPair V hγ hIGγ ω) ∈ bad}) ^ (1 / q) := by
  change P₀ ((localFieldPair V h₀ hIG₀) ⁻¹' (reconstruct ⁻¹' bad)) ≤
    (∫⁻ x, hcmp.density x ^ p ∂(Pγ.map (localFieldPair V hγ hIGγ))) ^ (1 / p) *
      (Pγ ((localFieldPair V hγ hIGγ) ⁻¹' (reconstruct ⁻¹' bad))) ^ (1 / q)
  exact local_badEvent_le_holder hcmp (hreconstruct hbad)

end MatedCRTHarmonic.GMS4c
