import MatedCRTHarmonic.GMS4.Prop210Transfer
import MatedCRTHarmonic.GMS4.Probability
import MatedCRTHarmonic.GMS4.CellGraphInterface

/-!
# Fixed-scale probabilistic adapter for [18] Proposition 2.10

The deterministic implication `(4.20)` is proved in `Prop210Transfer`. This file applies it
outcome by outcome in a `CellFamily.RandomCellFamily`, and transfers an outer-measure estimate for
The localized bad event to G3's exact `Prop210Bound` bad event. No measurability of either event
is needed.

The current `GMSLemma27.CellModel` deliberately contains only the field, area measure, curve,
and curve-segment cells. Its source-faithful missing graph bridge is the named
`.CellModelGraphCoupling` from `CellGraphInterface.lean`, whose Brownian law comes from frozen
`IsCellCoupling` and whose mesh identifications are almost sure. This file contains no
Proposition 2.10 estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.GMS3

/-- The fixed-scale domain/function assumptions in [18] Proposition 2.10
. The paper's notation
`B_r(partial D)` is represented by `Metric.thickening r (frontier D)`. -/
def Prop210Admissible (epsilon rho C beta : ℝ) (D : Set ℂ) (f : ℂ → ℝ) : Prop :=
  0 < epsilon ∧ epsilon < 1 ∧ 0 < rho ∧ rho < 1 ∧ 1 < C ∧ 0 < beta ∧
    IsOpen D ∧ IsConnected D ∧ D ⊆ Metric.ball 0 rho ∧
    (∀ r ∈ Set.Ioo (0 : ℝ) 1,
      volume (Metric.thickening r (frontier D)) ≤ ENNReal.ofReal (C * r)) ∧
    (∀ z ∈ D, 0 ≤ f z ∧ f z ≤ C * epsilon ^ (-beta)) ∧
    ∀ z ∈ D, ∀ w ∈ D,
      |f z - f w| ≤ C * epsilon ^ (-beta) * dist z w

/-- The localized integral event for one scale and one fixed test pair `(D,f)`. -/
def LocalizedIntegralGood (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ)
    (f : ℂ → ℝ) (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞) (A eta : ℝ) : Set F.Ω :=
  {omega | (∫⁻ z in D, ENNReal.ofReal (f z) * uStar k omega z) ≤
    ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal eta}

/-- G3's exact Proposition 2.10 event for one scale and one fixed test pair `(D,f)`. -/
def Prop210Good (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ)
    (f : ℂ → ℝ) (A eta : ℝ) : Set F.Ω :=
  {omega | Prop210Bound (F.H k omega) D f A eta}

/-- Failure of the localized integral estimate. -/
def LocalizedIntegralBad (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ)
    (f : ℂ → ℝ) (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞) (A eta : ℝ) : Set F.Ω :=
  (LocalizedIntegralGood F k D f uStar A eta)ᶜ

/-- Failure of G3's exact Proposition 2.10 estimate. -/
def Prop210Bad (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ)
    (f : ℂ → ℝ) (A eta : ℝ) : Set F.Ω :=
  (Prop210Good F k D f A eta)ᶜ

/-- Outcome-wise `(4.20)`: the localized good event implies G3's exact good event, with the
factor `2` visible in both constants. -/
theorem localizedIntegralGood_subset_prop210Good
    (F : CellFamily.RandomCellFamily) (k : ℕ) {D : Set ℂ} (hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞) {A eta : ℝ}
    (hlocal : ∀ omega z, z ∈ D → uDens (F.H k omega) z ≤ 2 * uStar k omega z) :
    LocalizedIntegralGood F k D f uStar A eta ⊆ Prop210Good F k D f (2 * A) (2 * eta) := by
  intro omega homega
  exact prop210Bound_of_localized_integral (F.H k omega) hD f (uStar k omega)
    (hlocal omega) homega

/-- Consequently the exact Proposition 2.10 failure event is contained in the localized failure
event. This is the event implication needed before the one-scale estimate application. -/
theorem prop210Bad_subset_localizedIntegralBad
    (F : CellFamily.RandomCellFamily) (k : ℕ) {D : Set ℂ} (hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞) {A eta : ℝ}
    (hlocal : ∀ omega z, z ∈ D → uDens (F.H k omega) z ≤ 2 * uStar k omega z) :
    Prop210Bad F k D f (2 * A) (2 * eta) ⊆
      LocalizedIntegralBad F k D f uStar A eta :=
  compl_subset_compl.mpr
    (localizedIntegralGood_subset_prop210Good F k hD f uStar hlocal)

/-- A localized bad-event estimate at a fixed scale transfers unchanged to the exact
`Prop210Bound` bad event. The constants in the conclusion are explicitly `2A` and `2 eta`. -/
theorem measure_prop210Bad_le_of_localizedIntegralBad
    (F : CellFamily.RandomCellFamily) (k : ℕ) {D : Set ℂ} (hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞) {A eta : ℝ}
    (hlocal : ∀ omega z, z ∈ D → uDens (F.H k omega) z ≤ 2 * uStar k omega z)
    (p : ℝ≥0∞) (hprob : F.P (LocalizedIntegralBad F k D f uStar A eta) ≤ p) :
    F.P (Prop210Bad F k D f (2 * A) (2 * eta)) ≤ p :=
  (measure_mono (prop210Bad_subset_localizedIntegralBad F k hD f uStar hlocal)).trans hprob

/-- Polynomial per-scale specialization in the form used by the one-scale estimate. -/
theorem measure_prop210Bad_le_scalePower
    (F : CellFamily.RandomCellFamily) (k : ℕ) {D : Set ℂ} (hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞) {A eta C alpha : ℝ}
    (hlocal : ∀ omega z, z ∈ D → uDens (F.H k omega) z ≤ 2 * uStar k omega z)
    (hprob : F.P (LocalizedIntegralBad F k D f uStar A eta) ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ alpha)) :
    F.P (Prop210Bad F k D f (2 * A) (2 * eta)) ≤
      ENNReal.ofReal (C * CellFamily.mesh k ^ alpha) :=
  measure_prop210Bad_le_of_localizedIntegralBad F k hD f uStar hlocal _ hprob

/-- The fixed-scale Proposition 2.10 adapter in the paper's parameterization. For an admissible
fixed pair `(D,f)`, a localized failure estimate at half the error budget yields the same
estimate for G3's exact event at error `epsilon_k ^ alpha`. The deterministic `(4.20)` loss is
displayed as `2*A`; halving the localized error compensates for its factor of two. The admissibility
assumptions belong to the producer of `hprob`; the event-transfer step itself uses only
measurability of `D`. -/
theorem measure_prop210Bad_le_of_admissible
    (F : CellFamily.RandomCellFamily) (k : ℕ) {rho C beta alpha alphaFail Cfail A : ℝ}
    {D : Set ℂ} {f : ℂ → ℝ}
    (hadm : Prop210Admissible (CellFamily.mesh k) rho C beta D f)
    (uStar : ℕ → F.Ω → ℂ → ℝ≥0∞)
    (hlocal : ∀ omega z, z ∈ D → uDens (F.H k omega) z ≤ 2 * uStar k omega z)
    (hprob : F.P (LocalizedIntegralBad F k D f uStar A (CellFamily.mesh k ^ alpha / 2)) ≤
      ENNReal.ofReal (Cfail * CellFamily.mesh k ^ alphaFail)) :
    F.P (Prop210Bad F k D f (2 * A) (CellFamily.mesh k ^ alpha)) ≤
      ENNReal.ofReal (Cfail * CellFamily.mesh k ^ alphaFail) := by
  have htransfer := measure_prop210Bad_le_of_localizedIntegralBad F k
    hadm.2.2.2.2.2.2.1.measurableSet f uStar hlocal _ hprob
  have heta : 2 * (CellFamily.mesh k ^ alpha / 2) = CellFamily.mesh k ^ alpha := by ring
  simpa only [heta] using htransfer

end MatedCRTHarmonic.GMS4

