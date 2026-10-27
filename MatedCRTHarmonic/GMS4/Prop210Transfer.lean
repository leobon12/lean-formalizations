import MatedCRTHarmonic.GMS3.Lemma31

/-!
# Localized-to-cell-density transfer for [18] Proposition 2.10

Source: [18] (4.19)–(4.20).
The second-moment correction for Proposition 4.8 is: its second-moment argument is
performed without inserting the global event `E^ε` into the conditional expectation. This file only
formalizes the later deterministic implication (4.20): a bound for the localized density `u_*` gives
The corresponding bound for G3's selection-free cell density, with the factor 2 retained explicitly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4

open MatedCRTHarmonic.GMS3

variable {V E : Type*} {G : LFMultigraph V E} {o : V}

/-- The pointwise comparison (4.20) transfers a localized integral estimate to G3's density. -/
theorem prop210Bound_of_localized_integral
    (H : CellularEmbedding G o) {D : Set ℂ} (hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℂ → ℝ≥0∞) {A η : ℝ}
    (hlocal : ∀ z ∈ D, uDens H z ≤ 2 * uStar z)
    (hbound : (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :
    Prop210Bound H D f (2 * A) (2 * η) := by
  unfold Prop210Bound
  have hpoint : ∀ z ∈ D,
      ENNReal.ofReal (f z) * uDens H z ≤
        2 * (ENNReal.ofReal (f z) * uStar z) := by
    intro z hz
    calc
      ENNReal.ofReal (f z) * uDens H z ≤
          ENNReal.ofReal (f z) * (2 * uStar z) :=
        mul_le_mul' le_rfl (hlocal z hz)
      _ = 2 * (ENNReal.ofReal (f z) * uStar z) := by ac_rfl
  have hint : (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
      2 * (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) := by
    calc
      _ ≤ ∫⁻ z in D, 2 * (ENNReal.ofReal (f z) * uStar z) :=
        setLIntegral_mono' hD hpoint
      _ = 2 * (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) := by
        rw [lintegral_const_mul' 2 _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hA : ENNReal.ofReal (2 * A) = ENNReal.ofReal 2 * ENNReal.ofReal A :=
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))
  have hη : ENNReal.ofReal (2 * η) = ENNReal.ofReal 2 * ENNReal.ofReal η :=
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))
  calc
    (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
        2 * (ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :=
      hint.trans (mul_le_mul' le_rfl hbound)
    _ = ENNReal.ofReal (2 * A) * (∫⁻ z in D, ENNReal.ofReal (f z)) +
        ENNReal.ofReal (2 * η) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num, mul_add, hA, hη]
      ac_rfl

/-- The spatial almost-everywhere form of (4.20). The density `uDens` is
selection-free and can sum several cell weights on null cell boundaries, so
this is the form that follows from the paper's selected-cell comparison. -/
theorem prop210Bound_of_localized_integral_ae
    (H : CellularEmbedding G o) {D : Set ℂ} (_hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℂ → ℝ≥0∞) {A η : ℝ}
    (hlocal : ∀ᵐ z ∂volume.restrict D, uDens H z ≤ 2 * uStar z)
    (hbound : (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :
    Prop210Bound H D f (2 * A) (2 * η) := by
  unfold Prop210Bound
  have hpoint : ∀ᵐ z ∂volume.restrict D,
      ENNReal.ofReal (f z) * uDens H z ≤
        2 * (ENNReal.ofReal (f z) * uStar z) := by
    filter_upwards [hlocal] with z hz
    calc
      ENNReal.ofReal (f z) * uDens H z ≤
          ENNReal.ofReal (f z) * (2 * uStar z) :=
        mul_le_mul' le_rfl hz
      _ = 2 * (ENNReal.ofReal (f z) * uStar z) := by ac_rfl
  have hint : (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
      2 * (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) := by
    calc
      _ ≤ ∫⁻ z in D, 2 * (ENNReal.ofReal (f z) * uStar z) :=
        lintegral_mono_ae hpoint
      _ = 2 * (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) := by
        rw [lintegral_const_mul' 2 _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hA : ENNReal.ofReal (2 * A) = ENNReal.ofReal 2 * ENNReal.ofReal A :=
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))
  have hη : ENNReal.ofReal (2 * η) = ENNReal.ofReal 2 * ENNReal.ofReal η :=
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))
  calc
    (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
        2 * (ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :=
      hint.trans (mul_le_mul' le_rfl hbound)
    _ = ENNReal.ofReal (2 * A) * (∫⁻ z in D, ENNReal.ofReal (f z)) +
        ENNReal.ofReal (2 * η) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num, mul_add, hA, hη]
      ac_rfl

/-- The paper's pointwise selected-cell estimate (4.20) transfers to the
selection-free density used by `Prop210Bound`, since distinct cells overlap
only on a planar null set. -/
theorem prop210Bound_of_selected_cell_comparison
    (H : CellularEmbedding G o) {D : Set ℂ} (hD : MeasurableSet D)
    (f : ℂ → ℝ) (uStar : ℂ → ℝ≥0∞) {A η : ℝ}
    (c : ℂ → V) (hc : ∀ z, z ∈ H.cell (c z))
    (hselected : ∀ z ∈ D, uCoef H (c z) ≤ 2 * uStar z)
    (hbound : (∫⁻ z in D, ENNReal.ofReal (f z) * uStar z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) :
    Prop210Bound H D f (2 * A) (2 * η) := by
  have heq := uDens_ae_eq H c hc
  have hlocal : ∀ᵐ z ∂volume.restrict D, uDens H z ≤ 2 * uStar z :=
    (ae_restrict_iff' hD).2 (heq.mono fun z hz hzD => by
      rw [hz]
      exact hselected z hzD)
  exact prop210Bound_of_localized_integral_ae H hD f uStar hlocal hbound

end MatedCRTHarmonic.GMS4

