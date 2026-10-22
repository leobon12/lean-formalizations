import HigherDimLQGContinuity.Lemma21.PinTransfer

/-!
# Corrected Proposition A.3 and Lemma 2.1 (packet L4)

The Appendix A result is stated for canonical continuum metrics on compact
subcritical parameter sets. `lemma21_of` then applies the radius-one pin
change to a whole interval from zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- A fixed admissible kernel receives one uniform window over every compact
subcritical parameter set. -/
theorem l4_compact_window {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {J : Set ℝ}
    (hJ : IsSubcritCompact d J) :
    ∃ b μ : ℝ, 0 < b ∧ 0 < μ ∧ μ ≤ 1 ∧
      ∀ ξ ∈ J, 0 < ξ → UHyp d κ b μ ξ := by
  obtain ⟨b, μ, hb, hμ, hμ1, hw⟩ :=
    exists_uHyp_of_isSubcritCompact (show 2 ≤ d by omega) hJ
  exact ⟨b, μ, by linarith, hμ, hμ1, hw κ hκ⟩

/-- On a probability space, a positive moment controls every smaller
nonnegative moment by `u^p ≤ 1 + u^q`. -/
theorem l4_lintegral_lower_order {α : Type*} [MeasurableSpace α]
    (P : Measure α) [IsProbabilityMeasure P]
    (f : α → ℝ≥0∞) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (∫⁻ a, f a ^ p ∂P) ≤ 1 + ∫⁻ a, f a ^ q ∂P := by
  calc
    (∫⁻ a, f a ^ p ∂P) ≤ ∫⁻ a, (1 : ℝ≥0∞) + f a ^ q ∂P := by
      apply lintegral_mono
      intro a
      rcases le_total (f a) 1 with h | h
      · exact le_add_of_le_of_nonneg (ENNReal.rpow_le_one h hp) bot_le
      · exact (ENNReal.rpow_le_rpow_of_exponent_le h hpq).trans
          (le_add_of_nonneg_left bot_le)
    _ = 1 + ∫⁻ a, f a ^ q ∂P := by
      rw [lintegral_add_left measurable_const]
      simp

/-- Proposition A.3 (i), (ii), (iv), (vii): log integrability, a two-sided
Hölder envelope, a buffered diameter moment at the same order, and almost
sure properness and constant-speed geodesics. -/
theorem propA3Main {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {J : Set ℝ} (hJ : IsSubcritCompact d J) :
    (∀ ξ ∈ J, 0 < ξ → ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d)) ∧
    (∃ p σ β C A : ℝ, 0 < p ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧ 0 < C ∧ 0 ≤ A ∧
      (∀ ξ ∈ J, 0 < ξ → ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        HolderEnvelope (pinLaw d 1) (rho D) p σ β C A) ∧
      ∀ U Kc : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
        IsCompact Kc → Kc ⊆ U → ∃ Cdiam : ℝ,
          ∀ ξ ∈ J, 0 < ξ →
            ∀ D : DistRd d → ContMetric d,
              IsStrongExpMetric d ξ (distExp d ξ) D →
              ∫⁻ g, (diamIn (rho D g) U Kc) ^ p
                ∂(pinLaw d 1) ≤ ENNReal.ofReal Cdiam) ∧
    (∀ ξ ∈ J, 0 < ξ → ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      ∀ᵐ g ∂(pinLaw d 1), ProperSpace (rho D g).Space ∧
        ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d),
          IsConstSpeedGeod (rho D g) x y γ) := by
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ := l4_compact_window hd hκ hJ
  refine ⟨fun ξ hξ hξ0 D hD =>
    l4_unit_logIntegrable hd hκ hC1 hC2 hb hμ hμ1 (hwin ξ hξ hξ0) hD,
    ?_, fun ξ hξ hξ0 D hD =>
      l4_pinned_proper hd (hwin ξ hξ hξ0) hD one_pos⟩
  obtain ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC, hA, hpplus, henv⟩ :=
    l4_unit_envelope hd hκ hC1 hC2 hb hμ hμ1
  refine ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC, hA,
    fun ξ hξ hξ0 D hD => henv ξ (hwin ξ hξ hξ0) D hD, ?_⟩
  intro U Kc hU hUb hUc hK hKU
  obtain ⟨M, hM⟩ := l4_unit_diam hd hκ hC1 hC2 hb hμ hμ1 U Kc hU hUb hUc hK hKU
  let Cdiam : ℝ := 1 + max 0 M
  refine ⟨Cdiam, fun ξ hξ hξ0 D hD => ?_⟩
  haveI : IsProbabilityMeasure (pinLaw d 1) :=
    isProbabilityMeasure_pinLaw (show 2 ≤ d by omega) 1
  calc
    (∫⁻ g, (diamIn (rho D g) U Kc) ^ p ∂(pinLaw d 1)) ≤
        1 + ∫⁻ g, (diamIn (rho D g) U Kc) ^
          (Real.sqrt (2 * d) / (64 * b)) ∂(pinLaw d 1) :=
            l4_lintegral_lower_order (pinLaw d 1) _ hp.le hpplus
    _ ≤ 1 + ENNReal.ofReal (max 0 M) := by
      exact add_le_add le_rfl ((hM ξ (hwin ξ hξ hξ0) D hD).trans
        (ENNReal.ofReal_le_ofReal (le_max_right 0 M)))
    _ = ENNReal.ofReal Cdiam := by
      dsimp [Cdiam]
      rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 0 M)]
      norm_num

/-- Proposition A.3 (iii): all inverse moments of a fixed annular crossing. -/
theorem propA3Cross {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {J : Set ℝ} (hJ : IsSubcritCompact d J)
    (z : Rd d) {a c q : ℝ} (ha : 0 < a) (hac : a < c) (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ ∈ J, 0 < ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹ ^ q
          ∂(pinLaw d 1) ≤ ENNReal.ofReal C := by
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ := l4_compact_window hd hκ hJ
  obtain ⟨C, hC⟩ := l4_unit_cross hd hκ hC1 hC2 hb hμ hμ1 z ha hac hq
  exact ⟨C, fun ξ hξ hξ0 D hD => hC ξ (hwin ξ hξ hξ0) D hD⟩

/-- Proposition A.3 (iv): a positive buffered-diameter moment. -/
theorem propA3Diam {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {J : Set ℝ} (hJ : IsSubcritCompact d J) :
    ∃ pplus : ℝ, 0 < pplus ∧
      ∀ U Kc : Set (Rd d), IsOpen U → Bornology.IsBounded U → IsConnected U →
        IsCompact Kc → Kc ⊆ U → ∃ C : ℝ,
          ∀ ξ ∈ J, 0 < ξ →
            ∀ D : DistRd d → ContMetric d,
              IsStrongExpMetric d ξ (distExp d ξ) D →
              ∫⁻ g, (diamIn (rho D g) U Kc) ^ pplus
                ∂(pinLaw d 1) ≤ ENNReal.ofReal C := by
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ := l4_compact_window hd hκ hJ
  have hp : 0 < Real.sqrt (2 * d) / (64 * b) := by
    apply div_pos (Real.sqrt_pos.2 ?_) (by positivity)
    have : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  refine ⟨Real.sqrt (2 * d) / (64 * b), hp, ?_⟩
  intro U Kc hU hUb hUc hK hKU
  obtain ⟨C, hC⟩ := l4_unit_diam hd hκ hC1 hC2 hb hμ hμ1 U Kc hU hUb hUc hK hKU
  exact ⟨C, fun ξ hξ hξ0 D hD => hC ξ (hwin ξ hξ hξ0) D hD⟩

/-- Proposition A.3 (v): logarithmic moments of fixed point distances. -/
theorem propA3LogPt {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {J : Set ℝ} (hJ : IsSubcritCompact d J)
    (x y : Rd d) (hxy : x ≠ y) {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ ξ ∈ J, 0 < ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q)
          ∂(pinLaw d 1) ≤ ENNReal.ofReal C := by
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ := l4_compact_window hd hκ hJ
  obtain ⟨C, hC⟩ := l4_unit_logMoments hd hκ hC1 hC2 hb hμ hμ1 x y hxy hq
  exact ⟨C, fun ξ hξ hξ0 D hD => hC ξ (hwin ξ hξ hξ0) D hD⟩

/-- Proposition A.3 (vi): a relative escape tail bound. -/
theorem propA3Escape {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {J : Set ℝ} (hJ : IsSubcritCompact d J) :
    ∃ pesc : ℝ, 0 < pesc ∧ ∀ K : ℝ, 1 ≤ K → ∃ CK : ℝ,
      ∀ ξ ∈ J, 0 < ξ →
        ∀ D : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
          ∀ R S : ℝ, 1 ≤ R → 4 ≤ S →
            pinLaw d 1 {g | ¬ (ENNReal.ofReal K *
              diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
              setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))} ≤
                ENNReal.ofReal (CK * S ^ (-pesc)) := by
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ := l4_compact_window hd hκ hJ
  obtain ⟨pesc, hpesc, hesc⟩ := l4_unit_escape hd hκ hC1 hC2 hb hμ hμ1
  refine ⟨pesc, hpesc, fun K hK => ?_⟩
  obtain ⟨CK, hCK⟩ := hesc K hK
  exact ⟨CK, fun ξ hξ hξ0 D hD R S hR hS =>
    hCK ξ (hwin ξ hξ hξ0) D hD R S hR hS⟩

/-- Lemma 2.1 under precisely the two continuum shape interfaces C1 and C2.
The positive pin may be chosen in `[1,10]` (indeed any positive radius). -/
theorem lemma21_of {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {ξbar s : ℝ} (hbar : ξbar ∈ subcritSet d)
    (hs1 : 1 ≤ s) (_hs10 : s ≤ 10) :
    UniformEstimates d ξbar s := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ :=
    exists_uHyp_of_isSubcritCompact hd2 (l4_subcrit_interval hd2 hbar)
  have hwin' : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, UHyp d κ b μ ξ := by
    intro ξ hξ
    exact hwin κ hκ ξ ⟨hξ.1.le, hξ.2⟩ hξ.1
  have hU := l4_unit_estimates hd hκ hC1 hC2 (by linarith : 0 < b) hμ hμ1 hwin'
  exact l4_pin_estimates hd (by linarith : 0 < b) (by linarith : 0 < s) hwin' hU

end HigherDimLQGContinuity
