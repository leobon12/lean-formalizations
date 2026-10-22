import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.UnifBase.Hyp
import HigherDimLQGContinuity.Param.Interval
import HigherDimLQGContinuity.Fatou.Main
import HigherDimLQGContinuity.Continuum.LowerEnvelope
import HigherDimLQGContinuity.Continuum.LowerHolder
import HigherDimLQGContinuity.Continuum.DiamGeneral
import HigherDimLQGContinuity.Continuum.Log
import HigherDimLQGContinuity.Continuum.Escape
import HigherDimLQGContinuity.Continuum.Proper
import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGMetric.Sec8.Geod
import HigherDimLQGMetric.Sec10.Lemma101
import HigherDimLQGMetric.Proper.Proper
import HigherDimLQGMetric.Shell.Across
import HigherDimLFPP.Field.Exists

/-!
# The unit-pin continuum estimates (packet L4)

This file assembles the continuum Fatou and lower-modulus results into the
unit-pin clauses of Lemma 2.1. The pin change is in a companion module.
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

/-- The compact interval from zero to a subcritical upper parameter. -/
theorem l4_subcrit_interval {d : ℕ} (hd : 2 ≤ d) {b : ℝ}
    (hb : b ∈ subcritSet d) : IsSubcritCompact d (Icc 0 b) := by
  refine ⟨isCompact_Icc, ?_, ?_⟩
  · intro ξ hξ
    exact hξ.1
  · intro ξ hξ hξ0
    have hcrit : b < xiCrit d := by
      rw [subcritSet_eq_Ioo hd] at hb
      exact hb.2
    have hmem : ξ ∈ subcritSet d := by
      rw [subcritSet_eq_Ioo hd]
      exact ⟨hξ0, hξ.2.trans_lt hcrit⟩
    exact hmem.2

/-- All positive parameters in a fixed subcritical interval satisfy one uniform hypothesis. -/
theorem l4_exists_window {d : ℕ} (hd : 3 ≤ d) {ξbar : ℝ}
    (hbar : ξbar ∈ subcritSet d) :
    ∃ (κ : Rd d → ℝ) (b μ : ℝ), HigherDimLFPP.IsLFPPKernel κ ∧
      0 < b ∧ 0 < μ ∧ μ ≤ 1 ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, UHyp d κ b μ ξ := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨b, μ, hb, hμ, hμ1, hwin⟩ :=
    exists_uHyp_of_isSubcritCompact (show 2 ≤ d by omega)
      (l4_subcrit_interval (show 2 ≤ d by omega) hbar)
  exact ⟨κ, b, μ, hκ, by linarith, hμ, hμ1,
    fun ξ hξ => hwin κ hκ ξ ⟨hξ.1.le, hξ.2⟩ hξ.1⟩

/-- Inverse internal crossings are bounded by inverse global crossings. -/
theorem l4_cross_le {d : ℕ} (G : ContMetric d) (z : Rd d) (a c q : ℝ) (hq : 0 ≤ q) :
    (setDistIn G univ (sphere z a) (sphere z c))⁻¹ ^ q ≤
      (acrossDist G z a c)⁻¹ ^ q := by
  apply ENNReal.rpow_le_rpow _ hq
  apply ENNReal.inv_le_inv.2
  simp only [setDistIn, acrossDist]
  refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
  exact (iInf₂_le u hu).trans ((iInf₂_le v hv).trans (G.ofReal_le_internal univ u v))

/-- The open-inner-ball escape failure is contained in the closed-inner-ball failure. -/
theorem l4_escape_event_sub {d : ℕ} (G : ContMetric d) (K R S : ℝ) :
    ¬ (ENNReal.ofReal K * diamIn G (ball (0 : Rd d) (2 * R)) (ball 0 R) <
        setDistIn G univ (sphere 0 (2 * R)) (sphere 0 (S * R))) →
      acrossDist G 0 (2 * R) (S * R) ≤
        ENNReal.ofReal K * internalDiamRd G (closedBall (0 : Rd d) R) (ball 0 (2 * R)) := by
  intro h
  have h1 : acrossDist G 0 (2 * R) (S * R) ≤
      setDistIn G univ (sphere 0 (2 * R)) (sphere 0 (S * R)) := by
    simp only [setDistIn, acrossDist]
    refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
    exact (iInf₂_le u hu).trans ((iInf₂_le v hv).trans (G.ofReal_le_internal univ u v))
  have h2 : diamIn G (ball (0 : Rd d) (2 * R)) (ball 0 R) ≤
      internalDiamRd G (closedBall (0 : Rd d) R) (ball 0 (2 * R)) := by
    simp only [diamIn, internalDiamRd]
    exact iSup₂_mono' fun u hu => ⟨u, ball_subset_closedBall hu,
      iSup₂_mono' fun v hv => ⟨v, ball_subset_closedBall hv, le_rfl⟩⟩
  exact h1.trans ((not_lt.1 h).trans (by gcongr))

/-- One explicit order satisfies the upper moment constraint for the whole window. -/
private theorem l4_moment_params {d : ℕ} (hd : 3 ≤ d) {b μ : ℝ}
    (hb : 0 < b) (hμ : 0 < μ) :
    0 < μ / 2 ∧ μ / 2 < μ ∧
      0 < Real.sqrt (2 * d) / (64 * b) ∧
      32 * (Real.sqrt (2 * d) / (64 * b)) * b ≤ Real.sqrt (2 * d) := by
  have hsqrt : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  have hden : 0 < 64 * b := by positivity
  refine ⟨by linarith, by linarith, div_pos hsqrt hden, ?_⟩
  have hb0 : b ≠ 0 := ne_of_gt hb
  field_simp
  linarith

/-- The (E0) clause under the unit pin. -/
theorem l4_unit_logIntegrable {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {ξ : ℝ} (hξ : UHyp d κ b μ ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D) :
    Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d) := by
  obtain ⟨hσ, hσμ, hp, hpb⟩ := l4_moment_params hd hb hμ
  obtain ⟨C, A, h⟩ := continuum_fatou hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  exact (h ξ hξ D hD).1

/-- The unit-pin form of (E2), with the geometric shape fixed before the bound. -/
theorem l4_unit_cross {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (z : Rd d) {a c q : ℝ} (ha : 0 < a) (hac : a < c) (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (setDistIn (rho D g) univ (sphere z a) (sphere z c))⁻¹ ^ q
          ∂(pinLaw d 1) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := continuum_invCross hd hκ hC1 hC2 hb hμ hμ1 z ha hac hq
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  rw [pinLaw_one (show 2 ≤ d by omega)]
  exact (lintegral_mono fun g => l4_cross_le (rho D g) z a c q hq.le).trans
    (hC ξ hξ D hD)

/-- The unit-pin form of (E3), at the explicit moment order supplied by Fatou. -/
theorem l4_unit_diam {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (U Kc : Set (Rd d)) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : IsConnected U) (hK : IsCompact Kc) (hKU : Kc ⊆ U) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, (diamIn (rho D g) U Kc) ^ (Real.sqrt (2 * d) / (64 * b))
          ∂(pinLaw d 1) ≤ ENNReal.ofReal C := by
  obtain ⟨hσ, hσμ, hp, hpb⟩ := l4_moment_params hd hb hμ
  obtain ⟨C, hC⟩ := continuum_diam hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
    U Kc hU hUb hUc hK hKU
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  rw [pinLaw_one (show 2 ≤ d by omega)]
  exact hC ξ hξ D hD

/-- The unit-pin form of (E4). -/
theorem l4_unit_logMoments {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (x y : Rd d) (hxy : x ≠ y) {q : ℝ} (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
        ∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))| ^ q)
          ∂(pinLaw d 1) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := continuum_logPt hd hκ hC1 hC2 hb hμ hμ1 x y hxy hq
  refine ⟨C, fun ξ hξ D hD => ?_⟩
  rw [pinLaw_one (show 2 ≤ d by omega)]
  simpa only [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith : 0 ≤ q)] using hC ξ hξ D hD

/-- The unit-pin form of (E5); the bad event is enlarged to a global crossing
and a closed inner ball, exactly as in the continuum escape estimate. -/
theorem l4_unit_escape {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ pesc : ℝ, 0 < pesc ∧ ∀ K : ℝ, 1 ≤ K → ∃ CK : ℝ,
      ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
      ∀ R S : ℝ, 1 ≤ R → 4 ≤ S →
        pinLaw d 1 {g | ¬ (ENNReal.ofReal K *
          diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
          setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))} ≤
          ENNReal.ofReal (CK * S ^ (-pesc)) := by
  obtain ⟨hσ, hσμ, hp, hpb⟩ := l4_moment_params hd hb hμ
  let q : ℝ := μ / (2 * b ^ 2)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqb : q ^ 2 * b ^ 2 ≤ q * μ / 2 := by
    dsimp [q]
    have hb0 : b ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hb)
    field_simp
    norm_num
  obtain ⟨C, hC0, hC⟩ := continuum_escape_rho hd hκ hC1 hC2 hb hμ hμ1
    hσ hσμ hp hpb hq hqb
  refine ⟨μ / 4 * min q (Real.sqrt (2 * d) / (64 * b)),
    mul_pos (by linarith) (lt_min hq hp), fun K hK =>
      ⟨C * (K ^ q + 1), fun ξ hξ D hD R S hR hS => ?_⟩⟩
  rw [pinLaw_one (show 2 ≤ d by omega)]
  calc
    normLGFLaw d {g | ¬ (ENNReal.ofReal K *
      diamIn (rho D g) (ball 0 (2 * R)) (ball 0 R) <
      setDistIn (rho D g) univ (sphere 0 (2 * R)) (sphere 0 (S * R)))} ≤
      normLGFLaw d {g | acrossDist (rho D g) 0 (2 * R) (S * R) ≤
        ENNReal.ofReal K * internalDiamRd (rho D g)
          (closedBall (0 : Rd d) R) (ball 0 (2 * R))} := by
        apply measure_mono
        intro g hg
        exact l4_escape_event_sub (rho D g) K R S hg
    _ ≤ ENNReal.ofReal
      (C * (K ^ q + 1) * S ^ (-(μ / 4 * min q (Real.sqrt (2 * d) / (64 * b))))) :=
      hC ξ hξ D hD K R S hK hR hS

/-- Properness and constant-speed geodesics hold under any positive pin. -/
theorem l4_pinned_proper {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    {b μ ξ : ℝ} (hξ : UHyp d κ b μ ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂(pinLaw d s), ProperSpace (rho D g).Space ∧
      ∀ x y : Rd d, ∃ γ : C(unitInterval, Rd d),
        IsConstSpeedGeod (rho D g) x y γ := by
  have hd2 : 2 ≤ d := by omega
  haveI : IsProbabilityMeasure (pinLaw d s) := isProbabilityMeasure_pinLaw hd2 s
  have hlgf := (isWholeSpaceLGF_pinLaw hd2 hs).1
  have hsub := fatou_subcritical hξ
  have hp := lemma27_proper hd hsub.1 hsub.2 (lemma101 hd2 hsub.1 hD)
    (pinLaw d s) id hlgf
  have hl := hD.length (pinLaw d s) id hlgf.isLGFPlusCont
  filter_upwards [hp, hl] with g hg hlen
  have hlenρ : (rho D g).IsLength :=
    ContMetric.isLength_smul (Real.exp_pos _) hlen
  letI : ProperSpace (D g).Space := hg
  have hproperρ : ProperSpace (rho D g).Space := by
    apply sec8_proper_of_metric_lower (D g) (rho D g) (Real.exp_pos _)
    intro u v
    change Real.exp (-logMean D) * (D g).1 (u, v) ≤
      Real.exp (-logMean D) * (D g).1 (u, v)
    exact le_rfl
  exact ⟨hproperρ, fun x y => @sec8_exists_constSpeedGeod d (rho D g)
    hlenρ hproperρ x y⟩

/-- A sum of two envelopes has a controlled fractional moment. -/
private theorem l4_lintegral_sum_envelope {d : ℕ} (ν : Measure (DistRd d))
    (Hu Hl : DistRd d → ℝ) (hHu : Measurable Hu) (_hHl : Measurable Hl)
    (hHu1 : ∀ g, 1 ≤ Hu g) (hHl1 : ∀ g, 1 ≤ Hl g)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫⁻ g, ENNReal.ofReal ((Hu g + Hl g) ^ p) ∂ν) ≤
      (∫⁻ g, ENNReal.ofReal ((Hu g) ^ p) ∂ν) +
        ∫⁻ g, ENNReal.ofReal ((Hl g) ^ p) ∂ν := by
  calc
    (∫⁻ g, ENNReal.ofReal ((Hu g + Hl g) ^ p) ∂ν) ≤
        ∫⁻ g, (ENNReal.ofReal ((Hu g) ^ p) + ENNReal.ofReal ((Hl g) ^ p)) ∂ν := by
          apply lintegral_mono
          intro g
          change ENNReal.ofReal ((Hu g + Hl g) ^ p) ≤
            ENNReal.ofReal (Hu g ^ p) + ENNReal.ofReal (Hl g ^ p)
          rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith [hHu1 g, hHl1 g]) hp,
            ENNReal.ofReal_add (by linarith [hHu1 g]) (by linarith [hHl1 g]),
            ← ENNReal.ofReal_rpow_of_nonneg (by linarith [hHu1 g]) hp,
            ← ENNReal.ofReal_rpow_of_nonneg (by linarith [hHl1 g]) hp]
          exact ENNReal.rpow_add_le_add_rpow _ _ hp hp1
    _ = _ := lintegral_add_left' ((ENNReal.measurable_ofReal.comp
      (hHu.pow_const p)).aemeasurable) _

/-- The unit-pin two-sided Hölder envelope, with one moment order and one polynomial bound. -/
theorem l4_unit_envelope {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    ∃ p σ β C A : ℝ, 0 < p ∧ 0 < σ ∧ σ < 1 ∧ 1 < β ∧ 0 < C ∧ 0 ≤ A ∧
      p ≤ Real.sqrt (2 * d) / (64 * b) ∧
      ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
          HolderEnvelope (pinLaw d 1) (rho D) p σ β C A := by
  let σ : ℝ := μ / 2
  let pplus : ℝ := Real.sqrt (2 * d) / (64 * b)
  let p : ℝ := min pplus (1 / 2)
  let β : ℝ := 2 + d + Real.sqrt (2 * d) * b + b ^ 2
  have ⟨hσ, hσμ, hpplus, hpbplus⟩ := l4_moment_params hd hb hμ
  have hσ1 : σ < 1 := by dsimp [σ]; linarith
  have hp : 0 < p := lt_min hpplus (by norm_num)
  have hp1 : p ≤ 1 := (min_le_right ..).trans (by norm_num)
  have hpq : p < 1 := lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have hpb : 32 * p * b ≤ Real.sqrt (2 * d) := by
    have hle : p ≤ pplus := min_le_left ..
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ 32 * b by positivity)]
  have hβ : 1 < β := by
    dsimp [β]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hsqrt : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hsqrt hb.le, sq_nonneg b]
  have hβcond : 1 ≤ (1 : ℝ) * (β - 1 - Real.sqrt (2 * d) * b) -
      (1 : ℝ) ^ 2 * b ^ 2 - d := by
    dsimp [β]
    ring_nf
    norm_num
  obtain ⟨Cu, Au, hu⟩ := continuum_fatou hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  obtain ⟨Cl, hCl0, hl⟩ := continuum_holderLower hd hκ hC1 hC2 hb hμ hμ1
    (show 0 < (1 : ℝ) by norm_num) hβcond
  let Al : ℝ := (d : ℝ) + 2 * b ^ 2
  let A : ℝ := max 0 Au + p * β + Al
  let B : ℝ := Cl * (1 / (1 - p)) * 16 ^ (p * β)
  let C : ℝ := max 1 Cu + B
  have hAl0 : 0 ≤ Al := by dsimp [Al]; positivity
  have hpβ0 : 0 ≤ p * β := mul_nonneg hp.le (by linarith : 0 ≤ β)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hC0 : 0 < C := by dsimp [C]; linarith [le_max_left 1 Cu]
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC0, hA0,
    (min_le_left ..), fun ξ hξ D hD R hR => ?_⟩
  obtain ⟨_hint, hupper⟩ := hu ξ hξ D hD
  obtain ⟨Hu, hHum, hHu1, hHumom, hHupt⟩ := hupper R hR
  obtain ⟨Hl, hHlm, hHl1, hHlmom, hHlpt⟩ := hl ξ hξ D hD R hR
  let H : DistRd d → ℝ := fun g => Hu g + Hl g
  have hH1 : ∀ g, 1 ≤ H g := fun g => by dsimp [H]; linarith [hHu1 g, hHl1 g]
  have hpoly (R : ℝ) (hR : 1 ≤ R) :
      Cu * (1 + R) ^ Au + Cl * (1 / (1 - p)) * (16 * R) ^ (p * β) *
        (1 + R) ^ Al ≤ C * (1 + R) ^ A := by
    have hRbase : 1 ≤ 1 + R := by linarith
    have hR0 : 0 ≤ R := by linarith
    have huAu : (1 + R) ^ Au ≤ (1 + R) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hRbase (by dsimp [A]; linarith [le_max_right 0 Au])
    have hlpow : (16 * R) ^ (p * β) ≤ 16 ^ (p * β) * (1 + R) ^ (p * β) := by
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (by linarith : 0 ≤ 1 + R)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) hpβ0
    have hRA : (1 + R) ^ (p * β + Al) ≤ (1 + R) ^ A :=
      Real.rpow_le_rpow_of_exponent_le hRbase (by dsimp [A]; linarith [le_max_left 0 Au])
    have heq : (1 + R) ^ (p * β) * (1 + R) ^ Al =
        (1 + R) ^ (p * β + Al) := (Real.rpow_add (by linarith : 0 < 1 + R) _ _).symm
    have hCu : Cu ≤ max 1 Cu := le_max_right 1 Cu
    have hCu0 : 0 ≤ max 1 Cu := by linarith [le_max_left 1 Cu]
    have hpow0 : 0 ≤ (1 + R) ^ A := Real.rpow_nonneg (by linarith) _
    have hcoef0 : 0 ≤ Cl * (1 / (1 - p)) := by positivity
    calc
      Cu * (1 + R) ^ Au + Cl * (1 / (1 - p)) * (16 * R) ^ (p * β) *
          (1 + R) ^ Al ≤
          max 1 Cu * (1 + R) ^ A + B * (1 + R) ^ A := by
            apply add_le_add
            · exact (mul_le_mul_of_nonneg_right hCu (Real.rpow_nonneg (by linarith) _)).trans
                (mul_le_mul_of_nonneg_left huAu hCu0)
            · dsimp [B]
              calc
                Cl * (1 / (1 - p)) * (16 * R) ^ (p * β) * (1 + R) ^ Al ≤
                    Cl * (1 / (1 - p)) * (16 ^ (p * β) * (1 + R) ^ (p * β)) *
                      (1 + R) ^ Al := by gcongr
                _ = B * ((1 + R) ^ (p * β) * (1 + R) ^ Al) := by ring
                _ ≤ B * (1 + R) ^ A := by rw [heq]; exact mul_le_mul_of_nonneg_left hRA hB0
      _ = C * (1 + R) ^ A := by dsimp [C]; ring
  refine ⟨H, hHum.add hHlm, hH1, ?_, ?_⟩
  · rw [pinLaw_one (show 2 ≤ d by omega)]
    have hsum := l4_lintegral_sum_envelope (normLGFLaw d) Hu Hl hHum hHlm hHu1 hHl1 hp.le hp1
    calc
      (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d)) ≤
          ENNReal.ofReal (Cu * (1 + R) ^ Au) +
            ENNReal.ofReal (Cl * (1 / (1 - p)) * (16 * R) ^ (p * β) * (1 + R) ^ Al) := by
            dsimp [H]
            exact hsum.trans (add_le_add hHumom (by
              simpa only [one_div, one_mul, mul_one, one_pow, Al] using hHlmom p hp hpq))
      _ = ENNReal.ofReal (Cu * (1 + R) ^ Au +
          Cl * (1 / (1 - p)) * (16 * R) ^ (p * β) * (1 + R) ^ Al) := by
            rw [ENNReal.ofReal_add]
            · exact le_of_lt (by
                have h : 0 < Cu * (1 + R) ^ Au := by
                  haveI : IsProbabilityMeasure (normLGFLaw d) := by
                    rw [← pinLaw_one (show 2 ≤ d by omega)]
                    exact isProbabilityMeasure_pinLaw (show 2 ≤ d by omega) 1
                  have hnonzero : (0 : ℝ≥0∞) < ∫⁻ g, ENNReal.ofReal (Hu g ^ p) ∂(normLGFLaw d) := by
                    have h1 : ∀ g, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Hu g ^ p) := by
                      intro g
                      rw [← ENNReal.ofReal_one]
                      exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (hHu1 g) hp.le)
                    calc (0 : ℝ≥0∞) < 1 := zero_lt_one
                      _ = ∫⁻ _, (1 : ℝ≥0∞) ∂(normLGFLaw d) := by simp
                      _ ≤ _ := lintegral_mono fun g => h1 g
                  have := hnonzero.trans_le hHumom
                  exact (ENNReal.ofReal_pos.mp this)
                exact h)
            · positivity
      _ ≤ ENNReal.ofReal (C * (1 + R) ^ A) := ENNReal.ofReal_le_ofReal (hpoly R hR)
  · rw [pinLaw_one (show 2 ≤ d by omega)]
    filter_upwards [hHupt, hHlpt] with g hgu hgl
    constructor
    · intro z hz s hs
      have hHg : Hu g ≤ H g := by dsimp [H]; linarith [hHl1 g]
      exact (hgu z hz s hs).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hHg (Real.rpow_nonneg hs.1.le _)))
    · intro x hx y hy
      have hHg : Hl g ≤ H g := by dsimp [H]; linarith [hHu1 g]
      have hpos : 0 < Hl g := by linarith [hHl1 g]
      have hinv : (H g)⁻¹ ≤ (Hl g)⁻¹ := inv_anti₀ hpos hHg
      calc
        (H g)⁻¹ * ‖x - y‖ ^ β ≤ (Hl g)⁻¹ * ‖x - y‖ ^ β :=
          mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg (norm_nonneg _) _)
        _ = ‖x - y‖ ^ β / Hl g := by ring
        _ ≤ (rho D g).1 (x, y) := hgl x hx y hy

/-- Lemma 2.1 at its unit pin, uniformly over the Appendix A parameter window. -/
theorem l4_unit_estimates {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ ξbar : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hwin : ∀ ξ ∈ Ioc (0 : ℝ) ξbar, UHyp d κ b μ ξ) :
    UniformEstimates d ξbar 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ D hD
    exact l4_unit_logIntegrable hd hκ hC1 hC2 hb hμ hμ1 (hwin ξ hξ) hD
  · obtain ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC, hA, _hpplus, henv⟩ :=
      l4_unit_envelope hd hκ hC1 hC2 hb hμ hμ1
    exact ⟨p, σ, β, C, A, hp, hσ, hσ1, hβ, hC, hA,
      fun ξ hξ D hD => henv ξ (hwin ξ hξ) D hD⟩
  · intro z r₁ r₂ q hr₁ hr₁₂ hq
    obtain ⟨K, hK⟩ := l4_unit_cross hd hκ hC1 hC2 hb hμ hμ1 z hr₁ hr₁₂ hq
    exact ⟨K, fun ξ hξ D hD => hK ξ (hwin ξ hξ) D hD⟩
  · have hp : 0 < Real.sqrt (2 * d) / (64 * b) := (l4_moment_params hd hb hμ).2.2.1
    refine ⟨Real.sqrt (2 * d) / (64 * b), hp, ?_⟩
    intro U Kc hU hUb hUc hK hKU
    obtain ⟨K, hbound⟩ := l4_unit_diam hd hκ hC1 hC2 hb hμ hμ1 U Kc hU hUb hUc hK hKU
    exact ⟨K, fun ξ hξ D hD => hbound ξ (hwin ξ hξ) D hD⟩
  · intro x y hxy q hq
    obtain ⟨K, hbound⟩ := l4_unit_logMoments hd hκ hC1 hC2 hb hμ hμ1 x y hxy hq
    exact ⟨K, fun ξ hξ D hD => hbound ξ (hwin ξ hξ) D hD⟩
  · obtain ⟨pesc, hpesc, hesc⟩ := l4_unit_escape hd hκ hC1 hC2 hb hμ hμ1
    refine ⟨pesc, hpesc, ?_⟩
    intro K hK
    obtain ⟨CK, hCK⟩ := hesc K hK
    exact ⟨CK, fun ξ hξ D hD R S hR hS => hCK ξ (hwin ξ hξ) D hD R S hR hS⟩
  · intro ξ hξ D hD
    exact l4_pinned_proper hd (hwin ξ hξ) hD one_pos

end HigherDimLQGContinuity
