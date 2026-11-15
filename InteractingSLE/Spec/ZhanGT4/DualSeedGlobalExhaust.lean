/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalAgreement

/-!
# Removing the actual map bands on the original clock

Packet PROVE-ZHAN-GT4-A22. The band constants may grow with the index.
Pathwise eventual agreement, rather than uniform bounds in that index,
identifies the chosen stochastic integral under one fixed measure.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open Girsanov
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Actual event-localized map calculus and exhaustion yield the full
positive-time mapped-driver identity. No band integral identity is assumed. -/
theorem seedMap_positive_integral_of_exhaustion
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {d : Ω → SeedData n} {κ : ℝ}
    (hκ : 0 < κ) {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} (hε : 0 < ε)
    {T : Ω → ℝ≥0} {E : ℕ → Set Ω} {S : ℕ → Ω → ℝ≥0}
    {ρ K γ Γ lam : ℕ → ℝ} {A : Set ℂ} {r a₀ ρm : ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ)
    (hST : ∀ k ω, ω ∈ E k → S k ω ≤ T ω)
    (hown : ∀ k ω, ω ∈ E k → OwnData (d ω).W A (d ω).φ (S k ω) (d ω).a (d ω).W')
    (hconst : ∀ k ω, ω ∈ E k → (d ω).SeedConst A ε (S k ω) r a₀ (γ k) (Γ k) (lam k) ρm)
    (hF : ∀ k, IsSeedDriftField (Real.sqrt κ) (ρ k) (K k) B D
      (onEvB (E k) (seedMappedDrift κ d T)) ε (onEvS (E k) ε (S k))
      (onEv (E k) (fun ω => (d ω).F 0)) (onEv (E k) (fun ω => (d ω).F 1))
      (onEv (E k) (fun ω => (d ω).F 2)) (onEv (E k) (fun ω => (d ω).F 3))
      (onEv (E k) (fun ω => (d ω).mapTime)))
    (hρ : ∀ k, 0 < ρ k) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hS : ∀ k, IsStoppingTime 𝓕 fun ω => (onEvS (E k) ε (S k) ω : WithTop ℝ≥0))
    (hmA : ∀ k j (u : ℝ≥0), ε ≤ u → Measurable[𝓕 u]
      ((E k ∩ {ω | u ≤ S k ω}).indicator fun ω => (d ω).A j u))
    (hmRate : ∀ k (u : ℝ≥0), ε ≤ u → Measurable[𝓕 u]
      ((E k ∩ {ω | u ≤ S k ω}).indicator fun ω => (d ω).d10Rate u))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (d ω).A 1 u))
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (T ω)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, 0 < u → u ≤ T ω → |(d ω).A 1 u| ≤ C)
    (hstage : ∀ ω, ε ≤ T ω → ∀ᶠ k in atTop, ω ∈ E k ∧ S k ω = T ω)
    {t : ℝ≥0} (hεt : ε ≤ t) :
    (fun ω => (d ω).A 0 (min t (T ω)) - (d ω).A 0 (min ε (T ω)) -
      (∫ u in (min ε (T ω) : ℝ≥0)..(min t (T ω) : ℝ≥0), (d ω).d10Rate u)) =ᵐ[P]
    fun ω => stochIntegral P 𝓕 B (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T) t ω -
      stochIntegral P 𝓕 B (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T) ε ω := by
  have hpre := isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have : IsProbabilityMeasure P := hpre.isGaussianProcess.isProbabilityMeasure
  let v := positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T
  let z := seedFin2Endpoint T v
  let w := seedEndWindow ε z
  let wk := fun k => seedMapBandCoeff d κ B D ε (E k) (S k)
  have hf k := seedMapBandCoeff_facts (P := P) hdW (hF k) hBc hκ (hρ k) (hS k) (hmA k 1)
  choose Ck hCk hbk using fun k => (hf k).2.2
  obtain ⟨hw, hrw, hbw⟩ := seedMap_window_facts (P := P) ε hT hm hc hC hb
  have hlim := seed_stochIntegral_sub_eq_of_eventual_band hpre
    hw hbw hrw (fun k => (hf k).1) hbk (fun k => (hf k).2.1)
    (ε := 0) (t := t) bot_le
    (fk := fun k => seedMapBandIncrement d ε (E k) (S k) t)
    (fun k => seedMap_original_event_Ito hκ hε hdW hdκ (hST k) (hown k) (hconst k)
      (hF k) hB hBc (hρ k) (hS k) (hmA k) (hmRate k) hεt) (f := fun ω =>
      (d ω).A 0 (min t (T ω)) - (d ω).A 0 (min ε (T ω)) -
        (∫ u in (min ε (T ω) : ℝ≥0)..(min t (T ω) : ℝ≥0), (d ω).d10Rate u)) (by
    apply ae_of_all
    intro ω
    by_cases he : ε ≤ T ω
    · filter_upwards [hstage ω he] with k hk
      have hle : ε ≤ S k ω := by simpa only [onEvS_of_mem hk.1] using (hF k).le ω
      refine ⟨fun u _ => seedMapBandCoeff_agrees hdW hε hk.1 hle hk.2 u, ?_⟩
      simp only [seedMapBandIncrement, indicator_of_mem hk.1, hk.2, min_eq_left he,
        min_eq_left (NNReal.coe_le_coe.2 he)]
    · apply Eventually.of_forall
      intro k
      have hnot : ω ∉ E k := by
        intro hω
        have hh := (hF k).le ω
        rw [onEvS_of_mem hω] at hh
        exact he (hh.trans (hST k ω hω))
      have hlt : T ω < ε := lt_of_not_ge he
      have heq (u : ℝ≥0) : w u ω = 0 := by
        dsimp only [w, z, v]
        by_cases hu : ε ≤ u
        · have hn : ¬u ≤ T ω := not_le_of_gt (hlt.trans_le hu)
          simp only [seedEndWindow, hu, seedFin2Endpoint, positiveStopped,
            hn, and_false, ite_false, ite_self]
        · simp only [seedEndWindow, hu, ite_false]
      refine ⟨fun u _ => (seedMapBandCoeff_off d κ B D ε (S k) hnot u).trans (heq u).symm, ?_⟩
      simp only [seedMapBandIncrement, indicator_of_notMem hnot,
        min_eq_right hlt.le, min_eq_right (hlt.le.trans hεt),
        min_eq_right (NNReal.coe_le_coe.2 hlt.le),
        min_eq_right (NNReal.coe_le_coe.2 (hlt.le.trans hεt)), sub_self,
        intervalIntegral.integral_same])
  have hp := isStronglyPredictable_positiveStopped 𝓕
    (X := fun u ω => Real.sqrt κ * (d ω).A 1 u) (S := T)
    (fun u => by
      convert (hm u).const_mul (Real.sqrt κ) using 1
      funext ω
      by_cases hu : u ≤ T ω <;> simp [indicator, hu])
    (fun ω => continuousOn_const.mul (hc ω))
  have hrv : IsRiemannRegular P v := isRiemannRegular_positiveStopped P
    (fun ω => continuousOn_const.mul (hc ω))
  have hbvp : ∀ u ω, |v u ω| ≤ |Real.sqrt κ| * C := by
    intro u ω
    dsimp only [v]
    unfold positiveStopped
    split_ifs with hu
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb u ω hu.1 hu.2) (abs_nonneg _)
    · simpa only [abs_zero] using mul_nonneg (abs_nonneg (Real.sqrt κ)) hC
  have hC' := mul_nonneg (abs_nonneg (Real.sqrt κ)) hC
  have hwin := seed_stochIntegral_window hpre hBc
    (seedFin2Endpoint_adapted hT hp.stronglyAdapted) (abs_seedFin2Endpoint_le hC' hbvp)
    (seedFin2Endpoint_regular hrv) hεt
  have het := seed_stochIntegral_endpoint hpre hBc hT
    hp.stronglyAdapted hC' hbvp hrv t
  have hee := seed_stochIntegral_endpoint hpre hBc hT
    hp.stronglyAdapted hC' hbvp hrv ε
  have hz := seedStochIntegral_zero_ae hpre hw hbw hrw
  filter_upwards [hlim, hwin, het, hee, hz] with ω hl hw' ht' he' hz'
  change _ = stochIntegral P 𝓕 B v t ω - stochIntegral P 𝓕 B v ε ω
  change _ = stochIntegral P 𝓕 B w t ω - stochIntegral P 𝓕 B w 0 ω at hl
  rw [hz', sub_zero, hw', ht', he'] at hl
  exact hl

end InteractingSLE.ZhanGT4
