/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Band
import InteractingSLE.Spec.ZhanGT4.DualSeedEndRemove

/-!
# Removal of the actual seeded bands in the original logarithmic formula

Packet PROVE-ZHAN-GT4-A22. The actual coefficient and compensated-log
stage equalities are proved, including the complementary event. A21's
gap-band exhaustion removes the stopping localization path by path.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ : ℝ} {n : ℕ} {d : Ω → SeedData n} {B D : ℝ≥0 → Ω → ℝ}
  {ε t R : ℝ≥0} {T : Ω → ℝ≥0} {Y : SeedGap n → ℝ≥0 → Ω → ℝ}

/-- The actual local fields suffice for the positive-time normalized
logarithm; stage agreement and all stochastic limit estimates are proved. -/
theorem seed_logIto_at_of_actual_bands (hκ : 0 < κ) (hε : 0 < ε) (hεt : ε ≤ t)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) (hTR : ∀ ω, T ω ≤ ε + R)
    (hYc : ∀ i ω, Continuous (Y i · ω)) (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hYv : ∀ ω i (u : ℝ≥0), ε ≤ u → u ≤ T ω → Y i u ω = (d ω).gapVal i u)
    (hne : ∀ ω i u, u ∈ Ioc (0 : ℝ) (T ω) → (d ω).gapVal i u ≠ 0)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hr : IsRiemannRegular P (seedNoise κ d T))
    (hfields : ∀ k : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      let E := bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
      let S := bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T
      IsDriftLogField 𝓕 (Real.sqrt κ) ρ K B D (onEvB E (fun ω => (d ω).drift)) ε (onEvS E ε S)
        (onEv E (fun ω => (d ω).ell)) (onEv E (fun ω => (d ω).ellX))
        (onEv E (fun ω => (d ω).ellXX)) (onEv E (fun ω => (d ω).ellXXX))
        (onEv E (fun ω => (d ω).ellT))) :
    (fun ω => (d ω).normEll (min t (T ω)) - (d ω).normEll (min ε (T ω))) =ᵐ[P]
      fun ω => -(stochIntegral P 𝓕 B (seedNoise κ d T) t ω -
        stochIntegral P 𝓕 B (seedNoise κ d T) ε ω) -
        (quadInt (seedNoise κ d T) t ω - quadInt (seedNoise κ d T) ε ω) / 2 := by
  classical
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hpre := isFilteredPreBrownian_of_isFilteredBrownianReal hB
  let E (k : ℕ) := bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
  let S (k : ℕ) := bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T
  choose ρ K hρ hK hL using hfields
  have hS (k : ℕ) : IsStoppingTime 𝓕 fun ω => (onEvS (E k) ε (S k) ω : WithTop ℝ≥0) :=
    isStoppingTime_onEvS (isStoppingTime_bandExit hYc hYm hT) le_bandExit (measurableSet_bandEv hYm hT)
  let wk (k : ℕ) := seedFin2BandCoeff d κ B D ε (E k) (S k)
  let fk (k : ℕ) (ω : Ω) := seedFin2BandProcess d κ B D ε (E k) (S k) t ω -
    seedFin2BandProcess d κ B D ε (E k) (S k) 0 ω
  have hfacts (k : ℕ) : StronglyAdapted 𝓕 (wk k) ∧ IsRiemannRegular P (wk k) ∧
      ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ u ω, |wk k u ω| ≤ Ck :=
    (hL k).seed_original_coef_facts hBc (Real.sqrt_pos.2 hκ) (hρ k) (hS k)
  choose Ck hCk hbk using fun k => (hfacts k).2.2
  let w : ℝ≥0 → Ω → ℝ := fun u ω => -seedNoise κ d T u ω
  have hw : StronglyAdapted 𝓕 w := fun u => (hp.stronglyAdapted u).neg
  have hbw (u : ℝ≥0) (ω : Ω) : |w u ω| ≤ C := by simpa only [w, abs_neg] using hb u ω
  have hrw : IsRiemannRegular P w := hr.mono fun ω hω => hω.mono fun _ hu => hu.neg
  let v := seedFin2Endpoint T w
  have hv := seedFin2Endpoint_adapted hT hw
  have hbv := abs_seedFin2Endpoint_le (S := T) hC hbw
  have hrv := seedFin2Endpoint_regular (S := T) hrw
  let win := seedEndWindow ε v
  have hwin := seedEndWindow_adapted (ε := ε) hv
  have hrwin := seedEndWindow_isRiemannRegular (ε := ε) hrv
  have hbwin (u : ℝ≥0) (ω : Ω) : |win u ω| ≤ C := by
    unfold win seedEndWindow
    split_ifs
    · exact hbv _ _
    · simpa only [abs_zero] using hC
  let f (ω : Ω) := (d ω).normEll (min t (T ω)) - (d ω).normEll (min ε (T ω)) +
    (quadInt (seedNoise κ d T) t ω - quadInt (seedNoise κ d T) ε ω) / 2
  have hstage : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, (∀ u ≤ t, wk k u ω = win u ω) ∧ fk k ω = f ω := by
    apply Eventually.of_forall
    intro ω
    by_cases hεT : ε ≤ T ω
    · have hneY : ∀ i u, ε ≤ u → u ≤ T ω → Y i u ω ≠ 0 := by
        intro i u hεu hu
        rw [hYv ω i u hεu hu]
        exact hne ω i u ⟨NNReal.coe_pos.2 (hε.trans_le hεu), hu⟩
      filter_upwards [eventually_bandEv_bandExit_eq hYc hεT (hTR ω) hneY] with k hk
      refine ⟨fun u _ => seedFin2Band_coef_agrees hdW hk.1 hε (le_bandExit ω) hk.2 u, ?_⟩
      have hh := seed_band_log_agreement hκ.le hε hεt hdW hp hb (hL k) hk.1 hk.2 (hne ω)
      simpa only [fk, f, E, S, seedFin2BandProcess, NNReal.coe_min,
        min_eq_left (show (ε : ℝ) ≤ T ω from hεT)] using hh
    · have hTε := le_of_not_ge hεT
      have hf0 : f ω = 0 := by
        dsimp only [f]
        rw [min_eq_right (show (T ω : ℝ) ≤ t from hTε.trans hεt),
          min_eq_right (show (T ω : ℝ) ≤ ε from hTε),
          seedNoise_quadInt_sub_of_horizon_le hp hb hεt ω hTε]
        ring
      apply Eventually.of_forall
      intro k
      have hnot : ω ∉ E k := fun hh => hεT hh.1
      refine ⟨?_, ?_⟩
      · intro u _
        change seedFin2BandCoeff d κ B D ε (E k) (S k) u ω = _
        rw [(seedFin2Band_zero hnot u).1]
        change 0 = seedEndWindow ε (seedFin2Endpoint T w) u ω
        unfold seedEndWindow seedFin2Endpoint w
        by_cases hu : ε ≤ u
        · have hut : ¬ u ≤ T ω := not_le_of_gt ((lt_of_not_ge hεT).trans_le hu)
          simp only [hu, seedNoise, positiveStopped, hut, and_false, ite_false, neg_zero, ite_self]
        · simp only [hu, ite_false]
      · dsimp only [fk]
        rw [(seedFin2Band_zero hnot t).2, (seedFin2Band_zero hnot 0).2, hf0, sub_self]
  have hIto (k : ℕ) : fk k =ᵐ[P] fun ω =>
      stochIntegral P 𝓕 B (wk k) t ω - stochIntegral P 𝓕 B (wk k) 0 ω :=
    (hL k).seed_original_stochIntegral hB hBc (Real.sqrt_pos.2 hκ) (hρ k) (hS k) t
  have hremove := seed_stochIntegral_sub_eq_of_eventual_band hpre hwin hbwin hrwin
    (fun k => (hfacts k).1) hbk (fun k => (hfacts k).2.1) (ε := 0) (t := t) bot_le hIto hstage
  have hneg (u : ℝ≥0) : stochIntegral P 𝓕 B w u =ᵐ[P]
      fun ω => -stochIntegral P 𝓕 B (seedNoise κ d T) u ω := by
    simpa only [neg_one_mul] using seed_stochIntegral_const_mul hpre hp.stronglyAdapted hb hr (-1) u
  filter_upwards [hremove, seedStochIntegral_zero_ae hpre hwin hbwin hrwin,
    seed_stochIntegral_window hpre hBc hv hbv hrv hεt,
    seed_stochIntegral_endpoint hpre hBc hT hw hC hbw hrw t,
    seed_stochIntegral_endpoint hpre hBc hT hw hC hbw hrw ε, hneg t, hneg ε]
    with ω hh h0 hcut het heε hnt hnε
  change f ω = _ at hh
  rw [h0, sub_zero, hcut, het, heε, hnt, hnε] at hh
  dsimp only [f] at hh
  linarith only [hh]

end InteractingSLE.ZhanGT4
