/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageIntegral

/-!
# The Doléans identity, including the seed entrance limit

Packet PROVE-ZHAN-GT4-A22. The remaining local stochastic-calculus input
is the positive-time random-field Itô identity, stated explicitly below.
The entrance passage is proved from the bounded-noise isometry; it is not
an additional input. The change of measure uses the original filtration.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The positive-time random-field Itô calculation after removing the finite
gap bands. This is the precise remaining calculus input, distinct from a
terminal density identity or an image-law statement. -/
def SeedPositiveLogIto {n : ℕ} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (B θ : ℝ≥0 → Ω → ℝ) (d : Ω → SeedData n) (S : Ω → ℝ≥0) : Prop :=
  ∀ ε t : ℝ≥0, 0 < ε → ε ≤ t →
    (fun ω => (d ω).normEll (min t (S ω)) - (d ω).normEll (min ε (S ω))) =ᵐ[P]
      fun ω => -(Girsanov.stochIntegral P 𝓕 B θ t ω - Girsanov.stochIntegral P 𝓕 B θ ε ω) -
        (Girsanov.quadInt θ t ω - Girsanov.quadInt θ ε ω) / 2

/-- The quadratic integral of bounded progressive noise is continuous at
all times; in particular it tends to zero at the entrance. -/
theorem continuous_seedQuadInt {𝓕 : Filtration ℝ≥0 mΩ}
    {θ : ℝ≥0 → Ω → ℝ} (hθ : IsStronglyProgressive 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (ω : Ω) :
    Continuous (Girsanov.quadInt θ · ω) := by
  have hθ₂ : IsStronglyProgressive 𝓕 (fun u ω => θ u ω ^ 2) := fun t => (hθ t).pow 2
  have hb₂ : ∀ u ω, |θ u ω ^ 2| ≤ C ^ 2 := fun u ω => by
    simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hb u ω) 2
  exact Girsanov.continuous_drift hθ₂ hb₂ ω

/-- The stochastic integral starts at zero, with its actual chosen version. -/
theorem seedStochIntegral_zero_ae {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownian B 𝓕 P) (hm : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hreg : Girsanov.IsRiemannRegular P θ) :
    Girsanov.stochIntegral P 𝓕 B θ 0 =ᵐ[P] fun _ => 0 := by
  apply (eLpNorm_eq_zero_iff
    (Girsanov.memLp_stochIntegral hB hm hb hreg 0).aestronglyMeasurable two_ne_zero).1
  have hh := eLpNorm_seedStochIntegral_le hB hm hb hreg 0
  simpa only [NNReal.coe_zero, mul_zero, Real.sqrt_zero, ENNReal.ofReal_zero, le_zero_iff] using hh

/-- Extend the positive-time stochastic logarithm through the seed entrance.
No stochastic-integral continuity at zero is assumed. -/
theorem seed_log_doleans_ae_of_positiveIto {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownian B 𝓕 P) (hθ : IsStronglyProgressive 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hreg : Girsanov.IsRiemannRegular P θ)
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω)))
    (hIto : SeedPositiveLogIto P 𝓕 B θ d S) (t : ℝ≥0) :
    (fun ω => (d ω).normEll (min t (S ω)) - (d ω).normEll 0) =ᵐ[P]
      fun ω => -Girsanov.stochIntegral P 𝓕 B θ t ω - Girsanov.quadInt θ t ω / 2 := by
  by_cases ht : t = 0
  · subst t
    filter_upwards [seedStochIntegral_zero_ae hB hθ.stronglyAdapted hb hreg] with ω hω
    simp only [NNReal.coe_zero, min_eq_left (S ω).coe_nonneg, sub_self, hω,
      Girsanov.quadInt, intervalIntegral.integral_same, neg_zero, zero_div]
  have htp : 0 < t := lt_of_le_of_ne (zero_le (a := t)) (Ne.symm ht)
  let ε : ℕ → ℝ≥0 := fun k => t / (k + 1)
  have hεp : ∀ k, 0 < ε k := fun k => div_pos htp (by positivity)
  have hεt : ∀ k, ε k ≤ t := fun k => div_le_self (zero_le (a := t)) (le_add_of_nonneg_left (zero_le (a := (k : ℝ≥0))))
  have hε : Tendsto ε atTop (𝓝 0) := by
    have he := (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)).comp (tendsto_add_atTop_nat 1)
    have he' : Tendsto (fun k : ℕ => ((ε k : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, ε, NNReal.coe_div,
        NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using he
    exact NNReal.tendsto_coe.1 he'
  obtain ⟨ns, hns, hlim⟩ :=
    (tendstoInMeasure_seedStochIntegral_zero hB hθ.stronglyAdapted hb hreg hε).exists_seq_tendsto_ae
  have hids : ∀ᵐ ω ∂P, ∀ k, (d ω).normEll (min t (S ω)) - (d ω).normEll (min (ε (ns k)) (S ω)) =
      -(Girsanov.stochIntegral P 𝓕 B θ t ω - Girsanov.stochIntegral P 𝓕 B θ (ε (ns k)) ω) -
        (Girsanov.quadInt θ t ω - Girsanov.quadInt θ (ε (ns k)) ω) / 2 :=
    ae_all_iff.2 fun k => hIto _ _ (hεp _) (hεt _)
  filter_upwards [hlim, hids] with ω hω hidsω
  have he := hε.comp hns.tendsto_atTop
  have hn : Tendsto (fun k => (d ω).normEll (min (ε (ns k)) (S ω))) atTop (𝓝 ((d ω).normEll 0)) := by
    apply (hc ω 0 ⟨le_rfl, (S ω).coe_nonneg⟩).tendsto.comp
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hecoe : Tendsto (fun k => (ε (ns k) : ℝ)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, NNReal.coe_zero] using
          NNReal.continuous_coe.continuousAt.tendsto.comp he
      simpa only [min_eq_left (S ω).coe_nonneg] using
        hecoe.min (tendsto_const_nhds (x := (S ω : ℝ)))
    · exact Eventually.of_forall fun k => ⟨(min (ε (ns k)) (S ω)).coe_nonneg,
        by exact_mod_cast min_le_right (ε (ns k)) (S ω)⟩
  have hq : Tendsto (fun k => Girsanov.quadInt θ (ε (ns k)) ω) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Girsanov.quadInt, NNReal.coe_zero, intervalIntegral.integral_same] using
      (continuous_seedQuadInt hθ hb ω).continuousAt.tendsto.comp he
  have hleft := (tendsto_const_nhds (x := (d ω).normEll (min (t : ℝ) (S ω)))).sub hn
  have hright := ((tendsto_const_nhds (x := Girsanov.stochIntegral P 𝓕 B θ t ω)).sub hω).neg.sub
    (((tendsto_const_nhds (x := Girsanov.quadInt θ t ω)).sub hq).div_const 2)
  have heq := tendsto_nhds_unique hleft (hright.congr fun k => (hidsω k).symm)
  simpa only [sub_zero] using heq

/-- The actual normalized seeded density equals the general-filtration
Doléans exponential once the positive-time random-field Itô step is supplied. -/
theorem seedDensity_eq_doleans_of_positiveIto {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredPreBrownian B 𝓕 P) (hθ : IsStronglyProgressive 𝓕 θ)
    {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C) (hreg : Girsanov.IsRiemannRegular P θ)
    {d : Ω → SeedData n} {S : Ω → ℝ≥0}
    (hc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (S ω)))
    (hIto : SeedPositiveLogIto P 𝓕 B θ d S) {U : ℝ≥0} (hSU : ∀ ω, S ω ≤ U) :
    seedDensity d S =ᵐ[P] Girsanov.doleansDensity P 𝓕 B θ U := by
  filter_upwards [seed_log_doleans_ae_of_positiveIto hB hθ hb hreg hc hIto U] with ω hω
  exact congrArg Real.exp (by simpa only [min_eq_right (NNReal.coe_le_coe.2 (hSU ω))] using hω)

end InteractingSLE.ZhanGT4
