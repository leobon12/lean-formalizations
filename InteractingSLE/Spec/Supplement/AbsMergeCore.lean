/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.BrownianMotion.Basic
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal

/-!
# Lévy's 0–1 law against a fresh Gaussian increment

Packet PROVE-ABSMERGE (the probabilistic core of `FixedTimeAbsorbedMergeStatement`). Abstract; no SLE here.

Let `B` be a Brownian motion of the filtration `𝓕`, let `t > 0`, and let `a_n = t − t/2^{n+1}` (`grid`), so that the
normalized increments `Z_n = (B_t − B_{a_n}) / √(t − a_n)` (`normIncr`) are standard Gaussian and independent of
`𝓕_{a_n}`. Let `G` be an event of `⨆ₙ 𝓕_{a_n}` and `x_n` an `𝓕_{a_n}`-measurable variable such that, almost surely
on `G`,

* (lower bound) `x_n − c ≤ Z_n` for all `n ≥ N`, and
* (upper bound) `x_n → −∞` forces `Z_n → −∞`.

Then `P(G) = 0` (**`measure_eq_zero_of_lowerBound`**). Proof: by Lévy's upward theorem
(`Integrable.tendsto_ae_condExp`) `P(G | 𝓕_{a_n}) → 1` on `G`; by independence `P(G | 𝓕_{a_n}) ≤ P(Z ≥ −K − c) < 1`
wherever `x_n ≥ −K` (`ae_condExp_le_of_lowerBound`), so `x_n → −∞` on `G`; hence `Z_n → −∞` on `G`, an event of
probability `0` because every `Z_n` is standard Gaussian (`measure_tendsto_normIncr_atBot`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace AbsMerge

/-! ### The grid `a_n = t − t/2^{n+1}` -/

/-- The grid `a_n = t − t/2^{n+1}`, increasing to `t`. -/
def grid (t : ℝ≥0) (n : ℕ) : ℝ≥0 := t - t / 2 ^ (n + 1)

theorem div_two_pow_le (t : ℝ≥0) (n : ℕ) : t / 2 ^ (n + 1) ≤ t :=
  div_le_self zero_le (one_le_pow₀ one_le_two)

theorem coe_grid (t : ℝ≥0) (n : ℕ) : (grid t n : ℝ) = t - t / 2 ^ (n + 1) := by
  rw [grid, NNReal.coe_sub (div_two_pow_le t n), NNReal.coe_div, NNReal.coe_pow, NNReal.coe_two]

theorem sub_grid (t : ℝ≥0) (n : ℕ) : (t : ℝ) - grid t n = t / 2 ^ (n + 1) := by
  rw [coe_grid]; ring

theorem sub_grid_pos {t : ℝ≥0} (ht : 0 < t) (n : ℕ) : 0 < (t : ℝ) - grid t n := by
  rw [sub_grid]; positivity

theorem sub_grid_succ (t : ℝ≥0) (n : ℕ) : (t : ℝ) - grid t (n + 1) = ((t : ℝ) - grid t n) / 2 := by
  rw [sub_grid, sub_grid, pow_succ]
  field_simp

theorem grid_lt {t : ℝ≥0} (ht : 0 < t) (n : ℕ) : grid t n < t := by
  have := sub_grid_pos ht n
  exact_mod_cast (by linarith : (grid t n : ℝ) < t)

theorem grid_mono (t : ℝ≥0) : Monotone (grid t) := by
  intro m n h
  have h2 : (2 : ℝ) ^ (m + 1) ≤ 2 ^ (n + 1) := pow_le_pow_right₀ one_le_two (by omega)
  have : (t : ℝ) / 2 ^ (n + 1) ≤ t / 2 ^ (m + 1) := div_le_div_of_nonneg_left t.2 (by positivity) h2
  rw [← NNReal.coe_le_coe, coe_grid, coe_grid]
  linarith

theorem tendsto_sub_grid (t : ℝ≥0) : Tendsto (fun n => (t : ℝ) - grid t n) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h2 := (h.const_mul (t : ℝ)).comp (tendsto_add_atTop_nat 1)
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, sub_grid, div_eq_mul_inv, one_mul, inv_pow]

theorem tendsto_coe_grid (t : ℝ≥0) : Tendsto (fun n => (grid t n : ℝ)) atTop (𝓝 t) := by
  have := (tendsto_sub_grid t).const_sub (t : ℝ)
  rw [sub_zero] at this
  exact this.congr fun n => by ring

theorem tendsto_grid (t : ℝ≥0) : Tendsto (grid t) atTop (𝓝 t) :=
  NNReal.tendsto_coe.1 (tendsto_coe_grid t)

/-- The filtration `n ↦ 𝓕_{a_n}`. -/
def gridFiltration {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    Filtration ℕ mΩ where
  seq n := 𝓕 (grid t n)
  mono' _ _ h := 𝓕.mono (grid_mono t h)
  le' _ := 𝓕.le _

/-- The normalized increment `Z_n = (B_t − B_{a_n}) / √(t − a_n)`. -/
def normIncr {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  (B t ω - B (grid t n) ω) / Real.sqrt ((t : ℝ) - grid t n)

/-! ### Gaussian facts -/

/-- A standard Gaussian gives mass `< 1` to every closed right half-line. -/
theorem gaussianReal_Ici_lt_one (y : ℝ) : gaussianReal 0 1 (Ici y) < 1 := by
  have hpos : gaussianReal 0 1 (Iio y) ≠ 0 := by
    intro h
    have h0 := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
    rw [Real.volume_Iio] at h0
    exact ENNReal.top_ne_zero h0
  refine lt_of_le_of_ne prob_le_one fun h => hpos ?_
  rw [← compl_Ici, prob_compl_eq_one_sub measurableSet_Ici, h, tsub_self]

theorem toReal_gaussianReal_Ici_lt_one (y : ℝ) : (gaussianReal 0 1 (Ici y)).toReal < 1 := by
  have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 (gaussianReal_Ici_lt_one y)
  rwa [ENNReal.toReal_one] at this

/-- The mass of `(−∞, −K]` under a standard Gaussian tends to `0`. -/
theorem tendsto_gaussianReal_Iic : Tendsto (fun K : ℕ => gaussianReal 0 1 (Iic (-(K : ℝ)))) atTop (𝓝 0) := by
  have hanti : Antitone fun K : ℕ => Iic (-(K : ℝ)) :=
    fun K K' h => Iic_subset_Iic.2 (neg_le_neg (Nat.cast_le.2 h))
  have hinter : (⋂ K : ℕ, Iic (-(K : ℝ))) = ∅ := by
    ext y
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨K, hK⟩ := exists_nat_gt (-y)
    exact ⟨K, by linarith⟩
  have := tendsto_measure_iInter_atTop (μ := gaussianReal 0 1)
    (fun K => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rwa [hinter, measure_empty] at this

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}

omit [IsProbabilityMeasure P] in
/-- The normalized increments are standard Gaussian. -/
theorem hasLaw_normIncr (hB : IsFilteredBrownianReal 𝓕 B P) (ht : 0 < t) (n : ℕ) :
    HasLaw (normIncr B t n) (gaussianReal 0 1) P := by
  set v : ℝ := (t : ℝ) - grid t n with hv_def
  have hv : 0 < v := sub_grid_pos ht n
  have h1 : HasLaw (B t - B (grid t n)) (gaussianReal 0 (nndist (t : ℝ) (grid t n))) P :=
    hB.1.toIsPreBrownianReal.hasLaw_sub t (grid t n)
  have hnd : nndist (t : ℝ) (grid t n) = v.toNNReal := by
    ext
    rw [coe_nndist, Real.dist_eq, abs_of_pos hv, Real.coe_toNNReal _ hv.le]
  have h2 : HasLaw (fun y : ℝ => (Real.sqrt v)⁻¹ * y) (gaussianReal 0 1)
      (gaussianReal 0 (nndist (t : ℝ) (grid t n))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul, mul_zero, hnd]
    congr 1
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_one, NNReal.coe_mk, Real.coe_toNNReal _ hv.le]
    rw [inv_pow, Real.sq_sqrt hv.le, inv_mul_cancel₀ hv.ne']
  refine (h2.comp h1).congr (ae_of_all _ fun ω => ?_)
  simp only [normIncr, Function.comp_apply, Pi.sub_apply, div_eq_inv_mul, hv_def]

omit [IsProbabilityMeasure P] in
/-- **The normalized increments do not tend to `−∞`** (almost surely). -/
theorem measure_tendsto_normIncr_atBot (hB : IsFilteredBrownianReal 𝓕 B P) (ht : 0 < t) :
    P {ω | Tendsto (fun n => normIncr B t n ω) atTop atBot} = 0 := by
  have hle : ∀ K : ℕ, P {ω | Tendsto (fun n => normIncr B t n ω) atTop atBot} ≤
      gaussianReal 0 1 (Iic (-(K : ℝ))) := by
    intro K
    set s : ℕ → Set Ω := fun M => {ω | ∀ n, M ≤ n → normIncr B t n ω ≤ -(K : ℝ)}
    have hmono : Monotone s := fun M M' h ω hω n hn => hω n (h.trans hn)
    have hsub : {ω | Tendsto (fun n => normIncr B t n ω) atTop atBot} ⊆ ⋃ M, s M := fun ω hω => by
      obtain ⟨M, hM⟩ := eventually_atTop.1 (tendsto_atBot.1 hω (-(K : ℝ)))
      exact mem_iUnion.2 ⟨M, hM⟩
    have hs : ∀ M, P (s M) ≤ gaussianReal 0 1 (Iic (-(K : ℝ))) := fun M => by
      calc P (s M) ≤ P {ω | normIncr B t M ω ≤ -(K : ℝ)} := measure_mono fun ω hω => hω M le_rfl
        _ = gaussianReal 0 1 {y | y ≤ -(K : ℝ)} := (hasLaw_normIncr hB ht M).measure_eq measurableSet_Iic
        _ = gaussianReal 0 1 (Iic (-(K : ℝ))) := rfl
    calc P {ω | Tendsto (fun n => normIncr B t n ω) atTop atBot} ≤ P (⋃ M, s M) := measure_mono hsub
      _ ≤ gaussianReal 0 1 (Iic (-(K : ℝ))) := le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hs
  exact le_antisymm (ge_of_tendsto' tendsto_gaussianReal_Iic hle) (by positivity)

/-- **The conditional probability given `𝓕_{a_n}` is at most `P(Z ≥ −K − c)` where `x_n ≥ −K`**, when `x_n − c ≤ Z_n`
almost surely on `G`. -/
theorem ae_condExp_le_of_lowerBound (hB : IsFilteredBrownianReal 𝓕 B P) (ht : 0 < t) {G : Set Ω}
    (hGm : MeasurableSet G) {n : ℕ} {x : Ω → ℝ} (hx : Measurable[𝓕 (grid t n)] x) {c K : ℝ}
    (hlow : ∀ᵐ ω ∂P, ω ∈ G → x ω - c ≤ normIncr B t n ω) :
    ∀ᵐ ω ∂P, -K ≤ x ω →
      (P[G.indicator (fun _ => (1 : ℝ)) | 𝓕 (grid t n)]) ω ≤ (gaussianReal 0 1 (Ici (-K - c))).toReal := by
  have hm : 𝓕 (grid t n) ≤ mΩ := 𝓕.le _
  set f := P[G.indicator (fun _ => (1 : ℝ)) | 𝓕 (grid t n)] with hf_def
  set q := (gaussianReal 0 1 (Ici (-K - c))).toReal with hq_def
  have hfm : StronglyMeasurable[𝓕 (grid t n)] f := stronglyMeasurable_condExp
  set A := {ω | -K ≤ x ω} ∩ {ω | q < f ω} with hA_def
  have hAm : MeasurableSet[𝓕 (grid t n)] A :=
    (measurableSet_le measurable_const hx).inter (measurableSet_lt measurable_const hfm.measurable)
  have hAm' : MeasurableSet A := hm _ hAm
  suffices hA : P A = 0 by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hA] with ω hω hxω
    exact not_lt.1 fun h => hω ⟨hxω, h⟩
  have hint : Integrable (G.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hGm
  -- `∫_A f = P(A ∩ G)`
  have hI : ∫ ω in A, f ω ∂P = P.real (A ∩ G) := by
    rw [hf_def, setIntegral_condExp hm hint hAm, setIntegral_indicator hGm, setIntegral_const, smul_eq_mul,
      mul_one]
  -- independence: `P(A ∩ {Z_n ≥ −K − c}) = P(A) · P(Z ≥ −K − c)`
  have hind := (Indep_iff _ _ P).1 (hB.2.2 (grid t n) t (grid_lt ht n).le)
  set E := {ω | -K - c ≤ normIncr B t n ω} with hE_def
  have hEc : MeasurableSet[MeasurableSpace.comap (fun ω => B t ω - B (grid t n) ω) inferInstance] E := by
    refine ⟨(fun y : ℝ => y / Real.sqrt ((t : ℝ) - grid t n)) ⁻¹' Ici (-K - c),
      measurableSet_Ici.preimage (measurable_id.div_const _), ?_⟩
    ext ω
    simp only [mem_preimage, mem_Ici, hE_def, Set.mem_ofPred_eq, normIncr]
  have hPE : P E = gaussianReal 0 1 (Ici (-K - c)) := (hasLaw_normIncr hB ht n).measure_eq measurableSet_Ici
  have hle : P.real (A ∩ G) ≤ q * P.real A := by
    have h1 : P (A ∩ G) ≤ P (E ∩ A) := by
      refine measure_mono_ae ?_
      filter_upwards [hlow] with ω hω hmem
      have h3 := hω hmem.2
      have h4 : -K ≤ x ω := hmem.1.1
      exact ⟨show -K - c ≤ normIncr B t n ω by linarith, hmem.1⟩
    rw [hind E A hEc hAm, hPE] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) h1
    rwa [ENNReal.toReal_mul] at h2
  by_contra hA
  have hApos : 0 < P A := pos_iff_ne_zero.2 hA
  have hfi : IntegrableOn (fun ω => f ω - q) A P := (integrable_condExp.sub (integrable_const q)).integrableOn
  have hnn : 0 ≤ᵐ[P.restrict A] fun ω => f ω - q :=
    ae_restrict_of_forall_mem hAm' fun ω hω => (sub_pos.2 hω.2).le
  have hsupp : Function.support (fun ω => f ω - q) ∩ A = A :=
    inter_eq_right.2 fun ω hω => (sub_pos.2 hω.2).ne'
  have hpos := (setIntegral_pos_iff_support_of_nonneg_ae hnn hfi).2 (by rwa [hsupp])
  rw [integral_sub integrable_condExp.integrableOn (integrable_const q), setIntegral_const, smul_eq_mul, hI]
    at hpos
  linarith [mul_comm q (P.real A)]

/-- **Lévy's 0–1 law against a fresh Gaussian increment.** If `G ∈ ⨆ₙ 𝓕_{a_n}` and `𝓕_{a_n}`-measurable `x_n` satisfy,
almost surely on `G`, `x_n − c ≤ Z_n` for `n ≥ N` and `x_n → −∞ ⇒ Z_n → −∞`, then `P(G) = 0`. -/
theorem measure_eq_zero_of_lowerBound (hB : IsFilteredBrownianReal 𝓕 B P) (ht : 0 < t) {G : Set Ω}
    (hG : MeasurableSet[⨆ n, 𝓕 (grid t n)] G) {x : ℕ → Ω → ℝ}
    (hx : ∀ n, Measurable[𝓕 (grid t n)] (x n)) {c : ℝ} {N : ℕ}
    (hlow : ∀ᵐ ω ∂P, ω ∈ G → ∀ n, N ≤ n → x n ω - c ≤ normIncr B t n ω)
    (hup : ∀ᵐ ω ∂P, ω ∈ G → Tendsto (fun n => x n ω) atTop atBot →
      Tendsto (fun n => normIncr B t n ω) atTop atBot) : P G = 0 := by
  set ℱ := gridFiltration 𝓕 t with hℱ
  have hle : (⨆ n, 𝓕 (grid t n)) ≤ mΩ := iSup_le fun n => 𝓕.le _
  have hGm : MeasurableSet G := hle _ hG
  set g : Ω → ℝ := G.indicator fun _ => 1 with hg_def
  have hint : Integrable g P := (integrable_const (1 : ℝ)).indicator hGm
  have hgm : StronglyMeasurable[⨆ n, ℱ n] g :=
    StronglyMeasurable.indicator stronglyMeasurable_const hG
  have hlev := hint.tendsto_ae_condExp hgm
  have hbd : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ n, N ≤ n → -(K : ℝ) ≤ x n ω →
      (P[g | ℱ n]) ω ≤ (gaussianReal 0 1 (Ici (-(K : ℝ) - c))).toReal := by
    rw [ae_all_iff]
    intro K
    rw [ae_all_iff]
    intro n
    by_cases hn : N ≤ n
    · have := ae_condExp_le_of_lowerBound hB ht hGm (hx n) (K := K) (c := c)
        (hlow.mono fun ω h hω => h hω n hn)
      filter_upwards [this] with ω h _ hxω
      exact h hxω
    · exact ae_of_all _ fun ω h => absurd h hn
  have hxbot : ∀ᵐ ω ∂P, ω ∈ G → Tendsto (fun n => x n ω) atTop atBot := by
    filter_upwards [hlev, hbd] with ω hl hb hω
    have hg1 : g ω = 1 := indicator_of_mem hω _
    rw [hg1] at hl
    rw [tendsto_atBot]
    intro y
    obtain ⟨K, hK⟩ := exists_nat_ge (-y)
    have hev : ∀ᶠ n in atTop, (gaussianReal 0 1 (Ici (-(K : ℝ) - c))).toReal < (P[g | ℱ n]) ω :=
      hl.eventually (lt_mem_nhds (toReal_gaussianReal_Ici_lt_one _))
    filter_upwards [hev, eventually_ge_atTop N] with n h1 h2
    by_contra hcon
    have := hb K n h2 (by linarith [not_le.1 hcon])
    linarith
  refine le_antisymm ?_ (by positivity)
  calc P G ≤ P {ω | Tendsto (fun n => normIncr B t n ω) atTop atBot} := by
        refine measure_mono_ae ?_
        filter_upwards [hxbot, hup] with ω h1 h2 hω
        exact h2 hω (h1 hω)
    _ = 0 := measure_tendsto_normIncr_atBot hB ht

end Prob

end AbsMerge

end Theorem14

end InteractingSLE
