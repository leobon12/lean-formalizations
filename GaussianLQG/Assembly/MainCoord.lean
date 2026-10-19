import GaussianLQG.Core.Interfaces
import GaussianLQG.Probability.Medians
import GaussianLQG.LQG.Exponents
import GaussianLQG.Assembly.MainCoord.Limits
import LQGMetric.Papers.GM.S1.Assembly

/-!
# Proof of Theorem `thm:main` in coordinates (blueprint §7, Steps 1–6)

For an arbitrary `S : Setup` we derive the conclusions of the main theorem (blueprint Theorem
`thm:main`; source Theorem 1.1) from the four interface propositions of `Core/Interfaces.lean`:

* `S.CrossingConv` (Proposition `prop:crossing`): `𝖸_γ = (log C_γ - b_γ)/ξ_γ → M` in probability;
* `S.FixedPairConv` (Corollary `cor:fixed-pair`): `(log D^γ(0,1) - b_γ)/ξ_γ → H(0,0)` in probability;
* `S.LawM` (Lemma `lem:law-M`): `q` is the unique median of `M`;
* `S.H00Law`: `H(0,0) ~ N(0, 3/2)`.

The proof follows `blueprint/sections/s7-medians.tex`:

* Step 1 (`Setup.tendsto_neg_b_div_xi`): `C_γ > 0` and `x ↦ (log x - b)/ξ` is increasing on
  `(0, ∞)`; by (S5) and Lemma `lem:medians`(a), `-b_γ/ξ_γ` is a median of `𝖸_γ`; by
  Proposition `prop:crossing`, Lemma `lem:law-M` and Lemma `lem:medians`(b), `-b_γ/ξ_γ → q`.
* Steps 2–3 (`Setup.tendstoInMeasure_main`): with `X_γ = (log D^γ(0,1) - b_γ)/ξ_γ` we have
  `(D^γ(0,1) - 1)/γ = G_γ(X_γ)`, where `G_γ(y) = (exp(ξ_γ (y + b_γ/ξ_γ)) - 1)/γ`
  (`Setup.firstOrderMap`). Since `ξ_γ/γ → 1/2` (Lemma `lem:exponents`) and `b_γ/ξ_γ → -q`
  (Step 1), `G_γ(y) → (z - q)/2` as `γ ↓ 0`, `y → z`; the continuous-mapping theorem
  `tendstoInMeasure_comp_of_tendsto_uncurry` turns Corollary `cor:fixed-pair` into (1.7).
* Step 4 (`Setup.map_main_limit`, `Setup.tendstoInDistribution_main`): `(H(0,0) - q)/2 ~
  N(-q/2, 3/8)`, and convergence in probability implies convergence in law.
* Step 6 (`Setup.tendsto_median_main`): a median `m_γ` of `D^γ(0,1)` is positive and
  `(log m_γ - b_γ)/ξ_γ` is a median of `X_γ` (Lemma `lem:medians`(a)); `H(0,0)` has the unique
  median `0`, so `(log m_γ - b_γ)/ξ_γ → 0` (Lemma `lem:medians`(b)), and
  `(m_γ - 1)/γ = G_γ((log m_γ - b_γ)/ξ_γ) → -q/2`.

Step 5 (`q` is the unique median of `M`, `q < 0`) is `S.LawM` itself.

The main result is `Setup.main_coord`. The random variables are measurable for every `γ` (by
(S2)), so `M` and `H(0,0)` are a.e.-measurable as limits in probability (in this Mathlib, the
push-forward of a measure under a map that is not a.e.-measurable is a Dirac mass, so the law
hypotheses alone would not give this).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

namespace Setup

variable (S : Setup)

/-! ## Measurability and positivity of the random variables -/

/-- `ω ↦ D^γ(0,1)` is measurable, for every `γ`. -/
theorem measurable_dist01 (γ : ℝ) : Measurable fun ω => (S.D γ ω).1 (0, 1) :=
  (ContinuousMap.measurable_eval ((0 : ℂ), (1 : ℂ))).comp
    (measurable_subtype_coe.comp (S.measurable_D γ))

/-- `D^γ(0,1) > 0`: `D^γ(ω)` is a metric and `0 ≠ 1`. -/
theorem dist01_pos (γ : ℝ) (ω : Coord) : 0 < (S.D γ ω).1 (0, 1) :=
  LQGMetric.GM.cm_pos_of_ne (S.D γ ω) zero_ne_one

/-- The crossing distance `ω ↦ C_γ(ω)` is measurable, for every `γ`. -/
theorem measurable_crossing (γ : ℝ) :
    Measurable fun ω => LQGMetric.GM.crossFn (S.D γ ω).1 :=
  LQGMetric.GM.measurable_crossFn_contMetric.comp (S.measurable_D γ)

/-- `C_γ > 0`: the two sides of the unit square are compact and disjoint. -/
theorem crossing_pos (γ : ℝ) (ω : Coord) : 0 < LQGMetric.GM.crossFn (S.D γ ω).1 :=
  LQGMetric.GM.crossFn_pos_contMetric (S.D γ ω)

/-- `𝖸_γ = (log C_γ - b_γ)/ξ_γ` is measurable, for every `γ`. -/
theorem measurable_normCrossing (γ : ℝ) :
    Measurable fun ω => (Real.log (LQGMetric.GM.crossFn (S.D γ ω).1) - S.b γ) / S.ξ γ :=
  ((Real.measurable_log.comp (S.measurable_crossing γ)).sub_const _).div_const _

/-- `(log D^γ(0,1) - b_γ)/ξ_γ` is measurable, for every `γ`. -/
theorem measurable_normLogDist01 (γ : ℝ) :
    Measurable fun ω => (Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) / S.ξ γ :=
  ((Real.measurable_log.comp (S.measurable_dist01 γ)).sub_const _).div_const _

/-- `M` is a.e.-measurable, as the limit in probability of the measurable `𝖸_γ`. -/
theorem aemeasurable_M_of_crossingConv (hcross : S.CrossingConv) : AEMeasurable S.M stdP :=
  TendstoInMeasure.aemeasurable (fun γ => (S.measurable_normCrossing γ).aemeasurable) hcross

/-- `H(0,0)` is a.e.-measurable, as the limit in probability of `(log D^γ(0,1) - b_γ)/ξ_γ`. -/
theorem aemeasurable_H00_of_fixedPairConv (hfix : S.FixedPairConv) :
    AEMeasurable (S.H 0 0) stdP :=
  TendstoInMeasure.aemeasurable (fun γ => (S.measurable_normLogDist01 γ).aemeasurable) hfix

/-- For `γ ∈ (0,2)`, `y ↦ (y - b_γ)/ξ_γ` is non-decreasing. -/
theorem monotone_normalize {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    Monotone fun y : ℝ => (y - S.b γ) / S.ξ γ := fun _ _ hab =>
  div_le_div_of_nonneg_right (sub_le_sub_right hab _) (S.ξ_pos γ hγ0 hγ2).le

/-! ## Step 1: `-b_γ/ξ_γ → q` -/

/-- **Step 1** (blueprint §7, source (6.1)): `-b_γ/ξ_γ → q` as `γ ↓ 0`. -/
theorem tendsto_neg_b_div_xi (hcross : S.CrossingConv) (hlawM : S.LawM) :
    Tendsto (fun γ => -S.b γ / S.ξ γ) (𝓝[>] 0) (𝓝 S.q) := by
  refine tendsto_of_isMedian_of_tendstoInMeasure hcross
    (Eventually.of_forall fun γ => (S.measurable_normCrossing γ).aemeasurable)
    (S.aemeasurable_M_of_crossingConv hcross) hlawM.1.2 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with γ hγ
  -- `log 1 = 0` is a median of `log C_γ`, by (S5)
  have hlog := IsMedian.map_log (S.measurable_crossing γ).aemeasurable
    (ae_of_all _ (S.crossing_pos γ)) (S.S5 γ hγ.1 hγ.2)
  rw [Real.log_one] at hlog
  -- hence `(0 - b_γ)/ξ_γ` is a median of `𝖸_γ`
  have h := IsMedian.map_comp_monotone
    (Real.measurable_log.comp (S.measurable_crossing γ)).aemeasurable hlog
    (S.monotone_normalize hγ.1 hγ.2)
  simp only [zero_sub] at h
  exact h

/-- `b_γ/ξ_γ → -q` as `γ ↓ 0`. -/
theorem tendsto_b_div_xi (hcross : S.CrossingConv) (hlawM : S.LawM) :
    Tendsto (fun γ => S.b γ / S.ξ γ) (𝓝[>] 0) (𝓝 (-S.q)) := by
  refine (S.tendsto_neg_b_div_xi hcross hlawM).neg.congr fun γ => ?_
  rw [neg_div, neg_neg]

/-! ## Steps 2–3: the first-order expansion in probability -/

/-- The deterministic map `G_γ(y) = (exp(ξ_γ (y + b_γ/ξ_γ)) - 1)/γ` of Steps 3 and 6. At
`y = (log x - b_γ)/ξ_γ` it equals `(x - 1)/γ` (`firstOrderMap_eq`). -/
def firstOrderMap (γ y : ℝ) : ℝ := (Real.exp (S.ξ γ * (y + S.b γ / S.ξ γ)) - 1) / γ

/-- `G_γ` is continuous, for every `γ`. -/
theorem continuous_firstOrderMap (γ : ℝ) : Continuous (S.firstOrderMap γ) :=
  ((Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.add continuous_const))).sub continuous_const).div_const _

/-- For `γ ∈ (0,2)` and `x > 0`: `G_γ((log x - b_γ)/ξ_γ) = (x - 1)/γ`. -/
theorem firstOrderMap_eq {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {x : ℝ} (hx : 0 < x) :
    S.firstOrderMap γ ((Real.log x - S.b γ) / S.ξ γ) = (x - 1) / γ := by
  have hξ : S.ξ γ ≠ 0 := (S.ξ_pos γ hγ0 hγ2).ne'
  rw [firstOrderMap, ← add_div, sub_add_cancel, mul_div_cancel₀ _ hξ, Real.exp_log hx]

/-- `G_γ(y) → (z - q)/2` as `γ ↓ 0` and `y → z` (from `ξ_γ/γ → 1/2` and Step 1). -/
theorem tendsto_firstOrderMap (hcross : S.CrossingConv) (hlawM : S.LawM) (z : ℝ) :
    Tendsto (fun p : ℝ × ℝ => S.firstOrderMap p.1 p.2) (𝓝[>] 0 ×ˢ 𝓝 z)
      (𝓝 ((z - S.q) / 2)) := by
  have h := tendsto_exp_mul_sub_one_div S.tendsto_xi_div_self
    (S.tendsto_b_div_xi hcross hlawM) z
  rw [← sub_eq_add_neg] at h
  exact h

/-- **Steps 2–3** (blueprint §7; source (1.7), (6.2)): `(D^γ(0,1) - 1)/γ → (H(0,0) - q)/2` in
probability as `γ ↓ 0`. -/
theorem tendstoInMeasure_main (hcross : S.CrossingConv) (hfix : S.FixedPairConv)
    (hlawM : S.LawM) :
    TendstoInMeasure stdP (fun γ ω => ((S.D γ ω).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (S.H 0 0 ω - S.q) / 2) := by
  have h := tendstoInMeasure_comp_of_tendsto_uncurry (G₀ := fun z => (z - S.q) / 2) hfix
    (S.tendsto_firstOrderMap hcross hlawM)
    (fun γ => ((S.continuous_firstOrderMap γ).measurable.comp
      (S.measurable_normLogDist01 γ)).aestronglyMeasurable)
  refine TendstoInMeasure.congr' ?_ (ae_of_all _ fun ω => rfl) h
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with γ hγ
  exact ae_of_all _ fun ω => S.firstOrderMap_eq hγ.1 hγ.2 (S.dist01_pos γ ω)

/-! ## Step 4: the limit law and convergence in law -/

/-- **Step 4** (blueprint §7; source (6.3)): `(H(0,0) - q)/2 ~ N(-q/2, 3/8)`. -/
theorem map_main_limit (hfix : S.FixedPairConv) (hH : S.H00Law) :
    stdP.map (fun ω => (S.H 0 0 ω - S.q) / 2) = gaussianReal (-S.q / 2) (3 / 8 : ℝ≥0) := by
  have hm : Measurable fun y : ℝ => (y - S.q) / 2 := (measurable_id.sub_const _).div_const _
  have h1 : stdP.map (fun ω => (S.H 0 0 ω - S.q) / 2) =
      (stdP.map (S.H 0 0)).map (fun y : ℝ => (y - S.q) / 2) :=
    (AEMeasurable.map_map_of_aemeasurable hm.aemeasurable
      (S.aemeasurable_H00_of_fixedPairConv hfix)).symm
  have h2 : (fun y : ℝ => (y - S.q) / 2) = (fun y : ℝ => y / 2) ∘ (fun y : ℝ => y - S.q) := rfl
  rw [h1, hH, h2, ← Measure.map_map (by fun_prop : Measurable fun y : ℝ => y / 2)
    (by fun_prop : Measurable fun y : ℝ => y - S.q), gaussianReal_map_sub_const,
    gaussianReal_map_div_const]
  congr 1
  · ring
  · ext
    norm_num

/-- **Step 4** (blueprint §7; source (1.8)): `(D^γ(0,1) - 1)/γ → N(-q/2, 3/8)` in law as
`γ ↓ 0`, indexed by `γ ∈ (0,2)`. -/
theorem tendstoInDistribution_main (hcross : S.CrossingConv) (hfix : S.FixedPairConv)
    (hlawM : S.LawM) (hH : S.H00Law) :
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((S.D γ ω).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => stdP)
      (gaussianReal (-S.q / 2) (3 / 8 : ℝ≥0)) :=
  tendstoInDistribution_Ioo_of_tendstoInMeasure (X := fun γ ω => ((S.D γ ω).1 (0, 1) - 1) / γ)
    (S.tendstoInMeasure_main hcross hfix hlawM)
    (fun γ => (((S.measurable_dist01 γ).sub_const 1).div_const _).aemeasurable)
    (((S.aemeasurable_H00_of_fixedPairConv hfix).sub_const _).div_const _)
    (S.map_main_limit hfix hH)

/-! ## Step 6: medians -/

/-- **Step 6** (blueprint §7; source (1.9)): if `m_γ` is a median of `D^γ(0,1)` for every
`γ ∈ (0,2)`, then `m_γ = 1 - (q/2) γ + o(γ)` as `γ ↓ 0`. -/
theorem tendsto_median_main (hcross : S.CrossingConv) (hfix : S.FixedPairConv) (hlawM : S.LawM)
    (hH : S.H00Law) (m : ℝ → ℝ)
    (hm : ∀ γ, 0 < γ → γ < 2 →
      LQGMetric.IsMedian (stdP.map fun ω => (S.D γ ω).1 (0, 1)) (m γ)) :
    Tendsto (fun γ => (m γ - (1 - S.q / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioo (0 : ℝ) 2 :=
    Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)
  -- medians of `D^γ(0,1)` are positive
  have hmpos : ∀ γ, 0 < γ → γ < 2 → 0 < m γ := fun γ hγ0 hγ2 =>
    IsMedian.pos_of_ae_pos (S.measurable_dist01 γ).aemeasurable (ae_of_all _ (S.dist01_pos γ))
      (hm γ hγ0 hγ2)
  -- `(log m_γ - b_γ)/ξ_γ` is a median of `(log D^γ(0,1) - b_γ)/ξ_γ`
  have hmed : ∀ᶠ γ in 𝓝[>] (0 : ℝ), LQGMetric.IsMedian
      (stdP.map fun ω => (Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) / S.ξ γ)
      ((Real.log (m γ) - S.b γ) / S.ξ γ) := by
    filter_upwards [hev] with γ hγ
    have hlog := IsMedian.map_log (S.measurable_dist01 γ).aemeasurable
      (ae_of_all _ (S.dist01_pos γ)) (hm γ hγ.1 hγ.2)
    exact IsMedian.map_comp_monotone
      (Real.measurable_log.comp (S.measurable_dist01 γ)).aemeasurable hlog
      (S.monotone_normalize hγ.1 hγ.2)
  -- `H(0,0) ~ N(0, 3/2)` has the unique median `0`
  have huniq : ∀ m', LQGMetric.IsMedian (stdP.map (S.H 0 0)) m' → m' = 0 := by
    intro m' hm'
    rw [hH] at hm'
    exact eq_of_isMedian_gaussianReal 0 (by norm_num) hm'
  -- Lemma `lem:medians`(b): `(log m_γ - b_γ)/ξ_γ → 0`
  have hy := tendsto_of_isMedian_of_tendstoInMeasure hfix
    (Eventually.of_forall fun γ => (S.measurable_normLogDist01 γ).aemeasurable)
    (S.aemeasurable_H00_of_fixedPairConv hfix) huniq hmed
  -- hence `(m_γ - 1)/γ = G_γ((log m_γ - b_γ)/ξ_γ) → -q/2`
  have hG := ((S.tendsto_firstOrderMap hcross hlawM 0).comp
    (tendsto_id.prodMk hy)).add_const (S.q / 2)
  rw [show (0 - S.q) / 2 + S.q / 2 = 0 by ring] at hG
  refine hG.congr' ?_
  filter_upwards [hev] with γ hγ
  have hγne : γ ≠ 0 := hγ.1.ne'
  simp only [Function.comp_apply, id_eq]
  rw [S.firstOrderMap_eq hγ.1 hγ.2 (hmpos γ hγ.1 hγ.2)]
  field_simp
  ring

/-! ## The main theorem in coordinates -/

/-- **Theorem `thm:main` in coordinates** (blueprint §7, Steps 1–6; source Theorem 1.1), relative
to the interface propositions `CrossingConv` (Proposition `prop:crossing`), `FixedPairConv`
(Corollary `cor:fixed-pair`), `LawM` (Lemma `lem:law-M`) and `H00Law` (`H(0,0) ~ N(0, 3/2)`):

1. `(D^γ(0,1) - 1)/γ → (H(0,0) - q)/2` in probability as `γ ↓ 0` (1.7);
2. `(H(0,0) - q)/2 ~ N(-q/2, 3/8)`;
3. `(D^γ(0,1) - 1)/γ → N(-q/2, 3/8)` in law as `γ ↓ 0` (1.8);
4. every choice of medians `m_γ` of `D^γ(0,1)` satisfies `m_γ = 1 - (q/2) γ + o(γ)` (1.9). -/
theorem main_coord (hcross : S.CrossingConv) (hfix : S.FixedPairConv) (hlawM : S.LawM)
    (hH : S.H00Law) :
    TendstoInMeasure stdP (fun γ ω => ((S.D γ ω).1 (0, 1) - 1) / γ) (𝓝[>] 0)
        (fun ω => (S.H 0 0 ω - S.q) / 2) ∧
    stdP.map (fun ω => (S.H 0 0 ω - S.q) / 2) = gaussianReal (-S.q / 2) (3 / 8 : ℝ≥0) ∧
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((S.D γ ω).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => stdP)
      (gaussianReal (-S.q / 2) (3 / 8 : ℝ≥0)) ∧
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (stdP.map fun ω => (S.D γ ω).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - S.q / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
  ⟨S.tendstoInMeasure_main hcross hfix hlawM, S.map_main_limit hfix hH,
    S.tendstoInDistribution_main hcross hfix hlawM hH,
    S.tendsto_median_main hcross hfix hlawM hH⟩

end Setup

end GaussianLQG
