import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Probability.BMLLN
import QuantumZipper.Proofs.LQG.WedgeGood

/-!
# W-D (wedge decomposition), part 1: deterministic pieces

Decision D29 (`DECISIONS.md`), `handoff/WEDGE-UNZIP.md`, core statement
`WedgeUnzip.WedgeDecompStmt`. Sources: Sheffield, arXiv:1012.4797, §1.6 (the `α`-wedge is the
lateral part of a free field plus the radial process `A_t`, which for `t ≥ 0` is
`√2 b_t + (α − Q)t`); Duplantier–Miller–Sheffield, arXiv:1409.7055, §4.1 and Def. 4.4 (a free
field is its lateral part plus an independent two-sided radial Brownian motion `h_{e^{-t}}(0)`).

The decomposition replaces the radial part of the wedge *outside* the unit disc by the backward
radial Brownian motion `n` of the free field itself (as in `WedgeGood.wedgeRefGoodAS_of_logSing`):
the radial profile is `prof b n z = √2 b(−log|z|)` on the closed unit disc (`b` the forward wedge
Brownian motion) and `√2 n(log|z|)` outside. The correction `corrField` is the difference
`Q t + A_t − √2 n(−t) − α t` at `t = −log|z| < 0` and `0` on the closed unit disc.

This file proves the deterministic facts:
* `jmod_eq_integral_of_continuous`: the dyadic Riemann-sum reading `Jmod` of a path integral is
  the integral, for every continuous path of linear growth (dominated convergence);
* `integrable_integral_prof`: the profile is integrable against every admissible measure and its
  integral is read by `Jmod` (so it is a measurable function of the paths);
* `continuous_corrField`, `corrField_eq_zero`, `kernel_eq_prof`: the correction is continuous,
  vanishes on the closed unit disc, and the wedge kernel is profile + `α(−log)` + correction;
* `ae_exists_linear_bound`: Brownian paths grow at most linearly (law of large numbers).
Own elementary arguments (the paper states the decomposition, not these identities).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip
namespace WDec

open WedgeRes WedgeGood WedgeTK

/-! ## 1. `Jmod` is the integral on continuous paths of linear growth -/

theorem tendsto_flr (s : ℝ≥0) : Tendsto (fun n => flr n s) atTop (𝓝 s) := by
  have h : Tendsto (fun n => (flr n s : ℝ)) atTop (𝓝 (s : ℝ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h4 : Tendsto (fun n : ℕ => (1 : ℝ) / 4 ^ n) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).congr fun n => one_div_pow (4 : ℝ) n
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h4
    rw [← coe_nndist]
    exact nndist_flr_le n s
  exact NNReal.tendsto_coe.1 h

/-- **`Jmod` reads the integral of a continuous path of linear growth** (deterministic; dominated
convergence of the dyadic Riemann sums). -/
theorem jmod_eq_integral_of_continuous {lam : Measure ℝ≥0} [IsFiniteMeasure lam]
    (hlam : Integrable (fun s : ℝ≥0 => (s : ℝ)) lam) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    {C : ℝ} (hC : ∀ s : ℝ≥0, |w s| ≤ C * (1 + (s : ℝ))) :
    Integrable w lam ∧ Jmod lam w = ∫ s, w s ∂lam := by
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 0)
    simpa using h
  have hbd : Integrable (fun s : ℝ≥0 => C * (1 + (s : ℝ))) lam :=
    ((integrable_const (1 : ℝ)).add hlam).const_mul C
  have hint : Integrable w lam :=
    hbd.mono' hw.aestronglyMeasurable (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs]; exact hC s)
  refine ⟨hint, ?_⟩
  have ht : Tendsto (fun n => Jn lam n w) atTop (𝓝 (∫ s, w s ∂lam)) := by
    unfold Jn
    refine tendsto_integral_of_dominated_convergence (fun s => C * (1 + (s : ℝ)))
      (fun n => (hw.measurable.comp (measurable_flr n)).aestronglyMeasurable) hbd
      (fun n => ae_of_all _ fun s => ?_) (ae_of_all _ fun s => ?_)
    · rw [Real.norm_eq_abs]
      refine (hC _).trans ?_
      exact mul_le_mul_of_nonneg_left (by linarith [flr_le n s]) hC0
    · exact (hw.tendsto s).comp (tendsto_flr s)
  exact ht.limUnder_eq

/-! ## 2. The radial profile -/

/-- The two-sided radial profile: `√2 b(−log|z|)` on the closed unit disc, `√2 n(log|z|)`
outside. -/
def prof (b n : ℝ≥0 → ℝ) (z : ℂ) : ℝ :=
  if ‖z‖ ≤ 1 then √2 * b (tau z) else √2 * n (tauM z)

/-- **The profile is integrable against an admissible measure, and its integral is read by
`Jmod`** (continuous paths of linear growth). -/
theorem integrable_integral_prof {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {b n : ℝ≥0 → ℝ}
    (hb : Continuous b) (hn : Continuous n) {C : ℝ}
    (hbC : ∀ s : ℝ≥0, |b s| ≤ C * (1 + (s : ℝ))) (hnC : ∀ s : ℝ≥0, |n s| ≤ C * (1 + (s : ℝ))) :
    Integrable (prof b n) μ ∧ ∫ z, prof b n z ∂μ =
      √2 * (Jmod ((μ.restrict Dsc).map tau) b + Jmod ((μ.restrict Dscᶜ).map tauM) n) := by
  have := hμ.1
  have h1 := jmod_eq_integral_of_continuous (integrable_tau_restrict hμ Dsc) hb hbC
  have h2 := jmod_eq_integral_of_continuous (integrable_tauM_restrict hμ Dscᶜ) hn hnC
  have hA1 : IntegrableOn (fun z => b (tau z)) Dsc μ :=
    (integrable_map_measure hb.aestronglyMeasurable measurable_tau.aemeasurable).1 h1.1
  have hA2 : IntegrableOn (fun z => n (tauM z)) Dscᶜ μ :=
    (integrable_map_measure hn.aestronglyMeasurable measurable_tauM.aemeasurable).1 h2.1
  have e1 : ∫ s, b s ∂((μ.restrict Dsc).map tau) = ∫ z in Dsc, b (tau z) ∂μ :=
    integral_map measurable_tau.aemeasurable hb.aestronglyMeasurable
  have e2 : ∫ s, n s ∂((μ.restrict Dscᶜ).map tauM) = ∫ z in Dscᶜ, n (tauM z) ∂μ :=
    integral_map measurable_tauM.aemeasurable hn.aestronglyMeasurable
  set f : ℂ → ℝ := prof b n with hf
  have hf1 : EqOn (fun z => √2 * b (tau z)) f Dsc := fun z hz => by
    have : ‖z‖ ≤ 1 := by simpa using hz
    simp only [hf, prof, this, ↓reduceIte]
  have hf2 : EqOn (fun z => √2 * n (tauM z)) f Dscᶜ := fun z hz => by
    have : ¬ ‖z‖ ≤ 1 := by simpa using hz
    simp only [hf, prof, this, ↓reduceIte]
  have i1 : IntegrableOn f Dsc μ :=
    IntegrableOn.congr_fun (hA1.const_mul (√2) : IntegrableOn _ Dsc μ) hf1 measurableSet_Dsc
  have i2 : IntegrableOn f Dscᶜ μ :=
    IntegrableOn.congr_fun (hA2.const_mul (√2) : IntegrableOn _ Dscᶜ μ) hf2
      measurableSet_Dsc.compl
  have hint : Integrable f μ := by
    have := i1.union i2
    rwa [union_compl_self, integrableOn_univ] at this
  refine ⟨hint, ?_⟩
  rw [← integral_add_compl measurableSet_Dsc hint,
    ← setIntegral_congr_fun measurableSet_Dsc hf1,
    ← setIntegral_congr_fun measurableSet_Dsc.compl hf2, integral_const_mul,
    integral_const_mul, h1.2, h2.2, e1, e2]
  ring

/-! ## 3. The correction -/

/-- The correction as a function of the log-scale `t`: `0` for `t ≥ 0`, and
`Q t + a t − √2 n(−t) − α t` for `t < 0`. -/
def corr (α Q : ℝ) (a : ℝ → ℝ) (n : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then 0 else Q * t + a t - √2 * n (-t).toNNReal - α * t

/-- The correction `G` on the plane, read at `t = −log max(|z|, 1)`. -/
def corrField (α Q : ℝ) (a : ℝ → ℝ) (n : ℝ≥0 → ℝ) (z : ℂ) : ℝ :=
  corr α Q a n (-Real.log (max ‖z‖ 1))

theorem corrField_eq_zero {α Q : ℝ} {a : ℝ → ℝ} {n : ℝ≥0 → ℝ} {z : ℂ} (hz : ‖z‖ ≤ 1) :
    corrField α Q a n z = 0 := by
  simp [corrField, corr, max_eq_right hz]

theorem continuous_corrField {α Q : ℝ} {a : ℝ → ℝ} {n : ℝ≥0 → ℝ} (ha : Continuous a)
    (hn : Continuous n) (ha0 : a 0 = 0) (hn0 : n 0 = 0) : Continuous (corrField α Q a n) := by
  have hc : Continuous (corr α Q a n) := by
    unfold corr
    refine Continuous.if_le continuous_const
      ((((continuous_const.mul continuous_id).add ha).sub
        (continuous_const.mul (hn.comp (continuous_real_toNNReal.comp continuous_neg)))).sub
        (continuous_const.mul continuous_id)) continuous_const continuous_id ?_
    intro t ht
    subst ht
    simp [ha0, hn0]
  exact hc.comp ((continuous_norm.max continuous_const).log
    (fun z => (one_pos.trans_le (le_max_right _ _)).ne')).neg

/-- **The wedge kernel is profile + log singularity + correction**, pointwise, when the radial
path is `√2 b_t + (α − Q)t` for `t ≥ 0`. -/
theorem kernel_eq_prof {α Q : ℝ} {a : ℝ → ℝ} {b n : ℝ≥0 → ℝ}
    (ha : ∀ t : ℝ, 0 ≤ t → a t = √2 * b t.toNNReal + (α - Q) * t) (z : ℂ) :
    Q * (-Real.log ‖z‖) + a (-Real.log ‖z‖) =
      prof b n z + α * (-Real.log ‖z‖) + corrField α Q a n z := by
  by_cases hz1 : ‖z‖ ≤ 1
  · have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg z) hz1)
    rw [corrField_eq_zero hz1, ha _ ht]
    simp only [prof, hz1, ↓reduceIte, tau]
    ring
  · have hz1' : 1 < ‖z‖ := lt_of_not_ge hz1
    have ht : ¬ 0 ≤ -Real.log ‖z‖ := by
      have := Real.log_pos hz1'; linarith
    simp only [prof, hz1, ↓reduceIte, corrField, corr, max_eq_left hz1'.le, ht, tauM, neg_neg]
    ring

/-! ## 4. Linear growth of Brownian paths -/

/-- **Brownian paths grow at most linearly**, a.s. (from the law of large numbers
`BMLLN.ae_tendsto_div_atTop` and continuity on a compact interval). -/
theorem ae_exists_linear_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0, |B t ω| ≤ C * (1 + (t : ℝ)) := by
  filter_upwards [BMLLN.ae_tendsto_div_atTop hB, hB.cont] with ω hdiv hcont
  have h1 : ∀ᶠ t : ℝ≥0 in atTop, |B t ω| ≤ (t : ℝ) := by
    have hε : ∀ᶠ t : ℝ≥0 in atTop, |(t : ℝ)⁻¹ * B t ω| < 1 := by
      have hmem : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 one_pos
      simpa only [Real.dist_eq, sub_zero] using hdiv.eventually hmem
    have hge : ∀ᶠ t : ℝ≥0 in atTop, (1 : ℝ) ≤ (t : ℝ) :=
      eventually_atTop.2 ⟨1, fun t ht => by exact_mod_cast ht⟩
    filter_upwards [hε, hge] with t ht hge1
    have ht1 : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le one_pos hge1
    have h1 : |B t ω| = (t : ℝ) * |(t : ℝ)⁻¹ * B t ω| := by
      have h2 : |B t ω| = |(t : ℝ)| * |(t : ℝ)⁻¹ * B t ω| := by
        rw [← abs_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht1), one_mul]
      rwa [abs_of_nonneg (le_of_lt ht1)] at h2
    rw [h1]
    calc (t : ℝ) * |(t : ℝ)⁻¹ * B t ω| ≤ (t : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (le_of_lt ht) ht1.le
      _ = (t : ℝ) := mul_one _
  obtain ⟨T, hT⟩ := eventually_atTop.1 h1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := max T 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max 1 M, le_trans zero_le_one (le_max_left 1 M), fun t => ?_⟩
  rcases lt_or_ge t (max T 1) with h | h
  · have h1 : |B t ω| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM t ⟨zero_le, le_of_lt h⟩
    have h3 : (0 : ℝ) ≤ 1 + (t : ℝ) := by positivity
    calc |B t ω| ≤ M := h1
      _ ≤ max 1 M := le_max_right _ _
      _ = max 1 M * 1 := (mul_one _).symm
      _ ≤ max 1 M * (1 + (t : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [NNReal.coe_nonneg t])
            (le_trans zero_le_one (le_max_left 1 M))
  · have h1 : |B t ω| ≤ (t : ℝ) := hT t ((le_max_left T 1).trans h)
    have h2 : (0 : ℝ) ≤ max 1 M := le_trans zero_le_one (le_max_left 1 M)
    have h3 : (1 : ℝ) ≤ max 1 M := le_max_left 1 M
    calc |B t ω| ≤ (t : ℝ) := h1
      _ = 1 * (t : ℝ) := (one_mul _).symm
      _ ≤ max 1 M * (t : ℝ) := mul_le_mul_of_nonneg_right h3 (NNReal.coe_nonneg t)
      _ ≤ max 1 M * (1 + (t : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [NNReal.coe_nonneg t]) h2

end WDec
end WedgeUnzip
end QuantumZipper
