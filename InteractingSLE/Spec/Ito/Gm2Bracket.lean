import InteractingSLE.Spec.Ito.Gm2Core
import InteractingSLE.Spec.Ito.Observable
import InteractingSLE.Spec.Ito.Bracket
import InteractingSLE.Spec.Ito.Localize

/-!
# The bracket of the mixed Itô residual

Packet PROVE-ITO-GEN2. Theorem 2.6's proof needs the quadratic variation of the martingale part of the
driver (`source/spec/p001-048.md` L982: `d⟨𝔥(z)⟩ = (4/κ)(Im 1/f)² dQ`, read backwards: from the bracket of
`𝔥(z)` to that of `W`). In martingale-problem form (Revuz–Yor IV.1.8): for the bounded data of
`Gm2Core.martingale_residual`, with continuous integrators,

**`martingale_residual_sq_sub_bracket`.** `N_t² − Σₖ ∫_{(0,t]} (∂_x F(Y, M))² aₖ dUₖ` is an
`𝓕`-martingale, where `N` is the mixed residual.

Proof: apply `martingale_residual` to `Φ((y, c, q), x) = (F(y, x) − c)² − q` (cut off far from the
bounded state) with the enlarged finite-variation coordinate `(Y, F(Y_0, M_0) + drift, bracket)`. Its
drift density vanishes identically (`driftDensity_Φ_eq_zero`), and its residual is `N² − bracket`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

/-! ### Continuity of a Stieltjes primitive -/

/-- **A Stieltjes primitive of a continuous integrand against a continuous integrator is continuous.** -/
theorem continuous_integral_Ioc_zero (U : StieltjesFunction ℝ≥0) (hU : Continuous U)
    {g : ℝ≥0 → ℝ} (hg : Continuous g) : Continuous fun t => ∫ u in Ioc 0 t, g u ∂U.measure := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t₀ + 1)).exists_bound_of_continuousOn
    hg.continuousOn
  have hlip : ∀ t ∈ Iic (t₀ + 1), |(∫ u in Ioc 0 t, g u ∂U.measure) -
      ∫ u in Ioc 0 t₀, g u ∂U.measure| ≤ B * |U t - U t₀| := by
    intro t ht
    have ht₀ : t₀ ∈ Iic (t₀ + 1) := (lt_add_one t₀).le
    rcases le_total t₀ t with h | h
    · rw [integral_Ioc_zero_sub U hg h, abs_of_nonneg (sub_nonneg.2 (U.mono h))]
      exact Gen.abs_stieltjes_integral_le U h fun u hu => by
        simpa only [Real.norm_eq_abs] using hB u ⟨bot_le, hu.2.trans ht⟩
    · rw [abs_sub_comm, integral_Ioc_zero_sub U hg h, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 (U.mono h))]
      exact Gen.abs_stieltjes_integral_le U h fun u hu => by
        simpa only [Real.norm_eq_abs] using hB u ⟨bot_le, hu.2.trans ht₀⟩
  have hU' : Tendsto (fun t => B * |U t - U t₀|) (𝓝 t₀) (𝓝 0) := by
    have := ((hU.tendsto t₀).sub_const (U t₀)).abs.const_mul B
    simpa only [sub_self, abs_zero, mul_zero] using this
  have hev : ∀ᶠ t in 𝓝 t₀, |(∫ u in Ioc 0 t, g u ∂U.measure) -
      ∫ u in Ioc 0 t₀, g u ∂U.measure| ≤ B * |U t - U t₀| :=
    Filter.mem_of_superset (Iic_mem_nhds (lt_add_one t₀)) fun t ht => hlip t ht
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  exact squeeze_zero_norm' (hev.mono fun t ht => by rwa [Real.norm_eq_abs]) hU'

/-! ### The squared residual as a function of the enlarged state -/

section Phi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E × ℝ → ℝ}

/-- `Φ((y, c, q), x) = (F(y, x) − c)² − q`: the squared residual minus the bracket, as a function of the
enlarged finite-variation state `(y, c, q)` and the martingale coordinate `x`. -/
def sqPhi (F : E × ℝ → ℝ) (p : (E × ℝ × ℝ) × ℝ) : ℝ := (F (p.1.1, p.2) - p.1.2.1) ^ 2 - p.1.2.2

theorem contDiff_sqPhi {n : WithTop ℕ∞} (hF : ContDiff ℝ n F) : ContDiff ℝ n (sqPhi F) := by
  have h1 : ContDiff ℝ n fun p : (E × ℝ × ℝ) × ℝ => F (p.1.1, p.2) :=
    hF.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  exact ((h1.sub (contDiff_fst.comp (contDiff_snd.comp contDiff_fst))).pow 2).sub
    (contDiff_snd.comp (contDiff_snd.comp contDiff_fst))

/-- The derivative of `F` along a line in the first slot is `∂_y F`. -/
theorem hasDerivAt_fst_line {q : E × ℝ} (hF : DifferentiableAt ℝ F q) (v : E) :
    HasDerivAt (fun t : ℝ => F (q.1 + t • v, q.2)) (partialFst F q v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => ((q.1 + t • v, q.2) : E × ℝ)) ((v, 0) : E × ℝ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => q.1 + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q.1
    exact h1.prodMk (hasDerivAt_const 0 q.2)
  have h := (show HasFDerivAt F (fderiv ℝ F q) (q.1 + (0 : ℝ) • v, q.2) by
    simpa using hF.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hline
  rw [partialFst_apply]
  simpa [Function.comp_def] using h

theorem partialFst_sqPhi (hF : ContDiff ℝ 3 F) (p : (E × ℝ × ℝ) × ℝ) (w : E × ℝ × ℝ) :
    partialFst (sqPhi F) p w = 2 * (F (p.1.1, p.2) - p.1.2.1) *
      (partialFst F (p.1.1, p.2) w.1 - w.2.1) - w.2.2 := by
  have hΦ : Differentiable ℝ (sqPhi F) := (contDiff_sqPhi hF).differentiable (by norm_num)
  have h1 := hasDerivAt_fst_line (q := (p.1.1, p.2)) ((hF.differentiable (by norm_num)) _) w.1
  have h2 : HasDerivAt (fun t : ℝ => p.1.2.1 + t * w.2.1) w.2.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.2.1).const_add p.1.2.1
  have h3 : HasDerivAt (fun t : ℝ => p.1.2.2 + t * w.2.2) w.2.2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const w.2.2).const_add p.1.2.2
  have key : HasDerivAt (fun t : ℝ =>
      (F ((p.1.1, p.2).1 + t • w.1, (p.1.1, p.2).2) - (p.1.2.1 + t * w.2.1)) ^ 2 -
        (p.1.2.2 + t * w.2.2))
      ((2 : ℕ) * (F ((p.1.1, p.2).1 + (0 : ℝ) • w.1, (p.1.1, p.2).2) - (p.1.2.1 + 0 * w.2.1)) ^
        (2 - 1) * (partialFst F (p.1.1, p.2) w.1 - w.2.1) - w.2.2) 0 :=
    ((h1.sub h2).pow 2).sub h3
  refine partialFst_eq_of_hasDerivAt (hΦ p) ?_
  have hfun : (fun t : ℝ => sqPhi F (p.1 + t • w, p.2)) = fun t : ℝ =>
      (F ((p.1.1, p.2).1 + t • w.1, (p.1.1, p.2).2) - (p.1.2.1 + t * w.2.1)) ^ 2 -
        (p.1.2.2 + t * w.2.2) := by
    funext t; simp only [sqPhi, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
  rw [hfun]
  refine key.congr_deriv ?_
  simp only [zero_smul, add_zero, zero_mul]
  norm_num

theorem partialSnd_sqPhi (hF : ContDiff ℝ 3 F) (p : (E × ℝ × ℝ) × ℝ) :
    partialSnd (sqPhi F) p = 2 * (F (p.1.1, p.2) - p.1.2.1) * partialSnd F (p.1.1, p.2) := by
  have hΦ : Differentiable ℝ (sqPhi F) := (contDiff_sqPhi hF).differentiable (by norm_num)
  have h1 := hasDerivAt_snd_line (p := (p.1.1, p.2)) ((hF.differentiable (by norm_num)) _)
  refine partialSnd_eq_of_hasDerivAt (hΦ p) ?_
  have key : HasDerivAt (fun y : ℝ => (F (p.1.1, y) - p.1.2.1) ^ 2 - p.1.2.2)
      ((2 : ℕ) * (F (p.1.1, p.2) - p.1.2.1) ^ (2 - 1) * partialSnd F (p.1.1, p.2)) p.2 :=
    ((h1.sub_const p.1.2.1).pow 2).sub_const p.1.2.2
  refine key.congr_deriv ?_
  norm_num

theorem partialSndSnd_sqPhi (hF : ContDiff ℝ 3 F) (p : (E × ℝ × ℝ) × ℝ) :
    partialSndSnd (sqPhi F) p = 2 * partialSnd F (p.1.1, p.2) ^ 2 +
      2 * (F (p.1.1, p.2) - p.1.2.1) * partialSndSnd F (p.1.1, p.2) := by
  have hΦ2 : ContDiffAt ℝ 2 (sqPhi F) p := (contDiff_sqPhi hF).contDiffAt.of_le (by norm_num)
  have hF2 : ContDiffAt ℝ 2 F (p.1.1, p.2) := hF.contDiffAt.of_le (by norm_num)
  have h1 := hasDerivAt_snd_line (p := (p.1.1, p.2)) ((hF.differentiable (by norm_num)) _)
  have h2 := hasDerivAt_partialSnd hF2
  refine partialSndSnd_eq_of_hasDerivAt hΦ2
    (g := fun y => 2 * (F (p.1.1, y) - p.1.2.1) * partialSnd F (p.1.1, y))
    (.of_forall fun y => partialSnd_sqPhi hF (p.1, y)) ?_
  have key : HasDerivAt (fun y : ℝ => 2 * (F (p.1.1, y) - p.1.2.1) * partialSnd F (p.1.1, y))
      (2 * partialSnd F (p.1.1, p.2) * partialSnd F (p.1.1, p.2) +
        2 * (F (p.1.1, p.2) - p.1.2.1) * partialSndSnd F (p.1.1, p.2)) p.2 :=
    ((h1.sub_const p.1.2.1).const_mul 2).mul h2
  refine key.congr_deriv ?_
  ring

/-- **The drift density of `Φ` along the enlarged state vanishes**: with the finite-variation densities
`(c, ∂_y F c + ½ ∂²_x F α, (∂_x F)² α)` and the bracket density `α`. -/
theorem partialFst_sqPhi_add_eq_zero (hF : ContDiff ℝ 3 F) (y : E) (cc qq x : ℝ) (v : E) (α : ℝ) :
    partialFst (sqPhi F) ((y, cc, qq), x)
        (v, partialFst F (y, x) v + 1 / 2 * partialSndSnd F (y, x) * α,
          partialSnd F (y, x) ^ 2 * α) +
      1 / 2 * partialSndSnd (sqPhi F) ((y, cc, qq), x) * α = 0 := by
  rw [partialFst_sqPhi hF, partialSndSnd_sqPhi hF]
  ring

end Phi

/-! ### The bracket -/

section Bracket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {m : ℕ}
  {F : E × ℝ → ℝ} {Y : ℝ≥0 → Ω → E} {M A : ℝ≥0 → Ω → ℝ}
  {U : Fin m → Ω → StieltjesFunction ℝ≥0} {c : Fin m → ℝ≥0 → Ω → E} {a : Fin m → ℝ≥0 → Ω → ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The drift density only depends on the germ of `F` at the state. -/
lemma driftDensity_congr {G : E × ℝ → ℝ} {k : Fin m} {u : ℝ≥0} {ω : Ω}
    (h : F =ᶠ[𝓝 (Y u ω, M u ω)] G) :
    driftDensity F Y M c a k u ω = driftDensity G Y M c a k u ω := by
  unfold driftDensity partialFst partialSndSnd
  rw [h.fderiv_eq, h.fderiv.fderiv_eq]

lemma integral_Ioc_self_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure ℝ≥0) (g : ℝ≥0 → G) : ∫ u in Ioc (0 : ℝ≥0) 0, g u ∂μ = 0 := by
  rw [Set.Ioc_self, Measure.restrict_empty, integral_zero_measure]

/-- **The bracket of the mixed residual, bounded case.** Under the hypotheses of `martingale_residual`
and with continuous integrators, `N² − Σₖ ∫ (∂_x F(Y, M))² aₖ dUₖ` is an `𝓕`-martingale. -/
theorem martingale_residual_sq_sub_bracket [IsProbabilityMeasure P]
    (hF : ContDiff ℝ 3 F) (hFc : HasCompactSupport F)
    (hM : Martingale M 𝓕 P) (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    {K L R V : ℝ} (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (hR : ∀ t ω, ‖Y t ω‖ ≤ R)
    (hV : ∀ t ω, ∑ k, ∫ u in Ioc 0 t, ‖c k u ω‖ ∂(U k ω).measure ≤ V)
    (hMc : ∀ ω, Continuous (M · ω)) (hAc : ∀ ω, Continuous (A · ω))
    (hYc : ∀ ω, Continuous (Y · ω)) (hcc : ∀ k ω, Continuous (c k · ω))
    (hac : ∀ k ω, Continuous (a k · ω)) (ha0 : ∀ k u ω, 0 ≤ a k u ω)
    (hUc : ∀ k ω, Continuous (U k ω))
    (hY : ∀ t ω, Y t ω = Y 0 ω + ∑ k, ∫ u in Ioc 0 t, c k u ω ∂(U k ω).measure)
    (hA : ∀ t ω, A t ω = A 0 ω + ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
    (hYa : ∀ t, Measurable[𝓕 t] (Y t)) (hca : ∀ k t, Measurable[𝓕 t] (c k t))
    (haa : ∀ k t, Measurable[𝓕 t] (a k t)) (hUa : ∀ k t, Measurable[𝓕 t] fun ω => U k ω t) :
    Martingale (fun t ω => residual F Y M U c a t ω ^ 2 - bracket F Y M U a t ω) 𝓕 P := by
  obtain ⟨C, hC0, hFb, hD1, hD2, -, -, -⟩ := exists_bound_of_contDiff_three hF hFc
  have hMa (t : ℝ≥0) : Measurable[𝓕 t] (M t) := (hM.stronglyAdapted t).measurable
  have hpath (ω : Ω) : Continuous fun u => ((Y u ω, M u ω) : E × ℝ) := (hYc ω).prodMk (hMc ω)
  -- the enlarged coordinate `(Y, F(Y₀, M₀) + drift, bracket)` and its densities
  set D : ℝ≥0 → Ω → ℝ := fun t ω => F (Y 0 ω, M 0 ω) +
    ∑ k, ∫ u in Ioc 0 t, driftDensity F Y M c a k u ω ∂(U k ω).measure with hDdef
  set q : Fin m → ℝ≥0 → Ω → ℝ := fun k u ω => partialSnd F (Y u ω, M u ω) ^ 2 * a k u ω with hqdef
  set Y' : ℝ≥0 → Ω → E × ℝ × ℝ := fun t ω => (Y t ω, D t ω, bracket F Y M U a t ω) with hY'def
  set c' : Fin m → ℝ≥0 → Ω → E × ℝ × ℝ := fun k u ω =>
    (c k u ω, driftDensity F Y M c a k u ω, q k u ω) with hc'def
  have hdc (k : Fin m) (ω : Ω) : Continuous fun u => driftDensity F Y M c a k u ω :=
    continuous_driftDensity hF (hYc ω) (hMc ω) (hcc k ω) (hac k ω)
  have hqc (k : Fin m) (ω : Ω) : Continuous fun u => q k u ω :=
    (((continuous_partialSnd' hF).comp (hpath ω)).pow 2).mul (hac k ω)
  -- bounds of the enlarged coordinate
  have hAt (t : ℝ≥0) (ω : Ω) : ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure ≤ 2 * L := by
    have h1 := hA t ω
    have h2 := (le_abs_self _).trans (MathFin.LevyQuadraticSums.abs_sub_le_two_mul hL 0 t ω)
    linarith
  have hDb (t : ℝ≥0) (ω : Ω) : |D t ω| ≤ C + C * (V + L) := by
    have h := abs_sum_integral_driftDensity_le (Y := Y) (M := M) (U := U) hD1 hD2 ha0 (fun k => hcc k ω)
      (fun k => hac k ω) t
    refine (abs_add_le _ _).trans (add_le_add (hFb _) (h.trans ?_))
    nlinarith [hV t ω, hAt t ω]
  have hq0 (k : Fin m) (u : ℝ≥0) (ω : Ω) : 0 ≤ q k u ω := mul_nonneg (sq_nonneg _) (ha0 k u ω)
  have hqle (k : Fin m) (u : ℝ≥0) (ω : Ω) : q k u ω ≤ C ^ 2 * a k u ω := by
    refine mul_le_mul_of_nonneg_right ?_ (ha0 k u ω)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_partialSnd_le _ _).trans (hD1 _)) 2
  have hQint (t : ℝ≥0) (ω : Ω) : 0 ≤ bracket F Y M U a t ω ∧
      bracket F Y M U a t ω ≤ C ^ 2 * (2 * L) := by
    refine ⟨sum_nonneg fun k _ => setIntegral_nonneg measurableSet_Ioc fun u _ => hq0 k u ω, ?_⟩
    refine le_trans (sum_le_sum fun k _ => setIntegral_mono_on
      (integrableOn_Ioc_of_continuous (U k ω) (hqc k ω) 0 t)
      ((integrableOn_Ioc_of_continuous (U k ω) (hac k ω) 0 t).const_mul (C ^ 2)) measurableSet_Ioc
      fun u _ => hqle k u ω) ?_
    simp only [integral_const_mul, ← mul_sum]
    exact mul_le_mul_of_nonneg_left (hAt t ω) (sq_nonneg C)
  set R₀ := |R| + |C + C * (V + L)| + |C ^ 2 * (2 * L)| + |K| with hR₀
  have hR' (t : ℝ≥0) (ω : Ω) : ‖Y' t ω‖ ≤ R₀ := by
    simp only [hY'def, Prod.norm_def, Real.norm_eq_abs, max_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · linarith [hR t ω, le_abs_self R, abs_nonneg (C + C * (V + L)),
        abs_nonneg (C ^ 2 * (2 * L)), abs_nonneg K]
    · linarith [hDb t ω, le_abs_self (C + C * (V + L)), abs_nonneg R,
        abs_nonneg (C ^ 2 * (2 * L)), abs_nonneg K]
    · rw [abs_of_nonneg (hQint t ω).1]
      linarith [(hQint t ω).2, le_abs_self (C ^ 2 * (2 * L)), abs_nonneg R,
        abs_nonneg (C + C * (V + L)), abs_nonneg K]
  have hstate (t : ℝ≥0) (ω : Ω) : ((Y' t ω, M t ω) : (E × ℝ × ℝ) × ℝ) ∈
      Metric.closedBall (0 : (E × ℝ × ℝ) × ℝ) R₀ := by
    have h1 := hK t ω
    have h2 := le_abs_self K
    have h3 := abs_nonneg R
    have h4 := abs_nonneg (C + C * (V + L))
    have h5 := abs_nonneg (C ^ 2 * (2 * L))
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    exact ⟨hR' t ω, by linarith⟩
  -- the total variation of the enlarged coordinate
  have hc'le (k : Fin m) (u : ℝ≥0) (ω : Ω) :
      ‖c' k u ω‖ ≤ (1 + C) * ‖c k u ω‖ + (C / 2 + C ^ 2) * a k u ω := by
    have h1 := abs_driftDensity_le (Y := Y) (M := M) (c := c) hD1 hD2 ha0 k u ω
    have h2 := hqle k u ω
    have h3 := hq0 k u ω
    have h4 := ha0 k u ω
    simp only [hc'def, Prod.norm_def, Real.norm_eq_abs, max_le_iff]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [norm_nonneg (c k u ω)]
    · nlinarith [norm_nonneg (c k u ω)]
    · rw [abs_of_nonneg h3]; nlinarith [norm_nonneg (c k u ω)]
  have hc'c (k : Fin m) (ω : Ω) : Continuous fun u => c' k u ω :=
    (hcc k ω).prodMk ((hdc k ω).prodMk (hqc k ω))
  set V' := (1 + C) * V + (C / 2 + C ^ 2) * (2 * L) with hV'def
  have hV' (t : ℝ≥0) (ω : Ω) : ∑ k, ∫ u in Ioc 0 t, ‖c' k u ω‖ ∂(U k ω).measure ≤ V' := by
    have hi1 (k : Fin m) := integrableOn_Ioc_of_continuous (U k ω) (hcc k ω).norm 0 t
    have hi2 (k : Fin m) := integrableOn_Ioc_of_continuous (U k ω) (hac k ω) 0 t
    have hib (k : Fin m) : IntegrableOn
        (fun u => (1 + C) * ‖c k u ω‖ + (C / 2 + C ^ 2) * a k u ω) (Ioc 0 t) (U k ω).measure :=
      integrableOn_Ioc_of_continuous (U k ω)
        ((continuous_const.mul (hcc k ω).norm).add (continuous_const.mul (hac k ω))) 0 t
    calc ∑ k, ∫ u in Ioc 0 t, ‖c' k u ω‖ ∂(U k ω).measure
        ≤ ∑ k, ∫ u in Ioc 0 t, ((1 + C) * ‖c k u ω‖ + (C / 2 + C ^ 2) * a k u ω) ∂(U k ω).measure :=
          sum_le_sum fun k _ => setIntegral_mono_on
            (integrableOn_Ioc_of_continuous (U k ω) (hc'c k ω).norm 0 t)
            (hib k) measurableSet_Ioc
            fun u _ => hc'le k u ω
      _ = (1 + C) * (∑ k, ∫ u in Ioc 0 t, ‖c k u ω‖ ∂(U k ω).measure) +
          (C / 2 + C ^ 2) * ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun k _ => ?_
          rw [integral_add ((hi1 k).const_mul _) ((hi2 k).const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ V' := by
          rw [hV'def]
          have := hV t ω
          have := hAt t ω
          have hC1 : 0 ≤ 1 + C := by linarith
          have hC2 : 0 ≤ C / 2 + C ^ 2 := by positivity
          nlinarith
  -- continuity, representation and measurability of the enlarged coordinate
  have hDc (ω : Ω) : Continuous fun t => D t ω :=
    continuous_const.add (continuous_finsetSum _ fun k _ =>
      continuous_integral_Ioc_zero (U k ω) (hUc k ω) (hdc k ω))
  have hQc (ω : Ω) : Continuous fun t => bracket F Y M U a t ω :=
    continuous_finsetSum _ fun k _ => continuous_integral_Ioc_zero (U k ω) (hUc k ω) (hqc k ω)
  have hY'c (ω : Ω) : Continuous fun t => Y' t ω := (hYc ω).prodMk ((hDc ω).prodMk (hQc ω))
  have hY' (t : ℝ≥0) (ω : Ω) :
      Y' t ω = Y' 0 ω + ∑ k, ∫ u in Ioc 0 t, c' k u ω ∂(U k ω).measure := by
    have hi (k : Fin m) : Integrable (fun u => c' k u ω) ((U k ω).measure.restrict (Ioc 0 t)) :=
      integrableOn_Ioc_of_continuous (U k ω) (hc'c k ω) 0 t
    have hi' (k : Fin m) : Integrable (fun u => (c' k u ω).2)
        ((U k ω).measure.restrict (Ioc 0 t)) :=
      integrableOn_Ioc_of_continuous (U k ω) ((hdc k ω).prodMk (hqc k ω)) 0 t
    have h1 (k : Fin m) : (∫ u in Ioc 0 t, c' k u ω ∂(U k ω).measure).1 =
        ∫ u in Ioc 0 t, c k u ω ∂(U k ω).measure := fst_integral (hi k)
    have h2 (k : Fin m) : (∫ u in Ioc 0 t, c' k u ω ∂(U k ω).measure).2.1 =
        ∫ u in Ioc 0 t, driftDensity F Y M c a k u ω ∂(U k ω).measure := by
      rw [snd_integral (hi k), fst_integral (hi' k)]
    have h3 (k : Fin m) : (∫ u in Ioc 0 t, c' k u ω ∂(U k ω).measure).2.2 =
        ∫ u in Ioc 0 t, q k u ω ∂(U k ω).measure := by
      rw [snd_integral (hi k), snd_integral (hi' k)]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [hY'def, Prod.fst_add, Prod.fst_sum, h1]
      exact hY t ω
    · simp only [hY'def, Prod.snd_add, Prod.fst_add, Prod.snd_sum, Prod.fst_sum, h2, hDdef,
        integral_Ioc_self_zero, sum_const_zero, add_zero]
    · simp only [hY'def, Prod.snd_add, Prod.snd_sum, h3, bracket, integral_Ioc_self_zero,
        sum_const_zero, zero_add, hqdef]
  have hdm (k : Fin m) (u : ℝ≥0) : Measurable[𝓕 u] (driftDensity F Y M c a k u) :=
    measurable_driftDensity hF (hYa u) (hMa u) (hca k u) (haa k u)
  have hqm (k : Fin m) (u : ℝ≥0) : Measurable[𝓕 u] (q k u) :=
    (((continuous_partialSnd' hF).measurable.comp ((hYa u).prodMk (hMa u))).pow_const 2).mul
      (haa k u)
  have hDm (t : ℝ≥0) : Measurable[𝓕 t] (D t) := by
    refine ((hF.continuous.measurable.comp ((hYa 0).prodMk (hMa 0))).mono (𝓕.mono bot_le)
      le_rfl).add (Finset.measurable_sum _ fun k _ => ?_)
    exact measurable_stieltjesIntegral (hdc k) (U k) (fun u hu => (hdm k u).mono (𝓕.mono hu) le_rfl)
      (fun u hu => (hUa k u).mono (𝓕.mono hu) le_rfl)
  have hQm (t : ℝ≥0) : Measurable[𝓕 t] (bracket F Y M U a t) :=
    Finset.measurable_sum _ fun k _ => measurable_stieltjesIntegral (hqc k) (U k)
      (fun u hu => (hqm k u).mono (𝓕.mono hu) le_rfl) (fun u hu => (hUa k u).mono (𝓕.mono hu) le_rfl)
  have hY'a (t : ℝ≥0) : Measurable[𝓕 t] (Y' t) := (hYa t).prodMk ((hDm t).prodMk (hQm t))
  have hc'a (k : Fin m) (t : ℝ≥0) : Measurable[𝓕 t] (c' k t) :=
    (hca k t).prodMk ((hdm k t).prodMk (hqm k t))
  -- the cut-off `Φ` and the core formula for it
  obtain ⟨χ, hχ, hχc, -, hχ1⟩ := exists_cutoff (isCompact_closedBall (0 : (E × ℝ × ℝ) × ℝ) R₀)
    isOpen_univ (subset_univ _)
  set Φ : (E × ℝ × ℝ) × ℝ → ℝ := fun p => χ p * sqPhi F p with hΦdef
  have hΦ : ContDiff ℝ 3 Φ := hχ.mul (contDiff_sqPhi hF)
  have hΦc : HasCompactSupport Φ := hχc.mul_right
  have hΦeq (t : ℝ≥0) (ω : Ω) : Φ =ᶠ[𝓝 ((Y' t ω, M t ω) : (E × ℝ × ℝ) × ℝ)] sqPhi F := by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet (hstate t ω))] with x hx
    simp [hΦdef, hx]
  have hcore := martingale_residual (P := P) (𝓕 := 𝓕) hΦ hΦc hM hM2 hK hL hR' hV' hMc hAc hY'c
    hc'c hac ha0 hY' hA hY'a hc'a haa hUa
  -- its residual is the squared residual minus the bracket
  have hz (k : Fin m) (t : ℝ≥0) (ω : Ω) :
      ∫ u in Ioc 0 t, driftDensity Φ Y' M c' a k u ω ∂(U k ω).measure = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ)) fun u _ => ?_,
      integral_zero]
    rw [driftDensity_congr (hΦeq u ω)]
    exact partialFst_sqPhi_add_eq_zero hF (Y u ω) (D u ω) (bracket F Y M U a u ω) (M u ω)
      (c k u ω) (a k u ω)
  have heq : residual Φ Y' M U c' a =
      fun t ω => residual F Y M U c a t ω ^ 2 - bracket F Y M U a t ω := by
    funext t ω
    simp only [residual, hz, sum_const_zero, sub_zero]
    rw [(hΦeq t ω).eq_of_nhds, (hΦeq 0 ω).eq_of_nhds]
    simp only [sqPhi, hY'def, hDdef, bracket, integral_Ioc_self_zero, sum_const_zero, add_zero,
      sub_self]
    ring
  rw [← heq]
  exact hcore

end Bracket

end InteractingSLE.Ito.Gm2
