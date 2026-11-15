import InteractingSLE.Spec.Ito.Gm2Path
import MathFin.Probability.Martingales.MartingaleSetIntegral

/-!
# Itô's formula in martingale-problem form for a bounded martingale with a general bracket

Packet PROVE-ITO-GEN2. The bounded core of the formula Theorem 2.6's proof applies
(`source/spec/p001-048.md` L977–L986; Revuz–Yor IV.3.3 in martingale-problem form):

**`martingale_residual`.** Let `M` be a bounded continuous `𝓕`-martingale and `A` a bounded continuous
process with `M² − A` a martingale and `A = A_0 + Σₖ ∫ aₖ dUₖ` (`aₖ ≥ 0`), where the `Uₖ` are random
Stieltjes integrators. Let `Y = Y_0 + Σₖ ∫ cₖ dUₖ` be a bounded adapted finite-variation coordinate of
bounded total variation, and `F` a `C³` function with compact support. Then the mixed residual
`F(Y_t, M_t) − F(Y_0, M_0) − Σₖ ∫_{(0,t]} (∂_y F cₖ + ½ ∂²_x F aₖ) dUₖ` is an `𝓕`-martingale.

The integrators need not be absolutely continuous (singular force-point motions are allowed), and
the bracket need not be Lipschitz. The proof feeds the general engine
(`integral_mul_sub_eq_zero_of_defectExcess`) with the pathwise cell estimates of `Gm2Path`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

section Measurability

variable {Ω : Type*}

/-- **A random Stieltjes integral of a continuous integrand is measurable** for any σ-algebra `m` for
which the integrand and the integrator are measurable at all times up to `t`: it is the pointwise limit
of its uniform left-point Riemann–Stieltjes sums. -/
theorem measurable_stieltjesIntegral {m : MeasurableSpace Ω} {g : ℝ≥0 → Ω → ℝ}
    (hg : ∀ ω, Continuous (g · ω)) (U : Ω → StieltjesFunction ℝ≥0) {t : ℝ≥0}
    (hgm : ∀ u ≤ t, Measurable[m] (g u)) (hUm : ∀ u ≤ t, Measurable[m] fun ω => U ω u) :
    Measurable[m] fun ω => ∫ u in Ioc 0 t, g u ω ∂(U ω).measure := by
  refine measurable_of_tendsto_metrizable (f := fun n ω => ∑ k ∈ range n,
    g (MathFin.unifPartIcc 0 t n k) ω *
      (U ω (MathFin.unifPartIcc 0 t n (k + 1)) - U ω (MathFin.unifPartIcc 0 t n k)))
    (fun n => ?_) (tendsto_pi_nhds.2 fun ω =>
      Gen.tendsto_stieltjes_sum (U ω) (hg ω) (show (0 : ℝ≥0) ≤ t from bot_le))
  refine Finset.measurable_sum _ fun k hk => ?_
  have hn : n ≠ 0 := by rintro rfl; simp at hk
  have hle (j : ℕ) (hj : j ≤ n) : MathFin.unifPartIcc 0 t n j ≤ t := by
    have := MathFin.unifPartIcc_mono 0 t n hj
    rwa [MathFin.unifPartIcc_self (show (0 : ℝ≥0) ≤ t from bot_le) hn] at this
  have hk' : k < n := Finset.mem_range.1 hk
  exact (hgm _ (hle k hk'.le)).mul ((hUm _ (hle (k + 1) hk')).sub (hUm _ (hle k hk'.le)))

end Measurability

section Core

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {m : ℕ}
  {F : E × ℝ → ℝ} {Y : ℝ≥0 → Ω → E} {M A : ℝ≥0 → Ω → ℝ}
  {U : Fin m → Ω → StieltjesFunction ℝ≥0} {c : Fin m → ℝ≥0 → Ω → E} {a : Fin m → ℝ≥0 → Ω → ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma abs_partialSnd_le (F : E × ℝ → ℝ) (p : E × ℝ) : |partialSnd F p| ≤ ‖fderiv ℝ F p‖ := by
  have h := (fderiv ℝ F p).le_opNorm ((0 : E), (1 : ℝ))
  rw [norm_zero_one, mul_one] at h
  rw [← Real.norm_eq_abs]; exact h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_partialFst_apply (hF : ContDiff ℝ 3 F) :
    Continuous fun q : (E × ℝ) × E => partialFst F q.1 q.2 :=
  (((hF.continuous_fderiv (by norm_num)).clm_comp continuous_const).comp continuous_fst).clm_apply
    continuous_snd

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_partialSnd' (hF : ContDiff ℝ 3 F) : Continuous (partialSnd F) :=
  (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_partialSndSnd' (hF : ContDiff ℝ 3 F) : Continuous (partialSndSnd F) :=
  (((hF.fderiv_right (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).continuous_fderiv
    (by norm_num)).clm_apply continuous_const).clm_apply continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_driftDensity (hF : ContDiff ℝ 3 F) {ω : Ω} (hYc : Continuous (Y · ω))
    (hMc : Continuous (M · ω)) {k : Fin m} (hcc : Continuous (c k · ω))
    (hac : Continuous (a k · ω)) : Continuous fun u => driftDensity F Y M c a k u ω :=
  ((continuous_partialFst_apply hF).comp ((hYc.prodMk hMc).prodMk hcc)).add
    ((continuous_const.mul ((continuous_partialSndSnd' hF).comp (hYc.prodMk hMc))).mul hac)

omit [FiniteDimensional ℝ E] in
lemma measurable_driftDensity [SecondCountableTopology E] (hF : ContDiff ℝ 3 F)
    {mm : MeasurableSpace Ω} {u : ℝ≥0} {k : Fin m}
    (hY : Measurable[mm] (Y u)) (hM : Measurable[mm] (M u)) (hc : Measurable[mm] (c k u))
    (ha : Measurable[mm] (a k u)) : Measurable[mm] (driftDensity F Y M c a k u) :=
  ((continuous_partialFst_apply hF).measurable.comp ((hY.prodMk hM).prodMk hc)).add
    ((measurable_const.mul ((continuous_partialSndSnd' hF).measurable.comp (hY.prodMk hM))).mul ha)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma abs_driftDensity_le {C : ℝ} (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C)
    (hD2 : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C) (ha0 : ∀ k u ω, 0 ≤ a k u ω) (k : Fin m) (u : ℝ≥0)
    (ω : Ω) : |driftDensity F Y M c a k u ω| ≤ C * ‖c k u ω‖ + 1 / 2 * C * a k u ω := by
  unfold driftDensity
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← Real.norm_eq_abs]
    exact ((partialFst F _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((norm_partialFst_le _).trans (hD1 _)) (norm_nonneg _))
  · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg (ha0 k u ω),
      mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      ((abs_partialSndSnd_le _).trans (hD2 _)) (ha0 k u ω)) (by norm_num)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The drift integral is bounded** by `C (TV + ½ Σₖ ∫ aₖ dUₖ)`. -/
lemma abs_sum_integral_driftDensity_le {C : ℝ} (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C)
    (hD2 : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C) (ha0 : ∀ k u ω, 0 ≤ a k u ω) {ω : Ω}
    (hcc : ∀ k, Continuous (c k · ω)) (hac : ∀ k, Continuous (a k · ω)) (t : ℝ≥0) :
    |∑ k, ∫ u in Ioc 0 t, driftDensity F Y M c a k u ω ∂(U k ω).measure| ≤
      C * (∑ k, ∫ u in Ioc 0 t, ‖c k u ω‖ ∂(U k ω).measure) +
        1 / 2 * C * ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure := by
  have hk (k : Fin m) : |∫ u in Ioc 0 t, driftDensity F Y M c a k u ω ∂(U k ω).measure| ≤
      C * (∫ u in Ioc 0 t, ‖c k u ω‖ ∂(U k ω).measure) +
        1 / 2 * C * ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure := by
    rw [← Real.norm_eq_abs, ← integral_const_mul, ← integral_const_mul, ← integral_add
      ((integrableOn_Ioc_of_continuous (U k ω) (hcc k).norm 0 t).const_mul C)
      ((integrableOn_Ioc_of_continuous (U k ω) (hac k) 0 t).const_mul _)]
    refine norm_integral_le_of_norm_le (((integrableOn_Ioc_of_continuous (U k ω)
      (hcc k).norm 0 t).const_mul C).add
      ((integrableOn_Ioc_of_continuous (U k ω) (hac k) 0 t).const_mul _)) (.of_forall fun u => ?_)
    rw [Real.norm_eq_abs]
    exact abs_driftDensity_le hD1 hD2 ha0 k u ω
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun k _ => hk k).trans ?_)
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]

/-- **Itô's formula in martingale-problem form, bounded case.** See the module docstring. -/
theorem martingale_residual [IsProbabilityMeasure P]
    (hF : ContDiff ℝ 3 F) (hFc : HasCompactSupport F)
    (hM : Martingale M 𝓕 P) (hM2 : Martingale (fun t ω => M t ω ^ 2 - A t ω) 𝓕 P)
    {K L R V : ℝ} (hK : ∀ t ω, |M t ω| ≤ K) (hL : ∀ t ω, |A t ω| ≤ L)
    (hR : ∀ t ω, ‖Y t ω‖ ≤ R)
    (hV : ∀ t ω, ∑ k, ∫ u in Ioc 0 t, ‖c k u ω‖ ∂(U k ω).measure ≤ V)
    (hMc : ∀ ω, Continuous (M · ω)) (hAc : ∀ ω, Continuous (A · ω))
    (hYc : ∀ ω, Continuous (Y · ω)) (hcc : ∀ k ω, Continuous (c k · ω))
    (hac : ∀ k ω, Continuous (a k · ω)) (ha0 : ∀ k u ω, 0 ≤ a k u ω)
    (hY : ∀ t ω, Y t ω = Y 0 ω + ∑ k, ∫ u in Ioc 0 t, c k u ω ∂(U k ω).measure)
    (hA : ∀ t ω, A t ω = A 0 ω + ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure)
    (hYa : ∀ t, Measurable[𝓕 t] (Y t)) (hca : ∀ k t, Measurable[𝓕 t] (c k t))
    (haa : ∀ k t, Measurable[𝓕 t] (a k t)) (hUa : ∀ k t, Measurable[𝓕 t] fun ω => U k ω t) :
    Martingale (residual F Y M U c a) 𝓕 P := by
  obtain ⟨C, hC0, hFb, hD1, hD2, hLip1, hLip2', hLip2⟩ := exists_bound_of_contDiff_three hF hFc
  have hMa (t : ℝ≥0) : Measurable[𝓕 t] (M t) := (hM.stronglyAdapted t).measurable
  -- monotonicity of the bracket
  have hAinc (ω : Ω) {s t : ℝ≥0} (hst : s ≤ t) : A t ω - A s ω =
      ∑ k, ∫ u in Ioc s t, a k u ω ∂(U k ω).measure := by
    rw [hA t ω, hA s ω, add_sub_add_left_eq_sub, ← sum_sub_distrib]
    exact sum_congr rfl fun k _ => integral_Ioc_zero_sub (U k ω) (hac k ω) hst
  have hAm (ω : Ω) : Monotone (A · ω) := fun s t hst => by
    have := hAinc ω hst
    have h0 : 0 ≤ ∑ k, ∫ u in Ioc s t, a k u ω ∂(U k ω).measure :=
      sum_nonneg fun k _ => setIntegral_nonneg measurableSet_Ioc fun u _ => ha0 k u ω
    simp only; linarith
  -- adaptedness of the residual
  have hXm (t : ℝ≥0) : Measurable[𝓕 t] (residual F Y M U c a t) := by
    have h0 : Measurable[𝓕 t] fun ω => F (Y 0 ω, M 0 ω) :=
      (hF.continuous.measurable.comp ((hYa 0).prodMk (hMa 0))).mono (𝓕.mono bot_le) le_rfl
    refine ((hF.continuous.measurable.comp ((hYa t).prodMk (hMa t))).sub h0).sub
      (Finset.measurable_sum _ fun k _ => ?_)
    exact measurable_stieltjesIntegral (fun ω => continuous_driftDensity hF (hYc ω) (hMc ω)
      (hcc k ω) (hac k ω)) (U k) (fun u hu => (measurable_driftDensity hF (hYa u) (hMa u)
        (hca k u) (haa k u)).mono (𝓕.mono hu) le_rfl)
      (fun u hu => (hUa k u).mono (𝓕.mono hu) le_rfl)
  -- boundedness of the residual
  have hdrift (t : ℝ≥0) (ω : Ω) :
      |∑ k, ∫ u in Ioc 0 t, driftDensity F Y M c a k u ω ∂(U k ω).measure| ≤ C * (V + L) := by
    have hAt : ∑ k, ∫ u in Ioc 0 t, a k u ω ∂(U k ω).measure ≤ 2 * L := by
      have := hAinc ω (s := 0) (t := t) bot_le
      have h2 := (le_abs_self _).trans (MathFin.LevyQuadraticSums.abs_sub_le_two_mul hL 0 t ω)
      linarith
    refine (abs_sum_integral_driftDensity_le hD1 hD2 ha0 (fun k => hcc k ω) (fun k => hac k ω)
      t).trans ?_
    nlinarith [hV t ω]
  have hXb (t : ℝ≥0) (ω : Ω) : |residual F Y M U c a t ω| ≤ 2 * C + C * (V + L) := by
    unfold residual
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans ?_) (hdrift t ω))
    linarith [hFb (Y t ω, M t ω), hFb (Y 0 ω, M 0 ω)]
  have hXi (t : ℝ≥0) : Integrable (residual F Y M U c a t) P :=
    integrable_of_abs_le ((hXm t).mono (𝓕.le t) le_rfl) (hXb t)
  -- the frozen coefficients
  have hc1 (r : ℝ≥0) : StronglyMeasurable[𝓕 r] (fun ω => partialSnd F (Y r ω, M r ω)) :=
    ((continuous_partialSnd' hF).measurable.comp ((hYa r).prodMk (hMa r))).stronglyMeasurable
  have hc2 (r : ℝ≥0) : StronglyMeasurable[𝓕 r] (fun ω => partialSndSnd F (Y r ω, M r ω)) :=
    ((continuous_partialSndSnd' hF).measurable.comp ((hYa r).prodMk (hMa r))).stronglyMeasurable
  have hc1b (r : ℝ≥0) (ω : Ω) : |partialSnd F (Y r ω, M r ω)| ≤ C :=
    (abs_partialSnd_le _ _).trans (hD1 _)
  have hc2b (r : ℝ≥0) (ω : Ω) : |partialSndSnd F (Y r ω, M r ω)| ≤ C :=
    (abs_partialSndSnd_le _).trans (hD2 _)
  -- the uniform bound and the pathwise limit of the excesses
  set η₀ := 2 * |R| + 2 * |K| with hη₀def
  have hη₀ : 0 ≤ η₀ := by positivity
  have hdom (s t : ℝ≥0) (hst : s ≤ t) (n : ℕ) (ω : Ω) :
      defectExcess (residual F Y M U c a) (fun r ω => partialSnd F (Y r ω, M r ω))
        (fun r ω => partialSndSnd F (Y r ω, M r ω)) M A C s t n ω ≤
        C * η₀ * (3 * V + 2 * L) := by
    refine (defectExcess_residual_le hF hC0 hLip1 hLip2' hLip2 (hYc ω) (hMc ω) (fun k => hcc k ω)
      (fun k => hac k ω) (fun k u => ha0 k u ω) (fun t => hY t ω) (fun t => hA t ω) hst n hη₀
      fun k _ u _ => ⟨?_, ?_⟩).trans ?_
    · calc ‖Y u ω - Y (MathFin.unifPartIcc s t n k) ω‖
          ≤ ‖Y u ω‖ + ‖Y (MathFin.unifPartIcc s t n k) ω‖ := norm_sub_le _ _
        _ ≤ η₀ := by linarith [hR u ω, hR (MathFin.unifPartIcc s t n k) ω, le_abs_self R,
            abs_nonneg K]
    · calc |M u ω - M (MathFin.unifPartIcc s t n k) ω|
          ≤ |M u ω| + |M (MathFin.unifPartIcc s t n k) ω| := abs_sub _ _
        _ ≤ η₀ := by linarith [hK u ω, hK (MathFin.unifPartIcc s t n k) ω, le_abs_self K,
            abs_nonneg R]
    · have hTV : (∑ k, ∫ u in Ioc s t, ‖c k u ω‖ ∂(U k ω).measure) ≤ V := by
        refine le_trans (sum_le_sum fun k _ => setIntegral_mono_set
          (integrableOn_Ioc_of_continuous (U k ω) (hcc k ω).norm 0 t)
          ((ae_restrict_iff' measurableSet_Ioc).2 (.of_forall fun u _ => norm_nonneg _))
          (Eventually.of_forall (Ioc_subset_Ioc_left bot_le))) (hV t ω)
      have hA2 : A t ω - A s ω ≤ 2 * L :=
        (le_abs_self _).trans (MathFin.LevyQuadraticSums.abs_sub_le_two_mul hL s t ω)
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0 hη₀)
  -- the martingale property, tested against past events
  refine martingale_iff_setIntegral_eq.2 ⟨fun t => (hXm t).stronglyMeasurable, hXi, ?_⟩
  intro s t hst H hH
  let ξ : Ω → ℝ := H.indicator (fun _ => 1)
  have hξ : Measurable[𝓕 s] ξ := measurable_const.indicator hH
  have hξb (ω : Ω) : |ξ ω| ≤ 1 := by
    by_cases hω : ω ∈ H
    · simp only [ξ, Set.indicator_of_mem hω, abs_one, le_refl]
    · simp only [ξ, Set.indicator_of_notMem hω, abs_zero, zero_le_one]
  have hz := integral_mul_sub_eq_zero_of_defectExcess hM hM2 hK hL hAm hMc hAc hst
    (fun r => (hXm r).mono (𝓕.le r) le_rfl) hXi hc1 hc2 hc1b hc2b (hdom s t hst)
    (fun ω => tendsto_defectExcess_residual hF hC0 hLip1 hLip2' hLip2 (hYc ω) (hMc ω)
      (fun k => hcc k ω) (fun k => hac k ω) (fun k u => ha0 k u ω) (fun t => hY t ω)
      (fun t => hA t ω) hst) hξ.stronglyMeasurable hξb
  have hξi (r : ℝ≥0) : Integrable (fun ω => ξ ω * residual F Y M U c a r ω) P :=
    (hXi r).bdd_mul (hξ.mono (𝓕.le s) le_rfl).aestronglyMeasurable (.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hξb ω)
  have heq (r : ℝ≥0) : (fun ω => ξ ω * residual F Y M U c a r ω) =
      H.indicator (residual F Y M U c a r) := by
    funext ω
    by_cases hω : ω ∈ H
    · simp only [ξ, Set.indicator_of_mem hω, one_mul]
    · simp only [ξ, Set.indicator_of_notMem hω, zero_mul]
  simp_rw [mul_sub] at hz
  rw [integral_sub (hξi t) (hξi s), heq t, heq s,
    integral_indicator (𝓕.le s H hH), integral_indicator (𝓕.le s H hH), sub_eq_zero] at hz
  exact hz.symm

end Core

end InteractingSLE.Ito.Gm2
