import QuantumZipper.Proofs.Zipper.XFlowEnergyE3Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-ENERGY, E3 (2/3): the circle modulus at radii `ρ ≥ x`

* `energy_mixFc_le_set`: `RegUnif.energy_mixFc_le_strip` (UnifUCE2Basic) with the strip
  `{Im z < τ}` of the base variable replaced by an arbitrary measurable set `S` (same proof);
* `energyCirc_large_le`: for `u, s` fixed and two circles `(d, r)`, `(d', r')` with radii
  `≥ r₀`, `ρ ≥ x`: both `ν_p` are mixtures over the fixed base `circA` (`flowNu_eq_mix`); off the
  set `S` where one of the two source points has `Im < τ`, the pushed centres are
  `(Lc/τ)·δ`-close (`norm_revMap_sub_le_strip`) and the JointMod space modulus
  `abs_kernelCov2_νT_space_unif` bounds the per-point energy; on `S` the crude bound is paid by
  `circA(S) ≤ 36 √(τ/r₀)` (`foldedCircle_strip_le`).

Sources: Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (through the JointMod space
modulus); the mixture/strip interpolation is the D33 E2 argument (own elementary argument).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint RegUnif B2 CharFun MeasUnzip

theorem energy_mixFc_le_set {A : Measure ℂ} [IsProbabilityMeasure A] {w w' : ℂ → ℂ}
    (hw : Measurable w) (hw' : Measurable w') {ψ ψ' : ℂ → ℂ} (hψ : Measurable ψ)
    (hψ' : Measurable ψ') {ρ ρ' α C B : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hL : ∀ᵐ z ∂A, GoodM ((foldedCircle (w z) ρ).map ψ) α C B ∧
      GoodM ((foldedCircle (w' z) ρ').map ψ') α C B)
    {Kb Ks : ℝ} {S : Set ℂ} (hset : MeasurableSet S) (hKb0 : 0 ≤ Kb) (hKs0 : 0 ≤ Ks)
    (hbig : ∀ᵐ z ∂A, z ∉ S →
      kernelCov2 neumannH (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ'))
        (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ')) ≤ Kb)
    (hsmall : ∀ᵐ z ∂A, z ∈ S →
      kernelCov2 neumannH (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ'))
        (((foldedCircle (w z) ρ).map ψ), ((foldedCircle (w' z) ρ').map ψ')) ≤ Ks) :
    kernelCov2 neumannH ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ')
      ((bindFc (A.map w) ρ).map ψ, (bindFc (A.map w') ρ').map ψ') ≤
      (Real.sqrt Kb + Real.sqrt Ks * (A S).toReal) ^ 2 := by
  classical
  set K : ℂ → ℝ := fun z => Kb + (if z ∈ S then Ks else 0) with hKdef
  have hK : ∀ᵐ z ∂A, kernelCov2 neumannH (((foldedCircle (w z) ρ).map ψ),
      ((foldedCircle (w' z) ρ').map ψ')) (((foldedCircle (w z) ρ).map ψ),
      ((foldedCircle (w' z) ρ').map ψ')) ≤ K z := by
    filter_upwards [hbig, hsmall] with z hb hs
    by_cases h : z ∈ S
    · simp only [hKdef]; simp only [h, ite_true]; exact le_trans (hs h) (by linarith)
    · simp only [hKdef]; simp only [h, ite_false, add_zero]; exact hb h
  have hmeas : Measurable fun z : ℂ => Real.sqrt (K z) :=
    Real.continuous_sqrt.measurable.comp
      (measurable_const.add (Measurable.ite hset measurable_const measurable_const))
  have hKi : Integrable (fun z : ℂ => Real.sqrt (K z)) A := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.sqrt (Kb + Ks)) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    simp only [hKdef]
    by_cases h : z ∈ S
    · simp only [h, ite_true]; linarith
    · simp only [h, ite_false, add_zero]; linarith
  have h := energy_mixFc_le hw hw' hψ hψ' hα hC hB hL hK hKi
  -- the strip is paid for by its `A`-measure
  have hpt : ∀ z : ℂ, Real.sqrt (K z) ≤ Real.sqrt Kb + Real.sqrt Ks *
      (S.indicator (fun _ => (1 : ℝ)) z) := by
    intro z
    simp only [hKdef]
    by_cases h : z ∈ S
    · have hmem : z ∈ S := h
      rw [if_pos h, Set.indicator_of_mem hmem]
      have hsq : Kb + Ks ≤ (Real.sqrt Kb + Real.sqrt Ks) ^ 2 := by
        have h1 := Real.sq_sqrt hKb0
        have h2 := Real.sq_sqrt hKs0
        nlinarith [Real.sqrt_nonneg Kb, Real.sqrt_nonneg Ks]
      refine (Real.sqrt_le_sqrt hsq).trans (le_of_eq ?_)
      rw [Real.sqrt_sq (by positivity)]; ring
    · have hmem : z ∉ S := h
      rw [if_neg h, add_zero, Set.indicator_of_notMem hmem, mul_zero, add_zero]
  have hint1 : Integrable (fun z : ℂ => (S.indicator (fun _ => (1 : ℝ)) z)) A := by
    refine Integrable.of_bound (measurable_const.indicator hset).aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs]
    by_cases h : z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ S from h)]; norm_num
    · rw [Set.indicator_of_notMem (show z ∉ S from h)]; norm_num
  have hginteg : Integrable (fun z : ℂ => Real.sqrt Kb + Real.sqrt Ks *
      (S.indicator (fun _ => (1 : ℝ)) z)) A :=
    (integrable_const _).add (hint1.const_mul _)
  have hmono := integral_mono hKi hginteg hpt
  have hcalc : ∫ z : ℂ, (Real.sqrt Kb + Real.sqrt Ks *
      (S.indicator (fun _ => (1 : ℝ)) z)) ∂A =
      Real.sqrt Kb + Real.sqrt Ks * (A S).toReal := by
    rw [integral_add (integrable_const _) (hint1.const_mul _), integral_const_mul,
      integral_indicator_const (1 : ℝ) hset, integral_const]
    simp [Measure.real, probReal_univ]
  have h2 : (∫ (z : ℂ), Real.sqrt (K z) ∂A) ^ 2 ≤
      (Real.sqrt Kb + Real.sqrt Ks * (A S).toReal) ^ 2 :=
    pow_le_pow_left₀ (integral_nonneg fun z => Real.sqrt_nonneg _)
      (hmono.trans (le_of_eq hcalc)) 2
  exact h.trans h2

theorem norm_circleMap_sub_circleMap_le (d d' : ℂ) (r r' θ : ℝ) :
    ‖circleMap d r θ - circleMap d' r' θ‖ ≤ ‖d - d'‖ + |r - r'| := by
  have e : circleMap d r θ - circleMap d' r' θ =
      (d - d') + ((r - r' : ℝ) : ℂ) * Complex.exp (θ * Complex.I) := by
    simp only [circleMap]; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem revBound_le_of {M s T R₁ R₂ : ℝ} (hsT : s ≤ T) (h0 : 0 ≤ R₁) (h12 : R₁ ≤ R₂) :
    revBound M s R₁ ≤ revBound M T R₂ := by
  unfold revBound; rw [abs_of_nonneg h0, abs_of_nonneg (h0.trans h12)]; linarith

theorem circA_map_eq (d : ℂ) (r : ℝ) :
    circA.map (fun z : ℂ => foldH (circleMap d r z.re)) = foldedCircle d r := by
  have hf : Measurable fun z : ℂ => foldH (circleMap d r z.re) :=
    measurable_foldH.comp ((measurable_circleMap d r).comp Complex.measurable_re)
  unfold circA
  rw [foldedCircle, circleUnif_eq_map_circLeb, Measure.map_map measurable_foldH
    (measurable_circleMap d r), Measure.map_map hf Complex.measurable_ofReal]
  rfl

theorem circA_src_facts (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ z ∂circA, foldH (circleMap d r z.re) ∈ H ∧ ‖foldH (circleMap d r z.re)‖ ≤ ‖d‖ + r :=
  circA_ae_eq d (P := fun w => w ∈ H ∧ ‖w‖ ≤ ‖d‖ + r) (measurableSet_H_norm_le _)
    ((TwoPoint.foldedCircle_ae_mem_H d hr).and (TwoPoint.foldedCircle_ae_norm_le d hr.le))

theorem circA_strip_le (d : ℂ) {r τ : ℝ} (hr : 0 < r) (hτ : 0 < τ) :
    circA {z | (foldH (circleMap d r z.re)).im < τ} ≤
      ENNReal.ofReal (18 * Real.sqrt (τ / r)) := by
  have hf : Measurable fun z : ℂ => foldH (circleMap d r z.re) :=
    measurable_foldH.comp ((measurable_circleMap d r).comp Complex.measurable_re)
  have hset : MeasurableSet {w : ℂ | w.im < τ} :=
    (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have e : circA {z | (foldH (circleMap d r z.re)).im < τ} = foldedCircle d r {w | w.im < τ} := by
    rw [← circA_map_eq d r, Measure.map_apply hf hset]; rfl
  rw [e]
  refine le_trans (measure_mono_ae ?_) (foldedCircle_strip_le d hr hτ)
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
  exact fun (hzτ : z.im < τ) => show |z.im| < τ by
    rw [abs_of_pos (show 0 < z.im from hz)]; exact hzτ

/-- **The circle modulus at radii `ρ ≥ x`** (strip form). -/
theorem energyCirc_large_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T Mw : ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T, |W t| ≤ Mw) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hus : u + s ≤ T)
    {d d' : ℂ} {r r' r₀ Rd : ℝ} (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hr' : r₀ ≤ r') (hRd1 : 1 ≤ Rd)
    (hdR : ‖d‖ + r ≤ Rd) (hdR' : ‖d'‖ + r' ≤ Rd) {x ρ τ δ : ℝ} (hx : 0 < x) (hxρ : x ≤ ρ)
    (hρ1 : ρ ≤ 1) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hδ : ‖d - d'‖ + |r - r'| ≤ δ) :
    kernelCov2 neumannH (flowMu W (u, s, d, r) ρ, flowMu W (u, s, d', r') ρ)
      (flowMu W (u, s, d, r) ρ, flowMu W (u, s, d', r') ρ) ≤
    2 * (spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
        ((Real.sqrt (Rd ^ 2 + 4 * T) + 1) * (Rd + 1) / τ * δ) ^ (1 / 12 : ℝ)) +
      2 * (spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
        (2 * revBound (2 * Mw) T Rd) ^ (1 / 12 : ℝ) * (36 * Real.sqrt (τ / r₀)) ^ 2) := by
  have hT : 0 ≤ T := by linarith
  have hM0 : 0 ≤ Mw := (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT⟩)
  have hr0 : 0 < r := hr₀.trans_le hr
  have hr0' : 0 < r' := hr₀.trans_le hr'
  have hρ0 : 0 < ρ := hx.trans_le hxρ
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu, by linarith⟩
  have hRb0 : 0 ≤ revBound (2 * Mw) T Rd := revBound_nonneg (by linarith) hT
  have hsK := spaceK_nonneg_E2 (R := revBound (2 * Mw) T Rd + 1) hM0 hT hx
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hδ
  have hLc0 : 0 ≤ (Real.sqrt (Rd ^ 2 + 4 * T) + 1) * (Rd + 1) := by positivity
  have hKb0 : 0 ≤ spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
      ((Real.sqrt (Rd ^ 2 + 4 * T) + 1) * (Rd + 1) / τ * δ) ^ (1 / 12 : ℝ) := by positivity
  have hKs0 : 0 ≤ spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
      (2 * revBound (2 * Mw) T Rd) ^ (1 / 12 : ℝ) := by positivity
  have hm1 : Measurable fun z : ℂ => foldH (circleMap d r z.re) :=
    measurable_foldH.comp ((measurable_circleMap d r).comp Complex.measurable_re)
  have hm2 : Measurable fun z : ℂ => foldH (circleMap d' r' z.re) :=
    measurable_foldH.comp ((measurable_circleMap d' r').comp Complex.measurable_re)
  have hSm : MeasurableSet ({z : ℂ | (foldH (circleMap d r z.re)).im < τ} ∪
      {z : ℂ | (foldH (circleMap d' r' z.re)).im < τ}) :=
    (measurableSet_lt (Complex.measurable_im.comp hm1) measurable_const).union
      (measurableSet_lt (Complex.measurable_im.comp hm2) measurable_const)
  have hψm : Measurable (revMap (vrev W u) u) := TwoPoint.measurable_revMap (continuous_vrev hW u) hu
  have hV := continuous_vrev hW (u + s)
  have hcen : ∀ (dd : ℂ) (rr : ℝ) (z : ℂ), foldH (circleMap dd rr z.re) ∈ H →
      ‖foldH (circleMap dd rr z.re)‖ ≤ ‖dd‖ + rr → ‖dd‖ + rr ≤ Rd →
      ‖cenM W u s dd rr z‖ ≤ revBound (2 * Mw) T Rd := by
    intro dd rr z h1 h2 h3
    have h0 : 0 ≤ ‖dd‖ + rr := (norm_nonneg _).trans h2
    exact (norm_revMap_le_revBound hV hs
      (fun t _ => abs_vrev_le hM ⟨add_nonneg hu hs, hus⟩ t) _ h2).trans
      (revBound_le_of (by linarith) h0 h3)
  have hpair : ∀ z : ℂ, ‖cenM W u s d r z‖ ≤ revBound (2 * Mw) T Rd →
      ‖cenM W u s d' r' z‖ ≤ revBound (2 * Mw) T Rd →
      kernelCov2 neumannH ((foldedCircle (cenM W u s d r z) ρ).map (revMap (vrev W u) u),
        (foldedCircle (cenM W u s d' r' z) ρ).map (revMap (vrev W u) u))
        ((foldedCircle (cenM W u s d r z) ρ).map (revMap (vrev W u) u),
        (foldedCircle (cenM W u s d' r' z) ρ).map (revMap (vrev W u) u)) ≤
      spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
        ‖cenM W u s d r z - cenM W u s d' r' z‖ ^ (1 / 12 : ℝ) := by
    intro z n1 n2
    have hz1 : ‖cenM W u s d r z‖ + ρ ≤ revBound (2 * Mw) T Rd + 1 := by linarith
    have hz2 : ‖cenM W u s d' r' z‖ + ρ ≤ revBound (2 * Mw) T Rd + 1 := by linarith
    rw [← (goodM_pushed_circle hW hW0 hM huT hx hxρ hz1).1,
      ← (goodM_pushed_circle hW hW0 hM huT hx hxρ hz2).1]
    have hs' := abs_kernelCov2_νT_space_unif hW hW0 hx hM (β := 1 / 12) (by norm_num) le_rfl
      huT hxρ hxρ hz1 hz2
    rw [sub_self, abs_zero, add_zero] at hs'
    exact (le_abs_self _).trans hs'
  have hf1 := circA_src_facts d hr0
  have hf2 := circA_src_facts d' hr0'
  rw [e3_flowMu_eq_map hW hW0 hM hu hs hus d hr0 hρ0, e3_flowMu_eq_map hW hW0 hM hu hs hus d' hr0' hρ0,
    flowNu_eq_mix hW hs d r, flowNu_eq_mix hW hs d' r']
  have key := energy_mixFc_le_set (A := circA) (measurable_cenM hW hs d r)
    (measurable_cenM hW hs d' r') hψm hψm (ρ := ρ) (ρ' := ρ) (α := 1 / 3)
    (C := frostC T x (revBound (2 * Mw) T Rd + 1))
    (B := revBound (2 * Mw) T (revBound (2 * Mw) T Rd + 1))
    (by norm_num) (by unfold frostC; positivity) (revBound_nonneg (by linarith) hT)
    (by
      filter_upwards [hf1, hf2] with z h1 h2
      have n1 := hcen d r z h1.1 h1.2 hdR
      have n2 := hcen d' r' z h2.1 h2.2 hdR'
      exact ⟨(goodM_pushed_circle hW hW0 hM huT hx hxρ (by linarith : ‖cenM W u s d r z‖ + ρ ≤
          revBound (2 * Mw) T Rd + 1)).2,
        (goodM_pushed_circle hW hW0 hM huT hx hxρ (by linarith : ‖cenM W u s d' r' z‖ + ρ ≤
          revBound (2 * Mw) T Rd + 1)).2⟩)
    hSm hKb0 hKs0
    (by
      filter_upwards [hf1, hf2] with z h1 h2 hzS
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hzS
      have n1 := hcen d r z h1.1 h1.2 hdR
      have n2 := hcen d' r' z h2.1 h2.2 hdR'
      refine (hpair z n1 n2).trans (mul_le_mul_of_nonneg_left ?_ hsK)
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
      have hi1 : (foldH (circleMap d r z.re)).im ≤ Rd :=
        (Complex.im_le_norm _).trans (h1.2.trans hdR)
      have hi2 : (foldH (circleMap d' r' z.re)).im ≤ Rd :=
        (Complex.im_le_norm _).trans (h2.2.trans hdR')
      have hl := norm_revMap_sub_le_strip hV hs hτ hzS.1 hi1 hzS.2 hi2
      have hy1 : 1 ≤ Real.sqrt (Rd ^ 2 + 4 * s) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hy2 : Real.sqrt (Rd ^ 2 + 4 * s) ≤ Real.sqrt (Rd ^ 2 + 4 * T) :=
        Real.sqrt_le_sqrt (by linarith)
      have hexp : Real.exp |Real.log (Real.sqrt (Rd ^ 2 + 4 * s))| ≤
          Real.sqrt (Rd ^ 2 + 4 * T) + 1 := by
        refine (exp_abs_log_le (by linarith)).trans ?_
        have : 1 / Real.sqrt (Rd ^ 2 + 4 * s) ≤ 1 := by
          rw [div_le_one (by linarith)]; exact hy1
        linarith
      have hRτ : Rd + 1 / τ ≤ (Rd + 1) / τ := by
        have : Rd ≤ Rd / τ := by rw [le_div_iff₀ hτ]; nlinarith
        rw [add_div]; linarith
      have hΛ : Real.exp |Real.log (Real.sqrt (Rd ^ 2 + 4 * s))| * (Rd + 1 / τ) ≤
          (Real.sqrt (Rd ^ 2 + 4 * T) + 1) * (Rd + 1) / τ := by
        rw [mul_div_assoc]
        exact mul_le_mul hexp hRτ (by have : 0 < 1 / τ := (by positivity); linarith)
          (by positivity)
      have hab : ‖foldH (circleMap d r z.re) - foldH (circleMap d' r' z.re)‖ ≤ δ :=
        (TwoPoint.norm_foldH_sub_le _ _).trans
          ((norm_circleMap_sub_circleMap_le d d' r r' z.re).trans hδ)
      calc ‖cenM W u s d r z - cenM W u s d' r' z‖
          = ‖revMap (vrev W (u + s)) s (foldH (circleMap d r z.re)) -
              revMap (vrev W (u + s)) s (foldH (circleMap d' r' z.re))‖ := rfl
        _ ≤ (Real.exp |Real.log (Real.sqrt (Rd ^ 2 + 4 * s))| * (Rd + 1 / τ)) *
              ‖foldH (circleMap d r z.re) - foldH (circleMap d' r' z.re)‖ := hl
        _ ≤ (Real.sqrt (Rd ^ 2 + 4 * T) + 1) * (Rd + 1) / τ * δ :=
            mul_le_mul hΛ hab (norm_nonneg _) (by positivity))
    (by
      filter_upwards [hf1, hf2] with z h1 h2 _
      have n1 := hcen d r z h1.1 h1.2 hdR
      have n2 := hcen d' r' z h2.1 h2.2 hdR'
      refine (hpair z n1 n2).trans (mul_le_mul_of_nonneg_left ?_ hsK)
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
      exact (norm_sub_le _ _).trans (by linarith))
  refine key.trans ?_
  set m := (circA ({z : ℂ | (foldH (circleMap d r z.re)).im < τ} ∪
      {z : ℂ | (foldH (circleMap d' r' z.re)).im < τ})).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hsq : Real.sqrt (τ / r) ≤ Real.sqrt (τ / r₀) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hτ.le hr₀ hr)
  have hsq' : Real.sqrt (τ / r') ≤ Real.sqrt (τ / r₀) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hτ.le hr₀ hr')
  have hmle : m ≤ 36 * Real.sqrt (τ / r₀) := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    calc circA ({z : ℂ | (foldH (circleMap d r z.re)).im < τ} ∪
          {z : ℂ | (foldH (circleMap d' r' z.re)).im < τ})
        ≤ circA {z : ℂ | (foldH (circleMap d r z.re)).im < τ} +
            circA {z : ℂ | (foldH (circleMap d' r' z.re)).im < τ} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (18 * Real.sqrt (τ / r₀)) + ENNReal.ofReal (18 * Real.sqrt (τ / r₀)) :=
          add_le_add ((circA_strip_le d hr0 hτ).trans (ENNReal.ofReal_le_ofReal (by linarith)))
            ((circA_strip_le d' hr0' hτ).trans (ENNReal.ofReal_le_ofReal (by linarith)))
      _ = ENNReal.ofReal (36 * Real.sqrt (τ / r₀)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  have hm2 : m ^ 2 ≤ (36 * Real.sqrt (τ / r₀)) ^ 2 := pow_le_pow_left₀ hm0 hmle 2
  set Kb := spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
      ((Real.sqrt (Rd ^ 2 + 4 * T) + 1) * (Rd + 1) / τ * δ) ^ (1 / 12 : ℝ) with hKb
  set Ks := spaceK Mw T x (revBound (2 * Mw) T Rd + 1) *
      (2 * revBound (2 * Mw) T Rd) ^ (1 / 12 : ℝ) with hKs
  have e1 := Real.sq_sqrt hKb0
  have e2 := Real.sq_sqrt hKs0
  have h3 : (Real.sqrt Kb + Real.sqrt Ks * m) ^ 2 ≤
      2 * Real.sqrt Kb ^ 2 + 2 * (Real.sqrt Ks ^ 2 * m ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt Kb - Real.sqrt Ks * m)]
  rw [e1, e2] at h3
  have h4 := mul_le_mul_of_nonneg_left hm2 hKs0
  linarith

end F1
end QuantumZipper
