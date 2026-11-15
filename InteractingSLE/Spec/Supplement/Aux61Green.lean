/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAHL7
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal

/-!
# Aux. lemmas 61–62, deterministic layer: the Green potential of a source along the Loewner flow

Packet PROVE-GB7A2. Source: specification Aux. lemmas 61–62 (`source/spec/p241-288.md`, pp. 261–263): the
Cameron–Martin comparison of a flow line with a reference flow line through a cutoff `f` of the difference of the
two harmonic means, whose source `v = −(2π)⁻¹ Δ f` lies away from the hulls. This project replaces the Gaussian
field by its deterministic shadow: the conditional Cameron–Martin exponent `(𝔥_t − 𝔥_0, v) + ½ G_t(v, v)` is never
formed; only its two ingredients are used, the Green potential `G_{ℍ∖K_s} v` and the source drift
`A(u) = ∫ Im(2/f_u(z)) v(z) dz`.

This file proves, for an abstract bounded source `v` supported away from the hulls (`IsSrc`), the generic facts the
route needs (the source-specific facts of `Spec/Sec7/LocalExtAHL6` in general form):

* `IsSrc.greenPot_eq`: **the integrated Loewner–Green identity against `v`**,
  `G_{ℍ∖K_s} v (y) = G_ℍ v (y) − ∫₀ˢ Im(2/f_u(y)) A(u) du`;
* `IsSrc.continuousOn_srcDrift`, `IsSrc.abs_srcDrift_le`: continuity and boundedness of the source drift;
* `integral_greenH_mul_indicator_greenDensity`: **Green inversion** `G_ℍ(−(2π)⁻¹ Δ f) = f` on `ℍ` for an odd
  compactly supported `C²` function `f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H fwdMap fwdHull IsForwardSol greenH)

/-! ### Sources away from the hulls -/

variable (W : ℝ → ℝ) (v : ℂ → ℝ)

/-- **The source drift** `A(u) = ∫ Im(2/f_u(z)) v(z) dz`. -/
def srcDrift (u : ℝ) : ℝ := ∫ z, (2 / fwdMap W u z).im * v z

/-- **The Green potential of `v` in `ℍ ∖ K_s`**: `G_{ℍ∖K_s} v (y) = ∫ G_ℍ(f_s y, f_s z) v(z) dz`. -/
def greenPot (s : ℝ) (y : ℂ) : ℝ := ∫ z, greenH (fwdMap W s y) (fwdMap W s z) * v z

/-- **The Green potential of `v` in `ℍ`**: `G_ℍ v (y) = ∫ G_ℍ(y, z) v(z) dz`. -/
def greenPot0 (y : ℂ) : ℝ := ∫ z, greenH y z * v z

/-- **A source for the time interval `[0, t]`**: `v` is measurable, bounded by `Cv`, and vanishes off a bounded
set of points of `ℍ` that are alive through `[0, t]` and stay at distance `≥ m > 0` from the driver. -/
structure IsSrc (t Cv R m : ℝ) : Prop where
  meas : Measurable v
  bound : ∀ z, |v z| ≤ Cv
  m_pos : 0 < m
  alive : ∀ z, v z ≠ 0 → z ∈ H \ fwdHull W t
  norm_le : ∀ z, v z ≠ 0 → ‖z‖ ≤ R
  far : ∀ z, v z ≠ 0 → ∀ u ∈ Icc (0 : ℝ) t, m ≤ ‖fwdMap W u z‖

variable {W v}

namespace IsSrc

variable {t Cv R m : ℝ}

theorem Cv_nonneg (h : IsSrc W v t Cv R m) : 0 ≤ Cv := (abs_nonneg _).trans (h.bound 0)

/-- `v` is dominated by `Cv` times the indicator of the closed ball of radius `R`. -/
theorem abs_le_indicator (h : IsSrc W v t Cv R m) (z : ℂ) :
    |v z| ≤ Cv * (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hz : v z = 0
  · rw [hz, abs_zero]
    exact mul_nonneg h.Cv_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  · rw [Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact h.norm_le z hz), mul_one]
    exact h.bound z

theorem integrable (h : IsSrc W v t Cv R m) : Integrable v := by
  have hball : Integrable fun z : ℂ => (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  exact (hball.const_mul Cv).mono' h.meas.aestronglyMeasurable
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact h.abs_le_indicator z)

/-- `|Im(2/f_u(z))| ≤ 2/m` on the source. -/
theorem abs_im_two_div_le (h : IsSrc W v t Cv R m) {u : ℝ} (hu : u ∈ Icc 0 t) {z : ℂ} (hz : v z ≠ 0) :
    |(2 / fwdMap W u z).im| ≤ 2 / m :=
  LocalExt.abs_im_two_div_le_of_norm h.m_pos (h.far z hz u hu)

/-- `Im(2/f_u)` on the support of `v`, `0` elsewhere (a measurable version of the kernel). -/
def srcKer (W : ℝ → ℝ) (v : ℂ → ℝ) (u : ℝ) (z : ℂ) : ℝ :=
  open Classical in if v z ≠ 0 then (2 / fwdMap W u z).im else 0

theorem srcKer_mul (W : ℝ → ℝ) (v : ℂ → ℝ) (u : ℝ) (z : ℂ) :
    srcKer W v u z * v z = (2 / fwdMap W u z).im * v z := by
  by_cases hz : v z = 0
  · simp [hz]
  · simp [srcKer, hz]

theorem continuousOn_fwdMap_time (h : IsSrc W v t Cv R m) (hW : Continuous W) (ht : 0 ≤ t) {z : ℂ}
    (hz : v z ≠ 0) : ContinuousOn (fun u => fwdMap W u z) (Icc 0 t) :=
  Ito.continuousOn_fwdMap_time' hW ht (h.alive z hz)

/-- The kernel `(u, z) ↦ Im(2/f_u(z))` is continuous in `u ∈ [0, t]` on the support of `v`. -/
theorem continuousOn_srcKer (h : IsSrc W v t Cv R m) (hW : Continuous W) (ht : 0 ≤ t) (z : ℂ) :
    ContinuousOn (fun u => srcKer W v u z) (Icc 0 t) := by
  by_cases hz : v z = 0
  · simp only [srcKer, hz, ne_eq, not_true_eq_false, ite_false]; exact continuousOn_const
  · simp only [srcKer, hz, ne_eq, not_false_eq_true, ite_true]
    exact Complex.continuous_im.comp_continuousOn (continuousOn_const.div (h.continuousOn_fwdMap_time hW ht hz)
      fun u hu => Ito.fwdMap_ne_zero hW ht (h.alive z hz) hu)

/-- The kernel is measurable in `z` at each time `u ∈ [0, t]`. -/
theorem measurable_srcKer (h : IsSrc W v t Cv R m) (hW : Continuous W) {u : ℝ} (hu : u ∈ Icc 0 t) :
    Measurable (srcKer W v u) := by
  classical
  have hS : MeasurableSet {z | v z ≠ 0} := (h.meas (measurableSet_singleton 0)).compl
  have hopen := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hu.1
  have hsub : {z | v z ≠ 0} ⊆ H \ fwdHull W u := fun z hz =>
    Ito.mem_diff_fwdHull_of_le (h.alive z hz) hu.2
  have hc : ContinuousOn (fun z => (2 / fwdMap W u z).im) (H \ fwdHull W u) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_const.div
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hu.1).continuousOn)
      fun z hz => Ito.fwdMap_ne_zero hW hu.1 hz ⟨hu.1, le_rfl⟩)
  have hm : Measurable fun z => (H \ fwdHull W u).piecewise (fun z => (2 / fwdMap W u z).im) (fun _ => 0) z :=
    hc.measurable_piecewise continuousOn_const hopen.measurableSet
  have he : srcKer W v u = fun z => {z | v z ≠ 0}.piecewise
      (fun z => (H \ fwdHull W u).piecewise (fun z => (2 / fwdMap W u z).im) (fun _ => 0) z) (fun _ => 0) z := by
    funext z
    by_cases hz : v z = 0
    · simp [srcKer, hz, Set.piecewise]
    · have hz' : z ∈ H \ fwdHull W u := hsub hz
      simp [srcKer, hz, Set.piecewise, hz']
  rw [he]
  exact Measurable.piecewise hS hm measurable_const

/-- **The source drift is continuous** on `[0, t]` (dominated convergence). -/
theorem continuousOn_srcDrift (h : IsSrc W v t Cv R m) (hW : Continuous W) (ht : 0 ≤ t) :
    ContinuousOn (srcDrift W v) (Icc 0 t) := by
  have he : srcDrift W v = fun u => ∫ z, srcKer W v u z * v z := by
    funext u; exact integral_congr_ae (ae_of_all _ fun z => (srcKer_mul W v u z).symm)
  rw [he]
  refine continuousOn_of_dominated (bound := fun z => 2 / m * |v z|)
    (fun u hu => ((h.measurable_srcKer hW hu).mul h.meas).aestronglyMeasurable)
    (fun u hu => ae_of_all _ fun z => ?_) (h.integrable.abs.const_mul _) (ae_of_all _ fun z => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    by_cases hz : v z = 0
    · simp [hz]
    · simp only [srcKer, hz, ne_eq, not_false_eq_true, ite_true]
      exact mul_le_mul_of_nonneg_right (h.abs_im_two_div_le hu hz) (abs_nonneg _)
  · exact (h.continuousOn_srcKer hW ht z).mul continuousOn_const

theorem abs_srcDrift_le (h : IsSrc W v t Cv R m) {u : ℝ} (hu : u ∈ Icc 0 t) :
    |srcDrift W v u| ≤ 2 / m * ∫ z, |v z| := by
  rw [srcDrift, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    (h.integrable.abs.const_mul _) (ae_of_all _ fun z => ?_))
  beta_reduce
  rw [abs_mul]
  by_cases hz : v z = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (h.abs_im_two_div_le hu hz) (abs_nonneg _)

/-- A continuous compactly supported bump equal to `1` on `B̄(0, R)`. -/
theorem exists_bump (R : ℝ) : ∃ ψ : ℂ → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ z, 0 ≤ ψ z) ∧
    ∀ z, ‖z‖ ≤ R → ψ z = 1 := by
  set R₁ := max R 0
  have h0 : 0 ≤ R₁ := le_max_right _ _
  refine ⟨LocalExt.cutoffFn R₁ (R₁ + 1), LocalExt.contDiff_cutoffFn.continuous (n := 0), ?_, ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R₁ + 1)) fun z hz => by
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact LocalExt.cutoffFn_eq_zero h0 (by linarith) hz.le
  · intro z; exact Real.smoothTransition.nonneg _
  · intro z hz; exact LocalExt.cutoffFn_eq_one h0 (by linarith) (hz.trans (le_max_left _ _))

/-- `G_ℍ(y, ·) v` is integrable. -/
theorem integrable_greenH_mul (h : IsSrc W v t Cv R m) (y : ℂ) : Integrable fun z => greenH y z * v z := by
  obtain ⟨ψ, hψc, hψs, hψ0, hψ1⟩ := exists_bump R
  have i1 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hψc hψs (conj y)
  have i2 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hψc hψs y
  have hg : Integrable fun z => Cv * (|Real.log ‖z - conj y‖ * ψ z| + |Real.log ‖z - y‖ * ψ z|) :=
    (i1.abs.add i2.abs).const_mul Cv
  have hm : AEStronglyMeasurable (fun z => greenH y z * v z) volume := by
    have : Measurable fun z => greenH y z := by
      unfold greenH
      exact ((measurable_const.sub (Complex.continuous_conj.measurable)).norm.log).sub
        ((measurable_const.sub measurable_id).norm.log)
    exact (this.mul h.meas).aestronglyMeasurable
  refine hg.mono' hm (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : v z = 0
  · rw [hz, abs_zero, mul_zero]
    exact mul_nonneg h.Cv_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
  · have hψz : ψ z = 1 := hψ1 z (h.norm_le z hz)
    rw [hψz, mul_one, mul_one, mul_comm]
    refine mul_le_mul (h.bound z) ?_ (abs_nonneg _) h.Cv_nonneg
    unfold greenH
    rw [QuantumZipper.norm_sub_conj_comm y z, norm_sub_rev y z]
    exact abs_sub _ _

/-- **The integrated Loewner–Green identity against the source**: for `y` alive at `s ≤ t`,
`G_{ℍ∖K_s} v (y) = G_ℍ v (y) − ∫₀ˢ Im(2/f_u(y)) A(u) du` (Hadamard's formula (3.16) integrated against `v`,
Fubini). -/
theorem greenPot_eq (h : IsSrc W v t Cv R m) (hW : Continuous W) {s : ℝ} (hs : s ∈ Icc 0 t) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) :
    greenPot W v s y = greenPot0 v y - ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * srcDrift W v u := by
  classical
  have hs0 := hs.1
  have ht : 0 ≤ t := hs0.trans hs.2
  -- the kernel at `y` is bounded on `[0, s]`
  set δ := (fwdMap W s y).im with hδ
  have hδpos : 0 < δ := Ito.im_fwdMap_pos hW hs0 hy ⟨hs0, le_rfl⟩
  have hanti := (QuantumZipper.im_isForwardSol_le hW hy.1 (Ito.isForwardSol_fwdMap_of_mem hW hs0 hy)).1
  have hky : ∀ u ∈ Icc (0 : ℝ) s, |(2 / fwdMap W u y).im| ≤ 2 / δ := fun u hu => by
    have hle : δ ≤ (fwdMap W u y).im := hanti hu ⟨hs0, le_rfl⟩ hu.2
    exact LocalExt.abs_im_two_div_le_of_norm hδpos (hle.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _)))
  have hcl : ∀ u, LocalExt.clampS s u ∈ Icc 0 t := fun u =>
    ⟨(LocalExt.clampS_mem hs0 u).1, (LocalExt.clampS_mem hs0 u).2.trans hs.2⟩
  -- the integrand on `ℝ × ℂ`
  set F : ℝ → ℂ → ℝ := fun u z => (2 / fwdMap W (LocalExt.clampS s u) y).im *
    (srcKer W v (LocalExt.clampS s u) z * v z) with hF_def
  have hcy : Continuous fun u => (2 / fwdMap W (LocalExt.clampS s u) y).im := by
    refine Complex.continuous_im.comp ?_
    have hc := (Ito.continuousOn_fwdMap_time' hW hs0 hy).comp_continuous (LocalExt.continuous_clampS s)
      (LocalExt.clampS_mem hs0)
    exact continuous_const.div hc fun u => Ito.fwdMap_ne_zero hW hs0 hy (LocalExt.clampS_mem hs0 u)
  have hFm : Measurable fun p : ℝ × ℂ => F p.1 p.2 := by
    refine Coupling.measurable_uncurry_of_continuousOn isClosed_univ (0 : ℝ) (fun z => ?_) (fun u _ => ?_)
      (fun u hu => absurd (mem_univ u) hu)
    · refine Continuous.continuousOn ?_
      have hk : Continuous fun u => srcKer W v (LocalExt.clampS s u) z :=
        (h.continuousOn_srcKer hW ht z).comp_continuous (LocalExt.continuous_clampS s) hcl
      exact hcy.mul (hk.mul continuous_const)
    · exact measurable_const.mul ((h.measurable_srcKer hW (hcl u)).mul h.meas)
  -- the bound
  set K := 2 / δ * (2 / m) * Cv with hK
  have hFb : ∀ u z, |F u z| ≤ K * (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z := by
    intro u z
    by_cases hz : v z = 0
    · simp only [hF_def, hz, mul_zero, abs_zero]
      exact mul_nonneg (by have := h.Cv_nonneg; have := h.m_pos; positivity)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · rw [Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact h.norm_le z hz), mul_one]
      simp only [hF_def, srcKer, hz, ne_eq, not_false_eq_true, ite_true, abs_mul]
      have h1 := hky _ (LocalExt.clampS_mem hs0 u)
      have h2 := h.abs_im_two_div_le (hcl u) hz
      have h3 := h.bound z
      have hm2 : 0 ≤ 2 / m := div_nonneg zero_le_two h.m_pos.le
      calc |(2 / fwdMap W (LocalExt.clampS s u) y).im| * (|(2 / fwdMap W (LocalExt.clampS s u) z).im| * |v z|)
          ≤ 2 / δ * (2 / m * Cv) := by gcongr
        _ = K := by rw [hK]; ring
  have hint : Integrable (Function.uncurry F) ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => (1 : ℝ)) p.1 *
        (fun z => K * (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z) p.2)
        ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
      have hball : Integrable fun z : ℂ => (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z :=
        (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) s)) := by
        rw [uIoc_of_le hs0]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact Integrable.mul_prod (L := ℝ) (integrable_const _) (hball.const_mul K)
    refine hg.mono' hFm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, one_mul, Real.norm_eq_abs]
    exact hFb p.1 p.2
  -- the swap
  have hswap := intervalIntegral_integral_swap hint
  have hleft : ∫ u in (0 : ℝ)..s, ∫ z, F u z = ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * srcDrift W v u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs0] at hu
    simp only [hF_def, LocalExt.clampS_of_mem hu, integral_const_mul, srcDrift]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => srcKer_mul W v u z)
  have hright : ∀ z, z ≠ y → greenH (fwdMap W s y) (fwdMap W s z) * v z =
      greenH y z * v z - ∫ u in (0 : ℝ)..s, F u z := by
    intro z hzy
    by_cases hz : v z = 0
    · simp [hF_def, hz]
    · have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le (h.alive z hz) hs.2
      rw [Ito.greenH_fwdMap_eq_sub_integral hW hs0 hy hzs hzy.symm, sub_mul]
      congr 1
      rw [← intervalIntegral.integral_mul_const]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hs0] at hu
      simp only [hF_def, LocalExt.clampS_of_mem hu, srcKer, hz, ne_eq, not_false_eq_true, ite_true]
      ring
  have hFi : Integrable fun z => ∫ u in (0 : ℝ)..s, F u z := by
    have := hint.integral_prod_right
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, intervalIntegral.integral_of_le hs0, uIoc_of_le hs0]
  have hae : (fun z => greenH (fwdMap W s y) (fwdMap W s z) * v z) =ᵐ[volume]
      fun z => greenH y z * v z - ∫ u in (0 : ℝ)..s, F u z := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)] with z hz
    exact hright z hz
  rw [greenPot, integral_congr_ae hae, integral_sub (h.integrable_greenH_mul y) hFi, ← hswap, hleft, greenPot0]

end IsSrc

/-! ### Green inversion for odd functions -/

/-- `G_ℍ(w, z̄) = −G_ℍ(w, z)`. -/
theorem greenH_conj_right (w z : ℂ) : greenH w (conj z) = -greenH w z := by
  simp only [greenH, Complex.conj_conj]
  ring

section Inversion

variable {f : ℂ → ℝ} (h2 : ContDiff ℝ 2 f) (hc : HasCompactSupport f) (hodd : ∀ z, f (conj z) = -f z)
include h2 hc

omit hc in
theorem continuous_greenDensity : Continuous (QuantumZipper.K3.greenDensity f) :=
  QuantumZipper.K3.continuous_greenDensity h2

omit h2 in
theorem hasCompactSupport_greenDensity : HasCompactSupport (QuantumZipper.K3.greenDensity f) :=
  QuantumZipper.K3.hasCompactSupport_greenDensity hc

omit hc in
include hodd in
theorem greenDensity_conj (z : ℂ) :
    QuantumZipper.K3.greenDensity f (conj z) = -QuantumZipper.K3.greenDensity f z := by
  have hodd' : (fun y => f (conj y)) = fun y => -f y := funext hodd
  have h := LocalExt.laplacian_comp_conj h2 z
  rw [hodd', LocalExt.laplacian_neg_apply] at h
  simp only [QuantumZipper.K3.greenDensity]
  rw [← h]
  ring

omit hc in
include hodd in
theorem greenDensity_eq_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    QuantumZipper.K3.greenDensity f z = 0 := by
  have hcz : conj z = z := Complex.conj_eq_iff_im.2 hz
  have h := greenDensity_conj h2 hodd z
  rw [hcz] at h
  linarith

theorem integrable_greenH_mul_greenDensity (w : ℂ) :
    Integrable fun z => greenH w z * QuantumZipper.K3.greenDensity f z := by
  have hΔc := continuous_greenDensity h2
  have hs := hasCompactSupport_greenDensity hc
  have i1 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hs (conj w)
  have i2 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hs w
  refine (i1.sub i2).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply, greenH, QuantumZipper.norm_sub_conj_comm w z, norm_sub_rev w z]
  ring

/-- The whole-plane Green integral: `∫ G_ℍ(w, z) (−(2π)⁻¹ Δ f)(z) dz = f(w) − f(w̄)`. -/
theorem integral_greenH_mul_greenDensity (w : ℂ) :
    ∫ z, greenH w z * QuantumZipper.K3.greenDensity f z = f w - f (conj w) := by
  have hΔc := QuantumZipper.K3.continuous_laplacian_K3 h2
  have hΔs := QuantumZipper.K3.hasCompactSupport_laplacian_K3 hc
  have i1 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hΔs (conj w)
  have i2 := QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hΔc hΔs w
  have e : ∀ z, greenH w z * QuantumZipper.K3.greenDensity f z =
      -(2 * Real.pi)⁻¹ * (Real.log ‖z - conj w‖ * Laplacian.laplacian f z -
        Real.log ‖z - w‖ * Laplacian.laplacian f z) := by
    intro z
    simp only [greenH, QuantumZipper.K3.greenDensity, QuantumZipper.norm_sub_conj_comm w z, norm_sub_rev w z]
    ring
  simp_rw [e]
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [integral_const_mul, integral_sub i1 i2, QuantumZipper.K3.integral_log_norm_sub_mul_laplacian h2 hc,
    QuantumZipper.K3.integral_log_norm_sub_mul_laplacian h2 hc]
  field_simp
  ring

include hodd in
/-- **Green inversion** `G_ℍ(−(2π)⁻¹ Δ f) = f` for an odd (`f(z̄) = −f(z)`) compactly supported `C²` function
`f`: `∫ G_ℍ(w, z) 1_ℍ(z) (−(2π)⁻¹ Δ f)(z) dz = f(w)` (the whole-plane integral is twice the half-plane one, by
reflection; QuantumZipper's logarithmic potential representation `K3`). -/
theorem integral_greenH_mul_indicator_greenDensity (w : ℂ) :
    ∫ z, greenH w z * H.indicator (QuantumZipper.K3.greenDensity f) z = f w := by
  set v := QuantumZipper.K3.greenDensity f with hv
  set vLow : ℂ → ℝ := Set.indicator {z : ℂ | z.im < 0} v with hvLow
  have hHm : MeasurableSet H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hLm : MeasurableSet {z : ℂ | z.im < 0} := (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have hint := integrable_greenH_mul_greenDensity h2 hc w
  have hup : (fun z => greenH w z * H.indicator v z) = Set.indicator H (fun z => greenH w z * v z) := by
    funext z
    rw [Set.indicator_mul_right]
  have hlow : (fun z => greenH w z * vLow z) = Set.indicator {z : ℂ | z.im < 0} (fun z => greenH w z * v z) := by
    funext z
    rw [hvLow, Set.indicator_mul_right]
  have hsplit : (fun z => greenH w z * v z) = fun z => greenH w z * H.indicator v z + greenH w z * vLow z := by
    funext z
    rw [← mul_add]
    congr 1
    rcases lt_trichotomy z.im 0 with h | h | h
    · rw [Set.indicator_of_notMem (show z ∉ H from fun h' => by
        change 0 < z.im at h'; linarith), hvLow, Set.indicator_of_mem (show z ∈ {z : ℂ | z.im < 0} from h),
        zero_add]
    · rw [hv, greenDensity_eq_zero_of_im_eq_zero h2 hodd h, Set.indicator_of_notMem
        (show z ∉ H from fun h' => by change 0 < z.im at h'; linarith), hvLow,
        Set.indicator_of_notMem (show z ∉ {z : ℂ | z.im < 0} from fun h' => by
          change z.im < 0 at h'; linarith), add_zero]
    · rw [Set.indicator_of_mem (show z ∈ H from h), hvLow, Set.indicator_of_notMem
        (show z ∉ {z : ℂ | z.im < 0} from fun h' => by change z.im < 0 at h'; linarith), add_zero]
  have hrefl : ∫ z, greenH w z * vLow z = ∫ z, greenH w z * H.indicator v z := by
    rw [← (Complex.conjLIE.measurePreserving).integral_comp
      Complex.conjLIE.toHomeomorph.measurableEmbedding]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Complex.conjLIE_apply]
    rw [greenH_conj_right]
    by_cases hz : 0 < z.im
    · rw [hvLow, Set.indicator_of_mem (show conj z ∈ {z : ℂ | z.im < 0} by
        change (conj z).im < 0; rw [Complex.conj_im]; linarith), hv, greenDensity_conj h2 hodd,
        Set.indicator_of_mem (show z ∈ H from hz)]
      ring
    · rw [hvLow, Set.indicator_of_notMem (show conj z ∉ {z : ℂ | z.im < 0} by
        change ¬ (conj z).im < 0; rw [Complex.conj_im]; linarith),
        Set.indicator_of_notMem (show z ∉ H from hz)]
      ring
  have htot := integral_greenH_mul_greenDensity h2 hc w
  rw [← hv, hsplit, integral_add (hup ▸ hint.indicator hHm) (hlow ▸ hint.indicator hLm), hrefl,
    hodd] at htot
  linarith

end Inversion

end GB7a

end InteractingSLE
