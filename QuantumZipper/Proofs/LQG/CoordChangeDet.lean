import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.MetricSpace.Thickening
import QuantumZipper.Common.Basic

/-!
# M4-T4, deterministic part: the conformal map near a real interval

Blueprint `M4_BLUEPRINT.md`, node M4-T4. Let `ψ` be holomorphic on an open `U ⊇ [a, b]`, real
and strictly increasing on `[a, b]`, with `ψ' ≠ 0` there. For an inner interval
`[a', b'] ⊂ (a, b)` we extract uniform local data (`CoordChange.Data`):

* on each disc `B(t, 2δ)`, `t ∈ [a', b']`: `ψ` is holomorphic, satisfies the Schwarz reflection
  `ψ(z̄) = conj ψ(z)`, and `|ψ''| ≤ C`;
* `ψ'(t)` is real with `ψ'(t) ≥ m > 0`.

The difference quotient `dq ψ u v = ∫₀¹ ψ'(v + τ(u−v)) dτ` satisfies `ψ u − ψ v = (u−v) dq ψ u v`
and is `C`-Lipschitz in each variable. At scales `r ≤ r₀` it stays within `m/2` of `ψ'(t)`, which
gives the logarithmic distortion bound `|log|dq| − log ψ'(t)| ≤ (4C/m) r` used by the energy
lemma (M4-T4 step 2).
-/

noncomputable section

open Set Metric Filter Topology ComplexConjugate

namespace QuantumZipper
namespace CoordChange

/-! ### The difference quotient -/

/-- Difference quotient of `ψ` along the segment from `v` to `u`. -/
def dq (ψ : ℂ → ℂ) (u v : ℂ) : ℂ := ∫ τ in (0 : ℝ)..1, deriv ψ (v + (τ : ℂ) * (u - v))

theorem segment_mem {S : Set ℂ} (hS : Convex ℝ S) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : v + (τ : ℂ) * (u - v) ∈ S := by
  have h := hS hv hu (sub_nonneg.2 hτ.2) hτ.1 (by ring)
  have e : (1 - τ) • v + τ • u = v + (τ : ℂ) * (u - v) := by
    simp only [Complex.real_smul]; push_cast; ring
  rwa [e] at h

theorem continuous_segment (u v : ℂ) : Continuous fun τ : ℝ => v + (τ : ℂ) * (u - v) := by
  fun_prop

theorem intervalIntegrable_deriv_segment {S : Set ℂ} (hSo : IsOpen S) (hS : Convex ℝ S)
    {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ S) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) :
    IntervalIntegrable (fun τ : ℝ => deriv ψ (v + (τ : ℂ) * (u - v))) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  exact (hψ.deriv hSo).continuousOn.comp (continuous_segment u v).continuousOn
    (fun τ hτ => segment_mem hS hu hv hτ)

theorem sub_eq_mul_dq {S : Set ℂ} (hSo : IsOpen S) (hS : Convex ℝ S) {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ S) {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) :
    ψ u - ψ v = (u - v) * dq ψ u v := by
  have hpath : ∀ τ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun τ : ℝ => ψ (v + (τ : ℂ) * (u - v)))
      (deriv ψ (v + (τ : ℂ) * (u - v)) * (u - v)) τ := by
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have h1 : HasDerivAt (fun τ : ℝ => v + (τ : ℂ) * (u - v)) (u - v) τ := by
      have := (((hasDerivAt_id τ).ofReal_comp).mul_const (u - v)).const_add v
      simpa using this
    have hm := segment_mem hS hu hv hτ
    have h2 : HasDerivAt ψ (deriv ψ (v + (τ : ℂ) * (u - v))) (v + (τ : ℂ) * (u - v)) :=
      ((hψ _ hm).differentiableAt (hSo.mem_nhds hm)).hasDerivAt
    exact h2.comp τ h1
  have hint : IntervalIntegrable (fun τ : ℝ => deriv ψ (v + (τ : ℂ) * (u - v)) * (u - v))
      MeasureTheory.volume 0 1 :=
    (intervalIntegrable_deriv_segment hSo hS hψ hu hv).mul_const _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hpath hint
  rw [intervalIntegral.integral_mul_const] at h
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, add_zero] at h
  rw [show v + (u - v) = u by ring] at h
  rw [dq, ← h, mul_comm]

theorem dq_self (ψ : ℂ → ℂ) (u : ℂ) : dq ψ u u = deriv ψ u := by
  simp [dq]

theorem norm_dq_sub_le {S : Set ℂ} (hSo : IsOpen S) (hS : Convex ℝ S) {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ S) {C : ℝ} (hC : ∀ z ∈ S, ‖deriv (deriv ψ) z‖ ≤ C)
    {u v u' v' : ℂ} (hu : u ∈ S) (hv : v ∈ S) (hu' : u' ∈ S) (hv' : v' ∈ S) :
    ‖dq ψ u v - dq ψ u' v'‖ ≤ C * (‖u - u'‖ + ‖v - v'‖) := by
  have hd : DifferentiableOn ℂ (deriv ψ) S := hψ.deriv hSo
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC u hu)
  unfold dq
  rw [← intervalIntegral.integral_sub (intervalIntegrable_deriv_segment hSo hS hψ hu hv)
    (intervalIntegrable_deriv_segment hSo hS hψ hu' hv')]
  have key := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (C := C * (‖u - u'‖ + ‖v - v'‖))
    (f := fun τ : ℝ => deriv ψ (v + (τ : ℂ) * (u - v)) - deriv ψ (v' + (τ : ℂ) * (u' - v')))
    (fun τ hτ => by
      rw [uIoc_of_le zero_le_one] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hτ
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hd z hz).differentiableAt (hSo.mem_nhds hz)) hC hS
        (segment_mem hS hu' hv' hτ') (segment_mem hS hu hv hτ')
      refine hmv.trans (mul_le_mul_of_nonneg_left ?_ hC0)
      calc ‖v + (τ : ℂ) * (u - v) - (v' + (τ : ℂ) * (u' - v'))‖
          = ‖((1 - τ : ℝ) : ℂ) * (v - v') + (τ : ℂ) * (u - u')‖ := by congr 1; push_cast; ring
        _ ≤ ‖((1 - τ : ℝ) : ℂ) * (v - v')‖ + ‖(τ : ℂ) * (u - u')‖ := norm_add_le _ _
        _ = (1 - τ) * ‖v - v'‖ + τ * ‖u - u'‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
              Real.norm_of_nonneg (by linarith [hτ'.2]), Real.norm_of_nonneg hτ'.1]
        _ ≤ ‖u - u'‖ + ‖v - v'‖ := by
            nlinarith [norm_nonneg (u - u'), norm_nonneg (v - v'), hτ'.1, hτ'.2])
  simpa using key

/-! ### Logarithms -/

theorem abs_log_sub_log_le {x y c : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hx0 : 0 < x := hc.trans_le hx
  have hy0 : 0 < y := hc.trans_le hy
  have h1 : Real.log x - Real.log y ≤ (x - y) / y := by
    rw [← Real.log_div hx0.ne' hy0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [sub_div, div_self hy0.ne']; exact this
  have h2 : Real.log y - Real.log x ≤ (y - x) / x := by
    rw [← Real.log_div hy0.ne' hx0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [sub_div, div_self hx0.ne']; exact this
  rw [abs_le]
  constructor
  · have : (y - x) / x ≤ |x - y| / c := by
      rw [abs_sub_comm]
      calc (y - x) / x ≤ |y - x| / x := div_le_div_of_nonneg_right (le_abs_self _) hx0.le
        _ ≤ |y - x| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hx
    linarith
  · calc Real.log x - Real.log y ≤ (x - y) / y := h1
      _ ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
      _ ≤ |x - y| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hy

/-! ### Uniform local data -/

/-- Uniform local data of `ψ` on the inner interval `[a, b]` (M4-T4). -/
structure Data (ψ : ℂ → ℂ) (a b δ m C : ℝ) : Prop where
  δpos : 0 < δ
  mpos : 0 < m
  diff : ∀ t ∈ Icc a b, DifferentiableOn ℂ ψ (ball (t : ℂ) (2 * δ))
  refl : ∀ t ∈ Icc a b, ∀ z ∈ ball (t : ℂ) (2 * δ), ψ (conj z) = conj (ψ z)
  d2 : ∀ t ∈ Icc a b, ∀ z ∈ ball (t : ℂ) (2 * δ), ‖deriv (deriv ψ) z‖ ≤ C
  dre : ∀ t ∈ Icc a b, m ≤ (deriv ψ t).re
  dim : ∀ t ∈ Icc a b, (deriv ψ t).im = 0

theorem conj_mem_ball_real {t : ℝ} {ρ : ℝ} {z : ℂ} (hz : z ∈ ball (t : ℂ) ρ) :
    conj z ∈ ball (t : ℂ) ρ := by
  rw [mem_ball] at hz ⊢
  rwa [← Complex.conj_ofReal t, Complex.dist_conj_conj]

/-- Extraction of the uniform local data from the hypotheses of M4-T4. -/
theorem exists_data {ψ : ℂ → ℂ} {a b a' b' : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hJU : ∀ t ∈ Icc a b, (t : ℂ) ∈ U) (hψ : DifferentiableOn ℂ ψ U)
    (hre : ∀ t ∈ Icc a b, (ψ t).im = 0)
    (hmono : StrictMonoOn (fun t : ℝ => (ψ t).re) (Icc a b))
    (hne : ∀ t ∈ Icc a b, deriv ψ t ≠ 0) (ha : a < a') (hb : b' < b) :
    ∃ δ m C, Data ψ a' b' δ m C := by
  set K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc a' b' with hKdef
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    exact hJU t ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  set δ := min (ε / 2) (min ((a' - a) / 4) ((b - b') / 4)) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hδε : 2 * δ ≤ ε := by have := min_le_left (ε / 2) (min ((a' - a) / 4) ((b - b') / 4)); linarith
  have hδa : 2 * δ ≤ (a' - a) / 2 := by
    have := min_le_right (ε / 2) (min ((a' - a) / 4) ((b - b') / 4))
    have := min_le_left ((a' - a) / 4) ((b - b') / 4); linarith
  have hδb : 2 * δ ≤ (b - b') / 2 := by
    have := min_le_right (ε / 2) (min ((a' - a) / 4) ((b - b') / 4))
    have := min_le_right ((a' - a) / 4) ((b - b') / 4); linarith
  have hballU : ∀ t ∈ Icc a' b', ball (t : ℂ) (2 * δ) ⊆ U := fun t ht =>
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hδε)).trans
      ((closedBall_subset_cthickening (mem_image_of_mem _ ht) ε).trans hεU)
  have hballK : ∀ t ∈ Icc a' b', ball (t : ℂ) (2 * δ) ⊆ cthickening ε K := fun t ht =>
    (ball_subset_closedBall.trans (closedBall_subset_closedBall hδε)).trans
      (closedBall_subset_cthickening (mem_image_of_mem _ ht) ε)
  -- real points of the balls lie in `[a, b]`
  have hreal : ∀ t ∈ Icc a' b', ∀ x : ℝ, (x : ℂ) ∈ ball (t : ℂ) (2 * δ) → x ∈ Icc a b := by
    intro t ht x hx
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hx
    have := abs_lt.1 hx
    constructor <;> linarith [ht.1, ht.2]
  -- second derivative bound
  have hL : IsCompact (cthickening ε K) := hK.cthickening
  have hd2 : ContinuousOn (deriv (deriv ψ)) U := ((hψ.deriv hU).deriv hU).continuousOn
  obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn (hd2.mono hεU)
  -- derivative on the real line
  have hderiv : ∀ t ∈ Icc a' b', (deriv ψ t).im = 0 ∧ 0 < (deriv ψ t).re := by
    intro t ht
    have htab : t ∈ Icc a b := ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
    have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
    have hd : HasDerivAt ψ (deriv ψ t) t :=
      ((hψ _ (hJU t htab)).differentiableAt (hU.mem_nhds (hJU t htab))).hasDerivAt
    have hdr : HasDerivAt (fun x : ℝ => ψ x) (deriv ψ t) t := hd.comp_ofReal
    have him : HasDerivAt (fun x : ℝ => (ψ x).im) (deriv ψ t).im t := by
      exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hdr
    have hzero : (deriv ψ t).im = 0 := by
      have h0 : HasDerivAt (fun x : ℝ => (ψ x).im) 0 t :=
        (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
          (Filter.mem_of_superset hnhds fun x hx => hre x hx)
      exact him.unique h0
    have hreD : HasDerivAt (fun x : ℝ => (ψ x).re) (deriv ψ t).re t := hd.real_of_complex
    have hacc : AccPt t (𝓟 (Icc a b)) := by
      have h1 : AccPt t (𝓟 (univ : Set ℝ)) := by
        rw [accPt_principal_iff_nhdsWithin, ← compl_eq_univ_sdiff]; infer_instance
      have := h1.nhds_inter hnhds
      rwa [inter_univ] at this
    have hnn := hreD.hasDerivWithinAt.nonneg_of_monotoneOn hacc hmono.monotoneOn
    refine ⟨hzero, lt_of_le_of_ne hnn fun h => hne t htab ?_⟩
    exact Complex.ext (by simpa using h.symm) (by simpa using hzero)
  -- the lower bound `m`
  obtain ⟨m, hm0, hm⟩ : ∃ m, 0 < m ∧ ∀ t ∈ Icc a' b', m ≤ (deriv ψ t).re := by
    by_cases hne' : (Icc a' b').Nonempty
    · have hcont : ContinuousOn (fun t : ℝ => (deriv ψ t).re) (Icc a' b') :=
        Complex.continuous_re.comp_continuousOn
          ((hψ.deriv hU).continuousOn.comp Complex.continuous_ofReal.continuousOn
            (fun t ht => hKU (mem_image_of_mem _ ht)))
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont
      exact ⟨(deriv ψ t₀).re, (hderiv t₀ ht₀).2, fun t ht => hmin ht⟩
    · exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne'⟩
  refine ⟨δ, m, C, hδ, hm0, fun t ht => hψ.mono (hballU t ht), ?_,
    fun t ht z hz => hC z (hballK t ht hz), hm, fun t ht => (hderiv t ht).1⟩
  -- Schwarz reflection by the identity theorem
  intro t ht z hz
  set B := ball (t : ℂ) (2 * δ)
  have hBo : IsOpen B := isOpen_ball
  have hψB : DifferentiableOn ℂ ψ B := hψ.mono (hballU t ht)
  have hg : DifferentiableOn ℂ (fun w => conj (ψ (conj w))) B := by
    intro w hw
    have hw' : conj w ∈ B := conj_mem_ball_real hw
    have h1 : DifferentiableAt ℂ ψ (conj w) := (hψB _ hw').differentiableAt (hBo.mem_nhds hw')
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (t : ℂ), ψ w = conj (ψ (conj w)) := by
    have hT : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] t) (𝓝[≠] (t : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds) ?_
      exact eventually_nhdsWithin_of_forall fun x hx => by
        simpa using hx
    refine hT.frequently (Eventually.frequently ?_)
    have hB : ∀ᶠ x : ℝ in 𝓝[≠] t, (x : ℂ) ∈ B :=
      (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds).eventually
        (hBo.mem_nhds (mem_ball_self (by linarith)))
    filter_upwards [hB] with x hx
    have hxr := hre x (hreal t ht x hx)
    rw [Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.2 hxr).symm
  have heq := (hψB.analyticOnNhd hBo).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hBo) (convex_ball _ _).isPreconnected
    (mem_ball_self (by linarith)) hfreq
  have := heq (conj_mem_ball_real hz)
  simp only [Complex.conj_conj] at this
  exact this

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem C_nonneg (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) : 0 ≤ C :=
  (norm_nonneg _).trans (h.d2 t ht t (mem_ball_self (by linarith [h.δpos])))

theorem closedBall_sub (h : Data ψ a b δ m C) (t : ℝ) {r : ℝ} (hr : r ≤ δ) :
    closedBall (t : ℂ) r ⊆ ball (t : ℂ) (2 * δ) :=
  closedBall_subset_ball (by linarith [h.δpos])

theorem sub_eq (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {u v : ℂ}
    (hu : u ∈ ball (t : ℂ) (2 * δ)) (hv : v ∈ ball (t : ℂ) (2 * δ)) :
    ψ u - ψ v = (u - v) * dq ψ u v :=
  sub_eq_mul_dq isOpen_ball (convex_ball _ _) (h.diff t ht) hu hv

theorem dq_lip (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {u v u' v' : ℂ}
    (hu : u ∈ ball (t : ℂ) (2 * δ)) (hv : v ∈ ball (t : ℂ) (2 * δ))
    (hu' : u' ∈ ball (t : ℂ) (2 * δ)) (hv' : v' ∈ ball (t : ℂ) (2 * δ)) :
    ‖dq ψ u v - dq ψ u' v'‖ ≤ C * (‖u - u'‖ + ‖v - v'‖) :=
  norm_dq_sub_le isOpen_ball (convex_ball _ _) (h.diff t ht) (h.d2 t ht) hu hv hu' hv'

/-- `ψ` is real on the real points of the discs. -/
theorem im_eq_zero (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ}
    (hx : (x : ℂ) ∈ ball (t : ℂ) (2 * δ)) : (ψ x).im = 0 := by
  have := h.refl t ht x hx
  rw [Complex.conj_ofReal] at this
  exact Complex.conj_eq_iff_im.1 this.symm

/-- `ψ'(t)` as a complex number is its (positive) real part. -/
theorem deriv_eq_re (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) :
    deriv ψ t = ((deriv ψ t).re : ℂ) :=
  Complex.ext (by simp) (by simp [h.dim t ht])

theorem deriv_re_pos (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) :
    0 < (deriv ψ t).re :=
  h.mpos.trans_le (h.dre t ht)

theorem norm_deriv (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖deriv ψ t‖ = (deriv ψ t).re := by
  rw [h.deriv_eq_re ht, Complex.norm_real, Real.norm_of_nonneg (h.deriv_re_pos ht).le]
  simp

/-- The admissible scale `r₀`. -/
def r0 (δ m C : ℝ) : ℝ := min δ (m / (4 * (C + 1)))

theorem r0_pos (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) : 0 < r0 δ m C := by
  have := h.C_nonneg ht
  exact lt_min h.δpos (div_pos h.mpos (by positivity))

theorem r0_le_δ : r0 δ m C ≤ δ := min_le_left _ _

theorem two_C_r_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (_hr0 : 0 ≤ r)
    (hr : r ≤ r0 δ m C) : 2 * C * r ≤ m / 2 := by
  have hC := h.C_nonneg ht
  have h1 : r ≤ m / (4 * (C + 1)) := hr.trans (min_le_right _ _)
  have h2 : 2 * C * r ≤ 2 * C * (m / (4 * (C + 1))) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 * C * (m / (4 * (C + 1))) ≤ m / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [h.mpos]
  linarith

/-- Near `t`, the difference quotient is close to `ψ'(t)`. -/
theorem norm_dq_sub_deriv_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : r ≤ δ) {u v : ℂ} (hu : u ∈ closedBall (t : ℂ) r) (hv : v ∈ closedBall (t : ℂ) r) :
    ‖dq ψ u v - deriv ψ t‖ ≤ 2 * C * r := by
  have ht' : (t : ℂ) ∈ ball (t : ℂ) (2 * δ) := mem_ball_self (by linarith [h.δpos])
  have := h.dq_lip ht (h.closedBall_sub t hr hu) (h.closedBall_sub t hr hv) ht' ht'
  rw [dq_self] at this
  have hu' : ‖u - t‖ ≤ r := by rw [← dist_eq_norm]; exact hu
  have hv' : ‖v - t‖ ≤ r := by rw [← dist_eq_norm]; exact hv
  have hC := h.C_nonneg ht
  calc _ ≤ C * (‖u - t‖ + ‖v - t‖) := this
    _ ≤ C * (r + r) := mul_le_mul_of_nonneg_left (add_le_add hu' hv') hC
    _ = 2 * C * r := by ring

theorem norm_dq_ge (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ r0 δ m C) {u v : ℂ} (hu : u ∈ closedBall (t : ℂ) r)
    (hv : v ∈ closedBall (t : ℂ) r) : m / 2 ≤ ‖dq ψ u v‖ := by
  have h1 := h.norm_dq_sub_deriv_le ht (hr.trans r0_le_δ) hu hv
  have h2 := h.two_C_r_le ht hr0 hr
  have h3 : ‖deriv ψ t‖ - ‖dq ψ u v‖ ≤ ‖dq ψ u v - deriv ψ t‖ := by
    have := norm_sub_norm_le (deriv ψ t) (dq ψ u v)
    rwa [norm_sub_rev] at this
  rw [h.norm_deriv ht] at h3
  linarith [h.dre t ht]

theorem re_dq_ge (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ r0 δ m C) {u v : ℂ} (hu : u ∈ closedBall (t : ℂ) r)
    (hv : v ∈ closedBall (t : ℂ) r) : m / 2 ≤ (dq ψ u v).re := by
  have h1 := h.norm_dq_sub_deriv_le ht (hr.trans r0_le_δ) hu hv
  have h2 := h.two_C_r_le ht hr0 hr
  have h3 : |(dq ψ u v - deriv ψ t).re| ≤ ‖dq ψ u v - deriv ψ t‖ := Complex.abs_re_le_norm _
  rw [Complex.sub_re] at h3
  have := (abs_le.1 h3).1
  linarith [h.dre t ht]

/-- The logarithmic distortion bound. -/
theorem abs_log_norm_dq_sub_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ r0 δ m C) {u v : ℂ} (hu : u ∈ closedBall (t : ℂ) r)
    (hv : v ∈ closedBall (t : ℂ) r) :
    |Real.log ‖dq ψ u v‖ - Real.log (deriv ψ t).re| ≤ 4 * C / m * r := by
  have hm2 : 0 < m / 2 := by linarith [h.mpos]
  have h1 := abs_log_sub_log_le hm2 (h.norm_dq_ge ht hr0 hr hu hv)
    ((by linarith [h.dre t ht] : m / 2 ≤ (deriv ψ t).re))
  refine h1.trans ?_
  have h2 : |‖dq ψ u v‖ - (deriv ψ t).re| ≤ 2 * C * r := by
    rw [← h.norm_deriv ht]
    exact (abs_norm_sub_norm_le _ _).trans (h.norm_dq_sub_deriv_le ht (hr.trans r0_le_δ) hu hv)
  calc |‖dq ψ u v‖ - (deriv ψ t).re| / (m / 2) ≤ 2 * C * r / (m / 2) :=
        div_le_div_of_nonneg_right h2 hm2.le
    _ = 4 * C / m * r := by field_simp; ring

/-- Lipschitz bound for `log |dq|` at scales `≤ r₀`. -/
theorem abs_log_norm_dq_sub_log_norm_dq_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ r0 δ m C) {u v u' v' : ℂ}
    (hu : u ∈ closedBall (t : ℂ) r) (hv : v ∈ closedBall (t : ℂ) r)
    (hu' : u' ∈ closedBall (t : ℂ) r) (hv' : v' ∈ closedBall (t : ℂ) r) :
    |Real.log ‖dq ψ u v‖ - Real.log ‖dq ψ u' v'‖| ≤ 2 * C / m * (‖u - u'‖ + ‖v - v'‖) := by
  have hm2 : 0 < m / 2 := by linarith [h.mpos]
  have hrδ := hr.trans r0_le_δ
  refine (abs_log_sub_log_le hm2 (h.norm_dq_ge ht hr0 hr hu hv)
    (h.norm_dq_ge ht hr0 hr hu' hv')).trans ?_
  have h2 := (abs_norm_sub_norm_le (dq ψ u v) (dq ψ u' v')).trans
    (h.dq_lip ht (h.closedBall_sub t hrδ hu) (h.closedBall_sub t hrδ hv)
      (h.closedBall_sub t hrδ hu') (h.closedBall_sub t hrδ hv'))
  calc |‖dq ψ u v‖ - ‖dq ψ u' v'‖| / (m / 2) ≤ C * (‖u - u'‖ + ‖v - v'‖) / (m / 2) :=
        div_le_div_of_nonneg_right h2 hm2.le
    _ = 2 * C / m * (‖u - u'‖ + ‖v - v'‖) := by field_simp

/-- `ψ` maps the closed upper half of the small discs into `Hbar`. -/
theorem im_nonneg (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ r0 δ m C) {v : ℂ} (hv : v ∈ closedBall (t : ℂ) r) (him : 0 ≤ v.im) :
    0 ≤ (ψ v).im := by
  have hrδ := hr.trans r0_le_δ
  have hx : ((v.re : ℝ) : ℂ) ∈ closedBall (t : ℂ) r := by
    rw [mem_closedBall, Complex.dist_eq] at hv ⊢
    refine le_trans ?_ hv
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have := Complex.abs_re_le_norm (v - t)
    simpa using this
  have hsub := h.sub_eq ht (h.closedBall_sub t hrδ hv) (h.closedBall_sub t hrδ hx)
  have hre0 := h.im_eq_zero ht (h.closedBall_sub t hrδ hx)
  have hdiff : v - (v.re : ℂ) = (v.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hkey : (ψ v).im = v.im * (dq ψ v (v.re : ℂ)).re := by
    have := congrArg Complex.im hsub
    rw [Complex.sub_im, hre0, sub_zero, hdiff] at this
    rw [this]; simp
  rw [hkey]
  exact mul_nonneg him ((by linarith [h.mpos] : (0 : ℝ) ≤ m / 2).trans
    (h.re_dq_ge ht hr0 hr hv hx))

end Data

end CoordChange
end QuantumZipper
