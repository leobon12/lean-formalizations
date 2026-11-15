import InteractingSLE.GFF.LocalSets.Basic

/-!
# Smooth truncations and a Caccioppoli estimate near a boundary

Deterministic analysis for Proposition 3.4 (ii) of the specification (`source/spec/p001-048.md`,
`#prop-3.4-proof`, p. 48): a harmonic function `u` on an open set `V` that tends to `0` at the
boundary points of `V` inside an open set `U'`, cut off by `χ ∈ C_c^∞(U')`, has finite Dirichlet
energy and is a limit of test functions on `V` in the Dirichlet norm.

The source tests harmonicity with `ζ²((u − ε)₊ − (−u − ε)₊)`; here the Lipschitz truncation is
replaced by the smooth truncation `Φ_ε(t) = t · s(t²/ε² − 1)` (`s` = `Real.smoothTransition`), which
vanishes for `|t| ≤ ε`, satisfies `0 ≤ Φ_ε' ≤ C`, `Φ_ε(t)² ≤ t² Φ_ε'(t)`, and `Φ_ε(t) → t`,
`Φ_ε'(t) → 1_{t ≠ 0}` as `ε → 0`. Then `gₙ = χ Φ_{εₙ}(u) ∈ C_c^∞(V)`, and:

* `truncCutoff_mem` : `χ Φ_ε(u)` is smooth with compact support in `V`;
* `integral_caccioppoli_le` (Caccioppoli): `∫ χ² Φ_ε'(u) |∇u|² ≤ 4 ∫ u² |∇χ|²`;
* `tendsto_integral_norm_fderiv_truncCutoff` : `∇gₙ` converges in `L²`, so `(gₙ)` is Cauchy for the
  Dirichlet energy, and `gₙ → χ u` pointwise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace InteractingSLE
namespace GFF

/-! ### The smooth truncation `Φ_ε(t) = t · s(t²/ε² − 1)` -/

/-- The smooth step `s = Real.smoothTransition` has a nonnegative derivative, vanishing outside
`[0, 1]`, so `(u + 1) s'(u)` is bounded. -/
lemma exists_deriv_smoothTransition_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ deriv Real.smoothTransition u ∧
      (u + 1) * deriv Real.smoothTransition u ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hc.continuousOn
  have hnn : ∀ u, 0 ≤ deriv Real.smoothTransition u := fun u =>
    Real.smoothTransition.monotone.deriv_nonneg
  have hout : ∀ u, u ∉ Icc (0 : ℝ) 1 → deriv Real.smoothTransition u = 0 := by
    intro u hu
    rcases not_and_or.1 hu with h | h
    · push Not at h
      have : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [gt_mem_nhds h] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      rw [this.deriv_eq, deriv_const]
    · push Not at h
      have : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 1 := by
        filter_upwards [lt_mem_nhds h] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [this.deriv_eq, deriv_const]
  refine ⟨2 * |C|, by positivity, fun u => ⟨hnn u, ?_⟩⟩
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · have h1 := hC u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn u)] at h1
    have h2 : u + 1 ≤ 2 := by linarith [hu.2]
    have h3 : 0 ≤ u + 1 := by linarith [hu.1]
    calc (u + 1) * deriv Real.smoothTransition u ≤ 2 * deriv Real.smoothTransition u :=
          mul_le_mul_of_nonneg_right h2 (hnn u)
      _ ≤ 2 * |C| := by linarith [le_abs_self C]
  · rw [hout u hu, mul_zero]
    positivity

/-- The smooth truncation `Φ_ε(t) = t · s(t²/ε² − 1)`. -/
def truncFun (ε t : ℝ) : ℝ := t * Real.smoothTransition (t ^ 2 / ε ^ 2 - 1)

/-- Its derivative `Φ_ε'(t) = s(u) + 2 (u + 1) s'(u)`, `u = t²/ε² − 1`. -/
def truncDeriv (ε t : ℝ) : ℝ :=
  Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) +
    2 * (t ^ 2 / ε ^ 2) * deriv Real.smoothTransition (t ^ 2 / ε ^ 2 - 1)

lemma hasDerivAt_truncFun (ε t : ℝ) : HasDerivAt (truncFun ε) (truncDeriv ε t) t := by
  have hs : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (t ^ 2 / ε ^ 2 - 1))
      (t ^ 2 / ε ^ 2 - 1) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero _ |>.hasDerivAt
  have hu : HasDerivAt (fun t : ℝ => t ^ 2 / ε ^ 2 - 1) (2 * t / ε ^ 2) t := by
    have := ((hasDerivAt_pow 2 t).div_const (ε ^ 2)).sub_const 1
    simpa using this
  have := (hasDerivAt_id t).mul (hs.comp t hu)
  have h2 : truncDeriv ε t = 1 * Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) +
      t * (deriv Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) * (2 * t / ε ^ 2)) := by
    unfold truncDeriv
    ring
  rw [h2]
  exact this

lemma contDiff_truncFun (ε : ℝ) {n : ℕ∞} : ContDiff ℝ n (truncFun ε) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.pow 2).div_const _ |>.sub contDiff_const))

lemma truncFun_eq_zero {ε t : ℝ} (h : t ^ 2 ≤ ε ^ 2) : truncFun ε t = 0 := by
  rw [truncFun, Real.smoothTransition.zero_of_nonpos, mul_zero]
  rcases eq_or_ne ε 0 with rfl | hε
  · simp
  · rw [sub_nonpos, div_le_one (by positivity)]
    exact h

lemma truncFun_zero (ε : ℝ) : truncFun ε 0 = 0 := by simp [truncFun]

lemma truncDeriv_zero (ε : ℝ) : truncDeriv ε 0 = 0 := by
  have h : deriv Real.smoothTransition (-1) = 0 := by
    have : Real.smoothTransition =ᶠ[𝓝 (-1 : ℝ)] fun _ => 0 := by
      filter_upwards [gt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [this.deriv_eq, deriv_const]
  simp [truncDeriv, h, Real.smoothTransition.zero_of_nonpos]

lemma abs_truncFun_le (ε t : ℝ) : |truncFun ε t| ≤ |t| := by
  rw [truncFun, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.smoothTransition.le_one _)

lemma truncDeriv_nonneg (ε t : ℝ) : 0 ≤ truncDeriv ε t := by
  have := (Real.smoothTransition.monotone.deriv_nonneg (x := t ^ 2 / ε ^ 2 - 1))
  unfold truncDeriv
  have : 0 ≤ t ^ 2 / ε ^ 2 := by positivity
  have := Real.smoothTransition.nonneg (t ^ 2 / ε ^ 2 - 1)
  positivity

lemma smoothTransition_le_truncDeriv (ε t : ℝ) :
    Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) ≤ truncDeriv ε t := by
  have := (Real.smoothTransition.monotone.deriv_nonneg (x := t ^ 2 / ε ^ 2 - 1))
  have : 0 ≤ t ^ 2 / ε ^ 2 := by positivity
  unfold truncDeriv
  nlinarith

lemma truncDeriv_le {C : ℝ} (hC : ∀ u : ℝ, (u + 1) * deriv Real.smoothTransition u ≤ C)
    (ε t : ℝ) : truncDeriv ε t ≤ 1 + 2 * C := by
  have h := hC (t ^ 2 / ε ^ 2 - 1)
  rw [sub_add_cancel] at h
  unfold truncDeriv
  linarith [Real.smoothTransition.le_one (t ^ 2 / ε ^ 2 - 1)]

lemma truncFun_sq_le (ε t : ℝ) : truncFun ε t ^ 2 ≤ t ^ 2 * truncDeriv ε t := by
  have h1 := Real.smoothTransition.nonneg (t ^ 2 / ε ^ 2 - 1)
  have h2 := Real.smoothTransition.le_one (t ^ 2 / ε ^ 2 - 1)
  have h3 := smoothTransition_le_truncDeriv ε t
  rw [truncFun, mul_pow]
  have : Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) ^ 2 ≤
      Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) :=
    by nlinarith
  exact mul_le_mul_of_nonneg_left (this.trans h3) (sq_nonneg t)

/-- For `t ≠ 0` and small `ε > 0`: `Φ_ε(t) = t` and `Φ_ε'(t) = 1`. -/
lemma truncFun_eventually {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), truncFun ε t = t ∧ truncDeriv ε t = 1 := by
  have ht2 : 0 < t ^ 2 / 2 := by positivity
  have hsq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 < t ^ 2 / 2 := by
    have : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    exact this.eventually (gt_mem_nhds ht2)
  filter_upwards [hsq, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : (0 : ℝ) < ε ^ 2 := by have : (0 : ℝ) < ε := hε0; positivity
  have hu : 1 < t ^ 2 / ε ^ 2 - 1 := by
    rw [lt_sub_iff_add_lt, one_add_one_eq_two, lt_div_iff₀ hε0']
    linarith
  have hd : deriv Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) = 0 := by
    have : Real.smoothTransition =ᶠ[𝓝 (t ^ 2 / ε ^ 2 - 1)] fun _ => 1 := by
      filter_upwards [lt_mem_nhds hu] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [this.deriv_eq, deriv_const]
  have h1 : Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) = 1 :=
    Real.smoothTransition.one_of_one_le hu.le
  exact ⟨by rw [truncFun, h1, mul_one], by rw [truncDeriv, h1, hd, mul_zero, add_zero]⟩

lemma truncDeriv_eq_zero {ε t : ℝ} (h : t ^ 2 < ε ^ 2) : truncDeriv ε t = 0 := by
  have hε : 0 < ε ^ 2 := lt_of_le_of_lt (sq_nonneg t) h
  have hneg : t ^ 2 / ε ^ 2 - 1 < 0 := by
    rw [sub_neg, div_lt_one hε]
    exact h
  have hd : deriv Real.smoothTransition (t ^ 2 / ε ^ 2 - 1) = 0 := by
    have : Real.smoothTransition =ᶠ[𝓝 (t ^ 2 / ε ^ 2 - 1)] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hneg] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [this.deriv_eq, deriv_const]
  rw [truncDeriv, Real.smoothTransition.zero_of_nonpos hneg.le, hd]
  ring

/-! ### Harmonic functions vanishing at part of the boundary -/

section Boundary

variable {V U' : Set ℂ} {u : ℂ → ℝ}

/-- If `u` is continuous on the open set `V` and tends to `0` at the boundary points of `V` in
`U'`, then `1_V u` is continuous at every point of `U'` and of `V`. -/
lemma continuousAt_indicator_of_tendsto_frontier (hV : IsOpen V) (hu : ContinuousOn u V)
    (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) {x : ℂ} (hx : x ∈ U' ∪ V) :
    ContinuousAt (V.indicator u) x := by
  by_cases hxV : x ∈ V
  · have he : V.indicator u =ᶠ[𝓝 x] u := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      exact indicator_of_mem hy u
    exact (hu.continuousAt (hV.mem_nhds hxV)).congr he.symm
  have hxU : x ∈ U' := hx.resolve_right hxV
  rw [ContinuousAt, indicator_of_notMem hxV]
  by_cases hxc : x ∈ closure V
  · have hxf : x ∈ frontier V ∩ U' := by
      rw [frontier, hV.interior_eq]
      exact ⟨⟨hxc, hxV⟩, hxU⟩
    rw [Metric.tendsto_nhds]
    intro ε hε
    have h := (Metric.tendsto_nhds.1 (hbd x hxf)) ε hε
    rw [eventually_nhdsWithin_iff] at h
    filter_upwards [h] with y hy
    by_cases hyV : y ∈ V
    · rw [indicator_of_mem hyV]
      exact hy hyV
    · rw [indicator_of_notMem hyV, dist_self]
      exact hε
  · have he : V.indicator u =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
      exact indicator_of_notMem (fun h => hy (subset_closure h)) u
    exact tendsto_const_nhds.congr' he.symm

variable {χ : ℂ → ℝ}

/-- Near a point outside `V`, either `χ = 0` or `|1_V u| < ε` (for `tsupport χ ⊆ U'`). -/
lemma eventually_eq_zero_or_sq_lt (hV : IsOpen V) (hu : ContinuousOn u V)
    (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U') {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : x ∉ V) :
    ∀ᶠ y in 𝓝 x, χ y = 0 ∨ V.indicator u y ^ 2 < ε ^ 2 := by
  by_cases hxs : x ∈ tsupport χ
  · have hc := continuousAt_indicator_of_tendsto_frontier hV hu hbd (Or.inl (hχU hxs))
    rw [ContinuousAt, indicator_of_notMem hx] at hc
    filter_upwards [(Metric.tendsto_nhds.1 hc) ε hε] with y hy
    right
    rw [dist_zero_right, Real.norm_eq_abs] at hy
    exact sq_lt_sq' (by linarith [neg_abs_le (V.indicator u y)]) (lt_of_le_of_lt (le_abs_self _) hy)
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxs] with y hy
    exact Or.inl hy

/-- The cut-off truncation `χ Φ_ε(1_V u)`. -/
def truncCutoff (V : Set ℂ) (u χ : ℂ → ℝ) (ε : ℝ) (x : ℂ) : ℝ :=
  χ x * truncFun ε (V.indicator u x)

lemma truncCutoff_eventuallyEq_zero (hV : IsOpen V) (hu : ContinuousOn u V)
    (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U') {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} (hx : x ∉ V) : truncCutoff V u χ ε =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [eventually_eq_zero_or_sq_lt hV hu hbd hχU hε hx] with y hy
  rcases hy with hy | hy
  · simp [truncCutoff, hy]
  · simp [truncCutoff, truncFun_eq_zero hy.le]

/-- `χ Φ_ε(1_V u)` is smooth for `u` harmonic on `V`. -/
lemma contDiff_truncCutoff (hV : IsOpen V) (hu : InnerProductSpace.HarmonicOnNhd u V)
    (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U')
    {n : ℕ∞} (hχ : ContDiff ℝ n χ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ n (truncCutoff V u χ ε) := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hxV : x ∈ V
  · have he : V.indicator u =ᶠ[𝓝 x] u := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      exact indicator_of_mem hy u
    have hux : ContDiffAt ℝ n u x :=
      (contDiffOn_of_harmonicOnNhd hu).contDiffAt (hV.mem_nhds hxV)
    have : ContDiffAt ℝ n (fun y => χ y * truncFun ε (u y)) x :=
      hχ.contDiffAt.mul ((contDiff_truncFun ε (n := n)).contDiffAt.comp x hux)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [he] with y hy
    simp only [truncCutoff, hy]
  · exact contDiffAt_const.congr_of_eventuallyEq
      (truncCutoff_eventuallyEq_zero hV hcu hbd hχU hε hxV)

lemma tsupport_truncCutoff_subset (hV : IsOpen V) (hu : ContinuousOn u V)
    (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U') {ε : ℝ}
    (hε : 0 < ε) : tsupport (truncCutoff V u χ ε) ⊆ V := fun x hx => by
  by_contra hxV
  exact (notMem_tsupport_iff_eventuallyEq.2
    (truncCutoff_eventuallyEq_zero hV hu hbd hχU hε hxV)) hx

lemma hasCompactSupport_truncCutoff (hχ : HasCompactSupport χ) (ε : ℝ) :
    HasCompactSupport (truncCutoff V u χ ε) :=
  hχ.mul_right

/-- The derivative of `χ Φ_ε(1_V u)`, valid at every point. -/
lemma fderiv_truncCutoff (hV : IsOpen V) (hu : InnerProductSpace.HarmonicOnNhd u V)
    (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U')
    (hχ : ContDiff ℝ 1 χ) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    fderiv ℝ (truncCutoff V u χ ε) x =
      truncFun ε (V.indicator u x) • fderiv ℝ χ x +
        (χ x * truncDeriv ε (V.indicator u x)) • fderiv ℝ (V.indicator u) x := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  by_cases hxV : x ∈ V
  · have he : V.indicator u =ᶠ[𝓝 x] u := by
      filter_upwards [hV.mem_nhds hxV] with y hy
      exact indicator_of_mem hy u
    have hdu : DifferentiableAt ℝ (V.indicator u) x :=
      (((contDiffOn_of_harmonicOnNhd (n := 1) hu).contDiffAt
        (hV.mem_nhds hxV)).differentiableAt one_ne_zero).congr_of_eventuallyEq he
    have h1 : HasFDerivAt (fun y => truncFun ε (V.indicator u y))
        (truncDeriv ε (V.indicator u x) • fderiv ℝ (V.indicator u) x) x :=
      (hasDerivAt_truncFun ε _).comp_hasFDerivAt x hdu.hasFDerivAt
    have h2 : HasFDerivAt (truncCutoff V u χ ε)
        (χ x • truncDeriv ε (V.indicator u x) • fderiv ℝ (V.indicator u) x +
          truncFun ε (V.indicator u x) • fderiv ℝ χ x) x :=
      (hχ.differentiable one_ne_zero x).hasFDerivAt.mul h1
    rw [h2.fderiv, smul_smul, add_comm]
  · rw [(truncCutoff_eventuallyEq_zero hV hcu hbd hχU hε hxV).fderiv_eq,
      indicator_of_notMem hxV, truncFun_zero, truncDeriv_zero]
    simp

end Boundary

/-! ### The Caccioppoli estimate -/

section Caccioppoli

open QuantumZipper.K3 (gradInner norm_fderiv_sq_eq_gradInner)

variable {V U' : Set ℂ} {u χ : ℂ → ℝ}

lemma continuous_truncDeriv (ε : ℝ) : Continuous (truncDeriv ε) := by
  have hs := Real.smoothTransition.continuous
  have hd := (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hq : Continuous fun t : ℝ => t ^ 2 / ε ^ 2 - 1 := by fun_prop
  exact (hs.comp hq).add ((continuous_const.mul ((continuous_pow 2).div_const _)).mul (hd.comp hq))

lemma indicator_eventuallyEq (hV : IsOpen V) {x : ℂ} (hx : x ∈ V) :
    V.indicator u =ᶠ[𝓝 x] u := by
  filter_upwards [hV.mem_nhds hx] with y hy
  exact indicator_of_mem hy u

lemma continuousAt_fderiv_indicator (hV : IsOpen V) (hu : InnerProductSpace.HarmonicOnNhd u V)
    {x : ℂ} (hx : x ∈ V) : ContinuousAt (fderiv ℝ (V.indicator u)) x := by
  have he : fderiv ℝ (V.indicator u) =ᶠ[𝓝 x] fderiv ℝ u := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (indicator_eventuallyEq hV hy).fderiv_eq
  exact ((((contDiffOn_of_harmonicOnNhd (n := 1) hu).continuousOn_fderiv_of_isOpen hV
    le_rfl).continuousAt (hV.mem_nhds hx))).congr he.symm

/-- `|⟨∇f, ∇g⟩| ≤ |∇f| |∇g|`, squared. -/
lemma gradInner_sq_le (f g : ℂ → ℝ) (x : ℂ) :
    gradInner f g x ^ 2 ≤ ‖fderiv ℝ f x‖ ^ 2 * ‖fderiv ℝ g x‖ ^ 2 := by
  rw [norm_fderiv_sq_eq_gradInner, norm_fderiv_sq_eq_gradInner]
  simp only [gradInner]
  nlinarith [sq_nonneg (fderiv ℝ f x 1 * fderiv ℝ g x Complex.I -
    fderiv ℝ f x Complex.I * fderiv ℝ g x 1)]

lemma tsupport_sq_subset (χ : ℂ → ℝ) : tsupport (fun y => χ y ^ 2) ⊆ tsupport χ :=
  closure_mono fun y hy h => hy (by simp [h])

variable (V u χ) in
/-- `A(x) = χ² Φ_ε'(1_V u) |∇(1_V u)|²`. -/
def caccA (ε : ℝ) (x : ℂ) : ℝ :=
  χ x ^ 2 * truncDeriv ε (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖ ^ 2

variable (V u χ) in
/-- `B(x) = (1_V u)² |∇χ|²`. -/
def caccB (x : ℂ) : ℝ := V.indicator u x ^ 2 * ‖fderiv ℝ χ x‖ ^ 2

variable (V u χ) in
/-- `M(x) = χ Φ_ε(1_V u) ⟨∇(1_V u), ∇χ⟩`. -/
def caccM (ε : ℝ) (x : ℂ) : ℝ :=
  χ x * truncFun ε (V.indicator u x) * gradInner (V.indicator u) χ x

lemma caccA_nonneg (ε : ℝ) (x : ℂ) : 0 ≤ caccA V u χ ε x := by
  have := truncDeriv_nonneg ε (V.indicator u x)
  unfold caccA
  positivity

lemma caccB_nonneg (x : ℂ) : 0 ≤ caccB V u χ x := by
  unfold caccB
  positivity

lemma sq_caccM_le (ε : ℝ) (x : ℂ) : caccM V u χ ε x ^ 2 ≤ caccA V u χ ε x * caccB V u χ x := by
  have h1 := truncFun_sq_le ε (V.indicator u x)
  have h2 := gradInner_sq_le (V.indicator u) χ x
  have h3 := truncDeriv_nonneg ε (V.indicator u x)
  unfold caccM caccA caccB
  rw [mul_pow, mul_pow]
  calc χ x ^ 2 * truncFun ε (V.indicator u x) ^ 2 * gradInner (V.indicator u) χ x ^ 2
      ≤ χ x ^ 2 * (V.indicator u x ^ 2 * truncDeriv ε (V.indicator u x)) *
          (‖fderiv ℝ (V.indicator u) x‖ ^ 2 * ‖fderiv ℝ χ x‖ ^ 2) := by gcongr
    _ = _ := by ring

variable (hV : IsOpen V) (hu : InnerProductSpace.HarmonicOnNhd u V)
  (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U')

include hV hu hbd hχU in
lemma continuous_caccA (hχ : ContDiff ℝ 1 χ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (caccA V u χ ε) := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ V
  · exact ((hχ.continuous.continuousAt.pow 2).mul ((continuous_truncDeriv ε).continuousAt.comp
      (continuousAt_indicator_of_tendsto_frontier hV hcu hbd (Or.inr hx)))).mul
      ((continuousAt_fderiv_indicator hV hu hx).norm.pow 2)
  · have hz : caccA V u χ ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_eq_zero_or_sq_lt hV hcu hbd hχU hε hx] with y hy
      rcases hy with hy | hy
      · simp [caccA, hy]
      · simp [caccA, truncDeriv_eq_zero hy]
    exact continuousAt_const.congr hz.symm

include hV hu hbd hχU in
lemma continuous_caccB (hχ : ContDiff ℝ 1 χ) : Continuous (caccB V u χ) := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U' ∪ V
  · exact ((continuousAt_indicator_of_tendsto_frontier hV hcu hbd hx).pow 2).mul
      ((hχ.continuous_fderiv one_ne_zero).continuousAt.norm.pow 2)
  · have hxs : x ∉ tsupport (fderiv ℝ χ) := fun h =>
      hx (Or.inl (hχU (tsupport_fderiv_subset ℝ h)))
    have hz : caccB V u χ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxs] with y hy
      simp [caccB, show fderiv ℝ χ y = 0 from hy]
    exact continuousAt_const.congr hz.symm

include hV hu hbd hχU in
lemma continuous_caccM (hχ : ContDiff ℝ 1 χ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (caccM V u χ ε) := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ V
  · have hfG := continuousAt_fderiv_indicator hV hu hx
    have hfχ := (hχ.continuous_fderiv one_ne_zero).continuousAt (x := x)
    have hg : ContinuousAt (gradInner (V.indicator u) χ) x :=
      ((hfG.clm_apply continuousAt_const).mul (hfχ.clm_apply continuousAt_const)).add
        ((hfG.clm_apply continuousAt_const).mul (hfχ.clm_apply continuousAt_const))
    exact (hχ.continuous.continuousAt.mul
      ((contDiff_truncFun ε (n := 0)).continuous.continuousAt.comp
      (continuousAt_indicator_of_tendsto_frontier hV hcu hbd (Or.inr hx)))).mul hg
  · have hz : caccM V u χ ε =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_eq_zero_or_sq_lt hV hcu hbd hχU hε hx] with y hy
      rcases hy with hy | hy
      · simp [caccM, hy]
      · simp [caccM, truncFun_eq_zero hy.le]
    exact continuousAt_const.congr hz.symm

lemma hasCompactSupport_caccA (hχc : HasCompactSupport χ) (ε : ℝ) :
    HasCompactSupport (caccA V u χ ε) :=
  hχc.mono' fun x hx => subset_tsupport _ fun h => hx (by simp [caccA, h])

lemma hasCompactSupport_caccB (hχc : HasCompactSupport χ) : HasCompactSupport (caccB V u χ) :=
  hχc.mono' fun x hx => tsupport_fderiv_subset ℝ (subset_tsupport _ fun h => hx (by
    simp [caccB, show fderiv ℝ χ x = 0 from h]))

lemma hasCompactSupport_caccM (hχc : HasCompactSupport χ) (ε : ℝ) :
    HasCompactSupport (caccM V u χ ε) :=
  hχc.mono' fun x hx => subset_tsupport _ fun h => hx (by simp [caccM, h])

include hV hu hbd hχU in
/-- **Weak harmonicity**: `∫ ⟨∇(1_V u), ∇ψ⟩ = 0` for `ψ = χ² Φ_ε(1_V u)`. -/
lemma integral_gradInner_truncCutoff_eq_zero (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, gradInner (V.indicator u) (truncCutoff V u (fun y => χ y ^ 2) ε) x = 0 := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  have hχ2U : tsupport (fun y => χ y ^ 2) ⊆ U' :=
    (tsupport_sq_subset χ).trans hχU
  have hχ2c : HasCompactSupport (fun y => χ y ^ 2) :=
    hχc.mono' fun y hy => subset_tsupport _ fun h => hy (by simp [h])
  set ψ := truncCutoff V u (fun y => χ y ^ 2) ε with hψdef
  have hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    contDiff_truncCutoff hV hu hbd hχ2U (hχ.pow 2) hε
  have hψc : HasCompactSupport ψ := hasCompactSupport_truncCutoff hχ2c ε
  have hψV : tsupport ψ ⊆ V := tsupport_truncCutoff_subset hV hcu hbd hχ2U hε
  obtain ⟨δ, hδ, hδV⟩ := hψc.isCompact.exists_cthickening_subset_open hV hψV
  have hcth : Metric.cthickening (δ / 2) (tsupport ψ) ⊆ V :=
    (Metric.cthickening_mono (half_le_self hδ.le) _).trans hδV
  obtain ⟨θ, hθ, -, hθV, hθ1⟩ := exists_cutoff (hψc.isCompact.cthickening (r := δ / 2)) hV hcth
  set w : ℂ → ℝ := fun x => θ x * u x
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w :=
    contDiff_mul_of_tsupport_subset hV hθ hθV (contDiffOn_of_harmonicOnNhd hu)
  set O := Metric.thickening (δ / 2) (tsupport ψ)
  have hO : IsOpen O := Metric.isOpen_thickening
  have hOV : O ⊆ V := (Metric.thickening_subset_cthickening _ _).trans hcth
  have hwu : ∀ y ∈ O, w =ᶠ[𝓝 y] u := fun y hy => by
    filter_upwards [hO.mem_nhds hy] with z hz
    simp [w, hθ1 (Metric.thickening_subset_cthickening _ _ hz)]
  have hwH : InnerProductSpace.HarmonicOnNhd w O := fun y hy =>
    (InnerProductSpace.harmonicAt_congr_nhds (hwu y hy)).2 (hu y (hOV hy))
  have hsub : tsupport ψ ⊆ O := Metric.self_subset_thickening (half_pos hδ) _
  have h1 := QuantumZipper.K3.integral_gradInner_eq_neg_integral_mul_laplacian
    (hw.of_le (by norm_cast))
    (hψ.of_le (by norm_cast)) hψc
  have h2 := LQGMetric.HarmLoc.integral_mul_laplacian_of_harmonic hO hwH
    (hψ.of_le (by norm_cast)) hψc hsub
  rw [h2, neg_zero] at h1
  rw [← h1]
  congr 1
  funext x
  by_cases hx : x ∈ O
  · simp only [gradInner]
    rw [((hwu x hx).trans (indicator_eventuallyEq hV (hOV hx)).symm).fderiv_eq]
  · have hxψ : x ∉ tsupport ψ := fun h => hx (hsub h)
    have h0 : fderiv ℝ ψ x = 0 := by
      rw [(notMem_tsupport_iff_eventuallyEq.1 hxψ).fderiv_eq]
      exact fderiv_const_apply 0
    simp [gradInner, h0]

include hV hu hbd hχU in
/-- **Caccioppoli inequality** (specification p. 48, smooth truncation): for `χ ∈ C_c^∞(U')`,
`∫ χ² Φ_ε'(u) |∇u|² ≤ 4 ∫ u² |∇χ|²` (integrands extended by zero off `V`). -/
theorem integral_caccA_le (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hχc : HasCompactSupport χ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, caccA V u χ ε x ≤ 4 * ∫ x, caccB V u χ x := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_cast)
  have hA := (continuous_caccA hV hu hbd hχU hχ1 hε).integrable_of_hasCompactSupport
    (hasCompactSupport_caccA hχc ε) (μ := volume)
  have hB := (continuous_caccB hV hu hbd hχU hχ1).integrable_of_hasCompactSupport
    (hasCompactSupport_caccB hχc) (μ := volume)
  have hM := (continuous_caccM hV hu hbd hχU hχ1 hε).integrable_of_hasCompactSupport
    (hasCompactSupport_caccM hχc ε) (μ := volume)
  -- expansion of the weak harmonicity identity
  have hexp : ∀ x, gradInner (V.indicator u) (truncCutoff V u (fun y => χ y ^ 2) ε) x =
      2 * caccM V u χ ε x + caccA V u χ ε x := by
    intro x
    have hχ2U : tsupport (fun y => χ y ^ 2) ⊆ U' :=
      (tsupport_sq_subset χ).trans hχU
    have hd := fderiv_truncCutoff hV hu hbd hχ2U (hχ1.pow 2) hε x
    have hsq : fderiv ℝ (fun y => χ y ^ 2) x = (2 * χ x) • fderiv ℝ χ x := by
      have := ((hχ1.differentiable one_ne_zero) x).hasFDerivAt.pow 2
      rw [this.fderiv]
      congr 1
      simp
    simp only [gradInner, hd, hsq, add_apply, smul_apply,
      smul_eq_mul, caccM, caccA, norm_fderiv_sq_eq_gradInner, gradInner]
    ring
  have hweak := integral_gradInner_truncCutoff_eq_zero hV hu hbd hχU hχ hχc hε
  simp only [hexp] at hweak
  rw [integral_add (hM.const_mul 2) hA, integral_const_mul] at hweak
  -- Cauchy–Schwarz
  have hsA2 : MemLp (fun x => Real.sqrt (caccA V u χ ε x)) 2 volume := by
    rw [memLp_two_iff_integrable_sq
      ((continuous_caccA hV hu hbd hχU hχ1 hε).sqrt.aestronglyMeasurable)]
    simpa only [Real.sq_sqrt (caccA_nonneg ε _)] using hA
  have hsB2 : MemLp (fun x => Real.sqrt (caccB V u χ x)) 2 volume := by
    rw [memLp_two_iff_integrable_sq
      ((continuous_caccB hV hu hbd hχU hχ1).sqrt.aestronglyMeasurable)]
    simpa only [Real.sq_sqrt (caccB_nonneg _)] using hB
  have hsA : MemLp (fun x => Real.sqrt (caccA V u χ ε x)) (ENNReal.ofReal 2) volume := by
    rwa [ENNReal.ofReal_ofNat]
  have hsB : MemLp (fun x => Real.sqrt (caccB V u χ x)) (ENNReal.ofReal 2) volume := by
    rwa [ENNReal.ofReal_ofNat]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun x => Real.sqrt_nonneg (caccA V u χ ε x))
    (ae_of_all _ fun x => Real.sqrt_nonneg (caccB V u χ x)) hsA hsB
  simp only [Real.rpow_two, Real.sq_sqrt (caccA_nonneg ε _), Real.sq_sqrt (caccB_nonneg _),
    ← Real.sqrt_eq_rpow] at hH
  have hpt : ∀ x, -caccM V u χ ε x ≤ Real.sqrt (caccA V u χ ε x) * Real.sqrt (caccB V u χ x) := by
    intro x
    rw [← Real.sqrt_mul (caccA_nonneg ε x)]
    exact (neg_le_abs _).trans (Real.abs_le_sqrt (sq_caccM_le ε x))
  have hint : -∫ x, caccM V u χ ε x ≤
      ∫ x, Real.sqrt (caccA V u χ ε x) * Real.sqrt (caccB V u χ x) := by
    rw [← integral_neg]
    refine integral_mono hM.neg ?_ hpt
    exact hsA2.integrable_mul hsB2
  set X := ∫ x, caccA V u χ ε x
  set Y := ∫ x, caccB V u χ x
  have hX : 0 ≤ X := integral_nonneg fun x => caccA_nonneg ε x
  have hY : 0 ≤ Y := integral_nonneg fun x => caccB_nonneg x
  have hXle : X ≤ 2 * (Real.sqrt X * Real.sqrt Y) := by linarith
  nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hY, Real.sqrt_nonneg X, Real.sqrt_nonneg Y,
    sq_nonneg (Real.sqrt X - 2 * Real.sqrt Y)]

end Caccioppoli

/-! ### The limit `ε → 0` -/

section Limit

open QuantumZipper.K3 (gradInner norm_fderiv_sq_eq_gradInner)

variable {V U' : Set ℂ} {u χ : ℂ → ℝ}

/-- `ι(t) = 1_{t ≠ 0}`. -/
def nzInd (t : ℝ) : ℝ := if t = 0 then 0 else 1

lemma nzInd_nonneg (t : ℝ) : 0 ≤ nzInd t := by unfold nzInd; split_ifs <;> norm_num

lemma nzInd_sq (t : ℝ) : nzInd t ^ 2 = nzInd t := by unfold nzInd; split_ifs <;> norm_num

/-- The truncation levels `εₙ = 1/(n + 1)`. -/
def epsSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma epsSeq_pos (n : ℕ) : 0 < epsSeq n := by unfold epsSeq; positivity

lemma tendsto_epsSeq : Tendsto epsSeq atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => epsSeq_pos n⟩

lemma tendsto_truncFun_seq (t : ℝ) : Tendsto (fun n => truncFun (epsSeq n) t) atTop (𝓝 t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [truncFun_zero]
  · exact tendsto_const_nhds.congr'
      ((tendsto_epsSeq.eventually (truncFun_eventually ht)).mono fun n hn => hn.1.symm)

lemma tendsto_truncDeriv_seq (t : ℝ) :
    Tendsto (fun n => truncDeriv (epsSeq n) t) atTop (𝓝 (nzInd t)) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [truncDeriv_zero, nzInd]
  · simp only [nzInd, ht, ↓reduceIte]
    exact tendsto_const_nhds.congr'
      ((tendsto_epsSeq.eventually (truncFun_eventually ht)).mono fun n hn => hn.2.symm)

lemma truncDeriv_le_nzInd {C : ℝ} (hC : ∀ u : ℝ, (u + 1) * deriv Real.smoothTransition u ≤ C)
    (ε t : ℝ) : truncDeriv ε t ≤ (1 + 2 * C) * nzInd t := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [truncDeriv_zero, nzInd]
  · simp only [nzInd, ht, ↓reduceIte, mul_one]
    exact truncDeriv_le hC ε t

variable (V u χ) in
/-- `I(x) = χ² 1_{u ≠ 0} |∇(1_V u)|²`, the `ε → 0` limit of `A`. -/
def caccI (x : ℂ) : ℝ := χ x ^ 2 * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖ ^ 2

variable (V u χ) in
/-- The limit gradient `(1_V u) ∇χ + χ 1_{u ≠ 0} ∇(1_V u)`. -/
def limGrad (x : ℂ) : ℂ →L[ℝ] ℝ :=
  V.indicator u x • fderiv ℝ χ x + (χ x * nzInd (V.indicator u x)) • fderiv ℝ (V.indicator u) x

lemma caccI_nonneg (x : ℂ) : 0 ≤ caccI V u χ x := by
  have := nzInd_nonneg (V.indicator u x)
  unfold caccI
  positivity

variable (hV : IsOpen V) (hu : InnerProductSpace.HarmonicOnNhd u V)
  (hbd : ∀ z ∈ frontier V ∩ U', Tendsto u (𝓝[V] z) (𝓝 0)) (hχU : tsupport χ ⊆ U')
  (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)

include hV hu hbd hχU hχ hχc in
/-- `χ² 1_{u ≠ 0} |∇u|²` is integrable (Fatou and the Caccioppoli inequality). -/
lemma integrable_caccI : Integrable (caccI V u χ) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_cast)
  have hlim : ∀ x, Tendsto (fun n => caccA V u χ (epsSeq n) x) atTop (𝓝 (caccI V u χ x)) :=
    fun x => ((tendsto_truncDeriv_seq _).const_mul _).mul_const _
  have hAm : ∀ n, AEStronglyMeasurable (caccA V u χ (epsSeq n)) volume := fun n =>
    (continuous_caccA hV hu hbd hχU hχ1 (epsSeq_pos n)).aestronglyMeasurable
  have hAi : ∀ n, Integrable (caccA V u χ (epsSeq n)) := fun n =>
    (continuous_caccA hV hu hbd hχU hχ1 (epsSeq_pos n)).integrable_of_hasCompactSupport
      (hasCompactSupport_caccA hχc _)
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop hAm (ae_of_all _ hlim), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => caccI_nonneg x)]
  calc ∫⁻ x, ENNReal.ofReal (caccI V u χ x)
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal (caccA V u χ (epsSeq n) x)) atTop := by
        congr 1
        funext x
        exact (((ENNReal.continuous_ofReal.tendsto _).comp (hlim x)).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (caccA V u χ (epsSeq n) x)) atTop :=
        lintegral_liminf_le' fun n => (hAm n).aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal (4 * ∫ x, caccB V u χ x) := by
        refine liminf_le_of_frequently_le' (Eventually.of_forall fun n => ?_).frequently
        rw [← ofReal_integral_eq_lintegral_ofReal (hAi n)
          (ae_of_all _ fun x => caccA_nonneg _ x)]
        exact ENNReal.ofReal_le_ofReal (integral_caccA_le hV hu hbd hχU hχ hχc (epsSeq_pos n))
    _ < ⊤ := ENNReal.ofReal_lt_top

include hV hu hbd hχU in
lemma continuous_mul_indicator (hχ1 : Continuous χ) :
    Continuous fun x => χ x * V.indicator u x := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U' ∪ V
  · exact hχ1.continuousAt.mul (continuousAt_indicator_of_tendsto_frontier hV hcu hbd hx)
  · have hxs : x ∉ tsupport χ := fun h => hx (Or.inl (hχU h))
    have hz : (fun x => χ x * V.indicator u x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxs] with y hy
      simp [show χ y = 0 from hy]
    exact continuousAt_const.congr hz.symm

include hV hu hbd hχU in
/-- Pointwise domination of `∇(χ Φ_ε(1_V u))` (with `K = 1 + 2C`). -/
lemma norm_fderiv_truncCutoff_le (hχ1 : ContDiff ℝ 1 χ) {C : ℝ}
    (hC : ∀ u : ℝ, (u + 1) * deriv Real.smoothTransition u ≤ C) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ‖fderiv ℝ (truncCutoff V u χ ε) x‖ ≤ |V.indicator u x| * ‖fderiv ℝ χ x‖ +
      (1 + 2 * C) * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖) := by
  rw [fderiv_truncCutoff hV hu hbd hχU hχ1 hε]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_truncFun_le _ _) (norm_nonneg _)
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (truncDeriv_nonneg _ _)]
    have := truncDeriv_le_nzInd hC ε (V.indicator u x)
    calc |χ x| * truncDeriv ε (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖
        ≤ |χ x| * ((1 + 2 * C) * nzInd (V.indicator u x)) * ‖fderiv ℝ (V.indicator u) x‖ := by
          gcongr
      _ = _ := by ring

omit hV hu hbd hχU in
lemma norm_limGrad_le {K : ℝ} (hK : 1 ≤ K) (x : ℂ) :
    ‖limGrad V u χ x‖ ≤ |V.indicator u x| * ‖fderiv ℝ χ x‖ +
      K * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖) := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
  · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (nzInd_nonneg _)]
    have h0 : 0 ≤ |χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖ := by
      have := nzInd_nonneg (V.indicator u x); positivity
    calc |χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖
        = 1 * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK h0

omit hV hu hbd hχU in
lemma sq_add_le_dom {K : ℝ} (x : ℂ) :
    (|V.indicator u x| * ‖fderiv ℝ χ x‖ +
      K * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖)) ^ 2 ≤
      2 * caccB V u χ x + 2 * K ^ 2 * caccI V u χ x := by
  have ha : (|V.indicator u x| * ‖fderiv ℝ χ x‖) ^ 2 = caccB V u χ x := by
    simp [caccB, mul_pow, sq_abs]
  have hb : (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖) ^ 2 =
      caccI V u χ x := by
    simp only [caccI, mul_pow, sq_abs, nzInd_sq]
  rw [← ha, ← hb]
  nlinarith [sq_nonneg (|V.indicator u x| * ‖fderiv ℝ χ x‖ -
    K * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖))]

include hV hu hbd hχU hχ hχc in
/-- `∇gₙ → limGrad` in `L²`, with `gₙ = χ Φ_{εₙ}(1_V u)`; the squared differences are integrable. -/
lemma tendsto_integral_norm_fderiv_sub_limGrad :
    (∀ n, Integrable fun x => ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x - limGrad V u χ x‖ ^ 2) ∧
      Tendsto (fun n => ∫ x, ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x - limGrad V u χ x‖ ^ 2)
        atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_smoothTransition_bound
  have hC' : ∀ u : ℝ, (u + 1) * deriv Real.smoothTransition u ≤ C := fun u => (hC u).2
  have hK1 : 1 ≤ 1 + 2 * C := by linarith
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_cast)
  have hfdc : ∀ n, Continuous (fderiv ℝ (truncCutoff V u χ (epsSeq n))) := fun n =>
    (contDiff_truncCutoff hV hu hbd hχU hχ (epsSeq_pos n)).continuous_fderiv (by norm_cast)
  have hconv : ∀ x, Tendsto (fun n => fderiv ℝ (truncCutoff V u χ (epsSeq n)) x) atTop
      (𝓝 (limGrad V u χ x)) := fun x => by
    simp only [fderiv_truncCutoff hV hu hbd hχU hχ1 (epsSeq_pos _), limGrad]
    exact ((tendsto_truncFun_seq _).smul_const _).add
      (((tendsto_truncDeriv_seq _).const_mul _).smul_const _)
  have hLm : AEStronglyMeasurable (limGrad V u χ) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfdc n).aestronglyMeasurable)
      (ae_of_all _ hconv)
  have hDi : Integrable fun x => 4 * (2 * caccB V u χ x + 2 * (1 + 2 * C) ^ 2 * caccI V u χ x) :=
    ((((continuous_caccB hV hu hbd hχU hχ1).integrable_of_hasCompactSupport
      (hasCompactSupport_caccB hχc)).const_mul 2).add
      ((integrable_caccI hV hu hbd hχU hχ hχc).const_mul _)).const_mul 4
  have hbd' : ∀ n x, ‖‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x - limGrad V u χ x‖ ^ 2‖ ≤
      4 * (2 * caccB V u χ x + 2 * (1 + 2 * C) ^ 2 * caccI V u χ x) := fun n x => by
    rw [Real.norm_of_nonneg (pow_two_nonneg _)]
    have h1 := norm_fderiv_truncCutoff_le hV hu hbd hχU hχ1 hC' (epsSeq_pos n) x
    have h2 := norm_limGrad_le (V := V) (u := u) (χ := χ) hK1 x
    have h3 := sq_add_le_dom (V := V) (u := u) (χ := χ) (K := 1 + 2 * C) x
    have h4 := norm_sub_le (fderiv ℝ (truncCutoff V u χ (epsSeq n)) x) (limGrad V u χ x)
    have h5 : ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x - limGrad V u χ x‖ ≤
        2 * (|V.indicator u x| * ‖fderiv ℝ χ x‖ +
          (1 + 2 * C) * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖)) := by
      linarith
    calc ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x - limGrad V u χ x‖ ^ 2
        ≤ (2 * (|V.indicator u x| * ‖fderiv ℝ χ x‖ +
          (1 + 2 * C) * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h5 2
      _ = 4 * (|V.indicator u x| * ‖fderiv ℝ χ x‖ +
          (1 + 2 * C) * (|χ x| * nzInd (V.indicator u x) * ‖fderiv ℝ (V.indicator u) x‖)) ^ 2 := by
          ring
      _ ≤ _ := by linarith
  refine ⟨fun n => Integrable.mono' hDi (((hfdc n).aestronglyMeasurable.sub hLm).norm.pow 2)
    (ae_of_all _ (hbd' n)), ?_⟩
  have := tendsto_integral_of_dominated_convergence
    (F := fun n x => ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x - limGrad V u χ x‖ ^ 2) _
    (fun n => ((hfdc n).aestronglyMeasurable.sub hLm).norm.pow 2) hDi
    (fun n => ae_of_all _ (hbd' n))
    (ae_of_all _ fun x => ((hconv x).sub_const (limGrad V u χ x)).norm.pow 2)
  simpa using this

include hV hu hbd hχU hχ hχc in
/-- `∫ |∇gₙ|² → ∫ |limGrad|²`. -/
lemma tendsto_integral_norm_fderiv_truncCutoff :
    Tendsto (fun n => ∫ x, ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x‖ ^ 2) atTop
      (𝓝 (∫ x, ‖limGrad V u χ x‖ ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := exists_deriv_smoothTransition_bound
  have hC' : ∀ u : ℝ, (u + 1) * deriv Real.smoothTransition u ≤ C := fun u => (hC u).2
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_cast)
  have hfdc : ∀ n, Continuous (fderiv ℝ (truncCutoff V u χ (epsSeq n))) := fun n =>
    (contDiff_truncCutoff hV hu hbd hχU hχ (epsSeq_pos n)).continuous_fderiv (by norm_cast)
  have hconv : ∀ x, Tendsto (fun n => fderiv ℝ (truncCutoff V u χ (epsSeq n)) x) atTop
      (𝓝 (limGrad V u χ x)) := fun x => by
    simp only [fderiv_truncCutoff hV hu hbd hχU hχ1 (epsSeq_pos _), limGrad]
    exact ((tendsto_truncFun_seq _).smul_const _).add
      (((tendsto_truncDeriv_seq _).const_mul _).smul_const _)
  have hDi : Integrable fun x => 2 * caccB V u χ x + 2 * (1 + 2 * C) ^ 2 * caccI V u χ x :=
    (((continuous_caccB hV hu hbd hχU hχ1).integrable_of_hasCompactSupport
      (hasCompactSupport_caccB hχc)).const_mul 2).add
      ((integrable_caccI hV hu hbd hχU hχ hχc).const_mul _)
  refine tendsto_integral_of_dominated_convergence
    (F := fun n x => ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x‖ ^ 2) _
    (fun n => ((hfdc n).norm.pow 2).aestronglyMeasurable) hDi
    (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (hconv x).norm.pow 2)
  rw [Real.norm_of_nonneg (pow_two_nonneg _)]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (norm_fderiv_truncCutoff_le hV hu hbd hχU hχ1 hC' (epsSeq_pos n) x) 2).trans
    (sq_add_le_dom x)

include hV hu hbd hχU in
lemma fderiv_truncCutoff_eq_zero {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : x ∉ V) :
    fderiv ℝ (truncCutoff V u χ ε) x = 0 := by
  have hcu : ContinuousOn u V := (contDiffOn_of_harmonicOnNhd (n := 0) hu).continuousOn
  rw [(truncCutoff_eventuallyEq_zero hV hcu hbd hχU hε hx).fderiv_eq]
  exact fderiv_const_apply 0

include hV hu hbd hχU in
lemma dirichletEnergyOn_truncCutoff {ε : ℝ} (hε : 0 < ε) :
    QuantumZipper.dirichletEnergyOn V (truncCutoff V u χ ε) =
      (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ (truncCutoff V u χ ε) x‖ ^ 2 := by
  unfold QuantumZipper.dirichletEnergyOn
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp [fderiv_truncCutoff_eq_zero hV hu hbd hχU hε hx]]

omit hV hu hbd hχU in
/-- `E_V(f₁ − f₂) ≤ (2π)⁻¹ (2‖∇f₁ − L‖² + 2‖∇f₂ − L‖²)` for `f₁, f₂ ∈ C_c^1`. -/
lemma dirichletEnergyOn_sub_le {f₁ f₂ : ℂ → ℝ} (h₁ : ContDiff ℝ 1 f₁) (h₂ : ContDiff ℝ 1 f₂)
    (hc₁ : HasCompactSupport f₁) (hc₂ : HasCompactSupport f₂) (L : ℂ → ℂ →L[ℝ] ℝ)
    (hi₁ : Integrable fun x => ‖fderiv ℝ f₁ x - L x‖ ^ 2)
    (hi₂ : Integrable fun x => ‖fderiv ℝ f₂ x - L x‖ ^ 2) :
    QuantumZipper.dirichletEnergyOn V (f₁ - f₂) ≤
      (2 * Real.pi)⁻¹ *
        (2 * (∫ x, ‖fderiv ℝ f₁ x - L x‖ ^ 2) + 2 * ∫ x, ‖fderiv ℝ f₂ x - L x‖ ^ 2) := by
  have hd : ∀ x, fderiv ℝ (f₁ - f₂) x = fderiv ℝ f₁ x - fderiv ℝ f₂ x := fun x =>
    fderiv_sub (h₁.differentiable one_ne_zero x) (h₂.differentiable one_ne_zero x)
  have hint : Integrable fun x => ‖fderiv ℝ (f₁ - f₂) x‖ ^ 2 := by
    have hcs : HasCompactSupport (fderiv ℝ (f₁ - f₂)) := (hc₁.sub hc₂).fderiv ℝ
    have hcont : Continuous fun x => ‖fderiv ℝ (f₁ - f₂) x‖ ^ 2 :=
      (((h₁.sub h₂).continuous_fderiv one_ne_zero).norm).pow 2
    have hcs2 : HasCompactSupport fun x => ‖fderiv ℝ (f₁ - f₂) x‖ ^ 2 :=
      hcs.mono' fun x hx => subset_tsupport _ fun h => hx (by
        change ‖fderiv ℝ (f₁ - f₂) x‖ ^ 2 = 0
        rw [h, norm_zero]
        norm_num)
    exact hcont.integrable_of_hasCompactSupport hcs2
  unfold QuantumZipper.dirichletEnergyOn
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (setIntegral_le_integral hint (ae_of_all _ fun x => by positivity)).trans ?_
  refine (integral_mono (g := fun x => 2 * ‖fderiv ℝ f₁ x - L x‖ ^ 2 +
      2 * ‖fderiv ℝ f₂ x - L x‖ ^ 2) hint ((hi₁.const_mul 2).add (hi₂.const_mul 2))
    fun x => ?_).trans_eq ?_
  · rw [hd]
    have h1 := norm_sub_le (fderiv ℝ f₁ x - L x) (fderiv ℝ f₂ x - L x)
    rw [sub_sub_sub_cancel_right] at h1
    set p := ‖fderiv ℝ f₁ x - L x‖
    set q := ‖fderiv ℝ f₂ x - L x‖
    have hp : 0 ≤ p := norm_nonneg _
    have hq : 0 ≤ q := norm_nonneg _
    have h0 := norm_nonneg (fderiv ℝ f₁ x - fderiv ℝ f₂ x)
    calc ‖fderiv ℝ f₁ x - fderiv ℝ f₂ x‖ ^ 2 ≤ (p + q) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ 2 * p ^ 2 + 2 * q ^ 2 := by nlinarith [sq_nonneg (p - q)]
  · rw [integral_add (hi₁.const_mul 2) (hi₂.const_mul 2), integral_const_mul, integral_const_mul]

include hV hu hbd hχU hχ hχc in
/-- **Approximation by test functions** (specification p. 48, "approximating by these truncated
functions"): `gₙ = χ Φ_{εₙ}(1_V u) ∈ C_c^∞(V)` has convergent Dirichlet energy on `V`, is Cauchy for
the Dirichlet energy, and `∫ gₙ φ → ∫ χ (1_V u) φ` for continuous compactly supported `φ`. -/
theorem exists_dirichlet_approx :
    ∃ v : ℝ,
      Tendsto (fun n => QuantumZipper.dirichletEnergyOn V (truncCutoff V u χ (epsSeq n))) atTop
        (𝓝 v) ∧
      Tendsto (fun p : ℕ × ℕ => QuantumZipper.dirichletEnergyOn V
        (truncCutoff V u χ (epsSeq p.1) - truncCutoff V u χ (epsSeq p.2))) atTop (𝓝 0) ∧
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        Tendsto (fun n => ∫ x, truncCutoff V u χ (epsSeq n) x * φ x) atTop
          (𝓝 (∫ x, χ x * V.indicator u x * φ x)) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_cast)
  obtain ⟨hci, hc⟩ := tendsto_integral_norm_fderiv_sub_limGrad hV hu hbd hχU hχ hχc
  refine ⟨(2 * Real.pi)⁻¹ * ∫ x, ‖limGrad V u χ x‖ ^ 2, ?_, ?_, ?_⟩
  · have e : (fun n => QuantumZipper.dirichletEnergyOn V (truncCutoff V u χ (epsSeq n))) =
        fun n => (2 * Real.pi)⁻¹ * ∫ x, ‖fderiv ℝ (truncCutoff V u χ (epsSeq n)) x‖ ^ 2 :=
      funext fun n => dirichletEnergyOn_truncCutoff hV hu hbd hχU (epsSeq_pos n)
    rw [e]
    exact (tendsto_integral_norm_fderiv_truncCutoff hV hu hbd hχU hχ hχc).const_mul _
  · have hc1 : Tendsto (fun p : ℕ × ℕ =>
        ∫ x, ‖fderiv ℝ (truncCutoff V u χ (epsSeq p.1)) x - limGrad V u χ x‖ ^ 2) atTop (𝓝 0) := by
      rw [← prod_atTop_atTop_eq]; exact hc.comp tendsto_fst
    have hc2 : Tendsto (fun p : ℕ × ℕ =>
        ∫ x, ‖fderiv ℝ (truncCutoff V u χ (epsSeq p.2)) x - limGrad V u χ x‖ ^ 2) atTop (𝓝 0) := by
      rw [← prod_atTop_atTop_eq]; exact hc.comp tendsto_snd
    have hR := ((hc1.const_mul 2).add (hc2.const_mul 2)).const_mul (2 * Real.pi)⁻¹
    simp only [mul_zero, add_zero] at hR
    refine squeeze_zero (fun p => ?_) (fun p => dirichletEnergyOn_sub_le
      ((contDiff_truncCutoff hV hu hbd hχU hχ1 (epsSeq_pos p.1)))
      ((contDiff_truncCutoff hV hu hbd hχU hχ1 (epsSeq_pos p.2)))
      (hasCompactSupport_truncCutoff hχc _) (hasCompactSupport_truncCutoff hχc _)
      (limGrad V u χ) (hci p.1) (hci p.2)) hR
    unfold QuantumZipper.dirichletEnergyOn
    exact mul_nonneg (by positivity) (setIntegral_nonneg_of_ae (ae_of_all _ fun x => by positivity))
  · intro φ hφ hφc
    have hm := continuous_mul_indicator hV hu hbd hχU hχ.continuous
    refine tendsto_integral_of_dominated_convergence (fun x => ‖χ x * V.indicator u x * φ x‖)
      (fun n => ((contDiff_truncCutoff hV hu hbd hχU hχ1 (epsSeq_pos n)).continuous.mul
        hφ).aestronglyMeasurable)
      ((hm.mul hφ).norm.integrable_of_hasCompactSupport (hφc.mul_left.norm))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · simp only [truncCutoff, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (abs_truncFun_le (epsSeq n) (V.indicator u x)) (abs_nonneg _)) (abs_nonneg _)
    · simp only [truncCutoff]
      exact ((tendsto_truncFun_seq _).const_mul _).mul_const _

end Limit

end GFF
end InteractingSLE
