/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowWords
import InteractingSLE.Impl.PiecewiseConstant
import InteractingSLE.Foundations.Harmonic.StepData
import InteractingSLE.Foundations.Harmonic.PoissonH

/-!
# §7.4: deterministic steps of Aux. lemmas 117, 122, 132 and Lemma 7.26

Packet PROVE-SEC7-D (specification §7.4, `source/spec/p337-384.md` L897–L939 (Aux. lemma 117), `p385-432.md`
L104–L139 (Aux. lemma 122), L552–L630 (Aux. lemma 132), supplement `p433-480.md` L803–L812 (Lemma 7.26)).

* **Aux. lemma 117.** The driver from the argument at one interior point, `W = Re g − Im g · cot(arg(g − W))`
  (`eq_re_sub_im_mul_cot_arg`); the density identification at `w = i` and `w = 1 + i` turning (NC9.3) into (NC9.4)
  (`eq_zero_of_forall_im_inv`); the vanishing right local time (`tendsto_integral_indicator_inv`,
  `indicator_div_le_indicator_inv`); and (NC9.5) (`eq_zero_of_one_add_half_mul_eq_zero`).
* **Aux. lemma 122.** Harmonic measure of the exposed trace, `ω(z) = (arg(z − V⁺) − arg(z − V⁻))/π`
  (`phaseWindow`): strict monotonicity of `arg(z − x)` in `x` (`arg_sub_ofReal_lt_arg_sub_ofReal`), `0 < ω < 1`
  (`phaseWindow_mem_Ioo`), `ω` is the harmonic measure of `(V⁻, V⁺)` (`ofReal_phaseWindow_eq_harmonicMeasureH`) and the
  bounded harmonic extension of its indicator (`isBoundedHarmonicExtension_phaseWindow`); the difference formula
  (PS9.1) for two Poisson extensions differing by `d` on the exposed interval (`eqOn_sub_eq_mul_phaseWindow`); a
  continuous discrepancy with values in a lattice `cℤ` on a preconnected set is constant
  (`eq_of_isPreconnected_of_continuousOn_of_mem_zmultiples`, `eqOn_const_of_continuousOn_of_mem_zmultiples`).
* **Aux. lemma 132.** The map `F(z) = x₁(1 − e^{−z})` of (SS3) (`mapsTo_ss3Map`), the gap identities of (SS3)
  (`ss3_gap_one`, `ss3_gap_two`), `1 + tanh(X/2) = 2/(1 + e^{−X})` (`one_add_tanh_half`), the drift (SS5) and its limits
  (SS6) `b(−∞) = r₁ − c`, `b(+∞) = S − d` (`tendsto_ss5Drift_atBot`, `tendsto_ss5Drift_atTop`).
* **Lemma 7.26.** The retargeting map `ψ(z) = z/(x₂ − z)`, `ψ⁻¹(w) = x₂w/(1 + w)` (`lemma726Map_inv`,
  `lemma726Inv_map`, `mapsTo_lemma726Map`), and the endpoint correspondence (`lt_lemma726Inv_of_lt_neg_one`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

open DerivLog

/-! ### Aux. lemma 117 -/

/-- **Aux. lemma 117**: at an interior point `z` with `g = g_t(z) ∈ ℍ` and `f = g − W`, the driver is recovered from
`arg f`: `W = Re g − Im g · cot(arg f)`. -/
theorem eq_re_sub_im_mul_cot_arg {g : ℂ} (hg : 0 < g.im) (W : ℝ) :
    W = g.re - g.im * Real.cot (arg (g - W)) := by
  have hne : g - W ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hn : 0 < ‖g - W‖ := norm_pos_iff.2 hne
  have him : (g - W).im = g.im := by simp
  have hre : (g - W).re = g.re - W := by simp
  rw [Real.cot_eq_cos_div_sin, cos_arg hne, sin_arg, him, hre]
  field_simp
  ring

/-- **(NC9.3) ⟹ (NC9.4)**: if `Im(1/w) a + Im(1/w²) b = 0` at `w = i` and `w = 1 + i`, then `a = b = 0`. In Aux.
lemma 117, `a` and `b` are the densities `2(dA − μ dt) + Σ r_j dI^j` and `dQ − k dt`. -/
theorem eq_zero_of_forall_im_inv {a b : ℝ}
    (h₁ : (I⁻¹).im * a + ((I ^ 2)⁻¹).im * b = 0)
    (h₂ : ((1 + I)⁻¹).im * a + (((1 + I) ^ 2)⁻¹).im * b = 0) : a = 0 ∧ b = 0 := by
  have e1 : (I⁻¹).im = -1 := by simp
  have e2 : ((I ^ 2)⁻¹).im = 0 := by simp
  have e3 : ((1 + I)⁻¹).im = -(1 / 2) := by
    rw [inv_im]; simp [normSq_apply]; norm_num
  have e4 : (((1 + I) ^ 2)⁻¹).im = -(1 / 2) := by
    have : (1 + I) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
    rw [this, inv_im]; simp [normSq_apply]; norm_num
  rw [e1, e2] at h₁
  rw [e3, e4] at h₂
  constructor <;> linarith

/-- The same conclusion from the identity at every `w ∈ ℍ` (the form used after the density extension). -/
theorem eq_zero_of_forall_mem_H_im_inv {a b : ℝ}
    (h : ∀ w ∈ H, (w⁻¹).im * a + ((w ^ 2)⁻¹).im * b = 0) : a = 0 ∧ b = 0 :=
  eq_zero_of_forall_im_inv (h I (by show (0 : ℝ) < I.im; simp))
    (h (1 + I) (by show (0 : ℝ) < (1 + I).im; simp))

/-- The local-time bound of Aux. lemma 117: `1{0 < y < ε}/ε ≤ 1{0 < y < ε}/y`. -/
theorem indicator_div_le_indicator_inv {ε y : ℝ} :
    (Ioo 0 ε).indicator (fun _ => ε⁻¹) y ≤ (Ioo 0 ε).indicator (fun y => y⁻¹) y := by
  by_cases hy : y ∈ Ioo 0 ε
  · rw [indicator_of_mem hy, indicator_of_mem hy]
    exact inv_anti₀ hy.1 hy.2.le
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]

/-- **Vanishing right local time** (Aux. lemma 117): if `1{Y > 0}/Y` is integrable, then
`∫ 1{0 < Y < ε}/Y → 0` as `ε → 0⁺` (dominated convergence). With `d⟨Y⟩ = k du` and the bound
`indicator_div_le_indicator_inv` this gives `ε⁻¹ ∫ 1{0 < Y < ε} d⟨Y⟩ → 0`. -/
theorem tendsto_integral_indicator_inv {α : Type*} [MeasurableSpace α] {μ : Measure α} {Y : α → ℝ}
    (hYm : Measurable Y) (hY : Integrable (fun u => (Ioi 0).indicator (fun y => y⁻¹) (Y u)) μ) :
    Tendsto (fun ε => ∫ u, (Ioo 0 ε).indicator (fun y => y⁻¹) (Y u) ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hlim : ∀ u, Tendsto (fun ε => (Ioo 0 ε).indicator (fun y : ℝ => y⁻¹) (Y u)) (𝓝[>] 0) (𝓝 0) := by
    intro u
    by_cases hu : 0 < Y u
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hu] with ε hε
      exact (indicator_of_notMem (fun h : Y u ∈ Ioo 0 ε => absurd h.2 (not_lt.2 hε.2.le)) _).symm
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun ε => ?_)
      exact (indicator_of_notMem (fun h : Y u ∈ Ioo 0 ε => hu h.1) _).symm
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun u => (Ioo 0 ε).indicator (fun y : ℝ => y⁻¹) (Y u)) μ :=
    Eventually.of_forall fun ε =>
      ((measurable_inv.indicator measurableSet_Ioo).comp hYm).aestronglyMeasurable
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂μ,
      ‖(Ioo 0 ε).indicator (fun y : ℝ => y⁻¹) (Y u)‖ ≤ (Ioi 0).indicator (fun y => y⁻¹) (Y u) := by
    refine Eventually.of_forall fun ε => Eventually.of_forall fun u => ?_
    by_cases hu : Y u ∈ Ioo 0 ε
    · rw [indicator_of_mem hu, indicator_of_mem (show Y u ∈ Ioi 0 from hu.1),
        Real.norm_of_nonneg (inv_nonneg.2 hu.1.le)]
    · rw [indicator_of_notMem hu, norm_zero]
      exact indicator_nonneg (fun y (hy : y ∈ Ioi 0) => inv_nonneg.2 (le_of_lt hy)) _
  have key := tendsto_integral_filter_of_dominated_convergence
    (fun u => (Ioi 0).indicator (fun y : ℝ => y⁻¹) (Y u)) hmeas hbound hY
    (Eventually.of_forall hlim)
  simpa using key

/-- **(NC9.5)**: `(1 + r/2) dI = 0` with `r ≠ −2` forces `dI = 0`. -/
theorem eq_zero_of_one_add_half_mul_eq_zero {r x : ℝ} (hr : r ≠ -2) (h : (1 + r / 2) * x = 0) : x = 0 :=
  (mul_eq_zero.1 h).resolve_left fun h' => hr (by linarith)

/-! ### Aux. lemma 122: the harmonic measure of the exposed trace -/

/-- On `ℍ`, `arg (z − x)` is strictly increasing in the real point `x`. -/
theorem arg_sub_ofReal_lt_arg_sub_ofReal {z : ℂ} (hz : z ∈ H) {a b : ℝ} (hab : a < b) :
    arg (z - a) < arg (z - b) := by
  have hza : z - a ∈ H := sub_ofReal_mem_H hz a
  have hzb : z - b ∈ H := sub_ofReal_mem_H hz b
  have hq : (z - b) / (z - a) ∈ H := by
    have := Sec4.div_add_mem_H hz (show -b < -a by linarith)
    simpa [sub_eq_add_neg] using this
  have hlog := log_div_eq_sub_of_mem_H hzb hza
  have him := congrArg Complex.im hlog
  simp only [log_im, sub_im] at him
  have := (arg_mem_Ioo_of_mem_H hq).1
  linarith

/-- The harmonic measure of the exposed interval `(a, b)` in `ℍ`, `ω(z) = (arg(z − b) − arg(z − a))/π`
((PS9.1) with `a = V⁻_t`, `b = V⁺_t`, evaluated at `g_t(z)`). -/
def phaseWindow (a b : ℝ) (z : ℂ) : ℝ := (arg (z - b) - arg (z - a)) / π

/-- `0 < ω < 1` at every point of `ℍ` when `a < b`. -/
theorem phaseWindow_mem_Ioo {a b : ℝ} (hab : a < b) {z : ℂ} (hz : z ∈ H) :
    phaseWindow a b z ∈ Ioo 0 1 := by
  have h1 := arg_sub_ofReal_lt_arg_sub_ofReal hz hab
  have ha := arg_mem_Ioo_of_mem_H (sub_ofReal_mem_H hz a)
  have hb := arg_mem_Ioo_of_mem_H (sub_ofReal_mem_H hz b)
  have hπ := Real.pi_pos
  refine ⟨div_pos (by linarith) hπ, (div_lt_one hπ).2 (by linarith [ha.1, hb.2])⟩

/-- `ω` is the harmonic measure of `(a, b)` (Foundations' `harmonicMeasureH_Ioo`). -/
theorem ofReal_phaseWindow_eq_harmonicMeasureH {a b : ℝ} (hab : a ≤ b) {z : ℂ} (hz : z ∈ H) :
    ENNReal.ofReal (phaseWindow a b z) = harmonicMeasureH z (Ioo a b) := by
  rw [harmonicMeasureH_Ioo hz hab, phaseWindow]

/-- The three-piece step word `(0, 1, 0)` with breakpoints `a ≤ b`. -/
def windowStep (a b : ℝ) (hab : a ≤ b) : StepData where
  n := 2
  x := ![a, b]
  monotone_x := Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; simpa using hab
  v := ![0, 1, 0]

theorem harmonicExtH_windowStep {a b : ℝ} (hab : a ≤ b) (z : ℂ) :
    (windowStep a b hab).harmonicExtH z = phaseWindow a b z := by
  show stepHarmonicH 2 ![a, b] ![0, 1, 0] z = _
  rw [stepHarmonicH, Fin.sum_univ_two, phaseWindow]
  simp
  ring

theorem bdry_windowStep {a b : ℝ} (hab : a < b) {t : ℝ} (hta : t ≠ a) (htb : t ≠ b) :
    (windowStep a b hab.le).bdry t = (Ioo a b).indicator 1 t := by
  rcases lt_or_gt_of_ne hta with h | h
  · rw [indicator_of_notMem (fun h' : t ∈ Ioo a b => absurd h'.1 (not_lt.2 h.le)),
      (windowStep a b hab.le).bdry_eq_of_forall_le_iff (k := 0) (by simp [windowStep]) ?_]
    · simp [windowStep]
    · intro j; fin_cases j <;> simp [windowStep] <;> linarith
  · rcases lt_or_gt_of_ne htb with h' | h'
    · rw [indicator_of_mem (show t ∈ Ioo a b from ⟨h, h'⟩),
        (windowStep a b hab.le).bdry_eq_of_forall_le_iff (k := 1) (by simp [windowStep]) ?_]
      · simp [windowStep]
      · intro j; fin_cases j <;> simp [windowStep] <;> linarith
    · rw [indicator_of_notMem (fun h'' : t ∈ Ioo a b => absurd h''.2 (not_lt.2 h'.le)),
        (windowStep a b hab.le).bdry_eq_of_forall_le_iff (k := 2) (by simp [windowStep]) ?_]
      · simp [windowStep]
      · intro j; fin_cases j <;> simp [windowStep] <;> linarith

/-- `ω` is the bounded harmonic extension of the indicator of `(a, b)` off `{a, b}`. -/
theorem isBoundedHarmonicExtension_phaseWindow {a b : ℝ} (hab : a < b) :
    IsBoundedHarmonicExtension ((Ioo a b).indicator 1) {a, b} (phaseWindow a b) := by
  have he : (windowStep a b hab.le).harmonicExtH = phaseWindow a b :=
    funext (harmonicExtH_windowStep hab.le)
  refine ⟨he ▸ (windowStep a b hab.le).harmonicOnNhd_harmonicExtH, ⟨1, fun z hz => ?_⟩,
    fun t ht => ?_⟩
  · have := phaseWindow_mem_Ioo hab hz
    rw [abs_of_pos this.1]; exact this.2.le
  · have hta : t ≠ a := fun h => ht (Or.inl h)
    have htb : t ≠ b := fun h => ht (Or.inr h)
    rw [← he, ← bdry_windowStep hab hta htb]
    exact (windowStep a b hab.le).tendsto_harmonicExtH fun j => by
      fin_cases j <;> simp [windowStep] <;> [exact hta.symm; exact htb.symm]

/-- **(PS9.1)**: two bounded harmonic extensions whose boundary data differ by `d` exactly on the exposed interval
`(a, b)` (and agree off it, away from a finite exceptional set containing `a, b`) differ by `d ω` on `ℍ`. -/
theorem eqOn_sub_eq_mul_phaseWindow {g g₀ : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite) {a b d : ℝ}
    (hab : a < b) (haS : a ∈ S) (hbS : b ∈ S) {u u₀ : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hu₀ : IsBoundedHarmonicExtension g₀ S u₀)
    (hg : ∀ x ∉ S, g x = g₀ x + d * (Ioo a b).indicator 1 x) :
    EqOn (fun z => u z - u₀ z) (fun z => d * phaseWindow a b z) H := by
  obtain ⟨hω, -, hωl⟩ := isBoundedHarmonicExtension_phaseWindow hab
  obtain ⟨hh₀, ⟨C, hC⟩, hl₀⟩ := hu₀
  have hw : IsBoundedHarmonicExtension g S (fun z => u₀ z + d * phaseWindow a b z) := by
    refine ⟨hh₀.add ?_, ⟨C + |d|, fun z hz => ?_⟩, fun x hx => ?_⟩
    · have := hω.const_smul (c := d)
      simpa [Pi.smul_def, smul_eq_mul] using this
    · have h1 := hC z hz
      have h2 := phaseWindow_mem_Ioo hab hz
      calc |u₀ z + d * phaseWindow a b z| ≤ |u₀ z| + |d * phaseWindow a b z| := abs_add_le _ _
        _ ≤ C + |d| := by
          rw [abs_mul, abs_of_pos h2.1]
          have := mul_le_mul_of_nonneg_left h2.2.le (abs_nonneg d)
          linarith
    · have hxab : x ∉ ({a, b} : Set ℝ) := by
        rintro (rfl | rfl)
        · exact hx haS
        · exact hx hbS
      rw [hg x hx]
      exact (hl₀ x hx).add ((hωl x hxab).const_mul d)
  intro z hz
  have := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hS hw hu hz
  simp only at this ⊢
  rw [this]; ring

/-- A continuous function on a preconnected set with values in a lattice `cℤ` (`c ≠ 0`) is constant there (Aux.
lemma 122: the discrepancy `d_t ∈ 2πχℤ`). -/
theorem eq_of_isPreconnected_of_continuousOn_of_mem_zmultiples {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {f : X → ℝ} (hf : ContinuousOn f S) {c : ℝ} (hc : c ≠ 0)
    (hmem : ∀ t ∈ S, ∃ n : ℤ, f t = n * c) {s t : X} (hs : s ∈ S) (ht : t ∈ S) : f s = f t := by
  have hg : ContinuousOn (fun x => f x / c) S := hf.div_const c
  have hmaps : MapsTo (fun x => f x / c) S (range ((↑) : ℤ → ℝ)) := by
    intro x hx
    obtain ⟨n, hn⟩ := hmem x hx
    exact ⟨n, by simp only [hn]; field_simp⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have := hS.constant_of_mapsTo hdisc hg hmaps hs ht
  field_simp at this
  exact this

/-- **Aux. lemma 122, constancy of the phase**: a discrepancy `d_t` continuous on `(0, T)` with values in `cℤ`
(`c = 2πχ ≠ 0`) is one constant there. -/
theorem eqOn_const_of_continuousOn_of_mem_zmultiples {T : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo 0 T))
    {c : ℝ} (hc : c ≠ 0) (hmem : ∀ t ∈ Ioo 0 T, ∃ n : ℤ, f t = n * c) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 T) :
    EqOn f (fun _ => f t₀) (Ioo 0 T) := fun _ ht =>
  eq_of_isPreconnected_of_continuousOn_of_mem_zmultiples isPreconnected_Ioo hf hc hmem ht ht₀

/-! ### Aux. lemma 132: the strip process -/

/-- The map `F(z) = x₁(1 − e^{−z})` of (SS3). -/
def ss3Map (x₁ : ℝ) (z : ℂ) : ℂ := x₁ * (1 - exp (-z))

theorem ss3Map_zero (x₁ : ℝ) : ss3Map x₁ 0 = 0 := by simp [ss3Map]

/-- `F` maps the strip `S_π = {0 < Im z < π}` into `ℍ` (`x₁ > 0`). -/
theorem mapsTo_ss3Map {x₁ : ℝ} (hx : 0 < x₁) : MapsTo (ss3Map x₁) Sec4.stripPi H := by
  intro z hz
  show 0 < (ss3Map x₁ z).im
  simp only [ss3Map, mul_im, ofReal_re, ofReal_im, sub_im, one_im, exp_im, neg_im, neg_re,
    sub_re, one_re, zero_mul, add_zero, zero_sub, Real.sin_neg, mul_neg, neg_neg]
  exact mul_pos hx (mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2))

/-- (SS3): `V¹ − W = Y`, with `V¹ = p`, `W = p − Y`. -/
theorem ss3_gap_one (p Y : ℝ) : p - (p - Y) = Y := by ring

/-- (SS3): `V² − W = Y(1 + e^{−X})` with `Y = x₁e^{−t−ξ}`, `V² = p + x₁e^{−t−P}`, `W = p − Y`, `X = P − ξ`. -/
theorem ss3_gap_two (x₁ t ξ P p : ℝ) :
    p + x₁ * Real.exp (-t - P) - (p - x₁ * Real.exp (-t - ξ)) =
      x₁ * Real.exp (-t - ξ) * (1 + Real.exp (-(P - ξ))) := by
  have : Real.exp (-t - P) = Real.exp (-t - ξ) * Real.exp (-(P - ξ)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- `tanh x = 1 − 2/(e^{2x} + 1)`. -/
theorem tanh_eq_one_sub (x : ℝ) : Real.tanh x = 1 - 2 / (Real.exp (2 * x) + 1) := by
  have he := Real.exp_pos x
  rw [Real.tanh_eq, Real.exp_neg, two_mul, Real.exp_add]
  field_simp
  ring

/-- `1 + tanh(X/2) = 2/(1 + e^{−X})` (used for the second force coordinate in (SS4)). -/
theorem one_add_tanh_half (X : ℝ) : 1 + Real.tanh (X / 2) = 2 / (1 + Real.exp (-X)) := by
  have h1 := Real.exp_pos X
  have h2 := Real.exp_pos (-X)
  rw [tanh_eq_one_sub, show 2 * (X / 2) = X by ring, Real.exp_neg]
  field_simp
  ring

theorem tendsto_tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 2 / (Real.exp (2 * x) + 1)) atTop (𝓝 0) := by
    refine Tendsto.div_atTop tendsto_const_nhds ?_
    exact tendsto_atTop_add_const_right _ 1
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop two_pos))
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  rw [sub_zero] at this
  exact this.congr fun x => (tanh_eq_one_sub x).symm

theorem tendsto_tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have h : Tendsto (fun x : ℝ => 2 / (Real.exp (2 * x) + 1)) atBot (𝓝 (2 / (0 + 1))) := by
    refine tendsto_const_nhds.div (Tendsto.add_const 1 ?_) (by norm_num)
    exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot two_pos)
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  norm_num at this
  exact this.congr fun x => (tanh_eq_one_sub x).symm

/-- The gap drift (SS5): `b(x) = (1 + ω/2) tanh(x/2) − σ` with `ω = r₂`, `σ = κ/2 − 3 − r₁ − r₂/2`. -/
def ss5Drift (κ r₁ r₂ : ℝ) (x : ℝ) : ℝ := (1 + r₂ / 2) * Real.tanh (x / 2) - (κ / 2 - 3 - r₁ - r₂ / 2)

/-- **(SS6)**: `b(+∞) = S − d` with `S = r₁ + r₂`, `d = κ/2 − 4`. -/
theorem tendsto_ss5Drift_atTop (κ r₁ r₂ : ℝ) :
    Tendsto (ss5Drift κ r₁ r₂) atTop (𝓝 (r₁ + r₂ - (κ / 2 - 4))) := by
  have h : Tendsto (fun x : ℝ => Real.tanh (x / 2)) atTop (𝓝 1) :=
    tendsto_tanh_atTop.comp (tendsto_id.atTop_div_const two_pos)
  have h2 := (h.const_mul (1 + r₂ / 2)).sub_const (κ / 2 - 3 - r₁ - r₂ / 2)
  rw [show r₁ + r₂ - (κ / 2 - 4) = (1 + r₂ / 2) * 1 - (κ / 2 - 3 - r₁ - r₂ / 2) by ring]
  exact h2

/-- **(SS6)**: `b(−∞) = r₁ − c` with `c = d + 2 = κ/2 − 2`. -/
theorem tendsto_ss5Drift_atBot (κ r₁ r₂ : ℝ) :
    Tendsto (ss5Drift κ r₁ r₂) atBot (𝓝 (r₁ - (κ / 2 - 2))) := by
  have h : Tendsto (fun x : ℝ => Real.tanh (x / 2)) atBot (𝓝 (-1)) :=
    tendsto_tanh_atBot.comp (tendsto_id.atBot_div_const two_pos)
  have h2 := (h.const_mul (1 + r₂ / 2)).sub_const (κ / 2 - 3 - r₁ - r₂ / 2)
  rw [show r₁ - (κ / 2 - 2) = (1 + r₂ / 2) * -1 - (κ / 2 - 3 - r₁ - r₂ / 2) by ring]
  exact h2

/-! ### Lemma 7.26: the retargeting map -/

/-- `ψ(z) = z/(x₂ − z)` (Lemma 7.26 proof). -/
def lemma726Map (x₂ : ℝ) (z : ℂ) : ℂ := z / (x₂ - z)

/-- `ψ⁻¹(w) = x₂ w/(1 + w)`. -/
def lemma726Inv (x₂ : ℝ) (w : ℂ) : ℂ := x₂ * w / (1 + w)

theorem lemma726Map_inv {x₂ : ℝ} (hx : 0 < x₂) {w : ℂ} (hw : 1 + w ≠ 0) :
    lemma726Map x₂ (lemma726Inv x₂ w) = w := by
  have hx' : (x₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hd : (x₂ : ℂ) - x₂ * w / (1 + w) = x₂ / (1 + w) := by field_simp; ring
  rw [lemma726Map, lemma726Inv, hd]
  field_simp

theorem lemma726Inv_map {x₂ : ℝ} (hx : 0 < x₂) {z : ℂ} (hz : (x₂ : ℂ) - z ≠ 0) :
    lemma726Inv x₂ (lemma726Map x₂ z) = z := by
  have hx' : (x₂ : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have hd : 1 + z / (x₂ - z) = x₂ / (x₂ - z) := by field_simp; ring
  rw [lemma726Inv, lemma726Map, hd]
  field_simp

/-- `ψ` preserves `ℍ` for `x₂ > 0`. -/
theorem mapsTo_lemma726Map {x₂ : ℝ} (hx : 0 < x₂) : MapsTo (lemma726Map x₂) H H := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hne : (x₂ : ℂ) - z ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  show 0 < (z / (x₂ - z)).im
  rw [div_im]
  simp only [sub_re, sub_im, ofReal_re, ofReal_im, zero_sub]
  rw [← sub_div]
  refine div_pos ?_ (normSq_pos.2 hne)
  nlinarith

/-- A first old-target swallowing endpoint `u < −1` maps to a finite original point beyond `x₂`. -/
theorem lt_lemma726Inv_of_lt_neg_one {x₂ u : ℝ} (hx : 0 < x₂) (hu : u < -1) :
    x₂ < x₂ * u / (1 + u) := by
  rw [lt_div_iff_of_neg (by linarith)]
  nlinarith

end Sec7

end InteractingSLE
