/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCAux79SideSignFlow

/-!
# The orientation of the new piece, II: the relative map of the composed and single-path charts

Packet PROVE-FCSIDE (the deterministic orientation `FCAux79.IsFCSideSign`, spec p. 290). At a later line
`(s₀ + t, t₀)` whose tip `q = s₀ + t` is interior, compare the composed chart (inverse `Ψ = ψ ∘ f_Q⁻¹`) with the
single-path chart `f(z) = f^{(1)}_q(z − x₁)` of the first path at the same time `q`: the **relative map**
`h = f ∘ Ψ` is holomorphic and injective from `ℍ` into `ℍ`.

* `exists_tendsto_of_ultrafilter`: a function continuous on `ℍ` whose ultrafilter limits at a real point all lie in
  a set `S` containing no real interval has a limit there (two different limits `a₁ < a₂` would give, by the
  intermediate value theorem on the connected half-discs, an ultrafilter along which the real part is a constant
  `b ∈ (a₁, a₂) \ S`, whose limit would be `b`);
* `re_deriv_nonneg_of_im_pos`: the boundary derivative of a holomorphic map real at a real point and mapping the
  upper half-ball into `ℍ` has nonnegative real part;
* `IsPhysChart.exists_notMem_fibre`: the single-path inverse chart is constant on no real interval (Schwarz
  reflection and the identity theorem, `QuantumZipper.CA.eqOn_const_of_eq_const_on_Ioo`);
* `IsFCLine.exists_tendsto_rel` (**limits of the relative map**): at every real `c` that `Φ_Q` sends onto the chart
  path, `h` has a real limit `a` with `F̄(a) = Ψ̄(c)` (the ultrafilter limits are real,
  `IsPhysChart.exists_real_tendsto`, and lie in the fibre of the single-path inverse chart over `Ψ̄(c)`);
* `IsFCLine.sign_of_tendsto_rel` (**the sign**): if `Φ_Q` sends the whole real segment between `0` and `ξ` onto the
  chart path, the limit of `h` at `ξ` has the sign of `ξ`. The boundary extension `k` of `h` is real and continuous
  on the segment (`continuousOn_extendFrom`), nondecreasing by the Schwarz reflection at every interior point
  (`re_deriv_nonneg_of_im_pos`, `monotoneOn_of_deriv_nonneg`), vanishes at `0` (both charts send the interior tip
  `η₁(q)` to `0`, `IsPhysChart.tip_fibre`) and nowhere else (`F̄(k(c)) = Ψ̄(c) ≠ η₁(q)` for `c ≠ 0`, by the
  injectivity of `ψ` on `ℍ̄` and the tip fibre of the chart path).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE

namespace Restart.FCAux79

open Sec7 Sec7.SideHeightBox Supp7

/-! ### Two analytic facts at a real point -/

section Analytic

/-- **A limit from ultrafilter limits in a set without real intervals.** -/
theorem exists_tendsto_of_ultrafilter {h : ℂ → ℂ} {c : ℝ} {S : Set ℝ} (hhc : ContinuousOn h H)
    (hS : ∀ a b : ℝ, a < b → ∃ x ∈ Ioo a b, x ∉ S)
    (hU : ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ 𝓝[H] (c : ℂ) → ∃ a ∈ S, Tendsto h U (𝓝 (a : ℂ))) :
    ∃ a ∈ S, Tendsto h (𝓝[H] (c : ℂ)) (𝓝 (a : ℂ)) := by
  have := neBot_nhdsWithin_H_ofReal c
  obtain ⟨a₀, ha₀S, ha₀⟩ := hU (Ultrafilter.of (𝓝[H] (c : ℂ))) (Ultrafilter.of_le _)
  have hre : ∀ (U : Ultrafilter ℂ) (a : ℝ), Tendsto h U (𝓝 (a : ℂ)) → Tendsto (fun w => (h w).re) U (𝓝 a) :=
    fun U a ha => by
      have := (continuous_re.tendsto (a : ℂ)).comp ha
      rwa [ofReal_re] at this
  have key : ∀ U₁ U₂ : Ultrafilter ℂ, (U₁ : Filter ℂ) ≤ 𝓝[H] (c : ℂ) → (U₂ : Filter ℂ) ≤ 𝓝[H] (c : ℂ) →
      ∀ a₁ a₂ : ℝ, Tendsto h U₁ (𝓝 (a₁ : ℂ)) → Tendsto h U₂ (𝓝 (a₂ : ℂ)) → a₁ < a₂ → False := by
    intro U₁ U₂ hU₁ hU₂ a₁ a₂ h₁ h₂ h12
    obtain ⟨b, hb, hbS⟩ := hS a₁ a₂ h12
    set T : Set ℂ := {w | w ∈ H ∧ (h w).re = b} with hTdef
    have hfreq : ∀ s ∈ 𝓝[H] (c : ℂ), (s ∩ T).Nonempty := by
      intro s hs
      obtain ⟨r, hr, hrs⟩ := Metric.mem_nhdsWithin_iff.1 hs
      have hB : H ∩ ball (c : ℂ) r ∈ 𝓝[H] (c : ℂ) := inter_mem_nhdsWithin H (ball_mem_nhds _ hr)
      have e₁ : ∀ᶠ w in (U₁ : Filter ℂ), w ∈ H ∩ ball (c : ℂ) r := hU₁ hB
      have e₂ : ∀ᶠ w in (U₂ : Filter ℂ), w ∈ H ∩ ball (c : ℂ) r := hU₂ hB
      have f₁ : ∀ᶠ w in (U₁ : Filter ℂ), (h w).re < b := (hre U₁ a₁ h₁) (Iio_mem_nhds hb.1)
      have f₂ : ∀ᶠ w in (U₂ : Filter ℂ), b < (h w).re := (hre U₂ a₂ h₂) (Ioi_mem_nhds hb.2)
      obtain ⟨w₁, hw₁B, hw₁b⟩ := (e₁.and f₁).exists
      obtain ⟨w₂, hw₂B, hw₂b⟩ := (e₂.and f₂).exists
      have hpc : IsPreconnected (H ∩ ball (c : ℂ) r) :=
        ((convex_halfSpace_im_gt 0).inter (convex_ball _ _)).isPreconnected
      have hcont : ContinuousOn (fun w => (h w).re) (H ∩ ball (c : ℂ) r) :=
        continuous_re.comp_continuousOn (hhc.mono inter_subset_left)
      obtain ⟨w, hw, hwe⟩ := hpc.intermediate_value hw₁B hw₂B hcont
        ⟨hw₁b.le, hw₂b.le⟩
      exact ⟨w, hrs ⟨hw.2, hw.1⟩, hw.1, hwe⟩
    have hneT : (𝓝[H] (c : ℂ) ⊓ 𝓟 T).NeBot := by
      rw [inf_principal_neBot_iff]; exact hfreq
    set U₃ := Ultrafilter.of (𝓝[H] (c : ℂ) ⊓ 𝓟 T) with hU₃def
    have hU₃le : (U₃ : Filter ℂ) ≤ 𝓝[H] (c : ℂ) ⊓ 𝓟 T := Ultrafilter.of_le _
    obtain ⟨a₃, ha₃S, ha₃⟩ := hU U₃ (hU₃le.trans inf_le_left)
    have hT : T ∈ (U₃ : Filter ℂ) := hU₃le (mem_inf_of_right (mem_principal_self T))
    have hb3 : a₃ = b := tendsto_nhds_unique (hre U₃ a₃ ha₃)
      (tendsto_const_nhds.congr' (Filter.mem_of_superset hT fun w hw => hw.2.symm))
    exact hbS (hb3 ▸ ha₃S)
  refine ⟨a₀, ha₀S, ?_⟩
  rw [tendsto_iff_ultrafilter]
  intro U hUle
  obtain ⟨a, -, ha⟩ := hU U hUle
  have hae : a = a₀ := by
    rcases lt_trichotomy a a₀ with h' | h' | h'
    · exact (key U _ hUle (Ultrafilter.of_le _) a a₀ ha ha₀ h').elim
    · exact h'
    · exact (key _ U (Ultrafilter.of_le _) hUle a₀ a ha₀ ha h').elim
  rw [← hae]
  exact ha

/-- **The boundary derivative of a map of the upper half-ball into `ℍ` has nonnegative real part** at a real point
where the map is real. -/
theorem re_deriv_nonneg_of_im_pos {G : ℂ → ℂ} {c r : ℝ} (hr : 0 < r) (hd : DifferentiableOn ℂ G (ball (c : ℂ) r))
    (hreal : (G c).im = 0) (hpos : ∀ z ∈ ball (c : ℂ) r, 0 < z.im → 0 < (G z).im) : 0 ≤ (deriv G c).re := by
  have hcB : (c : ℂ) ∈ ball (c : ℂ) r := mem_ball_self hr
  have hdx : DifferentiableAt ℂ G c := hd.differentiableAt (isOpen_ball.mem_nhds hcB)
  have hs := hasDerivAt_iff_tendsto_slope.1 hdx.hasDerivAt
  set φ : ℝ → ℂ := fun t => (c : ℂ) + (t : ℂ) * I with hφ
  have hφc : Continuous φ := by fun_prop
  have hφ0 : φ 0 = c := by simp [hφ]
  have hφt : Tendsto φ (𝓝[>] 0) (𝓝[≠] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (hφc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rwa [hφ0] at this
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [hφ, mem_compl_iff, mem_singleton_iff, add_eq_left, mul_eq_zero, ofReal_eq_zero, I_ne_zero,
        or_false]
      exact ne_of_gt ht
  have hlim := (continuous_re.tendsto _).comp (hs.comp hφt)
  refine ge_of_tendsto hlim ?_
  have hball : ∀ᶠ t in 𝓝[>] (0 : ℝ), φ t ∈ ball (c : ℂ) r :=
    ((hφc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually
      (show ball (c : ℂ) r ∈ 𝓝 (φ 0) by rw [hφ0]; exact isOpen_ball.mem_nhds hcB)
  filter_upwards [hball, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  have hφi : 0 < (φ t).im := by simp [hφ, htpos']
  have hp := hpos _ ht hφi
  show 0 ≤ (slope G c (φ t)).re
  have e : slope G c (φ t) = (G (φ t) - G c) / ((t : ℂ) * I) := by
    rw [slope_def_field]; simp [hφ]
  rw [e, div_re]
  have h1 : ((t : ℂ) * I).re = 0 := by simp
  have h2 : ((t : ℂ) * I).im = t := by simp
  rw [h1, h2, mul_zero, zero_div, zero_add, sub_im, hreal, sub_zero]
  exact div_nonneg (mul_nonneg hp.le htpos'.le) (normSq_nonneg _)

/-- **The single-path inverse chart is constant on no real interval.** -/
theorem IsPhysChart.exists_notMem_fibre {α : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ} (hch : IsPhysChart α q f Φ)
    (p : ℂ) {a b : ℝ} (hab : a < b) : ∃ x ∈ Ioo a b, Φ x ≠ p := by
  by_contra hall
  push Not at hall
  set m : ℝ := (a + b) / 2 with hm
  set r : ℝ := (b - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hballI : ∀ z ∈ ball (m : ℂ) r, z.im = 0 → z.re ∈ Ioo a b := by
    intro z hz hzim
    rw [mem_ball, Complex.dist_eq] at hz
    have h1 : |z.re - m| < r := by
      have := Complex.abs_re_le_norm (z - m)
      rw [sub_re, ofReal_re] at this
      linarith
    rw [abs_lt] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hzero : ∀ z ∈ Hbar ∩ ball (m : ℂ) r, Φ z - p = 0 := by
    refine QuantumZipper.CA.eqOn_const_of_eq_const_on_Ioo (x := m) (r := r)
      ((hch.diff.mono inter_subset_left).sub_const _) ((hch.inv_cont.mono inter_subset_left).sub continuousOn_const)
      (fun z hz hzim => ?_) hab (c := 0) (fun x hx => ⟨?_, by rw [hall x hx, sub_self]⟩)
    · rw [← ofReal_re_of_im hzim, hall _ (hballI z hz hzim), sub_self, zero_im]
    · rw [mem_ball, Complex.dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
  set z₁ : ℂ := (m : ℂ) + ((r / 2 : ℝ) : ℂ) * I with hz₁
  set z₂ : ℂ := (m : ℂ) + ((r / 3 : ℝ) : ℂ) * I with hz₂
  have hmem : ∀ s : ℝ, 0 < s → s < r → (m : ℂ) + (s : ℂ) * I ∈ H ∩ ball (m : ℂ) r := fun s hs hsr =>
    ⟨show 0 < ((m : ℂ) + (s : ℂ) * I).im by simp [hs], by
      rw [mem_ball, Complex.dist_eq, add_sub_cancel_left, norm_mul, norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hs]
      exact hsr⟩
  have h₁ := hmem (r / 2) (by linarith) (by linarith)
  have h₂ := hmem (r / 3) (by linarith) (by linarith)
  have e₁ := hzero _ ⟨QuantumZipper.H_subset_Hbar h₁.1, h₁.2⟩
  have e₂ := hzero _ ⟨QuantumZipper.H_subset_Hbar h₂.1, h₂.2⟩
  have hΦ : Φ z₁ = Φ z₂ := by rw [sub_eq_zero] at e₁ e₂; rw [e₁, e₂]
  have hzz : z₁ = z₂ := by rw [← hch.f_inv z₁ h₁.1, ← hch.f_inv z₂ h₂.1, hΦ]
  have := congrArg Complex.im hzz
  simp only [hz₁, hz₂, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    zero_add] at this
  linarith

end Analytic

/-! ### The single-path chart is holomorphic -/

section PhysDiff

/-- **The physical single-path chart `z ↦ f_q(z − x)` is holomorphic on the unbounded domain of the stopped trace**
(through the global continuation of the frozen driver). -/
theorem differentiableOn_physChart {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}
    (hg : IsGeneratingTrace W ζ (fun t => α t - x)) (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0)
    (hq : (q : ℝ≥0∞) < ζ) :
    DifferentiableOn ℂ (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)) (H \ fillH (α '' Icc 0 q)) := by
  obtain ⟨Wg, -, T', hqT', hWgc, -, -, hWeq, -⟩ := ReverseArc.exists_global_model hg hWc hW0 hq
  have hf : ∀ z, fwdMap (fun r : ℝ => W r.toNNReal) q z = fwdMap Wg q z := fun z =>
    fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => (hWeq r ⟨hr.1, hr.2.trans hqT'.le⟩).symm
  have hhull : fwdHull Wg q = fillH ((fun t => α t - x) '' Icc 0 q) := by
    rw [fwdHull_eq_of_eqOn q.coe_nonneg hqT' hWeq]
    exact SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hg hq
  have hd : DifferentiableOn ℂ (fun z => fwdMap Wg q (z - x)) (H \ fillH (α '' Icc 0 q)) := by
    refine (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWgc q.coe_nonneg).comp
      (differentiableOn_id.sub_const _) fun z hz => ?_
    have := (ReverseArc.mem_H_diff_fillH_phys_iff (α := α) x q z).1 hz
    rwa [← hhull] at this
  exact hd.congr fun z _ => hf _

end PhysDiff

/-! ### The relative map of the composed and single-path charts -/

section Rel

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} {ω : Ω} {x₁ x₂ : ℝ} {t : ℝ≥0}
  {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}

/-- The later line lies strictly after the first contact. -/
theorem IsFCLine.t_pos (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) : 0 < t := by
  refine lt_of_le_of_ne zero_le fun h => ?_
  have h1 : d.inv ω (γ Q) = d.inv ω (γ 0) := by rw [hl.tip, hl.inv_γ_zero hd, ← h, add_zero]
  exact (ne_of_gt hl.pos) (hl.injOn_inv_γ hd ⟨zero_le, le_rfl⟩ ⟨zero_le, zero_le⟩ h1)

/-- **The new piece misses the first-contact union** `K` after the contact. -/
theorem IsFCLine.notMem_K (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {u : ℝ≥0}
    (hu : d.s₀ ω < u) (hut : u ≤ d.s₀ ω + t) : d.η₁ ω u ∉ d.K ω := by
  have hfc := hl.isFirstContact hd
  have huζ : (u : ℝ≥0∞) ≤ d.ζ₁ ω := (ENNReal.coe_le_coe.2 hut).trans hl.le_life
  rw [hl.K_eq]
  rintro (⟨s', hs', he⟩ | ⟨t', ht', he⟩)
  · have := hl.injOn₁ ⟨zero_le, hs'.2.trans le_self_add⟩ ⟨zero_le, hut⟩ he
    exact absurd (this ▸ hs'.2) (not_le.2 hu)
  · obtain ⟨-, ht₀⟩ := hfc.2.2.2 u t' huζ ((ENNReal.coe_le_coe.2 ht'.2).trans hfc.2.1) he.symm
    have htt : t' = d.t₀ ω := le_antisymm ht'.2 ht₀
    have h1 : d.η₁ ω u = d.η₁ ω (d.s₀ ω) := by rw [hfc.2.2.1, ← htt]; exact he.symm
    have := hl.injOn₁ ⟨zero_le, hut⟩ ⟨zero_le, le_self_add⟩ h1
    exact (ne_of_gt hu) this

/-- The tip of the chart path is interior when the tip of the new piece is. -/
theorem IsFCLine.γ_mem_H_of_tip (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood)
    (htip : d.η₁ ω (d.s₀ ω + t) ∈ H) : γ Q ∈ H := by
  rcases mem_H_or_im_eq_zero (hl.γ_mem_Hbar le_rfl) with h | h
  · exact h
  exfalso
  have hK := hl.notMem_K hd (lt_add_of_pos_right _ (hl.t_pos hd)) le_rfl
  rcases hd.inv_mem_K_or hl.mem_E (γ Q).re with h1 | ⟨him, -, -⟩
  · rw [ofReal_re_of_im h, hl.tip] at h1; exact hK h1
  · rw [ofReal_re_of_im h, hl.tip] at him
    exact absurd him (ne_of_gt htip)

/-- **Limits of the relative map.** At every real `c` that `Φ_Q` sends onto the chart path, the relative map
`h = f ∘ Ψ` (`Ψ = ψ ∘ f_Q⁻¹`, `f = f^{(1)}_q(· − x₁)` with `q = s₀ + t`) has a real limit `a` within `ℍ`, read back by
the single-path inverse chart as `Ψ̄(c)`. -/
theorem IsFCLine.exists_tendsto_rel (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {W₁ : ℝ≥0 → ℝ}
    (hg₁ : IsGeneratingTrace W₁ (d.ζ₁ ω) (fun s => d.η₁ ω s - x₁))
    (hWc₁ : ContinuousOn W₁ {s | (s : ℝ≥0∞) < d.ζ₁ ω}) (hW0₁ : W₁ 0 = 0)
    (hqζ : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω) {c : ℝ}
    (hc : extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c ∈ γ '' Icc 0 Q) :
    ∃ a : ℝ, Tendsto (fun v => fwdMap (fun r : ℝ => W₁ r.toNNReal) (d.s₀ ω + t)
        (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v) - x₁)) (𝓝[H] (c : ℂ)) (𝓝 (a : ℂ)) ∧
      extendFrom H (fwdMapInv (fun r : ℝ => W₁ r.toNNReal) (d.s₀ ω + t)) a + x₁ =
        d.inv ω (extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c) := by
  set q := d.s₀ ω + t with hqdef
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  set Φ := extendFrom H (fwdMapInv w' Q) with hΦdef
  have hq0 : 0 < q := lt_of_lt_of_le (hl.t_pos hd) le_add_self
  have hch := isPhysChart hg₁ hWc₁ hW0₁ hl.path₁.1 hqζ hq0
  set p₀ := d.inv ω (Φ c) with hp₀
  have hp₀A : p₀ ∈ d.η₁ ω '' Icc 0 q := by
    obtain ⟨σ', hσ', hσ'e⟩ := hc
    obtain ⟨u, hu, he⟩ := hl.exists_inv_γ_eq hσ'.2
    exact ⟨u, ⟨zero_le, hu.2⟩, by rw [hp₀, ← hσ'e, he]⟩
  have hψc : ContinuousOn (d.inv ω) Hbar := (hl.chart hd).2.2.2.2.2.2.2.1
  have hT : Tendsto (fun v => d.inv ω (fwdMapInv w' Q v)) (𝓝[H] (c : ℂ)) (𝓝[H \ fillH (lineK d t ω)] p₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun v hv => (hl.inv_mem hd hv).1⟩
    have h1 := (hl.tendsto_fwdMapInv (ofReal_mem_Hbar c)).mono_right
      (nhdsWithin_mono _ fun z hz => QuantumZipper.H_subset_Hbar hz.1)
    exact (hψc (Φ c) (hl.isChart.inv_mem_Hbar (ofReal_mem_Hbar c))).tendsto.comp h1
  have hsub : d.η₁ ω '' Icc 0 q ⊆ lineK d t ω := fun z hz => Or.inl hz
  have hDA : H \ fillH (lineK d t ω) ⊆ H \ fillH (d.η₁ ω '' Icc 0 q) :=
    sdiff_subset_sdiff_right (fillH_mono hsub)
  have hhc : ContinuousOn (fun v => fwdMap (fun r : ℝ => W₁ r.toNNReal) q
      (d.inv ω (fwdMapInv w' Q v) - x₁)) H :=
    hch.cont.comp (differentiableOn_compInv hd hl).continuousOn fun v hv => hDA (hl.inv_mem hd hv).1
  have hU : ∀ U : Ultrafilter ℂ, (U : Filter ℂ) ≤ 𝓝[H] (c : ℂ) → ∃ a ∈ {a : ℝ | extendFrom H
      (fwdMapInv (fun r : ℝ => W₁ r.toNNReal) q) a + x₁ = p₀}, Tendsto (fun v => fwdMap (fun r : ℝ => W₁ r.toNNReal) q
        (d.inv ω (fwdMapInv w' Q v) - x₁)) U (𝓝 (a : ℂ)) := by
    intro U hU
    have hV : ((U.map fun v => d.inv ω (fwdMapInv w' Q v) : Ultrafilter ℂ) : Filter ℂ) ≤
        𝓝[H \ fillH (d.η₁ ω '' Icc 0 q)] p₀ := by
      rw [Ultrafilter.coe_map]
      exact (map_mono hU).trans (hT.mono_right (nhdsWithin_mono _ hDA))
    obtain ⟨a, hfa, hΦa⟩ := hch.exists_real_tendsto hp₀A _ hV
    refine ⟨a, hΦa, ?_⟩
    rw [Ultrafilter.coe_map] at hfa
    exact tendsto_map'_iff.1 hfa
  obtain ⟨a, haS, ha⟩ := exists_tendsto_of_ultrafilter hhc
    (fun a b hab => IsPhysChart.exists_notMem_fibre hch p₀ hab) hU
  exact ⟨a, ha, haS⟩

/-- **The sign of the relative map.** If `Φ_Q` sends the whole real segment between `0` and `ξ` onto the chart path,
and the tip `η₁(q)` (`q = s₀ + t`) is interior, the limit of the relative map `h = f ∘ Ψ` at `ξ` has the sign of
`ξ`: its boundary values on the segment are real, continuous, nondecreasing (Schwarz reflection), `0` at `0` and
nonzero elsewhere. -/
theorem IsFCLine.sign_of_tendsto_rel (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) (hd : d.IsMeasGood) {W₁ : ℝ≥0 → ℝ}
    (hg₁ : IsGeneratingTrace W₁ (d.ζ₁ ω) (fun s => d.η₁ ω s - x₁))
    (hWc₁ : ContinuousOn W₁ {s | (s : ℝ≥0∞) < d.ζ₁ ω}) (hW0₁ : W₁ 0 = 0)
    (hqζ : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) < d.ζ₁ ω) (htip : d.η₁ ω (d.s₀ ω + t) ∈ H) {ξ : ℝ}
    (hξ : ∀ c ∈ uIcc 0 ξ, extendFrom H (fwdMapInv (fun s : ℝ => W s.toNNReal) Q) c ∈ γ '' Icc 0 Q) {a : ℝ}
    (ha : Tendsto (fun v => fwdMap (fun r : ℝ => W₁ r.toNNReal) (d.s₀ ω + t)
        (d.inv ω (fwdMapInv (fun s : ℝ => W s.toNNReal) Q v) - x₁)) (𝓝[H] (ξ : ℂ)) (𝓝 (a : ℂ))) :
    (0 < ξ → 0 < a) ∧ (ξ < 0 → a < 0) := by
  set q := d.s₀ ω + t with hqdef
  set w₁ : ℝ → ℝ := fun r => W₁ r.toNNReal with hw₁
  set w' : ℝ → ℝ := fun s => W s.toNNReal with hw'
  set Φ := extendFrom H (fwdMapInv w' Q) with hΦdef
  set h : ℂ → ℂ := fun v => fwdMap w₁ q (d.inv ω (fwdMapInv w' Q v) - x₁) with hhdef
  have hq0 : 0 < q := lt_of_lt_of_le (hl.t_pos hd) le_add_self
  have hch := isPhysChart hg₁ hWc₁ hW0₁ hl.path₁.1 hqζ hq0
  have hsub : d.η₁ ω '' Icc 0 q ⊆ lineK d t ω := fun z hz => Or.inl hz
  have hDA : H \ fillH (lineK d t ω) ⊆ H \ fillH (d.η₁ ω '' Icc 0 q) :=
    sdiff_subset_sdiff_right (fillH_mono hsub)
  have hmapsΨ : ∀ v ∈ H, d.inv ω (fwdMapInv w' Q v) ∈ H \ fillH (d.η₁ ω '' Icc 0 q) := fun v hv =>
    hDA (hl.inv_mem hd hv).1
  have hhd : DifferentiableOn ℂ h H :=
    (differentiableOn_physChart hg₁ hWc₁ hW0₁ hqζ).comp (differentiableOn_compInv hd hl) hmapsΨ
  have hhc : ContinuousOn h H := hhd.continuousOn
  have hhH : ∀ v ∈ H, h v ∈ H := fun v hv => hch.maps (hmapsΨ v hv)
  -- the boundary extension on the segment
  have hlim : ∀ c ∈ uIcc 0 ξ, ∃ a : ℝ, Tendsto h (𝓝[H] (c : ℂ)) (𝓝 (a : ℂ)) ∧
      extendFrom H (fwdMapInv w₁ q) a + x₁ = d.inv ω (Φ c) :=
    fun c hc => hl.exists_tendsto_rel hd hg₁ hWc₁ hW0₁ hqζ (hξ c hc)
  set g := extendFrom H h with hgdef
  set B : Set ℂ := H ∪ (fun x : ℝ => (x : ℂ)) '' uIcc 0 ξ with hBdef
  have hgB : ContinuousOn g B := by
    refine continuousOn_extendFrom ?_ ?_
    · rintro z (hz | ⟨x, -, rfl⟩)
      · exact subset_closure hz
      · rw [closure_H]; exact ofReal_mem_Hbar x
    · rintro z (hz | ⟨x, hx, rfl⟩)
      · exact ⟨h z, (hhc.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds⟩
      · obtain ⟨a, ha, -⟩ := hlim x hx
        exact ⟨a, ha⟩
  have hgH : ∀ v ∈ H, g v = h v := fun v hv => extendFrom_eqOn_H hhc hv
  have hgR : ∀ c ∈ uIcc 0 ξ, ∃ a : ℝ, g c = a ∧ extendFrom H (fwdMapInv w₁ q) a + x₁ = d.inv ω (Φ c) := by
    intro c hc
    obtain ⟨a, ha, he⟩ := hlim c hc
    exact ⟨a, extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar c) ha, he⟩
  set k : ℝ → ℝ := fun c => (g c).re with hkdef
  have hkR : ∀ c ∈ uIcc 0 ξ, g c = (k c : ℂ) := by
    intro c hc
    obtain ⟨a, hga, -⟩ := hgR c hc
    rw [hkdef]; simp only [hga, ofReal_re]
  -- the values at `0` and elsewhere
  have htipΦ : extendFrom H (fwdMapInv w₁ q) 0 + x₁ = d.η₁ ω q := hch.tip
  have hk0 : k 0 = 0 := by
    obtain ⟨a, hga, hΦa⟩ := hgR 0 left_mem_uIcc
    have hΦ0 : Φ ((0 : ℝ) : ℂ) = γ Q := by rw [ofReal_zero]; exact hl.isChart.tip
    rw [hΦ0, hl.tip] at hΦa
    have ha0 : a = 0 := hch.tip_fibre htip a hΦa
    show (g ((0 : ℝ) : ℂ)).re = 0
    rw [hga, ha0, ofReal_zero, zero_re]
  have hγQ := hl.γ_mem_H_of_tip hd htip
  have hkne : ∀ c ∈ uIcc 0 ξ, c ≠ 0 → k c ≠ 0 := by
    intro c hc hc0 hk
    obtain ⟨a, hga, hΦa⟩ := hgR c hc
    have ha0 : a = 0 := by
      have := hkR c hc
      rw [hga, hk, ofReal_zero] at this
      exact_mod_cast this
    rw [ha0, ofReal_zero, htipΦ] at hΦa
    have h1 : d.inv ω (Φ c) = d.inv ω (γ Q) := by rw [← hΦa, hl.tip]
    have h2 := inv_injOn_Hbar hd hl (hl.isChart.inv_mem_Hbar (ofReal_mem_Hbar c)) (hl.γ_mem_Hbar le_rfl) h1
    exact hc0 (hl.isChart.tip_fibre hγQ c h2)
  -- monotonicity on the segment
  have hkc : ContinuousOn k (uIcc 0 ξ) :=
    continuous_re.comp_continuousOn (hgB.comp continuous_ofReal.continuousOn fun x hx => Or.inr ⟨x, hx, rfl⟩)
  have hint : interior (uIcc 0 ξ) = Ioo (min 0 ξ) (max 0 ξ) := by
    rw [show uIcc (0 : ℝ) ξ = Icc (min 0 ξ) (max 0 ξ) from rfl, interior_Icc]
  have hderiv : ∀ c ∈ Ioo (min 0 ξ) (max 0 ξ), ∃ k' : ℝ, HasDerivAt k k' c ∧ 0 ≤ k' := by
    intro c hc
    set r := min (c - min 0 ξ) (max 0 ξ - c) with hrdef
    have hr : 0 < r := lt_min (by linarith [hc.1]) (by linarith [hc.2])
    have hball_real : ∀ z ∈ ball (c : ℂ) r, z.im = 0 → z.re ∈ uIcc 0 ξ := by
      intro z hz hzim
      rw [mem_ball, Complex.dist_eq] at hz
      have h1 : |z.re - c| < r := by
        have := Complex.abs_re_le_norm (z - c)
        rw [sub_re, ofReal_re] at this
        linarith
      rw [abs_lt] at h1
      have h2 := min_le_left (c - min 0 ξ) (max 0 ξ - c)
      have h3 := min_le_right (c - min 0 ξ) (max 0 ξ - c)
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hcB : Hbar ∩ ball (c : ℂ) r ⊆ B := fun z hz => by
      rcases mem_H_or_im_eq_zero hz.1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨z.re, hball_real z hz.2 h', ofReal_re_of_im h'⟩
    obtain ⟨G, hGd, hGeq, -⟩ := QuantumZipper.CA.exists_reflection_extension (g := g) (x := c) (r := r)
      ((hhd.congr fun v hv => hgH v hv).mono inter_subset_left) (hgB.mono hcB) (fun z hz hzim => by
        rw [← ofReal_re_of_im hzim, hkR _ (hball_real z hz hzim), ofReal_im])
    have hcball : (c : ℂ) ∈ ball (c : ℂ) r := mem_ball_self hr
    have hGd' : HasDerivAt G (deriv G c) c := (hGd.differentiableAt (isOpen_ball.mem_nhds hcball)).hasDerivAt
    have hk_eq : k =ᶠ[𝓝 c] fun x : ℝ => (G x).re := by
      have : ∀ᶠ x : ℝ in 𝓝 c, (x : ℂ) ∈ ball (c : ℂ) r :=
        (continuous_ofReal.tendsto c).eventually (isOpen_ball.mem_nhds hcball)
      filter_upwards [this] with x hx
      simp only [hkdef]
      rw [hGeq ⟨ofReal_mem_Hbar x, hx⟩]
    refine ⟨(deriv G c).re, hGd'.real_of_complex.congr_of_eventuallyEq hk_eq, ?_⟩
    refine re_deriv_nonneg_of_im_pos hr hGd ?_ fun z hz hzim => ?_
    · rw [hGeq ⟨ofReal_mem_Hbar c, hcball⟩, hkR c (Ioo_subset_Icc_self hc), ofReal_im]
    · have hzH : z ∈ H := hzim
      rw [hGeq ⟨QuantumZipper.H_subset_Hbar hzH, hz⟩, hgH z hzH]
      exact hhH z hzH
  have hmono : MonotoneOn k (uIcc 0 ξ) := by
    refine monotoneOn_of_deriv_nonneg (convex_uIcc 0 ξ) hkc ?_ ?_
    · rw [hint]
      intro c hc
      obtain ⟨k', hk', -⟩ := hderiv c hc
      exact hk'.differentiableAt.differentiableWithinAt
    · rw [hint]
      intro c hc
      obtain ⟨k', hk', hk'0⟩ := hderiv c hc
      rw [hk'.deriv]
      exact hk'0
  -- conclusion
  have h0mem : (0 : ℝ) ∈ uIcc 0 ξ := left_mem_uIcc
  have hξmem : ξ ∈ uIcc 0 ξ := right_mem_uIcc
  have hkξ : k ξ = a := by
    have h1 : g ξ = a := extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar ξ) ha
    rw [hkR ξ hξmem] at h1
    exact_mod_cast h1
  refine ⟨fun hpos => ?_, fun hneg => ?_⟩
  · have h1 := hmono h0mem hξmem hpos.le
    have h2 := hkne ξ hξmem (ne_of_gt hpos)
    rw [hk0, hkξ] at h1
    rw [hkξ] at h2
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  · have h1 := hmono hξmem h0mem hneg.le
    have h2 := hkne ξ hξmem (ne_of_lt hneg)
    rw [hk0, hkξ] at h1
    rw [hkξ] at h2
    exact lt_of_le_of_ne h1 h2

end Rel

end Restart.FCAux79

end InteractingSLE
