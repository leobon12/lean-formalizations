/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Spec.Sec2.AddMarksPath
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import QuantumZipper.Proofs.RS.HullBasics

/-!
# A protected boundary mark keeps the trace off the boundary beyond it (§4.1, deterministic part)

Packet PROVE-SEC4-A3. Specification §4.1 (`source/spec/p097-144.md`, pp. 105–115): in the proofs of Lemma 4.3
("Dense passive marks on the upper boundary, all with cumulative weight at least `c`, exclude any upper-boundary
contact"), Lemma 4.5 ("A boundary contact in one of these open arcs would swallow a passive mark strictly between
that contact and the adjacent strip end … This contradicts noncollision") and Aux. lemma 22 (the same argument for
the old upper arcs). This file proves the deterministic content of that step, in a form that needs no passive marks:

* `re_add_eq_of_isForwardSol`: a solution of the centred forward flow from a real point is the real force
  equation `g_t(x) = x + ∫ 2/(g − W)`;
* `exists_isForwardSol_of_forceEq_right` (**protection**): if a right force path `u = y + ∫ 2/(u − w)`
  (`y ≥ 0`) stays strictly right of the driver at positive times, every real point `x ≥ y`, `x > 0`, is alive
  (never swallowed) on every `[0, T]`. Proof: if `x` is swallowed at `σ`, its centred flow tends to `0` at `σ⁻`
  (`tendsto_fwdMap_of_realSwallowAt`), and it dominates the centred mark `u − w ≥ 0` (two right solutions keep
  their order, `Sec2.le_of_forceEq_right`), so `u(σ) = w(σ)`;
* `exists_isForwardSol_of_forceEq_left`: the reflected statement (`x ≤ y ≤ 0`);
* `ne_ofReal_of_isGeneratingTrace` (**avoidance**): a continuous generating trace on `[0, ∞)` never visits a
  closed real set `C ∌ 0` all of whose points are alive at all times. Proof: at the first visit `s*` of `C`, at
  `η(s*) = y ∈ C`, points of `ℍ` near `y` are not swallowed by `s*` (`not_mem_fwdHull_of_isForwardSol`), while the
  hull `K_{s*}` is the filling of `η([0, s*])`. So `η(s) ∉ ℍ` for `s < s*` near `s*`; then
  `η([0, s*]) ∩ ℍ = η([0, s₁]) ∩ ℍ` for some `s₁ < s*`, so `K_{s*} = K_{s₁}`, contradicting the strict growth of
  Loewner hulls (`QuantumZipper.RS.fwdHull_ssubset`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

namespace InteractingSLE

namespace Sec4

/-! ### Real solutions of the centred flow as force equations -/

/-- A solution of the centred forward flow from a real point `x` solves the real force equation
`g_t(x) = x + ∫₀ᵗ 2/(g_s(x) − W_s)` with `g = Re u + W`. -/
theorem re_add_eq_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) {x T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (v t).re + W t = x + ∫ s in (0 : ℝ)..t, 2 / (v s).re := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have him : ∀ s ∈ Icc (0 : ℝ) T, (v s).im = 0 := fun s hs =>
    im_eq_zero_of_isForwardSol_real hW hv hs
  have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn (fun s => 2 / v s) (uIcc 0 t) :=
    (continuousOn_const.div hv.1 fun s hs => (hv.2 s hs).1).mono hsub
  have hint : IntervalIntegrable (fun s => 2 / v s) volume 0 t := hcont.intervalIntegrable
  have hre : (∫ s in (0 : ℝ)..t, 2 / v s).re = ∫ s in (0 : ℝ)..t, 2 / (v s).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hvs : v s = ((v s).re : ℂ) := Complex.ext (by simp) (by simp [him s (hsub hs)])
    simp only [Complex.reCLM_apply]
    rw [hvs]
    norm_cast
  have h := congrArg Complex.re (hv.2 t ht).2
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h
  rw [h, hre]
  ring

/-- `fwdMap` from a real point is real while the point is alive. -/
theorem fwdMap_eq_ofReal_re' {W : ℝ → ℝ} (hW : Continuous W) {x T : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t x = ((fwdMap W t x).re : ℂ) := by
  rw [fwdMap_eq_of_isForwardSol hW hv ht]
  exact Complex.ext (by simp) (by simp [im_eq_zero_of_isForwardSol_real hW hv ht])

/-! ### Protection of the real points beyond a non-colliding mark -/

/-- `w` is continuous on `ℝ≥0` when its real-time version is continuous. -/
theorem continuous_of_continuous_toNNReal {w : ℝ≥0 → ℝ}
    (hW : Continuous fun s : ℝ => w s.toNNReal) : Continuous w := by
  have h := hW.comp NNReal.continuous_coe
  refine h.congr fun t => ?_
  simp

/-- **Protection, right side.** If a right force path `u = y + ∫ 2/(u − w)` stays strictly right of the
driver at positive times, then every real point `x > 0` with `x ≥ y` is alive (has a solution of the
centred forward flow) on every `[0, T]`. -/
theorem exists_isForwardSol_of_forceEq_right {w u : ℝ≥0 → ℝ} {y : ℝ}
    (hW : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) (hu : Continuous u)
    (hueq : ∀ t : ℝ≥0, u t = y + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal))
    (huint : ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => 2 / (u s.toNNReal - w s.toNNReal)) volume 0 t)
    (hsep : ∀ t : ℝ≥0, 0 < t → w t < u t) {x : ℝ} (hx : 0 < x) (hyx : y ≤ x) {T : ℝ}
    (hT : 0 ≤ T) : ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T v := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hwc : Continuous w := continuous_of_continuous_toNNReal hW
  have hWw : ∀ t : ℝ≥0, W t = w t := fun t => by simp [hWdef]
  by_contra hdead
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW hW0 hx hT hdead
  set τ : ℝ≥0∞ := ((σ.toNNReal : ℝ≥0) : ℝ≥0∞) with hτdef
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ↔ (t : ℝ) < σ := fun t => by
    rw [hτdef, ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt]
  -- the uncentred flow of `x`
  set p : ℝ≥0 → ℝ := fun t => (fwdMap W t x).re + w t with hpdef
  have halive : ∀ t : ℝ, 0 ≤ t → t < σ → ∃ v, IsForwardSol W (x : ℂ) t v := fun t h0 h1 =>
    hsw.2.1 t ⟨h0, h1⟩
  -- continuity of `p` before `σ`
  have hpc : ContinuousOn p {t | (t : ℝ≥0∞) < τ} := by
    intro t₀ ht₀
    have ht₀' : (t₀ : ℝ) < σ := (hlt t₀).1 ht₀
    set s₀ : ℝ := ((t₀ : ℝ) + σ) / 2 with hs₀
    have hs₀0 : 0 ≤ s₀ := by have := t₀.coe_nonneg; rw [hs₀]; linarith [hσ.1]
    have hts₀ : (t₀ : ℝ) < s₀ := by rw [hs₀]; linarith
    obtain ⟨v₀, hv₀⟩ := halive s₀ hs₀0 (by rw [hs₀]; linarith)
    have hev : ∀ᶠ r in 𝓝 t₀, p r = (v₀ r).re + w r := by
      have hopen : IsOpen {r : ℝ≥0 | (r : ℝ) < s₀} := isOpen_lt NNReal.continuous_coe continuous_const
      filter_upwards [hopen.mem_nhds hts₀] with r hr
      simp only [hpdef]
      rw [fwdMap_eq_of_isForwardSol hW hv₀ ⟨r.coe_nonneg, le_of_lt hr⟩]
    have hcv : ContinuousAt (fun r : ℝ≥0 => (v₀ r).re + w r) t₀ := by
      refine ContinuousAt.add ?_ hwc.continuousAt
      have h1 : ContinuousOn (fun r : ℝ≥0 => v₀ r) {r : ℝ≥0 | (r : ℝ) ≤ s₀} :=
        hv₀.1.comp NNReal.continuous_coe.continuousOn fun r hr => ⟨r.coe_nonneg, hr⟩
      have h2 : {r : ℝ≥0 | (r : ℝ) ≤ s₀} ∈ 𝓝 t₀ := by
        have hopen : IsOpen {r : ℝ≥0 | (r : ℝ) < s₀} :=
          isOpen_lt NNReal.continuous_coe continuous_const
        exact Filter.mem_of_superset (hopen.mem_nhds hts₀) fun r (hr : (r : ℝ) < s₀) =>
          (le_of_lt hr : (r : ℝ) ≤ s₀)
      exact Complex.continuous_re.continuousAt.comp (h1.continuousAt h2)
    exact (hcv.congr (hev.mono fun r hr => hr.symm)).continuousWithinAt
  -- the force equation of `p` before `σ`
  have hpeq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      p t = x + ∫ s in (0 : ℝ)..t, 2 / (p s.toNNReal - w s.toNNReal) := by
    intro t ht
    obtain ⟨v, hv⟩ := halive t t.coe_nonneg ((hlt t).1 ht)
    have h := re_add_eq_of_isForwardSol hW hv ⟨t.coe_nonneg, le_rfl⟩
    have hpt : p t = (v t).re + W t := by
      simp only [hpdef]
      rw [fwdMap_eq_of_isForwardSol hW hv ⟨t.coe_nonneg, le_rfl⟩, hWw]
    rw [hpt, h]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    have hr' : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr.1
    simp only [hpdef, add_sub_cancel_right]
    rw [hr', fwdMap_eq_of_isForwardSol hW hv hr]
  -- integrability of the reciprocal gap of `p` before `σ`
  have hpint : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      IntervalIntegrable (fun s : ℝ => 2 / (p s.toNNReal - w s.toNNReal)) volume 0 t := by
    intro t ht
    obtain ⟨v, hv⟩ := halive t t.coe_nonneg ((hlt t).1 ht)
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le t.coe_nonneg]
    have hre : ContinuousOn (fun r => (v r).re) (Icc 0 (t : ℝ)) :=
      Complex.continuous_re.comp_continuousOn hv.1
    have hf : ContinuousOn (fun r => (2 : ℝ) / (v r).re) (Icc 0 (t : ℝ)) :=
      continuousOn_const.div hre fun r hr =>
        (QuantumZipper.re_pos_isForwardSol_real hW t.coe_nonneg hv (by rw [hW0]; exact hx) r hr).ne'
    refine hf.congr fun r hr => ?_
    · have hr' : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr.1
      simp only [hpdef, add_sub_cancel_right]
      rw [hr', fwdMap_eq_of_isForwardSol hW hv hr]
  -- `p` stays strictly right of the driver before `σ`
  have hgap : ∀ t : ℝ≥0, (t : ℝ) < σ → w t < p t := by
    intro t ht
    obtain ⟨v, hv⟩ := halive t t.coe_nonneg ht
    have := re_fwdMap_pos hW hW0 hx hv ⟨t.coe_nonneg, le_rfl⟩
    simp only [hpdef]
    linarith
  have hcoll : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧
      w s.toNNReal = p s.toNNReal} = 0 := by
    convert measure_empty (μ := (volume : Measure ℝ))
    refine eq_empty_iff_forall_notMem.2 fun s ⟨_, hs, he⟩ => ?_
    exact (hgap s.toNNReal ((hlt _).1 hs)).ne he
  -- the mark stays left of `p` before `σ`
  have hle : ∀ t : ℝ≥0, (t : ℝ) < σ → u t ≤ p t := fun t ht =>
    Sec2.le_of_forceEq_right (τ := τ) hyx hpc hu.continuousOn (fun ht => hpeq ht)
      (fun _ => hueq _) (fun ht => hpint ht) (fun _ => huint _)
      (fun ht => (hgap _ ((hlt _).1 ht)).le) hcoll ((hlt t).2 ht)
  -- squeeze the centred mark at `σ⁻`
  set Y : ℝ → ℝ := fun s => u s.toNNReal - w s.toNNReal with hYdef
  have hYc : Continuous Y := by
    simp only [hYdef]
    exact (hu.comp continuous_real_toNNReal).sub (hwc.comp continuous_real_toNNReal)
  have hX := (Complex.continuous_re.tendsto 0).comp (tendsto_fwdMap_of_realSwallowAt hW hW0 hx hsw)
  simp only [Complex.zero_re] at hX
  have hY0 : Tendsto Y (𝓝[<] σ) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hX ?_ ?_
    · filter_upwards [Ioo_mem_nhdsLT hσ.1] with s hs
      have hpos : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
      simp only [hYdef]
      linarith [hsep _ hpos]
    · filter_upwards [Ioo_mem_nhdsLT hσ.1] with s hs
      have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1.le
      have h1 := hle s.toNNReal (by rw [hs']; exact hs.2)
      simp only [hYdef, Function.comp_apply, hpdef, hs'] at h1 ⊢
      linarith
  have hYσ : Y σ = 0 :=
    tendsto_nhds_unique (hYc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hY0
  have hpos : 0 < σ.toNNReal := Real.toNNReal_pos.2 hσ.1
  have := hsep _ hpos
  simp only [hYdef] at hYσ
  linarith

/-- **Protection, left side** (reflection of `exists_isForwardSol_of_forceEq_right`): if a left force path
`u = y + ∫ 2/(u − w)` stays strictly left of the driver at positive times, every real point `x < 0` with
`x ≤ y` is alive on every `[0, T]`. -/
theorem exists_isForwardSol_of_forceEq_left {w u : ℝ≥0 → ℝ} {y : ℝ}
    (hW : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) (hu : Continuous u)
    (hueq : ∀ t : ℝ≥0, u t = y + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal))
    (huint : ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => 2 / (u s.toNNReal - w s.toNNReal)) volume 0 t)
    (hsep : ∀ t : ℝ≥0, 0 < t → u t < w t) {x : ℝ} (hx : x < 0) (hxy : x ≤ y) {T : ℝ}
    (hT : 0 ≤ T) : ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) T v := by
  have hfun : ∀ s : ℝ, (2 : ℝ) / (-u s.toNNReal - -w s.toNNReal) =
      -(2 / (u s.toNNReal - w s.toNNReal)) := fun s => by
    rw [neg_sub_neg, ← neg_sub (u s.toNNReal) (w s.toNNReal), div_neg]
  have h := exists_isForwardSol_of_forceEq_right (w := fun t => -w t) (u := fun t => -u t)
    (y := -y) hW.neg (by simp [hw0]) hu.neg (fun t => ?_) (fun t => ?_)
    (fun t ht => neg_lt_neg (hsep t ht)) (x := -x) (by linarith) (by linarith) hT
  · exact exists_isForwardSol_neg_iff.1 h
  · show -u t = -y + ∫ s in (0 : ℝ)..t, 2 / (-u s.toNNReal - -w s.toNNReal)
    simp_rw [hfun]
    rw [intervalIntegral.integral_neg, hueq t]
    ring
  · show IntervalIntegrable (fun s : ℝ => 2 / (-u s.toNNReal - -w s.toNNReal)) volume 0 t
    simp_rw [hfun]
    exact (huint t).neg

/-! ### The trace never visits a protected real set -/

/-- The filling of a closed set depends only on its trace on `ℍ`. -/
theorem fillH_congr {A B : Set ℂ} (hA : IsClosed A) (hB : IsClosed B) (h : A ∩ H = B ∩ H) :
    fillH A = fillH B := by
  have hiff : ∀ z, z ∈ H → (z ∈ A ↔ z ∈ B) := fun z hz =>
    ⟨fun ha => ((Set.ext_iff.1 h z).1 ⟨ha, hz⟩).1, fun hb => ((Set.ext_iff.1 h z).2 ⟨hb, hz⟩).1⟩
  have hd : H \ A = H \ B := by
    ext z
    constructor
    · rintro ⟨hz, hzA⟩
      exact ⟨hz, fun hzB => hzA ((hiff z hz).2 hzB)⟩
    · rintro ⟨hz, hzB⟩
      exact ⟨hz, fun hzA => hzB ((hiff z hz).1 hzA)⟩
  unfold fillH
  rw [hA.closure_eq, hB.closure_eq, hd]
  ext z
  constructor
  · rintro ⟨hz, hzA | hb⟩
    · exact ⟨hz, Or.inl ((hiff z hz).1 hzA)⟩
    · exact ⟨hz, Or.inr hb⟩
  · rintro ⟨hz, hzB | hb⟩
    · exact ⟨hz, Or.inl ((hiff z hz).2 hzB)⟩
    · exact ⟨hz, Or.inr hb⟩

/-- **The trace never visits a protected real set.** Let `η` be a continuous generating trace of the
Loewner chain driven by `w` on `[0, ∞)`. If `C ⊆ ℝ` is closed, `0 ∉ C`, and every point of `C` is alive
(never swallowed: the centred forward flow from it has a solution on every `[0, T]`), then `η` never takes
a value in `C`. -/
theorem ne_ofReal_of_isGeneratingTrace {w : ℝ≥0 → ℝ} (hW : Continuous fun s : ℝ => w s.toNNReal)
    (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) {C : Set ℝ} (hC : IsClosed C)
    (h0 : (0 : ℝ) ∉ C)
    (halive : ∀ y ∈ C, ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) T v) :
    ∀ t : ℝ≥0, ∀ y ∈ C, η t ≠ y := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  obtain ⟨hη0, hηc, hfill⟩ := hη
  have hηcont : Continuous η := by
    rw [← continuousOn_univ]
    refine hηc.mono fun t _ => ?_
    show (t : ℝ≥0∞) ≤ ⊤
    exact le_top
  intro t₀ y₀ hy₀ hηt₀
  set S : Set ℝ≥0 := η ⁻¹' (((↑) : ℝ → ℂ) '' C) with hSdef
  have hCc : IsClosed (((↑) : ℝ → ℂ) '' C) :=
    Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ hC
  have hSc : IsClosed S := hCc.preimage hηcont
  have hSne : S.Nonempty := ⟨t₀, y₀, hy₀, hηt₀.symm⟩
  set s₀ : ℝ≥0 := sInf S with hs₀def
  have hs₀S : s₀ ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  obtain ⟨y, hyC, hy⟩ := hs₀S
  have hs₀pos : 0 < s₀ := by
    rcases eq_zero_or_pos s₀ with h | h
    · exfalso
      rw [h, hη0] at hy
      have hy' : y = 0 := by exact_mod_cast hy
      exact h0 (hy' ▸ hyC)
    · exact h
  obtain ⟨v, hv⟩ := halive y hyC s₀ s₀.coe_nonneg
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol s₀.coe_nonneg hv
  set E : ℝ := Real.exp (2 / δ ^ 2 * s₀) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hnot : ∀ z : ℂ, 0 < z.im → ‖z - y‖ < δ / E → z ∉ fwdHull W s₀ := fun z hz hzy =>
    not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hz (by rwa [lt_div_iff₀ hE] at hzy)
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.1 hηcont.continuousAt (δ / E) (div_pos hδ hE)
  have hcompact : ∀ s : ℝ≥0, IsCompact (η '' Icc 0 s) := fun s =>
    isCompact_Icc.image hηcont
  have hK : ∀ s : ℝ≥0, fwdHull W s = fillH (η '' Icc 0 s) := fun s => by
    have h := hfill s ENNReal.coe_lt_top
    rw [isFilling_iff_inter_H_eq_fillH (hcompact s).isBounded (hcompact s).isClosed,
      inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := W)).2 _)] at h
    exact h
  -- trace points just before `s₀` are not in `ℍ`
  have hnotH : ∀ s : ℝ≥0, s < s₀ → dist s s₀ < ε → ¬ 0 < (η s).im := by
    intro s hs hd hpos
    have hmem : η s ∈ fwdHull W s₀ := by
      rw [hK]
      exact ⟨hpos, Or.inl (subset_closure ⟨s, ⟨zero_le, hs.le⟩, rfl⟩)⟩
    refine hnot (η s) hpos ?_ hmem
    have := hball hd
    rwa [dist_eq_norm, ← hy] at this
  set s₁ : ℝ≥0 := Real.toNNReal ((s₀ : ℝ) - ε / 2) with hs₁def
  have hs₁' : (s₁ : ℝ) = max ((s₀ : ℝ) - ε / 2) 0 := Real.coe_toNNReal' _
  have hs₁ : s₁ < s₀ := by
    rw [← NNReal.coe_lt_coe, hs₁']
    exact max_lt (by linarith) (NNReal.coe_pos.2 hs₀pos)
  have hdist : ∀ s : ℝ≥0, s₁ < s → s < s₀ → dist s s₀ < ε := by
    intro s h1 h2
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 (NNReal.coe_lt_coe.2 h2))]
    have h1' : (s₁ : ℝ) < s := NNReal.coe_lt_coe.2 h1
    have : (s₀ : ℝ) - ε / 2 ≤ s₁ := by rw [hs₁']; exact le_max_left _ _
    linarith
  have hAH : η '' Icc 0 s₀ ∩ H = η '' Icc 0 s₁ ∩ H := by
    ext z
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hz⟩
      refine ⟨⟨s, ⟨hs.1, ?_⟩, rfl⟩, hz⟩
      by_contra hlt
      have hlt' : s₁ < s := lt_of_not_ge hlt
      rcases hs.2.lt_or_eq with h | h
      · exact hnotH s h (hdist s hlt' h) hz
      · have hz' : (0 : ℝ) < (η s).im := hz
        rw [h, ← hy, Complex.ofReal_im] at hz'
        exact lt_irrefl _ hz'
    · rintro ⟨⟨s, hs, rfl⟩, hz⟩
      exact ⟨⟨s, ⟨hs.1, hs.2.trans hs₁.le⟩, rfl⟩, hz⟩
  have heq : fwdHull W s₀ = fwdHull W s₁ := by
    rw [hK, hK]
    exact fillH_congr (hcompact _).isClosed (hcompact _).isClosed hAH
  have hss := QuantumZipper.RS.fwdHull_ssubset hW hW0 s₁.coe_nonneg (NNReal.coe_lt_coe.2 hs₁)
  rw [heq] at hss
  exact hss.ne rfl

/-- **A generating trace enters `ℍ` in every time interval**: otherwise `η([0, s₂]) ∩ ℍ = η([0, s₁]) ∩ ℍ`, so the
hulls `K_{s₁}`, `K_{s₂}` (fillings of these ranges) coincide, contradicting their strict growth. -/
theorem exists_im_pos_of_isGeneratingTrace {w : ℝ≥0 → ℝ}
    (hW : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {s₁ s₂ : ℝ≥0} (h12 : s₁ < s₂) :
    ∃ s, s₁ < s ∧ s ≤ s₂ ∧ 0 < (η s).im := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  obtain ⟨-, hηc, hfill⟩ := hη
  have hηcont : Continuous η := by
    rw [← continuousOn_univ]
    refine hηc.mono fun t _ => ?_
    show (t : ℝ≥0∞) ≤ ⊤
    exact le_top
  by_contra hno
  push Not at hno
  have hcompact : ∀ s : ℝ≥0, IsCompact (η '' Icc 0 s) := fun s =>
    isCompact_Icc.image hηcont
  have hK : ∀ s : ℝ≥0, fwdHull W s = fillH (η '' Icc 0 s) := fun s => by
    have h := hfill s ENNReal.coe_lt_top
    rw [isFilling_iff_inter_H_eq_fillH (hcompact s).isBounded (hcompact s).isClosed,
      inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := W)).2 _)] at h
    exact h
  have hAH : η '' Icc 0 s₂ ∩ H = η '' Icc 0 s₁ ∩ H := by
    ext z
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hz⟩
      refine ⟨⟨s, ⟨hs.1, ?_⟩, rfl⟩, hz⟩
      by_contra hlt
      have hz' : (0 : ℝ) < (η s).im := hz
      exact absurd (hno s (lt_of_not_ge hlt) hs.2) (not_le.2 hz')
    · rintro ⟨⟨s, hs, rfl⟩, hz⟩
      exact ⟨⟨s, ⟨hs.1, hs.2.trans h12.le⟩, rfl⟩, hz⟩
  have heq : fwdHull W s₂ = fwdHull W s₁ := by
    rw [hK, hK]
    exact fillH_congr (hcompact _).isClosed (hcompact _).isClosed hAH
  have hss := QuantumZipper.RS.fwdHull_ssubset hW hW0 s₁.coe_nonneg (NNReal.coe_lt_coe.2 h12)
  rw [heq] at hss
  exact hss.ne rfl

/-- **A generating trace stays in the closed upper half-plane.** -/
theorem im_nonneg_of_isGeneratingTrace {w : ℝ≥0 → ℝ}
    (hW : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (t : ℝ≥0) : 0 ≤ (η t).im := by
  by_contra hneg
  rw [not_le] at hneg
  have hηcont : Continuous η := by
    rw [← continuousOn_univ]
    refine hη.2.1.mono fun t _ => ?_
    show (t : ℝ≥0∞) ≤ ⊤
    exact le_top
  have hopen : IsOpen {s : ℝ≥0 | (η s).im < 0} :=
    isOpen_lt (Complex.continuous_im.comp hηcont) continuous_const
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen t hneg
  have ht0 : 0 < t := by
    rcases eq_zero_or_pos t with h | h
    · rw [h, hη.1, Complex.zero_im] at hneg
      exact absurd hneg (lt_irrefl 0)
    · exact h
  set s₁ : ℝ≥0 := Real.toNNReal ((t : ℝ) - ε / 2) with hs₁def
  have hs₁' : (s₁ : ℝ) = max ((t : ℝ) - ε / 2) 0 := Real.coe_toNNReal' _
  have hs₁ : s₁ < t := by
    rw [← NNReal.coe_lt_coe, hs₁']
    exact max_lt (by linarith) (NNReal.coe_pos.2 ht0)
  obtain ⟨s, hs1, hs2, hpos⟩ := exists_im_pos_of_isGeneratingTrace hW hw0 hη hs₁
  have hmem : s ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2
      (NNReal.coe_le_coe.2 hs2))]
    have h1' : (s₁ : ℝ) < s := NNReal.coe_lt_coe.2 hs1
    have : (t : ℝ) - ε / 2 ≤ s₁ := by rw [hs₁']; exact le_max_left _ _
    linarith
  exact absurd (hball hmem) (not_lt.2 hpos.le)

end Sec4

end InteractingSLE
