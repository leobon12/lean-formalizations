/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Dimension.ForceGaps
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import QuantumZipper.Proofs.RS.RealAlive

/-!
# Aux. lemma 25: the real chart (deterministic Loewner facts)

Packet PROVE-AUX25. Specification, proof of Aux. lemma 25 (`source/spec/p097-144.md`, pp. 125–127). The proof
uses "the geometric force-endpoint identities": every force coordinate lies outside the boundary interval
`(L_q, R_q)` of the hull at time `q`, and a real contact of the trace is at the physical position of the
colliding force coordinate. Here these identities are replaced by comparisons for the centred real Loewner
equation `u(s₂) − u(s₁) = −(W(s₂) − W(s₁)) + ∫ 2/u` (the equation of a centred force coordinate `V − W`),
in the style of `Spec/Dimension/ForceGaps.lean`, so that no extreme prime end has to be identified.

* `le_sub_of_backward_cut`: a backward solution from above a force coordinate stays above it by at least
  the initial margin;
* `exists_isForwardSol_of_gt`: every real point to the right of a right force coordinate at time `t` is the
  image of a real point alive on `[0, t]`, which lies to the right of the coordinate's start;
* `IsLoewnerTraceLT.exists_tip_real_of_collision_right` (**the tip at a collision**): if a right force coordinate meets the driver
  at time `t`, the tip `η(t)` is a real point `x ≥ û(0)`, and every real point `> x` is alive on `[0, t]`;
* `IsLoewnerTraceLT.not_mem_image_of_isForwardSol`: a real point alive on `[0, q]` is not on `η([0, q])`;
* left-side versions by the reflection `(u, W) ↦ (−u, −W)` of the real equation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace Aux25

/-! ### Backward comparison -/

/-- **Backward comparison.** Let `û ≥ 0` solve the centred real Loewner equation on `[0, t]` (integrable
reciprocal, null zero set) and let `Y` solve the equation with the drift cut below at `δ` with
`Y(t) = û(t) + c`, `c > 0`. Then `Y − û ≥ c` on `[0, t]`. -/
theorem le_sub_of_backward_cut {W : ℝ → ℝ} {t : ℝ} {u Y : ℝ → ℝ} {c δ : ℝ}
    (hc : 0 < c) (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0)
    (hδ : 0 < δ) (hYc : ContinuousOn Y (Icc 0 t)) (hYt : Y t = u t + c)
    (hYeq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, Bessel.regDrift 2 δ (Y s)) :
    ∀ s ∈ Icc (0 : ℝ) t, c ≤ Y s - u s := by
  intro s₀ hs₀
  have hsub0 : Icc s₀ t ⊆ Icc 0 t := Icc_subset_Icc_left hs₀.1
  have hreg : Continuous (Bessel.regDrift 2 δ) :=
    (Bessel.lipschitzWith_regDrift (by norm_num) hδ).continuous
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) t → u s ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with s hs h1 h2
    exact hs ⟨h1, h2⟩
  have key := le_max_of_antitone_of_pos (f := fun s => Y s - u s) hs₀.2
    ((hYc.mono hsub0).sub (huc.mono hsub0)) ?_
  · simp only [hYt, add_sub_cancel_left] at key
    rcases le_total (Y s₀ - u s₀) 0 with h | h
    · rw [max_eq_right h] at key; linarith
    · rw [max_eq_left h] at key; exact key
  intro s₁ s₂ h1 h12 h2 hpos
  have hs₁ : s₁ ∈ Icc (0 : ℝ) t := ⟨hs₀.1.trans h1, h12.trans h2⟩
  have hs₂ : s₂ ∈ Icc (0 : ℝ) t := ⟨hs₀.1.trans (h1.trans h12), h2⟩
  have hI : Icc s₁ s₂ ⊆ Icc 0 t := Icc_subset_Icc hs₁.1 h2
  have hint1 : IntervalIntegrable (fun s => Bessel.regDrift 2 δ (Y s)) volume s₁ s₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h12]
    exact hreg.comp_continuousOn (hYc.mono hI)
  have ht0 : (0 : ℝ) ≤ t := hs₀.1.trans hs₀.2
  have hint2 : IntervalIntegrable (fun s => 2 / u s) volume s₁ s₂ :=
    huint.mono_set (by rw [uIcc_of_le h12, uIcc_of_le ht0]; exact hI)
  have hdiff : (Y s₂ - u s₂) - (Y s₁ - u s₁) =
      ∫ s in s₁..s₂, (Bessel.regDrift 2 δ (Y s) - 2 / u s) := by
    rw [intervalIntegral.integral_sub hint1 hint2]
    have e1 := hYeq s₁ hs₁ s₂ hs₂ h12
    have e2 := hueq s₁ hs₁ s₂ hs₂ h12
    linarith
  have hnn : 0 ≤ ∫ s in s₁..s₂, (2 / u s - Bessel.regDrift 2 δ (Y s)) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict h12 ?_
    have hmem : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), s ∈ Icc s₁ s₂ :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem, ae_restrict_of_ae hae] with s hs hsu
    have hu' : 0 < u s := lt_of_le_of_ne (hu0 s (hI hs)) (Ne.symm (hsu (hI hs)))
    have hYu : u s < Y s := by
      have := hpos s hs
      linarith
    have hYpos : 0 < Y s := hu'.trans hYu
    have h1 : Bessel.regDrift 2 δ (Y s) ≤ 2 / Y s := by
      show 2 / max (Y s) δ ≤ 2 / Y s
      exact div_le_div_of_nonneg_left (by norm_num) hYpos (le_max_left _ _)
    have h2 : 2 / Y s ≤ 2 / u s := div_le_div_of_nonneg_left (by norm_num) hu' hYu.le
    show (0 : ℝ) ≤ 2 / u s - Bessel.regDrift 2 δ (Y s)
    linarith
  rw [intervalIntegral.integral_sub hint2 hint1] at hnn
  rw [intervalIntegral.integral_sub hint1 hint2] at hdiff
  show Y s₂ - u s₂ ≤ Y s₁ - u s₁
  linarith

/-- **Real points to the right of a force coordinate are alive.** Let `û ≥ 0` solve the centred real
Loewner equation on `[0, t]` (integrable reciprocal, null zero set). For every real `y > û(t)` there is a
real forward solution `Y` on `[0, t]` from the real point `Y(0)` with `Y(t) = y`, and `Y − û ≥ y − û(t)`
on `[0, t]`. -/
theorem exists_isForwardSol_of_gt {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) {y : ℝ} (hy : u t < y) :
    ∃ Y : ℝ → ℝ, IsForwardSol W (Y 0 : ℂ) t (fun s => (Y s : ℂ)) ∧ Y t = y ∧
      ∀ s ∈ Icc (0 : ℝ) t, y - u t ≤ Y s - u s := by
  set c := y - u t with hcdef
  have hc : 0 < c := sub_pos.2 hy
  have hδ : 0 < c / 2 := by positivity
  obtain ⟨Y, hYc, hYt, hYeq⟩ := exists_backward_cut hW ht y hδ
  have hge := le_sub_of_backward_cut hc huc hu0 hueq huint hnull hδ hYc
    (by rw [hYt, hcdef]; ring) hYeq
  have hYpos : ∀ s ∈ Icc (0 : ℝ) t, c ≤ Y s := fun s hs => by
    have := hge s hs; have := hu0 s hs; linarith
  refine ⟨Y, ?_, hYt, hge⟩
  refine isForwardSol_ofReal hW0 hYc (fun s hs => (hc.trans_le (hYpos s hs)).ne') fun s hs => ?_
  rw [hYeq 0 ⟨le_rfl, ht⟩ s hs hs.1]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  exact Bessel.regDrift_of_le (by linarith [hYpos r ⟨hr.1, hr.2.trans hs.2⟩])

/-! ### Reflection -/

/-- A left alive real point moves alive points further left: if `q < W 0` is alive on `[0, T]` and
`y < q`, then `y` is alive on `[0, T]` (reflection of `QuantumZipper.RS.exists_isForwardSol_of_lt`). -/
theorem exists_isForwardSol_of_lt_left {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {q y : ℝ} (hq : q < W 0) (hyq : y < q) {u : ℝ → ℂ} (hu : IsForwardSol W (q : ℂ) T u) :
    ∃ v, IsForwardSol W (y : ℂ) T v := by
  have hu' := QuantumZipper.RS.isForwardSol_neg hu
  have h1 : (-(q : ℂ)) = ((-q : ℝ) : ℂ) := by push_cast; ring
  rw [h1] at hu'
  obtain ⟨v, hv⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt (W := fun t => -W t) hW.neg hT
    (show -W 0 < -q by linarith) (show -q < -y by linarith) hu'
  have hv' := QuantumZipper.RS.isForwardSol_neg hv
  simp only [neg_neg] at hv'
  have h2 : (-((-y : ℝ) : ℂ)) = (y : ℂ) := by push_cast; ring
  rw [h2] at hv'
  exact ⟨_, hv'⟩

/-- The left version of `exists_isForwardSol_of_gt`: for `û ≤ 0` and `y < û(t)`, a real forward solution
`Y` on `[0, t]` with `Y(t) = y` and `Y − û ≤ y − û(t)`. -/
theorem exists_isForwardSol_of_lt' {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, u s ≤ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) {y : ℝ} (hy : y < u t) :
    ∃ Y : ℝ → ℝ, IsForwardSol W (Y 0 : ℂ) t (fun s => (Y s : ℂ)) ∧ Y t = y ∧
      ∀ s ∈ Icc (0 : ℝ) t, Y s - u s ≤ y - u t := by
  have hu'eq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      -u s₂ - -u s₁ = -(-W s₂ - -W s₁) + ∫ s in s₁..s₂, 2 / -u s := by
    intro s₁ hs₁ s₂ hs₂ h12
    have h := hueq s₁ hs₁ s₂ hs₂ h12
    have e : ∫ s in s₁..s₂, 2 / -u s = -∫ s in s₁..s₂, 2 / u s := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext s
      rw [div_neg]
    rw [e]
    linarith
  have hu'int : IntervalIntegrable (fun s => 2 / -u s) volume 0 t := by
    have e : (fun s => 2 / -u s) = -(fun s => 2 / u s) := by
      funext s
      simp [div_neg]
    rw [e]
    exact huint.neg
  have hnull' : volume {s | s ∈ Icc (0 : ℝ) t ∧ -u s = 0} = 0 := by
    simpa only [neg_eq_zero] using hnull
  obtain ⟨Y, hYsol, hYt, hYge⟩ := exists_isForwardSol_of_gt (W := fun s => -W s)
    (u := fun s => -u s) hW.neg (by rw [hW0, neg_zero]) ht huc.neg
    (fun s hs => neg_nonneg.2 (hu0 s hs)) hu'eq hu'int hnull' (y := -y) (by linarith)
  have hv := QuantumZipper.RS.isForwardSol_neg hYsol
  simp only [neg_neg] at hv
  refine ⟨fun s => -Y s, ?_, by simp [hYt], fun s hs => ?_⟩
  swap
  · have := hYge s hs
    show -Y s - u s ≤ y - u t
    linarith
  convert hv using 1
  · push_cast; ring
  · funext s; push_cast; ring

/-! ### The tip at a force collision -/

section Tip

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- The boundary values `F̄_t(c_n)` along a real sequence `c_n → 0` converge to the tip `η(t)`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.tendsto_extendFrom_realSeq (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => extendFrom H (fwdMapInv W t) (c n : ℂ)) atTop (𝓝 (η t)) := by
  have hcont := (hη.hasBdryLimits hW hW0 ht htT).continuousOn
  have h0 : (0 : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hseq : Tendsto (fun n => (c n : ℂ)) atTop (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => mem_Hbar_of_im_eq_zero ?_⟩
    · have h := (continuous_ofReal.tendsto 0).comp hc
      rw [Complex.ofReal_zero] at h
      exact h
    · simp
  rw [← hη.extendFrom_zero hW hW0 ht htT]
  exact (hcont 0 h0).tendsto.comp hseq

/-- **The tip at a right force collision.** Let `û ≥ 0` solve the centred real Loewner equation on
`[0, t]` (integrable reciprocal, null zero set) with `û(t) = 0`. Then the tip `η(t)` is a real point
`x ≥ û(0)`, and every real `y > x` is alive on `[0, t]`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.exists_tip_real_of_collision_right (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {u : ℝ → ℝ}
    (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) (hut : u t = 0) :
    ∃ x : ℝ, η t = x ∧ u 0 ≤ x ∧ ∀ y : ℝ, x < y → ∃ v, IsForwardSol W (y : ℂ) t v := by
  have hcpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hsol : ∀ n : ℕ, ∃ Y : ℝ → ℝ, IsForwardSol W (Y 0 : ℂ) t (fun s => (Y s : ℂ)) ∧
      Y t = 1 / ((n : ℝ) + 1) ∧ ∀ s ∈ Icc (0 : ℝ) t, 1 / ((n : ℝ) + 1) - u t ≤ Y s - u s :=
    fun n => exists_isForwardSol_of_gt hW hW0 ht huc hu0 hueq huint hnull (by rw [hut]; exact hcpos n)
  choose Y hY using hsol
  set x : ℕ → ℝ := fun n => Y n 0 with hxdef
  have hF : ∀ n : ℕ, extendFrom H (fwdMapInv W t) ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) = (x n : ℂ) :=
      fun n => by
    have h := hη.extendFrom_eq_of_isForwardSol hW hW0 ht htT (hY n).1
    rwa [(hY n).2.1] at h
  have hx0 : ∀ n : ℕ, u 0 + 1 / ((n : ℝ) + 1) ≤ x n := fun n => by
    have h := (hY n).2.2 0 ⟨le_rfl, ht⟩
    rw [hut, sub_zero] at h
    simp only [hxdef]
    linarith
  have hlim : Tendsto (fun n => (x n : ℂ)) atTop (𝓝 (η t)) := by
    have h := hη.tendsto_extendFrom_realSeq hW hW0 ht htT tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [hF] using h
  have him : (η t).im = 0 := by
    have h := (Complex.continuous_im.tendsto _).comp hlim
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hre : Tendsto x atTop (𝓝 (η t).re) := by
    have h := (Complex.continuous_re.tendsto _).comp hlim
    simpa only [Function.comp_def, Complex.ofReal_re] using h
  refine ⟨(η t).re, Complex.ext (by simp) (by simp [him]), ?_, fun y hy => ?_⟩
  · refine ge_of_tendsto hre (Eventually.of_forall fun n => ?_)
    have := hx0 n; have := hcpos n; linarith
  · obtain ⟨n, hn⟩ := (hre.eventually (gt_mem_nhds hy)).exists
    have hxpos : W 0 < x n := by
      rw [hW0]; have := hx0 n; have := hcpos n; have := hu0 0 ⟨le_rfl, ht⟩; linarith
    exact QuantumZipper.RS.exists_isForwardSol_of_lt hW ht hxpos hn (hY n).1

/-- **The tip at a left force collision** (reflected `exists_tip_real_of_collision_right`): for `û ≤ 0` with `û(t) = 0`, the
tip is a real point `x ≤ û(0)` and every real `y < x` is alive on `[0, t]`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.exists_tip_real_of_collision_left (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {u : ℝ → ℝ}
    (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, u s ≤ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) (hut : u t = 0) :
    ∃ x : ℝ, η t = x ∧ x ≤ u 0 ∧ ∀ y : ℝ, y < x → ∃ v, IsForwardSol W (y : ℂ) t v := by
  have hcpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hsol : ∀ n : ℕ, ∃ Y : ℝ → ℝ, IsForwardSol W (Y 0 : ℂ) t (fun s => (Y s : ℂ)) ∧
      Y t = -(1 / ((n : ℝ) + 1)) ∧ ∀ s ∈ Icc (0 : ℝ) t, Y s - u s ≤ -(1 / ((n : ℝ) + 1)) - u t :=
    fun n => exists_isForwardSol_of_lt' hW hW0 ht huc hu0 hueq huint hnull
      (by rw [hut]; have := hcpos n; linarith)
  choose Y hY using hsol
  set x : ℕ → ℝ := fun n => Y n 0 with hxdef
  have hF : ∀ n : ℕ, extendFrom H (fwdMapInv W t) ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ) = (x n : ℂ) :=
    fun n => by
      have h := hη.extendFrom_eq_of_isForwardSol hW hW0 ht htT (hY n).1
      rwa [(hY n).2.1] at h
  have hx0 : ∀ n : ℕ, x n ≤ u 0 - 1 / ((n : ℝ) + 1) := fun n => by
    have h := (hY n).2.2 0 ⟨le_rfl, ht⟩
    rw [hut, sub_zero] at h
    simp only [hxdef]
    linarith
  have hneg : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    simpa only [neg_zero] using h
  have hlim : Tendsto (fun n => (x n : ℂ)) atTop (𝓝 (η t)) := by
    have h := hη.tendsto_extendFrom_realSeq hW hW0 ht htT hneg
    simpa only [hF] using h
  have him : (η t).im = 0 := by
    have h := (Complex.continuous_im.tendsto _).comp hlim
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hre : Tendsto x atTop (𝓝 (η t).re) := by
    have h := (Complex.continuous_re.tendsto _).comp hlim
    simpa only [Function.comp_def, Complex.ofReal_re] using h
  refine ⟨(η t).re, Complex.ext (by simp) (by simp [him]), ?_, fun y hy => ?_⟩
  · refine le_of_tendsto hre (Eventually.of_forall fun n => ?_)
    have := hx0 n; have := hcpos n; linarith
  · obtain ⟨n, hn⟩ := (hre.eventually (lt_mem_nhds hy)).exists
    have hxneg : x n < W 0 := by
      rw [hW0]; have := hx0 n; have := hcpos n; have := hu0 0 ⟨le_rfl, ht⟩; linarith
    exact exists_isForwardSol_of_lt_left hW ht hxneg hn (hY n).1

end Tip

/-! ### Alive real points are not on the prefix -/

section Prefix

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- **An alive real point is not on the trace prefix.** If the real point `x` is alive on `[0, q]`
(a forward solution exists), then `x ∉ η([0, q])`. Near `x` no point of `ℍ` is swallowed by time `q`
(`not_mem_fwdHull_of_isForwardSol`), while `η([0, q]) ∩ ℍ ⊆ K_q`; so `η` would be real on an interval of
times ending at a visit of `x`, contradicting strict growth (`IsLoewnerTraceLT.exists_mem_diff`). -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.ofReal_not_mem_image_of_isForwardSol
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hqT : q < T) {x : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) q v) :
    (x : ℂ) ∉ η '' Icc 0 q := by
  rintro ⟨s, hs, hηs⟩
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hq hv
  set E := Real.exp (2 / δ ^ 2 * q) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hball : ∀ z : ℂ, 0 < z.im → ‖z - (x : ℂ)‖ < δ / E → z ∉ fwdHull W q := by
    intro z hz hzx
    refine not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hz ?_
    calc ‖z - (x : ℂ)‖ * E < δ / E * E := mul_lt_mul_of_pos_right hzx hE
      _ = δ := div_mul_cancel₀ _ hE.ne'
  have hs0 : 0 < s := by
    rcases hs.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hη.1] at hηs
      have hv0 := QuantumZipper.FwdHolo.sol_zero hv hq
      have hne := (hv.2 0 ⟨le_rfl, hq⟩).1
      rw [hv0, hW0, ← hηs] at hne
      simp at hne
  have hηc : ContinuousWithinAt η (Icc 0 q) s :=
    (hη.2.1.mono fun r hr => ⟨hr.1, hr.2.trans_lt hqT⟩) s hs
  obtain ⟨ε, hε, hεball⟩ := Metric.continuousWithinAt_iff.1 hηc (δ / E) (by positivity)
  set t₁ := max (s - ε / 2) 0 with ht₁def
  have ht₁ : 0 ≤ t₁ := le_max_right _ _
  have ht₁s : t₁ < s := max_lt (by linarith) hs0
  obtain ⟨r, hr, hrK⟩ := hη.exists_mem_diff hW hW0 ht₁ ht₁s (hs.2.trans_lt hqT)
  have hrI : r ∈ Icc 0 q := ⟨ht₁.trans hr.1.le, hr.2.trans hs.2⟩
  have hrs : dist r s < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [le_max_left (s - ε / 2) 0, hr.1]
    · linarith [hr.2]
  have hd := hεball hrI hrs
  have hrH : η r ∈ H := by
    have h1 := hrK.1
    rw [hη.2.2 s hs.1 (hs.2.trans_lt hqT)] at h1
    exact fillH_subset_H _ h1
  have hrKq : η r ∈ fwdHull W q := by
    rw [hη.2.2 q hq hqT]
    exact ⟨hrH, Or.inl (subset_closure ⟨r, hrI, rfl⟩)⟩
  refine hball (η r) hrH ?_ hrKq
  rw [← hηs, ← dist_eq_norm]
  exact hd

/-- The boundary value of `F̄_q` at a point of `ℍ` is not on the prefix `η([0, q])`: it lies in `ℍ \ K_q`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.extendFrom_not_mem_image_of_mem_H
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hqT : q < T) {y : ℂ} (hy : y ∈ H) : extendFrom H (fwdMapInv W q) y ∉ η '' Icc 0 q := by
  obtain ⟨F, hFeq, hFc, -⟩ := hη.exists_extension hW hW0 hq hqT
  have hyb : y ∈ Hbar := QuantumZipper.H_subset_Hbar hy
  have h1 : Tendsto (fwdMapInv W q) (𝓝[H] y) (𝓝 (F y)) :=
    ((hFc y hyb).mono QuantumZipper.H_subset_Hbar).congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)
  rw [extendFrom_eq (by rw [closure_H]; exact hyb) h1, hFeq hy]
  have hmem := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hq hy
  rintro ⟨s, hs, hηs⟩
  refine hmem.2 ?_
  rw [hη.2.2 q hq hqT, ← hηs]
  refine ⟨?_, Or.inl (subset_closure ⟨s, hs, rfl⟩)⟩
  rw [hηs]
  exact hmem.1

/-- **Real points to the right of a right force coordinate at time `q` are not on the prefix**:
`F̄_q(y) ∉ η([0, q])` for real `y > û(q)`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.extendFrom_not_mem_image_of_gt
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hqT : q < T) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 q)) (hu0 : ∀ s ∈ Icc 0 q, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) q, ∀ s₂ ∈ Icc (0 : ℝ) q, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 q)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) q ∧ u s = 0} = 0) {y : ℝ} (hy : u q < y) :
    extendFrom H (fwdMapInv W q) (y : ℂ) ∉ η '' Icc 0 q := by
  obtain ⟨Y, hYsol, hYq, -⟩ := exists_isForwardSol_of_gt hW hW0 hq huc hu0 hueq huint hnull hy
  have h := hη.extendFrom_eq_of_isForwardSol hW hW0 hq hqT hYsol
  rw [hYq] at h
  rw [h]
  exact hη.ofReal_not_mem_image_of_isForwardSol hW hW0 hq hqT hYsol

/-- The left version: `F̄_q(y) ∉ η([0, q])` for real `y < û(q)`, `û ≤ 0` a left force coordinate. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.extendFrom_not_mem_image_of_lt
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hqT : q < T) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 q)) (hu0 : ∀ s ∈ Icc 0 q, u s ≤ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) q, ∀ s₂ ∈ Icc (0 : ℝ) q, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 q)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) q ∧ u s = 0} = 0) {y : ℝ} (hy : y < u q) :
    extendFrom H (fwdMapInv W q) (y : ℂ) ∉ η '' Icc 0 q := by
  obtain ⟨Y, hYsol, hYq, -⟩ := exists_isForwardSol_of_lt' hW hW0 hq huc hu0 hueq huint hnull hy
  have h := hη.extendFrom_eq_of_isForwardSol hW hW0 hq hqT hYsol
  rw [hYq] at h
  rw [h]
  exact hη.ofReal_not_mem_image_of_isForwardSol hW hW0 hq hqT hYsol

/-- A force coordinate that has not met the driver by time `q` (`û ≠ 0` on `[0, q]`) is itself a real
forward solution, so `F̄_q(û(q)) = û(0)` is not on the prefix. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.extendFrom_not_mem_image_of_ne_zero
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hqT : q < T) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 q)) (hune : ∀ s ∈ Icc 0 q, u s ≠ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) q, ∀ s₂ ∈ Icc (0 : ℝ) q, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s) :
    extendFrom H (fwdMapInv W q) (u q : ℂ) ∉ η '' Icc 0 q := by
  have hsol : IsForwardSol W (u 0 : ℂ) q (fun s => (u s : ℂ)) :=
    isForwardSol_ofReal hW0 huc hune fun s hs => hueq 0 ⟨le_rfl, hq⟩ s hs hs.1
  rw [hη.extendFrom_eq_of_isForwardSol hW hW0 hq hqT hsol]
  exact hη.ofReal_not_mem_image_of_isForwardSol hW hW0 hq hqT hsol

end Prefix

/-! ### Shifting a force coordinate to the chart at time `q` -/

section Shift

open QuantumZipper.RS (shiftDrive)

/-- A centred force coordinate on `[0, t]` restricts to one of the shifted driver `W(q + ·) − W(q)` on
`[0, t − q]`. -/
theorem centredEq_shift {W : ℝ → ℝ} {q t : ℝ} (hq : 0 ≤ q) (hqt : q ≤ t) {u : ℝ → ℝ}
    (huc : ContinuousOn u (Icc 0 t))
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) :
    ContinuousOn (fun s => u (q + s)) (Icc 0 (t - q)) ∧
      (∀ s₁ ∈ Icc (0 : ℝ) (t - q), ∀ s₂ ∈ Icc (0 : ℝ) (t - q), s₁ ≤ s₂ →
        u (q + s₂) - u (q + s₁) = -(shiftDrive W q s₂ - shiftDrive W q s₁) +
          ∫ s in s₁..s₂, 2 / u (q + s)) ∧
      IntervalIntegrable (fun s => 2 / u (q + s)) volume 0 (t - q) ∧
      volume {s | s ∈ Icc (0 : ℝ) (t - q) ∧ u (q + s) = 0} = 0 := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) (t - q), q + s ∈ Icc (0 : ℝ) t := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨huc.comp (continuous_const.add continuous_id).continuousOn hmem, ?_, ?_, ?_⟩
  · intro s₁ hs₁ s₂ hs₂ h12
    rw [hueq _ (hmem s₁ hs₁) _ (hmem s₂ hs₂) (by linarith),
      intervalIntegral.integral_comp_add_left (fun s => 2 / u s) q]
    simp only [shiftDrive]
    ring
  · have h1 : IntervalIntegrable (fun s => 2 / u s) volume q t :=
      huint.mono_set (by rw [uIcc_of_le hqt, uIcc_of_le (hq.trans hqt)]; exact Icc_subset_Icc_left hq)
    have h2 := h1.comp_add_left q
    simpa only [sub_self] using h2
  · refine measure_mono_null (t := (fun s => q + s) ⁻¹' {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0}) ?_ ?_
    · intro s hs
      exact ⟨hmem s hs.1, hs.2⟩
    · rw [measure_preimage_add]
      exact hnull

end Shift

/-! ### The prefix seen from the chart at time `q` -/

section Chart

open QuantumZipper.RS (shiftDrive)

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- **Pullback of an interior shifted tip** (finite-horizon form of the pullback identity): if the driver
after `A` agrees on `[0, u]` with a continuous driver `f` whose radial trace at `u` exists and lies in `ℍ`,
then `η(A + u) ∈ ℍ`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.mem_H_of_shiftDrive_eqOn (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {A u : ℝ} (hA : 0 ≤ A) (hu : 0 ≤ u) (hAuT : A + u < T)
    {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) (hEq : EqOn (shiftDrive W A) f (Icc 0 u))
    (hlim : Tendsto (fun y : ℝ => fwdMapInv f u (y * Complex.I)) (𝓝[>] 0) (𝓝 (QuantumZipper.trace f u)))
    (hH : QuantumZipper.trace f u ∈ H) : η (A + u) ∈ H := by
  have hS' := QuantumZipper.RS.continuous_shiftDrive hW A
  have htr : QuantumZipper.trace (shiftDrive W A) u = QuantumZipper.trace f u :=
    QuantumZipper.RS.trace_congr_drive hS' (QuantumZipper.RS.shiftDrive_zero _ _) hf hf0 hu hEq
  have hInv : EqOn (fwdMapInv (shiftDrive W A) u) (fwdMapInv f u) H :=
    QuantumZipper.RegCont.fwdMapInv_congr hS' (QuantumZipper.RS.shiftDrive_zero _ _) hf hf0 hEq
      ⟨hu, le_rfl⟩
  have hlimS : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W A) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (QuantumZipper.trace (shiftDrive W A) u)) := by
    rw [htr]
    exact hlim.congr' (eventually_mem_nhdsWithin.mono fun y hy =>
      (hInv (QuantumZipper.RS.mul_I_mem_H hy)).symm)
  have hpH : QuantumZipper.trace (shiftDrive W A) u ∈ H := htr ▸ hH
  have key := (QuantumZipper.RS.trace_add_of_tendsto_shift hW hW0 hA hu hpH hlimS).2.2
  rw [← hη.trace_eq hW hW0 (add_nonneg hA hu) hAuT, key]
  exact QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hA hpH

/-- The shift of a shift. -/
theorem shiftDrive_shiftDrive (W : ℝ → ℝ) (q A : ℝ) :
    shiftDrive (shiftDrive W q) (A - q) = shiftDrive W A := by
  funext r
  simp only [shiftDrive]
  ring_nf

/-- **(Aux. lemma 24, relative form.)** If the driver after a time `A ∈ [q, t]` agrees with a driver whose
trace is interior at `t − A`, then `η(t)` is not on the prefix `η([0, q])`: in the chart at `q` the tip at
`t − q` is interior, and `F̄_q` maps `ℍ` into `ℍ \ K_q`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.not_mem_image_of_shiftDrive_eqOn
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q A t : ℝ} (hq : 0 ≤ q)
    (hqA : q ≤ A) (hAt : A ≤ t) (htT : t < T) {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0)
    (hEq : EqOn (shiftDrive W A) f (Icc 0 (t - A)))
    (hlim : Tendsto (fun y : ℝ => fwdMapInv f (t - A) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (QuantumZipper.trace f (t - A))))
    (hH : QuantumZipper.trace f (t - A) ∈ H) : η t ∉ η '' Icc 0 q := by
  obtain ⟨hγ, hγη⟩ := hη.isLoewnerTraceLT_shift hW hW0 hq
  have hSc := QuantumZipper.RS.continuous_shiftDrive hW q
  have hγH : loewnerTip (shiftDrive W q) ((A - q) + (t - A)) ∈ H := by
    refine hγ.mem_H_of_shiftDrive_eqOn hSc (QuantumZipper.RS.shiftDrive_zero W q) (by linarith)
      (by linarith) (by linarith) hf hf0 ?_ hlim hH
    rw [shiftDrive_shiftDrive]
    exact hEq
  have h1 : (A - q) + (t - A) = t - q := by ring
  rw [h1] at hγH
  have h2 := hγη (t - q) (by linarith) (by linarith)
  rw [show q + (t - q) = t by ring] at h2
  rw [← h2]
  exact hη.extendFrom_not_mem_image_of_mem_H hW hW0 hq (by linarith) hγH

/-- **The main pathwise dichotomy, right collisions.** Let `û ≥ 0` be a right force coordinate on `[0, t]`
meeting the driver at `t`, and `q < t`. Either `η(t) ∉ η([0, q])`, or the *endpoint case* holds: `û` met the
driver before `q`, and in the chart at `q` every real point to the right of `û(q)` is alive up to `t`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.not_mem_image_or_endpoint_right
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q t : ℝ} (hq : 0 ≤ q)
    (hqt : q < t) (htT : t < T) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 t))
    (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) (hut : u t = 0) :
    η t ∉ η '' Icc 0 q ∨
      ((∃ s ∈ Icc 0 q, u s = 0) ∧
        ∀ y : ℝ, u q < y → ∃ v, IsForwardSol (shiftDrive W q) (y : ℂ) (t - q) v) := by
  obtain ⟨hγ, hγη⟩ := hη.isLoewnerTraceLT_shift hW hW0 hq
  have hSc := QuantumZipper.RS.continuous_shiftDrive hW q
  obtain ⟨huc', hueq', huint', hnull'⟩ := centredEq_shift hq hqt.le huc hueq huint hnull
  have hmem : ∀ s ∈ Icc (0 : ℝ) (t - q), q + s ∈ Icc (0 : ℝ) t := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨x, hx, hux, halive⟩ := hγ.exists_tip_real_of_collision_right hSc
    (QuantumZipper.RS.shiftDrive_zero W q) (by linarith) (by linarith) huc'
    (fun s hs => hu0 _ (hmem s hs)) hueq' huint' hnull' (by rw [show q + (t - q) = t by ring]; exact hut)
  rw [add_zero] at hux
  have hηt : η t = extendFrom H (fwdMapInv W q) (x : ℂ) := by
    have h2 := hγη (t - q) (by linarith) (by linarith)
    rw [show q + (t - q) = t by ring] at h2
    rw [← h2, hx]
  have hsubq : Icc (0 : ℝ) q ⊆ Icc 0 t := Icc_subset_Icc_right hqt.le
  by_cases hgt : u q < x
  · left
    rw [hηt]
    refine hη.extendFrom_not_mem_image_of_gt hW hW0 hq (by linarith) (huc.mono hsubq)
      (fun s hs => hu0 s (hsubq hs)) (fun s₁ hs₁ s₂ hs₂ h12 => hueq s₁ (hsubq hs₁) s₂ (hsubq hs₂) h12)
      (huint.mono_set (by rw [uIcc_of_le hq, uIcc_of_le (hq.trans hqt.le)]; exact hsubq)) ?_ hgt
    exact measure_mono_null (fun s (hs : s ∈ {s | s ∈ Icc (0 : ℝ) q ∧ u s = 0}) =>
      (⟨hsubq hs.1, hs.2⟩ : s ∈ {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0})) hnull
  · have hxeq : x = u q := le_antisymm (not_lt.1 hgt) hux
    by_cases hz : ∃ s ∈ Icc 0 q, u s = 0
    · right
      exact ⟨hz, fun y hy => halive y (by rw [hxeq]; exact hy)⟩
    · left
      push Not at hz
      rw [hηt, hxeq]
      exact hη.extendFrom_not_mem_image_of_ne_zero hW hW0 hq (by linarith) (huc.mono hsubq) hz
        (fun s₁ hs₁ s₂ hs₂ h12 => hueq s₁ (hsubq hs₁) s₂ (hsubq hs₂) h12)

/-- **The main pathwise dichotomy, left collisions** (mirror of the right case). Let `û ≤ 0` be a left force coordinate on `[0, t]`
meeting the driver at `t`, and `q < t`. Either `η(t) ∉ η([0, q])`, or the *endpoint case* holds: `û` met the
driver before `q`, and in the chart at `q` every real point to the left of `û(q)` is alive up to `t`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.not_mem_image_or_endpoint_left
    (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {q t : ℝ} (hq : 0 ≤ q)
    (hqt : q < t) (htT : t < T) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 t))
    (hu0 : ∀ s ∈ Icc 0 t, u s ≤ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) (hut : u t = 0) :
    η t ∉ η '' Icc 0 q ∨
      ((∃ s ∈ Icc 0 q, u s = 0) ∧
        ∀ y : ℝ, y < u q → ∃ v, IsForwardSol (shiftDrive W q) (y : ℂ) (t - q) v) := by
  obtain ⟨hγ, hγη⟩ := hη.isLoewnerTraceLT_shift hW hW0 hq
  have hSc := QuantumZipper.RS.continuous_shiftDrive hW q
  obtain ⟨huc', hueq', huint', hnull'⟩ := centredEq_shift hq hqt.le huc hueq huint hnull
  have hmem : ∀ s ∈ Icc (0 : ℝ) (t - q), q + s ∈ Icc (0 : ℝ) t := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨x, hx, hux, halive⟩ := hγ.exists_tip_real_of_collision_left hSc
    (QuantumZipper.RS.shiftDrive_zero W q) (by linarith) (by linarith) huc'
    (fun s hs => hu0 _ (hmem s hs)) hueq' huint' hnull' (by rw [show q + (t - q) = t by ring]; exact hut)
  rw [add_zero] at hux
  have hηt : η t = extendFrom H (fwdMapInv W q) (x : ℂ) := by
    have h2 := hγη (t - q) (by linarith) (by linarith)
    rw [show q + (t - q) = t by ring] at h2
    rw [← h2, hx]
  have hsubq : Icc (0 : ℝ) q ⊆ Icc 0 t := Icc_subset_Icc_right hqt.le
  by_cases hgt : x < u q
  · left
    rw [hηt]
    refine hη.extendFrom_not_mem_image_of_lt hW hW0 hq (by linarith) (huc.mono hsubq)
      (fun s hs => hu0 s (hsubq hs)) (fun s₁ hs₁ s₂ hs₂ h12 => hueq s₁ (hsubq hs₁) s₂ (hsubq hs₂) h12)
      (huint.mono_set (by rw [uIcc_of_le hq, uIcc_of_le (hq.trans hqt.le)]; exact hsubq)) ?_ hgt
    exact measure_mono_null (fun s (hs : s ∈ {s | s ∈ Icc (0 : ℝ) q ∧ u s = 0}) =>
      (⟨hsubq hs.1, hs.2⟩ : s ∈ {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0})) hnull
  · have hxeq : x = u q := le_antisymm hux (not_lt.1 hgt)
    by_cases hz : ∃ s ∈ Icc 0 q, u s = 0
    · right
      exact ⟨hz, fun y hy => halive y (by rw [hxeq]; exact hy)⟩
    · left
      push Not at hz
      rw [hηt, hxeq]
      exact hη.extendFrom_not_mem_image_of_ne_zero hW hW0 hq (by linarith) (huc.mono hsubq) hz
        (fun s₁ hs₁ s₂ hs₂ h12 => hueq s₁ (hsubq hs₁) s₂ (hsubq hs₂) h12)

end Chart

/-! ### Forward comparison and real forward solutions -/

section Compare

/-- **Forward comparison** for the centred real Loewner equation on `[a, b]`. Let `û ≥ 0` be a solution
with a null zero set and `X` any solution (both with integrable reciprocals). Then `X − û` decreases
wherever it is positive, so `X − û ≤ max (X(a) − û(a)) 0` on `[a, b]`. In particular two right force
coordinates keep their order, and a real point to the right of a force coordinate stays to its right. -/
theorem sub_le_max_of_centredEq {W : ℝ → ℝ} {a b : ℝ} {u X : ℝ → ℝ}
    (huc : ContinuousOn u (Icc a b)) (hu0 : ∀ s ∈ Icc a b, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume a b)
    (hnull : volume {s | s ∈ Icc a b ∧ u s = 0} = 0)
    (hXc : ContinuousOn X (Icc a b))
    (hXeq : ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, s₁ ≤ s₂ →
      X s₂ - X s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / X s)
    (hXint : IntervalIntegrable (fun s => 2 / X s) volume a b) :
    ∀ s ∈ Icc a b, X s - u s ≤ max (X a - u a) 0 := by
  intro s₀ hs₀
  have hsub0 : Icc a s₀ ⊆ Icc a b := Icc_subset_Icc_right hs₀.2
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc a b → u s ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with s hs h1 h2
    exact hs ⟨h1, h2⟩
  refine le_max_of_antitone_of_pos (f := fun s => X s - u s) hs₀.1
    ((hXc.mono hsub0).sub (huc.mono hsub0)) ?_
  intro s₁ s₂ h1 h12 h2 hpos
  have hs₁ : s₁ ∈ Icc a b := ⟨h1, (h12.trans h2).trans hs₀.2⟩
  have hs₂ : s₂ ∈ Icc a b := ⟨h1.trans h12, h2.trans hs₀.2⟩
  have hI : Icc s₁ s₂ ⊆ Icc a b := Icc_subset_Icc hs₁.1 hs₂.2
  have hab : a ≤ b := hs₀.1.trans hs₀.2
  have hint1 : IntervalIntegrable (fun s => 2 / X s) volume s₁ s₂ :=
    hXint.mono_set (by rw [uIcc_of_le h12, uIcc_of_le hab]; exact hI)
  have hint2 : IntervalIntegrable (fun s => 2 / u s) volume s₁ s₂ :=
    huint.mono_set (by rw [uIcc_of_le h12, uIcc_of_le hab]; exact hI)
  have hdiff : (X s₂ - u s₂) - (X s₁ - u s₁) = ∫ s in s₁..s₂, (2 / X s - 2 / u s) := by
    rw [intervalIntegral.integral_sub hint1 hint2]
    have e1 := hXeq s₁ hs₁ s₂ hs₂ h12
    have e2 := hueq s₁ hs₁ s₂ hs₂ h12
    linarith
  have hnn : 0 ≤ ∫ s in s₁..s₂, (2 / u s - 2 / X s) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict h12 ?_
    have hmem : ∀ᵐ s ∂(volume.restrict (Icc s₁ s₂)), s ∈ Icc s₁ s₂ :=
      ae_restrict_mem measurableSet_Icc
    filter_upwards [hmem, ae_restrict_of_ae hae] with s hs hsu
    have hu' : 0 < u s := lt_of_le_of_ne (hu0 s (hI hs)) (Ne.symm (hsu (hI hs)))
    have hXu : u s < X s := by
      have := hpos s hs
      linarith
    have h2 : 2 / X s ≤ 2 / u s := div_le_div_of_nonneg_left (by norm_num) hu' hXu.le
    show (0 : ℝ) ≤ 2 / u s - 2 / X s
    linarith
  rw [intervalIntegral.integral_sub hint2 hint1] at hnn
  rw [intervalIntegral.integral_sub hint1 hint2] at hdiff
  show X s₂ - u s₂ ≤ X s₁ - u s₁
  linarith

/-- The two-point form of the integral equation of a function given in the one-point form
`X(s) = X(a) − (W(s) − W(a)) + ∫ₐˢ f`, `f` integrable on `[a, b]`. -/
theorem twoPoint_of_onePoint {W : ℝ → ℝ} {a b : ℝ} {X f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hX : ∀ s ∈ Icc a b, X s = X a - (W s - W a) + ∫ r in a..s, f r) :
    ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, s₁ ≤ s₂ → X s₂ - X s₁ = -(W s₂ - W s₁) + ∫ r in s₁..s₂, f r := by
  intro s₁ hs₁ s₂ hs₂ _
  have hab : a ≤ b := hs₁.1.trans hs₁.2
  have hi : ∀ c ∈ Icc a b, IntervalIntegrable f volume a c := fun c hc =>
    hf.mono_set (by rw [uIcc_of_le hc.1, uIcc_of_le hab]; exact Icc_subset_Icc_right hc.2)
  rw [← intervalIntegral.integral_interval_sub_left (hi s₂ hs₂) (hi s₁ hs₁), hX s₁ hs₁, hX s₂ hs₂]
  ring

end Compare

section RealSol

open QuantumZipper.RS (shiftDrive)

variable {W : ℝ → ℝ}

/-- **The real part of a real forward solution.** A forward solution from a real point is real; its real
part `X` is continuous, nonvanishing, and solves the real equation on `[0, T]`, with integrable reciprocal. -/
theorem exists_real_of_isForwardSol (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {y : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol W (y : ℂ) T v) :
    ∃ X : ℝ → ℝ, ContinuousOn X (Icc 0 T) ∧ (∀ s ∈ Icc (0 : ℝ) T, X s ≠ 0 ∧ v s = X s) ∧
      X 0 = y - W 0 ∧
      (∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
        X s₂ - X s₁ = -(W s₂ - W s₁) + ∫ r in s₁..s₂, 2 / X r) ∧
      IntervalIntegrable (fun s => 2 / X s) volume 0 T := by
  have him := QuantumZipper.im_isForwardSol_real hW hT hv
  set X : ℝ → ℝ := fun s => (v s).re with hXdef
  have hvX : ∀ s ∈ Icc (0 : ℝ) T, v s = X s := fun s hs =>
    Complex.ext (by simp [hXdef]) (by simp [him s hs])
  have hXc : ContinuousOn X (Icc 0 T) := Complex.continuous_re.comp_continuousOn hv.1
  have hX0 : ∀ s ∈ Icc (0 : ℝ) T, X s ≠ 0 := fun s hs h => by
    have := (hv.2 s hs).1
    rw [hvX s hs, h, Complex.ofReal_zero] at this
    exact this rfl
  have hXint : IntervalIntegrable (fun s => 2 / X s) volume 0 T :=
    (continuousOn_const.div hXc hX0).intervalIntegrable_of_Icc hT
  have hone : ∀ s ∈ Icc (0 : ℝ) T, X s = X 0 - (W s - W 0) + ∫ r in (0 : ℝ)..s, 2 / X r := by
    intro s hs
    have h1 := (hv.2 s hs).2
    have h0 := QuantumZipper.FwdHolo.sol_zero hv hT
    have hint : (∫ r in (0 : ℝ)..s, (2 : ℂ) / v r) = ((∫ r in (0 : ℝ)..s, 2 / X r : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hvX r ⟨hr.1, hr.2.trans hs.2⟩]
      push_cast
      rfl
    rw [hint, hvX s hs] at h1
    rw [hvX 0 ⟨le_rfl, hT⟩] at h0
    have h1' := congrArg Complex.re h1
    have h0' := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h1' h0'
    linarith
  refine ⟨X, hXc, fun s hs => ⟨hX0 s hs, hvX s hs⟩, ?_,
    twoPoint_of_onePoint hXint hone, hXint⟩
  have h0 := QuantumZipper.FwdHolo.sol_zero hv hT
  rw [hvX 0 ⟨le_rfl, hT⟩] at h0
  have := congrArg Complex.re h0
  simpa using this

/-- Restriction of a forward solution to a shorter horizon. -/
theorem isForwardSol_mono {z : ℂ} {T T' : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W z T v)
    (hT' : T' ≤ T) : IsForwardSol W z T' v :=
  ⟨hv.1.mono (Icc_subset_Icc_right hT'), fun s hs => hv.2 s ⟨hs.1, hs.2.trans hT'⟩⟩

/-- **Restart of a forward solution** at a time `a ∈ [0, T]`: `v(a + ·)` is a forward solution of the
shifted driver from `v(a)`. -/
theorem isForwardSol_shift {z : ℂ} {T : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol W z T v) {a : ℝ}
    (ha : 0 ≤ a) (haT : a ≤ T) :
    IsForwardSol (shiftDrive W a) (v a) (T - a) (fun τ => v (a + τ)) := by
  have hmem : ∀ τ ∈ Icc (0 : ℝ) (T - a), a + τ ∈ Icc (0 : ℝ) T := fun τ hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hint : IntervalIntegrable (fun r => (2 : ℂ) / v r) volume 0 T :=
    (continuousOn_const.div hv.1 fun r hr => (hv.2 r hr).1).intervalIntegrable_of_Icc (ha.trans haT)
  have hi : ∀ c ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun r => (2 : ℂ) / v r) volume 0 c := fun c hc =>
    hint.mono_set (by rw [uIcc_of_le hc.1, uIcc_of_le (ha.trans haT)]; exact Icc_subset_Icc_right hc.2)
  refine ⟨hv.1.comp (continuous_const.add continuous_id).continuousOn hmem, fun τ hτ =>
    ⟨(hv.2 _ (hmem τ hτ)).1, ?_⟩⟩
  have e1 := (hv.2 _ (hmem τ hτ)).2
  have e0 := (hv.2 a ⟨ha, haT⟩).2
  have hshift : (∫ r in (0 : ℝ)..τ, (2 : ℂ) / v (a + r)) = ∫ r in a..(a + τ), (2 : ℂ) / v r := by
    rw [intervalIntegral.integral_comp_add_left (fun r => (2 : ℂ) / v r) a, add_zero]
  rw [hshift, ← intervalIntegral.integral_interval_sub_left (hi _ (hmem τ hτ)) (hi a ⟨ha, haT⟩)]
  show v (a + τ) = _
  rw [e1]
  conv_rhs => rw [e0]
  simp only [shiftDrive]
  push_cast
  ring

end RealSol

section Transfer

open QuantumZipper.RS (shiftDrive)

/-- A continuous function on `[a, b]` without zeros and positive at `a` is positive. -/
theorem pos_of_ne_zero_of_pos {X : ℝ → ℝ} {a b : ℝ} (hXc : ContinuousOn X (Icc a b))
    (hX0 : ∀ s ∈ Icc a b, X s ≠ 0) (ha : 0 < X a) : ∀ s ∈ Icc a b, 0 < X s := by
  intro s hs
  by_contra hcon
  have hle : X s ≤ 0 := not_lt.1 hcon
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hs.1 (hXc.mono (Icc_subset_Icc_right hs.2))
    ⟨hle, ha.le⟩
  exact hX0 c ⟨hc.1, hc.2.trans hs.2⟩ hc0

/-- **The endpoint case moves to later charts.** Let `û ≥ 0` be a right force coordinate on `[0, b]` for a
continuous driver `W₁` with `W₁ 0 = 0`, and suppose every real point to the right of `û(0)` is alive up to
`b`. Then for `a ∈ [0, b]`, in the chart at `a` every real point to the right of `û(a)` is alive up to `b`:
the flow from `y = û(0) + (y' − û(a))/2` stays within `(y' − û(a))/2` of `û`, so it is left of `y'` at `a`. -/
theorem alive_shift_of_alive {W₁ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₁0 : W₁ 0 = 0) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 b))
    (hu0 : ∀ s ∈ Icc 0 b, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) b, ∀ s₂ ∈ Icc (0 : ℝ) b, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W₁ s₂ - W₁ s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 b)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) b ∧ u s = 0} = 0)
    (halive : ∀ y : ℝ, u 0 < y → ∃ v, IsForwardSol W₁ (y : ℂ) b v) :
    ∀ y' : ℝ, u a < y' → ∃ v, IsForwardSol (shiftDrive W₁ a) (y' : ℂ) (b - a) v := by
  intro y' hy'
  have hb : 0 ≤ b := ha.trans hab
  set y := u 0 + (y' - u a) / 2 with hydef
  obtain ⟨v, hv⟩ := halive y (by rw [hydef]; linarith)
  obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := exists_real_of_isForwardSol hW₁ hb hv
  rw [hW₁0, sub_zero] at hX0
  have hXpos := pos_of_ne_zero_of_pos hXc (fun s hs => (hXv s hs).1)
    (by rw [hX0, hydef]; linarith [hu0 0 ⟨le_rfl, hb⟩])
  have hsub : Icc (0 : ℝ) a ⊆ Icc 0 b := Icc_subset_Icc_right hab
  have hcmp := sub_le_max_of_centredEq (W := W₁) (a := 0) (b := a) (huc.mono hsub)
    (fun s hs => hu0 s (hsub hs)) (fun s₁ hs₁ s₂ hs₂ h12 => hueq s₁ (hsub hs₁) s₂ (hsub hs₂) h12)
    (huint.mono_set (by rw [uIcc_of_le ha, uIcc_of_le hb]; exact hsub))
    (measure_mono_null (fun s (hs : s ∈ {s | s ∈ Icc (0 : ℝ) a ∧ u s = 0}) =>
      (⟨hsub hs.1, hs.2⟩ : s ∈ {s | s ∈ Icc (0 : ℝ) b ∧ u s = 0})) hnull)
    (hXc.mono hsub) (fun s₁ hs₁ s₂ hs₂ h12 => hXeq s₁ (hsub hs₁) s₂ (hsub hs₂) h12)
    (hXint.mono_set (by rw [uIcc_of_le ha, uIcc_of_le hb]; exact hsub)) a ⟨ha, le_rfl⟩
  have hmax : max (X 0 - u 0) 0 = (y' - u a) / 2 := by
    rw [hX0, hydef, max_eq_left (by linarith)]
    ring
  rw [hmax] at hcmp
  have hXa : X a < y' := by linarith
  have hsh := isForwardSol_shift hv ha hab
  rw [(hXv a ⟨ha, hab⟩).2] at hsh
  exact QuantumZipper.RS.exists_isForwardSol_of_lt (QuantumZipper.RS.continuous_shiftDrive hW₁ a)
    (sub_nonneg.2 hab) (by rw [QuantumZipper.RS.shiftDrive_zero]; exact hXpos a ⟨ha, hab⟩) hXa hsh

/-- The first zero of a continuous function after a time where it does not vanish. -/
theorem exists_first_zero {u : ℝ → ℝ} {r t : ℝ} (hrt : r ≤ t) (huc : ContinuousOn u (Icc r t))
    (hur : u r ≠ 0) (hut : u t = 0) :
    ∃ σ ∈ Ioc r t, u σ = 0 ∧ ∀ s ∈ Ico r σ, u s ≠ 0 := by
  set S := Icc r t ∩ u ⁻¹' {0} with hS
  have hSc : IsCompact S :=
    isCompact_Icc.of_isClosed_subset (huc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      inter_subset_left
  have hSne : S.Nonempty := ⟨t, ⟨hrt, le_rfl⟩, hut⟩
  have hσ := hSc.sInf_mem hSne
  refine ⟨sInf S, ⟨lt_of_le_of_ne hσ.1.1 fun h => hur (by rw [h]; exact hσ.2), hσ.1.2⟩, hσ.2,
    fun s hs hs0 => ?_⟩
  have : sInf S ≤ s := csInf_le hSc.bddBelow ⟨⟨hs.1, hs.2.le.trans hσ.1.2⟩, hs0⟩
  exact absurd hs.2 (not_lt.2 this)

end Transfer

end Aux25

end InteractingSLE
