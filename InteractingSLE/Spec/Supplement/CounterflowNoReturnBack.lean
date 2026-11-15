/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Dimension.ForceGaps
import InteractingSLE.Foundations.Loewner.YuanCorollary13
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Foundations.Loewner.Reflect
import InteractingSLE.Spec.Sec5.GB7aAbove4Chart

/-!
# No return of a counterflow: boundary values through backward flows (deterministic)

Packet PROVE-CFNORETURN. For a continuous Loewner trace `η` of a continuous driver `W` (`W 0 = 0`) and a time
`t > 0`, write `F̄_t` for the boundary extension of the centred inverse map `F_t = fwdMapInv W t`. Let `û` be a
**right seed coordinate**: a nonnegative solution of the centred real Loewner equation on `[0, t]` with `û(0) = 0`
(the centred position `V⁰_R − W` of a right mark at `0⁺`). This file classifies the real zeros of `F̄_t` to the right
of the driver coordinate `0`:

* `extendFrom_eq_trace_of_lt` (**inside**): for `0 < c < û(t)`, `F̄_t(c) = η(v)` for some `v ∈ (0, t]`;
* `extendFrom_eq_of_gt` (**outside**): for `c > û(t)`, `F̄_t(c)` is a real point `x ≥ c − û(t) > 0` alive at `t`;
* `extendFrom_ne_zero_of_visit` (**at the seed**): if the trace visited a positive real point by time `t`,
  then `F̄_t(û(t)) ≠ 0`.

Hence (`eq_of_extendFrom_eq_zero_right`) if `η` does not return to `0` on `(0, t]`, a real zero `c > 0` of `F̄_t` is
the seed coordinate `û(t)`, and the trace has not visited `(0, ∞)` by time `t`.

**Proof of the inside case (backward flow).** Solve the centred equation backward from `c` at time `t`, with the drift
cut below at a small `δ` (`exists_backward_cut`); let `v_δ` be the last time where the solution is `≤ δ`. While the
solution `Y` stays below `û` the gap `û − Y` decreases forward in time (`2/û < 2/Y`), so it is at least `û(t) − c`
on `[v_δ, t]`; hence `û(v_δ) ≥ û(t) − c`, which keeps `v_δ` above a fixed `τ₀ > 0` (`û(0) = 0`), and forces the
solution to reach `δ` at all (`exists_backward_hit`). On `[v_δ, t]` it is a true real flow, so
`F̄_t(c) = F̄_{v_δ}(δ)` (`extendFrom_eq_of_realFlow`, through the shifted chain and the composition
`F̄_{a+u} = F̄_a ∘ F̄^{(a)}_u`, `extendFrom_add_eq`). Along `δ → 0` take a limit point `v* ∈ [τ₀, t]` of `v_δ`: in
both orders of `v_δ` and `v*` one writes `F̄_t(c) = F̄_{v*}(ζ_δ)` with `|ζ_δ| ≤ δ + 24 M + 8 √|v_δ − v*|`
(`norm_extendFrom_shift_sub_le`, `abs_realFlow_sub_le`), and continuity of `F̄_{v*}` at `0` gives
`F̄_t(c) = F̄_{v*}(0) = η(v*)`.

The left side is the reflection `z ↦ −z̄` (`extendFrom_fwdMapInv_neg`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace CfNoReturn

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### The shifted chains at the boundary -/

theorem isLoewnerTraceLT_of_isLoewnerTrace (hη : IsLoewnerTrace W η) (T : ℝ) : IsLoewnerTraceLT W T η :=
  ⟨hη.1, hη.2.1.mono Ico_subset_Ici_self, fun t ht _ => hη.2.2 t ht⟩

/-- **The boundary extension of a shifted inverse map moves points by at most `24 M + 8 √u`.** -/
theorem norm_extendFrom_shift_sub_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a u M : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (hM : ∀ r ∈ Icc (0 : ℝ) u, |W (a + r) - W a| ≤ M)
    {x : ℂ} (hx : x ∈ Hbar) :
    ‖extendFrom H (fwdMapInv (shiftDrive W a) u) x - x‖ ≤ 24 * M + 8 * Real.sqrt u := by
  have hV := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : shiftDrive W a 0 = 0 := QuantumZipper.RS.shiftDrive_zero W a
  have hcl : (𝓝[H] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hx)
  have ht := (((hη.hasBdryLimits_shift hW hW0 ha hu).tendsto hx).sub
    (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  refine le_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact norm_fwdMapInv_sub_le hV hV0 hu (fun r hr => hM r hr) hv

/-- **Composition at the boundary:** `F̄_{a+u}(x) = F̄_a(F̄^{(a)}_u(x))`, with `F̄^{(a)}_u(x) ∈ ℍ̄`. -/
theorem extendFrom_add_eq (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) {x : ℂ} (hx : x ∈ Hbar) :
    extendFrom H (fwdMapInv W (a + u)) x =
        extendFrom H (fwdMapInv W a) (extendFrom H (fwdMapInv (shiftDrive W a) u) x) ∧
      extendFrom H (fwdMapInv (shiftDrive W a) u) x ∈ Hbar := by
  obtain ⟨ξ, hξ, hFξ, hlim⟩ := hη.exists_tendsto_shift hW hW0 ha hu hx
  have he : extendFrom H (fwdMapInv (shiftDrive W a) u) x = ξ :=
    extendFrom_eq (by rw [closure_H]; exact hx) hlim
  rw [he]
  exact ⟨hFξ.symm, hξ⟩

/-- A real point of `ℍ̄`. -/
theorem ofReal_mem_Hbar' (x : ℝ) : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)

/-- **A real flow transports boundary values.** If `Y` solves the centred real Loewner equation on `[a, b]`
without vanishing, then `F̄^{(a)}_{b−a}(Y b) = Y a`; hence `F̄_b(Y b) = F̄_a(Y a)` and
`|Y b − Y a| ≤ 24 M + 8 √(b − a)`. -/
theorem extendFrom_shift_realFlow (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Icc a b))
    (hY0 : ∀ s ∈ Icc a b, Y s ≠ 0)
    (hYeq : ∀ s ∈ Icc a b, Y s - Y a = -(W s - W a) + ∫ r in a..s, 2 / Y r) :
    extendFrom H (fwdMapInv (shiftDrive W a) (b - a)) (Y b : ℂ) = Y a := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : V 0 = 0 := QuantumZipper.RS.shiftDrive_zero W a
  have hηs : IsLoewnerTrace V (loewnerTip V) := hη.isLoewnerTrace_shift hW hW0 ha
  set y : ℝ → ℝ := fun r => Y (a + r) with hydef
  have hmap : MapsTo (fun r : ℝ => a + r) (Icc 0 (b - a)) (Icc a b) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hyc : ContinuousOn y (Icc 0 (b - a)) :=
    hYc.comp (continuous_const.add continuous_id).continuousOn hmap
  have hy0 : ∀ r ∈ Icc (0 : ℝ) (b - a), y r ≠ 0 := fun r hr => hY0 _ (hmap hr)
  have hyeq : ∀ r ∈ Icc (0 : ℝ) (b - a), y r - y 0 = -(V r - V 0) + ∫ s in (0 : ℝ)..r, 2 / y s := by
    intro r hr
    have h1 := hYeq (a + r) (hmap hr)
    have h2 : ∫ s in (0 : ℝ)..r, 2 / y s = ∫ s in a..a + r, 2 / Y s := by
      simp only [hydef]
      rw [intervalIntegral.integral_comp_add_left (fun s => 2 / Y s) a, add_zero]
    rw [h2, hV0]
    simp only [hydef, hVdef, QuantumZipper.RS.shiftDrive, add_zero, sub_zero]
    linarith
  have hsol := isForwardSol_ofReal hV0 hyc hy0 hyeq
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  have h := (isLoewnerTraceLT_of_isLoewnerTrace hηs (b - a + 1)).extendFrom_eq_of_isForwardSol hV hV0 hba (by linarith) hsol
  simpa [hydef, add_sub_cancel] using h

theorem extendFrom_eq_of_realFlow (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Icc a b))
    (hY0 : ∀ s ∈ Icc a b, Y s ≠ 0)
    (hYeq : ∀ s ∈ Icc a b, Y s - Y a = -(W s - W a) + ∫ r in a..s, 2 / Y r) :
    extendFrom H (fwdMapInv W b) (Y b : ℂ) = extendFrom H (fwdMapInv W a) (Y a : ℂ) := by
  have h := (extendFrom_add_eq hη hW hW0 ha (sub_nonneg.2 hab) (ofReal_mem_Hbar' (Y b))).1
  rw [add_sub_cancel, extendFrom_shift_realFlow hη hW hW0 ha hab hYc hY0 hYeq] at h
  exact h

theorem abs_realFlow_sub_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Icc a b))
    (hY0 : ∀ s ∈ Icc a b, Y s ≠ 0)
    (hYeq : ∀ s ∈ Icc a b, Y s - Y a = -(W s - W a) + ∫ r in a..s, 2 / Y r)
    (hM : ∀ r ∈ Icc (0 : ℝ) (b - a), |W (a + r) - W a| ≤ M) :
    |Y b - Y a| ≤ 24 * M + 8 * Real.sqrt (b - a) := by
  have h := norm_extendFrom_shift_sub_le hη hW hW0 ha (sub_nonneg.2 hab) hM (ofReal_mem_Hbar' (Y b))
  rw [extendFrom_shift_realFlow hη hW hW0 ha hab hYc hY0 hYeq, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm] at h
  exact h

/-- Increments form of the centred equation, from its two-point form. -/
theorem realFlow_eq_of_incr {a b : ℝ} {Y : ℝ → ℝ}
    (hYeq : ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, s₁ ≤ s₂ → Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ r in s₁..s₂, 2 / Y r)
    (hab : a ≤ b) :
    ∀ s ∈ Icc a b, Y s - Y a = -(W s - W a) + ∫ r in a..s, 2 / Y r := fun s hs =>
  hYeq a ⟨le_rfl, hab⟩ s hs hs.1

/-! ### The real zero at a later return -/

/-- **A return transports to a real zero of an earlier boundary map.** If `η(u) = 0` and `0 ≤ t ≤ u`, there is a
real `c` with `|c| ≤ 24 M + 8 √(u − t)` and `F̄_t(c) = 0`. -/
theorem exists_extendFrom_eq_zero_of_return (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t u M : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) (hu : η u = 0)
    (hM : ∀ r ∈ Icc (0 : ℝ) (u - t), |W (t + r) - W t| ≤ M) :
    ∃ c : ℝ, |c| ≤ 24 * M + 8 * Real.sqrt (u - t) ∧ extendFrom H (fwdMapInv W t) (c : ℂ) = 0 := by
  have hut : 0 ≤ u - t := sub_nonneg.2 htu
  obtain ⟨hcomp, hζ⟩ := extendFrom_add_eq hη hW hW0 ht hut (zero_mem_Hbar)
  set ζ := extendFrom H (fwdMapInv (shiftDrive W t) (u - t)) 0 with hζdef
  have hbd := norm_extendFrom_shift_sub_le hη hW hW0 ht hut hM (zero_mem_Hbar)
  rw [← hζdef, sub_zero] at hbd
  have hF : extendFrom H (fwdMapInv W t) ζ = 0 := by
    rw [← hcomp, add_sub_cancel]
    have := hη.loewnerTip_eq hW hW0 (ht.trans htu)
    unfold loewnerTip at this
    rw [this, hu]
  have hζim : ζ.im = 0 := by
    rcases (show 0 ≤ ζ.im from hζ).lt_or_eq with hpos | h0
    · exfalso
      have hH : ζ ∈ H := hpos
      rw [extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht) hH] at hF
      have := QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hH
      rw [hF] at this
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)
    · exact h0.symm
  have hζeq : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [hζim])
  refine ⟨ζ.re, ?_, by rw [← hζeq]; exact hF⟩
  have : |ζ.re| ≤ ‖ζ‖ := Complex.abs_re_le_norm ζ
  linarith

/-! ### Reflection -/

theorem fwdMapInv_neg (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv (-W) t (LP.reflectC w) = LP.reflectC (fwdMapInv W t w) := by
  have hW' : Continuous (-W) := hW.neg
  have hW0' : (-W) 0 = 0 := by simp [hW0]
  set z := fwdMapInv W t w with hz
  have hzK := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw
  have hfz : fwdMap W t z = w := QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hw
  have hRz : LP.reflectC z ∈ H \ fwdHull (-W) t := by
    refine ⟨?_, fun h => ?_⟩
    · have : (0 : ℝ) < z.im := hzK.1
      show (0 : ℝ) < (LP.reflectC z).im
      simpa [LP.reflectC] using this
    · rw [LP.fwdHull_neg] at h
      obtain ⟨z', hz', he⟩ := h
      rw [LP.reflectC_injective he] at hz'
      exact hzK.2 hz'
  have h1 := LP.fwdMap_neg W ht z
  rw [hfz] at h1
  rw [← h1]
  exact QuantumZipper.RS.fwdMapInv_fwdMap hW' hW0' ht hRz

theorem tendsto_reflectC_nhdsWithin_H (x : ℂ) :
    Tendsto LP.reflectC (𝓝[H] (LP.reflectC x)) (𝓝[H] x) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := (LP.continuous_reflectC.tendsto (LP.reflectC x)).mono_left (nhdsWithin_le_nhds (s := H))
    rwa [LP.reflectC_reflectC] at this
  · filter_upwards [self_mem_nhdsWithin] with w hw
    have : (0 : ℝ) < w.im := hw
    show (0 : ℝ) < (LP.reflectC w).im
    simpa [LP.reflectC] using this

/-- **The boundary extensions of `W` and `−W` are conjugate by the reflection.** -/
theorem extendFrom_fwdMapInv_neg (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {x : ℂ} (hx : x ∈ Hbar) :
    extendFrom H (fwdMapInv (-W) t) (LP.reflectC x) = LP.reflectC (extendFrom H (fwdMapInv W t) x) := by
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto hx
  have hRx : LP.reflectC x ∈ closure H := by
    rw [closure_H]
    show (0 : ℝ) ≤ (LP.reflectC x).im
    have : (0 : ℝ) ≤ x.im := hx
    simpa [LP.reflectC] using this
  refine extendFrom_eq hRx ?_
  have h2 := (LP.continuous_reflectC.tendsto _).comp (hlim.comp (tendsto_reflectC_nhdsWithin_H x))
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hRw : LP.reflectC w ∈ H := by
    have : (0 : ℝ) < w.im := hw
    show (0 : ℝ) < (LP.reflectC w).im
    simpa [LP.reflectC] using this
  simp only [Function.comp]
  have := fwdMapInv_neg hW hW0 ht hRw
  rw [LP.reflectC_reflectC] at this
  rw [this]

/-! ### Backward real flows compared with a right seed coordinate -/

section Backward

variable {u : ℝ → ℝ} {t : ℝ}

theorem regDrift_eq_of_le {δ y : ℝ} (h : δ ≤ y) : Bessel.regDrift 2 δ y = 2 / y := by
  simp only [Bessel.regDrift, max_eq_left h]

/-- **Below the seed coordinate.** Let `û` solve the centred equation on `[0, t]` and `Y` the equation with
the drift cut at `δ`, `Y(t) = c < û(t)`. On any `[α, t]` where `Y ≥ δ`: `û(t) − c ≤ û(α) − Y(α)`. -/
theorem sub_le_of_backward_below {δ c α : ℝ} (hδ : 0 < δ) (hα : α ∈ Icc 0 t)
    (huc : ContinuousOn u (Icc 0 t))
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Icc 0 t)) (hYt : Y t = c)
    (hYeq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, Bessel.regDrift 2 δ (Y s))
    (hYδ : ∀ s ∈ Icc α t, δ ≤ Y s) (hcu : c < u t) :
    u t - c ≤ u α - Y α := by
  have hsub : Icc α t ⊆ Icc 0 t := Icc_subset_Icc_left hα.1
  have hreg : Continuous (Bessel.regDrift 2 δ) :=
    (Bessel.lipschitzWith_regDrift (by norm_num) hδ).continuous
  have key := le_max_of_antitone_of_pos (f := fun s => u s - Y s) hα.2
    ((huc.mono hsub).sub (hYc.mono hsub)) ?_
  · simp only [hYt] at key
    rcases le_max_iff.1 key with h | h
    · exact h
    · linarith
  intro s₁ s₂ h1 h12 h2 hpos
  have hs₁ : s₁ ∈ Icc (0 : ℝ) t := ⟨hα.1.trans h1, h12.trans h2⟩
  have hs₂ : s₂ ∈ Icc (0 : ℝ) t := ⟨hα.1.trans (h1.trans h12), h2⟩
  have hI : Icc s₁ s₂ ⊆ Icc 0 t := Icc_subset_Icc hs₁.1 h2
  have hint1 : IntervalIntegrable (fun s => Bessel.regDrift 2 δ (Y s)) volume s₁ s₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h12]
    exact hreg.comp_continuousOn (hYc.mono hI)
  have ht0 : (0 : ℝ) ≤ t := hα.1.trans hα.2
  have hint2 : IntervalIntegrable (fun s => 2 / u s) volume s₁ s₂ :=
    huint.mono_set (by rw [uIcc_of_le h12, uIcc_of_le ht0]; exact hI)
  have hnn : 0 ≤ ∫ s in s₁..s₂, (Bessel.regDrift 2 δ (Y s) - 2 / u s) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict h12 ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hYs : δ ≤ Y s := hYδ s ⟨h1.trans hs.1, hs.2.trans h2⟩
    have huY : Y s < u s := by have := hpos s hs; linarith
    have hYpos : 0 < Y s := hδ.trans_le hYs
    rw [regDrift_eq_of_le hYs]
    show (0 : ℝ) ≤ 2 / Y s - 2 / u s
    have : 2 / u s ≤ 2 / Y s := div_le_div_of_nonneg_left (by norm_num) hYpos huY.le
    linarith
  rw [intervalIntegral.integral_sub hint1 hint2] at hnn
  have e1 := hYeq s₁ hs₁ s₂ hs₂ h12
  have e2 := hueq s₁ hs₁ s₂ hs₂ h12
  show u s₂ - Y s₂ ≤ u s₁ - Y s₁
  linarith

/-- **Above the seed coordinate.** If `c > û(t)`, the cut backward solution from `c` stays at least
`c − û(t)` above `û` on `[0, t]`. -/
theorem sub_le_of_backward_above {δ c : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0)
    {Y : ℝ → ℝ} (hYc : ContinuousOn Y (Icc 0 t)) (hYt : Y t = c)
    (hYeq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, Bessel.regDrift 2 δ (Y s))
    (hcu : u t < c) : ∀ s ∈ Icc (0 : ℝ) t, c - u t ≤ Y s - u s := by
  intro s₀ hs₀
  have hsub : Icc s₀ t ⊆ Icc 0 t := Icc_subset_Icc_left hs₀.1
  have hreg : Continuous (Bessel.regDrift 2 δ) :=
    (Bessel.lipschitzWith_regDrift (by norm_num) hδ).continuous
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Icc (0 : ℝ) t → u s ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with s hs h1 h2
    exact hs ⟨h1, h2⟩
  have key := le_max_of_antitone_of_pos (f := fun s => Y s - u s) hs₀.2
    ((hYc.mono hsub).sub (huc.mono hsub)) ?_
  · simp only [hYt] at key
    rcases le_max_iff.1 key with h | h
    · exact h
    · linarith
  intro s₁ s₂ h1 h12 h2 hpos
  have hs₁ : s₁ ∈ Icc (0 : ℝ) t := ⟨hs₀.1.trans h1, h12.trans h2⟩
  have hs₂ : s₂ ∈ Icc (0 : ℝ) t := ⟨hs₀.1.trans (h1.trans h12), h2⟩
  have hI : Icc s₁ s₂ ⊆ Icc 0 t := Icc_subset_Icc hs₁.1 h2
  have hint1 : IntervalIntegrable (fun s => Bessel.regDrift 2 δ (Y s)) volume s₁ s₂ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h12]
    exact hreg.comp_continuousOn (hYc.mono hI)
  have hint2 : IntervalIntegrable (fun s => 2 / u s) volume s₁ s₂ :=
    huint.mono_set (by rw [uIcc_of_le h12, uIcc_of_le ht]; exact hI)
  have hnn : 0 ≤ ∫ s in s₁..s₂, (2 / u s - Bessel.regDrift 2 δ (Y s)) := by
    refine intervalIntegral.integral_nonneg_of_ae_restrict h12 ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hae] with s hs hsu
    have hu' : 0 < u s := lt_of_le_of_ne (hu0 s (hI hs)) (Ne.symm (hsu (hI hs)))
    have huY : u s < Y s := by have := hpos s hs; linarith
    have hYpos : 0 < Y s := hu'.trans huY
    have h1' : Bessel.regDrift 2 δ (Y s) ≤ 2 / Y s := by
      show 2 / max (Y s) δ ≤ 2 / Y s
      exact div_le_div_of_nonneg_left (by norm_num) hYpos (le_max_left _ _)
    have h2' : 2 / Y s ≤ 2 / u s := div_le_div_of_nonneg_left (by norm_num) hu' huY.le
    show (0 : ℝ) ≤ 2 / u s - Bessel.regDrift 2 δ (Y s)
    linarith
  rw [intervalIntegral.integral_sub hint2 hint1] at hnn
  have e1 := hYeq s₁ hs₁ s₂ hs₂ h12
  have e2 := hueq s₁ hs₁ s₂ hs₂ h12
  show Y s₂ - u s₂ ≤ Y s₁ - u s₁
  linarith

/-- **The backward flow from inside the seed interval reaches the driver after a fixed positive time.** -/
theorem exists_backward_hit (hW : Continuous W) (ht : 0 ≤ t)
    (huc : ContinuousOn u (Icc 0 t)) (huz : u 0 = 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t) {c : ℝ} (hcu : c < u t) :
    ∃ τ₀ > 0, ∀ δ, 0 < δ → δ < c → ∃ v ∈ Icc τ₀ t, ∃ Y : ℝ → ℝ, ContinuousOn Y (Icc v t) ∧ Y v = δ ∧
      Y t = c ∧ (∀ s ∈ Icc v t, δ ≤ Y s) ∧
      ∀ s₁ ∈ Icc v t, ∀ s₂ ∈ Icc v t, s₁ ≤ s₂ → Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ r in s₁..s₂, 2 / Y r := by
  rcases ht.eq_or_lt with h | ht0
  · refine ⟨1, one_pos, fun δ hδ hδc => ?_⟩
    exfalso
    rw [← h, huz] at hcu
    linarith
  set m := u t - c with hm
  have hm0 : 0 < m := sub_pos.2 hcu
  have h0t : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  obtain ⟨ε, hε, hεu⟩ := Metric.continuousWithinAt_iff.1 (huc 0 h0t) m hm0
  refine ⟨min (ε / 2) t, lt_min (half_pos hε) ht0, fun δ hδ hδc => ?_⟩
  obtain ⟨Y, hYc, hYt, hYeq⟩ := exists_backward_cut hW ht c hδ
  -- the last time at which `Y ≤ δ`
  set S : Set ℝ := Icc 0 t ∩ Y ⁻¹' Iic δ with hS
  have hSc : IsClosed S := hYc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := by
    by_contra hne
    have hall : ∀ s ∈ Icc (0 : ℝ) t, δ ≤ Y s := fun s hs => by
      by_contra hlt
      exact hne ⟨s, hs, (not_le.1 hlt).le⟩
    have h := sub_le_of_backward_below hδ h0t huc hueq huint hYc hYt hYeq hall hcu
    rw [huz] at h
    linarith [hall 0 h0t]
  have hSb : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
  set v := sSup S with hv
  have hvS : v ∈ S := hSc.csSup_mem hSne hSb
  have hvt : v ≤ t := hvS.1.2
  have hgt : ∀ s ∈ Ioc v t, δ < Y s := fun s hs => by
    by_contra hle
    have : s ∈ S := ⟨⟨hvS.1.1.trans hs.1.le, hs.2⟩, not_lt.1 hle⟩
    exact absurd (le_csSup hSb this) (not_le.2 hs.1)
  have hvt' : v < t := lt_of_le_of_ne hvt fun h => by
    have := hvS.2
    rw [h, mem_preimage, hYt, mem_Iic] at this
    linarith
  have hYv : Y v = δ := by
    refine le_antisymm hvS.2 ?_
    have hcw : ContinuousWithinAt Y (Ioc v t) v :=
      (hYc v hvS.1).mono (fun s hs => ⟨hvS.1.1.trans hs.1.le, hs.2⟩)
    have hne : (𝓝[Ioc v t] v).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hvt'.ne]
      exact ⟨le_rfl, hvt⟩
    exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun s hs => (hgt s hs).le)
  have hge : ∀ s ∈ Icc v t, δ ≤ Y s := fun s hs => by
    rcases hs.1.eq_or_lt with h | h
    · rw [← h, hYv]
    · exact (hgt s ⟨h, hs.2⟩).le
  have hcmp := sub_le_of_backward_below hδ hvS.1 huc hueq huint hYc hYt hYeq hge hcu
  have hvτ : min (ε / 2) t ≤ v := by
    by_contra hlt
    have hv1 : v < ε / 2 := lt_of_lt_of_le (not_le.1 hlt) (min_le_left _ _)
    have hd : dist v 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hvS.1.1]; linarith
    have := hεu hvS.1 hd
    rw [Real.dist_eq, huz, sub_zero] at this
    have := (abs_lt.1 this).2
    rw [hYv] at hcmp
    linarith
  refine ⟨v, ⟨hvτ, hvt⟩, Y, hYc.mono (Icc_subset_Icc_left hvS.1.1), hYv, hYt, hge, ?_⟩
  intro s₁ hs₁ s₂ hs₂ h12
  have h01 : s₁ ∈ Icc (0 : ℝ) t := ⟨hvS.1.1.trans hs₁.1, hs₁.2⟩
  have h02 : s₂ ∈ Icc (0 : ℝ) t := ⟨hvS.1.1.trans hs₂.1, hs₂.2⟩
  rw [hYeq s₁ h01 s₂ h02 h12]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le h12] at hr
  exact regDrift_eq_of_le (hge r ⟨hs₁.1.trans hr.1, hr.2.trans hs₂.2⟩)

/-- **The backward flow from beyond the seed interval is a real flow on all of `[0, t]`.** -/
theorem exists_backward_above (hW : Continuous W) (ht : 0 ≤ t)
    (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) {c : ℝ} (hcu : u t < c) :
    ∃ Y : ℝ → ℝ, ContinuousOn Y (Icc 0 t) ∧ Y t = c ∧ (∀ s ∈ Icc (0 : ℝ) t, c - u t ≤ Y s) ∧
      ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
        Y s₂ - Y s₁ = -(W s₂ - W s₁) + ∫ r in s₁..s₂, 2 / Y r := by
  set δ := (c - u t) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨Y, hYc, hYt, hYeq⟩ := exists_backward_cut hW ht c hδ
  have hcmp := sub_le_of_backward_above hδ ht huc hu0 hueq huint hnull hYc hYt hYeq hcu
  have hge : ∀ s ∈ Icc (0 : ℝ) t, c - u t ≤ Y s := fun s hs => by
    linarith [hcmp s hs, hu0 s hs]
  refine ⟨Y, hYc, hYt, hge, fun s₁ hs₁ s₂ hs₂ h12 => ?_⟩
  rw [hYeq s₁ hs₁ s₂ hs₂ h12]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le h12] at hr
  have hr' : r ∈ Icc (0 : ℝ) t := ⟨hs₁.1.trans hr.1, hr.2.trans hs₂.2⟩
  exact regDrift_eq_of_le (by linarith [hge r hr'])

end Backward

/-! ### Boundary values next to the seed -/

section Classify

variable {u : ℝ → ℝ} {t : ℝ}

/-- **Inside the seed interval:** for `0 < c < û(t)`, `F̄_t(c) = η(v)` for some `v ∈ (0, t]`. -/
theorem extendFrom_eq_trace_of_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) (huc : ContinuousOn u (Icc 0 t)) (huz : u 0 = 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t) {c : ℝ} (hc : 0 < c) (hcu : c < u t) :
    ∃ v ∈ Ioc 0 t, extendFrom H (fwdMapInv W t) (c : ℂ) = η v := by
  obtain ⟨τ₀, hτ₀, hhit⟩ := exists_backward_hit hW ht huc huz hueq huint hcu
  set δ : ℕ → ℝ := fun n => c / ((n : ℝ) + 2) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  have hδlt : ∀ n, δ n < c := fun n => by
    simp only [hδdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [n.cast_nonneg (α := ℝ)]
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simp only [hδdef]
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  choose v hv Y hYc hYv hYt hYδ hYeq using fun n => hhit (δ n) (hδpos n) (hδlt n)
  obtain ⟨vs, hvs, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hv
  have hvs0 : 0 < vs := hτ₀.trans_le hvs.1
  have hvst : vs ∈ Icc (0 : ℝ) t := ⟨hvs0.le, hvs.2⟩
  refine ⟨vs, ⟨hvs0, hvs.2⟩, ?_⟩
  have hFc : ContinuousWithinAt (extendFrom H (fwdMapInv W vs)) Hbar 0 :=
    (hη.hasBdryLimits hW hW0 hvs0.le).continuousOn 0 zero_mem_Hbar
  have h0 : extendFrom H (fwdMapInv W vs) 0 = η vs := hη.loewnerTip_eq hW hW0 hvs0.le
  rw [← h0]
  refine eq_of_forall_dist_le fun ε' hε' => ?_
  obtain ⟨r, hr, hball⟩ := Metric.continuousWithinAt_iff.1 hFc ε' hε'
  have hWu : UniformContinuousOn W (Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hW.continuousOn
  obtain ⟨ρ, hρ, hWρ⟩ := Metric.uniformContinuousOn_iff.1 hWu (r / 96) (by positivity)
  have hWb : ∀ a ∈ Icc (0 : ℝ) t, ∀ b ∈ Icc (0 : ℝ) t, |b - a| < ρ → |W b - W a| ≤ r / 96 :=
    fun a ha b hb hab => by
      have := hWρ b hb a ha (by rw [Real.dist_eq]; exact hab)
      rw [Real.dist_eq] at this
      exact this.le
  have hd : ∀ᶠ k in atTop, δ (φ k) < r / 4 ∧ dist (v (φ k)) vs < min ρ ((r / 32) ^ 2) := by
    refine ((hδlim.comp hφ.tendsto_atTop).eventually (gt_mem_nhds (by positivity))).and ?_
    exact Metric.tendsto_nhds.1 hlim _ (lt_min hρ (by positivity))
  obtain ⟨k, hk1, hk2⟩ := hd.exists
  set n := φ k with hn
  rw [Real.dist_eq] at hk2
  have hρk : |v n - vs| < ρ := hk2.trans_le (min_le_left _ _)
  have hsq : ∀ d : ℝ, 0 ≤ d → d ≤ |v n - vs| → 8 * Real.sqrt d < r / 4 := fun d hd0 hdle => by
    have h1 : Real.sqrt d < r / 32 := by
      rw [Real.sqrt_lt' (by positivity)]
      exact lt_of_le_of_lt hdle (hk2.trans_le (min_le_right _ _))
    linarith
  have hvn := hv n
  have hvn0 : 0 ≤ v n := hτ₀.le.trans hvn.1
  have hY0 : ∀ s ∈ Icc (v n) t, Y n s ≠ 0 := fun s hs => ((hδpos n).trans_le (hYδ n s hs)).ne'
  obtain ⟨ζ, hζH, hζF, hζn⟩ : ∃ ζ ∈ Hbar,
      extendFrom H (fwdMapInv W t) (c : ℂ) = extendFrom H (fwdMapInv W vs) ζ ∧ ‖ζ‖ < r := by
    rcases le_total vs (v n) with hle | hle
    · have hFt : extendFrom H (fwdMapInv W t) (c : ℂ) = extendFrom H (fwdMapInv W (v n)) (δ n : ℂ) := by
        have := extendFrom_eq_of_realFlow hη hW hW0 hvn0 hvn.2 (hYc n) hY0
          (realFlow_eq_of_incr (hYeq n) hvn.2)
        rw [hYt n, hYv n] at this
        exact this
      have hu'0 : 0 ≤ v n - vs := sub_nonneg.2 hle
      obtain ⟨hcomp, hξ⟩ := extendFrom_add_eq hη hW hW0 hvs0.le hu'0 (ofReal_mem_Hbar' (δ n))
      rw [add_sub_cancel] at hcomp
      refine ⟨_, hξ, hFt.trans hcomp, ?_⟩
      have hM : ∀ r' ∈ Icc (0 : ℝ) (v n - vs), |W (vs + r') - W vs| ≤ r / 96 := fun r' hr' =>
        hWb vs hvst (vs + r') ⟨by linarith [hr'.1], by linarith [hr'.2, hvn.2]⟩
          (by
            rw [add_sub_cancel_left, abs_of_nonneg hr'.1]
            exact lt_of_le_of_lt (hr'.2.trans (le_abs_self _)) hρk)
      have hb := norm_extendFrom_shift_sub_le hη hW hW0 hvs0.le hu'0 hM (ofReal_mem_Hbar' (δ n))
      have hδn : ‖(δ n : ℂ)‖ = δ n := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hδpos n)]
      have h8 := hsq (v n - vs) hu'0 (le_abs_self _)
      have htri := norm_le_insert' (extendFrom H (fwdMapInv (shiftDrive W vs) (v n - vs)) (δ n : ℂ))
        (δ n : ℂ)
      rw [hδn] at htri
      linarith
    · have hsub : Icc vs t ⊆ Icc (v n) t := Icc_subset_Icc_left hle
      have hFt : extendFrom H (fwdMapInv W t) (c : ℂ) = extendFrom H (fwdMapInv W vs) (Y n vs : ℂ) := by
        have := extendFrom_eq_of_realFlow hη hW hW0 hvs0.le hvs.2 ((hYc n).mono hsub)
          (fun s hs => hY0 s (hsub hs))
          (realFlow_eq_of_incr (fun s₁ hs₁ s₂ hs₂ h12 => hYeq n s₁ (hsub hs₁) s₂ (hsub hs₂) h12) hvs.2)
        rw [hYt n] at this
        exact this
      refine ⟨_, ofReal_mem_Hbar' _, hFt, ?_⟩
      have hsub' : Icc (v n) vs ⊆ Icc (v n) t := Icc_subset_Icc_right hvs.2
      have hM : ∀ r' ∈ Icc (0 : ℝ) (vs - v n), |W (v n + r') - W (v n)| ≤ r / 96 := fun r' hr' =>
        hWb (v n) ⟨hvn0, hvn.2⟩ (v n + r') ⟨by linarith [hr'.1], by linarith [hr'.2, hvs.2]⟩
          (by
            rw [add_sub_cancel_left, abs_of_nonneg hr'.1]
            exact lt_of_le_of_lt (hr'.2.trans (by rw [abs_sub_comm]; exact le_abs_self _)) hρk)
      have hb := abs_realFlow_sub_le hη hW hW0 hvn0 hle ((hYc n).mono hsub')
        (fun s hs => hY0 s (hsub' hs))
        (realFlow_eq_of_incr (fun s₁ hs₁ s₂ hs₂ h12 => hYeq n s₁ (hsub' hs₁) s₂ (hsub' hs₂) h12) hle) hM
      rw [hYv n] at hb
      have h8 := hsq (vs - v n) (sub_nonneg.2 hle) (by rw [abs_sub_comm]; exact le_abs_self _)
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := abs_sub_abs_le_abs_sub (Y n vs) (δ n)
      rw [abs_of_pos (hδpos n)] at this
      linarith
  rw [hζF]
  exact (hball hζH (by rw [dist_zero_right]; exact hζn)).le

/-- **Beyond the seed interval:** for `c > û(t)`, `F̄_t(c)` is a real point `x ≥ c − û(t)`, alive at `t`. -/
theorem extendFrom_eq_of_gt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0) {c : ℝ} (hcu : u t < c) :
    ∃ x : ℝ, c - u t ≤ x ∧ extendFrom H (fwdMapInv W t) (c : ℂ) = x ∧
      ∃ y : ℝ → ℂ, IsForwardSol W (x : ℂ) t y := by
  obtain ⟨Y, hYc, hYt, hge, hYeq⟩ := exists_backward_above hW ht huc hu0 hueq huint hnull hcu
  have hY0 : ∀ s ∈ Icc (0 : ℝ) t, Y s ≠ 0 := fun s hs =>
    (lt_of_lt_of_le (sub_pos.2 hcu) (hge s hs)).ne'
  have hsol := isForwardSol_ofReal hW0 hYc hY0 (realFlow_eq_of_incr hYeq ht)
  have h := (isLoewnerTraceLT_of_isLoewnerTrace hη (t + 1)).extendFrom_eq_of_isForwardSol hW hW0 ht
    (by linarith) hsol
  rw [hYt] at h
  exact ⟨Y 0, hge 0 ⟨le_rfl, ht⟩, h, _, hsol⟩

/-- **At the seed coordinate:** if the trace visited a positive real point by time `t`, then `F̄_t(û(t)) ≠ 0`
(it is at least that point). -/
theorem extendFrom_ne_zero_of_visit (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0)
    {s x₀ : ℝ} (hs : s ∈ Icc 0 t) (hx₀ : 0 < x₀) (hvis : η s = x₀) :
    extendFrom H (fwdMapInv W t) (u t : ℂ) ≠ 0 := by
  have hLT := isLoewnerTraceLT_of_isLoewnerTrace hη (t + 1)
  have hbig : ∀ n : ℕ, ∃ x : ℝ, x₀ ≤ x ∧
      extendFrom H (fwdMapInv W t) ((u t + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) = x := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨x, hx, hFx, y, hy⟩ := extendFrom_eq_of_gt hη hW hW0 ht huc hu0 hueq huint hnull
      (c := u t + 1 / ((n : ℝ) + 1)) (by linarith)
    refine ⟨x, ?_, hFx⟩
    have hxpos : 0 < x := lt_of_lt_of_le (by linarith) hx
    by_contra hlt
    have hys : IsForwardSol W (x : ℂ) s y :=
      ⟨hy.1.mono (Icc_subset_Icc_right hs.2), fun r hr => hy.2 r ⟨hr.1, hr.2.trans hs.2⟩⟩
    have hal := Sec7.Lemma76E.alive_of_isForwardSol hW hs.1 (by rw [hW0]; exact hxpos) hys
    have hal' := MartChar.RealFlow.Alive.of_le hW hal (not_le.1 hlt).le hs.1
    have hsol := WangWu.isForwardSol_of_alive hW hal'
    exact Sec5.GB7aAbove4.trace_ne_of_isForwardSol hLT hW hW0 ⟨hs.1, by linarith [hs.2]⟩ hsol hvis
  choose x hx hFx using hbig
  intro h0
  have hcont : ContinuousWithinAt (extendFrom H (fwdMapInv W t)) Hbar (u t : ℂ) :=
    (hη.hasBdryLimits hW hW0 ht).continuousOn _ (ofReal_mem_Hbar' _)
  have hseq : Tendsto (fun n : ℕ => ((u t + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[Hbar] (u t : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ofReal_mem_Hbar' _⟩
    have : Tendsto (fun n : ℕ => u t + 1 / ((n : ℝ) + 1)) atTop (𝓝 (u t + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at this
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hlim := hcont.tendsto.comp hseq
  rw [h0] at hlim
  have hre := (Complex.continuous_re.tendsto _).comp hlim
  have hre' : Tendsto x atTop (𝓝 0) := by
    refine hre.congr fun n => ?_
    simp only [Function.comp_apply, hFx, Complex.ofReal_re]
  have : x₀ ≤ 0 := by
    simpa using ge_of_tendsto hre' (Eventually.of_forall hx)
  linarith

/-- **Right real zeros of `F̄_t`.** If `η` does not vanish on `(0, t]`, a real zero `c > 0` of `F̄_t` is the seed
coordinate `û(t)`, and the trace has not visited `(0, ∞)` by time `t`. -/
theorem eq_of_extendFrom_eq_zero_right (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) (huc : ContinuousOn u (Icc 0 t)) (hu0 : ∀ s ∈ Icc 0 t, 0 ≤ u s) (huz : u 0 = 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) t, ∀ s₂ ∈ Icc (0 : ℝ) t, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / u s)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 t)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ u s = 0} = 0)
    (hret : ∀ s ∈ Ioc 0 t, η s ≠ 0) {c : ℝ} (hc : 0 < c)
    (hF : extendFrom H (fwdMapInv W t) (c : ℂ) = 0) :
    c = u t ∧ ∀ s ∈ Icc 0 t, ∀ x : ℝ, 0 < x → η s ≠ x := by
  rcases lt_trichotomy c (u t) with hlt | heq | hgt
  · exfalso
    obtain ⟨v, hv, hFv⟩ := extendFrom_eq_trace_of_lt hη hW hW0 ht huc huz hueq huint hc hlt
    exact hret v hv (by rw [← hFv]; exact hF)
  · refine ⟨heq, fun s hs x hx hvis => ?_⟩
    rw [heq] at hF
    exact extendFrom_ne_zero_of_visit hη hW hW0 ht huc hu0 hueq huint hnull hs hx hvis hF
  · exfalso
    obtain ⟨x, hx, hFx, -⟩ := extendFrom_eq_of_gt hη hW hW0 ht huc hu0 hueq huint hnull hgt
    rw [hFx] at hF
    have : x = 0 := by exact_mod_cast hF
    linarith [sub_pos.2 hgt]

end Classify

end CfNoReturn

end InteractingSLE
