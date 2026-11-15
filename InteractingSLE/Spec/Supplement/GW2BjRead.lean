/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BjBern
import InteractingSLE.Spec.Supplement.GW2BjLip
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Measurable readouts of uniformly Lipschitz driver functionals (near facts, piece 1)

Packet PROVE-GW2-BUF (round 7). A functional `Φ` of real drivers is Lipschitz in the uniform norm on `[0, T]` among
continuous drivers. Its readout on paths is the `limsup` of `Φ` along the Bernstein drivers. It is measurable, it reads
the path on `[0, T]` only, and on paths continuous on `[0, T]` it is `Φ` of the frozen driver.

* `lipRead T Φ w := limsup (Φ (bdrv T n w))`; **`measurable_lipRead`**, `lipRead_congr`, **`lipRead_eq`**;
* the regularized flow: `regFlowRead T ε y s`, **`measurable_regFlowRead`**, **`regFlowRead_eq`**.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow

/-- **The readout of a driver functional along the Bernstein drivers.** -/
def lipRead (T : ℝ≥0) (Φ : (ℝ → ℝ) → ℝ) (w : ℝ≥0 → ℝ) : ℝ := limsup (fun n => Φ (bdrv T n w)) atTop

/-- The Lipschitz property of a driver functional on `[0, T]` among continuous drivers. -/
def UnifLip (T : ℝ≥0) (Φ : (ℝ → ℝ) → ℝ) (C : ℝ) : Prop :=
  ∀ u u' : ℝ → ℝ, Continuous u → Continuous u' → ∀ δ : ℝ, 0 ≤ δ →
    (∀ s ∈ Icc (0 : ℝ) T, |u s - u' s| ≤ δ) → |Φ u - Φ u'| ≤ C * δ

theorem measurable_lipRead {T : ℝ≥0} {Φ : (ℝ → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hΦ : UnifLip T Φ C) :
    Measurable (lipRead T Φ) := by
  refine Measurable.limsup fun n => ?_
  have hc : Continuous fun v : Fin (n + 1) → ℝ => Φ (bsum T n v) := by
    refine Metric.continuous_iff.2 fun v ε hε => ⟨ε / (C + 1), by positivity, fun v' hv' => ?_⟩
    rw [Real.dist_eq]
    have h1 := hΦ (bsum T n v') (bsum T n v) (continuous_bsum T n v') (continuous_bsum T n v) ‖v' - v‖
      (norm_nonneg _) fun s _ => abs_bsum_sub_le T n v' v s
    have h2 : ‖v' - v‖ < ε / (C + 1) := by rwa [← dist_eq_norm]
    calc |Φ (bsum T n v') - Φ (bsum T n v)| ≤ C * ‖v' - v‖ := h1
      _ ≤ (C + 1) * ‖v' - v‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left h2 (by linarith)
      _ = ε := mul_div_cancel₀ _ (by linarith)
  exact hc.measurable.comp (measurable_gridVals T n)

/-- The readout reads the path on `[0, T]` only. -/
theorem lipRead_congr (T : ℝ≥0) (Φ : (ℝ → ℝ) → ℝ) {w w' : ℝ≥0 → ℝ} (h : ∀ u ≤ T, w u = w' u) :
    lipRead T Φ w = lipRead T Φ w' := by
  unfold lipRead
  simp only [bdrv_congr T _ h]

/-- **On a path continuous on `[0, T]` the readout is the functional of the frozen driver.** -/
theorem lipRead_eq {T : ℝ≥0} (hT : 0 < T) {Φ : (ℝ → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hΦ : UnifLip T Φ C)
    {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) : lipRead T Φ w = Φ (frozenDrive w T) := by
  have hwT : ContinuousOn w (Iic (T : ℝ).toNNReal) := by rwa [Real.toNNReal_coe]
  have hfc : Continuous (frozenDrive w T) := continuous_frozenDrive hwT
  have hlim : Tendsto (fun n => Φ (bdrv T n w)) atTop (𝓝 (Φ (frozenDrive w T))) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    have hδ : 0 < ε / (2 * (C + 1)) := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (tendsto_bdrv hT hw hδ)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 := hΦ (bdrv T n w) (frozenDrive w T) (continuous_bdrv T n w) hfc (ε / (2 * (C + 1))) hδ.le
      fun s hs => by rw [frozenDrive_eq hs]; exact hN n hn s hs
    calc |Φ (bdrv T n w) - Φ (frozenDrive w T)| ≤ C * (ε / (2 * (C + 1))) := h1
      _ ≤ (C + 1) * (ε / (2 * (C + 1))) := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  exact hlim.limsup_eq

/-! ### The regularized flow -/

/-- **The readout of the regularized flow** at level `ε` from `y`, at time `s`, for paths read on `[0, T]`. -/
def regFlowRead (T : ℝ≥0) (ε y s : ℝ) : (ℝ≥0 → ℝ) → ℝ := lipRead T fun u => regFlow u ε y s

theorem unifLip_regFlow {T : ℝ≥0} {ε : ℝ} (hε : 0 < ε) (y : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    UnifLip T (fun u => regFlow u ε y s) (1 + Real.exp ((2 / ε ^ 2).toNNReal * s)) := by
  intro u u' hu hu' δ hδ h
  rw [mul_comm]
  exact abs_regFlow_sub_le hu hu' hε T.2 hδ h y s hs

theorem measurable_regFlowRead (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) (y : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Measurable (regFlowRead T ε y s) :=
  measurable_lipRead (by positivity) (unifLip_regFlow hε y hs)

/-- **The readout is the regularized flow of the frozen driver** on paths continuous on `[0, T]`. -/
theorem regFlowRead_eq {T : ℝ≥0} (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) (y : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) :
    regFlowRead T ε y s w = regFlow (frozenDrive w T) ε y s :=
  lipRead_eq hT (by positivity) (unifLip_regFlow hε y hs) hw

end InteractingSLE.Theorem14.GW2Bh
