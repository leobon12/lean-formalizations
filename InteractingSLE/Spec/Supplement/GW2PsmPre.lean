/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmVer
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# GW2's open lines: two explored drivers agreeing up to `T` have the same traces, clocks and hulls up to `T`

Packet PROVE-GW2-STAGEMEAN, R121 round (prefix identification of the Claim(k) step), one sample:

* **`trace_eq_of_drv_eq`**: generating traces of two continuous drivers agreeing on `[0, T]` agree on `[0, T]`
  (the tip is the limit of the inverse Loewner map at `0`, which reads the driver on `[0, u]` only);
* `clockX_congr`, `hullX_congr`: ROOT2's relative clock and re-centred hull at time `t` read the explored driver on
  `[0, t]` only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Psm

open Exist.StagedLaw GW2Rz

/-- **Generating traces of two continuous drivers agreeing on `[0, T]` agree on `[0, T]`.** -/
theorem trace_eq_of_drv_eq {w w' : ℝ≥0 → ℝ} (hw : Continuous w) (hw' : Continuous w') (hw0 : w 0 = 0)
    (hw0' : w' 0 = 0) {γ γ' : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) (hγ' : IsGeneratingTrace w' ⊤ γ')
    {T : ℝ≥0} (h : ∀ u ≤ T, w u = w' u) {u : ℝ≥0} (hu : u ≤ T) : γ u = γ' u := by
  have h1 := hγ.tendsto_fwdMapInv_tip hw.continuousOn hw0 (ENNReal.coe_lt_top (r := u))
  have h2 := hγ'.tendsto_fwdMapInv_tip hw'.continuousOn hw0' (ENNReal.coe_lt_top (r := u))
  have hc : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hc' : Continuous fun s : ℝ => w' s.toNNReal := hw'.comp continuous_real_toNNReal
  have he : fwdMapInv (fun s : ℝ => w s.toNNReal) u = fwdMapInv (fun s : ℝ => w' s.toNNReal) u :=
    funext fun z => LocalExt.fwdMapInv_congr_of_continuousOn (t' := (u : ℝ) + 1) hc.continuousOn
      hc'.continuousOn u.coe_nonneg (by linarith) (fun x hx => h _ ((Real.toNNReal_le_iff_le_coe.2 hx.2).trans hu)) z
  rw [he] at h1
  have := GW1P.neBot_nhdsWithin_H (p := 0) (by simp [QuantumZipper.Hbar])
  exact tendsto_nhds_unique h1 h2

variable {Ω : Type*}

/-- **ROOT2's relative clock at `t` reads the explored driver on `[0, t]` only.** -/
theorem clockX_congr (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {w w' : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    {ω : Ω} (h : ∀ u ≤ t, w u ω = w' u ω) : clockX x s W' ζ' w t ω = clockX x s W' ζ' w' t ω := by
  unfold clockX recPair
  rw [GW2Wm.recOf_congr_top h]

/-- **The re-centred relative hull at `t` reads the explored driver on `[0, t]` only.** -/
theorem hullX_congr (x : ℝ) (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {w w' : ℝ≥0 → Ω → ℝ} {t : ℝ≥0}
    {ω : Ω} (h : ∀ u ≤ t, w u ω = w' u ω) : hullX x s W' ζ' w t ω = hullX x s W' ζ' w' t ω := by
  unfold hullX recPair
  rw [GW2Wm.recOf_congr_top h]

end InteractingSLE.Theorem14.GW2Psm
