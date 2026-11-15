/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftHeightMeas
import InteractingSLE.Spec.Zhan.ConstDriftTrace

/-!
# A strip path is determined by its strip driver: the explicit chordal data

Packet PROVE-ZHAN-A7. For a path `f` and any strip path `(w, v, ζ)` whose strip driver is the constant-drift driver
`ξ = drv κ σ f` of `f` (`HasStripDriver`), the chordal data of the strip path are the explicit functions of
`ConstDriftHeightMeas.lean` (Astra L1503–L1505: `u'(t) = q_t²`, `V_{u(t)} = −A_t`, `W_{u(t)} = q_t − A_t`):

* `chordalTime_eq_ss`: the chordal time of the strip time `t` is `s(t) = ∫₀ᵗ q²`;
* `v_chordalTime_eq`, `w_chordalTime_eq`: the end mark and the driver at that chordal time are `−A_t` and `q_t − A_t`;
* `extPath_w_eq_cdrv`: on `[0, s(N)]` the driver is the frozen explicit driver `cdrv κ σ f N`;
* `tendsto_rad`: the radial values `F_{s(t)}(iy)` of `ConstDriftHeightMeas.lean` converge, as `y ↓ 0`, to `η(s(t))` for
  every generating trace `η` on the strip life.

The proofs are the fundamental theorem of calculus for the inverse strip clock (`hasDerivAt_chordalTime_eq_exp`) and
for the end mark (`IsSepMark.hasDerivAt_v`), with the identity `w − v = e^{ξ − t}` of the strip driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H fwdMapInv)
open QuantumZipper.RS (CPath)

namespace InteractingSLE

namespace Zhan

namespace HeightLaw

open Strip Retarget

variable {κ σ : ℝ} {f : CPath} {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem stripDriver_eq_drv (h : HasStripDriver w v ζ fun t => drv κ σ f t) {u : ℝ} (hu : 0 ≤ u) :
    stripDriver (extPath w) (extPath v) u = drv κ σ f u := by
  have := h.2 u.toNNReal
  simp only [Real.coe_toNNReal _ hu] at this
  exact this

theorem exp_two_mul_eq_rate (f : CPath) (u : ℝ) :
    Real.exp (2 * (drv κ σ f u - u)) = rate κ σ f u := by
  rw [rate, qq, sq, ← Real.exp_add]
  ring_nf

/-- A strip-life time whose strip clock exceeds `T`. -/
theorem exists_isSepMark (h : HasStripDriver w v ζ fun t => drv κ σ f t) (T : ℝ) :
    ∃ S : ℝ≥0, IsStripLife w v ζ S ∧ T < stripClock (extPath w) (extPath v) S ∧
      IsSepMark (extPath w) (extPath v) S := by
  obtain ⟨S, hS, hT⟩ := h.1.2.2 (T + 1)
  exact ⟨S, hS, by linarith, h.1.2.1 S hS⟩

/-- **The chordal time is `s(t) = ∫₀ᵗ q²`.** -/
theorem chordalTime_eq_ss (h : HasStripDriver w v ζ fun t => drv κ σ f t) {t : ℝ} (ht : 0 ≤ t) :
    chordalTime (extPath w) (extPath v) t = ss κ σ f t := by
  obtain ⟨S, -, htT, hm⟩ := exists_isSepMark h t
  have hc : ContinuousOn (chordalTime (extPath w) (extPath v)) (Icc 0 t) :=
    hm.continuousOn_chordalTime.mono (Icc_subset_Icc_right htT.le)
  have hd : ∀ u ∈ Ioo 0 t, HasDerivAt (chordalTime (extPath w) (extPath v)) (rate κ σ f u) u := by
    intro u hu
    have := hm.hasDerivAt_chordalTime_eq_exp ⟨hu.1, hu.2.trans htT⟩
    rwa [stripDriver_eq_drv h hu.1.le, exp_two_mul_eq_rate] at this
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc hd
    ((continuous_rate f).intervalIntegrable 0 t)
  rw [hm.chordalTime_zero, sub_zero] at hFTC
  rw [ss, Retarget.clk, hFTC]

/-- The gap `w − v` at the chordal time of the strip time `t` is `q_t = e^{ξ_t − t}`. -/
theorem gap_chordalTime_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) {t : ℝ} (ht : 0 ≤ t) :
    extPath w (chordalTime (extPath w) (extPath v) t) - extPath v (chordalTime (extPath w) (extPath v) t) =
      qq κ σ f t := by
  obtain ⟨S, -, htT, hm⟩ := exists_isSepMark h t
  have hmem := hm.chordalTime_mem ⟨ht, htT.le⟩
  have hpos := sub_pos.2 (hm.lt _ hmem)
  have hs := stripDriver_eq_drv h ht
  rw [stripDriver] at hs
  rw [qq, ← hs, add_sub_cancel_left, Real.exp_log hpos]

/-- **The end mark at the chordal time of the strip time `t` is `−A_t`.** -/
theorem v_chordalTime_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) {t : ℝ} (ht : 0 ≤ t) :
    extPath v (chordalTime (extPath w) (extPath v) t) = -aa κ σ f t := by
  obtain ⟨S, -, htT, hm⟩ := exists_isSepMark h t
  set g : ℝ → ℝ := fun u => extPath v (chordalTime (extPath w) (extPath v) u) with hg
  have hc : ContinuousOn g (Icc 0 t) :=
    (hm.continuousOn_v.comp hm.continuousOn_chordalTime hm.mapsTo_chordalTime).mono
      (Icc_subset_Icc_right htT.le)
  have hd : ∀ u ∈ Ioo 0 t, HasDerivAt g (-2 * qq κ σ f u) u := by
    intro u hu
    have hu' : u ∈ Ioo 0 (stripClock (extPath w) (extPath v) S) := ⟨hu.1, hu.2.trans htT⟩
    have h1 := hm.hasDerivAt_v (hm.chordalTime_mem_Ioo hu')
    have h2 := hm.hasDerivAt_chordalTime_eq_exp hu'
    have h3 := h1.comp u h2
    have hgap := gap_chordalTime_eq h hu.1.le
    have hq := qq_pos (κ := κ) (σ := σ) f u
    have key : 2 / (extPath v (chordalTime (extPath w) (extPath v) u) -
        extPath w (chordalTime (extPath w) (extPath v) u)) *
        Real.exp (2 * (stripDriver (extPath w) (extPath v) u - u)) = -2 * qq κ σ f u := by
      rw [stripDriver_eq_drv h hu.1.le, exp_two_mul_eq_rate, rate,
        show extPath v (chordalTime (extPath w) (extPath v) u) - extPath w (chordalTime (extPath w) (extPath v) u) =
          -(qq κ σ f u) by rw [← hgap]; ring]
      field_simp
    rw [key] at h3
    exact h3
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc hd
    (((continuous_qq f).const_mul (-2)).intervalIntegrable 0 t)
  have h0 : g 0 = -1 := by simp only [hg, hm.chordalTime_zero, hm.v_zero]
  rw [h0, intervalIntegral.integral_const_mul] at hFTC
  rw [aa]
  linarith

/-- **The driver at the chordal time of the strip time `t` is `q_t − A_t`.** -/
theorem w_chordalTime_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) {t : ℝ} (ht : 0 ≤ t) :
    extPath w (chordalTime (extPath w) (extPath v) t) = ww κ σ f t := by
  have h1 := gap_chordalTime_eq h ht
  have h2 := v_chordalTime_eq h ht
  rw [ww]
  linarith

/-- **On `[0, s(N)]` the driver is the frozen explicit driver.** -/
theorem extPath_w_eq_cdrv (h : HasStripDriver w v ζ fun t => drv κ σ f t) {N : ℝ} (hN : 0 ≤ N) {s : ℝ}
    (hs : s ∈ Icc 0 (ss κ σ f N)) : extPath w s = cdrv κ σ f N s := by
  have hr := isRate (κ := κ) (σ := σ) f hN
  have ht := tt_mem (κ := κ) (σ := σ) f hN s
  have hss : ss κ σ f (tt κ σ f N s) = s := by
    rw [ss, tt, clampS_of_mem f hs]
    exact hr.clk_invClk hs
  rw [cdrv, ← w_chordalTime_eq h ht.1, chordalTime_eq_ss h ht.1, hss]

/-- The chordal time of the strip time `t` (`chordT`) is `s(t)`. -/
theorem coe_chordT_eq (h : HasStripDriver w v ζ fun t => drv κ σ f t) (t : ℝ≥0) :
    ((chordT w v t : ℝ≥0) : ℝ) = ss κ σ f t := by
  rw [(h.1.chordT_spec t).2.1, chordalTime_eq_ss h t.coe_nonneg]

theorem tendsto_mul_I_nhdsH : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun y hy => ?_⟩
  · have : Continuous fun y : ℝ => (y : ℂ) * I := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  · show 0 < ((y : ℂ) * I).im
    simpa using hy

/-- **The radial values converge to the trace**: for every generating trace `η` on the strip life,
`F_{s(t)}(iy) → η(s(t))` as `y ↓ 0`. -/
theorem tendsto_rad (h : HasStripDriver w v ζ fun t => drv κ σ f t) {η : ℝ≥0 → ℂ}
    (hη : ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun y => rad κ σ f t y) (𝓝[>] 0) (𝓝 (η (chordT w v t.toNNReal))) := by
  set a := chordT w v t.toNNReal with ha_def
  have ha : (a : ℝ) = ss κ σ f t := by rw [ha_def, coe_chordT_eq h, Real.coe_toNNReal _ ht]
  have hal := (h.1.chordT_spec t.toNNReal).1
  obtain ⟨s', has', hs'⟩ := h.1.exists_gt hal
  have h₁ : Sec7.IsGeneratingTraceIcc w a η :=
    Sec7.IsGeneratingTrace.isGeneratingTraceIcc (hη s' hs') (h.1.continuousOn_lt hs') h.1.1
      (ENNReal.coe_lt_coe.2 has')
  have hlim := h₁.2.2
  have hfz : fwdMapInv (fun s : ℝ => w s.toNNReal) a = fwdMapInv (frozenDrive w s') a :=
    fwdMapInv_eq_of_eqOn (NNReal.coe_nonneg a) (NNReal.coe_lt_coe.2 has') fun r hr => by
      rw [frozenDrive_eq hr]
  have hfc : Continuous (frozenDrive w s') :=
    continuous_frozenDrive (by rw [Real.toNNReal_coe]; exact h.1.continuousOn_le hs')
  have hN : (0 : ℝ) ≤ (⌈t⌉₊ : ℝ) := Nat.cast_nonneg _
  have hcf : ∀ z ∈ H, fwdMapInv (frozenDrive w s') a z = fwdMapInv (cdrv κ σ f ⌈t⌉₊) a z := by
    intro z hz
    refine LP.fwdMapInv_eq_of_eqOn_Icc hfc (continuous_cdrv f hN)
      (by rw [frozenDrive_zero (NNReal.coe_nonneg s'), h.1.1]) (cdrv_zero f hN) (NNReal.coe_nonneg a)
      (fun r hr => ?_) hz
    have hrs' : r ≤ s' := hr.2.trans (NNReal.coe_le_coe.2 has'.le)
    rw [frozenDrive_eq ⟨hr.1, hrs'⟩]
    refine extPath_w_eq_cdrv h hN ⟨hr.1, ?_⟩
    calc r ≤ (a : ℝ) := hr.2
      _ = ss κ σ f t := ha
      _ ≤ ss κ σ f ⌈t⌉₊ :=
        ((isRate (κ := κ) (σ := σ) f hN).clk_le_clk ⟨ht, Nat.le_ceil t⟩ ⟨hN, le_rfl⟩).2 (Nat.le_ceil t)
  rw [hfz] at hlim
  have hcomp := hlim.comp tendsto_mul_I_nhdsH
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [Function.comp_apply, rad, ← ha]
  exact hcf _ (show 0 < ((y : ℂ) * I).im by simpa using hy)

end HeightLaw

end Zhan

end InteractingSLE
