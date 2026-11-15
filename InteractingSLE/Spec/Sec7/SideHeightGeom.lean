/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SideValues
import InteractingSLE.Spec.Dimension.TraceBridge
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# A flow line's side heights: the deterministic part

Packet PROVE-SIDEHEIGHT. The single-path coupling mean at a time `q < ζ` is
`𝔥_q(z) = 𝔥⁰_q(f_q(z)) − χ arg f_q′(z)`, with `𝔥⁰_q` the bounded harmonic extension of the force data at the centred
positions `V̂_q = V_q − W_q` (frozen `couplingMean`). The force data is `λ` on `(0, V̂^{0,R}_q)` (the image of the right
side of the trace) and `−λ` on `(V̂^{0,L}_q, 0)` (the image of the left side); no force point lies there because every
mark satisfies `V̂^{i,R} ≥ V̂^{0,R}`, `V̂^{i,L} ≤ V̂^{0,L}`. This file proves, for every approach `F` to an
interior trace point `γ(t₀) ∈ ℍ` inside `ℍ \ K_q` along which `f_q → y ∈ ℝ`:

* `y ≠ 0` lies strictly inside the slit interval: `V̂^{i,L}_q < y < V̂^{i,R}_q` for every mark (the force coordinates
  are the geometric images of `0±` and real points outside are images of alive real points, which the boundary
  extension `F̄_q` sends back to the real line, while `F̄_q(y) = γ(t₀) ∈ ℍ`);
* **`tendsto_comp_fwdMap_of_pos`**, **`tendsto_comp_fwdMap_of_neg`**: `𝔥⁰_q(f_q(z)) → λ` if `y > 0` and `→ −λ` if
  `y < 0`.

The driver of the frozen integrated path is continuous only before the lifetime; the slit lemmas of
`WangWu/SideValues` (stated for a continuous driver and a trace on `[0, ∞)`) are restated with the boundary extension
at the one time `q` as a hypothesis (`HasBdryLimits`), which the driver frozen after a time `t₂ ∈ (q, ζ)`
(`frozenDrive`, `IsGeneratingTrace.isLoewnerTraceLT`) supplies.

Also: a generating trace forces its driver to start at `0` (`w_zero_of_isGeneratingTrace`), so two drivers generating
the same trace agree before the lifetime (`eqOn_of_isGeneratingTrace`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex Metric
open scoped NNReal ENNReal Interval

namespace InteractingSLE

namespace Sec7

namespace SideHeight

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open MartChar.RealFlow

/-! ### The slit lemmas with the boundary extension at one time -/

section Slit

variable {W : ℝ → ℝ} {t : ℝ}

/-- **The boundary extension at a starting point of the flow**: if `u` solves the centred flow from `p ∈ ℍ̄` on
`[0, t]` and `F_t` has boundary limits, then `F̄_t(u_t) = p` (as `WangWu.extendFrom_eq_of_isForwardSol`). -/
theorem extendFrom_eq_of_isForwardSol' (hB : HasBdryLimits (fwdMapInv W t)) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {p : ℂ} (hp : p ∈ Hbar) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W p t u) : extendFrom H (fwdMapInv W t) (u t) = p := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hu
  set E := Real.exp (2 / δ ^ 2 * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hev : ∀ᶠ z in 𝓝[H] p, z ∈ H \ fwdHull W t := by
    have hball : ∀ᶠ z in 𝓝[H] p, z ∈ Metric.ball p (δ / E) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p (by positivity))
    filter_upwards [hball, self_mem_nhdsWithin] with z hz hzH
    refine ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc ‖z - p‖ * E < δ / E * E := mul_lt_mul_of_pos_right hz hE0
      _ = δ := div_mul_cancel₀ δ hE0.ne'
  have hlim : Tendsto (fwdMap W t) (𝓝[H] p) (𝓝 (u t)) := tendsto_fwdMap_of_isForwardSol hW ht hu
  have hNe : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hp)
  have hmaps : ∀ᶠ z in 𝓝[H] p, fwdMap W t z ∈ H :=
    hev.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
  have hutH : u t ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hlim hmaps
  have hlim' : Tendsto (fwdMap W t) (𝓝[H] p) (𝓝[Hbar] (u t)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, hmaps.mono fun z hz => le_of_lt (show (0 : ℝ) < (fwdMap W t z).im from hz)⟩
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] (u t))
      (𝓝 (extendFrom H (fwdMapInv W t) (u t))) := hB.continuousOn (u t) hutH
  have h2 : Tendsto (fun z => extendFrom H (fwdMapInv W t) (fwdMap W t z)) (𝓝[H] p) (𝓝 p) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (hev.mono fun z hz => (WangWu.extendFrom_fwdMap hW hW0 ht hz).symm)
  exact tendsto_nhds_unique (hF.comp hlim') h2

/-- If real points `x_n → x` are mapped by `F̄_t` to real points, so is `x`. -/
theorem im_extendFrom_eq_zero_of_tendsto' (hB : HasBdryLimits (fwdMapInv W t)) {x : ℝ} {xn : ℕ → ℝ}
    (hxn : Tendsto xn atTop (𝓝 x)) (him : ∀ n, (extendFrom H (fwdMapInv W t) (xn n)).im = 0) :
    (extendFrom H (fwdMapInv W t) x).im = 0 := by
  have hxH : ((x : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv W t) x)) := hB.continuousOn _ hxH
  have hc : Tendsto (fun n => ((xn n : ℝ) : ℂ)) atTop (𝓝[Hbar] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto x).comp hxn,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((xn n : ℝ) : ℂ).im by simp⟩
  have h := (Complex.continuous_im.tendsto _).comp (hF.comp hc)
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun n => (him n).symm)

/-- **Right real points mapped into `ℍ` lie left of the image of `0⁺`** (as
`WangWu.lt_rightImg_sub_of_extendFrom_mem_H`): if `F̄_t(x) ∈ ℍ` then `x < R_t − W_t`. -/
theorem lt_rightImg_sub_of_extendFrom_mem_H' (hB : HasBdryLimits (fwdMapInv W t)) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {x : ℝ} (hFx : extendFrom H (fwdMapInv W t) x ∈ H) :
    x < rightImg W 0 t - W t := by
  by_contra hle
  push Not at hle
  have hM : rightImg W 0 t ≤ x + W t := by linarith
  have hseq : ∀ n : ℕ, ∃ y, 0 < y ∧ Alive W y t ∧ x + W t < gImg W y t ∧
      gImg W y t < x + W t + 1 / ((n : ℝ) + 1) :=
    fun n => exists_alive_gImg_mem hW ht (by positivity) hM
  choose y hy0 hya hyM hyM' using hseq
  set xn : ℕ → ℝ := fun n => gImg W (y n) t - W t with hxn
  have him : ∀ n, (extendFrom H (fwdMapInv W t) (xn n)).im = 0 := fun n => by
    have h := extendFrom_eq_of_isForwardSol' hB hW hW0 ht
      (show (0 : ℝ) ≤ ((y n : ℂ)).im by simp) (WangWu.isForwardSol_of_alive hW (hya n))
    have e : (cflow W (y n) t : ℂ) = ((xn n : ℝ) : ℂ) := by
      rw [hxn]
      simp only [gImg]
      push_cast
      ring
    rw [e] at h
    rw [h]
    simp
  have hlim : Tendsto xn atTop (𝓝 x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => x)
      (h := fun n : ℕ => x + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_ (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hyM n
      simp only [hxn]
      linarith
    · have := hyM' n
      simp only [hxn]
      linarith
  have := im_extendFrom_eq_zero_of_tendsto' hB hlim him
  have hpos : (0 : ℝ) < (extendFrom H (fwdMapInv W t) x).im := hFx
  linarith

/-- **Left real points mapped into `ℍ` lie right of the image of `0⁻`** (as
`WangWu.neg_rightImg_sub_lt_of_extendFrom_mem_H`). -/
theorem neg_rightImg_sub_lt_of_extendFrom_mem_H' (hB : HasBdryLimits (fwdMapInv W t)) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {x : ℝ} (hFx : extendFrom H (fwdMapInv W t) x ∈ H) :
    -rightImg (fun s => -W s) 0 t - W t < x := by
  by_contra hle
  push Not at hle
  have hM : rightImg (fun s => -W s) 0 t ≤ -x - W t := by linarith
  have hseq : ∀ n : ℕ, ∃ y, 0 < y ∧ Alive (fun s => -W s) y t ∧ -x - W t < gImg (fun s => -W s) y t ∧
      gImg (fun s => -W s) y t < -x - W t + 1 / ((n : ℝ) + 1) :=
    fun n => exists_alive_gImg_mem hW.neg ht (by positivity) hM
  choose y hy0 hya hyM hyM' using hseq
  set xn : ℕ → ℝ := fun n => -(gImg (fun s => -W s) (y n) t + W t) with hxn
  have hcf : ∀ n, cflow (fun s => -W s) (y n) t = gImg (fun s => -W s) (y n) t + W t := fun n => by
    simp only [gImg]
    ring
  have him : ∀ n, (extendFrom H (fwdMapInv W t) (xn n)).im = 0 := fun n => by
    have h := extendFrom_eq_of_isForwardSol' hB hW hW0 ht
      (show (0 : ℝ) ≤ (-(y n : ℂ)).im by simp) (WangWu.isForwardSol_neg_of_alive hW (hya n))
    have e : -(cflow (fun s => -W s) (y n) t : ℂ) = ((xn n : ℝ) : ℂ) := by
      rw [hcf n, hxn]
      push_cast
      ring
    rw [e] at h
    rw [h]
    simp
  have hlim : Tendsto xn atTop (𝓝 x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => x - 1 / ((n : ℝ) + 1))
      (h := fun _ => x) ?_ tendsto_const_nhds (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hyM' n
      simp only [hxn]
      linarith
    · have := hyM n
      simp only [hxn]
      linarith
  have := im_extendFrom_eq_zero_of_tendsto' hB hlim him
  have hpos : (0 : ℝ) < (extendFrom H (fwdMapInv W t) x).im := hFx
  linarith

end Slit

/-! ### Force coordinates through the frozen driver -/

section Force

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem toNNReal_lt_of_le {t₂ : ℝ} (ht₂ : ENNReal.ofReal t₂ < ζ) {t : ℝ≥0} (htt₂ : (t : ℝ) ≤ t₂) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) t) : (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (hs.2.trans htt₂)) ht₂

/-- **The right force coordinates are the geometric images for the frozen driver**: `v^{i,R}_t = R^{x^{i,R}}_t` for
the driver frozen after any `t₂ ≥ t` below the lifetime. -/
theorem vR_eq_rightImg_frozenDrive (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t₂ : ℝ}
    (ht₂ : ENNReal.ofReal t₂ < ζ) {t : ℝ≥0} (htt₂ : (t : ℝ) ≤ t₂) (i : Fin nR) :
    vR i t = rightImg (frozenDrive w t₂) (xR i) t := by
  obtain ⟨hw0, -, hvR0, hwc, -, hvRc, -, -, hwvR, -, -, hgapR, -, -, hvReq, -, hnullR, -, -, -⟩ := hp
  have hrw : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) ht₂
  have hx : 0 ≤ xR i := by
    have := hwvR 0 hζ0 i
    rwa [hw0, hvR0] at this
  have hlt := fun s (hs : s ∈ Icc (0 : ℝ) t) => toNNReal_lt_of_le ht₂ htt₂ hs
  have hfr : ∀ s ∈ Icc (0 : ℝ) t, frozenDrive w t₂ s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans htt₂⟩
  have hint : IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - frozenDrive w t₂ s)) volume 0 t := by
    have h0 : IntervalIntegrable (fun s : ℝ => (-2) * (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t :=
      (hgapR t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 le_rfl) (by
        simpa using toNNReal_lt_of_le ht₂ htt₂ ⟨t.coe_nonneg, le_rfl⟩)) i).const_mul (-2)
    refine h0.congr ?_
    intro s hs
    rw [uIoc_of_le t.coe_nonneg] at hs
    show _ = 2 / (vR i s.toNNReal - frozenDrive w t₂ s)
    rw [hfr s ⟨hs.1.le, hs.2⟩, div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  have hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ frozenDrive w t₂ s = vR i s.toNNReal} = 0 :=
    measure_mono_null (fun s (hs : s ∈ Icc (0 : ℝ) t ∧ frozenDrive w t₂ s = vR i s.toNNReal) =>
      (⟨hs.1.1, hlt s hs.1, (hfr s hs.1).symm.trans hs.2⟩ :
        0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR i s.toNNReal))
      (hnullR i)
  have key := WangWu.eq_rightImg_of_forceEq (v := fun s : ℝ => vR i s.toNNReal) (T := t) hrw
    (by rw [frozenDrive_zero ht₂0, hw0]) hx
    ((hvRc i).comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs)
    (fun s hs => by rw [hfr s hs]; exact hwvR _ (hlt s hs) i) hint
    (fun s hs => by
      have h1 := hvReq s.toNNReal (hlt s hs) i
      rw [Real.coe_toNNReal _ hs.1] at h1
      rw [h1]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hfr r ⟨hr.1, hr.2.trans hs.2⟩])
    hnull ⟨t.coe_nonneg, le_rfl⟩
  simpa using key

/-- **The left force coordinates are the reflected geometric images for the frozen driver**:
`v^{i,L}_t = −R^{−x^{i,L}}_t[−w̃]`. -/
theorem vL_eq_neg_rightImg_frozenDrive (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t₂ : ℝ}
    (ht₂ : ENNReal.ofReal t₂ < ζ) {t : ℝ≥0} (htt₂ : (t : ℝ) ≤ t₂) (i : Fin nL) :
    vL i t = -rightImg (fun s => -frozenDrive w t₂ s) (-xL i) t := by
  obtain ⟨hw0, hvL0, -, hwc, hvLc, -, -, hvLw, -, -, hgapL, -, -, hvLeq, -, hnullL, -, -, -, -⟩ := hp
  have hrw : Continuous (fun s => -frozenDrive w t₂ s) := (continuous_frozenDrive_of_lt hwc ht₂).neg
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) ht₂
  have hx : 0 ≤ -xL i := by
    have := hvLw 0 hζ0 i
    rw [hw0, hvL0] at this
    linarith
  have hlt := fun s (hs : s ∈ Icc (0 : ℝ) t) => toNNReal_lt_of_le ht₂ htt₂ hs
  have hfr : ∀ s ∈ Icc (0 : ℝ) t, frozenDrive w t₂ s = w s.toNNReal := fun s hs =>
    frozenDrive_eq ⟨hs.1, hs.2.trans htt₂⟩
  have hint : IntervalIntegrable (fun s : ℝ => 2 / (-vL i s.toNNReal - -frozenDrive w t₂ s)) volume 0 t := by
    have h0 : IntervalIntegrable (fun s : ℝ => 2 * (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t :=
      (hgapL t (by simpa using toNNReal_lt_of_le ht₂ htt₂ ⟨t.coe_nonneg, le_rfl⟩) i).const_mul 2
    refine h0.congr ?_
    intro s hs
    rw [uIoc_of_le t.coe_nonneg] at hs
    show _ = 2 / (-vL i s.toNNReal - -frozenDrive w t₂ s)
    rw [hfr s ⟨hs.1.le, hs.2⟩, div_eq_mul_inv]
    ring
  have hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ -frozenDrive w t₂ s = -vL i s.toNNReal} = 0 :=
    measure_mono_null (fun s (hs : s ∈ Icc (0 : ℝ) t ∧ -frozenDrive w t₂ s = -vL i s.toNNReal) =>
      (⟨hs.1.1, hlt s hs.1, (hfr s hs.1).symm.trans (neg_injective hs.2)⟩ :
        0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL i s.toNNReal))
      (hnullL i)
  have key := WangWu.eq_rightImg_of_forceEq (v := fun s : ℝ => -vL i s.toNNReal) (T := t) hrw
    (by simp only [frozenDrive_zero ht₂0, hw0, neg_zero]) hx
    ((hvLc i).comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs).neg
    (fun s hs => by rw [hfr s hs]; exact neg_le_neg (hvLw _ (hlt s hs) i)) hint
    (fun s hs => by
      have h1 := hvLeq s.toNNReal (hlt s hs) i
      rw [Real.coe_toNNReal _ hs.1] at h1
      rw [h1, neg_add, ← intervalIntegral.integral_neg]
      congr 1
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hs.1] at hr
      simp only [hfr r ⟨hr.1, hr.2.trans hs.2⟩]
      rw [show -vL i r.toNNReal - -w r.toNNReal = -(vL i r.toNNReal - w r.toNNReal) by ring, div_neg])
    hnull ⟨t.coe_nonneg, le_rfl⟩
  rw [Real.toNNReal_coe] at key
  linarith

end Force

/-! ### The side values of the coupling mean -/

section Side

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- **The boundary extension at a real limit of `f_q`**: if `F ≤ 𝓝[ℍ \ K_q] p` and `f_q → y ∈ ℝ` along `F`, then
`y` is a real point at which the boundary extension `F̄_q` of the inverse map (for the driver frozen after `t₂`) equals
`p`. -/
theorem extendFrom_eq_of_tendsto_fwdMap (hγ : IsGeneratingTrace w ζ γ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {q : ℝ≥0} {t₂ : ℝ} (hqt₂ : (q : ℝ) < t₂)
    (ht₂ : ENNReal.ofReal t₂ < ζ) {p : ℂ} {F : Filter ℂ} [F.NeBot]
    (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p) {y : ℝ}
    (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) :
    extendFrom H (fwdMapInv (frozenDrive w t₂) q) y = p := by
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, (fun s : ℝ => w s.toNNReal) r = frozenDrive w t₂ r :=
    fun r hr => (frozenDrive_eq hr).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) q = fwdHull (frozenDrive w t₂) q :=
    fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ heq
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (frozenDrive w t₂) q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => heq r ⟨hr.1, hr.2.trans hqt₂.le⟩
  rw [hK] at hF
  rw [hM] at hy
  have hB := (hγ.isLoewnerTraceLT ht₂).hasBdryLimits hW hW0 q.coe_nonneg hqt₂
  have hev : ∀ᶠ z in F, z ∈ H \ fwdHull (frozenDrive w t₂) q := hF self_mem_nhdsWithin
  have hyH : ((y : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ (y : ℂ).im by simp
  have hy' : Tendsto (fwdMap (frozenDrive w t₂) q) F (𝓝[Hbar] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hy, hev.mono fun z hz =>
      le_of_lt (show (0 : ℝ) < (fwdMap (frozenDrive w t₂) q z).im from
        QuantumZipper.FwdHolo.mapsTo_fwdMap hW q.coe_nonneg hz)⟩
  have h1 := (hB.continuousOn _ hyH).tendsto.comp hy'
  have h2 : Tendsto (fun z => extendFrom H (fwdMapInv (frozenDrive w t₂) q) (fwdMap (frozenDrive w t₂) q z)) F
      (𝓝 p) :=
    (show Tendsto (fun z : ℂ => z) F (𝓝 p) from hF.trans nhdsWithin_le_nhds).congr'
      (hev.mono fun z hz => (WangWu.extendFrom_fwdMap hW hW0 q.coe_nonneg hz).symm)
  exact tendsto_nhds_unique h1 h2

/-- **A real limit of `f_q` at a point of `ℍ` lies strictly inside the slit interval**: `V̂^{i,L}_q < y < V̂^{i,R}_q`
for every mark, when `F ≤ 𝓝[ℍ \ K_q] p`, `p ∈ ℍ` and `f_q → y` along `F`. -/
theorem mem_slit_of_tendsto_fwdMap (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hγ : IsGeneratingTrace w ζ γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {p : ℂ} (hpH : p ∈ H) {F : Filter ℂ} [F.NeBot]
    (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p) {y : ℝ}
    (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) :
    (∀ i, vL i q - w q < y) ∧ ∀ i, y < vR i q - w q := by
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hwc := hp.2.2.2.1
  have hw0 := hp.1
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have hB := (hγ.isLoewnerTraceLT ht₂).hasBdryLimits hW hW0 q.coe_nonneg hqt₂
  have hFy : extendFrom H (fwdMapInv (frozenDrive w t₂) q) y ∈ H := by
    rw [extendFrom_eq_of_tendsto_fwdMap hγ hwc hw0 hqt₂ ht₂ hF hy]
    exact hpH
  have hWq : frozenDrive w t₂ q = w q := by
    rw [frozenDrive_eq ⟨q.coe_nonneg, hqt₂.le⟩, Real.toNNReal_coe]
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) hq
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hk := neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hW hW0 q.coe_nonneg hFy
    have hxL : 0 ≤ -xL i := by
      have := hp.2.2.2.2.2.2.2.1 0 hζ0 i
      rw [hp.1, hp.2.1 i] at this
      linarith
    have hmono : rightImg (fun s => -frozenDrive w t₂ s) 0 q ≤ rightImg (fun s => -frozenDrive w t₂ s) (-xL i) q :=
      rightImg_mono_index hW.neg q.coe_nonneg hxL
    rw [vL_eq_neg_rightImg_frozenDrive hp ht₂ hqt₂.le i]
    rw [hWq] at hk
    linarith
  · have hk := lt_rightImg_sub_of_extendFrom_mem_H' hB hW hW0 q.coe_nonneg hFy
    have hxR : 0 ≤ xR i := by
      have := hp.2.2.2.2.2.2.2.2.1 0 hζ0 i
      rwa [hp.1, hp.2.2.1 i] at this
    have hmono := rightImg_mono_index hW q.coe_nonneg hxR
    rw [vR_eq_rightImg_frozenDrive hp ht₂ hqt₂.le i]
    rw [hWq] at hk
    linarith

/-- **Right-side height `λ`.** For the bounded harmonic extension `𝔥⁰_q` of the force data at time `q < ζ`, along every
approach `F` to a point of `ℍ` inside `ℍ \ K_q` on which `f_q → y > 0`: `𝔥⁰_q(f_q(z)) → λ = π/√κ`. -/
theorem tendsto_comp_fwdMap_of_pos (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hγ : IsGeneratingTrace w ζ γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q))
      (forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q)) u)
    {p : ℂ} (hpH : p ∈ H) {F : Filter ℂ} [F.NeBot] (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p)
    {y : ℝ} (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) (hy0 : 0 < y) :
    Tendsto (fun z => u (fwdMap (fun s : ℝ => w s.toNNReal) q z)) F (𝓝 (sleLambda κ)) := by
  obtain ⟨hL, hR⟩ := mem_slit_of_tendsto_fwdMap hp hγ hq hpH hF hy
  have hζ : ∀ i, vL i q - w q ≤ 0 := fun i => sub_nonpos.2 (hp.2.2.2.2.2.2.2.1 q hq i)
  have hyS : y ∉ forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hy0.ne' h0
    · linarith [hζ i]
    · exact (hR i).ne' hi
  have hdata : forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q) y = sleLambda κ := by
    simp only [forceBoundaryData, show ¬ y < 0 from not_lt.2 hy0.le, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_le.2 (hR i), Finset.sum_empty, add_zero, mul_one, sleLambda]
  have hbd := hu.2.2 y hyS
  rw [hdata] at hbd
  have hev : ∀ᶠ z in F, z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) q := hF self_mem_nhdsWithin
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (frozenDrive w t₂) q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => (frozenDrive_eq ⟨hr.1, hr.2.trans hqt₂.le⟩).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) q = fwdHull (frozenDrive w t₂) q :=
    fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => (frozenDrive_eq hr).symm
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hp.2.2.2.1 ht₂
  have hmaps : ∀ᶠ z in F, fwdMap (fun s : ℝ => w s.toNNReal) q z ∈ H := hev.mono fun z hz => by
    rw [hM]
    rw [hK] at hz
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW q.coe_nonneg hz
  exact hbd.comp (tendsto_nhdsWithin_iff.2 ⟨hy, hmaps⟩)

/-- **Left-side height `−λ`**: as `tendsto_comp_fwdMap_of_pos`, for `y < 0`. -/
theorem tendsto_comp_fwdMap_of_neg (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hγ : IsGeneratingTrace w ζ γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q))
      (forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q)) u)
    {p : ℂ} (hpH : p ∈ H) {F : Filter ℂ} [F.NeBot] (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p)
    {y : ℝ} (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) (hy0 : y < 0) :
    Tendsto (fun z => u (fwdMap (fun s : ℝ => w s.toNNReal) q z)) F (𝓝 (-sleLambda κ)) := by
  obtain ⟨hL, hR⟩ := mem_slit_of_tendsto_fwdMap hp hγ hq hpH hF hy
  have hζ : ∀ i, 0 ≤ vR i q - w q := fun i => sub_nonneg.2 (hp.2.2.2.2.2.2.2.2.1 q hq i)
  have hyS : y ∉ forceJumpSet (fun i => vL i q - w q) (fun i => vR i q - w q) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hy0.ne h0
    · exact (hL i).ne' hi.symm
    · linarith [hζ i]
  have hdata : forceBoundaryData κ ρL ρR (fun i => vL i q - w q) (fun i => vR i q - w q) y = -sleLambda κ := by
    simp only [forceBoundaryData, hy0, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_lt.2 (hL i).le, Finset.sum_empty, add_zero, mul_one, sleLambda]
  have hbd := hu.2.2 y hyS
  rw [hdata] at hbd
  have hev : ∀ᶠ z in F, z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) q := hF self_mem_nhdsWithin
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (frozenDrive w t₂) q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => (frozenDrive_eq ⟨hr.1, hr.2.trans hqt₂.le⟩).symm
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) q = fwdHull (frozenDrive w t₂) q :=
    fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ fun r hr => (frozenDrive_eq hr).symm
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hp.2.2.2.1 ht₂
  have hmaps : ∀ᶠ z in F, fwdMap (fun s : ℝ => w s.toNNReal) q z ∈ H := hev.mono fun z hz => by
    rw [hM]
    rw [hK] at hz
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW q.coe_nonneg hz
  exact hbd.comp (tendsto_nhdsWithin_iff.2 ⟨hy, hmaps⟩)

end Side

/-! ### The driver of a generating trace -/

section Driver

variable {w w' : ℝ≥0 → ℝ} {T : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- A solution of the centred flow on `[0, T]` makes the driver continuous on `[0, T]`
(`W_s = z − u_s + ∫₀ˢ 2/u`). -/
theorem continuousOn_of_isForwardSol {W : ℝ → ℝ} {z : ℂ} {t : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W z t u) : ContinuousOn W (Icc 0 t) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [Icc_eq_empty (not_le.2 ht)]
    exact continuousOn_empty _
  have hinv : ContinuousOn (fun s => 2 / u s) (Icc 0 t) :=
    continuousOn_const.div hu.1 fun s hs => (hu.2 s hs).1
  have hprim : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, 2 / u r) (Icc 0 t) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := (0 : ℝ)) (b := t)
      (f := fun r => 2 / u r) (by rw [uIcc_of_le ht]; exact hinv.integrableOn_Icc)
    rwa [uIcc_of_le ht] at h
  have hc : ContinuousOn (fun s => z - u s + ∫ r in (0 : ℝ)..s, 2 / u r) (Icc 0 t) :=
    (continuousOn_const.sub hu.1).add hprim
  have he : EqOn (fun s => z - u s + ∫ r in (0 : ℝ)..s, 2 / u r) (fun s => ((W s : ℝ) : ℂ)) (Icc 0 t) :=
    fun s hs => by
      simp only
      rw [(hu.2 s hs).2]
      ring
  have h1 : ContinuousOn (fun s => ((W s : ℝ) : ℂ)) (Icc 0 t) := hc.congr fun s hs => (he hs).symm
  exact (Complex.continuous_re.comp_continuousOn h1).congr fun s _ => by simp

/-- The hull of a generating trace at a time before the horizon is bounded: it is the filling of the compact range. -/
theorem fwdHull_eq_fillH_of_isGeneratingTrace (hγ : IsGeneratingTrace w T γ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) :
    fwdHull (fun s : ℝ => w s.toNNReal) t = fillH (γ '' Icc 0 t) := by
  have hA : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn
    (hγ.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht.le)
  exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed fun z hz => hz.1).1 (hγ.2.2 t ht)

/-- **A generating trace makes its driver continuous before the horizon.** -/
theorem continuousOn_of_isGeneratingTrace (hγ : IsGeneratingTrace w T γ) :
    ContinuousOn w {t | (t : ℝ≥0∞) < T} := by
  intro t ht
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  have ht₂' : ((t₂.toNNReal : ℝ≥0) : ℝ≥0∞) < T := ht₂T
  have hK := fwdHull_eq_fillH_of_isGeneratingTrace hγ ht₂'
  rw [Real.coe_toNNReal _ ht₂0] at hK
  set A := γ '' Icc 0 t₂.toNNReal with hA_def
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn
    (hγ.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans ht₂'.le)
  obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
  have hfill : fillH A ⊆ closedBall ((0 : ℝ) : ℂ) R := by
    refine fillH_subset_closedBall ?_
    rw [hAc.isClosed.closure_eq]
    simpa using hR
  set z : ℂ := ((|R| + 1 : ℝ) : ℂ) * I with hz
  have hzH : z ∈ H := by
    show 0 < z.im
    simp only [hz, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    positivity
  have hzK : z ∉ fwdHull (fun s : ℝ => w s.toNNReal) t₂ := by
    rw [hK]
    intro hzA
    have := hfill hzA
    rw [mem_closedBall, ofReal_zero, dist_zero_right, hz, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
    linarith [le_abs_self R]
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht₂0 hzH hzK
  have hWc := continuousOn_of_isForwardSol hu
  have h1 : ContinuousWithinAt w (Iio t₂.toNNReal) t := by
    have hmaps : MapsTo (fun s : ℝ≥0 => (s : ℝ)) (Iio t₂.toNNReal) (Icc 0 t₂) := fun s hs =>
      ⟨s.coe_nonneg, by
        have := (Real.lt_toNNReal_iff_coe_lt).1 hs
        exact this.le⟩
    have h2 := (hWc (t : ℝ) ⟨t.coe_nonneg, htt₂.le⟩).comp NNReal.continuous_coe.continuousWithinAt hmaps
    exact h2.congr (fun s _ => by simp) (by simp)
  have hmem : Iio t₂.toNNReal ∈ 𝓝 t := Iio_mem_nhds (Real.lt_toNNReal_iff_coe_lt.2 htt₂)
  exact ((continuousWithinAt_iff_continuousAt hmem).1 h1).continuousWithinAt

/-- Shifting the driver by a constant shifts the hull: `z ∈ K_t[W] ⇒ z + c ∈ K_t[W + c]`. -/
theorem add_mem_fwdHull_add {W : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (c : ℝ) {z : ℂ} (hz : z ∈ fwdHull W t) :
    z + c ∈ fwdHull (fun r => W r + c) t := by
  rw [mem_fwdHull_iff_forall ht] at hz ⊢
  refine ⟨show 0 < (z + c).im by simpa using (show 0 < z.im from hz.1),
    fun T' hT' ⟨u, hu⟩ => hz.2 T' hT' ⟨u, hu.1, fun s hs => ⟨(hu.2 s hs).1, ?_⟩⟩⟩
  rw [(hu.2 s hs).2]
  push_cast
  ring

/-- **A generating trace forces its driver to start at `0`**: the hulls `K_s` are nonempty and within `M + 3√s` of
`W_0`, and they are the fillings of `γ([0, s])`, which shrink to `γ(0) = 0`. -/
theorem w_zero_of_isGeneratingTrace (hγ : IsGeneratingTrace w T γ) (hT : 0 < T) : w 0 = 0 := by
  obtain ⟨t₂, ht₂0, ht₂T⟩ := exists_real_btwn_of_lt (t := 0) (by simpa using hT)
  simp only [NNReal.coe_zero] at ht₂0
  set c := w 0 with hc
  have hwc := continuousOn_of_isGeneratingTrace hγ
  set A : ℝ → ℝ := fun r => frozenDrive w t₂ r - c with hA_def
  have hA : Continuous A := (continuous_frozenDrive_of_lt hwc ht₂T).sub continuous_const
  have hA0 : A 0 = 0 := by simp [hA_def, frozenDrive_zero ht₂0.le, hc]
  have hfr : frozenDrive w t₂ = fun r => A r + c := by funext r; simp [hA_def]
  -- the bound at a small time `s`
  have key : ∀ s : ℝ, 0 < s → s < t₂ → ∀ ε : ℝ, (∀ r ∈ Icc (0 : ℝ) s, |A r| ≤ ε) →
      (∀ r : ℝ≥0, r ≤ s.toNNReal → ‖γ r‖ ≤ ε) → |c| ≤ ε + (ε + 3 * Real.sqrt s) := by
    intro s hs hst ε hM hR
    obtain ⟨z₀, hz₀⟩ := QuantumZipper.CaraR.fwdHull_nonempty hA hA0 hs
    have hz₀b := QuantumZipper.CaraR.fwdHull_subset_closedBall hA hs hM hz₀
    rw [mem_closedBall, dist_zero_right] at hz₀b
    have hmem : z₀ + c ∈ fwdHull (fun r : ℝ => w r.toNNReal) s := by
      have h1 := add_mem_fwdHull_add hs.le c hz₀
      rw [← hfr] at h1
      rw [fwdHull_eq_of_eqOn (W' := frozenDrive w t₂) hs.le hst fun r hr => (frozenDrive_eq hr).symm]
      exact h1
    have hsT : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hst.le) ht₂T
    have hK := fwdHull_eq_fillH_of_isGeneratingTrace hγ hsT
    rw [Real.coe_toNNReal _ hs.le] at hK
    rw [hK] at hmem
    have hAc : IsCompact (γ '' Icc 0 s.toNNReal) := isCompact_Icc.image_of_continuousOn
      (hγ.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hsT.le)
    have hsub : closure (γ '' Icc 0 s.toNNReal) ⊆ closedBall ((0 : ℝ) : ℂ) ε := by
      rw [hAc.isClosed.closure_eq]
      rintro _ ⟨r, hr, rfl⟩
      rw [mem_closedBall, ofReal_zero, dist_zero_right]
      exact hR r hr.2
    have hb := fillH_subset_closedBall hsub hmem
    rw [mem_closedBall, ofReal_zero, dist_zero_right] at hb
    have : ‖(c : ℂ)‖ ≤ ‖z₀ + c‖ + ‖z₀‖ := by
      calc ‖(c : ℂ)‖ = ‖(z₀ + c) - z₀‖ := by ring_nf
        _ ≤ ‖z₀ + c‖ + ‖z₀‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    linarith
  -- letting `s → 0`
  refine abs_eq_zero.1 (le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (abs_nonneg c))
  have hAt : Tendsto A (𝓝 0) (𝓝 0) := by simpa [hA0] using hA.tendsto 0
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.tendsto_nhds_nhds.1 hAt (ε / 3) (by positivity)
  have hγt : Tendsto γ (𝓝[{t | (t : ℝ≥0∞) ≤ T}] 0) (𝓝 0) := by
    have : Tendsto γ (𝓝[{t | (t : ℝ≥0∞) ≤ T}] 0) (𝓝 (γ 0)) := hγ.2.1 0 (by simp)
    rwa [hγ.1] at this
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hγt (ε / 3) (by positivity)
  set s : ℝ := min (min (δ₁ / 2) (δ₂ / 2)) (min (t₂ / 2) ((ε / 9) ^ 2)) with hs_def
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ δ₁ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hs2 : s ≤ δ₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hs3 : s ≤ t₂ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs4 : s ≤ (ε / 9) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsq : Real.sqrt s ≤ ε / 9 := by
    rw [show ε / 9 = Real.sqrt ((ε / 9) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt hs4
  have h := key s hs0 (by linarith) (ε / 3) (fun r hr => by
      have := hδ₁' (show dist r 0 < δ₁ by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hr.1]; linarith [hr.2])
      rw [Real.dist_eq, sub_zero] at this
      exact this.le)
    (fun r hr => by
      have hrs : (r : ℝ) ≤ s := (Real.le_toNNReal_iff_coe_le hs0.le).1 hr
      have hst₂ : s ≤ t₂ := by linarith
      have hrT : (r : ℝ≥0∞) ≤ T :=
        ((ENNReal.coe_le_coe.2 hr).trans (ENNReal.ofReal_le_ofReal hst₂)).trans ht₂T.le
      have := hδ₂' hrT (show dist r 0 < δ₂ by
        rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg r.coe_nonneg]; linarith)
      rw [dist_zero_right] at this
      exact this.le)
  linarith

/-- **Two drivers generating the same trace agree before the horizon** (the hulls determine the driver,
`Sec6.eqOn_of_fwdHull_eq`). -/
theorem eq_of_isGeneratingTrace (hγ : IsGeneratingTrace w T γ) (hγ' : IsGeneratingTrace w' T γ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : w t = w' t := by
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  have hT : 0 < T := lt_of_le_of_lt (by simp) ht
  have hW := continuous_frozenDrive_of_lt (continuousOn_of_isGeneratingTrace hγ) ht₂T
  have hW' := continuous_frozenDrive_of_lt (continuousOn_of_isGeneratingTrace hγ') ht₂T
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, w_zero_of_isGeneratingTrace hγ hT]
  have hW0' : frozenDrive w' t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, w_zero_of_isGeneratingTrace hγ' hT]
  have hhull : ∀ s ∈ Icc (0 : ℝ) t, fwdHull (frozenDrive w t₂) s = fwdHull (frozenDrive w' t₂) s := by
    intro s hs
    have hst : s < t₂ := lt_of_le_of_lt hs.2 htt₂
    rw [(hγ.isLoewnerTraceLT ht₂T).2.2 s hs.1 hst, (hγ'.isLoewnerTraceLT ht₂T).2.2 s hs.1 hst]
  have h := Sec6.eqOn_of_fwdHull_eq hW hW' hW0 hW0' t.coe_nonneg hhull ⟨t.coe_nonneg, le_rfl⟩
  rwa [frozenDrive_eq ⟨t.coe_nonneg, htt₂.le⟩, frozenDrive_eq ⟨t.coe_nonneg, htt₂.le⟩, Real.toNNReal_coe] at h

/-- Two drivers generating the same trace have the same forward maps before the horizon. -/
theorem fwdMap_eq_of_isGeneratingTrace (hγ : IsGeneratingTrace w T γ) (hγ' : IsGeneratingTrace w' T γ)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T) :
    fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (fun s : ℝ => w' s.toNNReal) q := by
  funext z
  refine fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => eq_of_isGeneratingTrace hγ hγ' ?_
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hq

/-- Two drivers generating the same trace have the same canonical `log f_q′` before the horizon. -/
theorem logDerivFwd_eq_of_isGeneratingTrace (hγ : IsGeneratingTrace w T γ) (hγ' : IsGeneratingTrace w' T γ)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T) :
    QuantumZipper.logDerivFwd (fun s : ℝ => w s.toNNReal) q =
      QuantumZipper.logDerivFwd (fun s : ℝ => w' s.toNNReal) q := by
  funext z
  unfold QuantumZipper.logDerivFwd
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le q.coe_nonneg] at hs
  rw [fwdMap_eq_of_eqOn hs.1 fun r hr => eq_of_isGeneratingTrace hγ hγ' (lt_of_le_of_lt
    (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 (hr.2.trans hs.2))) hq)]

end Driver

end SideHeight

end Sec7

end InteractingSLE
