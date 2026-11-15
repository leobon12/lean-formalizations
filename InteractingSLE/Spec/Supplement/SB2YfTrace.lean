/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.WangWu.ReverseContactBdryGlue
import InteractingSLE.Spec.ZhanGT4.D9Clear
import InteractingSLE.Spec.ZhanGT4.A1RefBridge
import InteractingSLE.Spec.Supplement.SB2XfChain
import InteractingSLE.Spec.Supplement.SB2MoNorm

/-!
# The relative curve of `IsStageS2`: the relative trace through its clock, continued by the frozen slit

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`'s lift `γ`). For a continuous driver `Wr` with a global Loewner trace
`ηr`, a continuous strictly increasing clock `τ` on `[0, sB]` from `0` to `u > 0`:

* `relClock τ sB u s = τ(min(max s 0, sB)) + max (s − sB) 0` (a continuous clock, `τ` on `[0, sB]`, then unit speed);
* **`relCurve`** `= extTrace Wr ηr u ∘ relClock`: `ηr ∘ τ` on `[0, sB]` (`relCurve_of_le`), then the image of the
  vertical slit under the frozen inverse map (`relCurve_of_gt`, in `ℍ ∖ K_u`);
* `continuous_relCurve`, `relCurve_zero`, `tendsto_norm_relCurve` (it tends to `∞`);
* `capClock_relCurve` (`capClock relCurve = τ` on `[0, sB]`) and **`relChainCore_relCurve`** (`Mn.RelChainCore`).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Sx

open YuanCorollary13 (extTrace extDrive)

/-- The clock of the relative curve: `τ` on `[0, sB]` (through the projection), then unit speed. -/
def relClock (τ : ℝ → ℝ) (sB : ℝ) (hsB : 0 ≤ sB) (s : ℝ) : ℝ :=
  τ (projIcc 0 sB hsB s) + max (s - sB) 0

/-- **The relative curve**: the relative trace through the clock, continued by the frozen slit. -/
def relCurve (Wr : ℝ → ℝ) (ηr : ℝ → ℂ) (τ : ℝ → ℝ) (sB u : ℝ) (hsB : 0 ≤ sB) : ℝ≥0 → ℂ :=
  fun s => extTrace Wr ηr u (relClock τ sB hsB s)

variable {Wr : ℝ → ℝ} {ηr : ℝ → ℂ} {τ : ℝ → ℝ} {sB u : ℝ} (hsB : 0 < sB)

theorem relClock_of_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ sB) : relClock τ sB hsB.le s = τ s := by
  simp only [relClock, projIcc_of_mem hsB.le ⟨hs0, hs⟩, max_eq_right (sub_nonpos.2 hs), add_zero]

theorem relClock_of_ge (hτs : τ sB = u) {s : ℝ} (hs : sB ≤ s) : relClock τ sB hsB.le s = u + (s - sB) := by
  simp only [relClock, projIcc_of_right_le hsB.le hs, max_eq_left (sub_nonneg.2 hs), hτs]

theorem continuous_relClock (hτc : ContinuousOn τ (Icc 0 sB)) : Continuous (relClock τ sB hsB.le) := by
  refine Continuous.add ?_ ((continuous_id.sub continuous_const).max continuous_const)
  exact hτc.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc 0 sB hsB.le s).2

theorem relClock_nonneg (hτm : MonotoneOn τ (Icc 0 sB)) (hτ0 : τ 0 = 0) (s : ℝ) : 0 ≤ relClock τ sB hsB.le s := by
  have h1 : τ 0 ≤ τ (projIcc 0 sB hsB.le s) :=
    hτm ⟨le_rfl, hsB.le⟩ (projIcc 0 sB hsB.le s).2 (projIcc 0 sB hsB.le s).2.1
  rw [hτ0] at h1
  exact add_nonneg h1 (le_max_right _ _)

theorem relCurve_of_le (hτm : MonotoneOn τ (Icc 0 sB)) (hτs : τ sB = u) {s : ℝ≥0} (hs : (s : ℝ) ≤ sB) :
    relCurve Wr ηr τ sB u hsB.le s = ηr (τ s) := by
  have hle : τ s ≤ u := hτs ▸ hτm ⟨NNReal.coe_nonneg s, hs⟩ ⟨hsB.le, le_rfl⟩ hs
  show extTrace Wr ηr u (relClock τ sB hsB.le s) = _
  rw [relClock_of_le hsB (NNReal.coe_nonneg s) hs, YuanCorollary13.extTrace_eq hle]

theorem relCurve_of_gt (hWc : Continuous Wr) (hW0 : Wr 0 = 0) (hu : 0 ≤ u) (hτs : τ sB = u) {s : ℝ≥0}
    (hs : sB < (s : ℝ)) :
    relCurve Wr ηr τ sB u hsB.le s = fwdMapInv Wr u (((2 * Real.sqrt ((s : ℝ) - sB) : ℝ) : ℂ) * I) ∧
      fwdMapInv Wr u (((2 * Real.sqrt ((s : ℝ) - sB) : ℝ) : ℂ) * I) ∈ H \ fwdHull Wr u := by
  have hr : 0 < (s : ℝ) - sB := sub_pos.2 hs
  have hwH : (((2 * Real.sqrt ((s : ℝ) - sB) : ℝ) : ℂ) * I) ∈ H := by
    show (0 : ℝ) < ((((2 * Real.sqrt ((s : ℝ) - sB) : ℝ) : ℂ) * I)).im
    simpa using Real.sqrt_pos.2 hr
  refine ⟨?_, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWc hW0 hu hwH⟩
  simp only [relCurve, relClock_of_ge hsB hτs hs.le, YuanCorollary13.extTrace,
    show ¬ (u + ((s : ℝ) - sB) ≤ u) by linarith, ↓reduceIte, add_sub_cancel_left]
  exact WangWu.extendFrom_fwdMapInv_eq hWc hW0 hu hwH

theorem continuous_relCurve (hWc : Continuous Wr) (hW0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hτc : ContinuousOn τ (Icc 0 sB)) (hτm : MonotoneOn τ (Icc 0 sB)) (hτ0 : τ 0 = 0) :
    Continuous (relCurve Wr ηr τ sB u hsB.le) := by
  have hext := (WangWu.isLoewnerTraceLT_of_isLoewnerTrace hηr (u + 1)).isLoewnerTrace_ext hWc hW0 hu
    (by linarith)
  refine hext.2.1.comp_continuous ((continuous_relClock hsB hτc).comp continuous_subtype_val) fun s => ?_
  exact relClock_nonneg hsB hτm hτ0 s

theorem relCurve_zero (hηr : IsLoewnerTrace Wr ηr) (hτm : MonotoneOn τ (Icc 0 sB)) (hτs : τ sB = u)
    (hτ0 : τ 0 = 0) : relCurve Wr ηr τ sB u hsB.le 0 = 0 := by
  rw [relCurve_of_le hsB hτm hτs (show ((0 : ℝ≥0) : ℝ) ≤ sB from hsB.le), NNReal.coe_zero, hτ0, hηr.1]

theorem tendsto_norm_relCurve (hWc : Continuous Wr) (hW0 : Wr 0 = 0) (hu : 0 ≤ u) (hτs : τ sB = u) :
    Tendsto (fun s => ‖relCurve Wr ηr τ sB u hsB.le s‖) atTop atTop := by
  obtain ⟨M, hM⟩ := (ZhanGT4.isMapOut_fwdMap_gen hWc hu).exists_norm_sub_le (isHPHull_fwdHull hWc hu)
  have h1 : Tendsto (fun s : ℝ≥0 => (s : ℝ) - sB) atTop atTop :=
    tendsto_atTop_add_const_right _ (-sB) (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hlim : Tendsto (fun s : ℝ≥0 => 2 * Real.sqrt ((s : ℝ) - sB) + -(|Wr u| + M)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((Real.tendsto_sqrt_atTop.comp h1).const_mul_atTop two_pos)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [h1.eventually (eventually_gt_atTop 0)] with s hs
  have hs' : sB < (s : ℝ) := sub_pos.1 hs
  obtain ⟨he, hm⟩ := relCurve_of_gt hsB hWc hW0 hu hτs hs'
  rw [he]
  set w : ℂ := ((2 * Real.sqrt ((s : ℝ) - sB) : ℝ) : ℂ) * I with hwdef
  have hwH : w ∈ H := by
    show (0 : ℝ) < w.im
    simpa [hwdef] using Real.sqrt_pos.2 hs
  have h2 := hM _ hm
  rw [QuantumZipper.RS.fwdMap_fwdMapInv hWc hW0 hu hwH] at h2
  have hw : ‖w‖ = 2 * Real.sqrt ((s : ℝ) - sB) := by
    rw [hwdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  have h3 : ‖w‖ ≤ ‖fwdMapInv Wr u w‖ + ‖((Wr u : ℝ) : ℂ)‖ + ‖w + ((Wr u : ℝ) : ℂ) - fwdMapInv Wr u w‖ := by
    calc ‖w‖ = ‖fwdMapInv Wr u w - ((Wr u : ℝ) : ℂ) + (w + ((Wr u : ℝ) : ℂ) - fwdMapInv Wr u w)‖ := by ring_nf
      _ ≤ ‖fwdMapInv Wr u w - ((Wr u : ℝ) : ℂ)‖ + ‖w + ((Wr u : ℝ) : ℂ) - fwdMapInv Wr u w‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs, hw] at h3
  linarith

variable (hτc : ContinuousOn τ (Icc 0 sB)) (hτm : StrictMonoOn τ (Icc 0 sB)) (hτ0 : τ 0 = 0) (hτs : τ sB = u)

include hτc hτm hτ0 hτs in
/-- The relative curve on `[0, s]` traces `ηr([0, τ s])`. -/
theorem image_relCurve {s : ℝ} (hs : s ∈ Icc 0 sB) :
    (fun r : ℝ => relCurve Wr ηr τ sB u hsB.le r.toNNReal) '' Icc 0 s = ηr '' Icc 0 (τ s) := by
  have h1 : (fun r : ℝ => relCurve Wr ηr τ sB u hsB.le r.toNNReal) '' Icc 0 s = (fun r => ηr (τ r)) '' Icc 0 s := by
    refine image_congr fun r hr => ?_
    have hr0 : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1
    rw [relCurve_of_le hsB hτm.monotoneOn hτs (by rw [hr0]; exact hr.2.trans hs.2), hr0]
  have h2 : τ '' Icc 0 s = Icc (τ 0) (τ s) :=
    (hτc.mono (Icc_subset_Icc_right hs.2)).image_Icc_of_monotoneOn hs.1
      (hτm.monotoneOn.mono (Icc_subset_Icc_right hs.2))
  rw [h1, ← image_image, h2, hτ0]

include hτc hτm hτ0 hτs in
/-- **The capacity clock of the relative curve is `τ` on `[0, sB]`.** -/
theorem capClock_relCurve (hWc : Continuous Wr) (hηr : IsLoewnerTrace Wr ηr) {s : ℝ} (hs : s ∈ Icc 0 sB) :
    Sec7.Lemma71C.capClock (fun r : ℝ => relCurve Wr ηr τ sB u hsB.le r.toNNReal) s = τ s := by
  have hτnn : 0 ≤ τ s := hτ0 ▸ hτm.monotoneOn ⟨le_rfl, hsB.le⟩ hs hs.1
  unfold Sec7.Lemma71C.capClock
  rw [image_relCurve hsB hτc hτm hτ0 hτs hs, ← hηr.2.2 _ hτnn, ZhanGT4.A1Ref.hcapSet_fwdHull hWc hτnn]
  ring

include hτc hτm hτ0 hτs in
/-- **The chain core of the relative curve** (driver `Wr`, trace `ηr`, on `[0, sB]`). -/
theorem relChainCore_relCurve (hWc : Continuous Wr) (hW0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) :
    Mn.RelChainCore (relCurve Wr ηr τ sB u hsB.le) sB Wr ηr := by
  have hcap := fun {s : ℝ} (hs : s ∈ Icc 0 sB) => capClock_relCurve hsB hτc hτm hτ0 hτs hWc hηr hs
  refine ⟨hWc, hW0, hηr, by rw [hcap ⟨le_rfl, hsB.le⟩, hτ0], fun a ha b hb hab => ?_,
    hτc.congr fun s hs => hcap hs, fun s hs => ⟨?_, ?_, ?_⟩⟩
  · rw [hcap ha, hcap hb]; exact hτm ha hb hab
  · rw [hcap hs]; exact hτ0 ▸ hτm.monotoneOn ⟨le_rfl, hsB.le⟩ hs hs.1
  · have hr0 : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    rw [hcap hs, relCurve_of_le hsB hτm.monotoneOn hτs (by rw [hr0]; exact hs.2), hr0]
  · have hτnn : 0 ≤ τ s := hτ0 ▸ hτm.monotoneOn ⟨le_rfl, hsB.le⟩ hs hs.1
    rw [hcap hs, hηr.2.2 _ hτnn, ← image_relCurve hsB hτc hτm hτ0 hτs hs, Mn.image_toNNReal_Icc _ hs.1]

end InteractingSLE.Theorem14.SB.Sx
