/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndHLaw

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the frozen time `σ = 0`, identification

Packet PROVE-A1-G3LAW2. At the frozen time `0` the frozen large hull is empty and its chart is the identity on `ℍ`, so
the canonical image of the small curve is the small curve itself (deterministic, any image start `xj`):

* `physMap_zero_eq`, `physHull_zero_eq`, `physHull_subset_H`: the chart at time `0` is the identity on `ℍ`, the hull is
  empty;
* **`isGoodTime_zero_time`**: every positive horizon before the image curve's lifetime is good;
* **`imgClk_imgDrv_zero_time`**: the canonical clock is the identity on `[0, S]` and the canonical image driver is the
  image curve's driver translated by `xj`;
* **`exists_ownData_zero_time`**: an image chain of the image curve against the empty frozen hull exists, and every one
  has the identity clock and the image curve's own driver on `[0, S]`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref

section ZeroTime

variable {xj : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞}

/-- At time `0` the physical chart is the identity on `ℍ` (centred driver). -/
theorem physMap_zero_eq (c : ℝ) (hk0 : wk 0 = 0) {z : ℂ} (hz : z ∈ H) : physMap c wk 0 z = z := by
  have hz' : z - (c : ℂ) ≠ (wk 0 : ℂ) := by
    intro he
    have him : (z - (c : ℂ)).im = (wk 0 : ℂ).im := by rw [he]
    have h1 : (0 : ℝ) < z.im := hz
    simp only [sub_im, ofReal_im, sub_zero] at him
    linarith
  simp only [physMap, QuantumZipper.B5.fwdMap_zero_time wk hz', hk0]
  push_cast
  ring

/-- A physical hull lies in `ℍ`. -/
theorem physHull_subset_H (c : ℝ) (w : ℝ → ℝ) (t : ℝ) : physHull c w t ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  have h1 : (0 : ℝ) < z.im := (QuantumZipper.fwdHull_mono (W := w)).2 t hz
  show 0 < (z + (c : ℂ)).im
  simpa using h1

/-- At time `0` the physical hull is empty (driver continuous a little beyond `0`). -/
theorem physHull_zero_eq (c : ℝ) {τ' : ℝ} (hτ' : 0 < τ') (hk : ContinuousOn wk (Icc 0 τ')) :
    physHull c wk 0 = ∅ := by
  have hV : Continuous (stopDrv wk τ') := continuous_stopDrv hk hτ'.le
  have he : fwdHull wk 0 = fwdHull (stopDrv wk τ') 0 :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt le_rfl hτ' (stopDrv_eqOn wk τ').symm
  rw [physHull, he, QuantumZipper.RS.fwdHull_zero_eq_empty hV, image_empty]

/-- **At the frozen time `0` every positive horizon before the image curve's lifetime is good.** -/
theorem isGoodTime_zero_time {τ' : ℝ} (hτ' : 0 < τ') (hk : ContinuousOn wk (Icc 0 τ')) {S : ℝ} (hS : 0 < S)
    (hSζ : ENNReal.ofReal S < ζj) : A1Ref.IsGoodTime xj wj ζj 0 wk 0 S := by
  refine ⟨hS, lt_of_lt_of_le hSζ (le_min le_rfl (le_iInf₂ fun s hs => ?_))⟩
  rw [physHull_zero_eq 0 hτ' hk, closure_empty, inter_empty] at hs
  exact absurd hs not_nonempty_empty

variable (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
  {τ' : ℝ} (hτ' : 0 < τ') (hk : ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0)

include hj hj0 hτ' hk hk0

/-- **At the frozen time `0` the canonical clock is the identity and the canonical image driver is the image curve's
driver translated by `xj`**, on `[0, S]` for a positive horizon `S` before the image curve's lifetime. -/
theorem imgClk_imgDrv_zero_time {S : ℝ} (hS : 0 < S) (hSζ : ENNReal.ofReal S < ζj) :
    (∀ t ∈ Icc (0 : ℝ) S, A1Ref.imgClk xj wj 0 wk 0 t = t) ∧
      ∀ t ∈ Icc (0 : ℝ) S, A1Ref.imgDrv xj wj ζj 0 wk 0 t = wj t + xj := by
  have hgood := isGoodTime_zero_time (xj := xj) (wj := wj) hτ' hk hS hSζ
  obtain ⟨T', hST', hcT'⟩ := A1SeedGeom.exists_continuousOn_beyond_of_isGoodTime hj hgood
  set V := stopDrv wj T' with hVdef
  have hT'0 : 0 ≤ T' := hS.le.trans hST'.le
  have hVc : Continuous V := continuous_stopDrv hcT' hT'0
  have hVe : EqOn wj V (Icc 0 T') := (stopDrv_eqOn wj T').symm
  have hV0 : V 0 = 0 := by rw [← hVe ⟨le_rfl, hT'0⟩, hj0]
  have hPH : ∀ t ∈ Icc (0 : ℝ) S, physHull xj wj t = physHull xj V t := fun t ht =>
    physHull_congr ht.1 (ht.2.trans_lt hST') hVe
  have himg : ∀ t ∈ Icc (0 : ℝ) S, physMap 0 wk 0 '' physHull xj wj t = physHull xj wj t := fun t _ => by
    conv_rhs => rw [← image_id (physHull xj wj t)]
    exact image_congr fun z hz => physMap_zero_eq 0 hk0 (physHull_subset_H xj wj t hz)
  have hclk : ∀ t ∈ Icc (0 : ℝ) S, A1Ref.imgClk xj wj 0 wk 0 t = t := by
    intro t ht
    unfold A1Ref.imgClk
    split_ifs with hpos
    · rw [himg t ht, hPH t ht, physHull_eq_fwdHull,
        hcapSet_fwdHull (W := fun r => V r + xj) (hVc.add continuous_const) ht.1]
      ring
    · exact (le_antisymm (not_lt.1 hpos) ht.1).symm
  have hIs : A1Ref.IsImgDrvOn xj wj 0 wk 0 S (fun σ => V σ + xj) := by
    refine ⟨hVc.add continuous_const, ?_, fun t ht => ?_⟩
    · have hev : physMap 0 wk 0 =ᶠ[𝓝[H] (xj : ℂ)] id :=
        eventually_nhdsWithin_of_forall fun z hz => physMap_zero_eq 0 hk0 hz
      have h1 : Tendsto (id : ℂ → ℂ) (𝓝[H] (xj : ℂ)) (𝓝 (xj : ℂ)) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      have h2 : (((V 0 + xj : ℝ)) : ℂ) = (xj : ℂ) := by rw [hV0, zero_add]
      rw [h2]
      exact h1.congr' hev.symm
    · rw [hclk t ht, himg t ht, hPH t ht, physHull_eq_fwdHull]
  have he := A1Ref.imgDrv_eqOn hj hj0 ⟨τ', hτ', hk⟩ hk0 le_rfl hgood hIs
  rw [hclk S ⟨hS.le, le_rfl⟩] at he
  refine ⟨hclk, fun t ht => ?_⟩
  rw [he ht]
  show V t + xj = wj t + xj
  rw [← hVe ⟨ht.1, ht.2.trans hST'.le⟩]

/-- **An image chain against the empty frozen hull exists, with the identity clock and the image curve's own driver**:
for a continuous driver `W` agreeing with `wj` on `[0, S]`, there are `(a, W')` with `OwnData` in the image curve's
frame (hull `physHull (0 − xj) wk 0 = ∅`, chart `physMap (0 − xj) wk 0`), `a = id` and `W' = wj` on `[0, S]`. -/
theorem exists_ownData_zero_time {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0) {S : ℝ} (hS : 0 < S)
    (hSζ : ENNReal.ofReal S < ζj) (hWj : EqOn W wj (Icc 0 S)) :
    ∃ a W' : ℝ → ℝ, OwnData W (physHull (0 - xj) wk 0) (physMap (0 - xj) wk 0) S a W' ∧
      (∀ t ∈ Icc (0 : ℝ) S, a t = t) ∧ ∀ t ∈ Icc (0 : ℝ) S, W' t = wj t := by
  have hkk : ∃ τ'', (0 : ℝ) < τ'' ∧ ContinuousOn wk (Icc 0 τ'') := ⟨τ', hτ', hk⟩
  have hA := isHPHull_physHull_loc (x := 0 - xj) le_rfl hkk
  have hφ := isMapOut_physMap_loc (x := 0 - xj) le_rfl hkk hk0
  have hd : Disjoint (closure (physHull (0 - xj) wk 0)) (closure (fwdHull W S)) := by
    rw [physHull_zero_eq (0 - xj) hτ' hk, closure_empty]
    exact empty_disjoint _
  obtain ⟨a, W', hown⟩ := exists_ownData hWc hW0 hS hA hφ hd
  have hgood := isGoodTime_zero_time (xj := xj) (wj := wj) hτ' hk hS hSζ
  obtain ⟨hclkA, hdrvA⟩ := imgClk_imgDrv_eqOn_of_ownData hown hWj hj hj0 hkk hk0 le_rfl hgood
  obtain ⟨hclk0, hdrv0⟩ := imgClk_imgDrv_zero_time (xj := xj) hj hj0 hτ' hk hk0 hS hSζ
  refine ⟨a, W', hown, fun t ht => (hclkA ht).symm.trans (hclk0 t ht), fun t ht => ?_⟩
  have haS : a S = S := (hclkA ⟨hS.le, le_rfl⟩).symm.trans (hclk0 S ⟨hS.le, le_rfl⟩)
  have h1 := hdrvA (show t ∈ Icc (0 : ℝ) (a S) by rw [haS]; exact ht)
  rw [hdrv0 t ht] at h1
  simp only at h1
  linarith only [h1]

end ZeroTime

end InteractingSLE.ZhanGT4.A1G3L2
