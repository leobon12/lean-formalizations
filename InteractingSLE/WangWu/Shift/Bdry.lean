/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Basic
import InteractingSLE.WangWu.ReverseContactBdryIdent

/-!
# The height-shifted two-slit law, part 2: the boundary correspondence of the two-slit chart

Packet PROVE-WW-B26 (the deterministic half; PROVE-WW-B14's `ReverseContactBdryLimit`/`ReverseContactBdryIdent` with
the height shift). Setting of `ReverseContactBdryLimit`: the forward slit `A = α((0, t])`, the reflected reverse slit
`G = R(β((0, s]))`, the chart `Ψ = revChart Wβ s` of `ℍ \ G`, an image trace `η'` of `W'` with `K'_T = Ψ(A)`, and the
two-slit chart `Φ = Ψ⁻¹ ∘ F'_T`. In the shifted setting the uncentred union mean `M` (of the forward field `h`)
satisfies `M − m_A → 0` on `A ∪ ℝ` and `M + m_G → δλ` on `G ∪ (ℝ \ {0})`, where `m_G = revSlitMean (r_L + δ) (r_R − δ)`
is the explicit mean of the reverse word `(r_R − δ; r_L + δ)` read through `R` (the reverse line is the level line of
`X = h − δλ`).

* `chartMeanW ρL ρR`: the explicit two-force mean in the image chart with arbitrary weights (B14's `chartMean rL rR` is
  `chartMeanW ![rL, −rL] ![rR, −rR]`);
* `tendsto_twoSlitChart_of_real_shift`, `tendsto_twoSlitChart_of_mem_H_shift`;
* **`exists_finite_tendsto_twoSlitChart_shift`**: `M ∘ Φ − chartMeanW ![r_L, −r_L − δ] ![r_R, −r_R + δ] → 0` at
  every real point outside a finite set.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.WangWu

open MartChar.RealFlow Shift

/-- **The explicit two-force mean in the image chart with arbitrary weights**: forces at `(a_L, b_L; a_R, b_R)`, the
images of `0∓` and of `Ψ(∞∓) = −1/v_R, −1/v_L`. -/
def chartMeanW (ρL ρR : Fin 2 → ℝ) (W : ℝ → ℝ) (T vL vR : ℝ) (y : ℂ) : ℝ :=
  condMean ρL ρR ![chartAL W T, chartBL W T vR] ![chartAR W T, chartBR W T vL] y

theorem chartMean_eq_chartMeanW (rL rR : ℝ) (W : ℝ → ℝ) (T vL vR : ℝ) :
    chartMean rL rR W T vL vR = chartMeanW ![rL, -rL] ![rR, -rR] W T vL vR := rfl

variable {Wα Wβ W' : ℝ → ℝ} {α β η' : ℝ → ℂ} {t s T : ℝ}

/-- **Boundary limits through the two-slit chart at real points with a real boundary image** (the points of `ℝ` and
of the reversed slit `G` seen from `Ψ`-coordinates). -/
theorem tendsto_twoSlitChart_of_real_shift (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hs : 0 < s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t)
    {rL rR δ vL vR : ℝ} (hvL : vL < 0) (hvR : 0 < vR) {M : ℂ → ℝ}
    (hG : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}),
      Tendsto (fun z => M z + revSlitMean (rL + δ) (rR - δ) Wβ s vL vR z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 (δ * wwLambda)))
    {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W' T) x = r)
    (hq : extendFrom H (fwdMapInv Wβ s) ((-r⁻¹ : ℝ) : ℂ) ≠ 0)
    (hxL : x ≠ chartBL W' T vR) (hxaL : x ≠ chartAL W' T) (hx0 : x ≠ 0) (hxaR : x ≠ chartAR W' T)
    (hxR : x ≠ chartBR W' T vL) :
    Tendsto (fun y => M (twoSlitChart Wβ s W' T y) - chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T vL vR y)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨hxr, -⟩ := eq_re_fwdMap_of_extendFrom_eq hη' hη'p hW' hW'0 hT.le hr hF
  set ξ : ℝ := -r⁻¹ with hξ
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hξH : (ξ : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (ξ : ℂ).im by simp
  have h1 : Tendsto (fwdMapInv W' T) (𝓝[H] (x : ℂ)) (𝓝[H] (r : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy⟩
    have := (hη'.hasBdryLimits hW' hW'0 hT.le).tendsto hxH
    rwa [hF] at this
  have hRr : negInv (r : ℂ) = (ξ : ℂ) := by rw [negInv, hξ]; push_cast; ring
  have h2 : Tendsto (fun y => negInv (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝[H] (ξ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hRr]
      exact (continuousAt_negInv (by exact_mod_cast hr)).tendsto.comp (tendsto_nhdsWithin_iff.1 h1).1
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy)
  set q := extendFrom H (fwdMapInv Wβ s) (ξ : ℂ) with hqdef
  have h3 : Tendsto (fun y => fwdMapInv Wβ s (negInv (fwdMapInv W' T y))) (𝓝[H] (x : ℂ)) (𝓝 q) :=
    ((hβ.hasBdryLimits hWβ hWβ0 hs.le).tendsto hξH).comp h2
  have h4 : Tendsto (twoSlitChart Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (negInv q)) :=
    (continuousAt_negInv hq).tendsto.comp h3
  have h4' : Tendsto (twoSlitChart Wβ s W' T) (𝓝[H] (x : ℂ))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] (negInv q)) :=
    tendsto_nhdsWithin_iff.2 ⟨h4, eventually_nhdsWithin_of_forall fun y hy =>
      twoSlitChart_mem hWβ hWβ0 hs.le hW' hW'0 hT.le hK' hy⟩
  have hqmem : negInv q ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}) := by
    have hqH : q ∈ Hbar := extendFrom_mem_Hbar hβ hWβ hWβ0 hs.le hξH
    have hqn := hβ.extendFrom_not_mem hWβ hWβ0 hs.le (x := (ξ : ℂ)) (by simp)
    by_cases hqH' : q ∈ H
    · left
      refine ⟨q, ?_, rfl⟩
      by_contra hK
      exact hqn ⟨hqH', hK⟩
    · right
      have hqim : q.im = 0 := le_antisymm (not_lt.1 hqH') hqH
      refine ⟨?_, fun h0 => hq ?_⟩
      · show (negInv q).im = 0
        simp [negInv, Complex.inv_im, hqim]
      · have h0' : negInv q = 0 := h0
        rw [negInv, neg_eq_zero, inv_eq_zero] at h0'
        exact h0'
  have hlimG := (hG _ hqmem).comp h4'
  -- the exact identity for the reverse mean
  have hrev : ∀ y ∈ H, revSlitMean (rL + δ) (rR - δ) Wβ s vL vR (twoSlitChart Wβ s W' T y) =
      condMean (fun _ : Fin 1 => rR - δ) (fun _ : Fin 1 => rL + δ) (fun _ => vL) (fun _ => vR)
        (negInv (fwdMapInv W' T y)) := by
    intro y hy
    simp only [revSlitMean, twoSlitChart, revChartInv, negInv_negInv']
    rw [QuantumZipper.RS.fwdMap_fwdMapInv hWβ hWβ0 hs.le
      (negInv_mem_H (QuantumZipper.RS.fwdMapInv_mem_H hW' hW'0 hT.le hy))]
  -- positions of `r`, `ξ`, `x`
  have hξ0 : ξ ≠ 0 := by simp [hξ, hr]
  have hr_of : ∀ c : ℝ, ξ = c → r = -c⁻¹ := fun c h => by
    rw [hξ] at h
    have : r⁻¹ = -c := by linarith
    rw [← inv_inv r, this, inv_neg]
  have hξL : ξ ≠ vL := fun h => hxR (by rw [hxr, hr_of vL h, chartBR])
  have hξR : ξ ≠ vR := fun h => hxL (by rw [hxr, hr_of vR h, chartBL])
  have hsol := fun (y : ℝ) (hy : y ≠ 0) => exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hy hT.le
  obtain ⟨vr, hvr⟩ := hsol r hr
  obtain ⟨vb, hvb⟩ := hsol (-vR⁻¹) (neg_ne_zero.2 (inv_ne_zero hvR.ne'))
  obtain ⟨vc, hvc⟩ := hsol (-vL⁻¹) (neg_ne_zero.2 (inv_ne_zero hvL.ne))
  have hbneg : -vR⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hvR)
  have hcpos : 0 < -vL⁻¹ := neg_pos.2 (inv_lt_zero.2 hvL)
  have hrneg : 0 < ξ → r < 0 := fun h => by
    rw [hξ, neg_pos] at h; exact inv_lt_zero.1 h
  have hrpos : ξ < 0 → 0 < r := fun h => by
    rw [hξ, neg_lt_zero] at h; exact inv_pos.1 h
  have hA : 0 < ξ → ξ < vR → x < chartBL W' T vR := fun h0 h => by
    have hr0 := hrneg h0
    have hrb : r < -vR⁻¹ := (neg_inv_lt_iff_of_neg_of_pos hr0 hvR).1 h
    rw [hxr, chartBL]
    exact re_fwdMap_lt_re_fwdMap hW' hW'0 hT.le hrb (Or.inr hbneg) hvr hvb
  have hB : vR < ξ → chartBL W' T vR < x ∧ x < chartAL W' T := fun h => by
    have hr0 := hrneg (hvR.trans h)
    have hrb : -vR⁻¹ < r := by
      refine lt_of_le_of_ne (not_lt.1 fun h' => ?_) fun e => hξR ?_
      · exact absurd ((neg_inv_lt_iff_of_neg_of_pos hr0 hvR).2 h') (not_lt.2 h.le)
      · rw [hξ, ← e, inv_neg, inv_inv, neg_neg]
    refine ⟨?_, lt_of_le_of_ne ?_ hxaL⟩
    · rw [hxr, chartBL]
      exact re_fwdMap_lt_re_fwdMap hW' hW'0 hT.le hrb (Or.inr hr0) hvb hvr
    · rw [hxr, chartAL]
      exact re_fwdMap_le_neg_rightImg hW' hW'0 hT.le hr0 hvr
  have hC : ξ < vL → chartAR W' T < x ∧ x < chartBR W' T vL := fun h => by
    have hr0 := hrpos (h.trans hvL)
    have hrc : r < -vL⁻¹ := (neg_inv_lt_iff_of_pos_of_neg hr0 hvL).1 h
    refine ⟨lt_of_le_of_ne ?_ (Ne.symm hxaR), ?_⟩
    · rw [hxr, chartAR]
      exact rightImg_sub_le_re_fwdMap hW' hW'0 hT.le hr0 hvr
    · rw [hxr, chartBR]
      exact re_fwdMap_lt_re_fwdMap hW' hW'0 hT.le hrc (Or.inl hr0) hvr hvc
  have hD : vL < ξ → ξ < 0 → chartBR W' T vL < x := fun h h0 => by
    have hr0 := hrpos h0
    have hrc : -vL⁻¹ < r := by
      refine lt_of_le_of_ne (not_lt.1 fun h' => ?_) fun e => hξL ?_
      · exact absurd ((neg_inv_lt_iff_of_pos_of_neg hr0 hvL).2 h') (not_lt.2 h.le)
      · rw [hξ, ← e, inv_neg, inv_inv, neg_neg]
    rw [hxr, chartBR]
    exact re_fwdMap_lt_re_fwdMap hW' hW'0 hT.le hrc (Or.inl hcpos) hvc hvr
  have hmatch := fbd_add_fbd_eq_shift (rL := rL) (rR := rR) (δ := δ)
    (chartBL_lt hη' hη'p hW' hW'0 hT.le hvR) (chartAL_nonpos hW' hT.le) (chartAR_nonneg hW' hT.le)
    (chartAR_lt hη' hη'p hW' hW'0 hT.le hvL) hξ0 hξL hξR hA hB hC hD
  -- the two boundary values
  have hcβ := (isBoundedHarmonicExtension_condMean (fun _ : Fin 1 => rR - δ) (fun _ : Fin 1 => rL + δ)
    (vL := fun _ => vL) (vR := fun _ => vR) (fun _ => hvL.le) (fun _ => hvR.le)).2.2 ξ
    (forceJumpSet_one hξ0 hξL hξR)
  have h5 : Tendsto (fun y => revSlitMean (rL + δ) (rR - δ) Wβ s vL vR (twoSlitChart Wβ s W' T y)) (𝓝[H] (x : ℂ))
      (𝓝 (forceBoundaryData 4 (fun _ : Fin 1 => rR - δ) (fun _ : Fin 1 => rL + δ) (fun _ => vL) (fun _ => vR)
        ξ)) := by
    refine (hcβ.comp h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hrev y hy).symm
  have hvL' : ∀ i, (![chartAL W' T, chartBL W' T vR] : Fin 2 → ℝ) i ≤ 0 := by
    intro i; fin_cases i
    · exact chartAL_nonpos hW' hT.le
    · exact (chartBL_lt hη' hη'p hW' hW'0 hT.le hvR).le.trans (chartAL_nonpos hW' hT.le)
  have hvR' : ∀ i, 0 ≤ (![chartAR W' T, chartBR W' T vL] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact chartAR_nonneg hW' hT.le
    · exact (chartAR_nonneg hW' hT.le).trans (chartAR_lt hη' hη'p hW' hW'0 hT.le hvL).le
  have h6 := (isBoundedHarmonicExtension_condMean ![rL, -rL - δ] ![rR, -rR + δ] hvL' hvR').2.2 x
    (forceJumpSet_two hx0 hxaL hxL hxaR hxR)
  have h7 := (hlimG.sub h5).sub h6
  have hval : δ * wwLambda - forceBoundaryData 4 (fun _ : Fin 1 => rR - δ) (fun _ : Fin 1 => rL + δ)
      (fun _ => vL) (fun _ => vR) ξ - forceBoundaryData 4 ![rL, -rL - δ] ![rR, -rR + δ]
      ![chartAL W' T, chartBL W' T vR] ![chartAR W' T, chartBR W' T vL] x = 0 := by linarith
  rw [hval] at h7
  refine h7.congr fun y => ?_
  simp only [Function.comp_apply, chartMeanW]
  ring

/-- **Boundary limits through the two-slit chart at the sides of the forward slit.** -/
theorem tendsto_twoSlitChart_of_mem_H_shift (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hβp : IsProperArc β) (hs : 0 < s) (hG : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {rL rR δ vL vR : ℝ} (hvL : vL < 0) (hvR : 0 < vR) {M : ℂ → ℝ}
    (hA : ∀ z₀ ∈ fwdHull Wα t ∪ {z : ℂ | z.im = 0},
      Tendsto (fun z => M z - fwdSlitMean rL rR Wα t z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀)
        (𝓝 0))
    {x : ℝ} (hFH : extendFrom H (fwdMapInv W' T) x ∈ H) (hx0 : x ≠ 0) :
    Tendsto (fun y => M (twoSlitChart Wβ s W' T y) - chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T vL vR y)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set C := H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) with hCdef
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  set r := extendFrom H (fwdMapInv W' T) x with hr
  -- `r = Ψ(α(u))` with `0 < u < t`
  have hrK : r ∈ fwdHull W' T := by
    by_contra hK
    exact hη'.extendFrom_not_mem hW' hW'0 hT.le (x := (x : ℂ)) (by simp) ⟨hFH, hK⟩
  rw [hK', fwdHull_eq_image_Ioc hα hαp ht.le] at hrK
  obtain ⟨_, ⟨u, hu, rfl⟩, hru⟩ := hrK
  have hut : u < t := by
    refine lt_of_le_of_ne hu.2 fun hut => hx0 ?_
    rw [hut, ← htip] at hru
    exact eq_zero_of_extendFrom_eq_tip hη' hη'p hW' hW'0 hT hru.symm
  have hαA : α u ∈ fwdHull Wα t := by
    rw [fwdHull_eq_image_Ioc hα hαp ht.le]; exact ⟨u, hu, rfl⟩
  have hαuG : α u ∈ H \ negInv '' fwdHull Wβ s :=
    ⟨hαp.mem_H u hu.1, fun h => disjoint_left.1 hdisj hαA h⟩
  -- `Φ(y) → α(u)` within `C`
  have hΦlim : Tendsto (twoSlitChart Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝[C] (α u)) := by
    have h1 : Tendsto (fwdMapInv W' T) (𝓝[H] (x : ℂ)) (𝓝 r) := (hη'.hasBdryLimits hW' hW'0 hT.le).tendsto hxH
    have hrH : r ∈ H := hFH
    have h2 : ContinuousAt (revChartInv Wβ s) r :=
      (continuousOn_revChartInv hWβ hWβ0 hs.le).continuousAt (QuantumZipper.isOpen_H.mem_nhds hrH)
    have h3 := h2.tendsto.comp h1
    rw [← hru, revChartInv_revChart hWβ hWβ0 hs.le hαuG] at h3
    exact tendsto_nhdsWithin_iff.2 ⟨h3, eventually_nhdsWithin_of_forall fun y hy =>
      twoSlitChart_mem hWβ hWβ0 hs.le hW' hW'0 hT.le hK' hy⟩
  have hlimA := (hA (α u) (Or.inl hαA)).comp hΦlim
  -- the position of `x`
  have hxL : chartAL W' T < x := neg_rightImg_sub_lt_of_extendFrom_mem_H hη' hW' hW'0 hT.le hFH
  have hxR : x < chartAR W' T := lt_rightImg_sub_of_extendFrom_mem_H hη' hW' hW'0 hT.le hFH
  have hbL := chartBL_lt hη' hη'p hW' hW'0 hT.le hvR (vR := vR)
  have hbR := chartAR_lt hη' hη'p hW' hW'0 hT.le hvL (vL := vL)
  have hvL' : ∀ i, (![chartAL W' T, chartBL W' T vR] : Fin 2 → ℝ) i ≤ 0 := by
    intro i; fin_cases i
    · exact chartAL_nonpos hW' hT.le
    · exact hbL.le.trans (chartAL_nonpos hW' hT.le)
  have hvR' : ∀ i, 0 ≤ (![chartAR W' T, chartBR W' T vL] : Fin 2 → ℝ) i := by
    intro i; fin_cases i
    · exact chartAR_nonneg hW' hT.le
    · exact (chartAR_nonneg hW' hT.le).trans hbR.le
  have hc := (isBoundedHarmonicExtension_condMean ![rL, -rL - δ] ![rR, -rR + δ] hvL' hvR').2.2 x
    (forceJumpSet_two hx0 hxL.ne' (hbL.trans hxL).ne' hxR.ne (hxR.trans hbR).ne)
  -- the common value `−λ` or `+λ`
  set ℓ := forceBoundaryData 4 ![rL, -rL - δ] ![rR, -rR + δ] ![chartAL W' T, chartBL W' T vR]
    ![chartAR W' T, chartBR W' T vL] x with hℓ
  have hsides := fun {y : ℂ} (hy : y ∈ H) => fwdMap_twoSlitChart_mem_sides hα hαp hWα hWα0 ht hWβ hWβ0 hβ hβp
    hs hG hdisj hW' hW'0 hη' hη'p hT hK' htip hy
  have hΓ := isProperArc_sepArc hα hαp hWα hWα0 ht hWβ hWβ0 hβ hβp hs hdisj hW' hW'0 hη' hT hK' htip
  have hαL := chartAL_nonpos hWα ht.le
  have hαR := chartAR_nonneg hWα ht.le
  have hmeanA : Tendsto (fun y => fwdSlitMean rL rR Wα t (twoSlitChart Wβ s W' T y)) (𝓝[H] (x : ℂ)) (𝓝 ℓ) := by
    rw [Filter.tendsto_iff_ultrafilter]
    intro U hU
    have hUΦ : (U.map (twoSlitChart Wβ s W' T) : Filter ℂ) ≤ 𝓝[C] (α u) := hΦlim.mono_left hU
    obtain ⟨x₁, hx₁0, hFx₁, hlim₁, -⟩ := exists_real_tendsto_fwdMap hα hαp hWα hWα0 hu.1 hut
      (S := C) (fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl h)⟩) (U.map (twoSlitChart Wβ s W' T)) hUΦ
    have hFx₁H : extendFrom H (fwdMapInv Wα t) x₁ ∈ H := by rw [hFx₁]; exact hαp.mem_H u hu.1
    have hx₁L : chartAL Wα t < x₁ := neg_rightImg_sub_lt_of_extendFrom_mem_H hα hWα hWα0 ht.le hFx₁H
    have hx₁R : x₁ < chartAR Wα t := lt_rightImg_sub_of_extendFrom_mem_H hα hWα hWα0 ht.le hFx₁H
    have hcA := (isBoundedHarmonicExtension_condMean (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      (vL := fun _ => chartAL Wα t) (vR := fun _ => chartAR Wα t) (fun _ => hαL) (fun _ => hαR)).2.2 x₁
      (forceJumpSet_one hx₁0 hx₁L.ne' hx₁R.ne)
    have h1 := hcA.comp hlim₁
    have hre : Tendsto (fun y : ℂ => y.re) (U : Filter ℂ) (𝓝 x) := by
      have h0 : (U : Filter ℂ) ≤ 𝓝 (x : ℂ) := hU.trans nhdsWithin_le_nhds
      have h2 := (Complex.continuous_re.tendsto (x : ℂ)).mono_left h0
      rwa [Complex.ofReal_re] at h2
    have hUH : ∀ᶠ y in (U : Filter ℂ), y ∈ H := hU self_mem_nhdsWithin
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · -- left side
      have hev : ∀ᶠ y in (U : Filter ℂ), y ∈ H ∧ y.re < 0 :=
        hUH.and (hre.eventually (gt_mem_nhds hxneg))
      have hx₁neg : x₁ < 0 := by
        refine lt_of_le_of_ne (not_lt.1 fun hpos => hΓ.notMem_closure_leftSideOf_of_pos hpos ?_) hx₁0
        refine mem_closure_of_tendsto (tendsto_nhdsWithin_iff.1 hlim₁).1 ?_
        rw [Ultrafilter.coe_map, Filter.eventually_map]
        exact hev.mono fun y hy => (hsides hy.1).1 hy.2
      have hv1 : forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ => chartAL Wα t)
          (fun _ => chartAR Wα t) x₁ = ℓ := by
        rw [hℓ, fbd_one_neg hx₁neg, fbd_two_neg hxneg]
        simp only [show ¬ x₁ < chartAL Wα t from not_lt.2 hx₁L.le, show ¬ x < chartAL W' T from not_lt.2 hxL.le,
          show ¬ x < chartBL W' T vR from not_lt.2 (hbL.trans hxL).le, ↓reduceIte, add_zero]
      rw [hv1] at h1
      exact h1
    · -- right side
      have hev : ∀ᶠ y in (U : Filter ℂ), y ∈ H ∧ 0 < y.re :=
        hUH.and (hre.eventually (lt_mem_nhds hxpos))
      have hx₁pos : 0 < x₁ := by
        refine lt_of_le_of_ne (not_lt.1 fun hneg => hΓ.notMem_closure_rightSideOf_of_neg hneg ?_) hx₁0.symm
        refine mem_closure_of_tendsto (tendsto_nhdsWithin_iff.1 hlim₁).1 ?_
        rw [Ultrafilter.coe_map, Filter.eventually_map]
        exact hev.mono fun y hy => (hsides hy.1).2 hy.2
      have hv1 : forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ => chartAL Wα t)
          (fun _ => chartAR Wα t) x₁ = ℓ := by
        rw [hℓ, fbd_one_nonneg hx₁pos.le, fbd_two_nonneg hxpos.le]
        simp only [show ¬ chartAR Wα t ≤ x₁ from not_le.2 hx₁R, show ¬ chartAR W' T ≤ x from not_le.2 hxR,
          show ¬ chartBR W' T vL ≤ x from not_le.2 (hxR.trans hbR), ↓reduceIte, add_zero]
      rw [hv1] at h1
      exact h1
  have h := hlimA.add (hmeanA.sub hc)
  rw [sub_self, add_zero] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, chartMeanW]
  ring

/-- **The boundary correspondence of the two-slit chart** (step (S3b) of the contact step). Under the boundary
behaviour of the union mean `M` against the two explicit slit means, `M ∘ Φ − chartMean → 0` at every real point
outside a finite set (the five force positions of `chartMean` and the two points `f'_T(−1/c)`, `c` the force images of
the reverse slit, which `Φ` sends to `∞`). -/
theorem exists_finite_tendsto_twoSlitChart_shift (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β) (hs : 0 < s) (hG : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {rL rR δ vL vR : ℝ} (hvL : vL < 0) (hvR : 0 < vR) {M : ℂ → ℝ}
    (hA : ∀ z₀ ∈ fwdHull Wα t ∪ {z : ℂ | z.im = 0},
      Tendsto (fun z => M z - fwdSlitMean rL rR Wα t z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀)
        (𝓝 0))
    (hGl : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}),
      Tendsto (fun z => M z + revSlitMean (rL + δ) (rR - δ) Wβ s vL vR z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 (δ * wwLambda))) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      Tendsto (fun y => M (twoSlitChart Wβ s W' T y) - chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T vL vR y)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set e₁ : ℝ := (fwdMap W' T ((-(chartAR Wβ s)⁻¹ : ℝ) : ℂ)).re with he₁
  set e₂ : ℝ := (fwdMap W' T ((-(chartAL Wβ s)⁻¹ : ℝ) : ℂ)).re with he₂
  refine ⟨{chartBL W' T vR, chartAL W' T, 0, chartAR W' T, chartBR W' T vL, e₁, e₂}, by simp, fun x hx => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
  obtain ⟨hxbL, hxaL, hx0, hxaR, hxbR, hxe₁, hxe₂⟩ := hx
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  set r := extendFrom H (fwdMapInv W' T) x with hr
  by_cases hrH : r ∈ H
  · exact tendsto_twoSlitChart_of_mem_H_shift hα hαp hWα hWα0 ht hWβ hWβ0 hβ hβp hs hG hdisj hW' hW'0 hη' hη'p hT
      hK' htip hvL hvR hA hrH hx0
  · have hrim : r.im = 0 := le_antisymm (not_lt.1 hrH) (extendFrom_mem_Hbar hη' hW' hW'0 hT.le hxH)
    have hreq : r = ((r.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hrim])
    have hr0 : r.re ≠ 0 := by
      intro h0
      have hF0 : extendFrom H (fwdMapInv W' T) x = 0 := by rw [← hr, hreq, h0, Complex.ofReal_zero]
      rcases extendFrom_eq_zero_imp hη' hη'p hW' hW'0 hT hF0 with h | h
      · exact hxaR (by rw [chartAR]; linarith)
      · exact hxaL (by rw [chartAL]; linarith)
    have hF : extendFrom H (fwdMapInv W' T) x = (r.re : ℂ) := by rw [← hr]; exact hreq
    have hq : extendFrom H (fwdMapInv Wβ s) ((-(r.re)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      intro hq0
      have hxr := (eq_re_fwdMap_of_extendFrom_eq hη' hη'p hW' hW'0 hT.le hr0 hF).1
      have hinv : ∀ c : ℝ, -(r.re)⁻¹ = c → r.re = -c⁻¹ := fun c h => by
        have : (r.re)⁻¹ = -c := by linarith
        rw [← inv_inv r.re, this, inv_neg]
      rcases extendFrom_eq_zero_imp hβ hβp hWβ hWβ0 hs hq0 with h | h
      · exact hxe₁ (by rw [hxr, he₁, hinv (chartAR Wβ s) (by rw [chartAR]; linarith)])
      · exact hxe₂ (by rw [hxr, he₂, hinv (chartAL Wβ s) (by rw [chartAL]; linarith)])
    exact tendsto_twoSlitChart_of_real_shift hWβ hWβ0 hβ hs hW' hW'0 hη' hη'p hT hK' hvL hvR hGl hr0 hF hq hxbL hxaL
      hx0 hxaR hxbR

end InteractingSLE.WangWu
