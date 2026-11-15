/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdryChart

/-!
# Boundary limits through the two-slit chart: the real points and the reversed slit

Packet PROVE-WW-B14 (the deterministic half of the contact step's N3). Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.18 (text dump
L1611–1629). Setting (deterministic): a simple proper Loewner trace `α` of `Wα` with slit `A = α((0, t])`, a simple
proper Loewner trace `β` of `Wβ` with reflected slit `G = R(β((0, s]))`, `R(z) = −1/z`, the chart `Ψ = revChart Wβ s`
of `ℍ \ G`, and a simple proper Loewner trace `η'` of `W'` with `K'_T = Ψ(A)` (`exists_imageTrace`). The chart of the
two-slit domain `C = ℍ \ (A ∪ G)` is `Φ = Ψ⁻¹ ∘ F'_T` (`twoSlitChart`).

The candidate mean in `Ψ`-coordinates is the explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean `chartMean` with force
positions `a_L ≤ 0 ≤ a_R` (the images of `0∓` under `f'_T`) and `b_L < a_L`, `a_R < b_R` (the images of
`Ψ(∞∓) = −1/v_R, −1/v_L`).

* `twoSlitChart_mem`: `Φ` maps `ℍ` into `C`.
* **`tendsto_twoSlitChart_of_real`**: at a real point `x` off the five force positions whose boundary image
  `F̄'_T(x) = r` is real (so `x = f'_T(r)`), and whose reverse image `F̄_s(−1/r)` is not the base `0`: if `M` (the
  uncentred union mean) satisfies `M + m_G → 0` at every point of `G ∪ (ℝ \ {0})` (`m_G` the explicit reverse mean),
  then `M ∘ Φ − chartMean → 0` at `x`. Here `m_G(Φ(y)) = condMean^β(−1/F'_T(y))` exactly, and the boundary values
  match (`fbd_add_fbd_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.WangWu

open MartChar.RealFlow

/-! ### The objects -/

/-- The centred left image `a_L = L_T − W_T` of `0⁻`. -/
def chartAL (W : ℝ → ℝ) (T : ℝ) : ℝ := -rightImg (fun s => -W s) 0 T - W T

/-- The centred right image `a_R = R_T − W_T` of `0⁺`. -/
def chartAR (W : ℝ → ℝ) (T : ℝ) : ℝ := rightImg W 0 T - W T

/-- The image `b_L = f_T(−1/v_R)` of the left far force point. -/
def chartBL (W : ℝ → ℝ) (T vR : ℝ) : ℝ := (fwdMap W T ((-vR⁻¹ : ℝ) : ℂ)).re

/-- The image `b_R = f_T(−1/v_L)` of the right far force point. -/
def chartBR (W : ℝ → ℝ) (T vL : ℝ) : ℝ := (fwdMap W T ((-vL⁻¹ : ℝ) : ℂ)).re

/-- **The candidate mean in the image chart**: the explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean with forces at
`(a_L, b_L; a_R, b_R)`, as a function of the mapped-out point. -/
def chartMean (rL rR : ℝ) (W : ℝ → ℝ) (T vL vR : ℝ) (y : ℂ) : ℝ :=
  condMean ![rL, -rL] ![rR, -rR] ![chartAL W T, chartBL W T vR] ![chartAR W T, chartBR W T vL] y

/-- The explicit mean of the forward slit, `condMean^α(f_t(z))` with the true force images. -/
def fwdSlitMean (rL rR : ℝ) (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℝ :=
  condMean (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ => chartAL W t) (fun _ => chartAR W t) (fwdMap W t z)

/-- The explicit mean of the reversed slit read through `R`, `condMean^β(f_s(R z))` (forces `v_L, v_R`). -/
def revSlitMean (rL rR : ℝ) (W : ℝ → ℝ) (s vL vR : ℝ) (z : ℂ) : ℝ :=
  condMean (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (fun _ => vL) (fun _ => vR) (fwdMap W s (negInv z))

/-- The two-slit chart `Φ = Ψ⁻¹ ∘ F'_T`. -/
def twoSlitChart (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (T : ℝ) (y : ℂ) : ℂ :=
  revChartInv Wβ s (fwdMapInv W' T y)

variable {Wα Wβ W' : ℝ → ℝ} {α β η' : ℝ → ℂ} {t s T : ℝ}

/-! ### Positions of the force points -/

theorem chartAL_nonpos (hW : Continuous W') (hT : 0 ≤ T) : chartAL W' T ≤ 0 := by
  have := le_rightImg (w := fun s => -W' s) hW.neg 0 hT
  rw [chartAL]; linarith

theorem chartAR_nonneg (hW : Continuous W') (hT : 0 ≤ T) : 0 ≤ chartAR W' T := by
  have := le_rightImg hW 0 hT
  rw [chartAR]; linarith

theorem chartBL_lt (hη : IsLoewnerTrace W' η') (hγ : IsProperArc η') (hW : Continuous W') (hW0 : W' 0 = 0)
    (hT : 0 ≤ T) {vR : ℝ} (hvR : 0 < vR) : chartBL W' T vR < chartAL W' T := by
  have h1 : -vR⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hvR)
  have h2 : -vR⁻¹ < -vR⁻¹ / 2 := by linarith
  have h3 : -vR⁻¹ / 2 < 0 := by linarith
  obtain ⟨v₁, hv₁⟩ := exists_isForwardSol_of_isProperArc hη hγ hW hW0 h1.ne hT
  obtain ⟨v₂, hv₂⟩ := exists_isForwardSol_of_isProperArc hη hγ hW hW0 h3.ne hT
  have h4 := re_fwdMap_lt_re_fwdMap hW hW0 hT h2 (Or.inr h3) hv₁ hv₂
  have h5 := re_fwdMap_le_neg_rightImg hW hW0 hT h3 hv₂
  rw [chartBL, chartAL]; linarith

theorem chartAR_lt (hη : IsLoewnerTrace W' η') (hγ : IsProperArc η') (hW : Continuous W') (hW0 : W' 0 = 0)
    (hT : 0 ≤ T) {vL : ℝ} (hvL : vL < 0) : chartAR W' T < chartBR W' T vL := by
  have h1 : 0 < -vL⁻¹ := neg_pos.2 (inv_lt_zero.2 hvL)
  have h2 : -vL⁻¹ / 2 < -vL⁻¹ := by linarith
  have h3 : 0 < -vL⁻¹ / 2 := by linarith
  obtain ⟨v₁, hv₁⟩ := exists_isForwardSol_of_isProperArc hη hγ hW hW0 h3.ne' hT
  obtain ⟨v₂, hv₂⟩ := exists_isForwardSol_of_isProperArc hη hγ hW hW0 h1.ne' hT
  have h4 := re_fwdMap_lt_re_fwdMap hW hW0 hT h2 (Or.inl h3) hv₁ hv₂
  have h5 := rightImg_sub_le_re_fwdMap hW hW0 hT h3 hv₁
  rw [chartBR, chartAR]; linarith

/-! ### The chart maps into the two-slit domain -/

theorem twoSlitChart_mem (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hs : 0 ≤ s) (hW' : Continuous W')
    (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) {y : ℂ}
    (hy : y ∈ H) : twoSlitChart Wβ s W' T y ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) := by
  have hF := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 hT hy
  have hz := revChartInv_mem hWβ hWβ0 hs hF.1
  refine ⟨hz.1, fun h => ?_⟩
  rcases h with hA | hG
  · refine hF.2 ?_
    rw [hK', ← revChart_revChartInv hWβ hWβ0 hs hF.1]
    exact mem_image_of_mem _ hA
  · exact hz.2 hG

/-! ### The real points and the reversed slit -/

/-- Inverse-order bookkeeping: for `r < 0 < c`, `−1/r < c ↔ r < −1/c`. -/
theorem neg_inv_lt_iff_of_neg_of_pos {r c : ℝ} (hr : r < 0) (hc : 0 < c) : -r⁻¹ < c ↔ r < -c⁻¹ := by
  have hr' : r⁻¹ < 0 := inv_lt_zero.2 hr
  have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne
  have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have hc' : 0 < c⁻¹ := inv_pos.2 hc
  constructor
  · intro h; nlinarith [mul_lt_mul_of_pos_right h (neg_pos.2 hr)]
  · intro h; nlinarith [mul_lt_mul_of_pos_right h hc]

/-- For `r > 0 > c`, `−1/r < c ↔ r < −1/c`. -/
theorem neg_inv_lt_iff_of_pos_of_neg {r c : ℝ} (hr : 0 < r) (hc : c < 0) : -r⁻¹ < c ↔ r < -c⁻¹ := by
  have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have h2 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne
  have hr' : 0 < r⁻¹ := inv_pos.2 hr
  have hc' : c⁻¹ < 0 := inv_lt_zero.2 hc
  constructor
  · intro h; nlinarith [mul_lt_mul_of_pos_right h hr]
  · intro h; nlinarith [mul_lt_mul_of_pos_right h (neg_pos.2 hc)]

theorem forceJumpSet_two {aL bL aR bR x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ aL) (h2 : x ≠ bL) (h3 : x ≠ aR)
    (h4 : x ≠ bR) : x ∉ forceJumpSet ![aL, bL] ![aR, bR] := by
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, Fin.exists_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, not_or]
  exact ⟨h0, ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩, fun h => h3 h.symm, fun h => h4 h.symm⟩

theorem forceJumpSet_one {vL vR x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ vL) (h2 : x ≠ vR) :
    x ∉ forceJumpSet (fun _ : Fin 1 => vL) (fun _ : Fin 1 => vR) := by
  simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, exists_const, not_or]
  exact ⟨h0, fun h => h1 h.symm, fun h => h2 h.symm⟩

/-- **Boundary limits through the two-slit chart at real points with a real boundary image** (the points of `ℝ` and
of the reversed slit `G` seen from `Ψ`-coordinates). -/
theorem tendsto_twoSlitChart_of_real (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hs : 0 < s) (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t)
    {rL rR vL vR : ℝ} (hvL : vL < 0) (hvR : 0 < vR) {M : ℂ → ℝ}
    (hG : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}),
      Tendsto (fun z => M z + revSlitMean rL rR Wβ s vL vR z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0))
    {x r : ℝ} (hr : r ≠ 0) (hF : extendFrom H (fwdMapInv W' T) x = r)
    (hq : extendFrom H (fwdMapInv Wβ s) ((-r⁻¹ : ℝ) : ℂ) ≠ 0)
    (hxL : x ≠ chartBL W' T vR) (hxaL : x ≠ chartAL W' T) (hx0 : x ≠ 0) (hxaR : x ≠ chartAR W' T)
    (hxR : x ≠ chartBR W' T vL) :
    Tendsto (fun y => M (twoSlitChart Wβ s W' T y) - chartMean rL rR W' T vL vR y) (𝓝[H] (x : ℂ)) (𝓝 0) := by
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
  have hrev : ∀ y ∈ H, revSlitMean rL rR Wβ s vL vR (twoSlitChart Wβ s W' T y) =
      condMean (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (fun _ => vL) (fun _ => vR)
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
  have hmatch := fbd_add_fbd_eq_zero (rL := rL) (rR := rR)
    (chartBL_lt hη' hη'p hW' hW'0 hT.le hvR) (chartAL_nonpos hW' hT.le) (chartAR_nonneg hW' hT.le)
    (chartAR_lt hη' hη'p hW' hW'0 hT.le hvL) hξ0 hξL hξR hA hB hC hD
  -- the two boundary values
  have hcβ := (isBoundedHarmonicExtension_condMean (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL)
    (vL := fun _ => vL) (vR := fun _ => vR) (fun _ => hvL.le) (fun _ => hvR.le)).2.2 ξ
    (forceJumpSet_one hξ0 hξL hξR)
  have h5 : Tendsto (fun y => revSlitMean rL rR Wβ s vL vR (twoSlitChart Wβ s W' T y)) (𝓝[H] (x : ℂ))
      (𝓝 (forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (fun _ => vL) (fun _ => vR) ξ)) := by
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
  have h6 := (isBoundedHarmonicExtension_condMean ![rL, -rL] ![rR, -rR] hvL' hvR').2.2 x
    (forceJumpSet_two hx0 hxaL hxL hxaR hxR)
  have h7 := (hlimG.sub h5).sub h6
  have hval : (0 : ℝ) - forceBoundaryData 4 (fun _ : Fin 1 => rR) (fun _ : Fin 1 => rL) (fun _ => vL)
      (fun _ => vR) ξ - forceBoundaryData 4 ![rL, -rL] ![rR, -rR] ![chartAL W' T, chartBL W' T vR]
      ![chartAR W' T, chartBR W' T vL] x = 0 := by linarith
  rw [hval] at h7
  refine h7.congr fun y => ?_
  simp only [Function.comp_apply, chartMean]
  ring

end InteractingSLE.WangWu
