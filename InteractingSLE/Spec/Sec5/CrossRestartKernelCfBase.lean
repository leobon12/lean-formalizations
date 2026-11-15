/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfReal

/-!
# Lemma 4.7's direction, item (B): the new curve's side of the image chart, point by point

Packet PROVE-CFRESTART2. Setting (`IsCfImgSetup`): in the reversed-slit chart, a new curve (driver `Wα`, Loewner trace
`α` staying in `ℍ` on `(0, t]`, **not simple**), an obstacle `R(K^{Wβ}_s)` (`Wβ` with boundary limits, its hull
meeting `ℝ` only at `0`), and an image chain (driver `W'`, trace `η'` in `ℍ` on `(0, T]`) with `K^{W′}_T = Ψ(K^{Wα}_t)`
that keeps following the new curve for a while after `t` (a clock `τ`). The real line of the image chart splits into
the image hull's base interval `[a_L, a_R]` (`a_L = chartAL W′ T`, `a_R = chartAR W′ T`), where the inverse boundary
value `F̄′_T` lies in `ℍ` (or is `0` at the ends), and the outside, where it is real (PROVE-CFRESTART-C's slit side).
On the base interval this file proves, for the inverse transition map `Θ = f_t ∘ Ψ⁻¹ ∘ F′_T` and `Φ = Ψ⁻¹ ∘ F′_T`:

* `IsCfImgSetup.limits_base`: at every `x ∈ [a_L, a_R] ∖ {0}`, `Φ → p ∉ ℍ ∖ K_t` and `Θ` has a nonzero real limit
  `p₀` with `F̄_t(p₀) = p`, and the branch of `arg Θ′` tends to a multiple of `2π` (the tip lemma
  `eq_zero_of_tendsto_imgTheta_zero` excludes the cluster value `0`);
* `IsCfImgSetup.left_side`, `IsCfImgSetup.right_side`: on `[a_L, 0)` the limit `p₀` is negative and the branch tends
  to `0`; on `(0, a_R]` it is positive and the branch tends to `0` (connectedness from the physical points just
  outside the base interval, `imgTheta_tendsto_of_extendFrom_neg_of_mem_H`, `…_pos_of_mem_H`);
* the limit lies on the new curve's base interval: `chartAL Wα t < p₀ < chartAR Wα t` inside `(a_L, a_R)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal Real

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg MartChar.RealFlow Restart.RetAux79
open CrossCond.Word49 (junL junR)

/-- **The deterministic setting of the new curve's side** (see the module docstring). -/
structure IsCfImgSetup (Wα : ℝ → ℝ) (α : ℝ → ℂ) (t : ℝ) (Wβ : ℝ → ℝ) (s : ℝ) (W' : ℝ → ℝ) (η' : ℝ → ℂ)
    (T : ℝ) : Prop where
  hWα : Continuous Wα
  hWα0 : Wα 0 = 0
  ht : 0 < t
  hα : IsLoewnerTrace Wα α
  hαH : ∀ r ∈ Ioc (0 : ℝ) t, α r ∈ H
  hWβ : Continuous Wβ
  hWβ0 : Wβ 0 = 0
  hs : 0 ≤ s
  hB : HasBdryLimits (fwdMapInv Wβ s)
  hKs : ∀ z ∈ closure (fwdHull Wβ s), z.im = 0 → z = 0
  hjL : 0 < rightImg Wβ 0 s - Wβ s
  hjR : -rightImg (fun r => -Wβ r) 0 s - Wβ s < 0
  hGc : IsClosed (negInv '' fwdHull Wβ s)
  hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s)
  hdis : Disjoint (closure (fwdHull Wβ s)) (closure (negInv '' fwdHull Wα t))
  hW' : Continuous W'
  hW'0 : W' 0 = 0
  hT : 0 < T
  hη' : IsLoewnerTrace W' η'
  hη'H : ∀ r ∈ Ioc (0 : ℝ) T, η' r ∈ H
  hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t
  grow : ∃ (τ : ℝ → ℝ) (ε₀ : ℝ), 0 < ε₀ ∧ ContinuousWithinAt τ (Ici t) t ∧ τ t = T ∧
    (∀ r ∈ Icc t (t + ε₀), T ≤ τ r) ∧ (∀ r ∈ Icc t (t + ε₀), Disjoint (fwdHull Wα r) (negInv '' fwdHull Wβ s)) ∧
    ∀ r ∈ Icc t (t + ε₀), fwdHull W' (τ r) = revChart Wβ s '' fwdHull Wα r


section Base

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- The right base image is strictly right of the driver at positive times (`WangWu.chartAR_pos` for a trace staying
in `ℍ`; the simplicity was used only through `η t ∈ ℍ`). -/
theorem chartAR_pos_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ r ∈ Ioc (0 : ℝ) t, η r ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 < t) : 0 < chartAR W t := by
  by_contra hle
  have h0 : chartAR W t = 0 := le_antisymm (not_lt.1 hle) (chartAR_nonneg hW ht.le)
  have hreal : ∀ n : ℕ, (extendFrom H (fwdMapInv W t) ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)).im = 0 := by
    intro n
    have hxH := extendFrom_mem_Hbar hη hW hW0 ht.le (x := (((1 / ((n : ℝ) + 1)) : ℝ) : ℂ))
      (show (0 : ℝ) ≤ ((((1 / ((n : ℝ) + 1)) : ℝ) : ℂ)).im by simp)
    refine le_antisymm (not_lt.1 fun hpos => ?_) hxH
    have h1 := lt_rightImg_sub_of_extendFrom_mem_H hη hW hW0 ht.le hpos
    rw [← chartAR, h0] at h1
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have h := im_extendFrom_eq_zero_of_tendsto hη hW hW0 ht.le tendsto_one_div_add_atTop_nhds_zero_nat hreal
  rw [Complex.ofReal_zero, extendFrom_zero hη hW hW0 ht.le] at h
  have h3 : (0 : ℝ) < (η t).im := hηH t ⟨ht, le_rfl⟩
  rw [h] at h3
  exact lt_irrefl _ h3

/-- The left base image is strictly left of the driver at positive times (`WangWu.chartAL_neg` for a trace staying in
`ℍ`). -/
theorem chartAL_neg_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ r ∈ Ioc (0 : ℝ) t, η r ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 < t) : chartAL W t < 0 := by
  by_contra hle
  have h0 : chartAL W t = 0 := le_antisymm (chartAL_nonpos hW ht.le) (not_lt.1 hle)
  have hreal : ∀ n : ℕ, (extendFrom H (fwdMapInv W t) ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)).im = 0 := by
    intro n
    have hxH := extendFrom_mem_Hbar hη hW hW0 ht.le (x := (((-(1 / ((n : ℝ) + 1))) : ℝ) : ℂ))
      (show (0 : ℝ) ≤ ((((-(1 / ((n : ℝ) + 1))) : ℝ) : ℂ)).im by simp)
    refine le_antisymm (not_lt.1 fun hpos => ?_) hxH
    have h1 := neg_rightImg_sub_lt_of_extendFrom_mem_H hη hW hW0 ht.le hpos
    rw [← chartAL, h0] at h1
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hlim : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  have h := im_extendFrom_eq_zero_of_tendsto hη hW hW0 ht.le hlim hreal
  rw [Complex.ofReal_zero, extendFrom_zero hη hW hW0 ht.le] at h
  have h3 : (0 : ℝ) < (η t).im := hηH t ⟨ht, le_rfl⟩
  rw [h] at h3
  exact lt_irrefl _ h3

end Base

namespace IsCfImgSetup

variable {Wα Wβ W' : ℝ → ℝ} {α η' : ℝ → ℂ} {t s T : ℝ}

theorem hKt (hd : IsCfImgSetup Wα α t Wβ s W' η' T) :
    ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t) :=
  ofReal_notMem_closure_fwdHull_of_mem_H hd.hα hd.hαH hd.hWα hd.ht.le

/-- **No cluster value `0` of `Θ` away from the image tip** (the tip lemma). -/
theorem not_tendsto_zero (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x : ℝ} (hx : x ≠ 0) (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[H] (x : ℂ)) : ¬ Tendsto (imgTheta Wα t Wβ s W' T) U (𝓝 0) := by
  obtain ⟨τ, ε₀, hε₀, hτc, hτt, hτle, hdisjr, hgrow⟩ := hd.grow
  intro hΘ
  have := eq_zero_of_tendsto_imgTheta_zero hd.hWα hd.hWα0 hd.ht.le hd.hKt hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0
    hd.hT.le hd.hdis hε₀ hτc hτt hτle hdisjr hgrow hU hΘ
  exact hx (by exact_mod_cast this)

/-- On the open base interval of the image hull the inverse boundary value lies in `ℍ`. -/
theorem extendFrom_mem_H (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x : ℝ}
    (hx : x ∈ Ioo (chartAL W' T) (chartAR W' T)) : extendFrom H (fwdMapInv W' T) x ∈ H := by
  rcases (extendFrom_im_nonneg hd.hη' hd.hW' hd.hW'0 hd.hT.le x).lt_or_eq with hpos | h0
  · exact hpos
  · exfalso
    set w := extendFrom H (fwdMapInv W' T) x with hw
    have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h0])
    by_cases hr : w.re = 0
    · have h00 : extendFrom H (fwdMapInv W' T) x = 0 := by rw [← hw, hwr, hr, ofReal_zero]
      rcases extendFrom_eq_zero_imp_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT h00 with h | h
      · exact (lt_irrefl _ (h ▸ hx.1))
      · exact (lt_irrefl _ (h ▸ hx.2))
    · rcases outside_base_of_extendFrom_real_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le hr hwr with
        ⟨-, h⟩ | ⟨-, h⟩
      · exact lt_asymm h hx.1
      · exact lt_asymm h hx.2

/-- **`F̄_t` at the limit of `Θ` is the limit of `Φ`.** -/
theorem extendFrom_eq_of_tendsto (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x p₀ : ℝ} {p : ℂ}
    (hΦ : Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 p))
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ))) :
    extendFrom H (fwdMapInv Wα t) p₀ = p := by
  have := nhdsWithin_H_neBot x
  have hmem : ∀ᶠ y in 𝓝[H] (x : ℂ), revChartInv Wβ s (fwdMapInv W' T y) ∈
      H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) :=
    eventually_nhdsWithin_of_forall fun y hy =>
      revChartInv_fwdMapInv_mem hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hd.hK' hy
  have hΘH : ∀ᶠ y in 𝓝[H] (x : ℂ), imgTheta Wα t Wβ s W' T y ∈ H := hmem.mono fun y hy =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hd.hWα hd.ht.le ⟨hy.1, fun h => hy.2 (Or.inl h)⟩
  have hB := hd.hα.hasBdryLimits hd.hWα hd.hWα0 hd.ht.le
  have h1 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) (𝓝[H] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv Wα t) p₀)) :=
    (hB.tendsto (show (0 : ℝ) ≤ ((p₀ : ℝ) : ℂ).im by simp)).comp (tendsto_nhdsWithin_iff.2 ⟨hΘ, hΘH⟩)
  have h2 : Tendsto (fun y => fwdMapInv Wα t (imgTheta Wα t Wβ s W' T y)) (𝓝[H] (x : ℂ)) (𝓝 p) := by
    refine hΦ.congr' (hmem.mono fun y hy => ?_)
    exact (QuantumZipper.RS.fwdMapInv_fwdMap hd.hWα hd.hWα0 hd.ht.le ⟨hy.1, fun h => hy.2 (Or.inl h)⟩).symm
  exact tendsto_nhds_unique h1 h2

/-- **The per-point inputs on the closed base interval of the image hull** (except the image tip `0`). -/
theorem limits_base (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x : ℝ}
    (hx : x ∈ Icc (chartAL W' T) (chartAR W' T)) (hx0 : x ≠ 0) :
    ∃ p : ℂ, Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 p) ∧
      p ∉ H \ fwdHull Wα t ∧
      (∃ p₀ : ℝ, p₀ ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ))) ∧
      ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (2 * π * k)) := by
  have hcase : extendFrom H (fwdMapInv W' T) x = 0 ∨ extendFrom H (fwdMapInv W' T) x ∈ H := by
    rcases hx.1.lt_or_eq with h1 | h1
    · rcases hx.2.lt_or_eq with h2 | h2
      · exact Or.inr (hd.extendFrom_mem_H ⟨h1, h2⟩)
      · exact Or.inl (extendFrom_base_eq_zero_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le (Or.inr h2))
    · exact Or.inl (extendFrom_base_eq_zero_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le (Or.inl h1.symm))
  obtain ⟨p, hΦ, hp, -⟩ := exists_tendsto_Phi_of_extendFrom (Wα := Wα) (t := t) hd.hη' hd.hW' hd.hW'0 hd.hT.le
    hd.hWβ hd.hWβ0 hd.hs hd.hdisj hd.hK' hcase
  exact ⟨p, hΦ, hp, imgTheta_limits_of_tendsto_Phi hd.hα hd.hWα hd.hWα0 hd.ht.le hd.hKt hd.hWβ hd.hWβ0 hd.hs
    hd.hW' hd.hW'0 hd.hT.le hd.hGc hd.hdisj hd.hdis hd.hK' hΦ hp (hd.not_tendsto_zero hx0)⟩

/-- **The left half of the base interval**: on `[a_L, 0)` the limit of `Θ` is negative and the branch tends to `0`
(connectedness of `(a_L − δ, 0)`, where every point has a nonzero real limit and an integer branch, from the physical
points `(a_L − δ, a_L)` with negative limits and branch `0`). -/
theorem left_side (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x : ℝ} (hx : x ∈ Ico (chartAL W' T) 0) :
    (∃ p₀ : ℝ, p₀ < 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ))) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set aL := chartAL W' T with haL
  have haR0 : 0 < chartAR W' T := chartAR_pos_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT
  have hjL' : junL Wβ s < 0 := by
    rw [junL]; exact div_neg_of_neg_of_pos (by norm_num) hd.hjL
  have hcF := continuous_extendFrom_ofReal hd.hη' hd.hW' hd.hW'0 hd.hT.le
  have hbase : extendFrom H (fwdMapInv W' T) (aL : ℂ) = 0 :=
    extendFrom_base_eq_zero_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le (Or.inl rfl)
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 (hcF.continuousAt (x := aL)) (-junL Wβ s) (by linarith)
  -- the physical points just left of `a_L`
  have hphys : ∀ x' ∈ Ioo (aL - δ) aL,
      (∃ p : ℝ, p < 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
        Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    intro x' hx'
    obtain ⟨him, hre⟩ := re_extendFrom_neg_of_lt_chartAL_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le hx'.2
    set r := (extendFrom H (fwdMapInv W' T) x').re with hrdef
    have hr : extendFrom H (fwdMapInv W' T) x' = r := Complex.ext (by simp [hrdef]) (by simp [him])
    have hrj : junL Wβ s < r := by
      have h1 := hδb (x := x') (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx'.1, hx'.2])
      rw [hbase, hr, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
      have := neg_abs_le r
      linarith
    exact imgTheta_tendsto_of_extendFrom_neg_of_mem_H hd.hα hd.hαH hd.hWα hd.hWα0 hd.ht hd.hKt hd.hWβ hd.hWβ0 hd.hs
      hd.hB hd.hKs hd.hjL hd.hW' hd.hW'0 hd.hT.le hd.hη' hd.hη'H hr hre hrj
  set I : Set ℝ := Ioo (aL - δ) 0 with hI
  have hlimI : ∀ x' ∈ I,
      (∃ p₀ : ℝ, p₀ ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p₀ : ℂ))) ∧
        ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (2 * π * k)) := by
    intro x' hx'
    rcases lt_or_ge x' aL with hlt | hge
    · obtain ⟨⟨p, hp, hpl⟩, hb⟩ := hphys x' ⟨hx'.1, hlt⟩
      exact ⟨⟨p, hp.ne, hpl⟩, 0, by simpa using hb⟩
    · obtain ⟨-, -, -, h1, h2⟩ := hd.limits_base ⟨hge, (hx'.2.trans haR0).le⟩ hx'.2.ne
      exact ⟨h1, h2⟩
  -- the real part of the limit, continuous on `I`
  set a : ℂ → ℝ := fun y => (imgTheta Wα t Wβ s W' T y).re with hadef
  have hre : ∀ {x' p₀ : ℝ}, Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p₀ : ℂ)) →
      Tendsto a (𝓝[H] (x' : ℂ)) (𝓝 p₀) := fun {x' p₀} h => by
    have := (Complex.continuous_re.tendsto ((p₀ : ℝ) : ℂ)).comp h
    rw [Complex.ofReal_re] at this
    exact this
  have hgc : ContinuousOn (fun x' : ℝ => extendFrom H a (x' : ℂ)) I :=
    continuousOn_extendFrom_ofReal fun x' hx' => by
      obtain ⟨⟨p₀, -, hp⟩, -⟩ := hlimI x' hx'
      exact ⟨p₀, hre hp⟩
  have hgv : ∀ x' p₀ : ℝ, Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p₀ : ℂ)) →
      extendFrom H a (x' : ℂ) = p₀ := fun x' p₀ h => extendFrom_eq (ofReal_mem_closure_H x') (hre h)
  have hne : ∀ x' ∈ I, extendFrom H a (x' : ℂ) ≠ 0 := fun x' hx' => by
    obtain ⟨⟨p₀, hp0, hp⟩, -⟩ := hlimI x' hx'
    rw [hgv x' p₀ hp]
    exact hp0
  have haL0 : aL < 0 := chartAL_neg_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT
  have hx₁I : aL - δ / 2 ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨⟨p₁, hp₁, hp₁l⟩, hb₁⟩ := hphys (aL - δ / 2) ⟨by linarith, by linarith⟩
  have hg₁ : extendFrom H a ((aL - δ / 2 : ℝ) : ℂ) < 0 := by rw [hgv _ _ hp₁l]; exact hp₁
  have hneg : ∀ x' ∈ I, extendFrom H a (x' : ℂ) < 0 := by
    intro x' hx'
    by_contra hnn
    have hpos : 0 < extendFrom H a (x' : ℂ) := lt_of_le_of_ne (not_lt.1 hnn) (hne x' hx').symm
    obtain ⟨z, hz, hz0⟩ := isPreconnected_Ioo.intermediate_value hx₁I hx' hgc ⟨hg₁.le, hpos.le⟩
    exact hne z hz hz0
  have hxI : x ∈ I := ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨⟨p₀, -, hp⟩, -⟩ := hlimI x hxI
  refine ⟨⟨p₀, ?_, hp⟩, tendsto_zero_of_forall_tendsto_two_pi_int isPreconnected_Ioo
    (fun x' hx' => (hlimI x' hx').2) hx₁I hb₁ hxI⟩
  rw [← hgv x p₀ hp]
  exact hneg x hxI

/-- **The right half of the base interval**: on `(0, a_R]` the limit of `Θ` is positive and the branch tends to
`0` (mirror of `left_side`). -/
theorem right_side (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x : ℝ} (hx : x ∈ Ioc 0 (chartAR W' T)) :
    (∃ p₀ : ℝ, 0 < p₀ ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ))) ∧
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set aR := chartAR W' T with haR
  have haL0 : chartAL W' T < 0 := chartAL_neg_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT
  have haR0 : 0 < aR := chartAR_pos_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT
  have hjR' : 0 < junR Wβ s := by
    rw [junR]; exact div_pos_of_neg_of_neg (by norm_num) hd.hjR
  have hcF := continuous_extendFrom_ofReal hd.hη' hd.hW' hd.hW'0 hd.hT.le
  have hbase : extendFrom H (fwdMapInv W' T) (aR : ℂ) = 0 :=
    extendFrom_base_eq_zero_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le (Or.inr rfl)
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 (hcF.continuousAt (x := aR)) (junR Wβ s) hjR'
  -- the physical points just right of `a_R`
  have hphys : ∀ x' ∈ Ioo aR (aR + δ),
      (∃ p : ℝ, 0 < p ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ))) ∧
        Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    intro x' hx'
    obtain ⟨him, hre⟩ := re_extendFrom_pos_of_chartAR_lt_of_mem_H hd.hη' hd.hη'H hd.hW' hd.hW'0 hd.hT.le hx'.1
    set r := (extendFrom H (fwdMapInv W' T) x').re with hrdef
    have hr : extendFrom H (fwdMapInv W' T) x' = r := Complex.ext (by simp [hrdef]) (by simp [him])
    have hrj : r < junR Wβ s := by
      have h1 := hδb (x := x') (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx'.1, hx'.2])
      rw [hbase, hr, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
      have := le_abs_self r
      linarith
    exact imgTheta_tendsto_of_extendFrom_pos_of_mem_H hd.hα hd.hαH hd.hWα hd.hWα0 hd.ht hd.hKt hd.hWβ hd.hWβ0 hd.hs
      hd.hB hd.hKs hd.hjR hd.hW' hd.hW'0 hd.hT.le hd.hη' hd.hη'H hr hre hrj
  set I : Set ℝ := Ioo 0 (aR + δ) with hI
  have hlimI : ∀ x' ∈ I,
      (∃ p₀ : ℝ, p₀ ≠ 0 ∧ Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p₀ : ℂ))) ∧
        ∃ k : ℤ, Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (2 * π * k)) := by
    intro x' hx'
    rcases lt_or_ge aR x' with hlt | hle
    · obtain ⟨⟨p, hp, hpl⟩, hb⟩ := hphys x' ⟨hlt, hx'.2⟩
      exact ⟨⟨p, hp.ne', hpl⟩, 0, by simpa using hb⟩
    · obtain ⟨-, -, -, h1, h2⟩ := hd.limits_base ⟨(haL0.trans hx'.1).le, hle⟩ hx'.1.ne'
      exact ⟨h1, h2⟩
  set a : ℂ → ℝ := fun y => (imgTheta Wα t Wβ s W' T y).re with hadef
  have hre : ∀ {x' p₀ : ℝ}, Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p₀ : ℂ)) →
      Tendsto a (𝓝[H] (x' : ℂ)) (𝓝 p₀) := fun {x' p₀} h => by
    have := (Complex.continuous_re.tendsto ((p₀ : ℝ) : ℂ)).comp h
    rw [Complex.ofReal_re] at this
    exact this
  have hgc : ContinuousOn (fun x' : ℝ => extendFrom H a (x' : ℂ)) I :=
    continuousOn_extendFrom_ofReal fun x' hx' => by
      obtain ⟨⟨p₀, -, hp⟩, -⟩ := hlimI x' hx'
      exact ⟨p₀, hre hp⟩
  have hgv : ∀ x' p₀ : ℝ, Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x' : ℂ)) (𝓝 (p₀ : ℂ)) →
      extendFrom H a (x' : ℂ) = p₀ := fun x' p₀ h => extendFrom_eq (ofReal_mem_closure_H x') (hre h)
  have hne : ∀ x' ∈ I, extendFrom H a (x' : ℂ) ≠ 0 := fun x' hx' => by
    obtain ⟨⟨p₀, hp0, hp⟩, -⟩ := hlimI x' hx'
    rw [hgv x' p₀ hp]
    exact hp0
  have hx₁I : aR + δ / 2 ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨⟨p₁, hp₁, hp₁l⟩, hb₁⟩ := hphys (aR + δ / 2) ⟨by linarith, by linarith⟩
  have hg₁ : 0 < extendFrom H a ((aR + δ / 2 : ℝ) : ℂ) := by rw [hgv _ _ hp₁l]; exact hp₁
  have hposI : ∀ x' ∈ I, 0 < extendFrom H a (x' : ℂ) := by
    intro x' hx'
    by_contra hnn
    have hneg : extendFrom H a (x' : ℂ) < 0 := lt_of_le_of_ne (not_lt.1 hnn) (hne x' hx')
    obtain ⟨z, hz, hz0⟩ := isPreconnected_Ioo.intermediate_value hx' hx₁I hgc ⟨hneg.le, hg₁.le⟩
    exact hne z hz hz0
  have hxI : x ∈ I := ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨⟨p₀, -, hp⟩, -⟩ := hlimI x hxI
  refine ⟨⟨p₀, ?_, hp⟩, tendsto_zero_of_forall_tendsto_two_pi_int isPreconnected_Ioo
    (fun x' hx' => (hlimI x' hx').2) hx₁I hb₁ hxI⟩
  rw [← hgv x p₀ hp]
  exact hposI x hxI

/-- **The limit of `Θ` lies on the new curve's base interval** at points of the open image base interval, and `Φ`
tends there to a point of the new curve's hull. -/
theorem limit_mem_base (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {x p₀ : ℝ}
    (hx : x ∈ Ioo (chartAL W' T) (chartAR W' T))
    (hΘ : Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ))) :
    p₀ ∈ Ioo (chartAL Wα t) (chartAR Wα t) ∧ ∃ p ∈ fwdHull Wα t,
      Tendsto (fun y => revChartInv Wβ s (fwdMapInv W' T y)) (𝓝[H] (x : ℂ)) (𝓝 p) := by
  have hxH := hd.extendFrom_mem_H hx
  obtain ⟨p, hΦ, -, hpK⟩ := exists_tendsto_Phi_of_extendFrom (Wα := Wα) (t := t) hd.hη' hd.hW' hd.hW'0
    hd.hT.le hd.hWβ hd.hWβ0 hd.hs hd.hdisj hd.hK' (Or.inr hxH)
  have hpK' := hpK hxH
  have hpH : (0 : ℝ) < p.im := (QuantumZipper.fwdHull_mono (W := Wα)).2 t hpK'
  have he := hd.extendFrom_eq_of_tendsto hΦ hΘ
  refine ⟨⟨?_, ?_⟩, p, hpK', hΦ⟩
  · by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · have := (re_extendFrom_neg_of_lt_chartAL_of_mem_H hd.hα hd.hαH hd.hWα hd.hWα0 hd.ht.le hlt).1
      rw [he] at this
      linarith
    · have := extendFrom_base_eq_zero_of_mem_H hd.hα hd.hαH hd.hWα hd.hWα0 hd.ht.le (Or.inl heq)
      rw [he] at this
      rw [this] at hpH
      simp at hpH
  · by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · have := (re_extendFrom_pos_of_chartAR_lt_of_mem_H hd.hα hd.hαH hd.hWα hd.hWα0 hd.ht.le hlt).1
      rw [he] at this
      linarith
    · have := extendFrom_base_eq_zero_of_mem_H hd.hα hd.hαH hd.hWα hd.hWα0 hd.ht.le (Or.inr heq.symm)
      rw [he] at this
      rw [this] at hpH
      simp at hpH

/-- The flowed marks of a word with left marks `≤ 0` and right marks `≥ 0` lie outside the open base interval. -/
theorem notMem_forceJumpSet_of_mem_base {w : ℝ → ℝ} (hw : Continuous w) {r : ℝ} (hr : 0 ≤ r) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {y : ℝ}
    (hy : y ∈ Ioo (chartAL w r) (chartAR w r)) (hy0 : y ≠ 0) :
    y ∉ forceJumpSet (fun i => -rightImg (fun s => -w s) (-xL i) r - w r) (fun j => rightImg w (xR j) r - w r) := by
  rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
  · exact hy0 h
  · have := rightImg_mono_index (w := fun s => -w s) hw.neg hr (neg_nonneg.2 (hxL i))
    have h1 := hy.1
    rw [chartAL] at h1
    simp only at hi
    linarith
  · have := rightImg_mono_index hw hr (hxR j)
    have h1 := hy.2
    rw [chartAR] at h1
    simp only at hj
    linarith

/-- **The new curve's side of the image chart, point by point** (the (B) comparison on the open base interval of
the image hull). Let `uA` be the bounded harmonic extension of the new curve's word data at `t` (marks `xL ≤ 0 ≤ xR`
flowed by `Wα`) and `u` that of the image word's data at `T` (marks `yL ≤ 0 ≤ yR` flowed by `W′`), both at parameter
`κ′`, and suppose the union-mean expression `M + c` is asymptotic to the new curve's coupling mean at every point of
its hull (Proposition 3.8 read in the new curve's chart). Then at every `x ∈ (a_L, a_R) ∖ {0}`,
`M ∘ Φ + c − (u − χ′ (Im L′_T ∘ F′_T + arg_Ψ ∘ Φ)) → 0`: both words carry `∓λ′` on the two sides of the curve, the
limit `p₀` of `Θ` has the sign of `x` (`left_side`, `right_side`), and the branch vanishes. -/
theorem tendsto_imgChart_of_mem_base (hd : IsCfImgSetup Wα α t Wβ s W' η' T) {κ' : ℝ}
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {mL mR : ℕ} {σL : Fin mL → ℝ} {σR : Fin mR → ℝ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ}
    (hyL : ∀ i, yL i ≤ 0) (hyR : ∀ j, 0 ≤ yR j) {M uA u : ℂ → ℝ} {c : ℝ}
    (huA : IsBoundedHarmonicExtension
      (forceBoundaryData κ' ρL ρR (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ' σL σR (fun i => -rightImg (fun r => -W' r) (-yL i) T - W' T)
        (fun j => rightImg W' (yR j) T - W' T))
      (forceJumpSet (fun i => -rightImg (fun r => -W' r) (-yL i) T - W' T)
        (fun j => rightImg W' (yR j) T - W' T)) u)
    (hA : ∀ z₀ ∈ fwdHull Wα t, Tendsto (fun z => M z + c - couplingMean κ' Wα t uA z)
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0))
    {x : ℝ} (hx : x ∈ Ioo (chartAL W' T) (chartAR W' T)) (hx0 : x ≠ 0) :
    Tendsto (fun y => M (revChartInv Wβ s (fwdMapInv W' T y)) + c -
      (u y - chiC κ' * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
        (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  -- the common comparison step, given the limit `p₀ ≠ 0` of `Θ`, the vanishing branch and the data match
  have key : ∀ p₀ : ℝ, p₀ ≠ 0 → Tendsto (imgTheta Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 (p₀ : ℂ)) →
      Tendsto (imgBranch Wα t Wβ s W' T) (𝓝[H] (x : ℂ)) (𝓝 0) →
      (p₀ ∈ Ioo (chartAL Wα t) (chartAR Wα t) →
        forceBoundaryData κ' σL σR (fun i => -rightImg (fun r => -W' r) (-yL i) T - W' T)
          (fun j => rightImg W' (yR j) T - W' T) x =
        forceBoundaryData κ' ρL ρR (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
          (fun j => rightImg Wα (xR j) t - Wα t) p₀) →
      Tendsto (fun y => M (revChartInv Wβ s (fwdMapInv W' T y)) + c -
        (u y - chiC κ' * ((logDerivFwd W' T (fwdMapInv W' T y)).im +
          (logDerivPsi Wβ s (revChartInv Wβ s (fwdMapInv W' T y))).im))) (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro p₀ hp₀0 hΘ hbr hdata
    obtain ⟨hp₀I, p, hpK, hΦ⟩ := hd.limit_mem_base hx hΘ
    have hmem : ∀ᶠ y in 𝓝[H] (x : ℂ), revChartInv Wβ s (fwdMapInv W' T y) ∈
        H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s) :=
      eventually_nhdsWithin_of_forall fun y hy =>
        revChartInv_fwdMapInv_mem hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hd.hK' hy
    have hΦ' := tendsto_nhdsWithin_iff.2 ⟨hΦ, hmem⟩
    have hA' := (hA p hpK).comp hΦ'
    have huA' := huA.2.2 p₀ (notMem_forceJumpSet_of_mem_base hd.hWα hd.ht.le hxL hxR hp₀I hp₀0)
    have hu' := hu.2.2 x (notMem_forceJumpSet_of_mem_base hd.hW' hd.hT.le hyL hyR hx hx0)
    have hΘH : ∀ y ∈ H, imgTheta Wα t Wβ s W' T y ∈ H := fun y hy =>
      (imgTheta_mem hd.hWα hd.hWα0 hd.ht.le hd.hWβ hd.hWβ0 hd.hs hd.hW' hd.hW'0 hd.hT.le hd.hdisj hd.hK' hy).1
    exact tendsto_imgChart_of_newChart (Φ := fun y => revChartInv Wβ s (fwdMapInv W' T y))
      (LA := fun y => (logDerivFwd Wα t (revChartInv Wβ s (fwdMapInv W' T y))).im) hΘH hΘ huA' hu'
      (hdata hp₀I) hbr hA'
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · obtain ⟨⟨p₀, hp₀, hΘ⟩, hbr⟩ := hd.left_side ⟨hx.1.le, hneg⟩
    refine key p₀ hp₀.ne hΘ hbr fun hp₀I => ?_
    rw [forceBoundaryData_flow_slit_left (κ := κ') (ρL := σL) (ρR := σR) (xR := yR) hd.hW' hd.hT.le hyL hneg hx.1,
      forceBoundaryData_flow_slit_left (κ := κ') (ρL := ρL) (ρR := ρR) (xR := xR) hd.hWα hd.ht.le hxL hp₀ hp₀I.1]
  · obtain ⟨⟨p₀, hp₀, hΘ⟩, hbr⟩ := hd.right_side ⟨hpos, hx.2.le⟩
    refine key p₀ hp₀.ne' hΘ hbr fun hp₀I => ?_
    rw [forceBoundaryData_flow_slit_right (κ := κ') (ρL := σL) (ρR := σR) (xL := yL) hd.hW' hd.hT.le hyR hpos.le
        hx.2,
      forceBoundaryData_flow_slit_right (κ := κ') (ρL := ρL) (ρR := ρR) (xL := xL) hd.hWα hd.ht.le hxR hp₀.le hp₀I.2]

end IsCfImgSetup

end InteractingSLE.Sec5.CrossRestart
