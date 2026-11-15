/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactBdrySide

/-!
# The boundary correspondence of the two-slit chart (step (S3b) of the contact step)

Packet PROVE-WW-B14 (the deterministic half of the contact step's N3; PROVE-WW-B11's (S3b)). Wang–Wu
(`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), proof of Proposition 4.18 (text dump
L1611–1615: "The union boundary lemma identifies its harmonic mean on every exposed open arc. The only exceptions are
the finitely many slit tips, starting prime ends, and original boundary jumps. Corollary 4.8 excludes singular
contributions there and identifies the bounded mean.").

Setting of `ReverseContactBdryLimit`. Let `M` be a function on `C = ℍ \ (A ∪ G)` (the uncentred union mean) such that
* `M − m_A → 0` at every point of `A ∪ ℝ` (`m_A = fwdSlitMean`, the explicit forward mean), and
* `M + m_G → 0` at every point of `G ∪ (ℝ \ {0})` (`m_G = revSlitMean`, the explicit reverse mean read through `R`).

**`exists_finite_tendsto_twoSlitChart`**: then `M(Φ(y)) − chartMean(y) → 0` as `y → x` at every real `x` outside a
finite set, where `Φ = Ψ⁻¹ ∘ F'_T` is the two-slit chart and `chartMean` the explicit `SLE₄(r_L, −r_L; r_R, −r_R)` mean
in the image chart. With Corollary 4.8 through a half-plane chart this identifies the union mean.

* Real boundary image (`tendsto_twoSlitChart_of_real`, previous file): the points of `ℝ` and of the reversed slit.
* **`tendsto_twoSlitChart_of_mem_H`**: the boundary image `F̄'_T(x)` is a point `Ψ(α(u))`, `u < t`, of the image slit.
  Then `Φ(y) → α(u)` and, along every ultrafilter, `f_t(Φ(y))` tends to a real `x₁ ≠ 0` with `F̄_t(x₁) = α(u)`; the
  separating arc (`fwdMap_twoSlitChart_mem_sides`) forces `x₁ < 0` when `x < 0` (and `x₁ > 0` when `x > 0`), so both
  means tend to `−λ` (resp. `+λ`).
* The exceptional set: the five force positions of `chartMean`, and the two points sent by `Φ` to the base of `β`
  (`extendFrom_eq_zero_imp`); the base and the tip of the image slit are among the force positions
  (`eq_zero_of_extendFrom_eq_tip`, `extendFrom_eq_zero_imp`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.WangWu

open MartChar.RealFlow

variable {Wα Wβ W' : ℝ → ℝ} {α β η' : ℝ → ℂ} {t s T : ℝ}

/-- **Boundary limits through the two-slit chart at the sides of the forward slit.** -/
theorem tendsto_twoSlitChart_of_mem_H (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (hWα : Continuous Wα)
    (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0) (hβ : IsLoewnerTrace Wβ β)
    (hβp : IsProperArc β) (hs : 0 < s) (hG : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {rL rR vL vR : ℝ} (hvL : vL < 0) (hvR : 0 < vR) {M : ℂ → ℝ}
    (hA : ∀ z₀ ∈ fwdHull Wα t ∪ {z : ℂ | z.im = 0},
      Tendsto (fun z => M z - fwdSlitMean rL rR Wα t z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀)
        (𝓝 0))
    {x : ℝ} (hFH : extendFrom H (fwdMapInv W' T) x ∈ H) (hx0 : x ≠ 0) :
    Tendsto (fun y => M (twoSlitChart Wβ s W' T y) - chartMean rL rR W' T vL vR y) (𝓝[H] (x : ℂ)) (𝓝 0) := by
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
  have hc := (isBoundedHarmonicExtension_condMean ![rL, -rL] ![rR, -rR] hvL' hvR').2.2 x
    (forceJumpSet_two hx0 hxL.ne' (hbL.trans hxL).ne' hxR.ne (hxR.trans hbR).ne)
  -- the common value `−λ` or `+λ`
  set ℓ := forceBoundaryData 4 ![rL, -rL] ![rR, -rR] ![chartAL W' T, chartBL W' T vR]
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
  simp only [Function.comp_apply, chartMean]
  ring

/-- **The boundary correspondence of the two-slit chart** (step (S3b) of the contact step). Under the boundary
behaviour of the union mean `M` against the two explicit slit means, `M ∘ Φ − chartMean → 0` at every real point
outside a finite set (the five force positions of `chartMean` and the two points `f'_T(−1/c)`, `c` the force images of
the reverse slit, which `Φ` sends to `∞`). -/
theorem exists_finite_tendsto_twoSlitChart (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α)
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t) (hWβ : Continuous Wβ) (hWβ0 : Wβ 0 = 0)
    (hβ : IsLoewnerTrace Wβ β) (hβp : IsProperArc β) (hs : 0 < s) (hG : IsClosed (negInv '' fwdHull Wβ s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull Wβ s))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') (hT : 0 < T)
    (hK' : fwdHull W' T = revChart Wβ s '' fwdHull Wα t) (htip : η' T = revChart Wβ s (α t))
    {rL rR vL vR : ℝ} (hvL : vL < 0) (hvR : 0 < vR) {M : ℂ → ℝ}
    (hA : ∀ z₀ ∈ fwdHull Wα t ∪ {z : ℂ | z.im = 0},
      Tendsto (fun z => M z - fwdSlitMean rL rR Wα t z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀)
        (𝓝 0))
    (hGl : ∀ z₀ ∈ negInv '' fwdHull Wβ s ∪ ({z : ℂ | z.im = 0} \ {0}),
      Tendsto (fun z => M z + revSlitMean rL rR Wβ s vL vR z)
        (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull Wβ s)] z₀) (𝓝 0)) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ x : ℝ, x ∉ E →
      Tendsto (fun y => M (twoSlitChart Wβ s W' T y) - chartMean rL rR W' T vL vR y) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set e₁ : ℝ := (fwdMap W' T ((-(chartAR Wβ s)⁻¹ : ℝ) : ℂ)).re with he₁
  set e₂ : ℝ := (fwdMap W' T ((-(chartAL Wβ s)⁻¹ : ℝ) : ℂ)).re with he₂
  refine ⟨{chartBL W' T vR, chartAL W' T, 0, chartAR W' T, chartBR W' T vL, e₁, e₂}, by simp, fun x hx => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx
  obtain ⟨hxbL, hxaL, hx0, hxaR, hxbR, hxe₁, hxe₂⟩ := hx
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  set r := extendFrom H (fwdMapInv W' T) x with hr
  by_cases hrH : r ∈ H
  · exact tendsto_twoSlitChart_of_mem_H hα hαp hWα hWα0 ht hWβ hWβ0 hβ hβp hs hG hdisj hW' hW'0 hη' hη'p hT
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
    exact tendsto_twoSlitChart_of_real hWβ hWβ0 hβ hs hW' hW'0 hη' hη'p hT hK' hvL hvR hGl hr0 hF hq hxbL hxaL
      hx0 hxaR hxbR

end InteractingSLE.WangWu
