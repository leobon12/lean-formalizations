/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfSide
import InteractingSLE.Spec.Sec5.GlueCondUnionImgCf
import InteractingSLE.Spec.Restart.RetAux79Zone
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Lemma 4.7's direction, item (C), step 1: real boundary values of a non-simple image chart off the image hull

Packet PROVE-CFRESTART. On the obstacle (flow-slit) side and on the physical real line, the counterflow's image hull
`K^{W′}_T` in the reversed-slit chart is compared through the boundary values of the image chart's inverse map
`F′_T = fwdMapInv W′ T` at real points **outside** the image hull's base interval `[chartAL W′ T, chartAR W′ T]`.
Proposition 4.9's chain (PROVE-GLUECOND8/10) proved these facts for a **simple** image trace (`IsProperArc`); the
counterflow's image is not simple. The simple-arc proofs use simplicity only to know that the trace stays in `ℍ` at
positive times (so that no real point is ever swallowed). Here that is the hypothesis:

* **`exists_isForwardSol_of_mem_H`**: for a continuous Loewner trace that stays in `ℍ` on `(0, T]`, every nonzero real
  point has a forward solution up to `T` (it is never swallowed);
* `alive_of_mem_H`, `alive_neg_of_mem_H`: every positive real point is alive, for the driver and its reflection;
* **`extendFrom_gImg_sub`**, `extendFrom_neg_gImg_sub`: the boundary value of `F′_T` at the image `g_T(r) − W_T` of an
  alive real point `r` is `r`;
* **`re_extendFrom_pos_of_chartAR_lt_of_mem_H`**, **`re_extendFrom_neg_of_lt_chartAL_of_mem_H`**: right of the image
  hull's right base point the boundary value of `F′_T` is a positive real point, left of its left base point a negative
  one (the non-simple versions of `GlueImg.re_extendFrom_pos_of_chartAR_lt`, `…_neg_of_lt_chartAL`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- **No real point is swallowed by a trace that stays in `ℍ`**: for a continuous Loewner trace `η` of `W` with
`η(s) ∈ ℍ` for `0 < s ≤ T`, every real `x ≠ 0` has a forward solution up to `T`. (The argument of
`WangWu.exists_isForwardSol_of_isProperArc`, which uses its simple arc only through this property.) -/
theorem exists_isForwardSol_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) {x : ℝ} (hx : x ≠ 0) (hT : 0 ≤ T) :
    ∃ v, QuantumZipper.IsForwardSol W (x : ℂ) T v := by
  have hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull W t) (η '' Icc 0 t) := fun t ht => by
    rw [hη.2.2 t ht.1]
    exact isFilling_fillH (isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self))
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [← exists_isForwardSol_neg_iff]
    by_contra hdead
    have hW' : Continuous (fun s => -W s) := hW.neg
    have hW0' : (fun s => -W s) 0 = 0 := by simp [hW0]
    obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW' hW0' (neg_pos.2 hneg) hT hdead
    have hlim := tendsto_fwdMap_of_realSwallowAt hW' hW0' (neg_pos.2 hneg) hsw
    have hfill' : ∀ t ∈ Ico (0 : ℝ) σ,
        IsFilling (fwdHull (fun s => -W s) t) ((fun s => LP.reflectC (η s)) '' Icc 0 t) := by
      intro t ht
      have h1 := LP.isFilling_reflectC (hfill t ⟨ht.1, ht.2.trans_le hσ.2⟩)
      rw [image_image] at h1
      have h2 : fwdHull (fun s => -W s) t = LP.reflectC '' fwdHull W t := LP.fwdHull_neg W t
      rw [h2]
      exact h1
    have hmain := FiniteEndpoint.notMem_H_of_tendsto_fwdMap hW' hW0' hσ.1 (neg_pos.2 hneg)
      (γ := fun s => LP.reflectC (η s)) (by simp [hη.1, LP.reflectC])
      (LP.continuous_reflectC.comp_continuousOn (hη.2.1.mono Icc_subset_Ici_self)) hfill' hsw.2.1 hlim
    exact hmain (LP.reflectC_mem_H_iff.2 (hηH σ hσ))
  · by_contra hdead
    obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hW hW0 hpos hT hdead
    have hlim := tendsto_fwdMap_of_realSwallowAt hW hW0 hpos hsw
    have hmain := FiniteEndpoint.notMem_H_of_tendsto_fwdMap hW hW0 hσ.1 hpos (γ := η) hη.1
      (hη.2.1.mono Icc_subset_Ici_self) (fun t ht => hfill t ⟨ht.1, ht.2.trans_le hσ.2⟩) hsw.2.1 hlim
    exact hmain (hηH σ hσ)

/-- Every positive real point is alive, for a trace that stays in `ℍ`. -/
theorem alive_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H) (hW : Continuous W)
    (hW0 : W 0 = 0) (hT : 0 ≤ T) : ∀ y, 0 < y → Alive W y T := by
  intro y hy
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hη hηH hW hW0 hy.ne' hT
  rcases isForwardSol_real_cases hW hW0 hT hv with ⟨_, h, _⟩ | ⟨h, _, _⟩
  · exact h
  · exact absurd h (not_lt.2 hy.le)

/-- Every positive real point is alive for the reflected driver, for a trace that stays in `ℍ`. -/
theorem alive_neg_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H) (hW : Continuous W)
    (hW0 : W 0 = 0) (hT : 0 ≤ T) : ∀ y, 0 < y → Alive (fun s => -W s) y T := by
  intro y hy
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hη hηH hW hW0 (x := -y) (by linarith : -y ≠ 0) hT
  rcases isForwardSol_real_cases hW hW0 hT hv with ⟨h, _, _⟩ | ⟨_, h, _⟩
  · exact absurd h (by linarith)
  · rwa [neg_neg] at h

/-- **The boundary value of `F_T` at the image of a real point with a forward solution is that point**: if `r` is
real with a forward solution `v` on `[0, T]`, then `F̄_T(v_T) = r`. (A ball around `r` misses the hull, where
`F_T ∘ f_T = id`, and `f_T → v_T` at `r`.) -/
theorem extendFrom_eq_of_isForwardSol_real (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hT : 0 ≤ T) {r : ℝ} {v : ℝ → ℂ} (hv : QuantumZipper.IsForwardSol W (r : ℂ) T v) :
    extendFrom H (fwdMapInv W T) (v T) = r := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hv
  set E := Real.exp (2 / δ ^ 2 * T) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hball : ball (r : ℂ) (δ / E) ∈ 𝓝 (r : ℂ) := ball_mem_nhds _ (div_pos hδ hEpos)
  have hoff : ∀ᶠ z in 𝓝[H] (r : ℂ), z ∈ H \ fwdHull W T := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzH
    refine ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hv hδ hlow hzH ?_⟩
    rw [mem_ball, dist_eq] at hz
    calc ‖z - r‖ * E < δ / E * E := mul_lt_mul_of_pos_right hz hEpos
      _ = δ := div_mul_cancel₀ δ hEpos.ne'
  have hvT : (v T).im = 0 := im_eq_zero_of_isForwardSol_real hW hv ⟨hT, le_rfl⟩
  have hvH : v T ∈ Hbar := show (0 : ℝ) ≤ (v T).im by rw [hvT]
  have h1 : Tendsto (fwdMap W T) (𝓝[H] (r : ℂ)) (𝓝[H] (v T)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_fwdMap_of_isForwardSol hW hT hv,
      hoff.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT hz⟩
  have h2 := ((hη.hasBdryLimits hW hW0 hT).tendsto hvH).comp h1
  have h3 : Tendsto (fun z => fwdMapInv W T (fwdMap W T z)) (𝓝[H] (r : ℂ)) (𝓝 (r : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.congr' (hoff.mono fun z hz =>
      (QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT hz).symm)
  have := GlueImg.nhdsWithin_H_neBot r
  exact tendsto_nhds_unique h2 h3

/-- **Right of the image hull's right base point, the boundary value of `F_T` is a positive real point**, for a
continuous Loewner trace staying in `ℍ` on `(0, T]`. -/
theorem re_extendFrom_pos_of_chartAR_lt_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : chartAR W T < x) :
    (extendFrom H (fwdMapInv W T) x).im = 0 ∧ 0 < (extendFrom H (fwdMapInv W T) x).re := by
  have hM : rightImg W 0 T < x + W T := by rw [chartAR] at hx; linarith
  obtain ⟨r, hr, -, hg⟩ := exists_alive_gImg_eq hW hT hM
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hη hηH hW hW0 hr.ne' hT
  rcases isForwardSol_real_cases hW hW0 hT hv with ⟨-, -, hvT⟩ | ⟨hneg, -, -⟩
  · have hvx : v T = (x : ℂ) := by rw [hvT, hg]; push_cast; ring
    have h := extendFrom_eq_of_isForwardSol_real hη hW hW0 hT hv
    rw [hvx] at h
    rw [h]
    simp [hr]
  · exact absurd hneg (not_lt.2 hr.le)

/-- **Left of the image hull's left base point, the boundary value of `F_T` is a negative real point**, for a
continuous Loewner trace staying in `ℍ` on `(0, T]`. -/
theorem re_extendFrom_neg_of_lt_chartAL_of_mem_H (hη : IsLoewnerTrace W η) (hηH : ∀ s ∈ Ioc (0 : ℝ) T, η s ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : x < chartAL W T) :
    (extendFrom H (fwdMapInv W T) x).im = 0 ∧ (extendFrom H (fwdMapInv W T) x).re < 0 := by
  have hM : rightImg (fun s => -W s) 0 T < -x - W T := by rw [chartAL] at hx; linarith
  obtain ⟨y, hy, -, hg⟩ := exists_alive_gImg_eq hW.neg hT hM
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_mem_H hη hηH hW hW0 (x := -y) (by linarith : -y ≠ 0) hT
  rcases isForwardSol_real_cases hW hW0 hT hv with ⟨hpos, -, -⟩ | ⟨-, -, hvT⟩
  · exact absurd hpos (by linarith)
  · have hvx : v T = (x : ℂ) := by
      have hg' : gImg (fun s => -W s) y T = -x - W T := hg
      rw [hvT, neg_neg, hg']; push_cast; ring
    have h := extendFrom_eq_of_isForwardSol_real hη hW hW0 hT hv
    rw [hvx] at h
    rw [h]
    simp only [ofReal_im, ofReal_re, true_and]
    linarith

end InteractingSLE.Sec5.CrossRestart
