/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9Stops

/-!
# Compact containment and bounded coordinate variation at the local stops

The existing level, coefficient and clock bounds are applied to local paths.
In the two-mark ordered region, continuity of the full density supplies the
uniform variation bound required by the existing localized Itô theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

variable {Ω : Type*} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}
  {ω : Ω} {n : ℕ}

/-- Before the local spatial stop the existing box level is nonnegative. -/
theorem level_nonneg_of_lt (hg : IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hω : ω ∈ G) {r : ℝ≥0} (hr : r < rLoc 0 G S W VL VR B e n ω) :
    0 ≤ rLev 0 n (Coupling.stateAt W VL VR r ω) := by
  by_contra hn
  have hre : (r : ℝ≥0∞) < e ω :=
    (ENNReal.coe_le_coe.2 hr.le).trans_lt ((hg.loc_lt (G := G) n).trans_le (sepTime_le _ _ _))
  have hhit := Coupling.hitBelow_le (f := fun s => rLev 0 n (Coupling.stateAt W VL VR s ω)) hre (not_le.1 hn)
  have hle := rLoc_le_rHit (k := 0) (G := G) (T := S) (W := W) (VL := VL) (VR := VR)
    (B := B) (ζ := e) n ω
  simp only [rHit, hω, ↓reduceIte] at hle
  exact (not_le_of_gt hr) (WithTop.coe_le_coe.1 (hle.trans hhit))

/-- Continuity gives the same bounds through a positive local stop. -/
theorem level_nonneg_of_le (hg : IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hω : ω ∈ G) (hσ : 0 < rLoc 0 G S W VL VR B e n ω) {r : ℝ≥0}
    (hr : r ≤ rLoc 0 G S W VL VR B e n ω) :
    0 ≤ rLev 0 n (Coupling.stateAt W VL VR r ω) := by
  rcases hr.lt_or_eq with hr | rfl
  · exact level_nonneg_of_lt hg hω hr
  let σ := rLoc 0 G S W VL VR B e n ω
  have hc : ContinuousOn (fun r => rLev 0 n (Coupling.stateAt W VL VR r ω))
      {t : ℝ≥0 | (t : ℝ≥0∞) < e ω} :=
    (continuous_rLev 0 n).comp_continuousOn (hg.path.continuousOn_w.prodMk
      ((continuousOn_pi.2 hg.path.continuousOn_vL).prodMk (continuousOn_pi.2 hg.path.continuousOn_vR)))
  have hat := hc.continuousAt ((Coupling.isOpen_setOf_coe_lt (e ω)).mem_nhds
    ((hg.loc_lt (G := G) n).trans_le (sepTime_le _ _ _)))
  have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ⟩
  refine ge_of_tendsto (hat.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio σ))) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact level_nonneg_of_lt hg hω hr

/-- Reciprocal target gaps are uniformly bounded up to a positive local stop. -/
theorem gap_bounds (hg : IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hω : ω ∈ G) (hσ : 0 < rLoc 0 G S W VL VR B e n ω) {r : ℝ≥0}
    (hr : r ≤ rLoc 0 G S W VL VR B e n ω) :
    ∀ u ∈ Icc (0 : ℝ) r, 0 < gap (W · ω) (VR 0 · ω) u ∧
      (gap (W · ω) (VR 0 · ω) u)⁻¹ ≤ (n : ℝ) + 1 := by
  intro u hu
  have h := (rLev_nonneg_iff.1 (level_nonneg_of_le hg hω hσ
    ((Sec2.toNNReal_le_of_mem_Icc hu).trans hr))).2.1
  have hq : 0 < gap (W · ω) (VR 0 · ω) u :=
    (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity).trans_le h
  refine ⟨hq, ?_⟩
  rw [inv_le_comm₀ hq (by positivity)]
  have h' : 1 / ((n : ℝ) + 1) ≤ gap (W · ω) (VR 0 · ω) u := h
  rwa [one_div] at h'

/-- The actual first-mark coordinates stay in the ordered compact box. -/
theorem mem_orderedBox (ha : 0 < a) (_hab : a < b)
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hω : ω ∈ G) {r : ℝ≥0} (hr : r ≤ rLoc 0 G S W VL VR B e n ω) :
    (rCoordAt a 0 (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) r, B r ω) ∈
      orderedBox κ xL ρL ρR a b n := by
  have hg := hgood ω hω
  have hre : (r : ℝ≥0∞) < e ω :=
    (ENNReal.coe_le_coe.2 hr).trans_lt ((hg.loc_lt (G := G) n).trans_le (sepTime_le _ _ _))
  refine ⟨?_, hg.path.monotone_vR hre (by decide)⟩
  rcases (zero_le (a := rLoc 0 G S W VL VR B e n ω)).lt_or_eq with hσ | hσ
  · right
    have hlev := rLev_nonneg_iff.1 (level_nonneg_of_le hg hω hσ hr)
    simp only [Coupling.stateAt] at hlev
    have hnorm : ‖((fun i => VL i r ω), fun i => VR i r ω)‖ ≤ n := hlev.1
    have hgb := gap_bounds hg hω hσ hr
    have hdrv : drv κ xL ![a, b] ρL ρR
        (rCoordAt a 0 (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) r, B r ω) = W r ω :=
      (w_eq_drv_of_upTo hg.path hre _ _ _).symm
    have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr.trans (rLoc_le_n n ω)
    refine ⟨(norm_fst_le (((fun i => VL i r ω), fun i => VR i r ω) :
      (Fin 0 → ℝ) × (Fin 2 → ℝ))).trans hnorm,
      (norm_snd_le (((fun i => VL i r ω), fun i => VR i r ω) :
        (Fin 0 → ℝ) × (Fin 2 → ℝ))).trans hnorm, ?_, ?_,
      (fun i => i.elim0), hlev.2.2, abs_alpha_le ha r.coe_nonneg, ?_, ?_⟩
    · rcases (zero_le (a := r)).lt_or_eq with hr0 | hr0
      · have hb := MathFin.abs_le_N_of_le_exitTime (continuous_brownG hgood) hr0
          ((WithTop.coe_le_coe.2 hr).trans (rLoc_le_exitTime n ω))
        simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using hb
      · rw [← hr0, hg.zeroB, abs_zero]; positivity
    · simp only [qOf]
      rw [hdrv]
      exact hlev.2.1
    · exact (abs_beta_le ha r.coe_nonneg hgb).trans (by unfold betaBd; gcongr)
    · exact (abs_clk_le ha r.coe_nonneg hgb).trans (by unfold clkBd; gcongr)
  · left
    have hr0 : r = 0 := le_antisymm (hr.trans hσ.symm.le) bot_le
    subst r
    rw [rCoordAt_zero hg.path.vL_zero hg.path.vR_zero, hg.zeroB]
    rfl

/-- The full masked coordinate density has uniformly bounded integral up to each local stop. -/
theorem exists_integral_density_bound (ha : 0 < a) (hab : a < b)
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω) (n : ℕ) :
    ∃ Kb : ℝ, ∀ ω, ∫ s in (0 : ℝ)..(rLoc 0 G S W VL VR B e n ω : ℝ),
      ‖rDens κ xL ![a, b] ρL ρR 0 a G W VL VR B s ω‖ ≤ Kb := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_density (κ := κ) (xL := xL) (ρL := ρL) (ρR := ρR) ha hab n
  refine ⟨C * n, fun ω => ?_⟩
  by_cases hω : ω ∈ G
  · have hg := hgood ω hω
    let σ := rLoc 0 G S W VL VR B e n ω
    have hi := (intervalIntegrable_rDensAt (hg.path.mono (sepTime_le _ _ _))
      (hg.data ha hab) (hg.loc_lt (G := G) n)).norm
    simp only [rDens, hω, ↓reduceIte]
    refine (intervalIntegral.integral_mono_on (g := fun _ : ℝ => C)
      σ.coe_nonneg hi intervalIntegrable_const ?_).trans ?_
    · intro s hs
      exact hC _ (mem_orderedBox ha hab hgood hω (Sec2.toNNReal_le_of_mem_Icc hs))
    · rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
      have hrn : (σ : ℝ) ≤ n := by
        exact_mod_cast rLoc_le_n (k := 0) (G := G) (T := S) (W := W) (VL := VL)
          (VR := VR) (B := B) (ζ := e) n ω
      exact mul_le_mul_of_nonneg_left hrn hC0
  · simp only [rDens, hω, ↓reduceIte, norm_zero, intervalIntegral.integral_zero]
    positivity

end InteractingSLE.Sec5.TwoMark.Mart9
