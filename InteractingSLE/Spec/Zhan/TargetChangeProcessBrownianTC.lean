/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianTime

/-!
# `b̃` is a Brownian motion, part 5: the martingales in the new time

Packet PROVE-SEC7-C9. The new-time noise before the horizon is

  `bv0 v = (Ψ(Λ_{C⁻¹(v)}, b_{C⁻¹(v)}) − Ψ₀)/√κ`

(`bv0`; `0` off the good event). Reading the localized martingales of part 3 at the inverse clock (part 4), with
`S_n = C(σ_n)` (`newS`), the processes

* `bv0(u ∧ S_n)` (`martingale_bv0_stopped`),
* `bv0(u ∧ S_n)² − u ∧ S_n` (`martingale_bv0_sq_stopped`),
* `exp(a bv0(u ∧ S_n) − a²(u ∧ S_n)/2)` (`martingale_exp_bv0_stopped`)

are martingales of the new filtration `𝓗 = filtH`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL j m : ℕ}

/-- **The new-time noise before the horizon**: `(Ψ(Λ_{C⁻¹(v)}, b_{C⁻¹(v)}) − Ψ₀)/√κ` (`0` off the good event). -/
def bv0 (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ)
    (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (v : ℝ≥0) (ω : Ω) : ℝ :=
  (obs κ xL xR ρL ρR (LP.retargetIdx j m)
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR (invClk (rateT xR W VR ω) v).toNNReal ω,
        Sec2.TwoSeed.brownG G B (invClk (rateT xR W VR ω) v).toNNReal ω) -
    obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR))) / Real.sqrt κ

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-! ### Continuity and boundedness of the stopped observables -/

section Stopped

variable (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hD : LP.IsDistinctForceWord xL xR)
  (hj : 1 ≤ j)

include hgood hD hj in
theorem continuousOn_rCoordAt_Iic {ω : Ω} (hω : ω ∈ G) (n : ℕ) :
    ContinuousOn (fun s => rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) (W · ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) s) (Iic (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) := by
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hω' := hgood ω hω
  have hF := hω'.1.isForcePath
  set σ := rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω
  have hσs : ((σ : ℝ≥0) : ℝ≥0∞) < sepTime (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω) :=
    lt_sepTime_of_le_rLoc hω' hω hD hj le_rfl
  have hp := hω'.1.isSLEPathUpTo (sepTime_le (W · ω) (VR (LP.retargetIdx j m) · ω) (ζ ω))
  have hd := retargetData_of_isSLEPathUpTo hp hD hj fun _ ht => lt_of_lt_sepTime ht
  have hS := hd.sep.isSep_of_lt hσs
  have hsub : Iic σ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
    fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) (rLoc_lt_lifetime hω')
  have hmaps : MapsTo (fun s : ℝ≥0 => (s : ℝ)) (Iic σ) (Icc 0 (σ : ℝ)) :=
    fun s hs => ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  have hα := (hS.continuousOn_alpha (xk := LP.retargetPos xR)).comp NNReal.continuous_coe.continuousOn hmaps
  have hβ := (hS.continuousOn_beta (xk := LP.retargetPos xR)).comp NNReal.continuous_coe.continuousOn hmaps
  have hc := ((hS.isRate hpos).continuousOn_clk).comp NNReal.continuous_coe.continuousOn hmaps
  exact (continuousOn_pi.2 fun i => (hF.continuousOn_vL i).mono hsub).prodMk
    ((continuousOn_pi.2 fun i => (hF.continuousOn_vR i).mono hsub).prodMk (hα.prodMk (hβ.prodMk hc)))

include hgood hD hj in
theorem continuous_rCoord_stopped (n : ℕ) (ω : Ω) :
    Continuous fun t => rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω := by
  by_cases hω : ω ∈ G
  · simp only [rCoord, hω, ↓reduceIte]
    exact (continuousOn_rCoordAt_Iic hgood hD hj hω n).comp_continuous
      (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right _ _)
  · simp only [rCoord, hω, ↓reduceIte]; exact continuous_const

include hgood in
theorem continuous_brownG_stopped_r (n : ℕ) (ω : Ω) :
    Continuous fun t => Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω :=
  (continuous_brownG_r hgood ω).comp (continuous_id.min continuous_const)

include hgood hD hj in
theorem mem_rKc_rCoord (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) ∈
      rKc κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) n := by
  by_cases hω : ω ∈ G
  · simpa only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte] using
      mem_rKc_of_le_rLoc (hgood ω hω) hω hD hj hgood (min_le_right t _)
  · simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    exact mem_insert _ _

include hgood hD hj in
theorem exists_bound_rObs {F : RCoord nL (j + 1 + m) × ℝ → ℝ}
    (hF : ContinuousOn F (obsRegion κ xL xR ρL ρR (LP.retargetIdx j m))) (n : ℕ) :
    ∃ C, ∀ t ω, |F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_rKc κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) n).exists_bound_of_continuousOn
    (hF.mono (rKc_subset_obsRegion κ xL xR ρL ρR _ _ (rInit_mem_obsRegion hD hj _) n))
  exact ⟨C, fun t ω => by
    have := hC _ (mem_rKc_rCoord hgood hD hj n t ω); rwa [Real.norm_eq_abs] at this⟩

include hgood hD hj in
theorem continuous_rObs {F : RCoord nL (j + 1 + m) × ℝ → ℝ}
    (hF : ContinuousOn F (obsRegion κ xL xR ρL ρR (LP.retargetIdx j m))) (n : ℕ) (ω : Ω) :
    Continuous fun t => F (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
      Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) :=
  hF.comp_continuous ((continuous_rCoord_stopped hgood hD hj n ω).prodMk
    (continuous_brownG_stopped_r hgood n ω)) fun t =>
      rKc_subset_obsRegion κ xL xR ρL ρR _ _ (rInit_mem_obsRegion hD hj _) n (mem_rKc_rCoord hgood hD hj n t ω)

end Stopped

/-! ### Evaluation at the time change -/

section Eval

variable (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω) (hD : LP.IsDistinctForceWord xL xR)
  (hj : 1 ≤ j)

include hgood hD hj in
theorem rCoord_capTime_eq (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω)
        (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω =
    rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal ω := by
  by_cases hω : ω ∈ G
  · rw [min_capTime_newT_rLoc (hgood ω hω) hω hD hj n u]
  · simp only [rCoord, hω, ↓reduceIte]

include hgood hD hj in
theorem brownG_capTime_eq (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    Sec2.TwoSeed.brownG G B (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω)
        (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω =
    Sec2.TwoSeed.brownG G B (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal ω := by
  by_cases hω : ω ∈ G
  · rw [min_capTime_newT_rLoc (hgood ω hω) hω hD hj n u]
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]

include hgood hD hj in
/-- The clock coordinate at `C⁻¹(u ∧ S_n)` is `u ∧ S_n`. -/
theorem rCoord_clk_eq (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (invClk (rateT xR W VR ω) (min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)).toNNReal ω).2.2.2.2 =
      ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) := by
  by_cases hω : ω ∈ G
  · have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
    have hg := hgood ω hω
    have hS := sepUpTo_of_good hg hD hj
    have hσT := rLoc_lt_sepT hg hω hD hj (T := T) (B := B) (VL := VL) n
    obtain ⟨-, hlt⟩ := clk_lt_newHorizon' hS hpos hσT
    have hv : (((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0)) : ℝ≥0∞) < horT xR W VR ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hlt
    obtain ⟨S, _, _, _, hm, _⟩ := newTime_spec hS hpos hv
    have h0 : 0 ≤ invClk (rateT xR W VR ω) ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) := hm.1
    have hc : clk (rateT xR W VR ω) (invClk (rateT xR W VR ω) ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ))
        = ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) := clk_invClk_of_lt hS hpos hv
    simp only [rCoord, hω, ↓reduceIte, rCoordAt]
    show clk (rateT xR W VR ω) ((invClk (rateT xR W VR ω) _).toNNReal : ℝ) = _
    rw [Real.coe_toNNReal _ h0, hc]
  · simp only [rCoord, hω, ↓reduceIte, newS, rLoc_of_not_mem hω, NNReal.coe_zero, clk_zero,
      Real.toNNReal_zero, min_zero]

include hgood hD hj in
/-- The observable at `C⁻¹(u ∧ S_n)` is `√κ bv0(u ∧ S_n) + Ψ₀`. -/
theorem obs_capTime_eq (hκ : 0 < κ) (n : ℕ) (u : ℝ≥0) (ω : Ω) :
    obs κ xL xR ρL ρR (LP.retargetIdx j m)
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω)
          (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
       Sec2.TwoSeed.brownG G B (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ u) ω)
          (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) =
      Real.sqrt κ * bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω +
        obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) := by
  rw [rCoord_capTime_eq hgood hD hj, brownG_capTime_eq hgood hD hj, bv0,
    mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 hκ), sub_add_cancel]

end Eval

/-! ### The martingales in the new time -/

section NewMart

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)

include hE hGm hGc hgood hT hD hj in
/-- **`bv0(u ∧ S_n)` is a martingale of the new filtration.** -/
theorem martingale_bv0_stopped (hκ : 0 < κ) (n : ℕ) :
    Martingale (fun u ω => bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω)
      (filtH hE hGm hGc hgood hT hD hj) P := by
  have hP := hE.1.isProbabilityMeasure'
  obtain ⟨C, hC⟩ := exists_bound_rObs hgood hD hj
    (contDiffOn_obs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (k := LP.retargetIdx j m)
      (n := 0)).continuousOn n
  have hM : Martingale _ (filtH hE hGm hGc hgood hT hD hj) P :=
    martingale_comp_timeChange (isStoppingTime_newT hE hGm hGc hgood hT hD hj)
    (newT_mono' hgood hD hj) (martingale_obs_stopped hE hGm hGc hgood hT hD hj hκ.le n)
    (continuous_rObs hgood hD hj (contDiffOn_obs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
      (k := LP.retargetIdx j m) (n := 0)).continuousOn n) hC n (1 / Real.sqrt κ)
    (-(obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) / Real.sqrt κ))
  convert hM using 1
  funext u ω
  rw [obs_capTime_eq hgood hD hj hκ]
  field_simp
  ring

include hE hGm hGc hgood hT hD hj in
/-- **`bv0(u ∧ S_n)² − u ∧ S_n` is a martingale of the new filtration.** -/
theorem martingale_bv0_sq_stopped (hκ : 0 < κ) (n : ℕ) :
    Martingale (fun u ω => bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω ^ 2 -
      ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ)) (filtH hE hGm hGc hgood hT hD hj) P := by
  have hP := hE.1.isProbabilityMeasure'
  set c := obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) with hc
  obtain ⟨C, hC⟩ := exists_bound_rObs hgood hD hj
    (contDiffOn_obs2 κ xL xR ρL ρR (LP.retargetIdx j m) c (n := 0)).continuousOn n
  have hM : Martingale _ (filtH hE hGm hGc hgood hT hD hj) P :=
    martingale_comp_timeChange (isStoppingTime_newT hE hGm hGc hgood hT hD hj)
    (newT_mono' hgood hD hj) (martingale_obs2_stopped hE hGm hGc hgood hT hD hj hκ.le c n)
    (continuous_rObs hgood hD hj (contDiffOn_obs2 κ xL xR ρL ρR (LP.retargetIdx j m) c (n := 0)).continuousOn n)
    hC n (1 / κ) 0
  convert hM using 1
  funext u ω
  simp only [obs2]
  rw [obs_capTime_eq hgood hD hj hκ, rCoord_capTime_eq hgood hD hj, rCoord_clk_eq hgood hD hj,
    add_sub_cancel_right, mul_pow, Real.sq_sqrt hκ.le]
  field_simp
  ring

include hE hGm hGc hgood hT hD hj in
/-- **`exp(a bv0(u ∧ S_n) − a²(u ∧ S_n)/2)` is a martingale of the new filtration.** -/
theorem martingale_exp_bv0_stopped (hκ : 0 < κ) (a : ℝ) (n : ℕ) :
    Martingale (fun u ω => Real.exp (a * bv0 κ xL xR ρL ρR G W VL VR B (min u (newS xR G T W VL VR B ζ n ω)) ω -
      a ^ 2 * ((min u (newS xR G T W VL VR B ζ n ω) : ℝ≥0) : ℝ) / 2)) (filtH hE hGm hGc hgood hT hD hj) P := by
  have hP := hE.1.isProbabilityMeasure'
  set c := obs κ xL xR ρL ρR (LP.retargetIdx j m) (rInit xL xR (LP.retargetPos xR)) with hc
  obtain ⟨C, hC⟩ := exists_bound_rObs hgood hD hj
    (contDiffOn_expObs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (k := LP.retargetIdx j m) a
      (n := 0)).continuousOn n
  have hM : Martingale _ (filtH hE hGm hGc hgood hT hD hj) P :=
    martingale_comp_timeChange (isStoppingTime_newT hE hGm hGc hgood hT hD hj)
    (newT_mono' hgood hD hj) (martingale_expObs_stopped hE hGm hGc hgood hT hD hj hκ a n)
    (continuous_rObs hgood hD hj (contDiffOn_expObs (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
      (k := LP.retargetIdx j m) a (n := 0)).continuousOn n)
    hC n (Real.exp (-(a / Real.sqrt κ * c))) 0
  convert hM using 1
  funext u ω
  simp only [expObs]
  rw [obs_capTime_eq hgood hD hj hκ, rCoord_capTime_eq hgood hD hj, rCoord_clk_eq hgood hD hj, add_zero,
    ← Real.exp_add]
  congr 1
  field_simp
  ring

end NewMart

end Retarget

end Zhan

end InteractingSLE
