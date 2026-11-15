/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLawImage
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfBase

/-!
# Junction gaps and initial boundary data after earlier counterflow boundary contacts

PROVE-CROSSCOND-GEN. At a positive stop with an interior tip, both base gaps are
strict even if the trace touched the real line earlier. The existing theta data
calculation then identifies the entire initial image word off a finite set. These
results do not require `CfThetaBounds` or a globally interior counterflow trace.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMapInv chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu GlueImg MartChar.RealFlow Word49 Theta Cond44Ref Sec7.StripSysField

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- Only the present tip must lie in the upper half-plane to make the right base
gap positive. The nonsimple restart proof uses its stronger trace premise only here. -/
theorem chartAR_pos_of_interior_tip (hη : IsLoewnerTrace W η) (htip : η t ∈ H)
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
  have h3 : (0 : ℝ) < (η t).im := htip
  rw [h] at h3
  exact lt_irrefl _ h3

/-- The reflected base gap is negative under the same present-tip condition. -/
theorem chartAL_neg_of_interior_tip (hη : IsLoewnerTrace W η) (htip : η t ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 < t) : chartAL W t < 0 := by
  have hηR := CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hη
  have htipR : LP.reflectC (η t) ∈ H := by
    change 0 < (LP.reflectC (η t)).im
    simpa only [LP.im_reflectC] using (show 0 < (η t).im from htip)
  have hR := chartAR_pos_of_interior_tip hηR htipR hW.neg (by simp only [Pi.neg_apply, hW0, neg_zero]) ht
  change 0 < MartChar.RealFlow.rightImg (fun r => -W r) 0 t - -W t at hR
  change -MartChar.RealFlow.rightImg (fun r => -W r) 0 t - W t < 0
  linarith only [hR]

/-- The candidate original labels and the two junctions are ordered after earlier
counterflow boundary hits, provided the current stopped tip is interior. -/
theorem isOrderedForceWord_imageMarks_of_interior_tip
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (hη : IsLoewnerTrace W η) (htip : η t ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 < t) :
    IsOrderedForceWord (imageMarksL xL W t) (imageMarksR xR W t) :=
  isOrderedForceWord_imageMarks hF hW ht.le
    (chartAR_pos_of_interior_tip hη htip hW hW0 ht)
    (chartAL_neg_of_interior_tip hη htip hW hW0 ht)

/-- The full initial image boundary data, including all labels and the junction
weights, match the returned counterflow data outside a finite set. This reuses the
theta calculation; previous real contacts do not appear among its hypotheses. -/
theorem exists_finite_initial_data_match {κ θ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR)
    (hη : IsLoewnerTrace W η) (htip : η t ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 < t) :
    ∃ E : Set ℝ, E.Finite ∧ ∀ r : ℝ, r ∉ E →
      imgData0T ρL ρR xL xR θ κ W t r =
        returnData (cfOffset κ) (cfCoeff κ)
          (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
            (forceJumpFinset xL xR) W t) r + θ * chiC κ := by
  let J := forceJumpFinset xL xR
  let L := cfMarkL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ)) J W t
  let E : Set ℝ := {0, junL W t, junR W t} ∪ psiL W t '' (J : Set ℝ) ∪
    psiR W t '' (J : Set ℝ) ∪ Set.range (fun i => -(L i)⁻¹)
  have hEf : E.Finite :=
    (((Set.toFinite _).union ((Finset.finite_toSet J).image _)).union
      ((Finset.finite_toSet J).image _)).union (Set.finite_range _)
  refine ⟨E, hEf, fun r hr => ?_⟩
  have hr0 : r ≠ 0 := fun h => hr (by simp only [E, h, mem_union, mem_insert_iff, mem_singleton_iff]; tauto)
  have hrL : r ≠ junL W t := fun h => hr (by simp only [E, h, mem_union, mem_insert_iff, mem_singleton_iff]; tauto)
  have hrR : r ≠ junR W t := fun h => hr (by simp only [E, h, mem_union, mem_insert_iff, mem_singleton_iff]; tauto)
  have hpsiL : ∀ x ∈ J, psiL W t x ≠ r := by
    intro x hx he
    exact hr (Or.inl (Or.inl (Or.inr ⟨x, hx, he⟩)))
  have hpsiR : ∀ x ∈ J, psiR W t x ≠ r := by
    intro x hx he
    exact hr (Or.inl (Or.inr ⟨x, hx, he⟩))
  have hL : ∀ i, L i ≠ -r⁻¹ := by
    intro i he
    apply hr
    exact Or.inr ⟨i, by
      change -(L i)⁻¹ = r
      rw [he, inv_neg, inv_inv, neg_neg]⟩
  exact imgData0_eq_returnDataT ρL ρR xL xR θ hκ hW ht.le
    (chartAR_pos_of_interior_tip hη htip hW hW0 ht)
    (chartAL_neg_of_interior_tip hη htip hW hW0 ht)
    hF.2.1 hF.2.2.2 hr0 hrL hrR hpsiL hpsiR hL

/-- The initial image mean is the returned stopped counterflow mean with the
angle shift. Earlier counterflow boundary contacts introduce no extra input here:
uniqueness of bounded harmonic extension upgrades the finite data match. -/
theorem eqOn_initial_mean_of_interior_tip {κ θ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR)
    (hη : IsLoewnerTrace W η) (htip : η t ∈ H)
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 < t) {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (imgData0T ρL ρR xL xR θ κ W t)
      (forceJumpSet (imageMarksL xL W t) (imageMarksR xR W t)) u)
    (hv : IsBoundedHarmonicExtension
      (cfDataAt κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
        (forceJumpFinset xL xR) W t)
      (forceJumpSet
        (cfMarkL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
          (forceJumpFinset xL xR) W t)
        (cfMarkR κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
          (forceJumpFinset xL xR) W t)) v) :
    EqOn u (fun z => retMean κ v z + θ * chiC κ) H := by
  obtain ⟨E, hEf, hmatch⟩ := exists_finite_initial_data_match hκ ρL ρR xL xR hF hη htip hW hW0 ht
  have hvR := GlueCond.isBoundedHarmonicExtension_add_const
    (isBoundedHarmonicExtension_retMean (κ := κ) (S := forceJumpFinset
      (cfMarkL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
        (forceJumpFinset xL xR) W t)
      (cfMarkR κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
        (forceJumpFinset xL xR) W t)) (by rwa [coe_forceJumpFinset])) (θ * chiC κ)
  let SI := forceJumpSet (imageMarksL xL W t) (imageMarksR xR W t)
  let SC := returnExcept (forceJumpFinset
    (cfMarkL κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
      (forceJumpFinset xL xR) W t)
    (cfMarkR κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ))
      (forceJumpFinset xL xR) W t))
  have hSI : SI.Finite := by
    dsimp only [SI]
    rw [← coe_forceJumpFinset]
    exact Finset.finite_toSet _
  have hVS : IsBoundedHarmonicExtension (imgData0T ρL ρR xL xR θ κ W t)
      (E ∪ SI ∪ (SC : Set ℝ)) (fun z => retMean κ v z + θ * chiC κ) := by
    refine ⟨hvR.1, hvR.2.1, fun x hx => ?_⟩
    rw [hmatch x (fun h => hx (Or.inl (Or.inl h)))]
    exact hvR.2.2 x (fun h => hx (Or.inr h))
  have hUS : IsBoundedHarmonicExtension (imgData0T ρL ρR xL xR θ κ W t)
      (E ∪ SI ∪ (SC : Set ℝ)) u :=
    ⟨hu.1, hu.2.1, fun x hx => hu.2.2 x (fun h => hx (Or.inl (Or.inr h)))⟩
  exact PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension
    ((hEf.union hSI).union (Finset.finite_toSet SC)) hVS hUS

end InteractingSLE.Sec5.CrossCond.Gen
