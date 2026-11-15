/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuVer2
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# No threshold before the lifetime of an integrated path, read with the geometric force points

Packet PROVE-SB2-LCMEAN, round 13, step 1 of (I4) at the code level (handoff §R13.4). Along an integrated
`SLE_κ(ρ)` path the force coordinates are the geometric images of the frozen driver
(`Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive`, `vR_eq_rightImg_frozenDrive`) and there is no threshold before
the lifetime. So every continuous driver that agrees with the path's driver up to a time `T` below the lifetime has its
geometric threshold time (`FCDet.thr`) strictly after `T` (a finite threshold time is attained,
`FCDet.thr_mem_thresholdSet`):

* **`lt_thr_of_isIntegratedSLEPath`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Sec7.PocketTraversal MartChar.RealFlow

/-- **No threshold up to `T` for a driver agreeing with an integrated path up to `T < ζ`**: its geometric threshold
time is strictly after `T`. -/
theorem lt_thr_of_isIntegratedSLEPath {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W' t ω) {xL' : Ω → Fin nL → ℝ} {xR' : Ω → Fin nR → ℝ} {ω : Ω}
    (hxL : xL' ω = xL) (hxR : xR' ω = xR) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ)
    (hag : ∀ t : ℝ≥0, t ≤ T → W' t ω = w t) :
    (T : ℝ≥0∞) < FCDet.thr ρL ρR W' xL' xR' ω := by
  by_contra hle
  rw [not_lt] at hle
  have hfin : FCDet.thr ρL ρR W' xL' xR' ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  set τ : ℝ≥0 := (FCDet.thr ρL ρR W' xL' xR' ω).toNNReal with hτdef
  have hτ : FCDet.thr ρL ρR W' xL' xR' ω = τ := (ENNReal.coe_toNNReal hfin).symm
  have hmem := FCDet.thr_mem_thresholdSet (ρL := ρL) (ρR := ρR) hWc xL' xR' hτ
  have hτT : τ ≤ T := by
    have h1 : (τ : ℝ≥0∞) ≤ T := hτ ▸ hle
    exact_mod_cast h1
  have hτζ : (τ : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hτT) hT
  have hTζ : ENNReal.ofReal (T : ℝ) < ζ := by rwa [ENNReal.ofReal_coe_nnreal]
  have hnt := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 τ hτζ
  apply hnt
  have hfr : ∀ r ∈ Icc (0 : ℝ) τ, (fun s => -frozenDrive w T s) r = Bessel.realPath (fun t ω => -W' t ω) ω r := by
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans (by exact_mod_cast hτT)⟩
    simp only [Bessel.realPath]
    rw [frozenDrive_eq hrT, hag r.toNNReal ((Real.toNNReal_le_iff_le_coe).2 hrT.2)]
  have hfr' : ∀ r ∈ Icc (0 : ℝ) τ, frozenDrive w T r = Bessel.realPath W' ω r := by
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans (by exact_mod_cast hτT)⟩
    simp only [Bessel.realPath]
    rw [frozenDrive_eq hrT, hag r.toNNReal ((Real.toNNReal_le_iff_le_coe).2 hrT.2)]
  have hcW : Continuous (Bessel.realPath W' ω) := (hWc ω).comp continuous_real_toNNReal
  have hcW' : Continuous (Bessel.realPath (fun t ω => -W' t ω) ω) :=
    ((hWc ω).comp continuous_real_toNNReal).neg
  have eL : (fun i => vL i τ) = fun i => geomLW W' xL' i τ ω := by
    funext i
    rw [Sec7.SideHeight.vL_eq_neg_rightImg_frozenDrive hp hTζ (by exact_mod_cast hτT) i]
    simp only [geomLW, hxL]
    rw [Supp8.GB6.rightImg_congr hcW' τ.coe_nonneg hfr]
  have eR : (fun j => vR j τ) = fun j => geomRW W' xR' j τ ω := by
    funext j
    rw [Sec7.SideHeight.vR_eq_rightImg_frozenDrive hp hTζ (by exact_mod_cast hτT) j]
    simp only [geomRW, hxR]
    rw [Supp8.GB6.rightImg_congr hcW τ.coe_nonneg hfr']
  rw [eL, eR, ← hag τ hτT]
  exact hmem

end InteractingSLE.Theorem14.SB.Mu
