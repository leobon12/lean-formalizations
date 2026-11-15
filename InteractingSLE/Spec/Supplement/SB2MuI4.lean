/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MuThr

/-!
# (I4) at the code level, deterministic part

Packet PROVE-SB2-LCMEAN, round 13 (handoff §R13.4). Pathwise facts that turn F2b′'s version-level (I4) into the
code-level bound "the canonical lifetime is at most the relative lifetime":

* `exists_isIntegratedSLEPath_of_truncWord`: an integrated path of the flow-line word is one of the type word read off
  the padded word (`truncWord_padFL`; the integrated-path form of
  `Cond.isStoppedHullCoupling_flowLineWord_of_truncWord`);
* **`le_of_forall_thr_le`**: if an integrated path has the property that every continuous driver agreeing with it on
  `[0, R]` has its geometric threshold time at most `R`, then its lifetime is at most `R` (freeze the driver at `R`;
  `lt_thr_of_isIntegratedSLEPath`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Mu

open Restart Exist Exist.Staged Exist.StagedLaw

/-- **An integrated path of the flow-line word is one of the type word** read off the padded word. -/
theorem exists_isIntegratedSLEPath_of_truncWord {a κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hnL : flowLineNL b J 0 = nL) (hnR : flowLineNR b J 0 = nR)
    (hw : truncWord nL nR (padFL κ θ b J) = ((xL, xR), (ρL, ρR))) {w : ℝ≥0 → ℝ}
    {vL : Fin (flowLineNL b J 0) → ℝ≥0 → ℝ} {vR : Fin (flowLineNR b J 0) → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) w vL vR B ζ) :
    ∃ (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ), IsIntegratedSLEPath a xL xR ρL ρR w vL' vR' B ζ := by
  subst hnL hnR
  rw [truncWord_padFL] at hw
  simp only [Prod.mk.injEq] at hw
  obtain ⟨⟨e1, e2⟩, e3, e4⟩ := hw
  subst e1 e2 e3 e4
  exact ⟨vL, vR, hp⟩

/-- **The lifetime of an integrated path is at most `R`** when every continuous driver agreeing with the path's driver
on `[0, R]` has its geometric threshold time (for the path's word) at most `R`. -/
theorem le_of_forall_thr_le {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ) {Ω : Type*} {xL' : Ω → Fin nL → ℝ}
    {xR' : Ω → Fin nR → ℝ} {ω : Ω} (hxL : xL' ω = xL) (hxR : xR' ω = xR) (R : ℝ≥0)
    (hlife : ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω', Continuous fun t => Wc t ω') → (∀ t : ℝ≥0, t ≤ R → Wc t ω = w t) →
      FCDet.thr ρL ρR Wc xL' xR' ω ≤ R) :
    ζ ≤ R := by
  by_contra hlt
  rw [not_le] at hlt
  have hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ} := hp.2.2.2.1
  have hcI : ContinuousOn w (Iic R) := hwc.mono fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (mem_Iic.1 ht)) hlt
  set Wc : ℝ≥0 → Ω → ℝ := fun t _ => w (min t R) with hWcdef
  have hWcc : ∀ ω', Continuous fun t => Wc t ω' := fun _ =>
    hcI.comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right t R)
  have hag : ∀ t : ℝ≥0, t ≤ R → Wc t ω = w t := fun t ht => by simp only [hWcdef, min_eq_left ht]
  have h1 := hlife Wc hWcc hag
  have h2 := lt_thr_of_isIntegratedSLEPath hp hWcc hxL hxR hlt hag
  exact absurd h1 (not_le.2 h2)

end InteractingSLE.Theorem14.SB.Mu
