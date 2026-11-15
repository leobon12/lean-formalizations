/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12Beacon
import InteractingSLE.Spec.ZhanGT4.A1ERecWire
import InteractingSLE.Spec.Sec7.R6RelWire
import InteractingSLE.Spec.Sec5.StagedNPathNode
import InteractingSLE.Spec.Sec5.Prop55N

/-! # Committed inputs for the Theorem 1.2–1.3 assembly

Eight's first direction, G3's rows, and the node flag paths are proved.
R.6's phase-free certificate supplies the remaining shared-side input.
The Cond44 determination used here follows the acyclic R74 route.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Wire.T12Asm

open scoped Real
open QuantumZipper (chiC)
open Sec7 Sec7.RefWire

/-- Combine G3's two remaining directional laws on their actual parameter range. -/
theorem g3Law (hS : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hF : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ) :
    ∀ κ, ZhanGT4.A1RLaw.G3RectLawC κ := fun κ h4 h8 =>
  ZhanGT4.A1RLaw.g3RectLawC_of_dirs (hS κ h4 h8) (hF κ h4 h8) h4 h8

/-- Eight's first direction is the committed reconstruction theorem. -/
theorem eightLaw (hS : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ) :
    ∀ κ, ZhanGT4.A1RLaw.EightRectLawC κ := fun κ h8 =>
  ZhanGT4.A1RLaw.eightRectLawC_of_dirs (hS κ h8)
    (ZhanGT4.A1ERec.eightRectLawFstC κ) h8

/-- Cond44 determination from the three open C-law directions, by R74. -/
theorem cond44
    (hS : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawSndC κ)
    (hF : ∀ κ : ℝ, 4 < κ → κ < 8 → ZhanGT4.A1RLaw.G3RectLawFstC κ)
    (hE : ∀ κ : ℝ, 8 ≤ κ → ZhanGT4.A1RLaw.EightRectLawSndC κ) :
    AdmCode.Theorem12ParamCond44Statement.{0} :=
  Beacon.cond44 (g3Law hS hF) (eightLaw hE)

/-- R.6's certificate discharges Beacon's shared-side visits premise. -/
theorem sharedVisits
    (hG : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hE : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hCert : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      R6Rel.R6NestCertRemaining.{0} k rL rR) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → ¬ (rL < k - 6 ∧ rR < k - 6) →
      OuterPhNext.R7OuterSharedVisitsRemaining.{0} k rL rR := by
  have hA := late_partAInputs hG hE
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  have h51 := Beacon.prop51 hA hDy
  have h55 := Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51
  intro k hk rL rR hL hR hmax hbad
  exact R6Rel.r7OuterSharedVisitsRemaining_of_cert h55 hk hL hR
    (hCert k hk rL rR hL hR hmax hbad)

end InteractingSLE.Wire.T12Asm
