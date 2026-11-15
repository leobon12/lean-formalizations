/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdTop

/-! # The raised angle-zero word is the original angle word -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sf

open GW2Rd Restart Exist.StagedLaw PiecewiseConstantBoundaryData

/-- A typing of the raised word at angle zero types the original word at
 angle theta, including the seed marks and all genuine jump marks. -/
theorem isFlowType_of_upW {κ θ : ℝ} {c : BoundaryWord} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (ht : FCDet.IsFlowType κ 0 (upW (θ * chiC κ) c) xL xR ρL ρR) :
    FCDet.IsFlowType κ θ c xL xR ρL ρR := by
  have hJ := jumpSet_add_const c.isPiecewiseConstantBoundaryData (θ * chiC κ)
  have hL := leftLim_add_const c.isPiecewiseConstantBoundaryData (θ * chiC κ)
  have hR := rightLim_add_const c.isPiecewiseConstantBoundaryData (θ * chiC κ)
  let T (K : Finset ℝ) (L R : ℝ → ℝ) (β : ℝ) : Prop :=
    ∃ (eL : (K.filter (· < 0)).card + 1 = nL)
      (eR : (K.filter (0 < ·)).card + 1 = nR),
      (fun i => xL (Fin.cast eL i)) =
        Fin.cons 0 (fun i => (K.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i) - 0) ∧
      (fun j => xR (Fin.cast eR j)) =
        Fin.cons 0 (fun i => (K.filter (0 < ·)).orderEmbOfFin rfl i - 0) ∧
      (fun i => ρL (Fin.cast eL i)) =
        Fin.cons (-(L 0 + β * chiC κ) / sleLambda κ - 1)
          (fun i => let y := (K.filter (· < 0)).orderEmbOfFin rfl (Fin.rev i)
            (R y - L y) / sleLambda κ) ∧
      (fun j => ρR (Fin.cast eR j)) =
        Fin.cons ((R 0 + β * chiC κ) / sleLambda κ - 1)
          (fun i => let y := (K.filter (0 < ·)).orderEmbOfFin rfl i
            (R y - L y) / sleLambda κ)
  change T (jumpSet (fun y => c.fn y + θ * chiC κ) c.jumps)
    (leftLim (fun y => c.fn y + θ * chiC κ))
    (rightLim (fun y => c.fn y + θ * chiC κ)) 0 at ht
  change T (jumpSet c.fn c.jumps) (leftLim c.fn) (rightLim c.fn) θ
  rw [hJ, hL, hR] at ht
  simpa only [T, zero_mul, add_zero, add_sub_add_right_eq_sub] using ht

end InteractingSLE.Theorem14.GW2Sf
