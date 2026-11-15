/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BnStop
import InteractingSLE.Spec.Supplement.GW2JDetR11Data

/-!
# The near buffer and target are functions of the shape (decision D16)

Packet PROVE-GW2-BUF (round 11). `nearBuffer f n` and `nearTarget f` read the near family only through its shape
`(nL, nR, mL, mR, goLeft)`.

* `famShapeB f`: the shape of a near family (SDE's `famShape`, rebuilt from committed parts).
* `bufOfShape K n`, `targetOfShape K`: the buffer and the target of a shape cell.
* **`nearBuffer_eq_bufOfShape`**, **`nearTarget_eq_targetOfShape`**: definitional.

These are the `Bsh` of `GW2BnStop.shapeStop`.
-/

set_option autoImplicit false
noncomputable section

open Set

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open GW2JDetR11 GW2TipSystem GW2TipSystem.RootN4

/-- The shape of a near family. -/
def famShapeB {κ : ℝ} (f : NearCrossingFamily.{u} κ) : NearShape := (f.nL, f.nR, f.mL, f.mR, f.goLeft)

/-- The near buffer of a shape cell. -/
def bufOfShape (K : NearShape) (n : ℕ) : Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ)) :=
  if K.2.2.2.2 then CS3Cross.leftBuf K.2.2.1 K.2.1 n else CS3Cross.rightBuf K.1 K.2.2.2.1 n

/-- The near target of a shape cell. -/
def targetOfShape (K : NearShape) : Set (ℝ × (Fin K.1 → ℝ) × (Fin K.2.1 → ℝ)) :=
  if K.2.2.2.2 then CS3Cross.leftTarget else CS3Cross.rightTarget

theorem nearBuffer_eq_bufOfShape {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) :
    nearBuffer f n = bufOfShape (famShapeB f) n := rfl

theorem nearTarget_eq_targetOfShape {κ : ℝ} (f : NearCrossingFamily.{u} κ) :
    nearTarget f = targetOfShape (famShapeB f) := rfl

end InteractingSLE.Theorem14.GW2Bh
