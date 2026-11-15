/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TsTip
import InteractingSLE.Spec.Sec7.R6TsShared
import InteractingSLE.Spec.Sec7.R6TsReflect
import InteractingSLE.Spec.Sec7.R6TsSelect
import InteractingSLE.Spec.Sec7.R6TsNest

/-!
# The remaining incident Jordan boundary geometry

PROVE-R6-TWO, Astra §§2 and 4.3 (R98). These are explicitly named
geometric inputs, not proved existence statements. They contain no
later-time faces, chosen test points, physical agreement balls, or
normalization at the driver. The engine derives those conclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Sec7.R6Ts

open PocketStopSide Sec6

/-- The finite boundary part of the inverse of an ambient Jordan-face
uniformizer. Its existence for the selected face is still geometric.
Aux. 136 will prove the missing driver normalization. -/
structure AmbientInverseFactor (W : ℝ → ℝ) (t : ℝ) (E : ℂ → ℂ) where
  lift : ℂ → ℂ
  maps : MapsTo lift Hbar Hbar
  injective : InjOn lift Hbar
  factor : ∀ x : ℝ, E (x : ℂ) = extendFrom H (fwdMapInv W t) (lift x)

/-- **Named remaining force correspondence.** This is identification of
the prescribed transported incident seed mark, not uniqueness of the
physical force landing. It includes the seed-corner case. -/
def SharedForceIdentification (O I : Chart) (v w : ℝ) : Prop :=
  extendFrom ((pocketTransitionChart O I).dom : Set ℂ)
    (pocketTransitionChart O I).1 (v : ℂ) = (w : ℂ)

/-- **Named remaining geometry of Astra §2.5 and the unvisited shared
wall.** The inner initial coordinate is continuous on `P` (typically
the closed pocket with a finite target removed). `D` is the ambient
active domain at the common original time. Only initial-pocket local
agreement is supplied at shared wall points. Agreement of the selected
current components, and the reflected boundary values, are proved. -/
structure IncidentIntervalGeometry (C V P D : Set ℂ) (O I : Chart)
    (EO : ℂ → ℂ) (v w : ℝ) where
  interval : Set ℝ
  isOpen : IsOpen interval
  isPreconnected : IsPreconnected interval
  force_mem : v ∈ interval
  driver_mem : 0 ∈ interval
  force_neg : v < 0
  collars : ∀ x ∈ interval, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' (I.dom : Set ℂ)
  landing_mem : ∀ x ∈ interval, EO (x : ℂ) ∈ P
  force_identification : SharedForceIdentification O I v w
  shared_active : ∀ x ∈ interval, x < v → EO (x : ℂ) ∈ D
  shared_locally_connected : ∀ x ∈ interval, x < v → IsLocConnWithin C (EO (x : ℂ))
  shared_initial_wall : ∀ x ∈ interval, x < v →
    ∃ r > 0, C ∩ ball (EO (x : ℂ)) r ⊆ V

end InteractingSLE.Sec7.R6Ts
