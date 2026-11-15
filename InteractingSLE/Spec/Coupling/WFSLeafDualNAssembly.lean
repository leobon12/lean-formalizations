/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDualNDouglas
import InteractingSLE.Spec.Coupling.WFSLeafMartMAssembly

/-!
# Full-evolution cylinder regularity and the WFS endpoint

Douglas separation is now proved. The fixed cylinder-regularity target has
no remaining named input. WFS uses only the packet-permitted Theorems 1.2
and 1.3, with no further regularity or joint-law assumption.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE.WFS

/-- Full-evolution cylinder regularity, without an auxiliary theorem input. -/
theorem fullEvolutionCylinderRegularityStatement {κ : ℝ} (hκ : 0 < κ) :
    FullEvolutionCylinderRegularityStatement.{u} κ :=
  fullEvolutionCylinderRegularityStatement_of_douglas douglasL1SeparationStatement hκ

/-- The WFS leaf, using only the permitted Theorems 1.2 and 1.3. -/
theorem throughKernelStatement
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) : ThroughKernelStatement.{u, u} κ :=
  throughKernelStatement_of_douglas h12 h13 douglasL1SeparationStatement hκ

end InteractingSLE.WFS
