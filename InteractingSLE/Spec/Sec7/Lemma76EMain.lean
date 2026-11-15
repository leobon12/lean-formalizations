/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76EJunction

/-!
# Lemma 7.6 from its conditional-law content alone

Packet PROVE-LEMMA76E. With Aux. lemma 60 (`Lemma76E.pos_of_inv_mem_fst`) and the junction continuation inequality
(`Lemma76E.flowLineJunctionStatement`) proved, PROVE-LEMMA76D's named input `Lemma76CondDetStatement` follows from
`Lemma76CondDetHeightsStatement`, which keeps only the conditional-law content at a good disjoint pair: (R1), the
right-side heights of the conditional datum (`IsRightSideHeights`) and (Det).

* **`lemma76CondDetStatement_of_condDetHeights`**: `Lemma76CondDetStatement` from `Lemma76CondDetHeightsStatement`;
* **`lemma76Statement_of_condDetHeights`**, `lemma76Statement_of_param_heights`: Lemma 7.6 (both halves);
* `lemma76KernelStatement_of_condDetHeights`: PROVE-LEMMA76C's `Lemma76KernelStatement`.

**R43.** Canonical codes use Theorems 1.2–1.3; Lemma 7.6 feeds only the Theorem 1.5 route (Lemma 7.7, W8, Aux. 70).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE

namespace Sec7

open Restart

/-- **`Lemma76CondDetStatement` from its conditional-law content** (Aux. 60 and the junction inequality proved). -/
theorem lemma76CondDetStatement_of_condDetHeights (hD : Lemma76CondDetHeightsStatement.{u}) :
    Lemma76CondDetStatement.{u} :=
  lemma76CondDetStatement_of_heights Lemma76E.flowLineJunctionStatement hD

/-- **Lemma 7.6 (both halves) from canonical flow codes and the conditional-law content.** -/
theorem lemma76Statement_of_condDetHeights (hF : CanonicalFlowCodeStatement)
    (hD : Lemma76CondDetHeightsStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_condDet hF (lemma76CondDetStatement_of_condDetHeights hD)

/-- **Lemma 7.6 from Theorems 1.2 (measurable in the word) and 1.3 and the conditional-law content.** -/
theorem lemma76Statement_of_param_heights (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : Lemma76CondDetHeightsStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_param h12p h13 (lemma76CondDetStatement_of_condDetHeights hD)

/-- **PROVE-LEMMA76C's `Lemma76KernelStatement` from canonical flow codes and the conditional-law content.** -/
theorem lemma76KernelStatement_of_condDetHeights (hF : CanonicalFlowCodeStatement)
    (hD : Lemma76CondDetHeightsStatement.{u}) : Lemma76KernelStatement.{u} :=
  lemma76KernelStatement_of_condDet hF (lemma76CondDetStatement_of_condDetHeights hD)

end Sec7

end InteractingSLE
