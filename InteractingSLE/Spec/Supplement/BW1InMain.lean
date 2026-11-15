/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1InEndDet
import InteractingSLE.Spec.Supplement.BW1InInt

/-!
# Proposition BW1: the endpoint PROVED; BW1 from the version and K2's (S)/(L)

Packet PROVE-BW1-INPUTS.

* **`bw1EndpointStatement`** (PROVED): `BW1Life.BW1EndpointStatement` from Theorem 1.3 (at universes `u` and `0`) —
  the probabilistic half is GB5 under the conditional law (`ae_mem_bwAvoid`), the deterministic half is
  `bw1EndpointDetStatement`.
* **`bw1Statement_of_version_law`**: Proposition BW1 (`BW1.BW1Statement`) from Theorems 1.2–1.3, the canonical driver
  code, and the two remaining named inputs `BW1RelVersionStatement` (measurable exhausting versions of the relative
  exploration) and `BW1RelSafeLawStatement` (K2's (S) and (L) for the relative exploration; its integrability and
  threshold clauses are proved).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.BW1In

open BW1Life

/-- **BW1's endpoint, PROVED** (p. 614–615, "The endpoint and all relative stopping times"). -/
theorem bw1EndpointStatement (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0}) :
    BW1EndpointStatement.{u} :=
  bw1EndpointStatement_of_det h13 hT13₀ bw1EndpointDetStatement

/-- **Proposition BW1 from the version and K2's (S) and (L)** (the endpoint, the integrability and the threshold
clauses are proved). -/
theorem bw1Statement_of_version_law (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hcode : Restart.CanonicalDriverCodeStatement) (hV : BW1RelVersionStatement.{u})
    (hL : BW1RelSafeLawStatement.{u}) : BW1.BW1Statement.{u} :=
  bw1Statement_of_inputs h12p h13 hT13₀ hcode hV (bw1RelSafeStatement_of_law hT13₀ hL) (bw1EndpointStatement h13 hT13₀)

end InteractingSLE.Theorem14.BW1In
