/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeInf
import InteractingSLE.Spec.Sec7.R6FinWire

/-!
# `R6NestCertRemaining` in the mixed case and the outer phase input, R48-safe

PROVE-R6-SAFE. The wiring of PROVE-R6-CERT2 (`R6Fin.r6NestCertRemaining_of_geom`,
`R6Fin.r7OuterPhaseSideRemaining_of_cont_geom` and their `…_core` forms) **without** the input
`hstrip : R7StripOnConfig` (a full strip system on every R.7 configuration, which PROVE-STRIPSYS-SAFE showed is not
R48-constructible): the certificates come from `twoSeedNestCertInput_of_geom_safe` /
`twoSeedNestCertInputInf_of_geom_safe`, which build a constant-angle strip system from `h44` alone. The named inputs
are otherwise those of the `R6Fin` versions, verbatim.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Safe

open R6Fin R7Outer R7Leaves R6Nest R6Rel

variable {k rL rR : ℝ}

/-- **`R6NestCertRemaining` in the mixed case, R48-safe** (supplement p. 476, "Application to a mixed pocket";
`R6Fin.r6NestCertRemaining_of_geom` without `hstrip`): on every R.7 configuration, both outer pocket shapes
(`twoSeedNestCertInput_of_geom_safe`, `twoSeedNestCertInputInf_of_geom_safe` at the margins `(πχ(16/k), 0)`). -/
theorem r6NestCertRemaining_of_geom_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hgeom : R6GeomMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hgeomI : R6GeomMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hgeomII : R6GeomMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    R6NestCertRemaining.{u} k rL rR := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedNestCertInput_of_geom_safe h411 h51 h47 h47T haux7 h44 hword hgeom hk4 hL hR le_rfl le_rfl hmix
      hcfg hD hu₀' hV hGm hconf hζG hcfgP,
    twoSeedNestCertInputInf_of_geom_safe h411 h51 h47 h47T haux7 h44 hword hgeomI hgeomII hk4 hL hR le_rfl le_rfl
      hmix hcfg hD hu₀' hV hGm hconf hζG hcfgI⟩

/-- **The outer phase input from R.5 with continuity, the mixed-case R.6 certificates and the two-outer-arm
certificates**, R48-safe (drop-in for `R6Rel.r7OuterPhaseSideRemaining_of_cont_cert`; `R6Fin`'s version without
`hstrip`): outside Aux. 122's bounded sector the mixed case is `r6NestCertRemaining_of_geom_safe`; the two-outer-arm
case is the input `htwo`. -/
theorem r7OuterPhaseSideRemaining_of_cont_geom_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hgeom : R6GeomMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hgeomI : R6GeomMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hgeomII : R6GeomMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwo : k / 2 - 4 < rL → k / 2 - 4 < rR → R6NestCertRemaining.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  R6Rel.r7OuterPhaseSideRemaining_of_cont_cert
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51) hk4 hrL hrR hcont fun hbad =>
      (mixed_or_twoOuter hk4 hbad).elim
        (fun hmix => r6NestCertRemaining_of_geom_safe h411 h51 h47 h47T haux7 h44 hword hgeom hgeomI hgeomII hk4
          hrL hrR hmix)
        fun h => htwo h.1 h.2

/-- **`R6NestCertRemaining` in the mixed case from the core geometry inputs**, R48-safe (`…_of_geom_safe` with
`r6GeomMixedRemaining_of_core`, `r6GeomMixedInfRemaining_of_core`, `r6GeomMixedInfInfRemaining_of_core`). -/
theorem r6NestCertRemaining_of_core_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcore : R6GeomCoreMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreI : R6GeomCoreMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreII : R6GeomCoreMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    R6NestCertRemaining.{u} k rL rR :=
  r6NestCertRemaining_of_geom_safe h411 h51 h47 h47T haux7 h44 hword (r6GeomMixedRemaining_of_core hcore)
    (r6GeomMixedInfRemaining_of_core hcoreI) (r6GeomMixedInfInfRemaining_of_core hcoreII) hk4 hL hR hmix

/-- **The outer phase input from the core geometry inputs**, R48-safe (as
`r7OuterPhaseSideRemaining_of_cont_geom_safe`). -/
theorem r7OuterPhaseSideRemaining_of_cont_core_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcore : R6GeomCoreMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreI : R6GeomCoreMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreII : R6GeomCoreMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwo : k / 2 - 4 < rL → k / 2 - 4 < rR → R6NestCertRemaining.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_geom_safe h411 h51 h47 h47T haux7 h44 hword (r6GeomMixedRemaining_of_core hcore)
    (r6GeomMixedInfRemaining_of_core hcoreI) (r6GeomMixedInfInfRemaining_of_core hcoreII) hk4 hrL hrR hcont htwo

end InteractingSLE.Sec7.R6Safe
