/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FinInf
import InteractingSLE.Spec.Sec7.R6RelWire
import InteractingSLE.Spec.Sec7.R6FinGeomCore

/-!
# `R6NestCertRemaining` in the mixed case, and the outer phase input

PROVE-R6-CERT2. `r6NestCertRemaining_of_geom` proves PROVE-R6-NESTREL's named input `R6Rel.R6NestCertRemaining k r_L
r_R` in the **mixed case** (exactly one outer arm: `d < r_L, r_R ≤ d` or `r_L ≤ d < r_R`, `d = k/2 − 4`) from:

* the landed named inputs of the R.7 wiring: Props. 4.11Q, 5.1Q (hence 5.5), Lemma 4.7Q's hit laws, Aux. 7,
  `Theorem12ParamCond44Statement` (R74) and a strip system on every configuration (`R7StripOnConfig`);
* the inner pockets' R.5 word up to phase at the inner weights and margins (`PhaseCont.R7PhaseWordRemaining`,
  PROVE-POCKET-SIDEIN's target);
* the three named pathwise current-face geometry inputs `R6GeomMixedRemaining`, `R6GeomMixedInfRemaining`,
  `R6GeomMixedInfInfRemaining` (the transition across `J`, collars, landings and local agreement of the two active
  complements).

`r7OuterPhaseSideRemaining_of_cont_geom` is the drop-in for `R6Rel.r7OuterPhaseSideRemaining_of_cont_cert`: the
certificates of the mixed case are proved, and the two-outer-arm case remains the input `htwo`. The `…_core` versions
take the smaller core geometry inputs of `R6FinGeomCore` instead (`r6Geom*Remaining_of_core`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.R6Fin

open R7Outer R7Leaves R6Nest R6Rel

variable {k rL rR : ℝ}

/-- **`R6NestCertRemaining` in the mixed case** (supplement p. 476, "Application to a mixed pocket"): on every R.7
configuration, both outer pocket shapes (`twoSeedNestCertInput_of_geom`, `twoSeedNestCertInputInf_of_geom` at the
margins `(πχ(16/k), 0)`). -/
theorem r6NestCertRemaining_of_geom (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hstrip : R7StripOnConfig.{u} k rL rR (π * chiC (16 / k)) 0)
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
  exact ⟨twoSeedNestCertInput_of_geom h411 h51 h47 h47T haux7 h44 hstrip hword hgeom hk4 hL hR le_rfl le_rfl hmix
      hcfg hD hu₀' hV hGm hconf hζG hcfgP,
    twoSeedNestCertInputInf_of_geom h411 h51 h47 h47T haux7 h44 hstrip hword hgeomI hgeomII hk4 hL hR le_rfl le_rfl
      hmix hcfg hD hu₀' hV hGm hconf hζG hcfgI⟩

/-- Outside Aux. 122's bounded sector, either exactly one arm is outer (the mixed case) or both are. -/
theorem mixed_or_twoOuter (hk4 : 4 < k) (hbad : ¬ (rL < k - 6 ∧ rR < k - 6)) :
    ((k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) ∨
      (k / 2 - 4 < rL ∧ k / 2 - 4 < rR) := by
  have h1 : k / 2 - 4 < k - 6 := by linarith
  by_cases hl : k / 2 - 4 < rL <;> by_cases hr : k / 2 - 4 < rR
  · exact Or.inr ⟨hl, hr⟩
  · exact Or.inl (Or.inl ⟨hl, not_lt.1 hr⟩)
  · exact Or.inl (Or.inr ⟨not_lt.1 hl, hr⟩)
  · exact absurd ⟨lt_of_le_of_lt (not_lt.1 hl) h1, lt_of_le_of_lt (not_lt.1 hr) h1⟩ hbad

/-- **The outer phase input from R.5 with continuity, the mixed-case R.6 certificates and the two-outer-arm
certificates** (drop-in for `R6Rel.r7OuterPhaseSideRemaining_of_cont_cert`): outside Aux. 122's bounded sector the
mixed case is `r6NestCertRemaining_of_geom`; the two-outer-arm case is the input `htwo`. -/
theorem r7OuterPhaseSideRemaining_of_cont_geom (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hstrip : R7StripOnConfig.{u} k rL rR (π * chiC (16 / k)) 0)
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
        (fun hmix => r6NestCertRemaining_of_geom h411 h51 h47 h47T haux7 h44 hstrip hword hgeom hgeomI hgeomII hk4
          hrL hrR hmix)
        fun h => htwo h.1 h.2

/-- **`R6NestCertRemaining` in the mixed case from the core geometry inputs** (`r6NestCertRemaining_of_geom` with
`r6GeomMixedRemaining_of_core`, `r6GeomMixedInfRemaining_of_core`, `r6GeomMixedInfInfRemaining_of_core`). -/
theorem r6NestCertRemaining_of_core (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hstrip : R7StripOnConfig.{u} k rL rR (π * chiC (16 / k)) 0)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcore : R6GeomCoreMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreI : R6GeomCoreMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreII : R6GeomCoreMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hL : -2 < rL) (hR : -2 < rR)
    (hmix : (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR)) :
    R6NestCertRemaining.{u} k rL rR :=
  r6NestCertRemaining_of_geom h411 h51 h47 h47T haux7 h44 hstrip hword (r6GeomMixedRemaining_of_core hcore)
    (r6GeomMixedInfRemaining_of_core hcoreI) (r6GeomMixedInfInfRemaining_of_core hcoreII) hk4 hL hR hmix

/-- **The outer phase input from the core geometry inputs** (as `r7OuterPhaseSideRemaining_of_cont_geom`). -/
theorem r7OuterPhaseSideRemaining_of_cont_core (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hstrip : R7StripOnConfig.{u} k rL rR (π * chiC (16 / k)) 0)
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
  r7OuterPhaseSideRemaining_of_cont_geom h411 h51 h47 h47T haux7 h44 hstrip hword (r6GeomMixedRemaining_of_core hcore)
    (r6GeomMixedInfRemaining_of_core hcoreI) (r6GeomMixedInfInfRemaining_of_core hcoreII) hk4 hrL hrR hcont htwo

end InteractingSLE.Sec7.R6Fin
