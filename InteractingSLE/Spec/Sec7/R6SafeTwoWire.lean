/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeTwoInf
import InteractingSLE.Spec.Sec7.R6SafeOuterGeom

/-!
# R.6 for two outer arms, and the outer phase input without `hstrip` and without `htwo`

PROVE-R6-SAFE. PROVE-R6-CERT2's drop-in `R6Fin.r7OuterPhaseSideRemaining_of_cont_core` left the two-outer-arm case as
the opaque input `htwo : k/2 − 4 < r_L → k/2 − 4 < r_R → R6NestCertRemaining k r_L r_R`. Here it is proved
(supplement p. 476, "Application to two outer arms") through the intermediate mixed pocket `V` of `(α_R, β_L)`:

* **`r6NestCertMRemaining_two`**: the two-outer-arm certificates at arbitrary margins `c, c' ≥ 0`, from `V`'s
  zero-phase words (`R7OuterSideMRemaining` at `V`'s weights `(r_L, d)` and margins), `V`'s outer pocket geometry
  (`OuterGeomAeMRemaining`, same parameters; proved in `R6SafeOuterGeom`) and the three named current-face geometry
  cores `R6GeomCoreTwo{,Inf,InfInf}Remaining` (the shared `α_R` collar from `C` to `V`);
* **`r7OuterSideMRemaining_leftExt`**: `V`'s zero-phase words from the mixed-case R.6 chain at `V`'s parameters (`V` is
  always mixed: its left weight is `d`), i.e. from R.5 for `V` (`R6Rel.R7OuterPhaseContMRemaining`), the extremal pocket
  `(β_R, β_L)`'s R.5 word (`PhaseCont.R7PhaseWordRemaining` at `(d, d)`) and the mixed cores at `V`'s parameters;
* **`r7OuterPhaseSideRemaining_of_cont_core_two_safe`**: the drop-in for `R6Fin.r7OuterPhaseSideRemaining_of_cont_core`
  with neither `hstrip` nor `htwo`: the two-outer-arm inputs are the named statements above, required only when both
  arms are outer.

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

/-- **R.6's certificates for two outer arms at arbitrary margins `c, c' ≥ 0`** (supplement p. 476): on every R.7
configuration with two outer arms, both outer pocket shapes (`twoSeedNestCertInput_two`,
`twoSeedNestCertInputInf_two`). -/
theorem r6NestCertMRemaining_two (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (haux7 : Sec4.Aux7Statement.{u} k) {c c' : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hc : 0 ≤ c) (hc' : 0 ≤ c') (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR)
    (hsideV : R7OuterSideMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hgeoV : OuterGeomAeMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hcore : R6GeomCoreTwoRemaining.{u} k rL rR c c') (hcoreI : R6GeomCoreTwoInfRemaining.{u} k rL rR c c')
    (hcoreII : R6GeomCoreTwoInfInfRemaining.{u} k rL rR c c') :
    R6NestCertMRemaining.{u} k rL rR c c' := by
  intro Ω mΩ hSB P hP h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg
    b' J' h' h'' 𝓕 VL VR B hD u₀' hu₀' R L η hV q hq G hGm hPG hconf hζG hcfgP hcfgI
  exact ⟨twoSeedNestCertInput_two h411 h51 haux7 hk4 hL hc hc' hdL hdR hsideV hgeoV
      (r6GeomTwoRemaining_of_core hcore) hcfg hD hu₀' hV hGm hconf hζG hcfgP,
    twoSeedNestCertInputInf_two h411 h51 haux7 hk4 hL hc hc' hdL hdR hsideV hgeoV
      (r6GeomTwoInfRemaining_of_core hcoreI) (r6GeomTwoInfInfRemaining_of_core hcoreII) hcfg hD hu₀' hV hGm hconf
      hζG hcfgI⟩

/-- The intermediate pocket's left margin `c + (θ_L − π/2)χ` is at least `πχ(16/k)` when `c` is and the left arm is
outer. -/
theorem pi_chi_le_leftExt_margin {c : ℝ} (hk4 : 4 < k) (hcπ : π * chiC (16 / k) ≤ c) (hdR : k / 2 - 4 < rR) :
    π * chiC (16 / k) ≤ c + (R7.thetaL k rR - π / 2) * chiC (16 / k) := by
  have hχ := Sec4.chiC_pos (R7.sixteen_div_pos (by linarith)) (R7.sixteen_div_lt_four hk4)
  have hθL : π / 2 < R7.thetaL k rR := (R7.d_lt_rR_iff hk4).1 hdR
  nlinarith

/-- **The intermediate pocket's zero-phase words** (supplement p. 476, "The shared `β_L` collar transfers it to
`V`"): the outer phase input at `V`'s weights `(r_L, d)` and margins `(c + (θ_L − π/2)χ, c')` from the mixed-case
R.6 chain (`r7OuterPhaseSideMRemaining_of_core_safe`; `V` is mixed, so no two-outer input is needed). -/
theorem r7OuterSideMRemaining_leftExt (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u}) {c c' : ℝ}
    (hk4 : 4 < k) (hL : -2 < rL) (hcπ : π * chiC (16 / k) ≤ c) (hc' : 0 ≤ c') (hdR : k / 2 - 4 < rR)
    (hwordV : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (c + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (c' + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcoreV : R6GeomCoreMixedRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hcoreVI : R6GeomCoreMixedInfRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hcoreVII :
      R6GeomCoreMixedInfInfRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c')
    (hcontV :
      R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c') :
    R7OuterSideMRemaining.{u} k rL (k / 2 - 4) (c + (R7.thetaL k rR - π / 2) * chiC (16 / k)) c' :=
  r7OuterSideMRemaining_of_phase hk4 (r7OuterPhaseSideMRemaining_of_core_safe h411 h51 h47 h47T haux7 h44
    (pi_chi_le_leftExt_margin hk4 hcπ hdR) hc' hwordV hcoreV hcoreVI hcoreVII hk4 hL (by linarith) hcontV
    fun _ h => absurd h (lt_irrefl _))

/-- **The named inputs of R.6's two-outer-arm case at the margins `(πχ(16/k), 0)`**: R.5 for the intermediate pocket
`V` (`R6Rel.R7OuterPhaseContMRemaining` at `V`'s parameters), the R.5 word of the extremal pocket `(β_R, β_L)` at
`(d, d)`, the mixed-case cores at `V`'s parameters, and the three cores from `C` to `V`. (`V`'s outer pocket geometry
is proved, `outerGeomAeMRemaining_of_inputs`.) -/
def TwoOuterInputs (k rL rR : ℝ) : Prop :=
  PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4))
      (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k) +
        (r7A k (k / 2 - 4) - r7A k (innerLeft k (k / 2 - 4) (k / 2 - 4) (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))) ∧
    R6GeomCoreMixedRemaining.{u} k rL (k / 2 - 4) (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6GeomCoreMixedInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6GeomCoreMixedInfInfRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6Rel.R7OuterPhaseContMRemaining.{u} k rL (k / 2 - 4)
      (π * chiC (16 / k) + (R7.thetaL k rR - π / 2) * chiC (16 / k)) 0 ∧
    R6GeomCoreTwoRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6GeomCoreTwoInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0 ∧
    R6GeomCoreTwoInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0

/-- **`R6NestCertRemaining` for two outer arms** (the input `htwo` of `R6Fin.r7OuterPhaseSideRemaining_of_cont_core`),
from `TwoOuterInputs`. -/
theorem r6NestCertRemaining_two (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hk4 : 4 < k) (hL : -2 < rL) (hdL : k / 2 - 4 < rL) (hdR : k / 2 - 4 < rR)
    (hin : TwoOuterInputs.{u} k rL rR) : R6Rel.R6NestCertRemaining.{u} k rL rR :=
  r6NestCertMRemaining_two h411 h51 haux7 hk4 hL (nonneg_of_pi_chi_le hk4 le_rfl) le_rfl hdL hdR
    (r7OuterSideMRemaining_leftExt h411 h51 h47 h47T haux7 h44 hk4 hL le_rfl le_rfl hdR hin.1 hin.2.1 hin.2.2.1
      hin.2.2.2.1 hin.2.2.2.2.1)
    (outerGeomAeMRemaining_of_inputs h44 h411 h51 h47 h47T hA hk4 hL (by linarith) (lt_max_of_lt_left hdL)
      (pi_chi_le_leftExt_margin hk4 le_rfl hdR) le_rfl)
    hin.2.2.2.2.2.1 hin.2.2.2.2.2.2.1 hin.2.2.2.2.2.2.2

/-- **The outer phase input without `hstrip` and without `htwo`** (drop-in for
`R6Fin.r7OuterPhaseSideRemaining_of_cont_core`): R.5 with continuity (`hcont`), the mixed-case inner R.5 word
(`hword`) and cores (`hcore`, `hcoreI`, `hcoreII`), and, only when both arms are outer, `TwoOuterInputs`. -/
theorem r7OuterPhaseSideRemaining_of_cont_core_two_safe (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (haux7 : Sec4.Aux7Statement.{u} k) (h44 : AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hword : PhaseCont.R7PhaseWordRemaining.{u} k (innerRight k rL rL (k / 2 - 4)) (innerLeft k rR rR (k / 2 - 4))
      (π * chiC (16 / k) + (r7A k rR - r7A k (innerLeft k rR rR (k / 2 - 4))))
      (0 + (r7B k rL - r7B k (innerRight k rL rL (k / 2 - 4)))))
    (hcore : R6GeomCoreMixedRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreI : R6GeomCoreMixedInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hcoreII : R6GeomCoreMixedInfInfRemaining.{u} k rL rR (π * chiC (16 / k)) 0)
    (hk4 : 4 < k) (hrL : -2 < rL) (hrR : -2 < rR)
    (hcont : OuterPhNext.R7OuterPhaseContRemaining.{u} k rL rR)
    (htwoIn : k / 2 - 4 < rL → k / 2 - 4 < rR → TwoOuterInputs.{u} k rL rR) :
    OuterIn.R7OuterPhaseSideRemaining.{u} k rL rR :=
  r7OuterPhaseSideRemaining_of_cont_core_safe h411 h51 h47 h47T haux7 h44 hword hcore hcoreI hcoreII hk4 hrL hrR
    hcont fun hdL hdR => r6NestCertRemaining_two h411 h51 h47 h47T haux7 h44 hA hk4 hrL hdL hdR (htwoIn hdL hdR)

end InteractingSLE.Sec7.R6Safe
