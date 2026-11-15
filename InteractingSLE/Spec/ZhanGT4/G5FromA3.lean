/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.ZhanGT4.CrosscutA31
import InteractingSLE.Spec.ZhanGT4.A5ClearanceWire
import InteractingSLE.Spec.ZhanGT4.G5InverseBoundaryLocal

/-!
# (G5) at stopping times from the first-swallow crosscut A.3, and Part A at `16/κ` from A.2

Packet PROVE-ZHAN-G5A3. Source: Astra, *Follow-up proofs and dependency audit*, §A.3–A.4
(`source/external/AstraIG1/ig1_followup_proofs.txt` L648–L720, L743–L838, ruling R38).

PROVE-ZHAN-G5 showed that (G5) (`StoppingInverseBoundaryStatement κ′`, `κ′ = 16/κ > 4`) has no one-curve proof and that
the two-curve route A.1 → A.2 → A.3 gives it. The step A.3 ⇒ (G5) is already proved (packets PROVE-ZHAN-GT4-A2
and PROVE-ZHAN-GT4-A3): A.3 gives the open driver sides at every positive stopping time (A.4.2,
`stoppingOpenSidesStatement_of_firstSwallowCrosscut`: a coordinate `u` off the exterior coordinates is reached by a
first-swallow crosscut of the process restarted at `T`, whose open part lies in `ℍ`), A.4.2 at `T` and at the rational
times gives the real tip (A.4.3, `stoppingRealTipStatement_of_openSides`), and the two together are (G5)
(`stoppingInverseBoundaryStatement_of_firstSwallowCrosscut`). This file assembles the consequences the consumers need:

* `ae_forall_noInteriorPreimage_of_firstSwallowCrosscut`: the pointwise form used by the band arguments
  (`NoInteriorPreimage` at every real point, in particular at every swallowed real frontier point);
* `stoppingInverseBoundaryStatement_of_A2`, `stoppingCollarStatement_of_A2`: (G5) and (G7) for every `κ > 4` from A.2's
  two crosscut assertions (`A34.FourForceCrosscutG3LifeStatement` for `4 < κ < 8`, `A35.ThreeForceCrosscutEightStatement`
  for `κ ≥ 8`; A.3 is `A35.firstSwallowCrosscutStatement_of_A2`);
* `stoppingInverseBoundaryStatement_sixteen_div_of_firstSwallowCrosscut`, `…_of_A2`: (G5) at `16/κ`, `0 < κ < 4`;
* `Sec5.partAInputsSixteenDivOfClearance_of_firstSwallowCrosscut`, `Sec5.partAInputsSixteenDivOfClearance_of_A2`: Zhan's
  Part A inputs of Section 5 (clearance form) from A.3, resp. A.2, at `16/κ`; with Aux. lemma 7 at `16/κ` and the
  counterflow restart carrier.

A.2's statements stay named hypotheses (PROVE-ZHAN-GT4-A2X proves them from A.1). Nothing here uses Theorem 1.2,
Theorem 1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result or Aux. lemma 7 as an input (R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u v

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-- `16/κ > 4` for `0 < κ < 4`. -/
theorem four_lt_sixteen_div {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : 4 < 16 / κ := by
  rw [lt_div_iff₀ hκ]
  linarith

/-- **No interior preimage of any real point at a stopping time, from A.3** (`κ > 4`): at every positive finite stopping
time `T` of ordinary `SLE_κ`, almost surely no real coordinate off the exterior coordinates has a real point as the
boundary value of `F_T = g_T⁻¹(W_T + ·)` — in particular no swallowed real frontier point of `ℍ \ K_T` is reached from
the open inverse interval. This is the pointwise property the lifting lemma needs
(`exists_band_cluster_of_noInteriorPreimage`). -/
theorem ae_forall_noInteriorPreimage_of_firstSwallowCrosscut {κ : ℝ} (hκ : 4 < κ)
    (hA3 : FirstSwallowCrosscutStatement.{u} κ) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 (fun ω => (T ω : WithTop ℝ≥0))) (hT0 : ∀ ω, 0 < T ω) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, NoInteriorPreimage (drive κ B ω) (T ω) x := by
  filter_upwards [stoppingInverseBoundaryStatement_of_firstSwallowCrosscut hκ hA3 P 𝓕 B hB T hT hT0] with ω hω
  exact fun x => hω.noInteriorPreimage x

/-- **(G5) at stopping times from A.2** (`κ > 4`): A.2's crosscut assertions give A.3
(`A35.firstSwallowCrosscutStatement_of_A2`), and A.3 gives (G5). -/
theorem stoppingInverseBoundaryStatement_of_A2 {κ : ℝ} (hκ : 4 < κ)
    (hA2 : A34.FourForceCrosscutG3LifeStatement.{0} κ) (hA2' : A35.ThreeForceCrosscutEightStatement.{u} κ) :
    StoppingInverseBoundaryStatement.{u} κ :=
  stoppingInverseBoundaryStatement_of_firstSwallowCrosscut hκ (A35.firstSwallowCrosscutStatement_of_A2 hA2 hA2')

/-- **(G7), the stopping-time collar, from A.2** (`κ > 4`). -/
theorem stoppingCollarStatement_of_A2 {κ : ℝ} (hκ : 4 < κ)
    (hA2 : A34.FourForceCrosscutG3LifeStatement.{0} κ) (hA2' : A35.ThreeForceCrosscutEightStatement.{u} κ) :
    StoppingCollarStatement.{u} κ :=
  stoppingCollarStatement_of_firstSwallowCrosscut hκ (A35.firstSwallowCrosscutStatement_of_A2 hA2 hA2')

/-- **(G5) at `16/κ` from A.3 at `16/κ`**, `0 < κ < 4`. -/
theorem stoppingInverseBoundaryStatement_sixteen_div_of_firstSwallowCrosscut
    (hA3 : ∀ κ : ℝ, 0 < κ → κ < 4 → FirstSwallowCrosscutStatement.{u} (16 / κ)) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) : StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  stoppingInverseBoundaryStatement_of_firstSwallowCrosscut (four_lt_sixteen_div hκ hκ4) (hA3 κ hκ hκ4)

/-- **(G5) at `16/κ` from A.2**, `0 < κ < 4` (the input form of `Wire.theorem13Statement_of_open7_partA`). -/
theorem stoppingInverseBoundaryStatement_sixteen_div_of_A2
    (hA2 : ∀ κ : ℝ, A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, A35.ThreeForceCrosscutEightStatement.{u} κ) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  stoppingInverseBoundaryStatement_of_A2 (four_lt_sixteen_div hκ hκ4) (hA2 _) (hA2' _)

end InteractingSLE.ZhanGT4

namespace InteractingSLE.Sec5

/-- **Zhan's Part A inputs of Section 5 at `16/κ` (clearance form) from A.3 at `16/κ`**: the (G5) half from
`ZhanGT4.stoppingInverseBoundaryStatement_of_firstSwallowCrosscut`, the clearance half from
`ZhanGT4.A5Clear.separatedClearanceStatement`. -/
theorem partAInputsSixteenDivOfClearance_of_firstSwallowCrosscut
    (hA3 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.FirstSwallowCrosscutStatement.{0} (16 / κ)) :
    PartAInputsSixteenDivOfClearance :=
  partAInputsSixteenDivOfClearance_of_inverseBoundary fun _ hκ hκ4 =>
    ZhanGT4.stoppingInverseBoundaryStatement_sixteen_div_of_firstSwallowCrosscut hA3 hκ hκ4

/-- **Zhan's Part A inputs of Section 5 at `16/κ` (clearance form) from A.2's crosscut assertions** (the two-curve
route; the same hypotheses `hA2`, `hA2'` as `Wire.theorem13Statement_of_open7_partA` at universe `0`). -/
theorem partAInputsSixteenDivOfClearance_of_A2
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ) :
    PartAInputsSixteenDivOfClearance :=
  partAInputsSixteenDivOfClearance_of_inverseBoundary fun _ hκ hκ4 =>
    ZhanGT4.stoppingInverseBoundaryStatement_sixteen_div_of_A2 hA2 hA2' hκ hκ4

/-- Aux. lemma 7 at `κ′ = 16/κ` from A.2's crosscut assertions. -/
theorem aux7Statement_sixteen_div_of_A2
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    Sec4.Aux7Statement.{v} (16 / κ) :=
  aux7Statement_sixteen_div_of_partA_of_clearance (partAInputsSixteenDivOfClearance_of_A2 hA2 hA2') hκ hκ4

/-- The counterflow restart carrier from the restart law and A.2's crosscut assertions. -/
theorem counterflowSegmentRestartStatement_of_restartLaw_of_A2
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hR : CrossRestart.CounterflowRestartLawStatement.{u}) : CounterflowSegmentRestartStatement.{u} :=
  counterflowSegmentRestartStatement_of_restartLaw_of_partA_of_clearance
    (partAInputsSixteenDivOfClearance_of_A2 hA2 hA2') hR

end InteractingSLE.Sec5
