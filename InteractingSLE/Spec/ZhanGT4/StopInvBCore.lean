/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.G5FromA3
import InteractingSLE.Spec.ZhanGT4.A2ImgEndMain
import InteractingSLE.Spec.ZhanGT4.A1CanonStatement
import InteractingSLE.Spec.ZhanGT4.A1CoreStatement
import InteractingSLE.Spec.ZhanGT4.A2Part3IDExact
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFin
import InteractingSLE.Spec.ZhanGT4.A1PatchStatement
import InteractingSLE.Spec.ZhanGT4.A1G3CalcStatement
import InteractingSLE.Spec.ZhanGT4.A1EightSeedGlue
import InteractingSLE.Spec.ZhanGT4.A1G3RRMain
import InteractingSLE.Spec.ZhanGT4.A1RectMeasG3
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Statement
import InteractingSLE.Spec.ZhanGT4.A1RectLawSplit

/-!
# Theorem 1.5's (G5) leaf from Zhan's A.1 alone

Packet PROVE-T15-G5. Theorem 1.5's tops (`Wire.theorem15Statement_relay_expanded` and its siblings) take

`hG5 : ∀ κ : ℝ, 0 < κ → κ < 4 → ZhanGT4.StoppingInverseBoundaryStatement.{0} (16 / κ)`

as a separate leaf: (G5) for ordinary `SLE_{κ′}`, `κ′ = 16/κ > 4`, at every positive stopping time `T` — the
boundary values of `F_T = g_T⁻¹(W_T + ·)` on the open inverse interval lie in `ℍ` (Astra, *Follow-up proofs*,
§A.4.2–A.4.3,
`source/external/AstraIG1/ig1_followup_proofs.txt` L743–L838; R38).

(G5) has no one-curve proof (PROVE-ZHAN-G5: at a fixed time it is a critical intersection statement of two Bessel zero
sets whose indices sum to `1`), and Theorems 1.2–1.3 do not supply it: they determine and trace single coupled curves,
while (G5) is the simplicity of the frontier of an `SLE_{κ′}` hull, i.e. SLE duality. Its proof is the two-curve route
A.1 → A.2 → A.3 → (G5), every step of which after A.1 is landed:

* A.2 (`A34.FourForceCrosscutG3LifeStatement`, `A35.ThreeForceCrosscutEightStatement`) from A.1's RefUA form and A.2
  part 3 (`A2ImgEnd.fourForceCrosscutG3LifeStatement_of_refUA'`, `…EightStatement_of_refUA'`,
  `A2P3ID.smallInHull…_of_pairContact'`, `A2X.P3.pairContact…Statement`, all proved);
* A.3 and (G5) from A.2 (`stoppingInverseBoundaryStatement_of_A2`).

This file states the result in the exact form of the Theorem 1.5 leaf, from A.1 at each interface of the A.1 chain:

* `stoppingInverseBoundaryStatement_of_g3Core` (`4 < κ < 8`) and `stoppingInverseBoundaryStatement_of_eightCore`
  (`κ ≥ 8`): (G5) at one parameter from the one A.1 core statement that is not vacuous there;
* `stoppingInverseBoundaryStatement_sixteen_div_of_core`: the leaf `hG5` from the two A.1 core statements (R72/R76
  interface, also the target of R83's successor wiring `a1DualCoupling…CoreStatement_of_rectC`);
* `…_of_rect`: from R76's rectangle statements;
* `…_of_rectLaw`: from A.1's two remaining leaves `A1Asm.G3RectLaw`, `A1Asm.EightRectLaw` (the rows and the G3
  measurability are proved: `A1G3RR.g3RectRow`, `A1RectMeas.g3RectMeas`; Eight needs only its law,
  `A1Asm.a1DualCouplingEightSeedMStatement_of_rectLaw`);
* `…_of_dirs`: from the four directional laws of `A1RectLawSplit`.

These are the same A.1 leaves that Theorems 1.2–1.3's tops already carry (`Wire.Relay.cond44`, `Wire.late_partAInputs`),
so the leaf `hG5` of Theorem 1.5 is no longer independent mathematics. Nothing here uses Theorem 1.2, Theorem 1.3,
`Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param` result or Aux. 7 (the chain is R48-safe, so it may
also feed Theorems 1.2–1.3).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.ZhanGT4.StopInvB

open A1Asm

/-- A.1's G3 core is vacuous at `κ ≥ 8`. -/
theorem g3Core_of_eight_le {κ : ℝ} (hκ8 : 8 ≤ κ) : A1Canon.A1DualCouplingG3CoreStatement κ :=
  fun _ h8 => absurd h8 (not_lt.2 hκ8)

/-- A.1's Eight core is vacuous at `κ < 8`. -/
theorem eightCore_of_lt_eight {κ : ℝ} (hκ8 : κ < 8) : A1Canon.A1DualCouplingEightCoreStatement κ :=
  fun h8 => absurd hκ8 (not_lt.2 h8)

/-- **A.2's G3 crosscut from A.1's G3 core**: A.1 Core ⇒ Canon ⇒ RefUA, and A.2 part 3 (proved). -/
theorem fourForceCrosscutG3LifeStatement_of_core {κ : ℝ} (h : A1Canon.A1DualCouplingG3CoreStatement κ) :
    A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  A2ImgEnd.fourForceCrosscutG3LifeStatement_of_refUA' (A1Canon.a1DualCouplingG3RefUAStatement_of_core h)
    (A2P3ID.smallInHullG3Statement_of_pairContact' (A2X.P3.pairContactG3Statement κ))

/-- **A.2's Eight crosscut from A.1's Eight core**. -/
theorem threeForceCrosscutEightStatement_of_core {κ : ℝ} (h : A1Canon.A1DualCouplingEightCoreStatement κ) :
    A35.ThreeForceCrosscutEightStatement.{u} κ :=
  A2ImgEnd.threeForceCrosscutEightStatement_of_refUA' (A1Canon.a1DualCouplingEightRefUAStatement_of_core h)
    (A2P3ID.smallInHullEightStatement_of_pairContact' (A2X.P3.pairContactEightStatement κ))

/-- **(G5) at a stopping time from A.1's two cores** (`κ > 4`): A.1 ⇒ A.2 ⇒ A.3 ⇒ (G5). -/
theorem stoppingInverseBoundaryStatement_of_core {κ : ℝ} (hκ : 4 < κ)
    (hG3 : A1Canon.A1DualCouplingG3CoreStatement κ) (hE : A1Canon.A1DualCouplingEightCoreStatement κ) :
    StoppingInverseBoundaryStatement.{u} κ :=
  stoppingInverseBoundaryStatement_of_A2 hκ (fourForceCrosscutG3LifeStatement_of_core hG3)
    (threeForceCrosscutEightStatement_of_core hE)

/-- **(G5) for `4 < κ < 8` from A.1's G3 core alone.** -/
theorem stoppingInverseBoundaryStatement_of_g3Core {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8)
    (hG3 : A1Canon.A1DualCouplingG3CoreStatement κ) : StoppingInverseBoundaryStatement.{u} κ :=
  stoppingInverseBoundaryStatement_of_core hκ hG3 (eightCore_of_lt_eight hκ8)

/-- **(G5) for `κ ≥ 8` from A.1's Eight core alone.** -/
theorem stoppingInverseBoundaryStatement_of_eightCore {κ : ℝ} (hκ8 : 8 ≤ κ)
    (hE : A1Canon.A1DualCouplingEightCoreStatement κ) : StoppingInverseBoundaryStatement.{u} κ :=
  stoppingInverseBoundaryStatement_of_core (by linarith) (g3Core_of_eight_le hκ8) hE

/-- **Theorem 1.5's leaf `hG5` from A.1's two cores** (R72/R76; the target of R83's successor wiring). -/
theorem stoppingInverseBoundaryStatement_sixteen_div_of_core
    (hG3 : ∀ κ, A1Canon.A1DualCouplingG3CoreStatement κ) (hE : ∀ κ, A1Canon.A1DualCouplingEightCoreStatement κ) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  fun κ hκ hκ4 => stoppingInverseBoundaryStatement_of_core (four_lt_sixteen_div hκ hκ4) (hG3 (16 / κ)) (hE (16 / κ))

/-- **Theorem 1.5's leaf `hG5` from R76's rectangle statements.** -/
theorem stoppingInverseBoundaryStatement_sixteen_div_of_rect
    (hG3 : ∀ κ, A1Core.A1DualCouplingG3RectStatement κ) (hE : ∀ κ, A1Core.A1DualCouplingEightRectStatement κ) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  stoppingInverseBoundaryStatement_sixteen_div_of_core
    (fun κ => A1Core.a1DualCouplingG3CoreStatement_of_rect (hG3 κ))
    (fun κ => A1Core.a1DualCouplingEightCoreStatement_of_rect (hE κ))

/-- A.1's G3 rectangle statement from its remaining leaf `G3RectLaw` (row and measurability proved). -/
theorem g3RectStatement_of_rectLaw {κ : ℝ} (hL : G3RectLaw κ) : A1Core.A1DualCouplingG3RectStatement κ :=
  A1Patch.a1DualCouplingG3RectStatement_of_field (A1G3Calc.a1DualCouplingG3FieldStatement_of_seedG
    (A1G3RR.a1DualCouplingG3SeedGStatement_of_meas_law (A1RectMeas.g3RectMeas κ) hL))

/-- A.1's Eight rectangle statement from its remaining leaf `EightRectLaw`. -/
theorem eightRectStatement_of_rectLaw {κ : ℝ} (hL : EightRectLaw κ) : A1Core.A1DualCouplingEightRectStatement κ :=
  A1EightSeed.a1DualCouplingEightRectStatement_of_seedM (a1DualCouplingEightSeedMStatement_of_rectLaw hL)

/-- **Theorem 1.5's leaf `hG5` from A.1's two remaining rectangle laws.** -/
theorem stoppingInverseBoundaryStatement_sixteen_div_of_rectLaw
    (hG3 : ∀ κ, G3RectLaw κ) (hE : ∀ κ, EightRectLaw κ) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  stoppingInverseBoundaryStatement_sixteen_div_of_rect (fun κ => g3RectStatement_of_rectLaw (hG3 κ))
    (fun κ => eightRectStatement_of_rectLaw (hE κ))

/-- **Theorem 1.5's leaf `hG5` from the four directional rectangle laws** (`A1RectLawSplit`). -/
theorem stoppingInverseBoundaryStatement_sixteen_div_of_dirs
    (hG3S : ∀ κ, A1RectLaw.G3RectLawSnd κ) (hG3F : ∀ κ, A1RectLaw.G3RectLawFst κ)
    (hES : ∀ κ, A1RectLaw.EightRectLawSnd κ) (hEF : ∀ κ, A1RectLaw.EightRectLawFst κ) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → StoppingInverseBoundaryStatement.{u} (16 / κ) :=
  stoppingInverseBoundaryStatement_sixteen_div_of_rectLaw
    (fun κ => A1RectLaw.g3RectLaw_of_dirs (hG3S κ) (hG3F κ))
    (fun κ => A1RectLaw.eightRectLaw_of_dirs (hES κ) (hEF κ))

/-- **(G7), the stopping-time collar, at `16/κ` from A.1's two cores.** -/
theorem stoppingCollarStatement_sixteen_div_of_core
    (hG3 : ∀ κ, A1Canon.A1DualCouplingG3CoreStatement κ) (hE : ∀ κ, A1Canon.A1DualCouplingEightCoreStatement κ)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : StoppingCollarStatement.{u} (16 / κ) :=
  stoppingCollarStatement_of_inverseBoundary (by linarith [four_lt_sixteen_div hκ hκ4])
    (stoppingInverseBoundaryStatement_sixteen_div_of_core hG3 hE κ hκ hκ4)

end InteractingSLE.ZhanGT4.StopInvB
