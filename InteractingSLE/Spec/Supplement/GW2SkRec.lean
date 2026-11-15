/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SkSafe
import InteractingSLE.Spec.Supplement.GW2SgChart
import InteractingSLE.Spec.Supplement.GW2SgDec
import InteractingSLE.Spec.Exist.StagedLaw3Path

/-!
# GW2's stage identity: the augmented stage record and its exact decoders

Packet PROVE-GW2-RELDET, ruling R106. The stage step (`GW2Rd.ae_isStopDrvMatch_stage`) needs measurable decoders of the
stage record: the counterflow record `σ`, the relative start `A` and a continuous relative prefix `pre` agreeing with
the version's relative driver `R` up to the start. Reading `A` and `pre` from the physical history alone needs an
identified reader of GB6's relative driver (handoff, round 10). Instead the stage record is AUGMENTED by the record
of the relative prefix:

* `stgPreRec … T R ω = recOf (stgStart T ω) (R · ω, ⊤)`: the relative driver up to the stage start. It is readable at
  the physical time `T` (`measurable_stgPreRec`: GB6's readout at random times below the line clock);
* `pairEnc : RecData × RecData ≃ᵐ RecData` and `augRec x y ω = pairEnc (x ω, y ω)`;
* the decoders `augσ N`, `augA`, `augPre` are projections, with `augPre` the record driver `rdrv`. They are EXACT:
  `augσ` is GB6's counterflow record when `x` decodes to it, `augA` is the stage start, and `augPre` is continuous and
  equals `R` up to the start (`augDec_spec`).

For the stage identity itself (a pathwise statement) the σ-algebra of the record is immaterial. For JOINTDET's
kernel, the augmented record generates `c.sigma r l` up to null sets as soon as the explored path up to `T_n` is
almost surely a function of the past records (the joined canonical schedule; handoff).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.Staged Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.RelSafe

/-! ### The pair encoding -/

/-- A pair of records is uncountable. -/
instance uncountable_recData_pair : Uncountable (RecData × RecData) :=
  (show Function.Injective (fun r : RecData => ((r, r) : RecData × RecData)) from
    fun _ _ h => congrArg Prod.fst h).uncountable

/-- **The Borel encoding of a pair of records.** -/
def pairEnc : (RecData × RecData) ≃ᵐ RecData :=
  PolishSpace.measurableEquivOfNotCountable not_countable not_countable

/-- The augmented record: the stage record with a second record. -/
def augRec {Ω : Type*} (x y : Ω → RecData) (ω : Ω) : RecData := pairEnc (x ω, y ω)

theorem measurable_augRec {Ω : Type*} {m : MeasurableSpace Ω} {x y : Ω → RecData} (hx : Measurable[m] x)
    (hy : Measurable[m] y) : Measurable[m] (augRec x y) :=
  pairEnc.measurable.comp (hx.prodMk hy)

/-- The counterflow record decoder of the augmented stage record. -/
def augσ (N : ℕ) (z : RecData) : RecData := stgRecDec N (pairEnc.symm z).1

/-- The relative start decoder: the time of the prefix record. -/
def augA (z : RecData) : ℝ≥0 := (pairEnc.symm z).2.2.1.toNNReal

/-- The relative prefix decoder: the record driver of the prefix record. -/
def augPre (z : RecData) (u : ℝ≥0) : ℝ := rdrv (pairEnc.symm z).2 u

theorem measurable_augσ (N : ℕ) : Measurable (augσ N) :=
  (measurable_stgRecDec N).comp (measurable_fst.comp pairEnc.symm.measurable)

theorem measurable_augA : Measurable augA :=
  ENNReal.measurable_toNNReal.comp ((measurable_fst.comp measurable_snd).comp
    (measurable_snd.comp pairEnc.symm.measurable))

theorem measurable_augPre (u : ℝ≥0) : Measurable fun z => augPre z u :=
  (measurable_rdrv_apply (u : ℝ)).comp (measurable_snd.comp pairEnc.symm.measurable)

theorem continuous_augPre (z : RecData) : Continuous (augPre z) :=
  (continuous_rdrv _).comp NNReal.continuous_coe

/-! ### The prefix record -/

section Prefix

variable {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {V : Ω → ℝ≥0∞}

/-- **The record of the relative driver up to the stage start.** -/
def stgPreRec (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (V : Ω → ℝ≥0∞) (T : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (ω : Ω) : RecData :=
  recOf (stgStart s W Wα ζα GT V T ω : ℝ≥0∞) (fun u => R u ω, ⊤)

theorem stgPreRec_time (T : ℝ≥0) (R : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (stgPreRec s W Wα ζα GT V T R ω).2.1.toNNReal = stgStart s W Wα ζα GT V T ω := by
  change (min (stgStart s W Wα ζα GT V T ω : ℝ≥0∞) ⊤).toNNReal = _
  rw [min_eq_left le_top, ENNReal.toNNReal_coe]

/-- **The prefix record's driver is the relative driver up to the stage start.** -/
theorem rdrv_stgPreRec {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {ω : Ω} (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0)
    {u : ℝ≥0} (hu : u ≤ stgStart s W Wα ζα GT V T ω) : rdrv (stgPreRec s W Wα ζα GT V T R ω) u = R u ω := by
  have he := isRegularDriver_top hRc hR0
  have hlt : ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) < (fun u => R u ω, (⊤ : ℝ≥0∞)).2 := ENNReal.coe_lt_top
  have hg := Sec7.StripMark.isDrvGood_recOf_of_lt he hlt
  have hfin : min ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, (⊤ : ℝ≥0∞)).2 ≠ ⊤ := by
    rw [min_eq_left le_top]
    exact ENNReal.coe_ne_top
  have hsT : (u : ℝ) ≤ rtime (recOf ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, ⊤)) := by
    rw [rtime_recOf_coe]
    simp only [le_top, min_eq_left, ENNReal.toNNReal_coe, NNReal.coe_le_coe]
    exact hu
  have h := rdrv_recOf_eq he hg hfin hsT
  simpa only [stgPreRec, Real.toNNReal_coe] using h

end Prefix

/-! ### Readability of the prefix record at the stage start -/

section Read

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
  (hGT : ∀ ω ∈ GT, PhysGood s W Wα ζα γ α ω) (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r))
  (hGTm : ∀ t, MeasurableSet[physFilt hrec hWm P t] GT)

include hGT hGTm in
/-- **The prefix record is readable at the physical stage start.** -/
theorem measurable_stgPreRec (hver : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) (T : ℝ≥0) :
    Measurable[physFilt hrec hWm P T] (stgPreRec s W Wα ζα GT V T R) := by
  have hv := hver.1
  have hSM := measurable_stgStartM hGT hrec hWm hGTm hver T
  have hS : Measurable[physFilt hrec hWm P T] (stgStart s W Wα ζα GT V T) :=
    ENNReal.measurable_toNNReal.comp hSM
  have hRa : ∀ (d : ℝ≥0) {B : Set ℝ}, MeasurableSet B → MeasurableSet[physFilt hrec hWm P T]
      ({ω | (d : ℝ≥0∞) ≤ min (physClock s W Wα ζα GT T ω) (V ω)} ∩ R d ⁻¹' B) := fun d _ hB =>
    measurableSet_le_min_inter_drv hGT hrec hWm hGTm hver T le_rfl hB
  have hval : ∀ q : ℚ, Measurable[physFilt hrec hWm P T] fun ω =>
      R (min ((q : ℝ).toNNReal) (stgStart s W Wα ζα GT V T ω)) ω := fun q =>
    Supp8.GB6LineL.measurable_apply_randTime (m := physFilt hrec hWm P T) hv.2.1 (measurable_const.min hS)
      (fun ω => (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans ENNReal.coe_toNNReal_le_self) hRa
  have e : stgPreRec s W Wα ζα GT V T R = fun ω =>
      ((fun q : ℚ => R (min ((q : ℝ).toNNReal) (stgStart s W Wα ζα GT V T ω)) ω),
        ((stgStart s W Wα ζα GT V T ω : ℝ≥0) : ℝ≥0∞), false) := by
    funext ω
    simp only [stgPreRec, recOf, readRec, retOf, min_eq_left (le_top : _ ≤ (⊤ : ℝ≥0∞)), ← ENNReal.coe_min,
      ENNReal.toNNReal_coe, top_le_iff, ENNReal.coe_ne_top, decide_false]
  rw [e]
  have hv' : Measurable[physFilt hrec hWm P T] fun ω => fun q : ℚ =>
      R (min ((q : ℝ).toNNReal) (stgStart s W Wα ζα GT V T ω)) ω :=
    (@measurable_pi_iff Ω ℚ (fun _ => ℝ) (physFilt hrec hWm P T) _ _).2 hval
  exact hv'.prodMk ((measurable_coe_nnreal_ennreal.comp hS).prodMk measurable_const)

end Read

/-! ### The decoders are exact -/

/-- **The decoders of the augmented stage record are exact**: the counterflow record (when the stage record decodes to
it), the relative start, and a continuous prefix agreeing with the relative driver up to the start. -/
theorem augDec_spec {Ω : Type*} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {N : ℕ} {x : Ω → RecData} {rec : Ω → RecData} {ω : Ω}
    (hx : stgRecDec N (x ω) = rec ω) (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) :
    augσ N (augRec x (stgPreRec s W Wα ζα GT V T R) ω) = rec ω ∧
      augA (augRec x (stgPreRec s W Wα ζα GT V T R) ω) = stgStart s W Wα ζα GT V T ω ∧
      ∀ t ≤ augA (augRec x (stgPreRec s W Wα ζα GT V T R) ω),
        augPre (augRec x (stgPreRec s W Wα ζα GT V T R) ω) t = R t ω := by
  have hd : pairEnc.symm (augRec x (stgPreRec s W Wα ζα GT V T R) ω) =
      (x ω, stgPreRec s W Wα ζα GT V T R ω) := pairEnc.symm_apply_apply _
  have hA : augA (augRec x (stgPreRec s W Wα ζα GT V T R) ω) = stgStart s W Wα ζα GT V T ω := by
    rw [augA, hd]
    exact stgPreRec_time T R ω
  refine ⟨by rw [augσ, hd]; exact hx, hA, fun t ht => ?_⟩
  rw [augPre, hd]
  exact rdrv_stgPreRec hRc hR0 (hA ▸ ht)

end InteractingSLE.Theorem14.GW2Rd
