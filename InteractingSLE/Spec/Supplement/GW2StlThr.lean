/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeNeeds
import InteractingSLE.Spec.Supplement.GW2SfSafeThreshold

/-!
# GW2's stage lines, part 1: the threshold clause at a stage

Packet PROVE-GW2-STAGEMEAN, stage-lines round (targets of PROVE-GW2-SDE's `GW2Sde.StageInst.LinesLocal`). The
threshold clause `LinesLocal.thr` (and RELDET's `hthr` of `GW2Rd.hasRelSafe_of_local_rec`) is a statement on the
canonical space under the conditioned joint law of the record and the relative variable. PROVE-GW2-SAFE transferred a
physical no-threshold statement to it for GB6's record at a deterministic time (`GW2Sf.ae_canonStp_le_thr_gw2`); the
transfer itself does not depend on the record, the word map, the field or the relative driver:

* **`ae_canonStp_le_thr_of_bound`**: for ANY measurable record `rec`, word map `β`, record event `E`, field `Hr`,
  relative driver `R` (continuous from `0`) and stop `V`, a per-sample bound `V ≤ thr` of the typed word along `R`
  gives the canonical clause;
* **`ae_canonStp_le_thr_of_noThreshold`**: the same from the physical form of the exclusion (the flow-line word of
  `β(rec)`, its marks carried by the right images of `R`, no continuation threshold before `V`), which is the form
  `GW2Stm.ae_no_threshold_gw2_random` delivers;
* `augA_stgRec`, `measurable_stgStart_of_pre`, `measurable_stgR`, `measurable_stgV`: the stage start, driver and cap
  of a GB6 stage are measurable once the prefix record is;
* **`StageInst.lines_thr`**: `LinesLocal.thr` of a stage instance from the physical no-threshold statement of the
  stage word along the stage driver before the stage cap.

Measure-theoretic bookkeeping; conditional helper with distinct names, it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Stl

open Restart Exist.StagedLaw Sec7.PocketTraversal Restart.FCDet Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop GW2Rd
  GW2Sde GW2TipSystem GW2TipSystem.RootC24

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
  {rec : Ω → RecData} {β : RecData → BoundaryWord} {E : Set RecData} {Hr : Ω → DistOn upperHalfPlaneOpens}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **The threshold clause from a per-sample bound**, for any record, word map, field, driver and stop. -/
theorem ae_canonStp_le_thr_of_bound (hrec : Measurable rec) (hβ : Measurable β) (hE : MeasurableSet E)
    (hHr : Measurable Hr) (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) (hVm : Measurable V) (w : WordType)
    (hbound : ∀ᵐ ω ∂P, rec ω ∈ E → wordType κ (β (rec ω)) = w →
      V ω ≤ thr (typedRhoL w) (typedRhoR w) R (fun ω => typedXL κ w (β (rec ω)))
        (fun ω => typedXR κ w (β (rec ω))) ω) :
    ∀ᵐ y ∂((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL κ w (β y.1))
        (fun y => typedXR κ w (β y.1)) y := by
  have hΦ := hrec.prodMk (measurable_relVar hHr hRm hVm)
  have hxL : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXL κ w (β y.1) :=
    (((measurable_typedXL κ w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  have hxR : Measurable[canonFilt 0] fun y : Supp8.Q3Stop.CanonSpace => typedXR κ w (β y.1) :=
    (((measurable_typedXR κ w).comp hβ).comp measurable_fst_canonRec).mono (canonRec_le_canonFilt 0) le_rfl
  refine ae_cond_of_ae_comp hΦ (measurableSet_typeEvent hβ hE)
    (measurableSet_le measurable_canonStp (measurable_thr continuous_canonDrv stronglyAdapted_canonDrv hxL hxR)) ?_
  filter_upwards [hbound] with ω hb hm
  have hd : ∀ t, canonDrv t (rec ω, relVar Hr R V ω) = R t ω := fun t => relDrv_relVar (hRc ω) (hR0 ω) t
  rw [thr_congr (W := R) (xL := fun ω => typedXL κ w (β (rec ω))) (xR := fun ω => typedXR κ w (β (rec ω))) hd rfl
    rfl]
  exact hb hm.1 hm.2

/-- **The threshold clause from the physical exclusion**: if, almost surely on the record event, the flow-line word
of `β(rec)` with its marks carried by the right images of `R` meets no continuation threshold before `V`, the
canonical clause holds for every word type. -/
theorem ae_canonStp_le_thr_of_noThreshold (hrec : Measurable rec) (hβ : Measurable β) (hE : MeasurableSet E)
    (hHr : Measurable Hr) (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) (hVm : Measurable V)
    (hno : ∀ᵐ ω ∂P, rec ω ∈ E → ∀ u : ℝ≥0, (u : ℝ≥0∞) < V ω →
      ¬ ForceWord.ThresholdCondition
        (flowLineRhoL κ (β (rec ω)).fn (β (rec ω)).jumps 0 0) (flowLineRhoR κ (β (rec ω)).fn (β (rec ω)).jumps 0 0)
        (R u ω)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -R v.toNNReal ω)
          (-flowLineXL (β (rec ω)).fn (β (rec ω)).jumps 0 i) u)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => R v.toNNReal ω)
          (flowLineXR (β (rec ω)).fn (β (rec ω)).jumps 0 j) u))
    (w : WordType) :
    ∀ᵐ y ∂((P.map fun ω => (rec ω, relVar Hr R V ω))[|typeEvent κ w β E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL κ w (β y.1))
        (fun y => typedXR κ w (β y.1)) y := by
  refine ae_canonStp_le_thr_of_bound hrec hβ hE hHr hRm hRc hR0 hVm w ?_
  filter_upwards [hno] with ω hn hEω htype
  refine (GW2Sf.le_thr_iff_no_threshold hRc _ _ V ω).2 fun u hu => ?_
  have hnt := GW2Sf.not_threshold_images_of_isFlowType (isFlowType_typed htype)
    (D := fun v : ℝ => R v.toNNReal ω) (u := u) (by simpa only [Real.toNNReal_coe] using hn hEω u hu)
  convert hnt using 1
  simp only [Real.toNNReal_coe]
  rfl

end Generic

/-! ### The stage start, driver and cap -/

section Stage

variable {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω}
  {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {T : ℝ≥0}

omit [MeasurableSpace Ω] in
/-- The relative start decoder reads the stage start from the augmented record. -/
theorem augA_stgRec (x : Ω → RecData) (ω : Ω) :
    augA (stgRec s W Wα ζα GT R V T x ω) = stgStart s W Wα ζα GT V T ω := by
  change ((pairEnc.symm (pairEnc (x ω, stgPreRec s W Wα ζα GT V T R ω))).2.2.1).toNNReal = _
  rw [pairEnc.symm_apply_apply]
  exact stgPreRec_time T R ω

/-- The stage start is measurable once the prefix record is. -/
theorem measurable_stgStart_of_pre (hpre : Measurable (stgPreRec s W Wα ζα GT V T R)) :
    Measurable (stgStart s W Wα ζα GT V T) := by
  have e : stgStart s W Wα ζα GT V T = fun ω => (stgPreRec s W Wα ζα GT V T R ω).2.1.toNNReal :=
    funext fun ω => (stgPreRec_time T R ω).symm
  rw [e]
  exact ENNReal.measurable_toNNReal.comp (measurable_fst.comp (measurable_snd.comp hpre))

/-- The stage driver is measurable at every time. -/
theorem measurable_stgR (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hpre : Measurable (stgPreRec s W Wα ζα GT V T R)) (t : ℝ≥0) :
    Measurable (stgR s W Wα ζα GT R V T t) :=
  measurable_stgDrv hRm hRc (measurable_stgStart_of_pre hpre) t

/-- The stage cap is measurable. -/
theorem measurable_stgV (hVm : Measurable V) (hpre : Measurable (stgPreRec s W Wα ζα GT V T R)) :
    Measurable (stgV s W Wα ζα GT V T) :=
  hVm.sub (measurable_coe_nnreal_ennreal.comp (measurable_stgStart_of_pre hpre))

end Stage

/-! ### The threshold target of a stage instance -/

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **`LinesLocal.thr` of a stage instance** from the physical exclusion: almost surely on the record event, the
flow-line word of the stage word, carried along the stage driver, meets no continuation threshold before the stage
cap. -/
theorem StageInst.lines_thr (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (hβ : Measurable I.β)
    (hE : MeasurableSet I.E) (hHr : Measurable I.Hr)
    (hno : ∀ᵐ ω ∂c.P, I.srec c r l ω ∈ I.E → ∀ u : ℝ≥0, (u : ℝ≥0∞) < I.cap c ω →
      ¬ ForceWord.ThresholdCondition
        (flowLineRhoL c.κ (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 0)
        (flowLineRhoR c.κ (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 0)
        (I.drv c u ω)
        (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -I.drv c v.toNNReal ω)
          (-flowLineXL (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 i) u)
        (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => I.drv c v.toNNReal ω)
          (flowLineXR (I.β (I.srec c r l ω)).fn (I.β (I.srec c r l ω)).jumps 0 j) u))
    (w : WordType) :
    ∀ᵐ y ∂((c.P.map fun ω => (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))[|typeEvent c.κ w I.β I.E]),
      canonStp y ≤ thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL c.κ w (I.β y.1))
        (fun y => typedXR c.κ w (I.β y.1)) y :=
  ae_canonStp_le_thr_of_noThreshold (measurable_augRec (measurable_stageEncRec c r l) hpre) hβ hE hHr
    (measurable_stgR hv.1 hv.2.1 hpre) (fun ω => continuous_stgDrv (hv.2.1 ω) _) (fun _ => stgDrv_zero _ _)
    (measurable_stgV hv.2.2.2.2.1 hpre) hno w

end InteractingSLE.Theorem14.GW2Stl
