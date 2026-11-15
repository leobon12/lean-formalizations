/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TqCond
import InteractingSLE.Spec.Supplement.GW2WxMap

/-!
# `condGFF` on ROOTX's corrected root-`x` instances, and `InstInputsX` from the mean and the threshold alone

Packet PROVE-GW2-RELDET (round 28). `GW2TqCond.condGFF_of_mean0` at ROOTX's corrected instances
`GW2Rv.schedInstSX` with RELDET's `u₀` and marks (`schedChoiceLinesX`):

* `exists_abs_fn_le_of_hasShape`, **`exists_bound_schedWordMapX`**, `exists_bound_wmChoiceX`: GEOM2's root-`x` stage
  words have uniformly bounded heights (their heights lie in one finite set);
* **`condGFF_schedInstSX_of`**: `condGFF` of the corrected instance, for every good set, root-`x` version with finite
  stops and choice carrying RELDET's `u₀` and marks, from the word's properties and height bound and STAGEMEAN's mean at
  stage time `0`;
* **`openLinesX_schedChoiceLinesX_of_mean`**: `GW2Rz.OpenLinesX` of the corrected instance from STAGEMEAN's `mean`
  and SB2DRV's `noThreshold` alone (the set-level fields and `condGFF` are RELDET's);
* **`instInputsX_of_linesX_mean`**: `GW2Rv.InstInputsX` for `schedChoiceLinesX` from the base family's word map,
  record event and height bound, STAGEMEAN's `mean` and SB2DRV's `noThreshold`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

/-! ### The heights of GEOM2's root-`x` stage words are bounded -/

section Bound

open Restart Exist.StagedLaw GW2Stl GW2Wm

/-- A finite height set bounds the boundary data of every word of that shape. -/
theorem exists_abs_fn_le_of_hasShape {S : Set ℝ} (hS : S.Finite) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (N : ℕ) (c : BoundaryWord), HasShape S N c → ∀ y : ℝ, |c.fn y| ≤ M := by
  obtain ⟨M, hM⟩ := (hS.image fun x : ℝ => |x|).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun N c hc y => ?_⟩
  have hi : c.index y ≤ c.1 := (Finset.card_filter_le _ _).trans (Finset.card_range _).le
  exact (hM ⟨_, hc.1 _ hi, rfl⟩).trans (le_max_left _ _)

/-- **GEOM2's root-`x` stage words have uniformly bounded heights.** -/
theorem exists_bound_schedWordMapX (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (θa : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : RecData) (z : ℝ), |(schedWordMapX κ c' x s L N hN θa y).fn z| ≤ M := by
  obtain ⟨H₀, hH₀, N₀, hW₀⟩ := exists_hasShape_rootWordX κ c' x s
  obtain ⟨S, hS, N', hN'⟩ := exists_hasShape_stageWord κ hH₀ hW₀ (progAngle L) N
  obtain ⟨M, hM0, hM⟩ := exists_abs_fn_le_of_hasShape (hS.image fun z : ℝ => z + θa * QuantumZipper.chiC κ)
  exact ⟨M, hM0, fun y z => hM N' _ (hasShape_upW (hN' (stageDec x s L N hN y)) _) z⟩

/-- **The words of GEOM2's root-`x` choice have uniformly bounded heights.** -/
theorem exists_bound_wmChoiceX {Ω : Type u} (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (N : ℕ) (hN : L.length = N) (θa : ℝ) (E₀ : Set RecData) (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : RecData) (z : ℝ), |((wmChoiceX κ c' x s L N hN θa E₀ u₀ ℋ).β y).fn z| ≤ M :=
  exists_bound_schedWordMapX κ c' x s L N hN θa

end Bound

/-! ### `condGFF` on the corrected root-`x` instance -/

section Inst

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Sde GW2Sdh GW2Sdi GW2Stl LocalSets WholeField GW2Rz GW2Rv GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **`condGFF` of the corrected root-`x` instance** for every good set, root-`x` version with finite stops and choice
whose `u₀` and marks have RELDET's set-level properties (`exists_schedLinesLocal_setsXB`), from the word's properties
and height bound and STAGEMEAN's mean at stage time `0`. -/
theorem condGFF_schedInstSX_of (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤) {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω}
    (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    (hle : ∀ t, stgFilt (physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P)
      (historyTime c r l) (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t)
    (hamb : ∀ t, ℋ t ≤ mΩ)
    (hmeas : ∀ t, Measurable[mΩ, hittingSigma] (schedUnionX c r l a (historyTime c r l) t))
    (hopen : ∀ t ω, schedUnionX c r l a (historyTime c r l) t ω ⊆ H ∧
      IsOpen (H \ schedUnionX c r l a (historyTime c r l) t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P)
    (ch : SchedChoice Ω) (hu : ch.u₀ = u₀) (hℋ : ch.ℋ = ℋ)
    (hβ : Measurable ch.β ∧ (range fun y => wordType c.κ (ch.β y)).Countable ∧ ∀ y, (ch.β y).IsSorted)
    (hE₀ : MeasurableSet ch.E₀) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ (y : RecData) (z : ℝ), |(ch.β y).fn z| ≤ M)
    (hmean : ∀ (w : WordType) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean ((schedInstSX c r l a GT hA ch).B 0) (centredField c.h (schedInstSX c r l a GT hA ch).u₀) c.P g →
      ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, stageMeanAtX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1) w 0 ψ ω (g ω)) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ),
      Measurable[𝒢.1] ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1)) ∧ 0 ≤ M ∧
      (∀ y ∈ (schedInstSX c r l a GT hA ch).E, ∀ x ∉ ((schedInstSX c r l a GT hA ch).β y).jumps,
        |((schedInstSX c r l a GT hA ch).β y).fn x| ≤ M) ∧
      ∀ᵐ ω₀ ∂c.P, (schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω₀ ∈ (schedInstSX c r l a GT hA ch).E →
        IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) (schedInstSX c r l a GT hA ch).Hr
          ((schedInstSX c r l a GT hA ch).β ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω₀)).fn
          ((schedInstSX c r l a GT hA ch).β ((schedInstSX c r l a GT hA ch).srecX c r l (rootPt r.1) ω₀)).jumps := by
  subst hu hℋ
  set I := schedInstSX c r l a GT hA ch with hI
  have hWm : ∀ t, Measurable (I.W t) := measurable_schedW c r l a
  have hver : IsRelVersionXR (rootPt r.1) c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1
  have hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ I.W I.γ c.α I.R I.V := hA.1.1
  have hρ := hA.1.2.choose_spec
  -- the stage records, read by the marks at stage time `0`
  have hpreP := measurable_stgPreRecX hGT.1 hs hx (measurable_gb6Rec_src c) hWm
    (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGT.2.1 hGT.2.2) hver I.T
  have hP0 : physFilt (measurable_gb6Rec_src c) hWm c.P I.T ≤ ch.ℋ 0 := by
    refine le_trans ?_ (hle 0)
    rw [stgFilt_apply, add_zero]
    exact le_sup_left
  have henc : MeasurableSpace.comap (stageEncRec c r l) inferInstance ≤ ch.ℋ 0 := by
    refine le_trans ?_ (hle 0)
    rw [stgFilt_apply]
    exact le_sup_right
  have hcf : Measurable[ch.ℋ 0] (cfRec c.s c.W c.ζ) :=
    Measurable.of_comap_le ((le_sup_left.trans (physSigma_le_physFilt (measurable_gb6Rec_src c) hWm c.P I.T)).trans
      hP0)
  have hpre : Measurable[ch.ℋ 0] (stgPreRecX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    hpreP.mono hP0 le_rfl
  have hpreΩ : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T I.R) :=
    hpreP.mono ((physFilt (measurable_gb6Rec_src c) hWm c.P).le I.T) le_rfl
  have hrec : Measurable[ch.ℋ 0] (I.srecX c r l (rootPt r.1)) :=
    measurable_augRec (Measurable.of_comap_le henc) hpre
  -- the record event
  have hE : MeasurableSet I.E :=
    (hE₀.inter (measurableSet_succRec c r l)).inter (measurableSet_aliveRecX _ _ c.s hρ.1)
  have hfin : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω ≠ ⊤ :=
    Eventually.of_forall fun ω _ => ne_top_of_le_ne_top (hV ω) (min_le_right _ _)
  have hEgood := StageInst.E_good_of_recordX I hv hρ.2.1 hρ.2.2 inter_subset_right hfin
  -- the stage field
  have hHrm : Measurable I.Hr :=
    measurable_stgField c.hh.1 (isMeasChart_stgChartX (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpreΩ)
  -- the union at the stage start
  have hBm : Measurable[mΩ, hittingSigma] (I.B 0) := by
    change Measurable[mΩ, hittingSigma] (schedUnionSX c r l a 0)
    rw [schedUnionSX_eq_schedUnionX]
    exact hmeas 0
  have hBc : ∀ ω, I.B 0 ω ⊆ H ∧ IsOpen (H \ I.B 0 ω) := fun ω => by
    change schedUnionSX c r l a 0 ω ⊆ H ∧ IsOpen (H \ schedUnionSX c r l a 0 ω)
    rw [schedUnionSX_eq_schedUnionX]
    exact hopen 0 ω
  have hloc0 : IsHistoryAvoidanceLocal (I.ℋ 0) (I.B 0) (centredField c.h I.u₀) c.P := by
    change IsHistoryAvoidanceLocal (ch.ℋ 0) (schedUnionSX c r l a 0) (centredField c.h ch.u₀) c.P
    rw [schedUnionSX_eq_schedUnionX]
    exact hloc 0
  -- the shape of the stage chart on the record event
  have hdom : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      ((I.chartX c (rootPt r.1) ω).dom : Set ℂ) = H \ I.B 0 ω := by
    filter_upwards [hEgood, shape_of_unionX hGT.1 hs hx hv hGT.2.2 (F := I.srecX c r l (rootPt r.1) ⁻¹' I.E)
      (hEgood.mono fun _ h hm => (h hm).1) I.T (B := schedPhysUnionX c r l a) (fun _ _ => rfl) 0]
      with ω hg hsh hm
    obtain ⟨-, hlt⟩ := hg hm
    have hsucc : oldSuccess c r l ω := (augRec_mem_succRec_iff c r l _ ω).1 hm.1.2
    have hB : I.B 0 ω = schedPhysUnionX c r l a 0 ω := by
      change schedUnionSX c r l a 0 ω = schedPhysUnionX c r l a 0 ω
      unfold schedUnionSX
      exact ite_eq_left hsucc
    have h := hsh hm (by rw [add_zero]; exact hlt)
    rw [add_zero] at h
    rw [hB, h, dom_stgChart (isConformal_relChartX _ _ _) (hv.2.1 ω) (hv.2.2.1 ω)]
    rfl
  -- a positive cap on the record event
  have hcap : ∀ᵐ ω ∂c.P, I.srecX c r l (rootPt r.1) ω ∈ I.E →
      I.clockX c (rootPt r.1) 0 ω < I.capX c (rootPt r.1) ω := by
    filter_upwards [hEgood] with ω hg hm
    obtain ⟨-, hlt⟩ := hg hm
    have h0 : I.clockX c (rootPt r.1) 0 ω = 0 := by
      change min (physClockX (rootPt r.1) c.s c.W c.ζ I.W I.GT (I.T + 0) ω) (I.V ω) -
        stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω = 0
      rw [add_zero]
      exact tsub_self _
    rw [h0]
    change 0 < I.V ω - ((stgStartMX (rootPt r.1) c.s c.W c.ζ I.W I.GT I.V I.T ω).toNNReal : ℝ≥0∞)
    rw [ENNReal.coe_toNNReal (ne_top_of_lt hlt)]
    exact tsub_pos_of_lt hlt
  exact condGFF_of_mean0 I (rootPt r.1) hu₀.1 (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀)
    (hamb 0) hBm hBc hloc0 hcf hpre hrec hv.2.1 hv.2.2.1 hE hβ.2.1 (fun y _ => hβ.2.2 y) hM0
    (fun y _ z _ => hM y z) hHrm (fun ω hc => (chartTransport_eq_stgField (ch := schedChartX c r l a GT R V) hc).symm)
    hdom hcap hmean

end Inst

/-! ### The open lines inputs from the mean and the threshold -/

section Family

open GW2Sde GW2Sdh GW2Sdx GW2Rz GW2Rv GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513Schedule Supp8.Q3Stop LocalSets WholeField Exist.StagedLaw

variable (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) (base : SchedChoiceFamily.{u})
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **`condGFF` of the family's corrected root-`x` instances** (time-ordered history, good root; every good set and
root-`x` version with finite stops), from the base family's word map, record event and height bound and STAGEMEAN's
mean at stage time `0`. -/
theorem condGFF_schedChoiceLinesX (hord : TimeOrdered 0 (historyProgram c r l)) (hs : 0 < c.s)
    (hx : 0 ≤ rootPt r.1) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤)
    (hβ : Measurable (base Ω c r l a).β ∧ (range fun y => wordType c.κ ((base Ω c r l a).β y)).Countable ∧
      ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : MeasurableSet (base Ω c r l a).E₀)
    (hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : RecData) (z : ℝ), |((base Ω c r l a).β y).fn z| ≤ M)
    (hmean0 : ∀ (w : WordType) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).B 0)
        (centredField c.h (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).u₀) c.P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)) c r l (rootPt r.1) w 0 ψ
          ω (g ω)) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ),
      Measurable[𝒢.1] ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).srecX c r l
        (rootPt r.1)) ∧ 0 ≤ M ∧
      (∀ y ∈ (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).E,
        ∀ x ∉ ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).β y).jumps,
        |((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).β y).fn x| ≤ M) ∧
      ∀ᵐ ω₀ ∂c.P, (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).srecX c r l (rootPt r.1) ω₀ ∈
          (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).E →
        IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀)
          (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).Hr
          ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).β
            ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).srecX c r l (rootPt r.1) ω₀)).fn
          ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).β
            ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).srecX c r l (rootPt r.1)
              ω₀)).jumps := by
  obtain ⟨hu₀, -, -, hle, hamb, hmeas, hopen, hloc⟩ :=
    (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose_spec.choose_spec
  have hu : (schedChoiceLinesX h12 h13 base Ω c r l a).u₀ =
      (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose := by
    unfold schedChoiceLinesX
    rw [dite_eq_left hord]
  have hℋ : (schedChoiceLinesX h12 h13 base Ω c r l a).ℋ =
      (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose_spec.choose := by
    unfold schedChoiceLinesX
    rw [dite_eq_left hord]
  have hβ' : Measurable (schedChoiceLinesX h12 h13 base Ω c r l a).β ∧
      (range fun y => wordType c.κ ((schedChoiceLinesX h12 h13 base Ω c r l a).β y)).Countable ∧
      ∀ y, ((schedChoiceLinesX h12 h13 base Ω c r l a).β y).IsSorted := by
    rw [schedChoiceLinesX_β]
    exact hβ
  have hE₀' : MeasurableSet (schedChoiceLinesX h12 h13 base Ω c r l a).E₀ := by
    rw [schedChoiceLinesX_E₀]
    exact hE₀
  obtain ⟨M, hM0, hM⟩ := hbd
  have hM' : ∀ (y : RecData) (z : ℝ), |((schedChoiceLinesX h12 h13 base Ω c r l a).β y).fn z| ≤ M := by
    rw [schedChoiceLinesX_β]
    exact hM
  exact condGFF_schedInstSX_of c r l a hs hx hGT hA hV hu₀ hle hamb hmeas hopen hloc _ hu hℋ hβ' hE₀' hM0 hM' hmean0

/-- **The open lines inputs of the family's corrected root-`x` instances from STAGEMEAN's `mean` and SB2DRV's
`noThreshold` alone** (time-ordered history, good root; every good set and root-`x` version with finite stops):
the set-level fields are RELDET's (`exists_schedLinesLocal_setsXB`) and `condGFF` is `condGFF_schedChoiceLinesX`. -/
theorem openLinesX_schedChoiceLinesX_of_mean (hord : TimeOrdered 0 (historyProgram c r l)) (hs : 0 < c.s)
    (hx : 0 ≤ rootPt r.1) {GT : Set Ω}
    (hGT : (∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω) ∧
      MeasurableSet GT ∧ (∀ᵐ ω ∂c.P, ω ∈ GT ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s))
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hV : ∀ ω, V ω ≠ ⊤)
    (hβ : Measurable (base Ω c r l a).β ∧ (range fun y => wordType c.κ ((base Ω c r l a).β y)).Countable ∧
      ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : MeasurableSet (base Ω c r l a).E₀)
    (hbd : ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : RecData) (z : ℝ), |((base Ω c r l a).β y).fn z| ≤ M)
    (hmean : ∀ (w : WordType) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean ((schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).B t)
        (centredField c.h (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)).u₀) c.P g →
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)) c r l (rootPt r.1) w t ψ
          ω (g ω))
    (hno : NoThresholdX (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)) c r l (rootPt r.1)) :
    OpenLinesX (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)) c r l (rootPt r.1)
      (measurable_schedW c r l a) := by
  exact openLinesX_schedChoiceLinesX h12 h13 base c r l a hord GT hA
    ⟨hmean, hno, condGFF_schedChoiceLinesX h12 h13 base c r l a hord hs hx hGT hA hV hβ hE₀ hbd
      fun w g hg ψ => hmean w 0 g hg ψ⟩

variable {h12 h13 base}

/-- **ROOTX's instance inputs from the mean and the threshold alone**: `InstInputsX h13 ver (schedChoiceLinesX …)`
from the base family's word map, record event and height bound (for GEOM2's word map: `wmChoiceX_targets`,
`exists_bound_wmChoiceX`), STAGEMEAN's `mean` and SB2DRV's `noThreshold` on every root-`x` instance. The set-level
fields, `u₀` and `condGFF` are RELDET's. -/
theorem instInputsX_of_linesX_mean {ver : SchedVerXFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
      Measurable (base Ω c r l a).β ∧ (range fun y => wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
        MeasurableSet (base Ω c r l a).E₀)
    (hbd : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
        ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : RecData) (z : ℝ), |((base Ω c r l a).β y).fn z| ≤ M)
    (hmean : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → (h : GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : WordType) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
        IsLocalSetMean ((instX h13 ver (schedChoiceLinesX h12 h13 base) Ω c r l a n h.1).B t)
          (centredField c.h (instX h13 ver (schedChoiceLinesX h12 h13 base) Ω c r l a n h.1).u₀) c.P g →
        ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          stageMeanAtX (instX h13 ver (schedChoiceLinesX h12 h13 base) Ω c r l a n h.1) c r l (rootPt r.1) w t ψ ω
            (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → (h : GoodRoot c r) →
      ∀ a n : ℕ, NoThresholdX (instX h13 ver (schedChoiceLinesX h12 h13 base) Ω c r l a n h.1) c r l (rootPt r.1)) :
    InstInputsX h13 ver (schedChoiceLinesX h12 h13 base) where
  word := fun Ω _ _ c r l hTO h a => by
    rw [schedChoiceLinesX_β]
    exact hword Ω c r l hTO h a
  measurableSet_E₀ := fun Ω _ _ c r l hTO h a => by
    rw [schedChoiceLinesX_E₀]
    exact hE₀ Ω c r l hTO h a
  u₀ := fun Ω _ _ c r l hTO _ a => schedChoiceLinesX_u₀ h12 h13 base c r l a hTO
  openLines := fun Ω _ _ c r l hTO h a n =>
    openLinesX_schedChoiceLinesX_of_mean h12 h13 base c r l a hTO h.2 h.1 (schedGTX_spec h13 c r l a)
      ((ver Ω c r l a).isA h.1 n) ((ver Ω c r l a).fin n) (hword Ω c r l hTO h a) (hE₀ Ω c r l hTO h a)
      (hbd Ω c r l hTO h a) (hmean Ω c r l hTO h a n) (hno Ω c r l hTO h a n)

end Family

end InteractingSLE.Theorem14.GW2Rd
