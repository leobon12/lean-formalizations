/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ThSets
import InteractingSLE.Spec.Supplement.GW2RvPkg

/-!
# The root-`x` open lines inputs: RELDET's marks and locality of ROOTX's corrected union

Packet PROVE-GW2-RELDET (round 27). ROOTX's `GW2Rv.InstInputsX` asks, at good roots on time-ordered histories, for
`u₀` and the open lines inputs `GW2Rz.OpenLinesX` of the corrected root-`x` instances `GW2Rv.schedInstSX`. RELDET owns
the marks and the locality of the union `GW2Rv.schedUnionSX`; STAGEMEAN owns `mean`, `noThreshold` and `condGFF`.

* **`schedUnionSX_eq_schedUnionX`**: ROOTX's corrected union is RELDET's `schedUnionX` at the history time;
* **`exists_schedLinesLocal_setsXB`**: `exists_schedLinesLocal_setsX` with `u₀` the bounded harmonic extension;
* `OpenLinesMeanX`: STAGEMEAN's three fields of `OpenLinesX`; `openLinesX_of_sets`;
* **`exists_schedChoice_linesX`**: a bounded harmonic `u₀` and marks `ℋ` such that, for every good set, version and
  remaining choice, `OpenLinesX` of the corrected root-`x` instance follows from STAGEMEAN's part alone;
* **`schedChoiceLinesX`**, **`instInputsX_of_linesX`**: any base choice family with RELDET's `u₀` and `ℋ` put in;
  `GW2Rv.InstInputsX` then follows from the word map, the record event and STAGEMEAN's part.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

section Sets

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Supp8 Supp8.GB6 Supp8.GB6LineL Supp8.RelSafe
  Supp8.Q3Chain GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513Schedule

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The set-level fields for the root-`x` union, with `u₀` the bounded harmonic extension** (any root, stage start
after a time-ordered history; `exists_schedLinesLocal_setsX` with the extension property of `u₀` kept). -/
theorem exists_schedLinesLocal_setsXB [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hord : TimeOrdered 0 (historyProgram c r l))
    {T : ℝ≥0} (hT : historyTime c r l ≤ T) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      IsBoundedHarmonicExtension c.b c.jumps u₀ ∧ InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      (∀ t, stgFilt (physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P) T
        (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t) ∧
      (∀ t, ℋ t ≤ mΩ) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (schedUnionX c r l a T t)) ∧
      (∀ t ω, schedUnionX c r l a T t ω ⊆ H ∧ IsOpen (H \ schedUnionX c r l a T t ω)) ∧
      ∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionX c r l a T t) (centredField c.h u₀) c.P := by
  obtain ⟨b', J', h', hb', hTr, hcf⟩ := c.hcf
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.hb
  -- the angle-`0` flow data, its harmonic extension, and the retained marks (as in `exists_union_stageSet_gw2`)
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData c.κ
    (flowLineRhoL c.κ c.b c.jumps 0 0) (flowLineRhoR c.κ c.b c.jumps 0 0) (flowLineXL c.b c.jumps 0)
    (flowLineXR c.b c.jumps 0)
  have huh' : IsBoundedHarmonicExtension (cfData c.κ c.b c.jumps)
      (forceJumpSet (flowLineXL c.b c.jumps 0) (flowLineXR c.b c.jumps 0)) uh := huh
  have heq : EqOn uh u₀ H := fun z hz => by
    have h1 := eqOn_flowLine_harmonicExtension c.hκ c.hb 0 0 hu₀ huh hz
    simpa only [Complex.ofReal_zero, add_zero, zero_mul] using h1
  have hcen : centredField c.h uh = centredField c.h u₀ := by
    funext ω
    simp only [centredField]
    rw [WangWu.smoothDist_congr huh.1.continuousOn hu₀.1.continuousOn heq]
  have hz₀ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P :=
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h uh) c.P := by
    rw [hcen]
    exact hz₀
  have htr : ∀ ω, IsTranslateAddConst 0 (0 * chiC c.κ) (c.h ω) (c.h ω) := fun ω =>
    Sec5.CfGiven.isTranslateAddConst_zero_mul_self (c.h ω) (chiC c.κ)
  obtain ⟨ℋr, hnull, hrec, hAr, hℋd, hloc⟩ :=
    exists_retained_marks_rec_gw2 (θ := 0) h12 h13 c.hκ c.hb c.hh hb' hTr hcf htr huh' huh hh0 c.s
  rw [hcen] at hℋd hloc
  -- the explored marks
  choose 𝓜 h𝓜null h𝓜W h𝓜rec h𝓜d h𝓜Am h𝓜loc using fun t : ℝ≥0 =>
    exists_schedHullX_local h13 c r l a hord u₀ hu₀ (T + t) (hT.trans le_self_add)
  refine ⟨u₀, fun t => ℋr.1 ⊔ (𝓜 t).1, hu₀, hu₀.1, hz₀, fun t => ?_, fun t => sup_le ℋr.2 (𝓜 t).2,
    measurable_schedUnionX c r l a T, schedUnionX_subset_isOpen c r l a T, fun t => ?_⟩
  · -- the stage filtration lies in the marks
    rw [stgFilt_apply, physFilt_apply]
    have hmap : @Measurable Ω (RecData × (Fin ((entryList l).length + 1) → RecData)) (ℋr.1 ⊔ (𝓜 t).1) _
        (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ (schedSpecOf r.1 l) ((entryList l).length + 1)) :=
      (hrec.mono le_sup_left le_rfl).prodMk
        ((@measurable_pi_iff _ _ _ (ℋr.1 ⊔ (𝓜 t).1) _ _).2 fun j => (h𝓜rec t j).mono le_sup_right le_rfl)
    have henc : @Measurable Ω RecData (ℋr.1 ⊔ (𝓜 t).1) _ (stageEncRec c r l) :=
      (stageEnc _).measurable.comp hmap
    refine sup_le (sup_le (sup_le (hrec.comap_le.trans le_sup_left) (iSup₂_le fun s hs =>
      (h𝓜W t s hs).comap_le.trans le_sup_right)) (hnull.trans le_sup_left)) henc.comap_le
  · -- the marked locality of the union
    have hU := WalkLaw.isHistoryAvoidanceLocal_union_of_det (measurable_centredField c.hh.1 u₀)
      (fun U hUH => hAr (measurableSet_avoid U.isOpen hUH))
      (h𝓜Am t)
      hℋd (h𝓜d t) hloc (h𝓜loc t)
    refine WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ hU
    filter_upwards [c.hζ] with ω hz
    simp only [schedUnionX]
    rw [retSet_of_lt (by rw [hz]; exact ENNReal.coe_lt_top)]

/-- **ROOTX's corrected root-`x` union is RELDET's `schedUnionX` at the history time.** -/
theorem schedUnionSX_eq_schedUnionX (t : ℝ≥0) :
    GW2Rv.schedUnionSX c r l a t = schedUnionX c r l a (historyTime c r l) t := by
  funext ω
  unfold GW2Rv.schedUnionSX schedUnionX schedHullX
  by_cases h : oldSuccess c r l ω
  · simp only [h, ↓reduceIte, GW2Rz.schedPhysUnionX, schedHull]
    congr 1
    refine congrArg (fun f : ℂ → ℂ => f '' _) (funext fun z => ?_)
    exact add_comm _ _
  · simp only [h, ↓reduceIte]
    exact (union_eq_right.2 (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg)).symm

end Sets

section Lines

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Sde GW2Sdf GW2Sdh GW2Stl Restart.DomainMarkov Restart.FCDet Sec7.PocketTraversal Supp8.RelSafeS
  GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 LocalSets WholeField GW2Rz GW2Rv Sec5.Prop513Schedule

/-- **STAGEMEAN's part of the root-`x` open lines inputs** (`GW2Rz.OpenLinesX` without the set-level fields). -/
structure OpenLinesMeanX {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (I : StageInst Ω)
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (x₀ : ℝ) : Prop where
  mean : ∀ (w : WordType) (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
    IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
    ∀ᵐ ω ∂c.P, stageMeanAtX I c r l x₀ w t ψ ω (g ω)
  noThreshold : NoThresholdX I c r l x₀
  condGFF : ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ), Measurable[𝒢.1] (I.srecX c r l x₀) ∧ 0 ≤ M ∧
    (∀ y ∈ I.E, ∀ x ∉ (I.β y).jumps, |(I.β y).fn x| ≤ M) ∧
    ∀ᵐ ω₀ ∂c.P, I.srecX c r l x₀ ω₀ ∈ I.E →
      IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) I.Hr (I.β (I.srecX c r l x₀ ω₀)).fn
        (I.β (I.srecX c r l x₀ ω₀)).jumps

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The open lines inputs of a corrected root-`x` instance from the set-level fields** of the union
`schedUnionX` (at the history time) for the instance's `u₀` and marks, and STAGEMEAN's part. -/
theorem openLinesX_of_sets {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω}
    (hle : ∀ t, stgFilt (physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P)
      (historyTime c r l) (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t)
    (hamb : ∀ t, ℋ t ≤ mΩ)
    (hmeas : ∀ t, Measurable[mΩ, hittingSigma] (schedUnionX c r l a (historyTime c r l) t))
    (hopen : ∀ t ω, schedUnionX c r l a (historyTime c r l) t ω ⊆ H ∧
      IsOpen (H \ schedUnionX c r l a (historyTime c r l) t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P)
    (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : SchedChoice Ω) (hu : ch.u₀ = u₀) (hℋ : ch.ℋ = ℋ)
    (hm : OpenLinesMeanX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1)) :
    OpenLinesX (schedInstSX c r l a GT hA ch) c r l (rootPt r.1) (measurable_schedW c r l a) := by
  subst hu hℋ
  refine ⟨hle, hamb, fun t => ?_, fun t ω => ?_, fun t => ?_, hm.mean, hm.noThreshold, hm.condGFF⟩
  · change Measurable[mΩ, hittingSigma] (schedUnionSX c r l a t)
    rw [schedUnionSX_eq_schedUnionX]
    exact hmeas t
  · change schedUnionSX c r l a t ω ⊆ H ∧ IsOpen (H \ schedUnionSX c r l a t ω)
    rw [schedUnionSX_eq_schedUnionX]
    exact hopen t ω
  · change IsHistoryAvoidanceLocal (ch.ℋ t) (schedUnionSX c r l a t) (centredField c.h ch.u₀) c.P
    rw [schedUnionSX_eq_schedUnionX]
    exact hloc t

/-- **RELDET's set-level lines fields at every root** (time-ordered history; Theorems 1.2–1.3): a bounded harmonic
`u₀` and marks `ℋ` such that, for every good set, root-`x` version and remaining choice, the corrected root-`x`
instance's open lines inputs are STAGEMEAN's alone. -/
theorem exists_schedChoice_linesX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hord : TimeOrdered 0 (historyProgram c r l)) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω), IsBoundedHarmonicExtension c.b c.jumps u₀ ∧
      ∀ (GT : Set Ω) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
        (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
        (β : RecData → BoundaryWord) (E₀ : Set RecData) (σa kc : ℝ),
        OpenLinesMeanX (schedInstSX c r l a GT hA ⟨β, E₀, σa, kc, u₀, ℋ⟩) c r l (rootPt r.1) →
        OpenLinesX (schedInstSX c r l a GT hA ⟨β, E₀, σa, kc, u₀, ℋ⟩) c r l (rootPt r.1)
          (measurable_schedW c r l a) := by
  obtain ⟨u₀, ℋ, hu₀, -, -, hle, hamb, hmeas, hopen, hloc⟩ :=
    exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))
  exact ⟨u₀, ℋ, hu₀, fun GT R V hA β E₀ σa kc hm =>
    openLinesX_of_sets c r l a hle hamb hmeas hopen hloc GT hA _ rfl rfl hm⟩

end Lines

/-! ### The choice family with RELDET's `u₀` and marks -/

section Family

open GW2Sde GW2Sdh GW2Sdx GW2Rz GW2Rv GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513Schedule
  Supp8.Q3Stop

open Classical in
/-- **A base choice family with RELDET's `u₀` and marks put in** (on time-ordered histories; the base choice
otherwise): the word, record event and stage constants are the base family's. -/
def schedChoiceLinesX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (base : SchedChoiceFamily.{u}) : SchedChoiceFamily.{u} := fun Ω _ _ c r l a =>
  if hord : TimeOrdered 0 (historyProgram c r l) then
    { base Ω c r l a with
      u₀ := (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose
      ℋ := (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose_spec.choose }
  else base Ω c r l a

variable (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) (base : SchedChoiceFamily.{u})
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

theorem schedChoiceLinesX_β : (schedChoiceLinesX h12 h13 base Ω c r l a).β = (base Ω c r l a).β := by
  unfold schedChoiceLinesX
  split_ifs <;> rfl

theorem schedChoiceLinesX_E₀ : (schedChoiceLinesX h12 h13 base Ω c r l a).E₀ = (base Ω c r l a).E₀ := by
  unfold schedChoiceLinesX
  split_ifs <;> rfl

/-- On a time-ordered history the family's `u₀` is the bounded harmonic extension of the boundary data. -/
theorem schedChoiceLinesX_u₀ (hord : TimeOrdered 0 (historyProgram c r l)) :
    IsBoundedHarmonicExtension c.b c.jumps (schedChoiceLinesX h12 h13 base Ω c r l a).u₀ := by
  unfold schedChoiceLinesX
  rw [dite_eq_left hord]
  exact (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose_spec.choose_spec.1

/-- **The open lines inputs of the family's corrected root-`x` instances from STAGEMEAN's part** (time-ordered
history; every good set and root-`x` version). -/
theorem openLinesX_schedChoiceLinesX (hord : TimeOrdered 0 (historyProgram c r l)) (GT : Set Ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hm : OpenLinesMeanX (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)) c r l (rootPt r.1)) :
    OpenLinesX (schedInstSX c r l a GT hA (schedChoiceLinesX h12 h13 base Ω c r l a)) c r l (rootPt r.1)
      (measurable_schedW c r l a) := by
  obtain ⟨-, -, -, hle, hamb, hmeas, hopen, hloc⟩ :=
    (exists_schedLinesLocal_setsXB c r l a h12 h13 hord (le_refl (historyTime c r l))).choose_spec.choose_spec
  refine openLinesX_of_sets c r l a hle hamb hmeas hopen hloc GT hA _ ?_ ?_ hm
  · unfold schedChoiceLinesX
    rw [dite_eq_left hord]
  · unfold schedChoiceLinesX
    rw [dite_eq_left hord]

variable {h12 h13 base}

/-- **ROOTX's instance inputs for the family with RELDET's `u₀` and marks**: from the base family's word map and
record event, and STAGEMEAN's part of the open lines inputs on every root-`x` instance. -/
theorem instInputsX_of_linesX {ver : SchedVerXFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
      Measurable (base Ω c r l a).β ∧ (range fun y => wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
        MeasurableSet (base Ω c r l a).E₀)
    (hmean : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → (h : GoodRoot c r) →
      ∀ a n : ℕ, OpenLinesMeanX (instX h13 ver (schedChoiceLinesX h12 h13 base) Ω c r l a n h.1) c r l (rootPt r.1)) :
    InstInputsX h13 ver (schedChoiceLinesX h12 h13 base) where
  word := fun Ω _ _ c r l hTO h a => by
    rw [schedChoiceLinesX_β]
    exact hword Ω c r l hTO h a
  measurableSet_E₀ := fun Ω _ _ c r l hTO h a => by
    rw [schedChoiceLinesX_E₀]
    exact hE₀ Ω c r l hTO h a
  u₀ := fun Ω _ _ c r l hTO _ a => schedChoiceLinesX_u₀ h12 h13 base c r l a hTO
  openLines := fun Ω _ _ c r l hTO h a n =>
    openLinesX_schedChoiceLinesX h12 h13 base c r l a hTO _ _ (hmean Ω c r l hTO h a n)

end Family

end InteractingSLE.Theorem14.GW2Rd
