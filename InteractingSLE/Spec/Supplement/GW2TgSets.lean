/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TbSets
import InteractingSLE.Spec.Supplement.GW2TgLoc

/-!
# Decision D1: the stage union of a time-ordered history is marked local, outright

Packet PROVE-GW2-RELDET, decision D1 of `planning/reviews/DECISIONS-FABLE-1.md`.

**`exists_schedLinesLocal_setsT`**: the successor of `GW2TbSets.exists_schedLinesLocal_setsL` with the guard
`TimeOrdered 0 (historyProgram c r l)`. It gives the seven set-level fields of SDE's `StageInst.LinesLocal` for
`schedUnionL` at root `0` with stage start after the history, from Theorems 1.2–1.3 alone. The explored-hull input is
`GW2TgLoc.schedHullLocalStatementT`, which is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Supp8 Supp8.GB6 Supp8.GB6LineL Supp8.RelSafe
  Supp8.Q3Chain GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513Schedule

section Sets

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The set-level fields of SDE's `StageInst.LinesLocal` for the corrected union** (root `0`, stage start after a
time-ordered history), from Theorems 1.2–1.3 alone. -/
theorem exists_schedLinesLocal_setsT [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hr0 : rootPt r.1 = 0) (hord : TimeOrdered 0 (historyProgram c r l))
    {T : ℝ≥0} (hT : historyTime c r l ≤ T) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      (∀ t, stgFilt (physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P) T
        (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t) ∧
      (∀ t, ℋ t ≤ mΩ) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (schedUnionL c r l a T t)) ∧
      (∀ t ω, schedUnionL c r l a T t ω ⊆ H ∧ IsOpen (H \ schedUnionL c r l a T t ω)) ∧
      ∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnionL c r l a T t) (centredField c.h u₀) c.P := by
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
    schedHullLocalStatementT h13 c r l a hr0 hord u₀ hu₀ (T + t) (hT.trans le_self_add)
  refine ⟨u₀, fun t => ℋr.1 ⊔ (𝓜 t).1, hu₀.1, hz₀, fun t => ?_, fun t => sup_le ℋr.2 (𝓜 t).2,
    measurable_schedUnionL c r l a T, schedUnionL_subset_isOpen c r l a T, fun t => ?_⟩
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
    simp only [schedUnionL]
    rw [retSet_of_lt (by rw [hz]; exact ENNReal.coe_lt_top)]

end Sets

end InteractingSLE.Theorem14.GW2Rd
