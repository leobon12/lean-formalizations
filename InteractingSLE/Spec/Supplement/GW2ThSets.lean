/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ThHull
import InteractingSLE.Spec.Supplement.GW2TgSets

/-!
# The stage union at a root `x` is marked local (time-ordered histories)

Packet PROVE-GW2-RELDET, the explored half of the stage layer at every root (PROVE-GW2-ROOTX's D8, option (A):
"RELDET, locality"). The physical union at a root `x` is the counterflow's inverted hull together with the explored
hull translated to the root, both in the original field. At `x = 0` it is `GW2TbSets.schedUnionL`.

* `schedUnionX`, `measurable_schedHullX`, `measurable_schedUnionX`, `schedUnionX_subset_isOpen` (every sample);
* **`exists_schedLinesLocal_setsX`**: the seven set-level fields of `GW2TgSets.exists_schedLinesLocal_setsT` for
  `schedUnionX`, at EVERY root, for a time-ordered history, from Theorems 1.2–1.3. Only the sets and the marks are
  stated, so the result does not depend on the chart in which the stage is read.
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

/-- **The physical union of a stage at the root `x`** `[T, ·)` at the stage time `t`. -/
def schedUnionX (T t : ℝ≥0) (ω : Ω) : Set ℂ :=
  Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s ∪ schedHullX c r l a (T + t) ω

theorem measurable_schedHullX (q : ℝ≥0) : Measurable[mΩ, hittingSigma] (schedHullX c r l a q) := by
  classical
  refine @measurable_generateFrom _ _ mΩ _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  set x : ℝ := rootPt r.1 with hx
  have hK := measurable_schedHull_of c r l a ⟨mΩ, le_rfl⟩ (q := q) fun t _ => measurable_schedW c r l a t
  have hS : MeasurableSet[hittingSigma] {S : Set ℂ | (S ∩ (fun z => (x : ℂ) + z) ⁻¹' U).Nonempty} :=
    MeasurableSpace.measurableSet_generateFrom
      ⟨_, isOpen_preimage_add x hU, preimage_add_subset_H x hUH, rfl⟩
  have hne : ∀ K : Set ℂ, ((fun z => (x : ℂ) + z) '' K ∩ U).Nonempty ↔
      (K ∩ (fun z => (x : ℂ) + z) ⁻¹' U).Nonempty := by
    intro K
    rw [← not_disjoint_iff_nonempty_inter, ← not_disjoint_iff_nonempty_inter, disjoint_image_add_iff]
  have e : schedHullX c r l a q ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ({ω | oldSuccess c r l ω} ∩ schedHull c r l a q ⁻¹' {S : Set ℂ | (S ∩ (fun z => (x : ℂ) + z) ⁻¹' U).Nonempty}) ∪
        ({ω | oldSuccess c r l ω}ᶜ ∩ {_ω | (H ∩ U).Nonempty}) := by
    ext ω
    by_cases h : oldSuccess c r l ω
    · simp only [schedHullX, h, ↓reduceIte, mem_preimage, mem_ofPred_eq, mem_union, mem_inter_iff, true_and,
        mem_compl_iff, not_true_eq_false, false_and, or_false]
      exact hne _
    · simp only [schedHullX, h, ↓reduceIte, mem_preimage, mem_ofPred_eq, mem_union, mem_inter_iff, false_and,
        mem_compl_iff, not_false_eq_true, true_and, false_or]
  rw [e]
  exact ((measurableSet_oldSuccess c r l).inter (hK hS)).union ((measurableSet_oldSuccess c r l).compl.inter
    (by by_cases hn : (H ∩ U).Nonempty <;> simp [hn]))

theorem measurable_schedUnionX (T t : ℝ≥0) : Measurable[mΩ, hittingSigma] (schedUnionX c r l a T t) :=
  measurable_union_hitting ((measurable_invHull_rdrv c.s).comp (GW2Sde.measurable_gb6Rec_src c))
    (measurable_schedHullX c r l a (T + t))

theorem schedUnionX_subset_isOpen (T t : ℝ≥0) (ω : Ω) :
    schedUnionX c r l a T t ω ⊆ H ∧ IsOpen (H \ schedUnionX c r l a T t ω) := by
  set x : ℝ := rootPt r.1 with hx
  have h1 : IsOpen (H \ Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s) := by
    rw [Q3Rel.compl_invHull]
    exact WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
      c.s.coe_nonneg) sdiff_subset
  by_cases h : oldSuccess c r l ω
  · have e : schedHullX c r l a (T + t) ω = (fun z => (x : ℂ) + z) '' schedHull c r l a (T + t) ω := by
      simp only [schedHullX, h, ↓reduceIte]
      rfl
    have hsub : schedHullX c r l a (T + t) ω ⊆ H := by
      rw [e, ← image_add_H x]
      exact image_mono fun z hz => hz.1
    have h2 : IsOpen (H \ schedHullX c r l a (T + t) ω) := by
      rw [e, H_diff_image_add]
      exact isOpenMap_add_left (x : ℂ) _ (QuantumZipper.FwdHolo.isOpen_compl_fwdHull
        ((continuous_schedW c r l a ω).comp continuous_real_toNNReal) (T + t).coe_nonneg)
    refine ⟨union_subset (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg) hsub, ?_⟩
    rw [schedUnionX, ← sdiff_inter_sdiff]
    exact h1.inter h2
  · have e : schedUnionX c r l a T t ω = Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s ∪ H := by
      simp only [schedUnionX, schedHullX, h, ↓reduceIte]
    rw [e]
    refine ⟨union_subset (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg) subset_rfl, ?_⟩
    rw [sdiff_eq_empty.2 subset_union_right]
    exact isOpen_empty

/-- **The set-level fields of SDE's `StageInst.LinesLocal` for the corrected union** (any root, stage start after a
time-ordered history), from Theorems 1.2–1.3. -/
theorem exists_schedLinesLocal_setsX [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hord : TimeOrdered 0 (historyProgram c r l))
    {T : ℝ≥0} (hT : historyTime c r l ≤ T) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      InnerProductSpace.HarmonicOnNhd u₀ H ∧
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
  refine ⟨u₀, fun t => ℋr.1 ⊔ (𝓜 t).1, hu₀.1, hz₀, fun t => ?_, fun t => sup_le ℋr.2 (𝓜 t).2,
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

end Sets

end InteractingSLE.Theorem14.GW2Rd
