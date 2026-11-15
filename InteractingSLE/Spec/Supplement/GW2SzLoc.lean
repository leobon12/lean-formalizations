/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SyVer
import InteractingSLE.Spec.Supplement.GW2SgUnion
import InteractingSLE.Spec.Supplement.GW2SdeNeeds
import InteractingSLE.Spec.Supplement.GW2ShrFill
import InteractingSLE.Spec.Supplement.GB6LMeanDet

/-!
# GW2's stage identity: the stage union at the schedule instance is marked local

Packet PROVE-GW2-RELDET, ruling R106. The set-level fields of PROVE-GW2-SDE's `StageInst.LinesLocal`: `harmonic`,
`zbgff`, `sets_le`, `sets_le_ambient`, `sets_meas`, `sets_open`, `loc`.

The stage union is SDE's physical union (`schedUnion`, the set of `StageInst.shape_of_physUnion`'s `hB`): the
counterflow's inverted hull together with the FILLED explored hull `fwdHull schedW (T + t)` (`schedHull`).
Everything except the marked locality of the explored filled hull itself is proved here:
* the centring by the original data's bounded harmonic extension;
* the retained counterflow marks (round 10's `exists_retained_marks_rec_gw2`, at the angle `0`);
* the union of marked local sets (`WalkLaw.isHistoryAvoidanceLocal_union_of_det`);
* the hitting measurability of the hulls (via their records, `measurable_schedHull_of`);
* the openness of the complements;
* the stage filtration inside the marks.

**Named input (new mathematics)** `SchedHullLocalStatement`: at root `0` and at every physical time `q` after the
history, the filled explored hull `fwdHull schedW q` is history-marked local for field-determined marks. The marks
contain the explored path on `[0, q]` and the history's piece records.
* Round 10 proved marked locality of the explored CURVE points (`stageSet`, `exists_union_stageSet_gw2`).
* Single-coupling hulls are local (`Locality11.isLocalSet_hull_of_isFamilyLocal`).
* What is missing is the FILLED hull of a CONCATENATED schedule at a deterministic time.

**`exists_schedLinesLocal_sets`**: the seven fields at the schedule instance with root `0`, from Theorems 1.2–1.3 and
`SchedHullLocalStatement`. Conditional helper with a distinct name.

**Root `0` only.** For a root `x = rootPt r.1 ≠ 0` the physical explored set is `x + (joined trace)`
(`Gm.prefixSet_history_eq`), and generating traces start at `0` by definition. So `fwdHull schedW` is the
TRANSLATE by `−x` of the physical explored hull, which is not a local set of `c.h`, and GB6's version layer
(explored curve from `0`) does not describe the physical relative exploration there. See the round-16 handoff.
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
  Supp8.Q3Chain GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

section Defs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- The filled explored hull of the schedule at the physical time `q`. -/
def schedHull (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  fwdHull (fun s : ℝ => schedW c r l a s.toNNReal ω) (q : ℝ)

/-- **The physical union of a stage** `[T, ·)` at the stage time `t`: the counterflow's inverted hull and the filled
explored hull at `T + t` (SDE's `hB`). -/
def schedUnion (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (T t : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s ∪ schedHull c r l a (T + t) ω

/-- **Named input (new mathematics): the filled explored hull of the schedule is marked local** (root `0`, after
the history): field-determined marks containing the explored path on `[0, q]` and the history's piece records. -/
def SchedHullLocalStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 → ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension c.b c.jumps u₀ →
    ∀ q : ℝ≥0, historyTime c r l ≤ q → ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ},
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedHull c r l a q) (centredField c.h u₀) c.P

end Defs

section Sets

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The explored hull read from the record of the explored path frozen at `q`. -/
theorem schedHull_eq_rdrv (q : ℝ≥0) (ω : Ω) :
    schedHull c r l a q ω =
      fwdHull (rdrv (StagedEntrance.Strip.recOfDriver q fun t => schedW c r l a (min t q) ω)) (q : ℝ) := by
  have hc : Continuous fun t => schedW c r l a (min t q) ω :=
    (continuous_schedW c r l a ω).comp (continuous_id.min continuous_const)
  have h0 : (fun t => schedW c r l a (min t q) ω) 0 = 0 := by
    simp only [zero_min]
    exact schedW_zero c r l a ω
  rw [← rpath_rdrv]
  refine fwdHull_eq_of_agree (continuous_schedW c r l a ω) ((continuous_rdrv _).comp NNReal.continuous_coe)
    fun u hu => ?_
  have hu' : u ≤ q := by
    rw [max_eq_left q.coe_nonneg] at hu
    exact_mod_cast hu
  change schedW c r l a u ω = rdrv _ (u : ℝ)
  rw [Gm.rdrv_recOfDriver hc h0 u]
  simp only [min_eq_left hu']

end Sets

/-- **The explored hull is hitting-measurable for any σ-algebra reading the explored path on `[0, q]`.** -/
theorem measurable_schedHull_of {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {q : ℝ≥0} (M : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hm : ∀ t ≤ q, @Measurable Ω ℝ M.1 _ (schedW c r l a t)) :
    @Measurable Ω (Set ℂ) M.1 hittingSigma (schedHull c r l a q) := by
  have hp : @Measurable Ω (ℝ≥0 → ℝ) M.1 _ fun ω => fun t => schedW c r l a (min t q) ω :=
    (@measurable_pi_iff _ _ _ M.1 _ _).2 fun t => hm _ (min_le_right _ _)
  have hR : @Measurable Ω RecData M.1 _
      fun ω => StagedEntrance.Strip.recOfDriver q fun t => schedW c r l a (min t q) ω :=
    (StagedEntrance.Strip.measurable_recOfDriver q).comp hp
  have e : schedHull c r l a q = fun ω =>
      fwdHull (rdrv (StagedEntrance.Strip.recOfDriver q fun t => schedW c r l a (min t q) ω)) (q : ℝ) :=
    funext fun ω => schedHull_eq_rdrv c r l a q ω
  rw [e]
  exact (measurable_fwdHull_rdrv q).comp hR

/-- A union of hitting-measurable random sets is hitting-measurable. -/
theorem measurable_union_hitting {Ω : Type*} {m : MeasurableSpace Ω} {A K : Ω → Set ℂ}
    (hA : Measurable[m, hittingSigma] A)
    (hK : Measurable[m, hittingSigma] K) : Measurable[m, hittingSigma] fun ω => A ω ∪ K ω := by
  refine @measurable_generateFrom _ _ m _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have hS : MeasurableSet[hittingSigma] {S : Set ℂ | (S ∩ U).Nonempty} :=
    MeasurableSpace.measurableSet_generateFrom ⟨U, hU, hUH, rfl⟩
  have e : (fun ω => A ω ∪ K ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      A ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} ∪ K ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, union_inter_distrib_right, union_nonempty]
  rw [e]
  exact (hA hS).union (hK hS)

section Sets2

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The stage union lies in `ℍ` and has an open complement there, at every sample. -/
theorem schedUnion_subset_isOpen (T t : ℝ≥0) (ω : Ω) :
    schedUnion c r l a T t ω ⊆ H ∧ IsOpen (H \ schedUnion c r l a T t ω) := by
  refine ⟨union_subset (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg) fun z hz => hz.1, ?_⟩
  have h1 : IsOpen (H \ Q3Rel.invHull (rdrv (gb6Rec c.s c.W c.ζ ω)) c.s) := by
    rw [Q3Rel.compl_invHull]
    exact WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
      c.s.coe_nonneg) sdiff_subset
  have h2 : IsOpen (H \ schedHull c r l a (T + t) ω) :=
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((continuous_schedW c r l a ω).comp continuous_real_toNNReal)
      (T + t).coe_nonneg
  rw [schedUnion, ← sdiff_inter_sdiff]
  exact h1.inter h2

theorem measurable_schedUnion (T t : ℝ≥0) : Measurable[mΩ, hittingSigma] (schedUnion c r l a T t) :=
  measurable_union_hitting ((measurable_invHull_rdrv c.s).comp (GW2Sde.measurable_gb6Rec_src c))
    (measurable_schedHull_of c r l a ⟨mΩ, le_rfl⟩ fun t _ => measurable_schedW c r l a t)

/-- **The set-level fields of SDE's `StageInst.LinesLocal` at the schedule instance** (root `0`, stage start after
the history), from Theorems 1.2–1.3 and the named explored-hull locality. -/
theorem exists_schedLinesLocal_sets [StandardBorelSpace Ω] (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hS : SchedHullLocalStatement.{u}) (hr0 : rootPt r.1 = 0) {T : ℝ≥0}
    (hT : historyTime c r l ≤ T) :
    ∃ (u₀ : ℂ → ℝ) (ℋ : ℝ≥0 → MeasurableSpace Ω),
      InnerProductSpace.HarmonicOnNhd u₀ H ∧
      LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P ∧
      (∀ t, stgFilt (physFilt (GW2Sde.measurable_gb6Rec_src c) (measurable_schedW c r l a) c.P) T
        (GW2Sde.measurable_stageEncRec c r l) t ≤ ℋ t) ∧
      (∀ t, ℋ t ≤ mΩ) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (schedUnion c r l a T t)) ∧
      (∀ t ω, schedUnion c r l a T t ω ⊆ H ∧ IsOpen (H \ schedUnion c r l a T t ω)) ∧
      ∀ t, IsHistoryAvoidanceLocal (ℋ t) (schedUnion c r l a T t) (centredField c.h u₀) c.P := by
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
  choose 𝓜 h𝓜W h𝓜rec h𝓜d h𝓜loc using fun t : ℝ≥0 =>
    hS c r l a hr0 u₀ hu₀ (T + t) (hT.trans le_self_add)
  refine ⟨u₀, fun t => ℋr.1 ⊔ (𝓜 t).1, hu₀.1, hz₀, fun t => ?_, fun t => sup_le ℋr.2 (𝓜 t).2,
    measurable_schedUnion c r l a T, schedUnion_subset_isOpen c r l a T, fun t => ?_⟩
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
      (fun U hUH => measurable_schedHull_of c r l a (𝓜 t) (h𝓜W t) (measurableSet_avoid U.isOpen hUH))
      hℋd (h𝓜d t) hloc (h𝓜loc t)
    refine WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ hU
    filter_upwards [c.hζ] with ω hz
    simp only [schedUnion]
    rw [retSet_of_lt (by rw [hz]; exact ENNReal.coe_lt_top)]

end Sets2

end InteractingSLE.Theorem14.GW2Rd
