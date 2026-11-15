/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdLocPre
import InteractingSLE.Spec.Supplement.GW2RdLocCore
import InteractingSLE.Spec.Supplement.GW2RdLocDrv
import InteractingSLE.Spec.Supplement.GW2FbLocal

/-!
# GW2's union locality, part 4: `GW2RdUnionLocalityStatement` from Theorems 1.2–1.3

Packet PROVE-GW2-RELDET. The locality half of K2's line data for GW2, proved. At every deterministic physical time
`t` the set is

  `B t = retSet ∪ relClosureH (⋃ₙ K_{t,n})`,  `K_{t,n}` a version of the flow hull at `t ∧ σₙ`,

(`σₙ ↑ ζα` an announcing sequence of the flow's lifetime, `WholeField.exists_isAnnouncingSeq_of_adapted`), with marks
`ℋ t = ℋ_ret ⊔ ⨆ₙ 𝓕_{t ∧ σₙ}`:

* marked locality: `isHistoryAvoidanceLocal_union_relClosure_iUnion` (`GW2RdLocCore`) with the retained marks
  (`exists_retained_marks_rec_gw2`) and the stopped flow marks (`GW2Fb.exists_flowHull_marks`); the field is the
  centred ORIGINAL field `h − u_h` (`GW2Fb.centredField_flow_eq`: the angle constant is absorbed);
* `physFilt t ≤ ℋ t`: the record is a retained mark, and the extended flow driver at `r ≤ t` is measurable for the
  stopped flow marks and the null sets (`measurable_regW_iSup_stopping`, `GW2RdLocDrv`);
* before the stop, `t < ζα` (`ae_lt_lifetime_of_lt_stop`), so `t ≤ σₙ` for large `n` and `B t` is the physical union
  `invHull ∪ K^{ext}_t`.

**`gw2RdUnionLocalityStatement_of_thm12_thm13`**; with PROVE-GW2-UNIONMEAN's mean and PROVE-GW2-SAFE's threshold:
**`gw2JointDetC2Statement_of_thm12_thm13_mean_thr`**. R48: Theorems 1.2–1.3 enter as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain Supp8.RelSafe
open GW2JointKernel GW2TipSystem GW2Fb

/-- **The locality half of GW2's line data, from Theorems 1.2–1.3.** -/
theorem gw2RdUnionLocalityStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : GW2RdUnionLocalityStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hTr hcf hadmL hadmR hcomp hfl hα hseed
    s Hc hHcm hHc c' hcJ hcb GT hGT hGTm hGTae R V hver
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hcomp.mono fun ω hω => hω.1
  obtain ⟨X, 𝓕, VL, VR, Bp, htr, hC⟩ := id hfl
  have hE := hC.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  obtain ⟨u₀, hu₀⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)
  have huh' : IsBoundedHarmonicExtension (cfData κ b J) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh :=
    huh
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  have hcen : centredField h uh = centredField X u₀ := (centredField_flow_eq hκ hb htr huh' hu₀).2
  have hYm := hh0.measurable
  -- the retained marks
  obtain ⟨ℋr, hnullr, hrecr, hAr, hℋrd, hlocA⟩ :=
    exists_retained_marks_rec_gw2 h12 h13 hκ hb hh hb' hTr hcf htr huh' hu₀ hh0 s
  -- the flow's field-determined histories and an announcing sequence of its lifetime
  have hdetα := Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ (Theorem15.isOrderedForceWord_flowLine b J 0)
    P 𝓕 Wα VL VR Bp ζα X hC
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := Bp) (κ := κ)
    (xL := flowLineXL b J 0) (xR := flowLineXR b J 0)
    (fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  -- the stopping times `t ∧ σₙ` and the flow hulls there
  have hτ : ∀ (t : ℝ≥0) (n : ℕ), IsStoppingTime (drivingFiltration P hX)
      (fun ω => min (t : WithTop ℝ≥0) (σ n ω)) := fun t n => (isStoppingTime_const _ t).min (hσ.1 n)
  have hτζ : ∀ (t : ℝ≥0) (n : ℕ), ∀ᵐ ω ∂P, ((min (t : WithTop ℝ≥0) (σ n ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζα ω :=
    fun t n => (hσ.2.2.1 n).mono fun ω hω => lt_of_le_of_lt (min_le_right _ _) hω
  have hτt : ∀ (t : ℝ≥0) (n : ℕ) (ω : Ω), min (t : WithTop ℝ≥0) (σ n ω) ≠ ⊤ := fun t n ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have huntop : ∀ (t : ℝ≥0) (n : ℕ) (ω : Ω), (min (t : WithTop ℝ≥0) (σ n ω)).untopD 0 = min t (σ n ω) :=
    fun t n ω => by rw [← WithTop.coe_min, WithTop.untopD_coe]
  have hKex : ∀ (t : ℝ≥0) (n : ℕ), ∃ K : Ω → Set ℂ, Measurable[(hτ t n).measurableSpace, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((min (t : WithTop ℝ≥0) (σ n ω)).untopD 0 : ℝ≥0)) ∧
      (∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω)) ∧
      (hτ t n).measurableSpace ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal (hτ t n).measurableSpace K (centredField X u₀) P :=
    fun t n => exists_flowHull_marks hκ hC hdetα hu₀ hh0 hX (hτ t n) (hτζ t n) (hτt t n)
  choose K hKτ hKe hKc hτd hlocK using hKex
  have hKe' : ∀ t n, ∀ᵐ ω ∂P, K t n ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) (min t (σ n ω) : ℝ≥0) :=
    fun t n => (hKe t n).mono fun ω hω => by rw [hω, huntop]
  -- the measurability inputs of `GW2RdLocDrv`
  have hnull' : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[drivingFiltration P hX 0] N :=
    fun N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 0
  have hWad : ∀ (u : ℝ≥0) (A : Set ℝ), MeasurableSet A →
      MeasurableSet[drivingFiltration P hX u] {ω | (u : ℝ≥0∞) < ζα ω ∧ Wα u ω ∈ A} := by
    intro u A hA
    refine Ito.le_usualAugmentation _ _ u _ (MeasurableSpace.measurableSet_generateFrom
      ⟨u, le_rfl, A ×ˢ univ, hA.prod MeasurableSet.univ, ?_⟩)
    ext ω
    simp only [mem_ofPred_eq, mem_prod, mem_univ, and_true]
  -- the union and its marks
  refine ⟨uh, fun t => ℋr.1 ⊔ ⨆ n, (hτ t n).measurableSpace,
    fun t ω => retSet s W ζ ω ∪ relClosureH (⋃ n, K t n ω), huh.1, by rw [hcen]; exact hh0, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- the physical σ-algebra is in the marks
    intro t
    show physSigma (gb6Rec s W ζ) (regW s Wα ζα) t ⊔ Ito.nullSets P ≤ ℋr.1 ⊔ ⨆ n, (hτ t n).measurableSpace
    refine sup_le (sup_le (hrecr.comap_le.trans le_sup_left) (iSup₂_le fun r hr => ?_))
      (hnullr.trans le_sup_left)
    have hm := measurable_regW_iSup_stopping hκ hfl hnull' hWad hσ (hτ t) s hr
    exact hm.comap_le.trans (sup_le le_sup_right (hnullr.trans le_sup_left))
  · exact fun t => sup_le ℋr.2 (iSup_le fun n => (hτ t n).measurableSpace_le)
  · -- hitting-measurability
    intro t
    refine @measurable_generateFrom _ _ mΩ _ _ ?_
    rintro _ ⟨U, hU, hUH, rfl⟩
    have e : (fun ω => retSet s W ζ ω ∪ relClosureH (⋃ n, K t n ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
        ({ω | Disjoint (retSet s W ζ ω) U} ∩ ⋂ n, {ω | Disjoint (K t n ω) U})ᶜ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_inter_iff, mem_iInter,
        ← not_disjoint_iff_nonempty_inter,
        disjoint_union_left, disjoint_relClosureH_iff hU hUH, disjoint_iUnion_left]
    rw [e]
    exact ((ℋr.2 _ (hAr (measurableSet_avoid hU hUH))).inter (MeasurableSet.iInter fun n =>
      (hτ t n).measurableSpace_le _ (hKτ t n (measurableSet_avoid hU hUH)))).compl
  · -- relatively closed
    intro t ω
    refine ⟨union_subset (retSet_subset_H s W ζ ω) (relClosureH_subset _), ?_⟩
    have e : H \ (retSet s W ζ ω ∪ relClosureH (⋃ n, K t n ω)) =
        (H \ retSet s W ζ ω) ∩ (H \ relClosureH (⋃ n, K t n ω)) := by
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [e]
    exact (isOpen_H_diff_retSet s W ζ ω).inter (LocalSets.isOpen_H_diff_relClosureH _)
  · -- marked locality
    intro t
    rw [hcen]
    refine isHistoryAvoidanceLocal_union_relClosure_iUnion hYm hAr hℋrd hlocA (fun n m hnm => ?_) (hKτ t)
      (hτd t) (hlocK t) ?_
    · exact (hτ t n).measurableSpace_mono (hτ t m) fun ω =>
        min_le_min le_rfl (WithTop.coe_le_coe.2 (hσ.2.1 ω hnm))
    · filter_upwards [ae_all_iff.2 (hKe' t)] with ω hω n m hnm
      show K t n ω ⊆ K t m ω
      rw [hω n, hω m]
      exact WangWu.fwdHull_mono (by exact_mod_cast min_le_min le_rfl (hσ.2.1 ω hnm))
  · -- before the stop, the union is the physical union
    intro t
    filter_upwards [ae_lt_lifetime_of_lt_stop hfl hGT hver t, ae_all_iff.2 (hKe' t), ae_all_iff.2 (hKc t),
      hσ.2.2.2, hζ, ae_driver_zero_continuousOn hfl] with ω hP1 hKω hKcω hreach hz hd hωG hlt
    have ht := hP1 hωG hlt
    obtain ⟨n₀, hn₀⟩ := hreach t ht
    have hs : (s : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
    have hK₀ : K t n₀ ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
      rw [hKω n₀, min_eq_left hn₀]
    have hU : (⋃ n, K t n ω) = fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
      refine Subset.antisymm (iUnion_subset fun n => ?_) (hK₀ ▸ subset_iUnion (fun n => K t n ω) n₀)
      rw [hKω n]
      exact WangWu.fwdHull_mono (by exact_mod_cast min_le_left t (σ n ω))
    have hcl : relClosureH (⋃ n, K t n ω) = fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
      rw [hU, ← hK₀]
      exact relClosureH_eq_self (hKcω n₀).1 (hKcω n₀).2
    -- the flow hull is the extended flow's hull before the lifetime
    obtain ⟨t₄, htt₄, ht₄ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    have hext : fwdHull (fun r : ℝ => Wα r.toNNReal ω) t = fwdHull (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t := by
      refine fwdHull_eq_of_eqOn t.coe_nonneg (show (t : ℝ) < t₄ by exact_mod_cast htt₄) fun r hr => ?_
      have hr' : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < ζα ω := by
        refine lt_of_le_of_lt ?_ ht₄ζ
        exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2
      exact (regW_eq_of_lt s hd.1 hd.2 hr').symm
    show retSet s W ζ ω ∪ relClosureH (⋃ n, K t n ω) =
      Supp8.Q3Rel.invHull (rdrv (gb6Rec s W ζ ω)) s ∪ fwdHull (fun r : ℝ => regW s Wα ζα r.toNNReal ω) t
    rw [hcl, hext, retSet_of_lt hs]

/-- **GW2's root determination from Theorems 1.2–1.3, the union mean statement and the threshold clause.** -/
theorem gw2JointDetC2Statement_of_thm12_thm13_mean_thr (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hM : GW2RdUnionMeanStatement.{u}) (hT : GW2RdThrStatement.{u}) : GW2JointKernel.GW2JointDetC2Statement.{u} :=
  gw2JointDetC2Statement_of_thm12_thm13_locality_mean_thr h12p₀ h13₀ h13
    (gw2RdUnionLocalityStatement_of_thm12_thm13 h12 h13) hM hT

end InteractingSLE.Theorem14.GW2Rd
