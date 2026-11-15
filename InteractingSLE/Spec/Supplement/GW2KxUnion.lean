/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxSupp
import InteractingSLE.Spec.Supplement.GW2PsmXferC
import InteractingSLE.Spec.Supplement.GW2ThSets

/-!
# The stage-start mean of a history is its prefix's mean at the entry's end, at a root `x`

Packet PROVE-GW2-GEOM2, round 14 (D49). The transfer of the Claim(k) step (STAGEMEAN's `GW2PsmUnion`,
`GW2PsmXferC`) for the root-`x` union `schedUnionX` (RELDET's; ROOTX's `schedUnionSX` is it,
`GW2Rd.schedUnionSX_eq_schedUnionX`):

* `schedUnionX_cons_eq`, `schedUnionX_cons_subset`: the history's union at its start is the prefix's union at the
  entry's end on the history's success (the explored hulls agree, `GW2Psm.futureJoined_cons_eq`; the translation by
  `x` is common);
* `measurable_schedHullX_of`: the translated hull is hitting-measurable for any σ-algebra carrying the success and
  the explored hull; `measurable_schedUnionX_stgF`, `measurable_schedUnionX_det`;
* **`ae_mean_eq_consX`** (`GW2Psm.ae_mean_eq_on_event_of_det_H`), `exists_mean_schedUnionX`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open LocalSets WholeField Restart Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 Supp8 Supp8.GB6 Supp8.GB6LineL Supp8.RelSafe Supp8.Q3Chain GW2Rd GW2Psm

section Union

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The root-`x` union of a history at its start is the prefix's union at the entry's end** (on the history's
success). -/
theorem schedUnionX_cons_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ) (ω : Ω)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hold : oldSuccess c r (e :: l') ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r (e :: l') a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r (e :: l') a) ω ⟨j, hj⟩)))
    (hgood' : ∀ (j : ℕ) (hj : j < (futureProgram c r l' a').length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l' a') ω ⟨j, hj⟩)))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l')) :
    schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω =
      schedUnionX c r l' a' (historyTime c r l') δ ω := by
  have hold' := oldSuccess_of_cons c r e l' ω hold
  set T : ℝ≥0 := historyTime c r (e :: l') with hT
  have hc1 : Continuous fun s : ℝ => GW2Rd.schedW c r (e :: l') a s.toNNReal ω :=
    (GW2Rd.continuous_schedW c r (e :: l') a ω).comp continuous_real_toNNReal
  have hc2 : Continuous fun s : ℝ => GW2Rd.schedW c r l' a' s.toNNReal ω :=
    (GW2Rd.continuous_schedW c r l' a' ω).comp continuous_real_toNNReal
  have hK : fwdHull (fun s : ℝ => GW2Rd.schedW c r (e :: l') a s.toNNReal ω) (T : ℝ) =
      fwdHull (fun s : ℝ => GW2Rd.schedW c r l' a' s.toNNReal ω) (T : ℝ) := by
    refine LocalExt.fwdHull_congr_of_continuousOn (t' := (T : ℝ) + 1) hc1.continuousOn hc2.continuousOn
      T.coe_nonneg (by linarith) fun s hs => ?_
    have hsT : s.toNNReal ≤ T := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hs.2
    show GW2Rd.schedW c r (e :: l') a s.toNNReal ω = GW2Rd.schedW c r l' a' s.toNNReal ω
    rw [congrFun (GW2Rd.schedW_of_oldSuccess c r (e :: l') a hold) s.toNNReal,
      congrFun (GW2Rd.schedW_of_oldSuccess c r l' a' hold') s.toNNReal]
    exact futureJoined_cons_eq c r e l' a a' ω hord hord' hold hold' hgood hgood' hθ hcap _ hsT
  simp only [schedUnionX, schedHullX, hold, hold', ↓reduceIte, schedHull]
  rw [add_zero, hδ, hK]

/-- **The prefix's root-`x` union at the entry's end lies in the history's union at its start.** -/
theorem schedUnionX_cons_subset (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ) (δ : ℝ≥0) (ω : Ω)
    (heq : oldSuccess c r (e :: l') ω → schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω =
      schedUnionX c r l' a' (historyTime c r l') δ ω) :
    schedUnionX c r l' a' (historyTime c r l') δ ω ⊆ schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω := by
  by_cases hs : oldSuccess c r (e :: l') ω
  · rw [heq hs]
  · have h1 : schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω = H := by
      simp only [schedUnionX, schedHullX, hs, ↓reduceIte]
      exact union_eq_right.2 (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg)
    rw [h1]
    exact (schedUnionX_subset_isOpen c r l' a' (historyTime c r l') δ ω).1

/-- **The translated hull is hitting-measurable** for any σ-algebra carrying the success and the explored hull. -/
theorem measurable_schedHullX_of (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (q : ℝ≥0) (M : {m : MeasurableSpace Ω // m ≤ mΩ}) (hS : MeasurableSet[M.1] {ω | oldSuccess c r l ω})
    (hK : Measurable[M.1, hittingSigma] (schedHull c r l a q)) :
    Measurable[M.1, hittingSigma] (schedHullX c r l a q) := by
  classical
  refine @measurable_generateFrom _ _ M.1 _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  set x : ℝ := rootPt r.1 with hx
  have hS' : MeasurableSet[hittingSigma] {S : Set ℂ | (S ∩ (fun z => (x : ℂ) + z) ⁻¹' U).Nonempty} :=
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
  refine (hS.inter (hK hS')).union (hS.compl.inter ?_)
  by_cases hn : (H ∩ U).Nonempty
  · simp only [hn, ofPred_true]
    exact @MeasurableSet.univ _ M.1
  · simp only [hn, ofPred_false]
    exact @MeasurableSet.empty _ M.1

end Union

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The root-`x` union is hitting-measurable for the stage filtration.** -/
theorem measurable_schedUnionX_stgF (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (t : ℝ≥0) : Measurable[stgF c r l a t, hittingSigma] (schedUnionX c r l a (historyTime c r l) t) := by
  classical
  have hS : MeasurableSet[stgF c r l a t] {ω | oldSuccess c r l ω} :=
    sigma_le_stgF c r l a t _ (measurableSet_oldSuccess_rootSigma c r l)
  have hrec : Measurable[stgF c r l a t] (gb6Rec c.s c.W c.ζ) :=
    (measurable_rec_physSigma _ _ _).mono (physSigma_le_stgF c r l a t) le_rfl
  have hle : stgF c r l a t ≤ mΩ := (stgFilt _ _ _).le t
  have hhull : Measurable[stgF c r l a t, hittingSigma] (schedHull c r l a (historyTime c r l + t)) :=
    measurable_schedHull_of c r l a ⟨stgF c r l a t, hle⟩ fun s hs =>
      (measurable_schedW_physSigma c r l a hs).mono (physSigma_le_stgF c r l a t) le_rfl
  exact measurable_union_hitting ((measurable_invHull_rdrv c.s).comp hrec)
    (measurable_schedHullX_of c r l a _ ⟨stgF c r l a t, hle⟩ hS hhull)

/-- **The root-`x` union is field-determined.** -/
theorem measurable_schedUnionX_det (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) :
    Measurable[mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P, hittingSigma]
      (schedUnionX c r l a (historyTime c r l) t) := by
  classical
  -- the counterflow record, by GW2's retained marks
  obtain ⟨b', J', h', hb', hTr, hcf⟩ := c.hcf
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
  obtain ⟨ℋr, -, hrec, -, hℋd, -⟩ :=
    exists_retained_marks_rec_gw2 (θ := 0) h12 h13 c.hκ c.hb c.hh hb' hTr hcf htr huh' huh hh0 c.s
  rw [hcen] at hℋd
  have hrec𝓜 : Measurable[(mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P)]
      (gb6Rec c.s c.W c.ζ) :=
    Measurable.of_comap_le (le_inf (GW2Sde.measurable_gb6Rec_src c).comap_le (hrec.comap_le.trans hℋd))
  -- the explored path and the success, by the field
  have hW𝓜 : ∀ s, Measurable[(mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P)]
      (schedW c r l a s) := fun s =>
    Measurable.of_comap_le (le_inf (measurable_schedW c r l a s).comap_le
      (Gm.comap_le_aeSigma_centred_of_field c u₀ (Gm.measurable_schedW_field c r l a s)))
  have hS : MeasurableSet[(mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P)]
      {ω | oldSuccess c r l ω} := by
    refine MeasurableSpace.measurableSet_inf.2 ⟨measurableSet_oldSuccess c r l, ?_⟩
    have h1 := Gm.measurableSet_oldSuccess_field c r l
    rw [← comap_centredField c.h u₀] at h1
    exact le_aeSigma _ _ _ h1
  have hhull : Measurable[(mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P),
      hittingSigma] (schedHull c r l a (historyTime c r l + t)) :=
    measurable_schedHull_of c r l a
      ⟨(mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P), inf_le_left⟩
      fun s _ => hW𝓜 s
  exact measurable_union_hitting ((measurable_invHull_rdrv c.s).comp hrec𝓜)
    (measurable_schedHullX_of c r l a _
      ⟨mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P, inf_le_left⟩ hS hhull)

variable [StandardBorelSpace Ω]

/-- **The stage-start mean of a history is its prefix's mean at the entry's end**, on the history's success. -/
theorem ae_mean_eq_consX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l'))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    {g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg₁ : IsLocalSetMean (schedUnionX c r l' a' (historyTime c r l') δ) (centredField c.h u₀) c.P g₁)
    (hg₂ : IsLocalSetMean (schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0) (centredField c.h u₀) c.P g₂) :
    ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω → g₁ ω = g₂ ω := by
  classical
  have hh := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hloc₁ := isHistoryAvoidanceLocal_stgFX h12 h13 c r l' a' (Gm.timeOrdered_of_pairwise_lt hord') hu₀ δ
  have hloc₂ := isHistoryAvoidanceLocal_stgFX h12 h13 c r (e :: l') a (Gm.timeOrdered_of_pairwise_lt hord) hu₀ 0
  have hm₁ := measurable_schedUnionX_stgF c r l' a' δ
  have hm₂ := measurable_schedUnionX_stgF c r (e :: l') a 0
  have hd₁ := measurable_schedUnionX_det h12 h13 c r l' a' δ hu₀
  have hd₂ := measurable_schedUnionX_det h12 h13 c r (e :: l') a 0 hu₀
  have hle₂ : stgF c r (e :: l') a 0 ≤ mΩ := (stgFilt _ _ _).le 0
  have hSstg : MeasurableSet[stgF c r (e :: l') a 0] {ω | oldSuccess c r (e :: l') ω} :=
    sigma_le_stgF c r (e :: l') a 0 _ (measurableSet_oldSuccess_rootSigma c r (e :: l'))
  have hSdet : MeasurableSet[aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P]
      {ω | oldSuccess c r (e :: l') ω} := by
    have h1 := Gm.measurableSet_oldSuccess_field c r (e :: l')
    rw [← comap_centredField c.h u₀] at h1
    exact le_aeSigma _ _ _ h1
  have hℋ₁ : MeasurableSpace.comap (schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0) hittingSigma ⊔
      MeasurableSpace.generateFrom {{ω | oldSuccess c r (e :: l') ω}} ≤ stgF c r (e :: l') a 0 :=
    sup_le hm₂.comap_le (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hSstg))
  refine ae_mean_eq_on_event_of_det_H hh (hℋ₁.trans hle₂) (measurable_schedUnionX c r l' a' (historyTime c r l') δ)
    (measurable_schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0)
    (ae_of_all _ fun ω => schedUnionX_subset_isOpen c r l' a' (historyTime c r l') δ ω)
    (ae_of_all _ fun ω => schedUnionX_subset_isOpen c r (e :: l') a (historyTime c r (e :: l')) 0 ω)
    (fun V hV => MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_avoid V.isOpen hV, rfl⟩)
    (hd₁.comap_le.trans inf_le_right)
    (fun U G hUH hG hd F hF => hloc₁ U G hUH hG hd F (hm₁.comap_le _ hF))
    (fun V hV => le_sup_left (a := MeasurableSpace.comap (schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0)
      hittingSigma) _
      (MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_avoid V.isOpen hV, rfl⟩))
    (sup_le (hd₂.comap_le.trans inf_le_right) (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hSdet)))
    (fun U G hUH hG hd F hF => hloc₂ U G hUH hG hd F (hℋ₁ _ hF))
    (le_sup_right (a := MeasurableSpace.comap (schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0)
      hittingSigma) _
      (MeasurableSpace.measurableSet_generateFrom rfl)) ?_ ?_ hg₁ hg₂
  · filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hω hS
    have hS' : oldSuccess c r (e :: l') ω := hS
    exact (schedUnionX_cons_eq c r e l' a a' ω hord hord' hS' (hω (e :: l') a hS').1
      (hω l' a' (oldSuccess_of_cons c r e l' ω hS')).1 hθ hcap δ hδ).symm
  · intro ω hω
    have hω' : ¬ oldSuccess c r (e :: l') ω := hω
    simp only [schedUnionX, schedHullX, hω', ↓reduceIte]
    exact union_eq_right.2 (GW2Shr.invHull_subset_H (continuous_rdrv _) c.s.coe_nonneg)


/-- **A local-set mean of the root-`x` union exists.** -/
theorem exists_mean_schedUnionX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) (t : ℝ≥0) :
    ∃ g, IsLocalSetMean (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P g := by
  have hh := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hloc := isHistoryAvoidanceLocal_stgFX h12 h13 c r l a (Gm.timeOrdered_of_pairwise_lt hord) hu₀ t
  have h : IsGermConditionalLaw (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀) c.P :=
    ((isLocalSet_tfae hh (measurable_schedUnionX c r l a (historyTime c r l) t)
      (ae_of_all _ fun ω => schedUnionX_subset_isOpen c r l a (historyTime c r l) t ω)).out 1 3).1
      hloc.isAvoidanceLocal
  exact h

end InteractingSLE.Theorem14.GW2Kx
