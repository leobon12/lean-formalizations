/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmXfer
import InteractingSLE.Spec.Supplement.GW2PsmUnion
import InteractingSLE.Spec.Supplement.GW2TjLoc
import InteractingSLE.Spec.Supplement.GW2TfField
import InteractingSLE.Spec.Supplement.GW2RdLocPre
import InteractingSLE.Spec.Supplement.GW2SzLoc

/-!
# GW2's open lines: the stage-start mean of a history is its prefix's mean at the entry's end

Packet PROVE-GW2-STAGEMEAN, R121 round (the transfer of the Claim(k) step, root `0`):

* `measurable_schedUnionS_stgF`: the corrected union is hitting-measurable for the stage filtration;
* `measurable_schedUnionS_det`: it is field-determined (the counterflow record by GW2's retained marks, the explored
  path and the history's success by the field);
* **`ae_mean_eq_cons`**: for a prefix candidate `a'` of the entry's angle whose cap reaches past the entry's end,
  every local-set mean of the prefix's union at the entry's duration `δ` and every local-set mean of the history's
  union at its start agree almost surely on the history's success (`ae_mean_eq_on_event_of_det_H`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Psm

open LocalSets WholeField Restart Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 Supp8 Supp8.GB6 Supp8.GB6LineL Supp8.RelSafe Supp8.Q3Chain GW2Rd

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The corrected union is hitting-measurable for the stage filtration.** -/
theorem measurable_schedUnionS_stgF (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (t : ℝ≥0) : Measurable[stgF c r l a t, hittingSigma] (GW2Sdi.schedUnionS c r l a t) := by
  classical
  have hS : MeasurableSet[stgF c r l a t] {ω | oldSuccess c r l ω} :=
    sigma_le_stgF c r l a t _ (measurableSet_oldSuccess_rootSigma c r l)
  have hrec : Measurable[stgF c r l a t] (gb6Rec c.s c.W c.ζ) :=
    (measurable_rec_physSigma _ _ _).mono (physSigma_le_stgF c r l a t) le_rfl
  have hle : stgF c r l a t ≤ mΩ := (stgFilt _ _ _).le t
  have hhull : Measurable[stgF c r l a t, hittingSigma] (schedHull c r l a (historyTime c r l + t)) :=
    measurable_schedHull_of c r l a ⟨stgF c r l a t, hle⟩ fun s hs =>
      (measurable_schedW_physSigma c r l a hs).mono (physSigma_le_stgF c r l a t) le_rfl
  have hU : Measurable[stgF c r l a t, hittingSigma] (schedUnion c r l a (historyTime c r l) t) :=
    measurable_union_hitting ((measurable_invHull_rdrv c.s).comp hrec) hhull
  exact Measurable.ite hS hU measurable_const

/-- **The corrected union is field-determined.** -/
theorem measurable_schedUnionS_det (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (t : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀) :
    Measurable[mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P, hittingSigma]
      (GW2Sdi.schedUnionS c r l a t) := by
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
  have hU : Measurable[(mΩ ⊓ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P),
      hittingSigma] (schedUnion c r l a (historyTime c r l) t) :=
    measurable_union_hitting ((measurable_invHull_rdrv c.s).comp hrec𝓜) hhull
  exact Measurable.ite hS hU measurable_const

variable [StandardBorelSpace Ω]

/-- **The stage-start mean of a history is its prefix's mean at the entry's end**, on the history's success. -/
theorem ae_mean_eq_cons (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l'))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    {g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg₁ : IsLocalSetMean (GW2Sdi.schedUnionS c r l' a' δ) (centredField c.h u₀) c.P g₁)
    (hg₂ : IsLocalSetMean (GW2Sdi.schedUnionS c r (e :: l') a 0) (centredField c.h u₀) c.P g₂) :
    ∀ᵐ ω ∂c.P, oldSuccess c r (e :: l') ω → g₁ ω = g₂ ω := by
  classical
  have hh := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hloc₁ := isHistoryAvoidanceLocal_stgF h12 h13 c r l' a' hr0 (Gm.timeOrdered_of_pairwise_lt hord') hu₀ δ
  have hloc₂ := isHistoryAvoidanceLocal_stgF h12 h13 c r (e :: l') a hr0 (Gm.timeOrdered_of_pairwise_lt hord) hu₀ 0
  have hm₁ := measurable_schedUnionS_stgF c r l' a' δ
  have hm₂ := measurable_schedUnionS_stgF c r (e :: l') a 0
  have hd₁ := measurable_schedUnionS_det h12 h13 c r l' a' δ hu₀
  have hd₂ := measurable_schedUnionS_det h12 h13 c r (e :: l') a 0 hu₀
  have hle₂ : stgF c r (e :: l') a 0 ≤ mΩ := (stgFilt _ _ _).le 0
  have hSstg : MeasurableSet[stgF c r (e :: l') a 0] {ω | oldSuccess c r (e :: l') ω} :=
    sigma_le_stgF c r (e :: l') a 0 _ (measurableSet_oldSuccess_rootSigma c r (e :: l'))
  have hSdet : MeasurableSet[aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P]
      {ω | oldSuccess c r (e :: l') ω} := by
    have h1 := Gm.measurableSet_oldSuccess_field c r (e :: l')
    rw [← comap_centredField c.h u₀] at h1
    exact le_aeSigma _ _ _ h1
  have hℋ₁ : MeasurableSpace.comap (GW2Sdi.schedUnionS c r (e :: l') a 0) hittingSigma ⊔
      MeasurableSpace.generateFrom {{ω | oldSuccess c r (e :: l') ω}} ≤ stgF c r (e :: l') a 0 :=
    sup_le hm₂.comap_le (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hSstg))
  refine ae_mean_eq_on_event_of_det_H hh (hℋ₁.trans hle₂) (GW2Sdi.measurable_schedUnionS c r l' a' δ)
    (GW2Sdi.measurable_schedUnionS c r (e :: l') a 0)
    (ae_of_all _ fun ω => GW2Sdi.schedUnionS_subset_isOpen c r l' a' δ ω)
    (ae_of_all _ fun ω => GW2Sdi.schedUnionS_subset_isOpen c r (e :: l') a 0 ω)
    (fun V hV => MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_avoid V.isOpen hV, rfl⟩)
    (hd₁.comap_le.trans inf_le_right)
    (fun U G hUH hG hd F hF => hloc₁ U G hUH hG hd F (hm₁.comap_le _ hF))
    (fun V hV => le_sup_left (a := MeasurableSpace.comap (GW2Sdi.schedUnionS c r (e :: l') a 0) hittingSigma) _
      (MeasurableSpace.measurableSet_comap.2 ⟨_, measurableSet_avoid V.isOpen hV, rfl⟩))
    (sup_le (hd₂.comap_le.trans inf_le_right) (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hSdet)))
    (fun U G hUH hG hd F hF => hloc₂ U G hUH hG hd F (hℋ₁ _ hF))
    (le_sup_right (a := MeasurableSpace.comap (GW2Sdi.schedUnionS c r (e :: l') a 0) hittingSigma) _
      (MeasurableSpace.measurableSet_generateFrom rfl)) ?_ ?_ hg₁ hg₂
  · filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hω hS
    have hS' : oldSuccess c r (e :: l') ω := hS
    exact (schedUnionS_cons_eq c r e l' a a' ω hord hord' hS' (hω (e :: l') a hS').1
      (hω l' a' (oldSuccess_of_cons c r e l' ω hS')).1 hθ hcap δ hδ).symm
  · intro ω hω
    have hω' : ¬ oldSuccess c r (e :: l') ω := hω
    unfold GW2Sdi.schedUnionS
    simp only [hω', ↓reduceIte]

end InteractingSLE.Theorem14.GW2Psm
