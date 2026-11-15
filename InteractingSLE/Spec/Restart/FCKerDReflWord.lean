/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerDReflChart
import InteractingSLE.Spec.Sec5.CfDownWord

/-!
# Words, local-set means and Lemma 7.8's mean identification under the reflection

Packet PROVE-T15-FCKER4. The retained word of the reflected configuration is the sorted mirror word
`sreflWord c` (positions `−p (n − 1 − i)`, heights `−q (n − k)`): it is sorted, has the mirrored boundary function
`y ↦ −c.fn(−y)` and jumps `−J` (it agrees with `Sec7.StripWall.reflWord c` in both), and its flow-line type at angle
`−θ` is the type of `c` at angle `θ` with the sides exchanged (`isFlowType_sreflWord`, `isFlowType_of_sreflWord`,
`mem_typeSet_sreflWord_iff`, `typeXL_sreflWord`, `typeXR_sreflWord`). Its mean is the reflected mean
(`eqOn_mean_sreflWord`, `integral_mean_sreflWord`).

Lemma 7.8's mean identification transfers to the reflected configuration (`isBoxMeanIdentification_refl`): germ
σ-algebras are reflection invariant (`germSigma_reflect`), local-set means reflect (`IsLocalSetMean.reflect`), the
first-contact union of the reflected pair is the reflected union (`fcUnion_refl`, through `meetsQ_swap_reflH`), the
centred field reflects (`smoothDist_reflect`, `centredField_reflect`), and the chart transport reflects
(`chartTransport_reflPair`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerD

open LP (reflectC)
open Sec7.FlowReflect (reflField reflTest reflData reflJumps)
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

section Word

/-- **The sorted mirror image of a boundary word** under `y ↦ −y`: positions `−p (n − 1 − i)` (increasing again),
heights `−q (n − k)`. -/
def sreflWord (c : BoundaryWord) : BoundaryWord := (c.1, fun i => -c.2.1 (c.1 - 1 - i), fun k => -c.2.2 (c.1 - k))

theorem measurable_sreflWord : Measurable sreflWord := by
  refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
  · refine measurable_pi_iff.2 fun i => ?_
    exact measurable_from_prod_countable_right fun n =>
      ((measurable_pi_apply (n - 1 - i)).comp measurable_fst).neg
  · refine measurable_pi_iff.2 fun k => ?_
    exact measurable_from_prod_countable_right fun n =>
      ((measurable_pi_apply (n - k)).comp measurable_snd).neg

theorem sreflWord_isSorted {c : BoundaryWord} (hc : c.IsSorted) : (sreflWord c).IsSorted := by
  intro i j hij hj
  change -c.2.1 (c.1 - 1 - i) ≤ -c.2.1 (c.1 - 1 - j)
  have hj' : j < c.1 := hj
  exact neg_le_neg (hc _ _ (by omega) (by omega))

theorem index_sreflWord (c : BoundaryWord) (y : ℝ) :
    (sreflWord c).index y = (Sec7.StripWall.reflWord c).index y := by
  unfold BoundaryWord.index
  change ((Finset.range c.1).filter fun i => -c.2.1 (c.1 - 1 - i) < y).card =
    ((Finset.range c.1).filter fun i => -c.2.1 i < y).card
  refine Finset.card_bij (fun i _ => c.1 - 1 - i) (fun i hi => ?_) (fun i hi j hj he => ?_) (fun j hj => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    omega
  · simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨c.1 - 1 - j, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show c.1 - 1 - (c.1 - 1 - j) = j by omega]
    exact hj.2

theorem fn_sreflWord (c : BoundaryWord) : (sreflWord c).fn = (Sec7.StripWall.reflWord c).fn := by
  funext y
  change -c.2.2 (c.1 - (sreflWord c).index y) = -c.2.2 (c.1 - (Sec7.StripWall.reflWord c).index y)
  rw [index_sreflWord]

theorem jumps_sreflWord (c : BoundaryWord) : (sreflWord c).jumps = reflJumps c.jumps := by
  rw [← Sec7.StripWall.jumps_reflWord]
  ext y
  rw [BoundaryWord.mem_jumps, BoundaryWord.mem_jumps]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨c.1 - 1 - i, by change c.1 - 1 - i < c.1; change i < c.1 at hi; omega, he⟩
  · rintro ⟨i, hi, he⟩
    refine ⟨c.1 - 1 - i, by change c.1 - 1 - i < c.1; change i < c.1 at hi; omega, ?_⟩
    change -c.2.1 (c.1 - 1 - (c.1 - 1 - i)) = y
    change i < c.1 at hi
    rw [show c.1 - 1 - (c.1 - 1 - i) = i by omega]
    exact he

theorem fn_sreflWord_of_notMem {c : BoundaryWord} {y : ℝ} (hy : y ∉ reflJumps c.jumps) :
    (sreflWord c).fn y = reflData c.fn y := by
  rw [fn_sreflWord]
  exact Sec7.StripWall.fn_reflWord fun h => hy (Sec7.FlowReflect.mem_reflJumps.2 h)

theorem reflJumps_reflJumps' (J : Finset ℝ) : reflJumps (reflJumps J) = J := by
  ext y
  rw [Sec7.FlowReflect.mem_reflJumps, Sec7.FlowReflect.mem_reflJumps, neg_neg]

variable {nL nR : ℕ} {κ θ : ℝ} {c : BoundaryWord} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- **The flow-line type of the sorted mirror word**: sides exchanged, positions negated, angle negated. -/
theorem isFlowType_sreflWord (h : FCDet.IsFlowType κ θ c xL xR ρL ρR) :
    FCDet.IsFlowType κ (-θ) (sreflWord c) (fun i => -xR i) (fun j => -xL j) ρR ρL := by
  have h1 := Sec5.CfDown.FlowTypeAt.reflect c.isPiecewiseConstantBoundaryData
    (Sec5.CfDown.isFlowType_iff_flowTypeAt.1 h)
  rw [neg_zero] at h1
  have hfn : ∀ y ∉ reflJumps c.jumps, (sreflWord c).fn y = reflData c.fn y := fun y hy =>
    fn_sreflWord_of_notMem hy
  rw [Sec5.CfDown.isFlowType_iff_flowTypeAt, jumps_sreflWord,
    Sec5.CfDown.flowTypeAt_congr (jumpSet_congr hfn) (leftLim_congr hfn) (rightLim_congr hfn)]
  exact h1

/-- The converse of `isFlowType_sreflWord`. -/
theorem isFlowType_of_sreflWord {xL : Fin nR → ℝ} {xR : Fin nL → ℝ} {ρL : Fin nR → ℝ} {ρR : Fin nL → ℝ}
    (h : FCDet.IsFlowType κ (-θ) (sreflWord c) xL xR ρL ρR) :
    FCDet.IsFlowType κ θ c (fun i => -xR i) (fun j => -xL j) ρR ρL := by
  have h1 := Sec5.CfDown.FlowTypeAt.reflect (sreflWord c).isPiecewiseConstantBoundaryData
    (Sec5.CfDown.isFlowType_iff_flowTypeAt.1 h)
  rw [neg_neg, neg_zero, jumps_sreflWord, reflJumps_reflJumps'] at h1
  have hfn : ∀ y ∉ c.jumps, reflData (sreflWord c).fn y = c.fn y := by
    intro y hy
    have hy' : -y ∉ reflJumps c.jumps := by rwa [Sec7.FlowReflect.mem_reflJumps, neg_neg]
    simp only [reflData]
    rw [fn_sreflWord_of_notMem hy']
    simp only [reflData, neg_neg]
  rw [Sec5.CfDown.isFlowType_iff_flowTypeAt]
  exact (Sec5.CfDown.flowTypeAt_congr (jumpSet_congr hfn) (leftLim_congr hfn) (rightLim_congr hfn)).1 h1

/-- **A word of a flow-line type belongs to the type set, with the type's positions.** -/
theorem mem_typeSet_of_isFlowType (h : FCDet.IsFlowType κ θ c xL xR ρL ρR) :
    c ∈ FCDet.typeSet κ θ nL nR ρL ρR ∧ FCDet.typeXL κ θ nL nR ρL ρR c = xL ∧
      FCDet.typeXR κ θ nL nR ρL ρR c = xR := by
  classical
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := h
  subst eL eR
  simp only [Fin.cast_eq_self] at hxL hxR hρL hρR
  have hmem : c ∈ FCDet.typeSet κ θ (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0) ρL ρR := by
    refine ⟨rfl, rfl, fun i => ?_, fun j => ?_⟩
    · simp only [flowPad, i.2, ↓reduceDIte, ← hρL]
    · simp only [flowPad, j.2, ↓reduceDIte, ← hρR]
  refine ⟨hmem, ?_, ?_⟩
  · funext i
    simp only [FCDet.typeXL, hmem, ↓reduceIte, flowPad, i.2, ↓reduceDIte, ← hxL]
  · funext j
    simp only [FCDet.typeXR, hmem, ↓reduceIte, flowPad, j.2, ↓reduceDIte, ← hxR]

/-- **Type membership of the sorted mirror word.** -/
theorem mem_typeSet_sreflWord_iff :
    sreflWord c ∈ FCDet.typeSet κ (-θ) nR nL ρR ρL ↔ c ∈ FCDet.typeSet κ θ nL nR ρL ρR := by
  constructor
  · intro h
    have h2 := isFlowType_of_sreflWord (FCDet.isFlowType_of_mem_typeSet h)
    exact (mem_typeSet_of_isFlowType h2).1
  · intro h
    exact (mem_typeSet_of_isFlowType (isFlowType_sreflWord (FCDet.isFlowType_of_mem_typeSet h))).1

/-- **The type positions of the sorted mirror word** are the negated positions of the other side. -/
theorem typeXL_sreflWord : FCDet.typeXL κ (-θ) nR nL ρR ρL (sreflWord c) =
    fun i => -FCDet.typeXR κ θ nL nR ρL ρR c i := by
  classical
  by_cases h : c ∈ FCDet.typeSet κ θ nL nR ρL ρR
  · exact (mem_typeSet_of_isFlowType (isFlowType_sreflWord (FCDet.isFlowType_of_mem_typeSet h))).2.1
  · have h' : sreflWord c ∉ FCDet.typeSet κ (-θ) nR nL ρR ρL := fun h' => h (mem_typeSet_sreflWord_iff.1 h')
    funext i
    simp only [FCDet.typeXL, FCDet.typeXR, h, h', ↓reduceIte, Pi.zero_apply, neg_zero]

theorem typeXR_sreflWord : FCDet.typeXR κ (-θ) nR nL ρR ρL (sreflWord c) =
    fun j => -FCDet.typeXL κ θ nL nR ρL ρR c j := by
  classical
  by_cases h : c ∈ FCDet.typeSet κ θ nL nR ρL ρR
  · exact (mem_typeSet_of_isFlowType (isFlowType_sreflWord (FCDet.isFlowType_of_mem_typeSet h))).2.2
  · have h' : sreflWord c ∉ FCDet.typeSet κ (-θ) nR nL ρR ρL := fun h' => h (mem_typeSet_sreflWord_iff.1 h')
    funext j
    simp only [FCDet.typeXL, FCDet.typeXR, h, h', ↓reduceIte, Pi.zero_apply, neg_zero]

/-- **The mean of the sorted mirror word is the reflected mean**, on `ℍ`. -/
theorem eqOn_mean_sreflWord (hc : c.IsSorted) :
    EqOn (sreflWord c).mean (fun z => -c.mean (reflectC z)) H := by
  have hu := Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect (S' := (reflJumps c.jumps : Set ℝ))
    (g' := reflData c.fn) (BoundaryWord.isBoundedHarmonicExtension_mean c hc) fun x hx =>
      ⟨fun h => hx (Sec7.FlowReflect.mem_reflJumps.2 h), rfl⟩
  have hv := BoundaryWord.isBoundedHarmonicExtension_mean (sreflWord c) (sreflWord_isSorted hc)
  rw [jumps_sreflWord] at hv
  have hv' := (isBoundedHarmonicExtension_congr (fun y hy => (fn_sreflWord_of_notMem hy).symm) _).2 hv
  exact Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet _) hu hv'

/-- **The mean pairing of the sorted mirror word** is minus the mean pairing of the reflected test function. -/
theorem integral_mean_sreflWord (hc : c.IsSorted) (φ : TestOn upperHalfPlaneOpens) :
    ∫ z, (sreflWord c).mean z * φ z = -∫ z, c.mean z * reflTest φ z := by
  have e : ∫ z, (sreflWord c).mean z * φ z = ∫ z, -c.mean (reflectC z) * φ z := by
    congr 1
    funext z
    by_cases hz : z ∈ H
    · rw [eqOn_mean_sreflWord hc hz]
    · have h0 : φ z = 0 := φ.zero_on_compl (show z ∈ ((upperHalfPlaneOpens : Set ℂ))ᶜ from hz)
      rw [h0, mul_zero, mul_zero]
  rw [e, ← integral_neg, ← Sec7.FlowReflect.integral_comp_reflectC]
  congr 1
  funext z
  simp only [LP.reflectC_reflectC, Sec7.FlowReflect.reflTest_apply, neg_mul]

end Word

section Germ

open LocalSets

theorem dist_reflectC (z w : ℂ) : dist (reflectC z) (reflectC w) = dist z w :=
  LP.isometry_reflectC.dist_eq z w

theorem reflectC_mem_thickening_iff {δ : ℝ} {E : Set ℂ} {z : ℂ} :
    reflectC z ∈ Metric.thickening δ (reflectC '' E) ↔ z ∈ Metric.thickening δ E := by
  simp only [Metric.mem_thickening_iff]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, hd⟩
    exact ⟨w, hw, by rwa [dist_reflectC] at hd⟩
  · rintro ⟨w, hw, hd⟩
    exact ⟨reflectC w, mem_image_of_mem _ hw, by rwa [dist_reflectC]⟩

theorem reflectC_mem_germNbhd_iff {δ : ℝ} {S : Set ℂ} {z : ℂ} :
    reflectC z ∈ germNbhd δ (reflectC '' S) ↔ z ∈ germNbhd δ S := by
  have hR : reflectC '' S ∩ H ∪ {w : ℂ | w.im = 0} = reflectC '' (S ∩ H ∪ {w : ℂ | w.im = 0}) := by
    rw [image_union, image_inter LP.reflectC_injective, Sec7.FlowReflect.reflectC_image_H]
    congr 1
    ext w
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · intro hw
      exact ⟨reflectC w, by rwa [LP.im_reflectC], LP.reflectC_reflectC w⟩
    · rintro ⟨v, hv, rfl⟩
      rwa [LP.im_reflectC]
  simp only [germNbhd, mem_inter_iff, mem_union, mem_ofPred_eq, LP.norm_reflectC, LP.reflectC_mem_H_iff]
  rw [hR, reflectC_mem_thickening_iff]

theorem tsupport_subset_germNbhd_reflect_iff {δ : ℝ} {S : Set ℂ} {φ : TestOn upperHalfPlaneOpens} :
    tsupport φ ⊆ germNbhd δ (reflectC '' S) ↔ tsupport (reflTest φ) ⊆ germNbhd δ S := by
  rw [Sec7.FlowReflect.tsupport_reflTest]
  constructor
  · rintro h _ ⟨z, hz, rfl⟩
    have := h hz
    rwa [← LP.reflectC_reflectC z, reflectC_mem_germNbhd_iff] at this
  · intro h z hz
    rw [← LP.reflectC_reflectC z, reflectC_mem_germNbhd_iff]
    exact h (mem_image_of_mem _ hz)

variable {Ω : Type*}

/-- **The germ σ-algebra is reflection invariant.** -/
theorem germSigma_reflect (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    germSigma (fun ω => reflectC '' A ω) (fun ω => reflField (h ω)) = germSigma A h := by
  unfold germSigma
  congr 1
  funext n
  unfold germSigmaAt
  congr 1
  · change MeasurableSpace.comap ((fun S : Set ℂ => reflectC '' S) ∘ A) hittingSigma = _
    rw [← MeasurableSpace.comap_comp, Sec7.FlowReflect.comap_eq_of_involutive'
      Sec7.FlowReflect.measurable_image_reflectC Sec7.FlowReflect.imageReflectC_involutive]
  · congr 1
    ext E
    constructor
    · rintro ⟨φ, B, hB, rfl⟩
      refine ⟨reflTest φ, Neg.neg ⁻¹' B, measurable_neg hB, ?_⟩
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, tsupport_subset_germNbhd_reflect_iff,
        Sec7.FlowReflect.reflField_apply]
    · rintro ⟨φ, B, hB, rfl⟩
      refine ⟨reflTest φ, Neg.neg ⁻¹' B, measurable_neg hB, ?_⟩
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, tsupport_subset_germNbhd_reflect_iff,
        Sec7.FlowReflect.reflField_apply, Sec7.FlowReflect.reflTest_reflTest, neg_neg]

end Germ

section LocalMean

open LocalSets WholeField

theorem reflField_sub (f g : DistOn upperHalfPlaneOpens) : reflField (f - g) = reflField f - reflField g := by
  ext φ
  simp only [Sec7.FlowReflect.reflField_apply, sub_apply, neg_sub_neg, neg_sub]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- **Local-set means under the reflection**: if `g` is a version of the local-set mean of `A` for `h`, then `−g ∘ σ`
is one of `σ(A)` for `−h ∘ σ`. -/
theorem IsLocalSetMean.reflect {A : Ω → Set ℂ} {h g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A h P g) :
    IsLocalSetMean (fun ω => reflectC '' A ω) (fun ω => reflField (h ω)) P (fun ω => reflField (g ω)) := by
  obtain ⟨hm, hharm, hcond⟩ := hg
  refine ⟨?_, ?_, ?_⟩
  · rw [germSigma_reflect]
    exact Sec7.FlowReflect.measurable_reflField.comp hm
  · filter_upwards [hharm] with ω hω
    rw [LP.H_diff_reflectC_image]
    exact Sec7.FlowReflect.isHarmonicDistOn_reflField hω
  · rw [germSigma_reflect]
    have h1 := Sec7.FlowReflect.isCondZeroBoundaryGFF_reflField hcond
    simp only [reflField_sub] at h1
    exact h1

/-- The smooth distribution of the reflected harmonic function is the reflected smooth distribution. -/
theorem smoothDist_reflect {u : ℂ → ℝ} (hu : ContinuousOn u H) :
    SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => -u (reflectC z)) =
      reflField (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u) := by
  have hcH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  have hu' : ContinuousOn (fun z => -u (reflectC z)) upperHalfPlaneOpens := by
    refine (hu.comp LP.continuous_reflectC.continuousOn fun z hz => ?_).neg
    exact LP.reflectC_mem_H_iff.2 hz
  have hu'' : ContinuousOn u upperHalfPlaneOpens := hu
  ext φ
  rw [Sec7.FlowReflect.reflField_apply, SupercriticalConformalCovariance.GM24.smoothDist_apply hu',
    SupercriticalConformalCovariance.GM24.smoothDist_apply hu'', ← integral_neg,
    ← Sec7.FlowReflect.integral_comp_reflectC (fun x => -(reflTest φ x * u x))]
  congr 1
  funext x
  simp only [Sec7.FlowReflect.reflTest_apply, LP.reflectC_reflectC, mul_neg]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- **The centred reflected field is the reflected centred field.** -/
theorem centredField_reflect {u : ℂ → ℝ} (hu : ContinuousOn u H) (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    centredField (fun ω => reflField (h ω)) (fun z => -u (reflectC z)) ω = reflField (centredField h u ω) := by
  simp only [centredField, smoothDist_reflect hu, reflField_sub]

end LocalMean

section Union

open Sec6

/-- The reflected recorded history. -/
def reflH (y : Hist) : Hist := (y.1, fun q => reflectC (y.2 q))

theorem meetsQ_swap_reflH {a b : ℝ≥0∞} {y : Hist × Hist} :
    MeetsQ a b (reflH y.2, reflH y.1) ↔ MeetsQ b a y := by
  simp only [MeetsQ, reflH, dist_reflectC]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun m => ?_⟩
    obtain ⟨q₁, q₂, h1, h2, h3, h4, h5, h6, h7⟩ := hN m
    exact ⟨q₂, q₁, h4, h5, h6, h1, h2, h3, by rwa [dist_comm]⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, fun m => ?_⟩
    obtain ⟨q₁, q₂, h1, h2, h3, h4, h5, h6, h7⟩ := hN m
    exact ⟨q₂, q₁, h4, h5, h6, h1, h2, h3, by rwa [dist_comm]⟩

theorem recFst_swap_reflH (y : Hist × Hist) : recFst (reflH y.2, reflH y.1) = recSnd y := by
  simp only [recFst, recSnd, meetsQ_swap_reflH]

theorem recSnd_swap_reflH (y : Hist × Hist) : recSnd (reflH y.2, reflH y.1) = recFst y := by
  simp only [recFst, recSnd, meetsQ_swap_reflH]

variable {Ω : Type*}

theorem fullHist_refl (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ω : Ω) :
    fullHist (fun ω t => reflectC (η₂ ω t)) (fun ω t => reflectC (η₁ ω t)) ω =
      (reflH (fullHist η₁ η₂ ω).2, reflH (fullHist η₁ η₂ ω).1) := by
  simp only [fullHist, histOf, reflH]
  refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_) <;> funext q <;> simp [stopCoord, pathCoord]

/-- **The first-contact union of the reflected pair is the reflected union.** -/
theorem fcUnion_refl (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ω : Ω) :
    fcUnion (fun ω t => reflectC (η₂ ω t)) (fun ω t => reflectC (η₁ ω t)) ω = reflectC '' fcUnion η₁ η₂ ω := by
  rw [fcUnion_eq, fcUnion_eq, fullHist_refl, recFst_swap_reflH, recSnd_swap_reflH,
    image_inter LP.reflectC_injective, Sec7.FlowReflect.reflectC_image_H, image_union, ← image_comp,
    ← image_comp, union_comm]
  rfl

end Union

section BoxMean

open LocalSets WholeField

universe u

/-- **Lemma 7.8's mean identification for the reflected configuration**, with the sorted mirror word. -/
theorem isBoxMeanIdentification_refl {κ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    {u₀ : ℂ → ℝ} (hu₀ : ContinuousOn u₀ H) {d : PairData Ω} (hd : d.IsMeasGood) {β : Ω → BoundaryWord}
    (hsort : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hmean : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    IsBoxMeanIdentification κ P (fun ω => reflField (h ω)) (fun ω t => reflectC (η₂ ω t))
      (fun ω t => reflectC (η₁ ω t)) ζ₂ ζ₁ (fun z => -u₀ (reflectC z)) (isMeasGood_reflPair hd)
      (fun ω => sreflWord (β ω)) := by
  intro m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  have hloc : IsLocalSetMean (fcUnion (fun ω t => reflectC (ηc₂ ω t)) (fun ω t => reflectC (ηc₁ ω t)))
      (centredField h u₀) P (fun ω => reflField (g ω)) := by
    have h1 := IsLocalSetMean.reflect hg
    have e1 : fcUnion (fun ω t => reflectC (ηc₂ ω t)) (fun ω t => reflectC (ηc₁ ω t)) =
        fun ω => reflectC '' fcUnion ηc₁ ηc₂ ω := funext (fcUnion_refl ηc₁ ηc₂)
    have e2 : centredField h u₀ = fun ω => reflField (centredField (fun ω => reflField (h ω))
        (fun z => -u₀ (reflectC z)) ω) := by
      funext ω
      rw [centredField_reflect hu₀, Sec7.FlowReflect.reflField_reflField]
    rw [e1, e2]
    exact h1
  have key := hmean m (fun ω t => reflectC (ηc₂ ω t)) (fun ω t => reflectC (ηc₁ ω t))
    (fun ω => reflField (g ω)) (fun ω => LP.continuous_reflectC.comp (hc₂ ω))
    (fun ω => LP.continuous_reflectC.comp (hc₁ ω)) (fun t => LP.continuous_reflectC.measurable.comp (hm₂ t))
    (fun t => LP.continuous_reflectC.measurable.comp (hm₁ t))
    (by filter_upwards [hag₂] with ω hω t; rw [hω t, LP.reflectC_reflectC])
    (by filter_upwards [hag₁] with ω hω t; rw [hω t, LP.reflectC_reflectC]) hloc
  filter_upwards [key, hsort] with ω hk hs hbox φ
  rw [reflPair_meetBox hd] at hbox
  have hsω := hs (mem_iUnion.2 ⟨m, hbox⟩)
  have e : g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun z => -u₀ (reflectC z)) =
      reflField (reflField (g ω) + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) := by
    rw [Sec7.FlowReflect.reflField_add, Sec7.FlowReflect.reflField_reflField, smoothDist_reflect hu₀]
  have e2 := chartTransport_reflPair hd ω 0 (chiC κ)
    (reflField (g ω) + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
  rw [neg_zero] at e2
  rw [e, e2, Sec7.FlowReflect.reflField_apply, hk hbox, integral_mean_sreflWord hsω]

end BoxMean

end InteractingSLE.Restart.FCPlumb.FCKerD
