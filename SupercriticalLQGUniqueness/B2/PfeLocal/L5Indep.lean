import SupercriticalLQGUniqueness.B2.PfeLocal.L5Var
import LQGMetric.Papers.LM.T1_7E6

 

















set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open Function (onFun)
open LQGMetric (CondIndepEv DistC IsWholePlaneGFF)

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open LQGMetric.Blueprint LQGMetric.GM.Bilip LQGMetric.DFGPS.L219 LQGMetric.LM

 
theorem l5_seqIndep {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {L : Ω → LSCMetric}
    (hL : Measurable L) (hloc : Inputs.L5ObsLocality P h L) {ι : Type*} (W : ι → Set ℂ)
    (hWo : ∀ i, IsOpen (W i)) (hWb : ∀ i, Bornology.IsBounded (W i))
    (hWd : Pairwise (onFun Disjoint W)) :
    T17eSeqIndep h id (fun i ω => l5Enc (W i) (L ω)) P := by
  intro T j hj
  have hm := hh.measurable
  set V : TopologicalSpace.Opens ℂ := ⟨⋃ i ∈ T, W i, isOpen_biUnion fun i _ => hWo i⟩
  have hVb : Bornology.IsBounded (V : Set ℂ) :=
    (Bornology.isBounded_biUnion_finset T).2 fun i _ => hWb i
  have hsub : ∀ i ∈ T, W i ⊆ V := fun i hi => subset_biUnion_of_mem (u := W) hi
  have hdisj : Disjoint (W j) (V : Set ℂ) := by
    refine disjoint_iUnion₂_right.2 fun i hi => hWd ?_
    rintro rfl
    exact hj hi
  have hsubc : W j ⊆ (closure (V : Set ℂ))ᶜ :=
    (hdisj.closure_right (hWo j)).subset_compl_right
  have h1 := hloc V
  have h2 : CondIndepEv (fieldSigma h V) (l5ObsSigma L V)
      (MeasurableSpace.comap h inferInstance ⊔ l5ObsSigma L (closure (V : Set ℂ))ᶜ) P :=
    condIndepEv_transfer (fieldSigma_le hm V) (l5ObsSigma_le hL _)
      (sup_le (fieldSigmaClosed_le hm _) (l5ObsSigma_le hL _)) (fieldSigma_le hm V) h1
      (le_aeClosure _) (le_sup_right.trans (le_aeClosure _)) (le_sup_left.trans (le_aeClosure _))
      (sup_le ((LQGMetric.GermSplit.locGermSplitBdd P h hh V hVb).trans
        (aeClosure_mono (sup_le le_sup_right (le_sup_left.trans le_sup_left))))
        ((le_sup_right.trans le_sup_left).trans (le_aeClosure _)))
  have h3 : CondIndepEv (MeasurableSpace.comap h inferInstance) (l5ObsSigma L V)
      (l5ObsSigma L (closure (V : Set ℂ))ᶜ) P :=
    condIndepEv_transfer (fieldSigma_le hm V) (l5ObsSigma_le hL _)
      (sup_le hm.comap_le (l5ObsSigma_le hL _)) hm.comap_le h2
      ((fieldSigma_le_comapH h V).trans (le_aeClosure _))
      ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
      (le_sup_left.trans (le_aeClosure _))
      ((le_sup_right.trans le_sup_left).trans (le_aeClosure _))
  refine h3.mono ?_ ?_
  · exact iSup₂_le fun i hi => (l5_comap_enc_le L (W i)).trans (l5ObsSigma_mono L (hsub i hi))
  · exact (l5_comap_enc_le L (W j)).trans (l5ObsSigma_mono L hsubc)

 

theorem l5_condDistrib_pi {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {L : Ω → LSCMetric} (hL : Measurable L) (hloc : Inputs.L5ObsLocality P h L)
    {ι : Type} [Fintype ι] [DecidableEq ι] (W : ι → Set ℂ) (hWo : ∀ i, IsOpen (W i))
    (hWb : ∀ i, Bornology.IsBounded (W i)) (hWd : Pairwise (onFun Disjoint W)) :
    ∀ᵐ g ∂P.map h, (condDistrib id h P g).map (fun ω i => l5Enc (W i) (L ω)) =
      Measure.pi fun i => (condDistrib id h P g).map fun ω => l5Enc (W i) (L ω) :=
  t17e_condDistrib_pi hh.measurable measurable_id (fun i => (measurable_l5Enc (W i)).comp hL)
    (l5_seqIndep hh hL hloc W hWo hWb hWd)

 
theorem l5_grid_pi {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {L : Ω → LSCMetric} (hL : Measurable L) (hloc : Inputs.L5ObsLocality P h L) :
    ∀ᵐ g ∂P.map h, ∀ R j M i : ℕ, (condDistrib id h P g).map (l5SqEnc L R j M i) =
      Measure.pi fun k => (condDistrib id h P g).map fun ω => l5SqEnc L R j M i ω k := by
  refine ae_all_iff.2 fun R => ae_all_iff.2 fun j => ae_all_iff.2 fun M => ae_all_iff.2 fun i => ?_
  exact l5_condDistrib_pi hh hL hloc
    (fun k : t17Box (l5Mesh j) (R : ℝ) => t17Square (l5Mesh j) (l5Shift M i) k)
    (fun k => t17_isOpen_square _ _ _) (fun k => t17e_square_bounded _ _ _)
    fun k l hkl => t17Square_disjoint (l5Mesh_pos j) _ fun h => hkl (Subtype.ext h)

end SupercriticalLQGUniqueness.B2.PfeLocal
