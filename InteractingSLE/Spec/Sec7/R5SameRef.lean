/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5SameHeight
import InteractingSLE.Spec.Sec7.R5PhaseTwoSeed
import InteractingSLE.Spec.Sec7.Lemma725RefMarksWord
import InteractingSLE.Spec.Sec7.PocketPhaseMeans
import InteractingSLE.Spec.Supplement.WalkBdryCompare
import InteractingSLE.Spec.Supplement.Q3ChainDet

/-!
# Lemma R.5's old references on an R.7 pocket test: heights at the counterflow hull

Packet PROVE-R5-SAMETIME. For an R.7 change-pocket test (walls `R, L`, pocket `C = cfPocket R L r`, a walls-measurable
event `A`, a curve driven on `A`) and the counterflow coupling of `h''` (lifetime `⊤` almost surely), the old reference
at the original time `s` is `liveExt A γ C (regHull W' ζ' s) 0 = E ∪ K_s` with `E` the pocket exterior on the test
(`ℍ` off it) and `K_s` the counterflow hull.

* `measurable_centredField_walls`: the walls' centred field is a measurable function of the counterflow's;
* **`wallsSigma_le_aeSigma`**: the walls' σ-algebra is contained, up to null sets, in the counterflow field's (the walls
  are field-determined, transported to the counterflow frame by the chart relation of `IsCfDecomp`);
* `pocketExt` (the pocket exterior on the test), `pocketExt_union_regHull`, `measurableSet_disjoint_pocketExt`,
  **`pocketExt_facts`**: it is hitting-measurable, local (the raw reference law at time `0`, `pocketStopUnionLaw_ref`,
  where the hull is empty) and field-determined;
* **`ae_tendsto_harmRep_ref`**: every local-set mean `g` of the reference at time `s` has, almost surely on `A`, at
  every point `z₀` of the counterflow hull inside the pocket and along every approach `F` whose image under the
  ambient map `f_s` tends to a real non-jump point `x`, the reading `harmRep g + 𝔥₀ + χ arg f_s′ → β_s(x)` — the
  ambient word value (R.5's reference height with the ambient lift `liftB = arg f_s′`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Same

open LocalSets WholeField Aux119Heights PocketStopField PocketStopWalls PocketStopWallsFin PocketCoupling PocketStop
  PocketWordPerQ PocketCoord PocketJordan PocketStopSide PocketTraversal Lemma71C R5Phase PocketUnionPt

variable {Ω : Type*}

section Det

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
/-- A map almost surely equal to an `m`-measurable map is measurable for the null-completion `aeSigma m P`. -/
theorem measurable_aeSigma_of_ae_eq {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m : MeasurableSpace Ω} {X : Type*}
    [MeasurableSpace X] {g g' : Ω → X} (hg' : Measurable[m] g') (hgg : g =ᵐ[P] g') :
    Measurable[aeSigma m P] g := by
  intro B hB
  refine ⟨g' ⁻¹' B, hg' hB, ?_⟩
  filter_upwards [hgg] with ω hω
  show (ω ∈ g ⁻¹' B) = (ω ∈ g' ⁻¹' B)
  simp only [mem_preimage, hω]

omit mΩ in
theorem aeSigma_mono {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m m' : MeasurableSpace Ω} (hm : m ≤ m') :
    aeSigma m P ≤ aeSigma m' P :=
  fun _ ⟨G', hG', he⟩ => ⟨G', hm _ hG', he⟩

omit mΩ in
/-- **The walls' centred field is a measurable function of the counterflow's centred field** (the chart relation
`h'' = reflect(h) + m` of `PocketStopWallsFin.exists_centredField_counterflow_eq`). -/
theorem measurable_centredField_walls {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ u₀' : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀' : InnerProductSpace.HarmonicOnNhd u₀' H) :
    Measurable[MeasurableSpace.comap (centredField h'' u₀') inferInstance] (centredField h u₀) := by
  obtain ⟨m, hm⟩ := exists_centredField_counterflow_eq hT hTr hu₀ hu₀'
  refine (@LQGMetric.measurable_distOn_iff _ Ω (MeasurableSpace.comap (centredField h'' u₀') inferInstance) _).2
    fun ψ => ?_
  set ψ' := Chart.pushTest StripSysField.isConformal_infinityReturnChart ψ
  have e : (fun ω => centredField h u₀ ω ψ) = fun ω => m ψ' - centredField h'' u₀' ω ψ' := by
    funext ω
    rw [hm ψ' ω, WangWu.reflectField_apply, WangWu.pushTest_return_return]
    ring
  rw [e]
  exact measurable_const.sub ((LQGMetric.measurable_distOn_apply ψ').comp (comap_measurable _))

/-- **The walls' σ-algebra is field-determined**: it is contained, up to null sets, in the σ-algebra of the
counterflow's centred field (every wall value is almost surely a measurable function of the walls' field, which is a
measurable function of the counterflow's). -/
theorem wallsSigma_le_aeSigma {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω)) {u₀ u₀' : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀' : InnerProductSpace.HarmonicOnNhd u₀' H)
    {R L : Ω → ℝ≥0 → ℂ}
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω)) :
    wallsSigma P R L ≤ aeSigma (MeasurableSpace.comap (centredField h'' u₀') inferInstance) P := by
  have hw := measurable_centredField_walls hT hTr hu₀ hu₀'
  have hcoord : ∀ (i : Fin 2) (t : ℝ≥0),
      Measurable[aeSigma (MeasurableSpace.comap (centredField h'' u₀') inferInstance) P]
        fun ω => (![R, L] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω t := by
    intro i t
    fin_cases i
    · obtain ⟨f, hf, he⟩ := hdetR t
      exact measurable_aeSigma_of_ae_eq (hf.comp hw) he
    · obtain ⟨f, hf, he⟩ := hdetL t
      exact measurable_aeSigma_of_ae_eq (hf.comp hw) he
  have hfull := measurable_fullHist (mΩ := aeSigma (MeasurableSpace.comap (centredField h'' u₀') inferInstance) P)
    hcoord
  exact sup_le hfull.comap_le (Supp8.Q3Chain.nullSets_le_aeSigma _)

end Det

section Ext

/-- **The pocket exterior on the test** (`ℍ` off the test): the reference at relative level `0` with no hull. -/
def pocketExt (A : Set Ω) (γ : Ω → ℝ → ℂ) (C : Ω → Set ℂ) : Ω → Set ℂ := liveExt A γ C (fun _ => ∅) 0

/-- The reference with a hull `K ⊆ ℍ` is the union of the pocket exterior and `K`. -/
theorem pocketExt_union {A : Set Ω} {γ : Ω → ℝ → ℂ} {C K : Ω → Set ℂ} (hKH : ∀ ω, K ω ⊆ H) (ω : Ω) :
    pocketExt A γ C ω ∪ K ω = liveExt A γ C K 0 ω := by
  by_cases hl : ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)
  · rw [pocketExt, liveExt_of_live hl, liveExt_of_live hl, extHullSet, extHullSet]
    ext z
    simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_empty_iff_false, or_false]
    constructor
    · rintro (⟨hz, hzC⟩ | hzK)
      · exact ⟨hz, Or.inl hzC⟩
      · exact ⟨hKH ω hzK, Or.inr hzK⟩
    · rintro ⟨hz, hzC | hzK⟩
      · exact Or.inl ⟨hz, hzC⟩
      · exact Or.inr hzK
  · rw [pocketExt, liveExt_of_not_live hl, liveExt_of_not_live hl]
    exact union_eq_left.2 (hKH ω)

theorem live_zero_of_driven {A : Set Ω} {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ω : Ω}
    (hω : ω ∈ A) : ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) :=
  ⟨hω, by rw [ENNReal.coe_zero]; exact PocketPhaseMeans.capLife_pos (hγ ω hω)⟩

/-- On the test the pocket exterior is `ℍ ∖ C`. -/
theorem pocketExt_of_mem {A : Set Ω} {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {C : Ω → Set ℂ}
    {ω : Ω} (hω : ω ∈ A) : pocketExt A γ C ω = H ∩ (C ω)ᶜ := by
  rw [pocketExt, liveExt_of_live (live_zero_of_driven hγ hω), extHullSet, union_empty]

/-- **The avoidance events of the pocket exterior** are events of any σ-algebra containing the test and its
pocket-inclusion events. -/
theorem measurableSet_disjoint_pocketExt {𝓦 : MeasurableSpace Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {C : Ω → Set ℂ}
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet[𝓦] {ω | Disjoint (pocketExt A γ C ω) U} := by
  rcases U.eq_empty_or_nonempty with hU | hU
  · have e : {ω | Disjoint (pocketExt A γ C ω) U} = univ := by
      ext ω
      simp only [hU, disjoint_empty, mem_ofPred_eq, mem_univ]
    rw [e]
    exact MeasurableSet.univ
  · have e : {ω | Disjoint (pocketExt A γ C ω) U} = {ω | ω ∈ A ∧ U ⊆ C ω} := by
      ext ω
      simp only [mem_ofPred_eq]
      by_cases hω : ω ∈ A
      · rw [pocketExt_of_mem hγ hω]
        constructor
        · intro hd
          refine ⟨hω, fun z hz => ?_⟩
          by_contra hzC
          exact disjoint_left.1 hd ⟨hUH hz, hzC⟩ hz
        · rintro ⟨-, hUC⟩
          exact disjoint_left.2 fun z hz hzU => hz.2 (hUC hzU)
      · have hl : ¬ (ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)) := fun h => hω h.1
        rw [pocketExt, liveExt_of_not_live hl]
        simp only [hω, false_and, iff_false]
        obtain ⟨z, hz⟩ := hU
        exact fun hd => disjoint_left.1 hd (hUH hz) hz
    rw [e]
    exact hCin U hUo hUH

end Ext

section R7

variable {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

omit mΩ in
/-- The regularized hull at time `0` is empty. -/
theorem regHull_zero (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : regHull W ζ 0 = fun _ => ∅ := by
  funext ω
  rw [regHull, NNReal.coe_zero]
  exact QuantumZipper.RS.fwdHull_zero_eq_empty ((continuous_regDrv W ζ ω).comp continuous_real_toNNReal)

/-- **The pocket exterior of an R.7 change-pocket test** is hitting-measurable, field-determined (in the counterflow
frame) and a local set of the counterflow's centred field. The inputs are exactly the walls' data of
`R5Phase.pocketStopUnionLaw_ref`. -/
theorem pocketExt_facts
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) :
    Measurable[mΩ, hittingSigma] (pocketExt A γ fun ω => cfPocket (R ω) (L ω) r) ∧
      MeasurableSpace.comap (pocketExt A γ fun ω => cfPocket (R ω) (L ω) r) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h'' u₀') inferInstance) P ∧
      IsLocalSet (pocketExt A γ fun ω => cfPocket (R ω) (L ω) r) (centredField h'' u₀') P := by
  have hU := pocketStopUnionLaw_ref hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
    hlocL hGm hG hA hAG hγ 0
  rw [regHull_zero] at hU
  obtain ⟨E', hE'm, hloc, hEq⟩ := hU
  have hle := refInfo_le (P := P) hX hRm hLm 0
  have hA' : MeasurableSet[refInfo P hX R L 0] A := wallsSigma_le_refInfo (P := P) hX R L 0 _ hA
  have hpre : locPrefixSigma (refInfo P hX R L 0) A γ 0 = refInfo P hX R L 0 :=
    PocketStopSide.locPrefixSigma_zero_of_driven hA' hγ
  have hL := measurableSet_live (𝓦 := refInfo P hX R L 0) A γ 0
  have hLm' : MeasurableSet[mΩ] {ω | ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)} := hle _ (hpre ▸ hL)
  have hmE : Measurable[mΩ, hittingSigma] (pocketExt A γ fun ω => cfPocket (R ω) (L ω) r) :=
    measurable_liveExt hLm' hE'm hEq
  have hlocE := isHistoryAvoidanceLocal_liveExt hL hloc hEq
  have hreg : ∀ᵐ ω ∂P, pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω ⊆ H ∧
      IsOpen (H \ pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω) := by
    refine Eventually.of_forall fun ω => ?_
    by_cases hω : ω ∈ A
    · rw [pocketExt_of_mem hγ hω]
      have hCH : cfPocket (R ω) (L ω) r ⊆ H :=
        PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
      have hCo : IsOpen (cfPocket (R ω) (L ω) r) :=
        isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
      refine ⟨inter_subset_left, ?_⟩
      have e : H \ (H ∩ (cfPocket (R ω) (L ω) r)ᶜ) = cfPocket (R ω) (L ω) r := by
        ext z
        simp only [Set.mem_sdiff, mem_inter_iff, mem_compl_iff, not_and, not_not]
        exact ⟨fun hz => hz.2 hz.1, fun hz => ⟨hCH hz, fun _ => hz⟩⟩
      rw [e]
      exact hCo
    · have hl : ¬ (ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω)) := fun h => hω h.1
      rw [pocketExt, liveExt_of_not_live hl, Set.sdiff_self]
      exact ⟨subset_rfl, isOpen_empty⟩
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀'
  refine ⟨hmE, ?_, ((isLocalSet_tfae hh0 hmE hreg).out 1 4).1 hlocE.isAvoidanceLocal⟩
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have hWle := wallsSigma_le_aeSigma (P := P) hT' hTr hu₀ hu₀'.1 hdetR hdetL
  refine Theorem14.WalkBdry.hitting_comap_le_aeSigma fun U hUH => hWle _ ?_
  exact measurableSet_disjoint_pocketExt hγ
    (fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH)
    U.isOpen hUH

/-- **R.5's old reference at an original time keeps the ambient word at the counterflow hull** (R.7 change-pocket
tests). For the reference `liveExt A γ C (regHull W' ζ' s) 0` (pocket exterior ∪ counterflow hull at the deterministic
time `s`) and every local-set mean `g` of it for the counterflow's centred field: almost surely on the test, at every
point `z₀` of the hull inside the pocket and along every approach `F` (within `ℍ` at `ξ`) staying in the reference
complement whose image under the ambient Loewner map `f_s` tends to a real point `x` off the jump set at time `s`,
`harmRep g + 𝔥₀ + χ arg f_s′ → β_s(x)`, the force data at the centred positions at time `s`. -/
theorem ae_tendsto_harmRep_ref
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (s : ℝ≥0) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0)
      (centredField h'' u₀') P g) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ z₀ ∈ cfPocket (R ω) (L ω) r ∩ regHull W' ζ' s ω, ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun i => VL i s ω - W' s ω) (fun i => VR i s ω - W' s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) →
      (∀ᶠ y in 𝓝[H] ξ, F y ∈ H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω)
          (F y) + u₀' (F y) + chiC κ' * (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData κ' ρL ρR (fun i => VL i s ω - W' s ω) (fun i => VR i s ω - W' s ω) x)) := by
  obtain ⟨hEm, hEd, hEl⟩ := pocketExt_facts hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ
  have hKH : ∀ ω, regHull W' ζ' s ω ⊆ H := fun ω z hz => hz.1
  have hunion : (fun ω => pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω ∪ regHull W' ζ' s ω) =
      liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 := funext (pocketExt_union hKH)
  have hg' : IsLocalSetMean (fun ω => pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω ∪ regHull W' ζ' s ω)
      (centredField h'' u₀') P g := by
    rw [hunion]
    exact hg
  have hKm : Measurable[mΩ, hittingSigma] (regHull W' ζ' s) :=
    measurable_regHull (T := fun _ => s) hX measurable_const
  have hsζ : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζ' ω := by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact ENNReal.coe_lt_top
  have hKeq : ∀ᵐ ω ∂P, regHull W' ζ' s ω = fwdHull (fun t : ℝ => W' t.toNNReal ω) s := by
    filter_upwards [hζ, hC.1.2.2.2.2] with ω hζω hp
    have hcont : Continuous fun t => W' t ω := by
      rw [← continuousOn_univ]
      refine hp.2.2.2.1.mono fun t _ => ?_
      show ((t : ℝ≥0∞)) < ζ' ω
      rw [hζω]
      exact ENNReal.coe_lt_top
    exact regHull_eq hcont hζω s
  filter_upwards [ae_tendsto_harmRep_unionMean hC hκ' hu₀' hX s hsζ hKm hKeq hEm hEd hEl hg']
    with ω hω hωA z₀ hz₀ F ξ x hx hF hFU hfF
  have hCo : IsOpen (cfPocket (R ω) (L ω) r) :=
    isOpen_image_negInv' (hG ω (hAG hωA)).isOpen_changePocket (hG ω (hAG hωA)).changePocket_subset_H
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hCo z₀ hz₀.1
  have hball' : ∃ ρ > 0, pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω ∩ ball z₀ ρ ⊆ regHull W' ζ' s ω := by
    refine ⟨ρ, hρ, fun z hz => ?_⟩
    rw [pocketExt_of_mem hγ hωA] at hz
    exact absurd (hball hz.2) hz.1.2
  have he := pocketExt_union (A := A) (γ := γ) (C := fun ω => cfPocket (R ω) (L ω) r) hKH ω
  rw [← he] at hFU ⊢
  exact hω z₀ hz₀.2 hball' F ξ x hx hF hFU hfF

/-- **`ae_tendsto_harmRep_ref` for R.5's whole countable reference family** (`R5Phase.refHull`, the references at the
rational original times; the sets `liveExt A γ C (refHull W' ζ' i) 0` of `R5Phase.R5Clauses`), on one event: the
reference heights in the ambient lifts `liftB i ω = arg f′_{s_i}` are the ambient words at the times `s_i`. -/
theorem ae_tendsto_harmRep_refHull
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'')
    (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {gB : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgB : ∀ i, IsLocalSetMean (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
      (centredField h'' u₀') P (gB i)) :
    ∀ᵐ ω ∂P, ω ∈ A → ∀ i : ℕ, let s := Wire.Current.SideTest.rationalOriginalTime i;
      ∀ z₀ ∈ cfPocket (R ω) (L ω) r ∩ refHull W' ζ' i ω, ∀ (F : ℂ → ℂ) (ξ : ℂ) (x : ℝ),
      x ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) →
      Tendsto F (𝓝[H] ξ) (𝓝 z₀) →
      (∀ᶠ y in 𝓝[H] ξ, F y ∈ H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω) →
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s (F y)) (𝓝[H] ξ) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω)
          (F y) + u₀' (F y) + chiC κ' * (logDerivFwd (fun t : ℝ => W' t.toNNReal ω) s (F y)).im) (𝓝[H] ξ)
        (𝓝 (forceBoundaryData κ' ρL ρR (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) x)) := by
  have hall := ae_all_iff.2 fun i => ae_tendsto_harmRep_ref hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0
    hRm hLm hdetR hdetL hlocR hlocL hGm hG hA hAG hγ (Wire.Current.SideTest.rationalOriginalTime i) (hgB i)
  filter_upwards [hall] with ω hω hωA i
  exact hω i hωA

end R7

end InteractingSLE.Sec7.R5Same
