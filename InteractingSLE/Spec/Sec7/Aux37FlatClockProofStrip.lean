/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofPath
import InteractingSLE.Spec.Sec7.PocketStopWallsFinHull
import InteractingSLE.Spec.Sec7.PocketStopWallsFinReflect
import InteractingSLE.WangWu.ReverseContactMartFilt2Glue
import InteractingSLE.Spec.Sec5.CrossCond
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Spec.Supplement.WalkStageLocalAE

/-!
# Aux. lemma 37's flat clock, part 4: the strip exploration `m⁻¹(K′_t) ∪ α ∪ β`

Packet PROVE-FLATCLOCK. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L84–L95, pp. 197–198):
"The stochastic exploration in this proof is the union of the *filled* original counterflow hull `K_t` with the two
complete incoming curves. Its marked filtration and its Gaussian kernels are the ones in the hypotheses."

For the strip system's counterflow (flow chart, `cfHull W′ ζ′ t = m⁻¹(K′_t)`) and two complete walls `β`, `α` with
Lemma 6.2's inputs (continuous from `0`, field-determined, entrance-history local, transient), the exploration
`E_t = stripExpl W′ ζ′ β α t` is, at every deterministic time `t`, a history-marked local set of the centred field with
the marks `ℋ_t = σ(walls' full histories) ∨ 𝓕′_t` (`𝓕′` the counterflow's driving filtration):

* the counterflow hull in the flow chart, `negInv '' K̃′_t` (`K̃′` PROVE-STRIPSYS41's regularized hull), is marked local
  at every finite stopping time of `𝓕′` (`WangWu.isHistoryAvoidanceLocal_reflect_hull`, for the centred field written
  as `reflectField h′ − D` with `D` harmonic), and its avoidance events are adapted;
* the walls are determined local (`PocketStopWalls.walls_determinedLocal`) and recorded by their histories
  (`measurable_wallUnion_fullHist`);
* PROVE-STRIPSYS37's `isHistoryAvoidanceLocal_walls_hull_stoppingTime` at the constant stopping time `t` gives the union
  law for the version `ℍ ∩ (walls ∪ negInv '' K̃′_t)`, which equals `E_t` almost surely.

The marks increase in `t` and `E_r` (`r ≤ s`) is recorded by `ℋ_s` up to null sets, so the nested comparison
`IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq` and `flatClockStatement_of_nested` give

* **`stripExpl_markedLaw`**: the marks, the marked law at every time, the recording of `E_r` by `ℋ_s`, measurability,
  relative closedness and monotonicity;
* **`flatClockStatement_stripExpl_of_walls`**: `Aux37Germ.FlatClockStatement P univ (stripExpl W′ ζ′ β α) g` for every
  family `g` of versions of the means;
* `exists_isLocalSetMean_stripExpl_of_walls`: `E_t` is a local set and versions `g t` of its means exist.

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.FlatClockProof

open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open WangWu (negInv reflectField)
open LocalSets Aux119Nested Aux37Germ
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-! ### Hitting measurability -/

section Hitting

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The union of two hitting-measurable random sets is hitting-measurable. -/
theorem measurable_union_hitting {A B : Ω → Set ℂ} (hA : Measurable[m, hittingSigma] A)
    (hB : Measurable[m, hittingSigma] B) : Measurable[m, hittingSigma] fun ω => A ω ∪ B ω := by
  refine @measurable_generateFrom Ω (Set ℂ) m _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : (fun ω => A ω ∪ B ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      A ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} ∪ B ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, union_inter_distrib_right, union_nonempty]
  rw [e]
  exact (hA (measurableSet_hitting hUo hUH)).union (hB (measurableSet_hitting hUo hUH))

/-- **The walls are recorded by their full histories**: `wallUnion β α` is measurable for `σ(fullHist ![β, α])`. -/
theorem measurable_wallUnion_fullHist {β α : Ω → ℝ≥0 → ℂ} (hβc : ∀ ω, Continuous (β ω))
    (hαc : ∀ ω, Continuous (α ω)) :
    Measurable[MeasurableSpace.comap (PocketStopWalls.fullHist ![β, α]) inferInstance, hittingSigma]
      (wallUnion β α) := by
  have hc : ∀ i ω, Continuous ((![β, α] : Fin 2 → Ω → ℝ≥0 → ℂ) i ω) := fun i ω => by
    fin_cases i
    · exact hβc ω
    · exact hαc ω
  rw [wallUnion_eq_explored]
  refine @measurable_generateFrom Ω (Set ℂ) (MeasurableSpace.comap (PocketStopWalls.fullHist ![β, α])
    inferInstance) _ _ ?_
  rintro _ ⟨V, hVo, hVH, rfl⟩
  have e : Sec6.explored ![β, α] (fun _ _ => ⊤) ⁻¹' {S : Set ℂ | (S ∩ V).Nonempty} =
      ⋃ i, ⋃ q : ℚ≥0, PocketStopWalls.fullHist ![β, α] ⁻¹'
        {F : Fin 2 → Sec6.Hist | (F i).2 q ∈ V} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, Sec6.explored_inter_nonempty_iff hc hVo hVH ω, mem_iUnion, le_top,
      true_and, PocketStopWalls.fullHist, Sec6.histOf, Sec6.stopCoord, ↓reduceIte, Sec6.pathCoord]
  rw [e]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun q => ?_
  exact MeasurableSpace.measurableSet_comap.2 ⟨_, ((measurable_pi_apply q).comp
    (measurable_snd.comp (measurable_pi_apply i))) hVo.measurableSet, rfl⟩

end Hitting

/-! ### The strip exploration -/

section Strip

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- The strip system's counterflow hull lies in `ℍ` (every sample). -/
theorem cfHull_subset_H (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : cfHull W' ζ' t ω ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  exact WangWu.negInv_mem_H ((Sec5.GlueCond.hullAt_relClosed t _).1 hz)

/-- `Disjoint (S ∩ ℍ) V ↔ Disjoint S V` for `V ⊆ ℍ`. -/
theorem disjoint_inter_H_iff {S V : Set ℂ} (hV : V ⊆ H) : Disjoint (S ∩ H) V ↔ Disjoint S V := by
  constructor
  · intro hd
    exact Set.disjoint_left.2 fun z hzS hzV => Set.disjoint_left.1 hd ⟨hzS, hV hzV⟩ hzV
  · intro hd
    exact hd.mono_left inter_subset_left

/-- **The marked law of the strip exploration** (Aux. lemma 37, pp. 197–198: "its marked filtration and its Gaussian
kernels"): for the strip system's counterflow and two complete walls `β`, `α` with Lemma 6.2's inputs there are marks
`ℋ_t ≤ mΩ`, increasing in `t` (here `σ(walls' full histories) ∨ 𝓕′_t`), such that at every time `t` the exploration
`E_t = stripExpl W′ ζ′ β α t` is a history-marked local set of the centred field with marks `ℋ_t`; `E_r` is recorded by
`σ(E_s) ∨ ℋ_s` up to null sets for `r ≤ s`; `E_t` is hitting-measurable and almost surely relatively closed in `ℍ`;
and `E_r ⊆ E_s` almost surely for `r ≤ s`. -/
theorem stripExpl_markedLaw {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β α : Ω → ℝ≥0 → ℂ}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ)) :
    ∃ ℋ : ℝ≥0 → MeasurableSpace Ω, (∀ t, ℋ t ≤ mΩ) ∧ (∀ r s : ℝ≥0, r ≤ s → ℋ r ≤ ℋ s) ∧
      (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P) ∧
      (∀ r s : ℝ≥0, r ≤ s → MeasurableSpace.comap (stripExpl W' ζ' β α r) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (stripExpl W' ζ' β α s) hittingSigma ⊔ ℋ s) P) ∧
      (∀ t, Measurable[mΩ, hittingSigma] (stripExpl W' ζ' β α t)) ∧
      (∀ t, ∀ᵐ ω ∂P, stripExpl W' ζ' β α t ω ⊆ H ∧ IsOpen (H \ stripExpl W' ζ' β α t ω)) ∧
      (∀ r s : ℝ≥0, r ≤ s → ∀ᵐ ω ∂P, stripExpl W' ζ' β α r ω ⊆ stripExpl W' ζ' β α s ω) := by
  have hκ := hS.kappa_pos
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  have hXm := hX.measurable
  /- the walls -/
  set η : Fin 2 → Ω → ℝ≥0 → ℂ := ![β, α] with hη
  have hc : ∀ i ω, Continuous (η i ω) := fun i ω => by
    fin_cases i
    · exact hβc ω
    · exact hαc ω
  have h0 : ∀ i ω, η i ω 0 = (fun _ => (0 : ℂ)) i := fun i ω => by
    fin_cases i
    · exact hβ0 ω
    · exact hα0 ω
  have hm : ∀ i t, Measurable fun ω => η i ω t := fun i t => by
    fin_cases i
    · exact hβm t
    · exact hαm t
  have hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω) := fun i t => by
    fin_cases i
    · exact hβdet t
    · exact hαdet t
  have hloc : ∀ i, Sec6.IsEntranceHistoryLocal (η i) (WholeField.centredField h u₀) P := fun i => by
    fin_cases i
    · exact hβloc
    · exact hαloc
  have hΓeq : ∀ ω, (⋃ i, range (η i ω)) ∩ H = wallUnion β α ω := fun ω => by
    rw [wallUnion_eq_explored, PocketStopWalls.explored_top]
  have hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens
        (WholeField.centredField h u₀) (fun ω => G (WholeField.centredField h u₀ ω)) P →
      ∀ B : Set (Fin 2 → Sec6.Hist), MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (wallUnion β α ω) U} ∩ PocketStopWalls.fullHist η ⁻¹' B =ᵐ[P]
          (fun ω => markovCompl G (WholeField.centredField h u₀ ω)) ⁻¹' B' := by
    intro U G hUH hG hd B hB
    obtain ⟨B', hB', he⟩ := PocketStopWalls.walls_determinedLocal hXm hc h0 hm hdet hloc U G hUH hG hd B hB
    refine ⟨B', hB', ?_⟩
    simpa only [hΓeq] using he
  obtain ⟨hΓm, hΓloc, -⟩ := isLocalSet_wallUnion hX hβc hβ0 hβm hβdet hβloc hαc hα0 hαm hαdet hαloc htr
  have hΓX := measurable_wallUnion_fullHist hβc hαc
  have hXfm : Measurable (PocketStopWalls.fullHist η) := PocketStopWalls.measurable_fullHist hm
  /- the counterflow -/
  have hreg := StripPocketPath.ae_counterflow_trace hS hcumL hcumR
  have hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤ := hreg.mono fun ω hω => hω.1
  obtain ⟨b', J', h', -, htrc, hfl⟩ := hS.counterflow
  obtain ⟨h'', 𝓕c, VL, VR, B, htac, hC⟩ := hfl
  have e : h'' = h' := funext fun ω =>
    Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
  subst e
  have hXc := hC.2.2.2.1
  have hκ' : (0 : ℝ) < 16 / κ := by positivity
  set 𝓕 := drivingFiltration P hXc with h𝓕
  have : 𝓕.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  -- the centred field read in the counterflow chart
  set D : DistOn upperHalfPlaneOpens :=
    Sec5.CrossCond.cfShiftDist κ u₀ + smoothDist upperHalfPlaneOpens (fun _ => π / 2 * chiC κ) with hD
  have hDh : IsHarmonicDistOn D H :=
    Coupling.IsHarmonicDistOn.add' QuantumZipper.isOpen_H (Sec5.CrossCond.isHarmonicDistOn_cfShiftDist κ hu₀.1)
      (WholeField.isHarmonicDistOn_smoothDist fun _ _ => InnerProductSpace.harmonicAt_const _)
  have hfield : WholeField.centredField h u₀ = fun ω => reflectField (h'' ω) - D := by
    funext ω
    have e1 := Sec5.CrossCond.cenT_eq_reflectField_sub κ u₀ (htrc ω)
    rw [Sec5.GlueCond.cenT_eq_add_sub] at e1
    rw [hD, sub_add_eq_sub_sub, ← e1]
    simp only [WholeField.centredField]
    abel
  -- the hull process in the flow chart
  set K : ℝ≥0 → Ω → Set ℂ := fun t ω => negInv '' PocketStopWallsFin.regHull W' ζ' t ω with hK
  have hKmono : ∀ ω, Monotone fun t => K t ω := fun ω _ _ hst =>
    image_mono (PocketStopWallsFin.regHull_mono W' ζ' ω hst)
  have hKdisj : ∀ (S : Set ℂ) (U : Set ℂ), U ⊆ H → (Disjoint (negInv '' S) U ↔ Disjoint S (negInv '' U)) :=
    fun S U hUH => by
      rw [PocketStopWallsFin.disjoint_image_negInv_iff hUH]
      exact disjoint_inter_H_iff (image_subset_iff.2 fun z hz => WangWu.negInv_mem_H (hUH hz))
  have hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U} := by
    intro t U hUo hUH
    have hU' : negInv '' U ⊆ H := image_subset_iff.2 fun z hz => WangWu.negInv_mem_H (hUH hz)
    have e : {ω | Disjoint (K t ω) U} = {ω | Disjoint (PocketStopWallsFin.regHull W' ζ' t ω) (negInv '' U)} := by
      ext ω
      exact hKdisj _ U hUH
    rw [e]
    exact PocketStopWallsFin.measurableSet_disjoint_regHull hC hκ' hXc hζ t (negInv '' U)
      (WangWu.isOpen_image_negInv hUo hUH) hU'
  have hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {ω | Disjoint (K ((τ ω).untopD 0) ω) U} := by
    intro τ hτ hfin U hUo hUH
    have hU' : negInv '' U ⊆ H := image_subset_iff.2 fun z hz => WangWu.negInv_mem_H (hUH hz)
    have e : {ω | Disjoint (K ((τ ω).untopD 0) ω) U} =
        {ω | Disjoint (PocketStopWallsFin.regHull W' ζ' ((τ ω).untopD 0) ω) (negInv '' U)} := by
      ext ω
      exact hKdisj _ U hUH
    rw [e]
    exact PocketStopWallsFin.measurableSet_disjoint_regHull_stopping hC hκ' hXc hζ τ hτ hfin (negInv '' U)
      (WangWu.isOpen_image_negInv hUo hUH) hU'
  have hlocK : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      WholeField.IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => K ((τ ω).untopD 0) ω)
        (WholeField.centredField h u₀) P := by
    intro τ hτ hfin
    have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ' ω := by
      filter_upwards [hζ] with ω hω
      rw [hω]
      exact lt_top_iff_ne_top.2 (by exact_mod_cast hfin ω)
    have hA : Measurable[mΩ, hittingSigma] fun ω => K ((τ ω).untopD 0) ω :=
      WangWu.measurable_image_negInv.comp (PocketStopWallsFin.measurable_regHull hXc
        (PocketStopWallsFin.measurable_untopD_of_isStoppingTime hτ hfin))
    have hAK : ∀ᵐ ω ∂P, K ((τ ω).untopD 0) ω =
        negInv '' fwdHull (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
      filter_upwards [PocketStopWallsFin.ae_regHull_eq hC hζ] with ω hω
      simp only [hK, hω]
    have hl := WangWu.isHistoryAvoidanceLocal_reflect_hull hC hκ' hDh hXc hτ hτζ hA hAK
    rwa [← hfield] at hl
  /- the union law of the version `ℍ ∩ (walls ∪ K_t)` at every time -/
  set ℋ : ℝ≥0 → MeasurableSpace Ω := fun t =>
    MeasurableSpace.comap (PocketStopWalls.fullHist η) inferInstance ⊔ 𝓕 t with hℋ
  have hlaw : ∀ t : ℝ≥0, WholeField.IsHistoryAvoidanceLocal (ℋ t)
      (PocketStopWalls.wallsHullAt (wallUnion β α) K fun _ => ((t : WithTop ℝ≥0) : ℝ≥0∞))
      (WholeField.centredField h u₀) P := by
    intro t
    have hl := PocketStopWalls.isHistoryAvoidanceLocal_walls_hull_stoppingTime hXm hXfm hΓm hW hKmono hKad hKst
      hlocK (isStoppingTime_const 𝓕 t)
    rwa [IsStoppingTime.measurableSpace_const] at hl
  /- the version equals the exploration almost surely -/
  have hKeq : ∀ᵐ ω ∂P, ∀ t, cfHull W' ζ' t ω = K t ω := by
    filter_upwards [hreg, PocketStopWallsFin.ae_regHull_eq hC hζ] with ω hω hω' t
    simp only [Aux37Germ.cfHull, Sec5.GlueCond.cfHullQ, hK, Sec5.GlueCond.hullAt_cfHistory hω.1 hω.2.2.1 hω.2.1,
      hω' t]
  have hstrip : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, stripExpl W' ζ' β α t ω = H ∩ (wallUnion β α ω ∪ K t ω) := by
    filter_upwards [hKeq] with ω hω t
    have hWH : wallUnion β α ω ⊆ H := inter_subset_right
    rw [stripExpl, ← hω t, inter_eq_right.2 (union_subset hWH (cfHull_subset_H W' ζ' t ω)), union_comm]
  have hver : ∀ (t : ℝ≥0) (ω : Ω), PocketStopWalls.wallsHullAt (wallUnion β α) K
      (fun _ => ((t : WithTop ℝ≥0) : ℝ≥0∞)) ω = H ∩ (wallUnion β α ω ∪ K t ω) := by
    intro t ω
    simp [PocketStopWalls.wallsHullAt]
  /- the inputs of the nested comparison -/
  have hlocE : ∀ t : ℝ≥0, WholeField.IsHistoryAvoidanceLocal (ℋ t) (stripExpl W' ζ' β α t)
      (WholeField.centredField h u₀) P := by
    intro t
    refine Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae ?_ (hlaw t)
    filter_upwards [hstrip] with ω hω
    rw [hver, hω t]
  have hAm : ∀ t : ℝ≥0, Measurable[mΩ, hittingSigma] (stripExpl W' ζ' β α t) := fun t =>
    measurable_union_hitting (measurable_cfHull hS.counterflow t) hΓm
  have hAc : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, stripExpl W' ζ' β α t ω ⊆ H ∧ IsOpen (H \ stripExpl W' ζ' β α t ω) := by
    intro t
    filter_upwards [(isLocalSet_cfHull hS hcumL hcumR u₀ hu₀.1 t).2.1, hΓloc.2.1] with ω h1 h2
    refine ⟨union_subset h1.1 h2.1, ?_⟩
    have e : H \ stripExpl W' ζ' β α t ω = (H \ cfHull W' ζ' t ω) ∩ (H \ wallUnion β α ω) := by
      ext z
      simp only [stripExpl, Set.mem_sdiff, mem_union, mem_inter_iff]
      tauto
    rw [e]
    exact h1.2.inter h2.2
  have hsub : ∀ r s : ℝ≥0, r ≤ s → ∀ᵐ ω ∂P, stripExpl W' ζ' β α r ω ⊆ stripExpl W' ζ' β α s ω := by
    intro r s hrs
    filter_upwards [hstrip] with ω hω
    rw [hω r, hω s]
    exact inter_subset_inter_right _ (union_subset_union_right _ (hKmono ω hrs))
  have hℋle : ∀ t, ℋ t ≤ mΩ := fun t => sup_le hXfm.comap_le (𝓕.le t)
  have hℋmono : ∀ r s : ℝ≥0, r ≤ s → ℋ r ≤ ℋ s := fun r s hrs => sup_le_sup_left (𝓕.mono hrs) _
  have hVm : ∀ t : ℝ≥0, Measurable[ℋ t, hittingSigma] fun ω => H ∩ (wallUnion β α ω ∪ K t ω) := by
    intro t
    refine @measurable_generateFrom Ω (Set ℂ) (ℋ t) _ _ ?_
    rintro _ ⟨U, hUo, hUH, rfl⟩
    have e : (fun ω => H ∩ (wallUnion β α ω ∪ K t ω)) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
        wallUnion β α ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} ∪ {ω | Disjoint (K t ω) U}ᶜ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
      constructor
      · rintro ⟨z, ⟨-, hz | hz⟩, hzU⟩
        · exact Or.inl ⟨z, hz, hzU⟩
        · exact Or.inr ⟨z, hz, hzU⟩
      · rintro (⟨z, hz, hzU⟩ | ⟨z, hz, hzU⟩)
        · exact ⟨z, ⟨hUH hzU, Or.inl hz⟩, hzU⟩
        · exact ⟨z, ⟨hUH hzU, Or.inr hz⟩, hzU⟩
    rw [e]
    exact ((le_sup_left : MeasurableSpace.comap (PocketStopWalls.fullHist η) inferInstance ≤ ℋ t) _
      (hΓX (measurableSet_hitting hUo hUH))).union ((le_sup_right : 𝓕 t ≤ ℋ t) _ (hKad t U hUo hUH)).compl
  have hrec : ∀ r s : ℝ≥0, r ≤ s → MeasurableSpace.comap (stripExpl W' ζ' β α r) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (stripExpl W' ζ' β α s) hittingSigma ⊔ ℋ s) P := by
    intro r s hrs
    rintro _ ⟨B, hB, rfl⟩
    refine ⟨(fun ω => H ∩ (wallUnion β α ω ∪ K r ω)) ⁻¹' B, ?_, ?_⟩
    · exact (le_sup_right : ℋ s ≤ _) _ (hℋmono r s hrs _ (hVm r hB))
    · filter_upwards [hstrip] with ω hω
      change (stripExpl W' ζ' β α r ω ∈ B) = (H ∩ (wallUnion β α ω ∪ K r ω) ∈ B)
      rw [hω r]
  exact ⟨ℋ, hℋle, hℋmono, hlocE, hrec, hAm, hAc, hsub⟩

/-- **The flat clock for the strip exploration** (Aux. lemma 37, p. 198): for the strip system's counterflow and two
complete walls `β`, `α` with Lemma 6.2's inputs, and any versions `g t` of the means of `stripExpl W′ ζ′ β α t`, the
flat clock `FlatClockStatement P univ (stripExpl W′ ζ′ β α) g` holds. -/
theorem flatClockStatement_stripExpl_of_walls {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β α : Ω → ℝ≥0 → ℂ}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ))
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hg : ∀ t : ℝ≥0, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t)) :
    FlatClockStatement P univ (stripExpl W' ζ' β α) g := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨ℋ, hℋle, hℋmono, hlocE, hrec, hAm, hAc, hsub⟩ := stripExpl_markedLaw hS hcumL hcumR hu₀ hβc hβ0 hβm
    hβdet hβloc hαc hα0 hαm hαdet hαloc htr
  refine flatClockStatement_of_nested (fun t _ => hAc t) (fun r _ s _ hrs => hsub r s hrs) ?_
  intro r _ s _ hrs φ
  exact IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq hX (hAm r) (hAm s) (hℋle r) (hℋle s) (hℋmono r s hrs)
    (hlocE r) (hlocE s) (hAc r) (hAc s) (hsub r s hrs) (hrec r s hrs) (hg r) (hg s) φ

/-- **The strip exploration has versions of its means at every time** (Lemma 3.6, (i) ⇒ (iii), from the marked law):
there is a family `g` with `IsLocalSetMean (stripExpl W′ ζ′ β α t) (centredField h u₀) P (g t)` for every `t`; and
`stripExpl W′ ζ′ β α t` is a local set of the centred field. -/
theorem exists_isLocalSetMean_stripExpl_of_walls {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {Es : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : StripSys.IsStripSystem κ b jumps P h W' ζ' Es)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ jumps → b y + a * chiC κ ≤ -sleLambda κ)
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ jumps → sleLambda κ ≤ b y + a * chiC κ)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β α : Ω → ℝ≥0 → ℂ}
    (hβc : ∀ ω, Continuous (β ω)) (hβ0 : ∀ ω, β ω 0 = 0) (hβm : ∀ t, Measurable fun ω => β ω t)
    (hβdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => β ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hβloc : Sec6.IsEntranceHistoryLocal β (WholeField.centredField h u₀) P)
    (hαc : ∀ ω, Continuous (α ω)) (hα0 : ∀ ω, α ω 0 = 0) (hαm : ∀ t, Measurable fun ω => α ω t)
    (hαdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => α ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω))
    (hαloc : Sec6.IsEntranceHistoryLocal α (WholeField.centredField h u₀) P)
    (htr : ∀ᵐ ω ∂P, Tendsto (β ω) atTop (cobounded ℂ) ∧ Tendsto (α ω) atTop (cobounded ℂ)) :
    (∀ t, IsLocalSet (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P) ∧
      ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
        ∀ t, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P (g t) := by
  have hX := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀
  obtain ⟨ℋ, -, -, hlocE, -, hAm, hAc, -⟩ := stripExpl_markedLaw hS hcumL hcumR hu₀ hβc hβ0 hβm
    hβdet hβloc hαc hα0 hαm hαdet hαloc htr
  have hav : ∀ t, IsAvoidanceLocal (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P := fun t =>
    (hlocE t).isAvoidanceLocal
  have hex : ∀ t, ∃ g, IsLocalSetMean (stripExpl W' ζ' β α t) (WholeField.centredField h u₀) P g := fun t =>
    ((isLocalSet_tfae hX (hAm t) (hAc t)).out 1 3).1 (hav t)
  exact ⟨fun t => ((isLocalSet_tfae hX (hAm t) (hAc t)).out 1 4).1 (hav t),
    fun t => (hex t).choose, fun t => (hex t).choose_spec⟩

end Strip

end InteractingSLE.Sec7.FlatClockProof
