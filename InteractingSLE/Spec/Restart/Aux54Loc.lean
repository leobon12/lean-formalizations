/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Aux54Post

/-!
# Aux. lemma 54 for general words, part 12: locality on the record extension, and Aux. lemma 54

Packet PROVE-AUX54. The member identities at rational times (`DomainMarkov.HasRatMembers`) for the centred original
field on a record extension: for `r < s` and a finite family `F` of rational balls, the measurable version of the safe
event is read from the reference (`exists_safe_version`), every event `D` of the usual augmentation at `r` is split at
the reference's rule stop, and

* before the stop the identity is `setIntegral_lapTest_preE` (the stopped coupling's coded identities);
* after the stop it is `setIntegral_lapTest_postE` (the record extension, the marked locality and the reference).

`DomainMarkov.isLocalSet_hull_of_members` then gives **`extLocalityStatement`**, the named input of
`stoppedHullExtendRStatement_of_locality`, and so **`stoppedHullExtendRStatement`**: Aux. lemma 54 for general words in
its corrected form, for every `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal RealInnerProductSpace

universe u

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4 StoppedExtendWF Coupling DomainMarkov LQGMetric.MarkovZB LocalSets
open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {nL nR : ℕ}

/-! ### A measurable version of the safe event -/

/-- **The safe event of rational balls at `s` has a version in the driving filtration at `s`** (the safe sets on a
measurable event of full measure on which the paths are continuous). -/
theorem exists_safe_version {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    (hX₀ : IsMeasurableKilledDriving W₀ VL₀ VR₀ ζ₀)
    (hpath : ∀ᵐ ω ∂P₀, ContinuousOn (fun t => W₀ t ω) {t | (t : ℝ≥0∞) < ζ₀ ω} ∧ W₀ 0 ω = 0)
    {F : Finset (ℚ × ℚ × ℚ)} (hFH : ballsK F ⊆ H) (s : ℝ≥0) :
    ∃ S₀ : Set Ω₀, MeasurableSet[drivingFiltration P₀ hX₀ s] S₀ ∧
      S₀ =ᵐ[P₀] {ω | (s : ℝ≥0∞) < ζ₀ ω ∧ Disjoint (ballsK F) (fwdHull (fun r : ℝ => W₀ r.toNNReal ω) (s : ℝ))} := by
  classical
  set Nbad : Set Ω₀ := {ω | ¬ (ContinuousOn (fun t => W₀ t ω) {t | (t : ℝ≥0∞) < ζ₀ ω} ∧ W₀ 0 ω = 0)} with hNbad
  have hN0 : P₀ Nbad = 0 := ae_iff.1 hpath
  set Gd : Set Ω₀ := (toMeasurable P₀ Nbad)ᶜ with hGd
  have hGdm : MeasurableSet Gd := (measurableSet_toMeasurable P₀ Nbad).compl
  have hGd0 : MeasurableSet[drivingFiltration P₀ hX₀ 0] Gd :=
    (Ito.measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX₀)
      (measurableSet_toMeasurable P₀ Nbad) (by rw [measure_toMeasurable]; exact hN0) 0).compl
  have hgood : ∀ ω ∈ Gd, ContinuousOn (fun t => W₀ t ω) {t | (t : ℝ≥0∞) < ζ₀ ω} ∧ W₀ 0 ω = 0 := by
    intro ω hω
    by_contra hb
    exact hω (subset_toMeasurable P₀ Nbad hb)
  have hWa : AdaptedBefore (drivingFiltration P₀ hX₀) ζ₀ W₀ :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ P₀) (Coupling.adaptedBefore_killedDriving_W hX₀)
  refine ⟨safeU W₀ ζ₀ Gd (indK F) s, MeasurableSet.iUnion fun m => Coupling.measurableSet_safeSet hWa
    (fun ω hω => (hgood ω hω).1) hGd0 (by rw [tsupport_indK]; exact hFH) (by positivity) s, ?_⟩
  have hGae : ∀ᵐ ω ∂P₀, ω ∈ Gd := by
    rw [ae_iff]
    have e : {a | ¬ a ∈ Gd} = toMeasurable P₀ Nbad := by
      ext ω; simp [hGd]
    rw [e, measure_toMeasurable]
    exact hN0
  filter_upwards [hGae] with ω hω
  obtain ⟨hc, hw0⟩ := hgood ω hω
  have e : ω ∈ safeU W₀ ζ₀ Gd (indK F) s ↔ ω ∈ safeU W₀ ζ₀ univ (indK F) s := by
    simp only [safeU, Coupling.safeSet, mem_iUnion, mem_ofPred_eq, hω, mem_univ, true_and]
  exact propext (e.trans (mem_safeU_indK_iff hc hw0 hFH s))

/-! ### Locality on the record extension -/

/-- **Locality on the record extension** (the named input of `stoppedHullExtendRStatement_of_locality`), for every
`κ > 0`. -/
theorem extLocalityStatement {κ : ℝ} (hκ : 0 < κ) : ExtLocalityStatement.{u} κ := by
  classical
  intro nL nR xL xR ρL ρR hF R hRm hRg Ω mΩ P _ 𝓕 W VL VR B V h hSC hV hreg Ω₀ mΩ₀ _ P₀ _ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀
    h₀ href E _ hE hXE τ hτ hτζ
  have hE' := hE
  obtain ⟨hfst, hsnd, -, -, -⟩ := hE'
  have hC₀ := href.isOptionalHullCoupling hκ
  have hEv₀ := href.1
  have hX₀ := IsIntegratedSLEEvolution.isMeasurableKilledDriving hEv₀
  obtain ⟨hEv, hcont, hhm, hgff, hX, -⟩ := id hSC
  -- the paths of the reference
  have hpath₀ : ∀ᵐ ω₀ ∂P₀, ContinuousOn (dState W₀ VL₀ VR₀ ω₀) {t | (t : ℝ≥0∞) < ζ₀ ω₀} ∧
      dState W₀ VL₀ VR₀ ω₀ 0 = initVal xL xR := by
    filter_upwards [hEv₀.isSLEEvolutionUpTo.ae_path] with ω₀ hp
    refine ⟨continuousOn_state_of_isSLEPathUpTo hp, ?_⟩
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  have hpathE : ∀ᵐ p ∂E, ContinuousOn (fun t => W₀ t p.2) {t | (t : ℝ≥0∞) < ζ₀ p.2} ∧ W₀ 0 p.2 = 0 := by
    have h1 : ∀ᵐ ω₀ ∂(E.map Prod.snd), ContinuousOn (fun t => W₀ t ω₀) {t | (t : ℝ≥0∞) < ζ₀ ω₀} ∧
        W₀ 0 ω₀ = 0 := by
      rw [hsnd]
      filter_upwards [hEv₀.isSLEEvolutionUpTo.ae_path] with ω₀ hp
      exact ⟨hp.continuousOn_w, hp.w_zero⟩
    exact ae_of_ae_map measurable_snd.aemeasurable h1
  -- an inadmissible seed: the reference has no life, so there is no stopping time before its lifetime
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hζ0 : ∀ᵐ ω₀ ∂P₀, ζ₀ ω₀ = 0 := by
      filter_upwards [hEv₀.isSLEEvolutionUpTo.ae_path, ae_not_threshold_of_evolution hEv₀] with ω₀ hp hnt
      by_contra hne
      refine hnt 0 (pos_iff_ne_zero.2 hne) ?_
      rw [hp.w_zero, show (fun i => VL₀ i 0 ω₀) = xL from funext hp.vL_zero,
        show (fun j => VR₀ j 0 ω₀) = xR from funext hp.vR_zero]
      exact hseed
    have hζ0E : ∀ᵐ p ∂E, ζ₀ p.2 = 0 := by
      rw [← hsnd] at hζ0
      exact ae_of_ae_map measurable_snd.aemeasurable hζ0
    have hfalse : ∀ᵐ p ∂E, False := by
      filter_upwards [hτζ, hζ0E] with p h1 h2
      rw [h2] at h1
      exact ENNReal.not_lt_zero (show ((τ p : WithTop ℝ≥0) : ℝ≥0∞) < 0 from h1)
    have := measure_univ (μ := E)
    rw [ae_iff] at hfalse
    simp only [not_false_eq_true, ofPred_true] at hfalse
    rw [hfalse] at this
    exact zero_ne_one this
  -- the centred field on the extension
  set u₀ : ℂ → ℝ := Impl.forceExt κ (Ito.weightWord ρL ρR) xL xR with hu₀def
  have hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ :=
    Impl.isBoundedHarmonicExtension_forceExt κ (Ito.weightWord ρL ρR) xL xR
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  set T₀ : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens u₀ with hT₀def
  have hT₀ : IsHarmonicDistOn T₀ H := Coupling.isHarmonicDistOn_smoothDist_of hu₀
  have hgffE : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ (p : Ω × Ω₀) => h p.1 φ - ∫ z, u₀ z * φ z) E := by
    have h1 := hgff u₀ hu₀
    rw [← hfst] at h1
    exact Restart.isZBGFFProcess_comp measurable_fst h1
  have hXgff : IsZeroBoundaryGFF upperHalfPlaneOpens (fun p : Ω × Ω₀ => h p.1 - T₀) E :=
    Coupling.isZeroBoundaryGFF_sub_smoothDist (hhm.comp measurable_fst) hu₀c hgffE
  have hXm : Measurable fun p : Ω × Ω₀ => h p.1 - T₀ := (WholeField.measurable_sub_dist T₀).comp
    (hhm.comp measurable_fst)
  -- the reference's rule stop and the agreement before it
  set V₀ : Ω₀ → ℝ≥0∞ := ruleStop R W₀ VL₀ VR₀ ζ₀ with hV₀def
  have hV₀ζ : ∀ ω, V₀ ω ≤ ζ₀ ω := ruleStop_le R
  have hV₀ : IsStoppingTime (drivingFiltration P₀ hX₀) fun ω => (V₀ ω : WithTop ℝ≥0) :=
    isStoppingTime_ruleStop (P := P₀) hX₀ hRm hRg (hpath₀.mono fun _ h' => h'.1)
  have hc : ∀ᵐ ω ∂P, ContinuousOn (dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} ∧
      (∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (dState W VL VR ω) (Iic T)) ∧
      dState W VL VR ω 0 = initVal xL xR := by
    filter_upwards [hEv.ae_path, hcont] with ω hp hcω
    refine ⟨continuousOn_state_of_isSLEPathUpTo hp, hcω, ?_⟩
    simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
    exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
  have hag0 := IsRecExt.ae_agree hE hc hpath₀ hV₀ζ
  have hag : ∀ᵐ p ∂E, V p.1 = V₀ p.2 ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < V p.1 →
      dState W VL VR p.1 t = dState W₀ VL₀ VR₀ p.2 t := by
    filter_upwards [hag0] with p ⟨hVV, hst⟩
    refine ⟨hVV, fun t ht => hst t ht.le ?_⟩
    rw [hVV] at ht
    exact lt_of_lt_of_le ht (hV₀ζ p.2)
  -- the member identities
  have hmem : HasRatMembers E (killedDrivingFiltration hXE) (fun t (p : Ω × Ω₀) => W₀ t p.2) (fun p => ζ₀ p.2)
      (fun p => h p.1 - T₀) := by
    intro r s hrs F hFH
    have hpath₀' : ∀ᵐ ω ∂P₀, ContinuousOn (fun t => W₀ t ω) {t | (t : ℝ≥0∞) < ζ₀ ω} ∧ W₀ 0 ω = 0 := by
      filter_upwards [hEv₀.isSLEEvolutionUpTo.ae_path] with ω₀ hp
      exact ⟨hp.continuousOn_w, hp.w_zero⟩
    obtain ⟨S₀, hS₀m, hS₀⟩ := exists_safe_version hX₀ hpath₀' hFH (s : ℝ≥0)
    have hS₀m' : MeasurableSet S₀ := (drivingFiltration P₀ hX₀).le _ _ hS₀m
    have hSE : (Prod.snd ⁻¹' S₀ : Set (Ω × Ω₀)) =ᵐ[E]
        {p : Ω × Ω₀ | ((s : ℝ≥0) : ℝ≥0∞) < ζ₀ p.2 ∧
          Disjoint (ballsK F) (fwdHull (fun r : ℝ => W₀ r.toNNReal p.2) ((s : ℝ≥0) : ℝ))} := by
      have h1 : ∀ᵐ ω ∂(E.map Prod.snd), (ω ∈ S₀) = (ω ∈ {ω | ((s : ℝ≥0) : ℝ≥0∞) < ζ₀ ω ∧
          Disjoint (ballsK F) (fwdHull (fun r : ℝ => W₀ r.toNNReal ω) ((s : ℝ≥0) : ℝ))}) := by
        rw [hsnd]; exact hS₀
      exact ae_of_ae_map measurable_snd.aemeasurable h1
    refine ⟨Prod.snd ⁻¹' S₀, measurable_snd hS₀m', hSE, fun D hD => ?_⟩
    have hrs' : ((r : ℝ≥0)) < ((s : ℝ≥0)) := by exact_mod_cast hrs
    have hDn : MeasurableSet[Ito.nullAugmented (killedDrivingFiltration hXE) E (s : ℝ≥0)] D :=
      usualAugmentation_le_nullAugmented (killedDrivingFiltration hXE) hrs' _ hD
    have hDm : MeasurableSet D := (Ito.nullAugmented (killedDrivingFiltration hXE) E).le _ _ hDn
    intro f Ξ
    rw [integral_map hXm.aemeasurable
        (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable,
      integral_map hXm.aemeasurable (GFF.measurable_exp_I_mul (measurable_distOn_apply _)).aestronglyMeasurable]
    by_cases hU0 : ((ballsOpen F : TopologicalSpace.Opens ℂ) : Set ℂ) = ∅
    · exact projIdentity_of_empty _ (fun p : Ω × Ω₀ => h p.1 - T₀) hU0 f Ξ
    have hUne : ((ballsOpen F : TopologicalSpace.Opens ℂ) : Set ℂ).Nonempty := nonempty_iff_ne_empty.2 hU0
    have hUC : ((ballsOpen F : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ ballsK F := ballsU_subset_ballsK F
    have hCne : (ballsK F).Nonempty := hUne.mono hUC
    -- split at the reference's stop
    have hV₀m : Measurable V₀ :=
      (hRm.comp (measurable_killedHistory hX₀)).min (measurable_lifetime hX₀)
    set pre : Set (Ω × Ω₀) := {p | ((s : ℝ≥0) : ℝ≥0∞) < V₀ p.2} with hpre
    have hprem : MeasurableSet pre := measurableSet_lt measurable_const (hV₀m.comp measurable_snd)
    have hint : ∀ χ : TestOn upperHalfPlaneOpens,
        IntegrableOn (fun p : Ω × Ω₀ => Complex.exp (Complex.I * ((h p.1 - T₀) χ : ℂ))) (D ∩ Prod.snd ⁻¹' S₀) E :=
      fun χ => (GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hXm)).integrableOn
    -- before the stop
    have hpreId := setIntegral_lapTest_preE hSC hT₀ hX₀ hfst hXE hV₀ζ hag hDn (isCompact_ballsK F) hFH hCne
      hUC hSE f Ξ
    -- after the stop
    obtain ⟨A₀, hA₀, hDA₀⟩ := exists_snd_of_nullAugmented hX₀ hXE hDn
    set D₀ : Set Ω₀ := A₀ ∩ S₀ ∩ {ω | (V₀ ω : WithTop ℝ≥0) ≤ (((s : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)} with hD₀def
    have hD₀ : D₀ ∈ refSafeGens P₀ hX₀ (ballsK F) (s : ℝ≥0) := by
      refine ⟨((Ito.le_usualAugmentation _ P₀ _ _ hA₀).inter hS₀m).inter (hV₀ _), ?_⟩
      filter_upwards [hS₀] with ω hω hD
      exact (Iff.of_eq hω).1 hD.1.2
    have hD₀V : ∀ ω ∈ D₀, V₀ ω ≤ ((s : ℝ≥0) : ℝ≥0∞) := fun ω hω => hω.2
    have hpostSet : ((D ∩ Prod.snd ⁻¹' S₀) \ pre : Set (Ω × Ω₀)) =ᵐ[E] Prod.snd ⁻¹' D₀ := by
      filter_upwards [hDA₀] with p hp
      have hp' : p ∈ D ↔ p.2 ∈ A₀ := Iff.of_eq hp
      apply propext
      simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage, hpre, hD₀def, mem_ofPred_eq, not_lt]
      rw [hp']
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    have hpostId := setIntegral_lapTest_postE hSC hseed hreg href hX₀ hV₀ hV₀ζ hE hu₀ (isCompact_ballsK F) hFH
      hUC hUne hD₀ hD₀V f Ξ
    rw [← setIntegral_congr_set hpostSet, ← setIntegral_congr_set hpostSet] at hpostId
    rw [← integral_inter_add_sdiff hprem (hint _), ← integral_inter_add_sdiff hprem (hint _), mul_add]
    exact congrArg₂ (· + ·) hpreId hpostId
  -- locality
  have hloc := isLocalSet_hull_of_members hXgff (Coupling.adaptedBefore_killedDriving_W hXE) hpathE hmem hτ hτζ
  have h2 := Coupling.IsLocalSet.add_dist hloc hT₀
  have e : (fun p : Ω × Ω₀ => h p.1 - T₀ + T₀) = fun p => h p.1 := funext fun p => sub_add_cancel _ _
  rw [e] at h2
  exact h2

/-- **Aux. lemma 54 for general words** (specification p. 246), in its corrected form: Galmarino rule and regularity
at the stop (`StoppedHullExtendRStatement`), for every `κ > 0`. -/
theorem stoppedHullExtendRStatement {κ : ℝ} (hκ : 0 < κ) : StoppedHullExtendRStatement.{u} κ :=
  stoppedHullExtendRStatement_of_locality hκ (extLocalityStatement hκ)

/-- **A driver frozen after the stop is regular at the stop** (the consumers' stopped drivers `W_{·∧V}`): the
regularity hypothesis of `StoppedHullExtendRStatement` holds when, almost surely, `W` is constant after a finite
stop. -/
theorem isRegularStop_of_frozen {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hSC : StoppedExtend.IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h)
    (hfrz : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ∀ t : ℝ≥0, T ≤ t → W t ω = W T ω) :
    IsRegularStop ρL ρR P W VL VR V := by
  filter_upwards [hSC.2.1, hfrz] with ω hc hf T hT _
  refine ⟨T + 1, lt_add_of_pos_right T one_pos, ?_⟩
  have hcT : ContinuousOn (fun t => W t ω) (Iic T) := continuous_fst.comp_continuousOn (hc T hT)
  have hmin : ContinuousOn (fun t : ℝ≥0 => W (min t T) ω) (Iic (T + 1)) :=
    hcT.comp_continuous (continuous_id.min continuous_const) (fun t => min_le_right t T) |>.continuousOn
  refine hmin.congr fun t _ => ?_
  rcases le_total t T with htT | htT
  · simp only [min_eq_left htT]
  · simp only [min_eq_right htT]
    exact hf T hT t htT

end Aux54

end Restart

end InteractingSLE
