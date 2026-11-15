/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaMeans
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaWalkPhysical
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaReferenceLaw
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaUnionSet
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaHeights
import InteractingSLE.Spec.Supplement.GW2ConeData

/-! # GW4: original-measure reference heights for the transported union means -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull logDerivFwd)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField WalkLaw GW4Rel GW4Traverse Sec5.GlueCond Sec5.Cond44Ref
open Sec7.StripSysField MartChar.RealFlow Sec7.Aux119Heights

/-- The actual original union means have the exposed counterflow heights on
one event, simultaneously for all components and all protected references.
The statement includes physical landings on the real boundary. -/
theorem ae_exposed_original_union_heights
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {D : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hD : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (D spec))
    (hreg : ∀ spec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (D spec))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b J u₀)
    {A : ℝ≥0 → Ω → Set ℂ} {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hAm : ∀ t, Measurable[mΩ, hittingSigma] (A t))
    (hAc : ∀ t ω, A t ω ⊆ H ∧ IsOpen (H \ A t ω))
    (hA : ∀ t, ∀ᵐ ω ∂P, A t ω = relClosureH
      (walkUnionSet κ b J D ω ∪ cfHullQ t (cfHistory W ζ ω)))
    (hM : ∀ t, IsLocalSetMean (A t) (centredField h u₀) P
      (fun ω => M t ω - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)) :
    ∀ᵐ ω ∂P, ∀ F : Frame, F.IsOk → F.IsPathOk (fun r => W r ω) →
      Disjoint (walkUnionSet κ b J D ω) F.C →
      ∀ R : ℝ≥0 → ℝ, Continuous R → R 0 = 0 → ∀ V : ℝ≥0∞,
      (∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
        ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt (fun r => W r ω) t) →
      ∀ t q : ℝ≥0, F.ent (fun r => W r ω) ≤ t →
        (t : ℝ≥0∞) < F.exit (fun r => W r ω) → 0 < q → (q : ℝ≥0∞) < V →
        (q : ℝ) = F.rcap (fun r => W r ω) t →
      ∃ S : Set ℂ, S.Finite ∧ ∀ ξ ∈ Ioo
        (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
        (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q), ξ ≠ 0 → ∀ p : ℂ,
        Tendsto (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1
          (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ∉ S →
        ∃ s : ℚ, (F.ent (fun r => W r ω) : ℝ) < s ∧ (s : ℝ) < t ∧
          0 < F.rcap (fun r => W r ω) (s : ℝ).toNNReal ∧
          F.rcap (fun r => W r ω) (s : ℝ).toNNReal < F.rcap (fun r => W r ω) t ∧
          ∃ x r : ℝ, x ∈ Ioo
            (-rightImg (fun u : ℝ => -R u.toNNReal) 0
              (F.rcap (fun u => W u ω) (s : ℝ).toNNReal) -
              R (F.rcap (fun u => W u ω) (s : ℝ).toNNReal).toNNReal)
            (rightImg (fun u : ℝ => R u.toNNReal) 0
              (F.rcap (fun u => W u ω) (s : ℝ).toNNReal) -
              R (F.rcap (fun u => W u ω) (s : ℝ).toNNReal).toNNReal) ∧ 0 < r ∧
          (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
            (F.rcap (fun u => W u ω) (s : ℝ).toNNReal)).2.1 '' (H ∩ Metric.ball (x : ℂ) r) ⊆
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).dom : Set ℂ) ∧
          Tendsto (fun y => (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
            (F.rcap (fun u => W u ω) (s : ℝ).toNNReal)).1
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.2
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y) -
            (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
              (F.rcap (fun u => W u ω) (s : ℝ).toNNReal)).2.2
              ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
          Tendsto (fun y => harmRep (invField κ (M (s : ℝ).toNNReal ω))
              (WangWu.negInv '' (H \ A (s : ℝ).toNNReal ω))
              ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y) + chiC (16 / κ) *
              (logDerivFwd (fun r : ℝ => W r.toNNReal ω) (s : ℝ).toNNReal
                ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y)).im)
            (𝓝[H] (ξ : ℂ))
            (𝓝 (if ξ < 0 then -(Real.pi / Real.sqrt (16 / κ)) else Real.pi / Real.sqrt (16 / κ))) := by
  obtain ⟨h', hT, hfl⟩ := GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨h'', 𝓕, VL, VR, noise, hTr, hC⟩ := hfl
  have he : h'' = h' := funext fun ω =>
    GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (hTr ω)
  subst h''
  have hLI := Chart.locallyIntegrableOn_of_continuousOn
    CLoc.continuousOn_lift_inv_infinitySourceChart
  have he : h' = fun ω => invField κ (h ω) := by
    funext ω
    exact ((hT ω).eq_chartTransport Chart.isConformal_infinitySourceChart hLI).trans
      ((isChartTransport_invField hκ (h ω)).eq_chartTransport
        Chart.isConformal_infinitySourceChart hLI).symm
  subst h'
  obtain ⟨u₁, hu₁⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
    (flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps J) 0 0)
    (flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps J) 0 0)
    (flowLineXL (counterflowData κ b) (counterflowJumps J) 0)
    (flowLineXR (counterflowData κ b) (counterflowJumps J) 0)
  have hTr0 : ∀ ω, IsTranslateAddConst 0 0 (invField κ (h ω)) (invField κ (h ω)) := by
    intro ω
    simpa only [zero_mul] using isTranslateAddConst_zero_self (invField κ (h ω)) 0
  obtain ⟨E, hEc, hEm, hEeq, hEd, hEl⟩ := exists_physical_walk_union_version
    h12 h13 hκ hκ4 hb hh (fun ω => isChartTransport_invField hκ (h ω)) hTr0
    hu₀ hu₁.1 (WholeField.isZeroBoundaryGFF_centredField hC hu₁) hD hreg
  let K : ℚ → Ω → Set ℂ := fun s ω => hullAt (s : ℝ).toNNReal (cfHistory W ζ ω)
  have hKm : ∀ s, Measurable[mΩ, hittingSigma] (K s) := fun s =>
    (measurable_hullAt _).comp
      (measurable_cfHistory (isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf))
  have hKeq : ∀ s : ℚ, ∀ᵐ ω ∂P,
      K s ω = fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ).toNNReal := by
    intro s
    filter_upwards [hζ, hC.1.2.2.2.2] with ω hz hp
    have hw : Continuous (W · ω) := continuousOn_univ.1
      (hp.2.2.2.1.mono fun t _ => hz ▸ ENNReal.coe_lt_top)
    exact hullAt_cfHistory hz hp.1 hw (s : ℝ).toNNReal
  have hAE (s : ℚ) := ae_physical_union_eq hEc hEeq (s : ℝ).toNNReal (hA _)
  obtain ⟨G, hG, hGM⟩ := exists_physical_union_reference_means hκ hC hu₀.1 hu₁ hC.2.2.2.1 hζ
    hEm hEd hEl hKm hKeq (fun s => hAm (s : ℝ).toNNReal)
    (fun s => hAc (s : ℝ).toNNReal) hAE (fun s => hM (s : ℝ).toNNReal)
  have hHeight := ae_exposed_reference_heights (by positivity : 0 < 16 / κ)
    (GW3Word.flowLineXL_nonpos _ _) (GW3Word.flowLineXR_nonneg _ _) hC hu₁ hC.2.2.2.1 hζ
    hEm hEd hEl hKm hKeq hG
  filter_upwards [hHeight, hGM, hEeq, ae_all_iff.2 hKeq] with ω hHeightω hGMω hEω hKω
    F hF hw hDisj R hR hR0 V hVer t q htEnt htExit hq hqV hqt
  have hDE : Disjoint (relDom F.C) (E ω) := by
    rw [hEω]
    apply Set.disjoint_left.2
    rintro z hz ⟨x, hx, rfl⟩
    have hxC : x ∈ F.C := by
      change WangWu.negInv (WangWu.negInv x) ∈ F.C at hz
      simpa only [WangWu.negInv_negInv] using hz
    exact Set.disjoint_left.1 hDisj hx hxC
  obtain ⟨S, hS, hCover⟩ := hHeightω F hF hw hDE R hR hR0 V hVer t q htEnt htExit hq hqV hqt
  refine ⟨S, hS, fun ξ hξ hξ0 p hp hpS => ?_⟩
  obtain ⟨s, hsEnt, hst, hs0, hsq, x, r, hx, hr, hCol, hTr, hLift, hLim⟩ :=
    hCover ξ hξ hξ0 p hp hpS
  refine ⟨s, hsEnt, hst, hs0, hsq, x, r, hx, hr, hCol, hTr, hLift, ?_⟩
  have hCo := Frame.isOpen_C hF hw
  have hCH := CLoc.subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans
      Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun u : ℝ => R u.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun u : ℝ => R u.toNNReal) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hR0
  obtain ⟨v, hv⟩ := hVer q hqV
  have hDom := componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
    (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hv htEnt htExit hqt)
  have hCur := hBase.loewner hRR hRR0 q.coe_nonneg
  refine hLim.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  have hz : (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y ∈
      relDom F.C ∩ (H \ fwdHull (fun u : ℝ => W u.toNNReal ω) t) := by
    rw [← hDom]
    exact hCur.inv_mem_dom hy
  have hzU : (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y ∈
      H \ (E ω ∪ K s ω) := by
    refine ⟨hz.2.1, fun hm => ?_⟩
    rcases hm with hm | hm
    · exact Set.disjoint_left.1 hDE hz.1 hm
    · rw [hKω s] at hm
      exact hz.2.2 (QuantumZipper.fwdHull_mono.1
        (show ((s : ℝ).toNNReal : ℝ) ≤ (t : ℝ) from
          NNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hst.le)) hm)
  rw [(hGMω s).2 _ hzU]

end InteractingSLE.Theorem14.GW4Fix
