/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMuAmbient
import InteractingSLE.Spec.Supplement.GW4SafeRMuExposed
import InteractingSLE.Spec.Supplement.GW4SafeREtaReferences
import InteractingSLE.Spec.Supplement.GW4SafeREpsilonMean
import InteractingSLE.Spec.Supplement.GW4SafeRBoundaryLimits
import InteractingSLE.Spec.Supplement.GW4MartWire

/-! # GW4: global conditional-component representation and its announced form -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMapInv logDerivFwd)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField WalkLaw GW4Traverse GW4Rel Sec5.GlueCond Sec5.Cond44Ref
open Restart Sec7.StripSysField Supp8.RelSafe Sec7.Aux119Heights Sec7.PhaseSel

/-- GW4's actual component representation. All original union laws,
reference heights and the common lattice phase are supplied by their
landed constructions, before selecting a realized reference. -/
theorem gw4ComponentRepDStatement
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    Mart.GW4ComponentRepDStatement.{u} := by
  intro κ hκ hκ4 b J hb Ω mΩ _ P _ h hh W ζ hcf hζ D hD hreg wR wL
  obtain ⟨uOrig, A, M, huOrig, hOrigMean, hAc, hAm, hA, hMh, hTransport⟩ :=
    exists_component_union_mean_transport_with_mean h12 h13
      (fun s : ℚ => (s : ℝ).toNNReal) hκ hκ4 hb hh hcf hζ hD hreg
  have hpR := GW1X.isBoundaryContinuedProgram_walkR b J
  have hpL := GW1X.isBoundaryContinuedProgram_walkL b J
  have hjm : jointPast κ b J D ≤ mΩ := sup_le ((hD _ hpR).2.1 _) ((hD _ hpL).2.1 _)
  have hRw := GW4Reg.ae_ae_physSet_eq (hreg _ hpR) hjm le_sup_left
  have hLw := GW4Reg.ae_ae_physSet_eq (hreg _ hpL) hjm le_sup_right
  have hAν := ae_all_iff.2 fun s : ℚ => KernelTower.ae_ae_condExpKernel_of_ae hjm (hA (s : ℝ).toNNReal)
  have hMν := ae_all_iff.2 fun s : ℚ => KernelTower.ae_ae_condExpKernel_of_ae hjm (hMh (s : ℝ).toNNReal)
  have hζν := KernelTower.ae_ae_condExpKernel_of_ae hjm hζ
  have hHeightν := KernelTower.ae_ae_condExpKernel_of_ae hjm
    (ae_exposed_original_union_heights h12 h13 hκ hκ4 hb hh hcf hζ hD hreg
      huOrig hAm hAc hA hOrigMean)
  filter_upwards [hTransport, hRw, hLw, hAν, hMν, hζν, hHeightν]
    with ω₀ hTransω hRω hLω hAω hMω hζω hHeightω
  intro Rwalk Lwalk ν C hCm c hC bC JC hch htr hpc _ hgff c₀ _ hc₀J hc₀
    F Wd GT hF hFC hFc hGT hWm hGTm hGTae hVW R V hver u ℋ B hloc
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hX : IsGFFWithBoundaryData ν (fun ω => invField κ (hC ω)) c₀.fn c₀.jumps :=
    isGFFWithBoundaryData_invField_word hκ hpc hgff hc₀J hc₀
  have hS : ∀ᵐ ω ∂ν, walkUnionSet κ b J D ω = (Rwalk ∪ Lwalk) ∩ H := by
    filter_upwards [hRω, hLω] with ω h1 h2
    show walkSet κ b J wR (D wR) ω ∪ walkSet κ b J wL (D wL) ω = (Rwalk ∪ Lwalk) ∩ H
    simp only [walkSet]
    rw [h1, h2]
    exact (union_inter_distrib_right _ _ _).symm
  subst C
  subst c
  have hSC : ∀ᵐ ω ∂ν, Disjoint (walkUnionSet κ b J D ω) F.C := hS.mono fun ω hω => by
    rw [hω]
    exact (CLoc.disjoint_of_mem_betweenComponents hCm).mono_left inter_subset_left
  have hSet (s : ℚ) := ae_chartSet_eq_safeHull hF hGT hGTae hVW hζω hver
    (s : ℝ).toNNReal (hAω s) hSC
  have hExists : ∀ s : ℚ, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (B (s : ℝ).toNNReal) (centredField (fun ω => invField κ (hC ω)) u) ν g := by
    intro s
    obtain ⟨g, hg, -⟩ := exists_component_initial_reference hX hloc
      hver.1.1.2.2.1 hver.1.1.2.1 (s : ℝ).toNNReal
    exact ⟨g, hg⟩
  choose G hG using hExists
  obtain ⟨ω₁, hω₁⟩ := hGTae.exists
  let hc := GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 (Frame.isOpen_C hF (hGT ω₁ hω₁))
    (GW4Traverse.subset_H_of_mem_betweenComponents hF.2.1)
  have hMeans (s : ℚ) : ∀ᵐ ω ∂ν, lineClock F Wd GT V (s : ℝ).toNNReal ω < V ω →
      G s ω = invField κ (Chart.chartTransport hc 1 0 (chiC κ) (M (s : ℝ).toNNReal ω)) -
        smoothDist upperHalfPlaneOpens u := by
    obtain ⟨hc', hMean⟩ := hTransω F.C hCm F.c hC hch htr c₀ hX F Wd GT hF rfl rfl hGT
      hWm hGTm hGTae hVW R V hver u ℋ B hloc s (G s) (hG s)
    exact hMean
  have hBsets (s : ℚ) : ∀ᵐ ω ∂ν, lineClock F Wd GT V (s : ℝ).toNNReal ω < V ω →
      H \ B (s : ℝ).toNNReal ω = H \ CLoc.chartSet F.c (A (s : ℝ).toNNReal ω) := by
    filter_upwards [hSet s, hloc.2.2.2.2.2.2 (s : ℝ).toNNReal] with ω hSetω hShape hLive
    rw [hSetω hLive, H_diff_safeHull_of_lt F Wd GT R V (s : ℝ).toNNReal ω hLive]
    exact hShape hLive
  obtain ⟨d, hdc, hPhase⟩ := exists_component_lattice_phase hF hGT hGTae hver (16 / κ)
  refine ⟨d, Eventually.of_forall (fun ω => ?_), ?_⟩
  · obtain ⟨j, hj⟩ := hdc ω
    exact ⟨j * phaseStep (16 / κ), ⟨j, rfl⟩, fun q _ _ => hj q⟩
  · apply componentPhaseRepresentation_of_boundaryLimits (by positivity) hF hX hloc hGT hGTae hver
    intro t g hg
    have hAllGerm := ae_all_iff.2 fun s : {s : ℚ // (s : ℝ).toNNReal ≤ t} =>
      ae_component_reference_zero_germ_of_mean hF hX hGT hGTm hGTae hver hloc s.property
        (G s.val) g (hG s.val) hg
    have hAllShape := ae_all_iff.2 fun s : ℚ => hloc.2.2.2.2.2.2 (s : ℝ).toNNReal
    have hOut := ae_component_boundary_limits_outside_seed_interval
      (by positivity : 0 < 16 / κ) hX hloc hver.1.1.2.2.1 hver.1.1.2.1 d t g hg
    filter_upwards [hAllGerm, ae_all_iff.2 hMeans, ae_all_iff.2 hBsets, hAllShape,
      ae_all_iff.2 hMω, hHeightω, hSC, hVW, hGTae, hver.1.1.2.2.2.2, hPhase, hOut]
      with ω hGermω hMeanω hBsetω hShapeω hMhω hHeight hDisj hWω hω hVer hPhaseω hOutω hLive
    let q := (lineClock F Wd GT V t ω).toNNReal
    have hRc := hver.1.1.2.1 ω
    have hR0 := hver.1.1.2.2.1 ω
    have hw := hGT ω hω
    have hClock := component_lineClock_eq_rcap hF hGT hω hRc hR0 hVer hLive
    have hOldLive : ∀ s : ℚ, (s : ℝ).toNNReal ≤ t →
        lineClock F Wd GT V (s : ℝ).toNNReal ω < V ω := fun s hs =>
      (Frame.monotone_min_physClockG hF hGT (V := V) ω hs).trans_lt hLive
    have hIn : ∃ T : Set ℂ, T.Finite ∧ ∀ ξ : ℝ,
        ξ ∉ componentLineJumps (16 / κ) c₀ F (fun ω => invField κ (hC ω)) Wd GT R V t ω →
        ξ ∈ Ioo
          (componentVL (16 / κ) c₀ (fun ω => invField κ (hC ω)) R V (componentSeedL (16 / κ) c₀) q ω - R q ω)
          (componentVR (16 / κ) c₀ (fun ω => invField κ (hC ω)) R V (componentSeedR (16 / κ) c₀) q ω - R q ω) →
        extendFrom H (componentLineChart F Wd GT R V t ω).2.1 (ξ : ℂ) ∉ T →
        Tendsto (fun y => harmRep (g ω) (H \ B t ω) (fwdMapInv (MartChar.wpath R ω) q y) +
          u (fwdMapInv (MartChar.wpath R ω) q y) + chiC (16 / κ) *
            (logDerivFwd (MartChar.wpath R ω) q (fwdMapInv (MartChar.wpath R ω) q y)).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 (componentLinePhaseData (16 / κ) c₀ F
            (fun ω => invField κ (hC ω)) Wd GT R V d t ω ξ)) := by
      by_cases hq : 0 < q
      · have hWe : (fun r => W r ω) = fun r => Wd r ω := funext fun r => (hWω r).symm
        rw [hWe] at hHeight
        have hex := CLoc.lt_exit_of_lineClock_lt hF hGT hω hRc hR0 hVer hLive
        have htEnt : F.ent (fun r => Wd r ω) ≤ t := by
          by_contra hn
          have hz := Frame.rcap_eq_zero_of_le hF hw (not_le.1 hn).le
          have h := hClock t le_rfl
          rw [hz] at h
          exact (NNReal.coe_pos.2 hq).ne' h
        have hqV : (q : ℝ≥0∞) < V ω := by
          rw [ENNReal.coe_toNNReal (ne_top_of_lt hLive)]
          exact hLive
        have hCover := hHeight F hF hw hDisj (fun r => R r ω) hRc hR0 (V ω) hVer
          t q htEnt hex hq hqV (hClock t le_rfl)
        have hWeReal : (fun r : ℝ => W r.toNNReal ω) = fun r : ℝ => Wd r.toNNReal ω :=
          funext fun r => (hWω r.toNNReal).symm
        rw [hWeReal] at hCover
        obtain ⟨j, hj⟩ := hdc ω
        exact exposed_component_limits_of_reference_heights hκ hF hω hGT hRc hR0 hVer hloc.1.1
          (fun p q => (hj p).trans (hj q).symm) hLive hq rfl (fun s => (hAc s ω).2) hMhω
          (fun s hs => hBsetω s (hOldLive s hs))
          (fun s hs => hMeanω s (hOldLive s hs))
          (fun s hs => hShapeω s (hOldLive s hs))
          (fun s hs => hGermω ⟨s, hs⟩ hLive) hPhaseω hCover
      · have hq0 : q = 0 := le_antisymm (not_lt.1 hq) bot_le
        refine ⟨∅, Set.finite_empty, fun ξ _ hSeed _ => ?_⟩
        have hSeeds := component_seeds_zero (16 / κ) c₀ (fun ω => invField κ (hC ω)) R V ω
        rw [hq0, hSeeds.1, hSeeds.2] at hSeed
        exact (not_lt_of_ge hSeed.1.le hSeed.2).elim
    obtain ⟨T, hT, hInω⟩ := hIn
    obtain ⟨U, hU, -, hOutLim⟩ := hOutω hLive
    refine ⟨T ∪ U, hT.union hU, fun ξ hJ hξ => ?_⟩
    change ξ ∉ componentLineJumps (16 / κ) c₀ F (fun ω => invField κ (hC ω)) Wd GT R V t ω at hJ
    by_cases hSeed : ξ ∈ Ioo
        (componentVL (16 / κ) c₀ (fun ω => invField κ (hC ω)) R V (componentSeedL (16 / κ) c₀) q ω - R q ω)
        (componentVR (16 / κ) c₀ (fun ω => invField κ (hC ω)) R V (componentSeedR (16 / κ) c₀) q ω - R q ω)
    · exact hInω ξ hJ hSeed (fun h => hξ (Or.inl h))
    · exact hOutLim ξ hJ hSeed (fun h => hξ (Or.inr h))

/-- The representation input `hRep` used by
`Wire.theorem14Statement_assembled4`, derived from the actual RepD proof. -/
theorem gw4ComponentRepAStatement
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    Mart.GW4ComponentRepAStatement.{u} :=
  Mart.gw4ComponentRepAStatement_of_rep
    (Mart.gw4ComponentRepStatement_of_repD (gw4ComponentRepDStatement h12 h13))

end InteractingSLE.Theorem14.GW4Fix
