/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8Driver

/-! # GW2: the actual stopping-time chart mean in any relative driver version -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR8

open GW2Fb Supp8 Supp8.GB6 Supp8.GB6LMean Supp8.GB6LineL Exist.StagedLaw
open GW2JointKernel GW2TipSystem LocalSets WholeField Restart Sec7.PocketTraversal RelSafeS

/-- The actual chart mean can be read with any continuous relative driver
version that generates the physical hulls through the stopping time. No
relative SDE law, relative mean identity, or clock-regularity input is assumed. -/
theorem exists_chart_mean_stop_for_versions
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) (s : ℝ≥0)
    (hNR : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → v ≤ s → γ ω v ≠ 0)
    {c' : BoundaryWord} (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    {X : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) P 𝓕 Wα VL VR B ζα X)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (flowLineXL b J 0) (flowLineXR b J 0))
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      IsLocalSet (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fun ω => retSet s W ζ ω ∪ K ω) (centredField X u₀) P g →
        ∀ᵐ ω ∂P, γ ω s ∈ H → 0 < (τ ω).untopD 0 →
          (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime
            (fun u => (α ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 s) →
          let c := jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)
          let T := (τ ω).untopD 0
          let q := (relClock (fun r : ℝ => W r.toNNReal ω) s
            (fun r : ℝ => Wα r.toNNReal ω) T).toNNReal
          ∀ R : ℝ≥0 → ℝ, Continuous R → R 0 = 0 →
            HullsUpTo (fun r : ℝ => W r.toNNReal ω) s
              (fun r : ℝ => Wα r.toNNReal ω) (Ito.rpath R) T →
            ∀ (nL nR : ℕ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
              (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
              FCDet.IsFlowType κ θ c xL xR ρL ρR →
              ∀ ψ : TestOn upperHalfPlaneOpens,
                Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal) q) →
                Chart.chartTransport (isConformal_relChart (cfRec s W ζ ω))
                    1 (specOffset κ) (chiC κ)
                    (g ω + SupercriticalConformalCovariance.GM24.smoothDist
                      upperHalfPlaneOpens u₀) ψ =
                  ∫ y, couplingMean κ (fun r : ℝ => R r.toNNReal) q
                    (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => R t)
                      (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
                      (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () q) y * ψ y := by
  obtain ⟨K, hKm, hKe, hlocal, hmean⟩ := exists_chart_mean_stop
    h12 h13 hκ hb hG hb' hT hcf hcomp s hNR hc'J hc'b htr hC hα hX hτ hτζ hτt hu₀
  refine ⟨K, hKm, hKe, hlocal, fun g hg => ?_⟩
  filter_upwards [hmean g hg, hcomp, ae_driver_zero_continuousOn hcf,
    hC.1.2.2.2.2, hα, hτζ] with ω hmeanω hcompω hWω hpath hαω hτζω hsH hT0 hTc
  dsimp only
  obtain ⟨p, hp, hm⟩ := hmeanω hsH hT0 hTc
  intro R hRc hR0 hHR nL nR xL xR ρL ρR ht ψ hψ
  let T := (τ ω).untopD 0
  let U : ℝ → ℝ := fun r => W r.toNNReal ω
  let w : ℝ≥0 → ℝ := fun t => Wα t ω
  let a := relClock U s (Ito.rpath w) T
  let q := a.toNNReal
  have hWc : Continuous (W · ω) := by
    have hc := hWω.2
    rw [hcompω.1] at hc
    exact continuousOn_univ.mp (hc.mono fun _ _ => ENNReal.coe_lt_top)
  have hTζ : (T : ℝ≥0∞) < ζα ω := by
    obtain ⟨t, he⟩ := WithTop.ne_top_iff_exists.mp (hτt ω)
    dsimp only [T]
    rw [← he, WithTop.untopD_coe]
    rw [← he] at hτζω
    exact hτζω
  obtain ⟨ha0, hac⟩ := clock_regular_before_contact hcompω.2 hWc hWω.1 hsH
    hαω hpath.2.2.2.1 hpath.1 hTζ hTc
  have hpre := relChainStop_prefix hp
  have hclock : relClock U s (fun r : ℝ => p.1 r.toNNReal) T = a := (hpre T le_rfl).2.1
  have ha : 0 < a := hclock ▸ hp.2.2.2.2.2.2.2.1
  have hq : (q : ℝ) = a := Real.coe_toNNReal _ ha.le
  have he := relChainStop_driver_eq_of_hulls hp hRc hR0 ha0 hac hHR
  change EqOn (fun r : ℝ => p.2.2.1 r.toNNReal) (Ito.rpath R) (Icc 0 a) at he
  rw [← hq] at he
  have hPc : Continuous (fun t : ℝ≥0 => p.2.2.1 t) :=
    hp.2.2.2.2.1.comp continuous_subtype_val
  have hH : fwdHull (fun r : ℝ => p.2.2.1 r.toNNReal) q =
      fwdHull (Ito.rpath R) q := QuantumZipper.CharFunRhs.fwdHull_eq_of_eqOn
    (hPc.comp continuous_real_toNNReal) (hRc.comp continuous_real_toNNReal) q.coe_nonneg he
  have hψp : Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => p.2.2.1 r.toNNReal) q) := by
    rw [hH]
    exact hψ
  have hmψ := hm nL nR xL xR ρL ρR ht ψ hψp
  have hM := couplingMean_bheProc_congr (κ := κ) (W := fun t => p.2.2.1 t)
    (q := q) ρL ρR xL xR hRc he
  refine hmψ.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
  exact congrArg (fun f : ℂ → ℝ => f y * ψ y) hM

end InteractingSLE.Theorem14.GW2JDetR8
