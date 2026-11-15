/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8Chart

/-! # GW2: the canonical chart mean at physical stopping times -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR8

open GW2Fb Supp8 Supp8.GB6 Supp8.Q3Rel Supp8.Q3Chain Supp8.GB6LMean Supp8.GB6LineL
open Exist.StagedLaw GW2JointKernel GW2TipSystem LocalSets WholeField Restart Sec7.PocketTraversal
open RelSafeS

/-- FABLE's actual stopped union mean, in the chart form of the lines step.
The complete angle word is retained and every fixed typing is allowed.
The chain is frozen beyond the physical stopping time, before its lifetime. -/
theorem exists_chart_mean_stop
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
          ∃ p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ),
            IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
              (flowLineXL b J 0) (flowLineXR b J 0)
              (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
              (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
              (fun r : ℝ => W r.toNNReal ω) s (Wα · ω) T p ∧
            ∀ (nL nR : ℕ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
              (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
              FCDet.IsFlowType κ θ c xL xR ρL ρR →
              ∀ ψ : TestOn upperHalfPlaneOpens,
                Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => p.2.2.1 r.toNNReal) q) →
                Chart.chartTransport (isConformal_relChart (cfRec s W ζ ω))
                    1 (specOffset κ) (chiC κ)
                    (g ω + SupercriticalConformalCovariance.GM24.smoothDist
                      upperHalfPlaneOpens u₀) ψ =
                  ∫ y, couplingMean κ (fun r : ℝ => p.2.2.1 r.toNNReal) q
                    (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => p.2.2.1 t)
                      (geomLW (fun t (_ : Unit) => p.2.2.1 t) (fun _ => xL))
                      (geomRW (fun t (_ : Unit) => p.2.2.1 t) (fun _ => xR)) () q) y * ψ y := by
  obtain ⟨K, hKm, hKe, hlocal, hmean⟩ :=
    ae_eqOn_unionMean_gw2_of_thm12_thm13 h12 h13 hκ hb hG hb' hT hcf
      hcomp s hNR hc'J hc'b htr hC hα hX hτ hτζ hτt hu₀
  refine ⟨K, hKm, hKe, hlocal, fun g hg => ?_⟩
  filter_upwards [hmean g hg, hg.2.1, hKe, hcomp, ae_driver_zero_continuousOn hcf]
    with ω hmeanω hrepω hKeω hcompω hWω hsH hT0 hTc
  dsimp only
  obtain ⟨p, G, hp, hGb, hmeanp⟩ := hmeanω hsH hT0 hTc
  obtain ⟨wU, hwU, hrep⟩ := hrepω
  let T := (τ ω).untopD 0
  let U : ℝ → ℝ := fun r => W r.toNNReal ω
  let D : ℝ → ℝ := fun r => p.1 r.toNNReal
  let R : ℝ≥0 → ℝ := fun t => p.2.2.1 t
  let a := relClock U s (fun r : ℝ => Wα r.toNNReal ω) T
  let q := a.toNNReal
  have hpre := relChainStop_prefix hp
  have hclock : relClock U s D T = a := (hpre T le_rfl).2.1
  have ha : 0 < a := hclock ▸ hp.2.2.2.2.2.2.2.1
  have hq : (q : ℝ) = a := Real.coe_toNNReal _ ha.le
  have hDc : Continuous D := hp.1.comp continuous_real_toNNReal
  have hWr : Continuous p.2.2.1 := hp.2.2.2.2.1
  have hWr0 : p.2.2.1 0 = 0 := hp.2.2.2.2.2.1
  have hRc : Continuous R := hWr.comp continuous_subtype_val
  have hRp : Continuous (Ito.rpath R) := hRc.comp continuous_real_toNNReal
  have hR0 : R 0 = 0 := hWr0
  have hRp0 : Ito.rpath R 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hR0
  have hWR : EqOn p.2.2.1 (Ito.rpath R) (Icc 0 (q : ℝ)) := by
    intro x hx
    change p.2.2.1 x = p.2.2.1 (x.toNNReal : ℝ)
    rw [Real.coe_toNNReal _ hx.1]
  have hhs : fwdHull p.2.2.1 q = fwdHull (Ito.rpath R) q :=
    QuantumZipper.CharFunRhs.fwdHull_eq_of_eqOn hWr hRp q.coe_nonneg hWR
  have hKf : K ω = fwdHull D T := hKeω.trans (hpre T le_rfl).1.symm
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hcompω.1]; exact ENNReal.coe_lt_top
  have hWc : Continuous (W · ω) := by
    have hc := hWω.2
    rw [hcompω.1] at hc
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.mp hc
  have hr : rtime (cfRec s W ζ ω) = s := rtime_recOf_cfE s hsζ
  have hU : EqOn (rdrv (cfRec s W ζ ω)) U (Icc 0 (s : ℝ)) :=
    fun x hx => rdrv_recOf_cfE s hWω.1 hWω.2 hsζ hx.2
  have hHull : relMap U s '' fwdHull D T = fwdHull (Ito.rpath R) q := by
    have hh := (hpre T le_rfl).2.2
    rw [← (hpre T le_rfl).1] at hh
    change relMap U s '' fwdHull D T = fwdHull p.2.2.1 a at hh
    rw [← hq, hhs] at hh
    exact hh
  have hO : H \ (retSet s W ζ ω ∪ K ω) =
      (relChart (cfRec s W ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) q) := by
    rw [retSet_eq_invHull hsζ hWω.1 hWω.2, hKf]
    exact compl_union_eq_relChart hr (hWc.comp continuous_real_toNNReal) hU
      (isHPHull_fwdHull hDc T.coe_nonneg).1 (relChainStop_disjoint hp) hHull
  have hmean' := hmeanp wU hwU hrep
  change EqOn (fun z => wU z + u₀ z)
    (fun z => G (QuantumZipper.fwdMap p.2.2.1 (relClock U s D T) (relMap U s z)) -
      chiC κ * ((QuantumZipper.logDerivFwd p.2.2.1 (relClock U s D T)
        (relMap U s z)).im + (relLog U s z).im)) _ at hmean'
  rw [hclock, ← hq] at hmean' hGb
  refine ⟨p, hp, fun nL nR xL xR ρL ρR ht ψ hψ => ?_⟩
  have hGR := bhe_flowed_congr (fun i => GW3Word.flowLineXL_nonpos _ _ i)
    (fun j => GW3Word.flowLineXR_nonneg _ _ j) hWr hWr0 hRp hRp0 q.coe_nonneg hWR hGb
  exact chartTransport_eq_bheProc hκ ht hr hU hO hwU hu₀.1 hrep
    hmean' hWR hRc hR0 hGR hψ

end InteractingSLE.Theorem14.GW2JDetR8
