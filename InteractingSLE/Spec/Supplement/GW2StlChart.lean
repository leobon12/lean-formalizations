/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmUnion
import InteractingSLE.Spec.Supplement.GW2JDetR8Chart

/-!
# GW2's stage lines, part 4: the chart mean at a random retained time

Packet PROVE-GW2-STAGEMEAN, stage-lines round (the per-stage union mean `LinesLocal.mean` / RELDET's `hmeanL`, on the
`HasLaunchPairEq` route). At stage `k + 1`, conditionally on the past (`μ = condExpKernel P 𝒢_k ω₀`), the stage
field is a GFF of the stage word, the image counterflow is a complete counterflow of it, and the retained counterflow
is read up to the random own time `σ_k` (`GW2Sgk.exists_stop_of_datum`, `GW2Shr.invHull_eq_launch`). The union mean
of the stage is then GW2's stage-0 union mean under `μ` with `s` replaced by `σ_k` (`GW2Stm.exists_unionMean_gw2_stop`),
in the EqOn form of the harmonic representative. The lines step (`GW2Rd.hasRelSafe_of_local_rec`,
`GW2Sde.StageInst.LinesLocal.mean`) reads means as CHART TRANSPORTS of the canonical coupling mean of the typed word.
JOINTDET converted FABLE's deterministic-time mean to that form (`GW2JDetR8.exists_chart_mean_stop`); the conversion
is per sample, so it runs unchanged at a random retained time:

* **`exists_chart_mean_stop_random`**: the conclusion of `GW2JDetR8.exists_chart_mean_stop` with the deterministic
  retained time `s` replaced by a stopping time `σ` of the counterflow's driving filtration (the retained set is the
  measurable version `A` of `invHull W σ`): for every local-set mean `g` of `A ∪ K`, almost surely on
  `{γ(σ) ∈ ℍ, 0 < τ < T_c}`, there is a relative chain stop `p` such that for every typing of the angle-`θ` joint word
  of `cfRec σ W ζ` and every test function off the relative hull, the chart transport of `g + u₀` by
  `relChart (cfRec σ W ζ)` is the integral of the canonical coupling mean.

Valid under any probability measure (in particular under the conditional kernel of the stage). Conditional helper
with a distinct name; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Stl

open Restart Exist Exist.StagedLaw WholeField LocalSets Sec7.PocketTraversal
open Supp8 Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain RelSafeS
open Supp8.Q3Rel (invHull relLog)
open GW2JointKernel GW2TipSystem GW2Fb GW2JDetR8

/-- **The chart mean of the stopped union at a random retained time** (`GW2JDetR8.exists_chart_mean_stop` with `s`
replaced by a stopping time `σ` of the counterflow's driving filtration). -/
theorem exists_chart_mean_stop_random (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {c' : BoundaryWord} {h₁ : Ω → DistOn upperHalfPlaneOpens} {𝓕' : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL' : Fin (flowLineNL c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ} {VR' : Fin (flowLineNR c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ}
    {B' : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (htr' : ∀ ω, IsTranslateAddConst 0 (0 * chiC (16 / κ)) (h' ω) (h₁ ω))
    (hC' : IsOptionalHullCoupling (16 / κ) (flowLineXL c'.fn c'.jumps 0) (flowLineXR c'.fn c'.jumps 0)
      (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0) (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) P 𝓕' W VL' VR' B' ζ h₁)
    (hX' : IsMeasurableKilledDriving W VL' VR' ζ)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hNR : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → γ ω v ≠ 0) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX') σ) (hσt : ∀ ω, σ ω ≠ ⊤)
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
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ A K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      IsLocalSet (fun ω => A ω ∪ K ω) (centredField X u₀) P ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (fun ω => A ω ∪ K ω) (centredField X u₀) P g →
        ∀ᵐ ω ∂P, γ ω ((σ ω).untopD 0 : ℝ≥0) ∈ H → 0 < (τ ω).untopD 0 →
          (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ ω).untopD 0 : ℝ≥0)) →
          let sω : ℝ≥0 := (σ ω).untopD 0
          let c := jointWordOfRec (specOffset κ) κ c' (cfRec sω W ζ ω)
          let T := (τ ω).untopD 0
          let q := (relClock (fun r : ℝ => W r.toNNReal ω) sω (fun r : ℝ => Wα r.toNNReal ω) T).toNNReal
          ∃ p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ),
            IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
              (flowLineXL b J 0) (flowLineXR b J 0)
              (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
              (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
              (fun r : ℝ => W r.toNNReal ω) sω (Wα · ω) T p ∧
            ∀ (nL nR : ℕ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
              FCDet.IsFlowType κ θ c xL xR ρL ρR →
              ∀ ψ : TestOn upperHalfPlaneOpens,
                Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => p.2.2.1 r.toNNReal) q) →
                Chart.chartTransport (isConformal_relChart (cfRec sω W ζ ω)) 1 (specOffset κ) (chiC κ)
                    (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
                  ∫ y, couplingMean κ (fun r : ℝ => p.2.2.1 r.toNNReal) q
                    (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => p.2.2.1 t)
                      (geomLW (fun t (_ : Unit) => p.2.2.1 t) (fun _ => xL))
                      (geomRW (fun t (_ : Unit) => p.2.2.1 t) (fun _ => xR)) () q) y * ψ y := by
  obtain ⟨A, K, hAm, hKm, hAe, hKe, hlocal, hmean⟩ :=
    GW2Stm.exists_unionMean_gw2_stop h12 h13 hκ hb hG hT htr' hC' hX' hcomp hNR hσ hσt htr hC hα hX hτ hτζ hτt hu₀
  refine ⟨A, K, hAm, hKm, hAe, hKe, hlocal, fun g hg => ?_⟩
  filter_upwards [hmean g hg, hg.2.1, hKe, hAe, hcomp, hC'.1.2.2.2.2]
    with ω hmeanω hrepω hKeω hAeω hcompω hpω hsH hT0 hTc
  dsimp only
  obtain ⟨p, G, hp, hGb, hmeanp⟩ := hmeanω hsH hT0 hTc
  obtain ⟨wU, hwU, hrep⟩ := hrepω
  set s : ℝ≥0 := (σ ω).untopD 0 with hsdef
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
    have hc := hpω.2.2.2.1
    rw [hcompω.1] at hc
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.mp hc
  have hr : rtime (cfRec s W ζ ω) = s := rtime_recOf_cfE s hsζ
  have hU : EqOn (rdrv (cfRec s W ζ ω)) U (Icc 0 (s : ℝ)) :=
    fun x hx => rdrv_recOf_cfE s hpω.1 hpω.2.2.2.1 hsζ hx.2
  have hHull : relMap U s '' fwdHull D T = fwdHull (Ito.rpath R) q := by
    have hh := (hpre T le_rfl).2.2
    rw [← (hpre T le_rfl).1] at hh
    change relMap U s '' fwdHull D T = fwdHull p.2.2.1 a at hh
    rw [← hq, hhs] at hh
    exact hh
  have hO : H \ (A ω ∪ K ω) = (relChart (cfRec s W ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) q) := by
    rw [hAeω, hKf]
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

end InteractingSLE.Theorem14.GW2Stl
