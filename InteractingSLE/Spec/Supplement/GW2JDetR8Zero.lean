/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8StopMean

/-! # GW2: the chart mean at physical time zero, including arbitrary angles -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2JDetR8

open GW2Fb Supp8 Supp8.GB6 Supp8.Q3Rel Supp8.Q3Chain Supp8.GB6LMean Supp8.GB6LineL
open Exist.StagedLaw GW2JointKernel LocalSets WholeField Restart Sec7.PocketTraversal RelSafeS
open GW2TipSystem

/-- At time zero every flowed word is its original word, even at a nonzero angle. -/
theorem bhe_flowed_zero {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
      (forceJumpSet xL xR) G) :
    IsBoundedHarmonicExtension (flowedData κ ρL ρR xL xR W 0)
      (flowedJumps xL xR W 0) G := by
  have hL : (fun i => markPosL W 0 (xL i)) = xL := by
    funext i
    unfold markPosL
    rw [markPos_time_zero (w := fun s => -W s) hW.neg (by simp only [hW0, neg_zero])
      (neg_nonneg.mpr (hxL i)), neg_neg]
  have hR : (fun j => markPos W 0 (xR j)) = xR :=
    funext fun j => markPos_time_zero hW hW0 (hxR j)
  simpa only [flowedData, flowedJumps, hL, hR, coe_initJumps] using hG

/-- The retained counterflow mean already has the full joint angle word at
physical flow time zero. No positive flow lifetime is imposed. -/
theorem ae_chart_mean_zero (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' X : Ω → DistOn upperHalfPlaneOpens} {b b' : ℝ → ℝ} {J J' : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ))
      (chiC (16 / κ)) (h ω) (h' ω))
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (s : ℝ≥0)
    {c' : BoundaryWord} (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y)
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
        (flowLineXL b J 0) (flowLineXR b J 0))
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P)
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (retSet s W ζ) (centredField X u₀) P g) :
    ∀ᵐ ω ∂P,
      let c := jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)
      ∀ (R : ℝ≥0 → ℝ), Continuous R → R 0 = 0 →
      ∀ (nL nR : ℕ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
        (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ), FCDet.IsFlowType κ θ c xL xR ρL ρR →
        ∀ ψ : TestOn upperHalfPlaneOpens,
          Chart.chartTransport (isConformal_relChart (cfRec s W ζ ω))
              1 (specOffset κ) (chiC κ)
              (g ω + SupercriticalConformalCovariance.GM24.smoothDist
                upperHalfPlaneOpens u₀) ψ =
            ∫ y, couplingMean κ (Ito.rpath R) 0
              (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => R t)
                (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
                (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () 0) y * ψ y := by
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    κ (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0)
      (flowLineXL b J 0) (flowLineXR b J 0)
  have hcen := centredField_flow_eq hκ hb htr huh hu₀
  have hh0h : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h uh) P := by
    rw [hcen.2]
    exact hh0
  have hgh : IsLocalSetMean (retSet s W ζ) (centredField h uh) P g := by
    rw [hcen.2]
    exact hg
  have hret := ae_eqOn_retMean_gw2 h12 h13 hκ hb hG hb' hT hcf hc'J hc'b huh hh0h s hgh
  filter_upwards [hret, hζ, ae_driver_zero_continuousOn hcf, hg.2.1]
    with ω hretω hζω hWω hrepω
  dsimp only
  intro R hRc hR0 nL nR xL xR ρL ρR ht ψ
  let c := jointWordOfRec (specOffset κ) κ c' (cfRec s W ζ ω)
  have hsζ : (s : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
  have hWc : Continuous (W · ω) := by
    have hc := hWω.2
    rw [hζω] at hc
    exact continuousOn_univ.mp (hc.mono fun _ _ => ENNReal.coe_lt_top)
  obtain ⟨G, hGb⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData
    κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  have hG0 : IsBoundedHarmonicExtension (cfData κ c.fn c.jumps) (cfJumps c.fn c.jumps)
      (fun z => G z - θ * chiC κ) := by
    rw [coe_cfJumps]
    exact isBoundedHarmonicExtension_sub_const' hGb fun x => by
      rw [cfData, Sec5.RestartGen.forceBoundaryData_flowLine_angle hκ _ _ θ 0 x]
      ring
  obtain ⟨wU, hwU, hrep⟩ := hrepω
  have hmean := hretω hsζ _ hG0 wU hwU hrep
  have hRp : Continuous (Ito.rpath R) := hRc.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hR0
  have hHull0 : fwdHull (Ito.rpath R) 0 = ∅ :=
    QuantumZipper.RS.fwdHull_zero_eq_empty (W := Ito.rpath R) hRp
  have hGflow := bhe_flowed_zero (fun i => GW3Word.flowLineXL_nonpos _ _ i)
    (fun j => GW3Word.flowLineXR_nonneg _ _ j) hRp hRp0 hGb
  have hr : rtime (cfRec s W ζ ω) = s := rtime_recOf_cfE s hsζ
  have hU : EqOn (rdrv (cfRec s W ζ ω)) (fun r : ℝ => W r.toNNReal ω)
      (Icc 0 (s : ℝ)) := fun x hx => rdrv_recOf_cfE s hWω.1 hWω.2 hsζ hx.2
  have hO : H \ retSet s W ζ ω = (relChart (cfRec s W ζ ω)).2.1 ''
      (H \ fwdHull (Ito.rpath R) ((0 : ℝ≥0) : ℝ)) := by
    have hh : relMap (fun r : ℝ => W r.toNNReal ω) s '' (∅ : Set ℂ) =
        fwdHull (Ito.rpath R) 0 := by
      rw [Set.image_empty, hHull0]
    have hshape := compl_union_eq_relChart hr (hWc.comp continuous_real_toNNReal) hU
      (empty_subset H) (by
        rw [closure_empty]
        exact Set.disjoint_left.mpr (fun _ h => False.elim h)) hh
    rw [retSet_eq_invHull hsζ hWω.1 hWω.2, NNReal.coe_zero]
    simpa only [union_empty, Function.comp_def] using hshape
  have hv : EqOn (fun z => wU z + u₀ z)
      (fun z => G (fwdMap (Ito.rpath R) 0 (relMap (fun r : ℝ => W r.toNNReal ω) s z)) -
        chiC κ * ((logDerivFwd (Ito.rpath R) 0 (relMap (fun r : ℝ => W r.toNNReal ω) s z)).im +
          (relLog (fun r : ℝ => W r.toNNReal ω) s z).im)) (H \ retSet s W ζ ω) := by
    intro z hz
    have h1 := hmean hz
    have h2 := hcen.1 hz.1
    simp only at h1 h2
    dsimp only
    rw [fwdMap_zero_time (W := Ito.rpath R) hRp0]
    simp only [QuantumZipper.logDerivFwd, intervalIntegral.integral_same,
      neg_zero, Complex.zero_im, zero_add]
    rw [h2]
    linarith only [h1]
  exact chartTransport_eq_bheProc hκ ht hr hU hO hwU hu₀.1 hrep hv
    (fun _ _ => rfl) hRc hR0 hGflow
    (by rw [NNReal.coe_zero, hHull0]; exact Set.disjoint_left.mpr (fun _ _ h => False.elim h))

end InteractingSLE.Theorem14.GW2JDetR8
