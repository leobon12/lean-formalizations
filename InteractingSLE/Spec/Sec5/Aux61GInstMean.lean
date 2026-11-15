/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61UnionKPC1
import InteractingSLE.Spec.Sec5.Aux61GlueKMem
import InteractingSLE.Spec.Supplement.RLCG7aHarmCompletion
import InteractingSLE.Spec.Supplement.RLCG7aGreenHarmonic
import InteractingSLE.Spec.Sec7.SideHeightHull

/-!
# The canonical restart mean: harmonicity and its initial value

Packet PROVE-AUX61-GLUEINST. The cutoff density vanishes on the hull, so the
potential in `canonMean` equals the existing active-domain Green potential.
Its Dirichlet correction is harmonic by the proved positive harmonic integral
theorem. No determination theorem or post-contact kernel is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61GInst

open Restart.FlowStopIdentCMI (CMCut)
open Restart.FlowLocalityGen
open Aux61Win (IsCutoffOn meanF)
open Aux61Fib (FibData FibCode fibW)
open Aux61UnionK (canonMean bhe_canonExt)

universe u

/-- A cutoff harmonic near the hull has the same potential with either the
half-plane or the active-domain indicator. -/
theorem greenPot_eq_aliveGreenPot {F : CMCut} {q : ℂ → ℝ} {N : Set ℂ} {O : Set ℝ}
    (hF : IsCutoffOn F q N O) {w : ℝ → ℝ} {t : ℝ}
    (hKN : closure (fwdHull w t) ⊆ N) :
    GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t =
      aliveGreenPot F w t := by
  have he : H.indicator (QuantumZipper.K3.greenDensity F.f) =
      (H \ fwdHull w t).indicator (QuantumZipper.K3.greenDensity F.f) := by
    funext z
    by_cases hz : z ∈ H
    · by_cases hzK : z ∈ fwdHull w t
      · rw [indicator_of_mem hz, hF.harmonic z (hKN (subset_closure hzK)),
          indicator_of_notMem (fun h : z ∈ H \ fwdHull w t => h.2 hzK)]
      · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ H \ fwdHull w t from ⟨hz, hzK⟩)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (fun h : z ∈ H \ fwdHull w t => hz h.1)]
  rw [he]
  rfl

/-- Harmonicity of the explicit restart mean off the hull. -/
theorem harmonicOnNhd_meanF {κ : ℝ} {v q : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v H) (hq : InnerProductSpace.HarmonicOnNhd q H)
    {F : CMCut} {N : Set ℂ} {O : Set ℝ} (hF : IsCutoffOn F q N O)
    {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (hKN : closure (fwdHull w t) ⊆ N) :
    InnerProductSpace.HarmonicOnNhd (meanF κ v q F w t) (H \ fwdHull w t) := by
  have hInt : NonnegativeHarmonicIntegralStatement :=
    fun _ hU _ hk h0 hi => harmonicOnNhd_integral_nonneg hU hk h0 hi
  have hcor := harmonicOnNhd_physicalGreenCorrection_of_integral hInt F hw hw0 ht
  have hmean := (Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := κ) hw ht hv).add
    ((hq.mono sdiff_subset).sub hcor)
  have he : meanF κ v q F w t =
      fun z => couplingMean κ w t v z + (q z - (F.f z - aliveGreenPot F w t z)) := by
    funext z
    rw [meanF, greenPot_eq_aliveGreenPot hF hKN]
    ring
  rw [he]
  exact hmean

/-- The canonical candidate mean is harmonic at every code whose cutoff
contains the hull. No stochastic premise is needed. -/
theorem harmonicOnNhd_canonMean {d : FibData} {F : CMCut} {N : Set ℂ}
    (hF : IsCutoffOn F d.q N d.O₀) (s : ULift.{u} FibCode) (t : ℝ≥0)
    (hKN : closure (fwdHull (Ito.rpath (fibW · s)) t) ⊆ N) :
    InnerProductSpace.HarmonicOnNhd (canonMean d F s t)
      (H \ fwdHull (Ito.rpath (fibW · s)) t) := by
  exact harmonicOnNhd_meanF (bhe_canonExt d s t).1 d.q_harm hF
    ((FibCode.continuous_driver s.down).comp continuous_real_toNNReal)
    (by simpa only [Function.comp_apply, Real.toNNReal_zero] using FibCode.driver_zero s.down)
    t.coe_nonneg hKN

/-- The half-plane Green inversion at time zero, for a driver starting at zero. -/
theorem greenPot_zero (F : CMCut) {w : ℝ → ℝ} (hw0 : w 0 = 0) {z : ℂ} (hz : z ∈ H) :
    GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) 0 z = F.f z := by
  have hfix : ∀ y ∈ H, fwdMap w 0 y = y := by
    intro y hy
    have hy0 : y ≠ ((w 0 : ℝ) : ℂ) := by
      intro he
      have hi : 0 < y.im := hy
      rw [he, Complex.ofReal_im] at hi
      exact lt_irrefl _ hi
    rw [QuantumZipper.B5.fwdMap_zero_time w hy0, hw0, Complex.ofReal_zero, sub_zero]
  rw [GB7a.greenPot]
  calc (∫ y, QuantumZipper.greenH (fwdMap w 0 z) (fwdMap w 0 y) *
      H.indicator (QuantumZipper.K3.greenDensity F.f) y) =
      ∫ y, QuantumZipper.greenH z y * H.indicator (QuantumZipper.K3.greenDensity F.f) y := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        by_cases hy : y ∈ H
        · rw [hfix z hz, hfix y hy]
        · rw [indicator_of_notMem hy, mul_zero, mul_zero]
    _ = F.f z := GB7a.integral_greenH_mul_indicator_greenDensity
      (F.smooth.of_le (by simp)) F.compact F.odd z

/-- The explicit mean at time zero is the initial reference extension plus `q`. -/
theorem meanF_zero (κ : ℝ) (v q : ℂ → ℝ) (F : CMCut) {w : ℝ → ℝ} (hw0 : w 0 = 0)
    {z : ℂ} (hz : z ∈ H) : meanF κ v q F w 0 z = v z + q z := by
  have hz0 : z ≠ 0 := by
    intro he
    have hi : 0 < z.im := hz
    rw [he, Complex.zero_im] at hi
    exact lt_irrefl _ hi
  rw [meanF, Coupling.MartMeans2.couplingMean_zero κ hw0 v hz0, greenPot_zero F hw0 hz]
  ring

/-- The canonical extension and the initial reference extension agree on H. -/
theorem canonExt_zero (d : FibData) (s : ULift.{u} FibCode) :
    EqOn (Aux61FibK.canonExt d s 0) (Aux61GlueK.refMean0 d) H := by
  have hS : (forceJumpSet
      (fun i => Sec7.PocketTraversal.geomLW fibW (fun _ => flowLineXL d.bR d.JR 0) i 0 s - fibW 0 s)
      (fun j => Sec7.PocketTraversal.geomRW fibW (fun _ => flowLineXR d.bR d.JR 0) j 0 s - fibW 0 s)).Finite := by
    unfold forceJumpSet
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  exact Impl.eqOn_of_isBoundedHarmonicExtension hS (Aux61GlueK.refExt_zero d s)
    (Aux61FibK.refExt_canonExt d s 0)

/-- The canonical candidate at time zero is exactly `refMean0 + q`, pointwise on H. -/
theorem canonMean_zero (d : FibData) (F : CMCut) (s : ULift.{u} FibCode) :
    EqOn (canonMean d F s 0) (Aux61GlueK.fibMean0 d) H := by
  intro z hz
  have hw0 : Ito.rpath (fibW · s) 0 = 0 := by
    simp only [Ito.rpath, Real.toNNReal_zero, fibW, FibCode.driver_zero]
  rw [canonMean, NNReal.coe_zero, meanF_zero d.κ _ _ F hw0 hz, canonExt_zero d s hz]
  rfl

end InteractingSLE.Sec5.Aux61GInst
