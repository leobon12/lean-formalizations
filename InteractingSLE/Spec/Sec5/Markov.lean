/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.MarkovStop
import InteractingSLE.Spec.Sec5.MarkovFlow
import InteractingSLE.Spec.Coupling.WholeField2Kernel
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling

/-!
# Aux. lemma 53: restarting the optional hull specification at an own stopping time (the Gaussian clause)

Packet PROVE-SEC5-D. Specification p. 245, **Aux. lemma 53** (Restarting the original hull specification): "Let
`(h, W, V)` satisfy the original optional hull coupling of Theorem 1.1. At every finite own-filtration stopping time
`τ < T_*`, condition on the recorded driving history and map the active field and future hulls by the centered map
`f_τ = g_τ − W_τ`, with the inherited logarithmic derivative branch. Their conditional law again satisfies the original
optional hull specification, with the current force groups as initial data." Its proof: "The conditional Gaussian law
outside the later hull is already the original law at that later stopping time. Its harmonic mean is a function of the
later history alone. … Conformal invariance of the Green kernel transports this relative identity to the half-plane.
The chain rule with the inherited derivative logarithm gives the canonical finite-force mean from the current force
coordinates".

This file proves that conditional-law clause after the restart, for every later stopping time, in the **original
domain** of the chart `f_T` (`IsOptionalHullCoupling.restart_condExp`): for the restarted processes

  `W'_t = W_{T+t} − W_T`, `V'_t = V_{T+t} − W_T`, `ζ' = ζ − T`  (`restartDrv`, `restartMark`, `restartLife`)

with the restarted filtration `𝓖'_s = 𝓕_{T+s}` of the frozen driving filtration, every `𝓖'`-stopping time `τ' < ζ'`,
every bounded harmonic extension `u` of the restarted force data at `τ'`, and every test function `φ` supported in
`F_T(ℍ ∖ K'_{τ'})`, conditionally on `𝓖'_{τ'}` the pairing `(h, φ)` has the characteristic function of the restarted
coupling mean read through the chart `f_T = Chart.id.loewner W T` (minus `χ` times its lift `arg f_T′`) plus a
zero-boundary GFF on `F_T(ℍ ∖ K'_{τ'})`.

This is, verbatim, the hypothesis `IsChartCouplingCharFun κ ρL ρR P 𝓖' W' VL' VR' ζ' (restartChart W T) 0 χ h` of
PROVE-CPL-MART2 (`Spec/Coupling/MartMeans2Chart.lean`, in progress when this file was written), whose
`isCouplingCharFun_of_isChartTransport` transports it to the chart-transported field `h_T` (frozen `IsChartTransport`
with `σ = 1`, `a = 0`, `k = χ`): the clause `IsCouplingCharFun` of the restarted coupling in the half-plane.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper

namespace InteractingSLE

namespace Sec5

namespace Markov

/-! ### The restarted processes -/

section Defs

variable {Ω : Type*}

/-- The restarted driver `W'_t = W_{T+t} − W_T`. -/
def restartDrv (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => W (T ω + t) ω - W (T ω) ω

/-- A restarted force coordinate `V'_t = V_{T+t} − W_T`. -/
def restartMark (V W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => V (T ω + t) ω - W (T ω) ω

/-- The restarted lifetime `ζ' = ζ − T`. -/
def restartLife (ζ : Ω → ℝ≥0∞) (T : Ω → ℝ≥0) : Ω → ℝ≥0∞ := fun ω => ζ ω - T ω

/-- The chart `f_T` of the restart: `(f_T, F_T, Im log f_T′)` (`Chart.id.loewner`), with the frozen driver path
convention `s ↦ W_{s⁺}`. -/
def restartChart (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (ω : Ω) : Chart :=
  Chart.id.loewner (fun s : ℝ => W s.toNNReal ω) (T ω)

/-- The restarted force data relative to the restarted driver are the original ones at the later time. -/
theorem restartMark_sub_restartDrv (V W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    restartMark V W T t ω - restartDrv W T t ω = V (T ω + t) ω - W (T ω + t) ω := by
  simp only [restartMark, restartDrv]; ring

end Defs

/-! ### The conditional-law clause after the restart -/

section Clause

open Sec2.Restart

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 53, the conditional Gaussian clause after the restart** (in the original domain of the chart `f_T`).
Let `(h, W, V)` satisfy the frozen optional hull specification, `T` a finite stopping time of its driving filtration
`𝓕`, and `𝓖'_s = 𝓕_{T+s}` the restarted filtration. For every `𝓖'`-stopping time `τ'` before the restarted lifetime
`ζ − T`, every bounded harmonic extension `u` of the restarted force data at `τ'` and every test function `φ` supported
in `F_T(ℍ ∖ K'_{τ'})` (`K'` the hull of the restarted driver), almost surely

  `E[e^{i (h, φ)} | 𝓖'_{τ'}] = exp(i ∫ (𝔥'_{τ'} ∘ f_T − χ arg f_T′) φ − ½ ‖φ‖²_{H⁻¹(F_T(ℍ ∖ K'_{τ'}))})`.

(The body is PROVE-CPL-MART2's `IsChartCouplingCharFun` for the restarted processes, the chart `restartChart W T`,
height shift `0` and lift coefficient `χ`.) -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.restart_condExp
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < restartLife ζ T ω) (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (forceJumpSet
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (u ω))
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ (restartChart W T ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
        Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => restartDrv W T s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0) (u ω) ((restartChart W T ω).1 z) - 0 -
              chiC κ * (restartChart W T ω).2.2 z) * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((restartChart W T ω).2.1 ''
            (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) φ φ : ℝ) : ℂ)) := by
  classical
  obtain ⟨hE, -, -, hX', hcl⟩ := hC
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      ∀ t, MeasurableSet[drivingFiltration P hX t] s :=
    fun s hs h0 t => Ito.measurableSet_usualAugmentation_of_null hs h0 t
  have hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := by
    filter_upwards [hτζ] with ω hω htop
    rw [htop] at hω
    exact not_top_lt hω
  set σ := restartTime T τ with hσdef
  have hσ : IsStoppingTime (drivingFiltration P hX) σ := isStoppingTime_restartTime hT hnull hτ hτfin
  have hσval : ∀ ω, (σ ω).untopD 0 = T ω + (τ ω).untopD 0 := fun ω => restartTime_untopD T τ ω
  have hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hτζ, hτfin] with ω hω hfin
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hfin
    rw [← hr] at hω
    have h1 : ((T ω : ℝ≥0∞)) + (r : ℝ≥0∞) < ζ ω := lt_tsub_iff_left.1 hω
    show (((T ω + (τ ω).untopD 0 : ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω
    rw [← hr, WithTop.untopD_coe]
    exact_mod_cast h1
  have hu' : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω)
        (fun i => VR i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω)
        (fun i => VR i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω)) (u ω) := by
    intro ω
    have e1 : (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω) =
        fun i => VL i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω := funext fun i => by
      rw [restartMark_sub_restartDrv, hσval]
    have e2 : (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω) =
        fun i => VR i ((σ ω).untopD 0) ω - W ((σ ω).untopD 0) ω := funext fun i => by
      rw [restartMark_sub_restartDrv, hσval]
    rw [← e1, ← e2]
    exact hu ω
  have hmain := (hcl σ hσ hσζ).2 u hu' φ
  rw [measurableSpace_restartTime_eq hT hnull hτ hτfin]
  filter_upwards [hmain, hE.2.2.2.2, hτfin, hσζ] with ω hω hp hfin hσω hsupp
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hfin
  have hτr : (τ ω).untopD 0 = r := by rw [← hr, WithTop.untopD_coe]
  have hσr : (σ ω).untopD 0 = T ω + r := by rw [hσval, hτr]
  have hTr : ((T ω + r : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    have := hσω
    rw [show σ ω = ((T ω + r : ℝ≥0) : WithTop ℝ≥0) by simp only [hσdef, restartTime, hτr]] at this
    exact this
  obtain ⟨himg, hint⟩ := restart_path (w := fun t => W t ω) hp.2.2.2.1 hp.1 hTr κ (u ω)
  simp only [hτr] at hsupp ⊢
  rw [hσr] at hω
  have himg' : (restartChart W T ω).2.1 ''
      (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) (r : ℝ)) =
        H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((T ω + r : ℝ≥0) : ℝ) := himg
  rw [himg'] at hsupp ⊢
  have hdisj : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((T ω + r : ℝ≥0) : ℝ)) :=
    Set.disjoint_left.2 fun z hz hzK => (hsupp hz).2 hzK
  rw [hω hdisj, WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω) hp.2.2.2.1 hp.1
    hTr φ hdisj]
  congr 4
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport φ
  · have hz' : z ∈ (restartChart W T ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) (r : ℝ)) := by
      rw [himg']; exact hsupp hz
    exact congrArg (· * φ z) (hint z hz').symm
  · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]

end Clause

end Markov

end Sec5

end InteractingSLE
