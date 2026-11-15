/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineIfaceR
import InteractingSLE.Spec.Supplement.SB2DrvEraseCore
import InteractingSLE.Spec.Supplement.BW1LinesSafe

/-!
# SB2(1)'s line kernels, part 1: (S) and (L) from a line-set family

Packet PROVE-T14-SB2DRV (round 4), the measure-theoretic skeleton of the kernel half (`SB2LineKernelRStatement`). For
an entrance construction `D`, version data `Vd` and a type cell `w`, K2's (S) and (L) follow
(`BW1Lines.hasSafeLaw_life_of_lineKernel`, `BW1Lines.hasSafeMembers_life_of_lineLocal`, with the physical line
filtration `D.lineFiltC` (R108) and the relative clock `Vd.a`) from a family of line sets `B t` (absolute physical
time `t`) with three per-time inputs:

* **locality**: `B t` relatively closed in `ℍ` at every sample, hitting-measurable, history-marked local for
  `D.lineFiltC t`;
* **the hull identity**: almost surely on the cell and below the lifetime, `ℍ \ B t = c(ℍ \ K_{a t})` (the chart image
  of the relative hull's complement);
* **the line mean**: the local-set mean of `B t` plus `u₀`, read in the launch chart, is the canonical mean
  `couplingMean κ W (a t) (bheProc …)` off the relative hull.

The line kernel itself is the marked Gaussian kernel of `B t` given its germs and marks
(`RelSafeS.ae_condExp_cexp_marked`)
with the covariance of `c(ℍ \ K_{a t})` by the hull identity: **`hasSafeLaw_hasSafeMembers_of_lineSets`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **K2's (S) and (L) from a line-set family** with its locality, hull identity and line mean. -/
theorem hasSafeLaw_hasSafeMembers_of_lineSets (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionR HP I D) {w : WordType} (hw : w ∈ I.types)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
      H \ B t ω = (I.chart ω).2.1 '' (H \ fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal))
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (B t) (WholeField.centredField h u₀) P (g t))
    (hmean : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w) ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z) :
    HasSafeLaw κ (typedRhoL w) (typedRhoR w) P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) Vd.W
        (geomLW Vd.W (cellXL κ ψ I.word w)) (geomRW Vd.W (cellXR κ ψ I.word w))
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (FCDet.thr (typedRhoL w) (typedRhoR w) Vd.W (cellXL κ ψ I.word w) (cellXR κ ψ I.word w)) Vd.W
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField HP.field.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hpast : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.lineFiltC HP 0 :=
    D.past_le_marks.trans (D.marks_le_lineFiltC HP 0)
  obtain ⟨hc, hliftc, hlift, hdom, hfwd, -, hliftm⟩ := I.chart_measurable
  have hdom' : ∀ z, MeasurableSet[D.lineFiltC HP 0] {ω | z ∈ (I.chart ω).dom} := fun z => hpast _ (hdom z)
  have hfwd' : ∀ z, Measurable[D.lineFiltC HP 0] ({ω | z ∈ (I.chart ω).dom}.indicator fun ω => (I.chart ω).1 z) :=
    fun z => (hfwd z).mono hpast le_rfl
  have hliftm' : ∀ z, Measurable[D.lineFiltC HP 0]
      ({ω | z ∈ (I.chart ω).dom}.indicator fun ω => (I.chart ω).2.2 z) := fun z => (hliftm z).mono hpast le_rfl
  have hF : MeasurableSet[D.lineFiltC HP 0] (seedCell κ ψ I.word D.event w) :=
    (D.marks_le_lineFiltC HP 0) _ (measurableSet_seedCell (I.word_measurable.mono D.past_le_marks le_rfl)
      (D.measurableSet_event HP) w)
  have hℋ : ∀ t, D.lineFiltC HP t ≤ mΩ := fun t => (D.lineFiltC HP).le t
  refine ⟨?_, ?_⟩
  · refine BW1Lines.hasSafeLaw_life_of_lineKernel hF hc hdom' hfwd' hliftm' hliftc HP.field.1 (ψ * chiC κ) (chiC κ)
      Vd.clock_cont Vd.clock_mono Vd.clock_zero Vd.clock_meas Vd.timeChange _ (Vd.reach w hw) (Vd.reg w hw)
      (Vd.safeS w hw) (fun t => germSigma (B t) (WholeField.centredField h u₀) ⊔ D.lineFiltC HP t)
      (fun t => le_sup_right) (fun t => sup_le (germSigma_le (hBm t) hhm) (hℋ t))
      (fun t ω => g t ω + (h ω - WholeField.centredField h u₀ ω)) (fun t φ => ?_) hmean
    set U₀ : ℝ := ∫ z, u₀ z * φ z with hU₀
    set X₀ : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) with hX₀def
    have hXX₀ : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) = Complex.exp (Complex.I * (U₀ : ℂ)) • X₀ := by
      funext ω'
      simp only [hX₀def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add,
        WholeField.centredField_apply h hu₀.1 ω' φ]
      congr 1
      push_cast
      ring
    have hsmul := condExp_smul (μ := P) (Complex.exp (Complex.I * (U₀ : ℂ))) X₀
      (germSigma (B t) (WholeField.centredField h u₀) ⊔ D.lineFiltC HP t)
    filter_upwards [hsmul, Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hg t) φ,
      hBK t] with ω h1 h2 h3 hωF hlt hsupp
    have hGc : zeroGFFTestCov ((I.chart ω).2.1 '' (H \ fwdHull (fun s : ℝ => Vd.W s.toNNReal ω)
        (Vd.a t ω).toNNReal)) φ φ = zeroGFFTestCov (H \ B t ω) φ φ := by rw [h3 hωF hlt]
    have hM : (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ = g t ω φ + U₀ := by
      show g t ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
      rw [WholeField.centredField_apply h hu₀.1 ω φ]
      ring
    show P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        germSigma (B t) (WholeField.centredField h u₀) ⊔ D.lineFiltC HP t] ω =
      Complex.exp (Complex.I * ((g t ω + (h ω - WholeField.centredField h u₀ ω)) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((I.chart ω).2.1 '' (H \ fwdHull (fun s : ℝ => Vd.W s.toNNReal ω)
          (Vd.a t ω).toNNReal)) φ φ : ℝ) : ℂ))
    rw [hGc, hM, hXX₀, h1, Pi.smul_apply, smul_eq_mul, h2, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  · exact BW1Lines.hasSafeMembers_life_of_lineLocal HP.field.1 hu₀.1 hh0 hc hdom' hfwd' hliftm' hliftc hlift
      (ψ * chiC κ) (chiC κ) Vd.clock_cont Vd.clock_mono Vd.clock_zero Vd.clock_meas Vd.timeChange _
      (Vd.reach w hw) (Vd.reg w hw) (Vd.safeL w hw) (fun t => D.lineFiltC HP t) (fun t => le_rfl) hℋ B hBm hBc hloc
      hBK

end InteractingSLE.Theorem14.SB.Lv
