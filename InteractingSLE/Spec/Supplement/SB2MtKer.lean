/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MsVer
import InteractingSLE.Spec.Supplement.SB2DrvLineKer

/-!
# SB2(2)'s kernel half at one relative version: K2's (S) and (L) from line sets

Packet PROVE-SB2-LCMEAN, round 12 (D5: K2 with the line family). For a relative version `V : Ms.StageVersionG` at B's
stage `ℓ` (F2b) and a type cell of F3's word, K2's (S) and (L) for the chart field
`chartTransport (Φ ω) 1 (ψχ) χ (h ω)` follow from a family of line sets `B t` (B's own time `t`) with

* **locality**: `B t` relatively closed in `ℍ`, hitting-measurable, history-avoidance local for the completed line
  filtration `Ms.lineFiltC P 𝓖 t`;
* **the hull identity**: almost surely on the cell and below the version's lifetime, `ℍ ∖ B t = Φ⁻¹(ℍ ∖ K_{a t})`
  (for `B t = A₁ ∪ A₂ t` this is the version's field `hull`, **`hBK_of_hull`**);
* **the line mean**: the local-set mean of `B t` plus `u₀`, read in the chart, is K2's coupling mean off the relative
  hull.

**`hasSafeLaw_hasSafeMembers_of_stageLines`** is SB2(1)'s `Lv.hasSafeLaw_hasSafeMembers_of_lineSets` with SB2(2)'s
version, chart family and completed line filtration (`BW1Lines.hasSafeLaw_life_of_lineKernel`,
`BW1Lines.hasSafeMembers_life_of_lineLocal`; the line kernel is the marked Gaussian kernel
`Supp8.RelSafeS.ae_condExp_cexp_marked`).

R48: Theorems 1.2–1.3 are not used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mt

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {F : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord}
  {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L : Ω → ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The hull identity of the union line sets** from the version's field `hull`. -/
theorem hBK_of_hull (V : StageVersionG κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L) {w : WordType} (hw : w ∈ types)
    (t : ℝ≥0) : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → V.a t ω < V.Λ w ω →
      H \ (fun ω => A₁ t ω ∪ A₂ t ω) ω =
        (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) :=
  V.hull w hw t

omit [StandardBorelSpace Ω] in
/-- **K2's (S) and (L) on a type cell of F3's word from a line-set family** with its locality, hull identity and line
mean (SB2(2)'s transposition of `Lv.hasSafeLaw_hasSafeMembers_of_lineSets`). -/
theorem hasSafeLaw_hasSafeMembers_of_stageLines (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (V : StageVersionG κ ψ P F 𝓖 A₁ A₂ Φ β₁ types pc tL L)
    {w : WordType} (hw : w ∈ types) (hF : MeasurableSet[lineFiltC P 𝓖 0] (seedCell κ ψ β₁ F w))
    (hc : ∀ ω, (Φ ω).IsConformal) (hliftc : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (Φ ω).2.2 (Φ ω).dom)
    (hdom : ∀ z, MeasurableSet[lineFiltC P 𝓖 0] {ω | z ∈ (Φ ω).dom})
    (hfwd : ∀ z, Measurable[lineFiltC P 𝓖 0] ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).1 z))
    (hliftm : ∀ z, Measurable[lineFiltC P 𝓖 0] ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).2.2 z))
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (lineFiltC P 𝓖 t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w → V.a t ω < V.Λ w ω →
      H \ B t ω = (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal))
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (B t) (WholeField.centredField h u₀) P (g t))
    (hmean : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ F w →
      V.a t ω < V.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) V.W (geomLW V.W (cellXL κ ψ β₁ w))
            (geomRW V.W (cellXR κ ψ β₁ w)) ω (V.a t ω).toNNReal) z * φ z) :
    HasSafeLaw κ (typedRhoL w) (typedRhoR w) P V.𝓗 (seedCell κ ψ β₁ F w) (V.Λ w) V.W
        (geomLW V.W (cellXL κ ψ β₁ w)) (geomRW V.W (cellXR κ ψ β₁ w))
        (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P V.𝓗 (seedCell κ ψ β₁ F w) (V.Λ w) V.W
        (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hℋ : ∀ t, lineFiltC P 𝓖 t ≤ mΩ := fun t => (lineFiltC P 𝓖).le t
  refine ⟨?_, ?_⟩
  · refine BW1Lines.hasSafeLaw_life_of_lineKernel hF hc hdom hfwd hliftm hliftc hh.1 (ψ * chiC κ) (chiC κ)
      V.clock_cont V.clock_mono V.clock_zero V.clock_meas V.timeChange _ (V.reach w hw) (V.reg w hw)
      (V.safeS w hw) (fun t => germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t)
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
      (germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t)
    filter_upwards [hsmul, Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hg t) φ,
      hBK t] with ω h1 h2 h3 hωF hlt hsupp
    have hGc : zeroGFFTestCov ((Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω)
        (V.a t ω).toNNReal)) φ φ = zeroGFFTestCov (H \ B t ω) φ φ := by rw [h3 hωF hlt]
    have hM : (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ = g t ω φ + U₀ := by
      show g t ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
      rw [WholeField.centredField_apply h hu₀.1 ω φ]
      ring
    show P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + (h ω - WholeField.centredField h u₀ ω)) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω)
          (V.a t ω).toNNReal)) φ φ : ℝ) : ℂ))
    rw [hGc, hM, hXX₀, h1, Pi.smul_apply, smul_eq_mul, h2, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  · exact BW1Lines.hasSafeMembers_life_of_lineLocal hh.1 hu₀.1 hh0 hc hdom hfwd hliftm hliftc hlift
      (ψ * chiC κ) (chiC κ) V.clock_cont V.clock_mono V.clock_zero V.clock_meas V.timeChange _
      (V.reach w hw) (V.reg w hw) (V.safeL w hw) (fun t => lineFiltC P 𝓖 t) (fun t => le_rfl) hℋ B hBm hBc hloc
      hBK

end InteractingSLE.Theorem14.SB.Mt
