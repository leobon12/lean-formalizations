/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrVer
import InteractingSLE.Spec.Supplement.SB2CrLoc
import InteractingSLE.Spec.Supplement.SB2CiKer

/-!
# K2's (S) and (L) at the root from B-time line facts

Packet PROVE-SB2-CONDFIN (round 8, D44). `Ci.hasSafeLaw_hasSafeMembers_of_stageLines` for the root's versions in B's
own time (`Cr.RootVersionG`). The live cell is the root seed cell `seedCell … Fr w` (an event of the version's `𝓗 0`).
The conditioning cell of the line laws is `seedCell … univ w` (an event of `lineFiltC 𝓖 0`). The line facts are used
only where the clock is positive, which happens only on the root (`clock_root`).

* **`hasSafeLaw_hasSafeMembers_of_rootLines`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cr

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms

variable {κ ψ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {Fr : Set Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord}
  {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L : Ω → ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] in
theorem mem_seedCell_of_univ {w : WordType} {ω : Ω} (h1 : ω ∈ seedCell κ ψ β₁ univ w) (h2 : ω ∈ Fr) :
    ω ∈ seedCell κ ψ β₁ Fr w :=
  ⟨⟨h2, h1.1.2⟩, h1.2⟩

omit [StandardBorelSpace Ω] in
/-- **K2's (S) and (L) on a root type cell from B-time line facts** where the clock is positive. -/
theorem hasSafeLaw_hasSafeMembers_of_rootLines (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (V : RootVersionG κ ψ P Fr 𝓖 A₁ A₂ Φ β₁ types pc tL L)
    {w : WordType} (hw : w ∈ types) (hβ₁ : Measurable[lineFiltC P 𝓖 0] β₁)
    (hc : ∀ ω, (Φ ω).IsConformal) (hliftc : ∀ ω, ContinuousOn (Φ ω).2.2 (Φ ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (Φ ω).2.2 (Φ ω).dom)
    (hdom : ∀ z, MeasurableSet[lineFiltC P 𝓖 0] {ω | z ∈ (Φ ω).dom})
    (hfwd : ∀ z, Measurable[lineFiltC P 𝓖 0] ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).1 z))
    (hliftm : ∀ z, Measurable[lineFiltC P 𝓖 0] ({ω | z ∈ (Φ ω).dom}.indicator fun ω => (Φ ω).2.2 z))
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (lineFiltC P 𝓖 t) (B t) (WholeField.centredField h u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → V.a t ω < V.Λ w ω →
      H \ B t ω = (Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal))
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (B t) (WholeField.centredField h u₀) P (g t))
    (hmean : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w →
      0 < V.a t ω → V.a t ω < V.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ)
          (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => V.W s.toNNReal ω) (V.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) V.W (geomLW V.W (cellXL κ ψ β₁ w))
            (geomRW V.W (cellXR κ ψ β₁ w)) ω (V.a t ω).toNNReal) z * φ z) :
    HasSafeLaw κ (typedRhoL w) (typedRhoR w) P V.𝓗 (seedCell κ ψ β₁ Fr w) (V.Λ w) V.W
        (geomLW V.W (cellXL κ ψ β₁ w)) (geomRW V.W (cellXR κ ψ β₁ w))
        (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P V.𝓗 (seedCell κ ψ β₁ Fr w) (V.Λ w) V.W
        (fun ω => Chart.chartTransport (hc ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hhm : Measurable (WholeField.centredField h u₀) := WholeField.measurable_centredField hh.1 u₀
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hℋ : ∀ t, lineFiltC P 𝓖 t ≤ mΩ := fun t => (lineFiltC P 𝓖).le t
  set M : Set Ω := seedCell κ ψ β₁ univ w with hMdef
  have hM : MeasurableSet[lineFiltC P 𝓖 0] M := measurableSet_seedCell hβ₁ MeasurableSet.univ w
  have hFM : ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ β₁ Fr w → ω ∈ M :=
    Eventually.of_forall fun ω hω => ⟨⟨mem_univ ω, hω.1.2⟩, hω.2⟩
  have hroot : ∀ t, ∀ᵐ ω ∂P, ω ∈ M → 0 < V.a t ω → ω ∈ seedCell κ ψ β₁ Fr w := fun t => by
    filter_upwards [V.clock_root t] with ω hω hωM hpos using mem_seedCell_of_univ hωM (hω hpos)
  refine ⟨?_, ?_⟩
  · refine hasSafeLaw_life_of_lineKernelS hM hFM hc hdom hfwd hliftm hliftc hh.1 (ψ * chiC κ) (chiC κ)
      V.clock_cont V.clock_mono V.clock_zero V.clock_meas V.timeChange _ (V.reach w hw) (V.reg w hw)
      (fun t => by
        filter_upwards [hroot t, V.reg w hw] with ω h1 h2 hωM hpos using h2 (h1 hωM hpos))
      (V.safeS w hw) (fun t => germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t)
      (fun t => le_sup_right) (fun t => sup_le (germSigma_le (hBm t) hhm) (hℋ t))
      (fun t ω => g t ω + (h ω - WholeField.centredField h u₀ ω)) (fun t φ => ?_)
      (fun t φ => by
        filter_upwards [hroot t, hmean t φ] with ω h1 h2 hωM hpos hlt hd using h2 (h1 hωM hpos) hpos hlt hd)
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
      hBK t, hroot t] with ω h1 h2 h3 h4 hωM hpos hlt hsupp
    have hGc : zeroGFFTestCov ((Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω)
        (V.a t ω).toNNReal)) φ φ = zeroGFFTestCov (H \ B t ω) φ φ := by rw [h3 (h4 hωM hpos) hlt]
    have hM' : (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ = g t ω φ + U₀ := by
      show g t ω φ + (h ω φ - WholeField.centredField h u₀ ω φ) = _
      rw [WholeField.centredField_apply h hu₀.1 ω φ]
      ring
    show P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        germSigma (B t) (WholeField.centredField h u₀) ⊔ lineFiltC P 𝓖 t] ω =
      Complex.exp (Complex.I * ((g t ω + (h ω - WholeField.centredField h u₀ ω)) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((Φ ω).2.1 '' (H \ fwdHull (fun s : ℝ => V.W s.toNNReal ω)
          (V.a t ω).toNNReal)) φ φ : ℝ) : ℂ))
    rw [hGc, hM', hXX₀, h1, Pi.smul_apply, smul_eq_mul, h2, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  · exact hasSafeMembers_life_of_lineLocalS hh.1 hu₀.1 hh0 hc hdom hfwd hliftm hliftc hlift
      (ψ * chiC κ) (chiC κ) V.clock_cont V.clock_mono V.clock_zero V.clock_meas V.timeChange _
      (V.reach w hw) (V.reg w hw) (V.safeL w hw) (fun t => lineFiltC P 𝓖 t) (fun t => le_rfl) hℋ B hBm hBc hloc
      hBK

end InteractingSLE.Theorem14.SB.Cr
