/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermLineZero
import InteractingSLE.Spec.Sec6.Prop61BMarked
import InteractingSLE.Spec.Restart.RetPlumbProofResidualLines

/-!
# The line kernel of the line set, and K2's (S) from line kernels with a supported clock

Packet PROVE-RC-TERM, second run (ruling R124).

* **`IsLineData.ae_condExp_lineKernel`**: for line data at `(t, N)` and a local-set mean `g` of the line set
  `B = fill(ηc₂[0,N]) ∪ fill(ηc₁[0,t])`, almost surely, for every test supported in `D = ℍ ∖ B` when `D` is
  preconnected and nonempty, the conditional characteristic function of the field given
  `germSigma B ⊔ retSigma76 … t N` is Gaussian with mean `g + 𝔥₀` and the zero-boundary covariance of `D`.
  Proof: the marked component kernel `Sec6.ae_condExp_exp_eq_of_component_marked` (history locality of the line set,
  `IsLineData.isHistoryAvoidanceLocal_lineSet`), the split `h = (h − 𝔥₀) + 𝔥₀`, and `connectedComponentIn D z₀ = D`.
* **`hasSafeLaw_of_lineKernel_indicator`**: `Restart.DomainMarkov.Aux79.hasSafeLaw_of_lineKernel` with the supported
  clock `F.indicator Qc` and lifetime `F.indicator ζ` (the pattern of `RetAux79.hasSafeLaw_of_retLines_indicator`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Restart.DomainMarkov Supp7 Sec7 Sec7.Lemma76F Sec7.PocketTraversal
  Exist.Staged Exist.StagedLaw Sec2.Assembly LocalSets WholeField RLC.AStopProc
open Theorem14 Theorem14.SB

section Kernel

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
  {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ : ℝ}

/-- **The line kernel of the line set** (see the module docstring). -/
theorem IsLineData.ae_condExp_lineKernel (hh : IsGFFWithBoundaryData P h b jumps)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {t N : ℝ≥0} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (d : IsLineData P h u₀ η₁ η₂ ζ₁ ζ₂ x₁ x₂ t N ηc₁ ηc₂)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (lineSet ηc₁ ηc₂ t N) (centredField h u₀) P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ D : Set ℂ, IsPreconnected D → D.Nonempty → H \ lineSet ηc₁ ηc₂ t N ω = D → tsupport φ ⊆ D →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          germSigma (lineSet ηc₁ ηc₂ t N) (centredField h u₀) ⊔ retSigma76 P η₁ η₂ ζ₁ ζ₂ t N] ω =
        Complex.exp (Complex.I * ((g ω + smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov D φ φ : ℝ) : ℂ)) := by
  classical
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hA : Measurable[mΩ, hittingSigma] (lineSet ηc₁ ηc₂ t N) :=
    d.measurable_lineSet.mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) le_rfl
  have hk := Sec6.ae_condExp_exp_eq_of_component_marked hh0 hA (d.isLocalSet_lineSet hh0)
    (retSigma76_le P η₁ η₂ ζ₁ ζ₂ t N) d.isHistoryAvoidanceLocal_lineSet hg φ
  set S := smoothDist upperHalfPlaneOpens u₀ with hS
  set 𝒦 := germSigma (lineSet ηc₁ ηc₂ t N) (centredField h u₀) ⊔ retSigma76 P η₁ η₂ ζ₁ ζ₂ t N with h𝒦
  have hsplit : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      Complex.exp (Complex.I * (S φ : ℂ)) •
        fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul, WholeField.centredField, ← Complex.exp_add]
    congr 1
    rw [sub_apply]
    push_cast
    ring
  have hsm := condExp_smul (μ := P) (Complex.exp (Complex.I * (S φ : ℂ)))
    (fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ))) 𝒦
  filter_upwards [hk, hsm] with ω hkω hsmω D hD hne hDe hsupp
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀' : z₀ ∈ H \ lineSet ηc₁ ηc₂ t N ω := hDe ▸ hz₀
  have hcc : connectedComponentIn (H \ lineSet ηc₁ ηc₂ t N ω) z₀ = D := by
    rw [hDe]
    exact hD.connectedComponentIn hz₀
  rw [hsplit]
  refine hsmω.trans ?_
  rw [Pi.smul_apply, smul_eq_mul, hkω z₀ hz₀' (hcc ▸ hsupp), hcc, add_apply, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Kernel

section Wrapper

open Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 Coupling

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **(S) from line kernels and line means with the supported clock and lifetime** (see the module docstring). -/
theorem hasSafeLaw_of_lineKernel_indicator {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω}
    (hF : MeasurableSet[𝓖 0] F) {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a k : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (Qc t)))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (F ∩ lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ :
            ℝ) : ℂ)))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → Chart.chartTransport (hc ω) 1 a k (M t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (Qc t ω) (bheProc κ ρL ρR W VL VR ω (Qc t ω)) z * ψ z) :
    HasSafeLaw κ ρL ρR P (timeChange 𝓖 (fun t => F.indicator (Qc t)) hQa) F (F.indicator ζ) W VL VR
      fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := by
  classical
  obtain ⟨hc', hm', h0'⟩ := indicator_clock_properties hQc hQm hQ0 (F := F)
  apply Aux79.hasSafeLaw_of_lineKernel hF hc hdom hfwd hliftm hliftc hh a k hc' hm' h0' hQa
    (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) ?_ ?_ ?_ 𝒢L h𝒢L h𝒢Lm M ?_ ?_
  · intro q
    filter_upwards [hreach q] with ω hr hω hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := hr hω hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · filter_upwards [hreg] with ω hr hω
    simpa only [IsForceReg, indicator_of_mem hω] using hr hω
  · intro ψ t
    rw [lineSafe_indicator]
    exact hS ψ t
  · intro t φ
    filter_upwards [hker t φ] with ω hk hω hlt hs
    simpa only [indicator_of_mem hω] using hk hω
      (by simpa only [indicator_of_mem hω] using hlt)
      (by simpa only [indicator_of_mem hω] using hs)
  · intro t ψ
    filter_upwards [hmean t ψ] with ω hm hω hs
    rw [lineSafe_indicator] at hs
    simpa only [indicator_of_mem hω] using hm hω hs.2

end Wrapper

end Term

end InteractingSLE.RealContact
