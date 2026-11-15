/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetAux79Word
import InteractingSLE.Spec.Restart.DomainMarkovAux79Line

/-!
# (S) for the retained continuation from the later-line facts

Packet PROVE-RETAUX79. `Aux79.hasSafeLaw_of_lineKernel` (PROVE-DOMAINMARKOV8) gives K2's input (S) for a chart field
`chartTransport c₀ 1 a χ h` from the line kernels (Aux. 77 at deterministic lines) and the line mean identities
(`hmean`, Aux. 79 at deterministic lines). Here `hmean` is derived, almost surely on the live event and before the
lifetime, from four facts at each line `t` (capacity time `Q = Qc t`):

* the later-line chart `cl t` is the stop-line chart followed by `f_Q` ((III-a); for the retained charts of
  `Supp7.RetData` this is `retChart_trans`, at `Q = 0` it is trivial);
* the landed later-line identification (LEMMA76G): the transport of the line mean `M t` in `cl t` is the mean of a
  sorted word `β t`;
* the boundary-data identity ((III-b) through `eqOn_mean_add_of_forceBoundaryData`): the continuation's force data at
  `Q` are `(β t).fn + a` off a finite set.

## Main results

* **`ae_hmean_of_lines`**: `hmean` of `hasSafeLaw_of_lineKernel`;
* **`hasSafeLaw_of_retLines`**: (S) for the transported field, `hasSafeLaw_of_lineKernel` with `hmean` replaced by the
  line facts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv fwdHull logDerivFwd zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Restart.RetAux79

open Chart DomainMarkov DomainMarkov.Aux79 K2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **`hmean` of `Aux79.hasSafeLaw_of_lineKernel` from the line facts** (chart composition, the later-line
identification by a sorted word, and the boundary-data identity), almost surely on `F` before the lifetime. -/
theorem ae_hmean_of_lines {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0} {c₀ : Ω → Chart} (hc : ∀ ω, (c₀ ω).IsConformal)
    (hliftc : ∀ ω, ContinuousOn (c₀ ω).2.2 (c₀ ω).dom) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) {cl : ℝ≥0 → Ω → Chart} (hcl : ∀ t ω, (cl t ω).IsConformal)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (β : ℝ≥0 → Ω → BoundaryWord) (a : ℝ)
    (hline : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω → (β t ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        chartTransport (hcl t ω) 1 0 (QuantumZipper.chiC κ) (M t ω) φ = ∫ w, (β t ω).mean w * φ w) ∧
      (∀ w ∈ H, (cl t ω).2.1 w = (c₀ ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w)) ∧
      (∀ w ∈ H, (cl t ω).2.2 ((cl t ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (Qc t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w)).im +
          (c₀ ω).2.2 ((c₀ ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S, forceBoundaryData κ ρL ρR (fun i => VL i (Qc t ω) ω - W (Qc t ω) ω)
        (fun j => VR j (Qc t ω) ω - W (Qc t ω) ω) y = (β t ω).fn y + a) :
    ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ lineSafe Qc W ζ (tsupport ψ) t → chartTransport (hc ω) 1 a (QuantumZipper.chiC κ) (M t ω) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (Qc t ω) (bheProc κ ρL ρR W VL VR ω (Qc t ω)) z * ψ z := by
  intro t ψ
  filter_upwards [hline t] with ω hω hωF hωS
  obtain ⟨hs, hid, hinv, hlift, S, hS, hdata⟩ := hω hωF hωS.1
  have hu := eqOn_mean_add_of_forceBoundaryData (isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := W) (VL := VL) (VR := VR) ω (Qc t ω)) hs a hS hdata
  refine chartTransport_eq_integral_couplingMean_of_trans κ (hc ω) (hcl t ω)
    ((hc ω).continuousOn_lift_inv (hliftc ω)) ((hWc ω).comp continuous_real_toNNReal) (by simp [hW0 ω])
    (Qc t ω).coe_nonneg hinv hlift (BoundaryWord.continuousOn_mean _) a hid hu ψ fun z hz =>
      ⟨ψ.tsupport_subset hz, fun hK => Set.disjoint_left.1 hωS.2 hz hK⟩

/-- **(S) for the retained continuation from the line facts**: `Aux79.hasSafeLaw_of_lineKernel` (lift coefficient
`χ`, height shift `a`) with its `hmean` supplied by `ae_hmean_of_lines`. -/
theorem hasSafeLaw_of_retLines [IsProbabilityMeasure P] {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω}
    (hF : MeasurableSet[𝓖 0] F) {Qc : ℝ≥0 → Ω → ℝ≥0} {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (a : ℝ)
    (hQc : ∀ ω, Continuous fun t => Qc t ω) (hQm : ∀ ω, Monotone fun t => Qc t ω) (hQ0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q ≤ Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t] (lineSafe Qc W ζ (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω)) →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (Qc t ω))) φ φ :
            ℝ) : ℂ)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {cl : ℝ≥0 → Ω → Chart}
    (hcl : ∀ t ω, (cl t ω).IsConformal) (β : ℝ≥0 → Ω → BoundaryWord)
    (hline : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (Qc t ω : ℝ≥0∞) < ζ ω → (β t ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        chartTransport (hcl t ω) 1 0 (QuantumZipper.chiC κ) (M t ω) φ = ∫ w, (β t ω).mean w * φ w) ∧
      (∀ w ∈ H, (cl t ω).2.1 w = (c ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w)) ∧
      (∀ w ∈ H, (cl t ω).2.2 ((cl t ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (Qc t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w)).im +
          (c ω).2.2 ((c ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (Qc t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S, forceBoundaryData κ ρL ρR (fun i => VL i (Qc t ω) ω - W (Qc t ω) ω)
        (fun j => VR j (Qc t ω) ω - W (Qc t ω) ω) y = (β t ω).fn y + a) :
    HasSafeLaw κ ρL ρR P 𝓗' F ζ W VL VR fun ω => chartTransport (hc ω) 1 a (QuantumZipper.chiC κ) (h ω) :=
  hasSafeLaw_of_lineKernel hF hc hdom hfwd hliftm hliftc hh a (QuantumZipper.chiC κ) hQc hQm hQ0 hQa h𝓗' hreach hreg
    hS 𝒢L h𝒢L h𝒢Lm M hker (ae_hmean_of_lines hc hliftc hWc hW0 hcl M β a hline)

end Restart.RetAux79

end InteractingSLE
