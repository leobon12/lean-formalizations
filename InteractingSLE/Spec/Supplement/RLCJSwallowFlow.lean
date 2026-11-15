/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCJSwallow
import InteractingSLE.Spec.Sec7.Prop74ProofWord

/-!
# Lemma G8's finite swallow for the reference flow line

Packet PROVE-RLC-J, item (b), in the form in which Lemma G8's proof uses it (supplement p. 500): the reference path
`α` is the angle-`θ₁` flow line from `0` of the two-height field of Proposition 7.4 (`prop74Data`, `−a` on `ℝ₋`, `C` on
`ℝ₊`), a two-seed coupling of `SLE_κ(ρ_L; ρ_R)` with `ρ_L = (a − θχ)/λ − 1`, `ρ_R = (C + θχ)/λ − 1`
(`Sec7.isFlowLine_prop74Data_iff`). For G8's `α` (`a = 2λ + θ₂χ`, `θ = θ₁`): `ρ_L = 1 + d`, `ρ_R = r ∈ (−2, κ/2 − 2)`.

**`ae_flowLine_swallow_landing`**: every coupling witnessing the flow line has, almost surely, for the fixed `x > 0`, a
finite swallowing time `σ` of `x` at which the trace is a real point `q > x` (`RLCJ.ae_swallow_landing`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RLCJ

/-- **G8's finite swallow and landing point for the reference flow line.** Let `0 < κ < 4` and let `η` be the
angle-`θ` flow line from `0` of a field with the two-height data `prop74Data a C`, with left weight
`(a − θχ)/λ − 1 > −2` and hitting right weight `−2 < (C + θχ)/λ − 1 < κ/2 − 2`. For every fixed `x > 0` there is a
witnessing two-seed coupling (driver `W`) such that almost surely `x` is swallowed by `W` at a finite time `σ` before
the lifetime, and the trace at `σ` is a real point `q > x`, beyond which every real point is still alive. -/
theorem ae_flowLine_swallow_landing {κ a C θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : -2 < (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    (hR : -2 < (C + θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    (hRc : (C + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 < κ / 2 - 2)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsFlowLine κ (Sec7.prop74Data a C) {0} 0 θ P X η ζ) {x : ℝ} (hx : 0 < x) :
    ∃ (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      (∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (X ω) (h' ω)) ∧
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR
        (fun _ => (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
        (fun _ => (C + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) P 𝓕 W VL VR B ζ h' ∧
      ∀ᵐ ω ∂P, ∃ σ : ℝ≥0, (σ : ℝ≥0∞) < ζ ω ∧ RealSwallowAt (fun s : ℝ => W s.toNNReal ω) x σ ∧
        ∃ q : ℝ, x < q ∧ η ω σ = q ∧
          ∀ y : ℝ, q < y → ∃ v, QuantumZipper.IsForwardSol (fun s : ℝ => W s.toNNReal ω) (y : ℂ) σ v := by
  obtain ⟨h', 𝓕, W, VL, VR, B, htr, hc, htrace⟩ := Sec7.isFlowLine_prop74Data_iff.1 hfl
  have hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω) := by
    filter_upwards [htrace] with ω hω
    simpa using hω
  refine ⟨h', 𝓕, W, VL, VR, B, htr, hc, ?_⟩
  exact ae_swallow_landing (rL := (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    (rR := (C + θ * QuantumZipper.chiC κ) / sleLambda κ - 1) hκ hκ4 hL hR hRc hc.1 hη hx

end InteractingSLE.RLCJ
