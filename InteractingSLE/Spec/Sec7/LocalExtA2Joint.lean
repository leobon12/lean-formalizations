/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Cond

/-!
# The local comparison of Aux. lemma 55: the conditional Cameron–Martin shift (statement)

Packet PROVE-LOCEXT-A2 (steps 3–5 interface). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L206, p. 250):
"Conditional Cameron–Martin shifting changes the mean to `C_{K_t} − P_t f` and leaves this covariance unchanged."

Under `Q = Z · P` (`srcMeasure`), the conditional law of the field off the hull at a driving stop `τ ≤ S` is the frozen
Gaussian kernel with its mean shifted by the Green potential `G_{ℍ∖K_τ} v = greenPot` of the source. In the form used to
compute `E_Q[e^{i h(φ)} | 𝓖_τ] = E_P[Z e^{i h(φ)} | 𝓖_τ] / E_P[Z | 𝓖_τ]`:

`E_P[Z e^{i h(φ)} | 𝓖_τ] = N_τ · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v) φ − ½ E_τ(φ))` on `{supp φ ∩ K_τ = ∅}`,

where `N_τ = srcMart … τ = E_P[Z | 𝓖_τ]` (`setLIntegral_srcDensity`). Mathematically this is the conditional joint Gaussian
law of `(h(φ), (h, v))` given `𝓖_τ` (means `∫ 𝔥_τ φ`, `(𝔥_τ, v)`; covariances `E_τ(φ)`, `∫ φ G_{ℍ∖K_τ} v`, `E_τ(v)`) evaluated at
the complex parameter `(1, i)`.

`SrcJointKernelStatement κ` records it as a **named statement** (consumed by PROVE-LOCEXT-C for step 5). Its proof is not in
this file; see `planning/handoffs/PROVE-LOCEXT-A2.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (fwdHull)
open LQGMetric (TestOn DistOn)

/-- **The conditional Cameron–Martin shift before the local stop** (named statement): for every ordered word with
admissible seed, seed radius `r`, coupling with the frozen optional hull specification (`Ω : Type u`), driving stopping
time `τ ≤ S` and test function `φ`, almost surely on `{supp φ ∩ K_τ = ∅}`,
`E[Z e^{i h(φ)} | 𝓖_τ] = N_τ · exp(i ∫ (𝔥_τ − G_{ℍ∖K_τ} v) φ − ½ E_τ(φ))`. -/
def SrcJointKernelStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r),
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (τ : Ω → WithTop ℝ≥0)
        (hτ : IsStoppingTime (drivingFiltration P hX) τ),
        (∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) →
        ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
            condExp hτ.measurableSpace P (fun ω' => ((srcDensity κ ρL ρR hF hr (h ω') : ℝ) : ℂ) *
                Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
              ((srcMart κ xL xR ρL ρR r W VL VR ((τ ω).untopD 0) ω : ℝ) : ℂ) *
                cfVal (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
                    (bheAt κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                      (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) z -
                    greenPot κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) z) * φ z)
                  (loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ)

end LocalExt

end InteractingSLE
