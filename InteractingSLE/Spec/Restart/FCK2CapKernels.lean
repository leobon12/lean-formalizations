/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2CapTerminal
import InteractingSLE.Spec.Sec5.CrossCondGenFinalPass

/-!
# Capacity safe laws from forward marked kernels

The marked sigma algebras may vary without being monotone. Only censored
pieces of capacity events must be observable there. The optional passage is
the landed strict upper-dyadic theorem used by general-angle cross-conditioning.
No conditional kernel at the random inverse clock is assumed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
open LQGMetric LQGMetric.MarkovZB WangWu.ChartConst DomainMarkov DomainMarkov.K2 Coupling LocalSets
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Exact forward-time data for a capacity pairing. `S` is the protected live
event. Every censored capacity event has an a.s. version in the forward marks;
the bounded deterministic kernels converge along the inverse clock on `S`.
This is a named input, not an assertion that the source supplies these data. -/
def HasFCK2CapForwardKernel (P : Measure Ω) (m : MeasurableSpace Ω)
    (S : Set Ω) (X G : Ω → ℂ) : Prop :=
  let _ : MeasurableSpace Ω := mΩ
  ∃ (𝓜 : ℝ≥0 → MeasurableSpace Ω) (Av : ℝ≥0 → Set Ω)
    (K : ℝ≥0 → Ω → ℂ) (τ : Ω → ℝ≥0),
    (∀ t, 𝓜 t ≤ mΩ) ∧ Measurable τ ∧
    (∀ t ω, ω ∈ Av t → ‖K t ω‖ ≤ 1) ∧
    (∀ t, ∀ᵐ ω ∂P, ω ∈ Av t → P[X | 𝓜 t] ω = K t ω) ∧
    (∀ D, MeasurableSet[m] D → (∀ᵐ ω ∂P, ω ∈ D → ω ∈ S) →
      ∀ n k, ∃ B, MeasurableSet[𝓜 (dyq n k)] B ∧
        B =ᵐ[P] (D ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k))) ∧
    (∀ᵐ ω ∂P, ω ∈ S → (∀ᶠ n in atTop, ω ∈ Av (dyF n (τ ω))) ∧
      Tendsto (fun n => K (dyF n (τ ω)) ω) atTop (𝓝 (G ω)))

/-- The forward kernels imply the integral identity on every protected
capacity event. Neither `S` nor the forward protection events need be
measurable in the smaller capacity sigma algebra. -/
theorem setIntegral_eq_of_fcCapForwardKernel [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {S : Set Ω} {X G : Ω → ℂ}
    (hX : Integrable X P) (hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ 1)
    (h : HasFCK2CapForwardKernel (mΩ := mΩ) P m S X G) {D : Set Ω}
    (hD : MeasurableSet[m] D) (hs : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ S) :
    (∫ ω in D, X ω ∂P) = ∫ ω in D, G ω ∂P := by
  let _ : MeasurableSpace Ω := mΩ
  obtain ⟨𝓜, Av, K, τ, h𝓜, hτ, hKb, hdet, hread, hlim⟩ := h
  exact setIntegral_eq_of_dyadic hX hXb (fun n k => 𝓜 (dyq n k))
    (fun n k => h𝓜 (dyq n k)) hKb (fun n k => hdet (dyq n k)) hτ
    (hm _ hD) (hread D hD hs)
    (by filter_upwards [hs, hlim] with ω hsω hl hωD using hl (hsω hωD))

variable [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {F : Set Ω} {U : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- The Gaussian capacity safe law follows directly from deterministic
forward kernels; no intermediate safe law in a time-change filtration occurs. -/
theorem hasSafeLaw_of_fcCapForwardKernels {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hX : Measurable X)
    (hker : ∀ (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0),
      HasFCK2CapForwardKernel P (𝓕 q) {ω | ω ∈ F ∧ ω ∈ avoidSet W U ψ q}
        (fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)))
        (cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q))) :
    HasSafeLaw κ ρL ρR P 𝓕 F U W VL VR X := by
  intro ψ q D hD hs
  exact setIntegral_eq_of_fcCapForwardKernel (𝓕.le q)
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply ψ).comp hX))
    (ae_of_all P (fun ω => by rw [Complex.norm_exp_I_mul_ofReal]))
    (hker ψ q) hD hs

/-- The complement-member identities pass through the same forward kernel
construction. The projection factor is part of the limiting kernel. -/
theorem hasSafeMembers_of_fcCapForwardKernels (hX : Measurable X)
    (hker : ∀ (q : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ QuantumZipper.H →
      ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
      HasFCK2CapForwardKernel P (𝓕 q)
        {ω | ω ∈ F ∧ (q : ℝ≥0∞) < U ω ∧
          Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)}
        (fun ω => Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)))
        (fun ω => projFactor (ballsOpen Fb) f Ξ * Complex.exp (Complex.I * (X ω Ξ : ℂ)))) :
    HasSafeMembers P 𝓕 F U W X := by
  intro q Fb hFb D hD hs f Ξ
  rw [← integral_const_mul]
  exact setIntegral_eq_of_fcCapForwardKernel (𝓕.le q)
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply _).comp hX))
    (ae_of_all P (fun ω => by rw [Complex.norm_exp_I_mul_ofReal]))
    (hker q Fb hFb f Ξ) hD hs

end InteractingSLE.Restart.FCPlumb
