/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2
import InteractingSLE.Spec.Exist.Param12BorelTest

/-!
# The relative chain, part 1: conditioning on the live event

Packet PROVE-BW1-CHAIN (Proposition BW1, supplement pp. 613–615; the probabilistic chain shared with GB6). A relative
continuation (the counterflow read in a retained chart) lives only on a live event `F` of the retained past `𝒢`
(for BW1: the first piece ends at a threshold on the chosen side). Off `F` no relative driver and in particular no
Brownian motion need exist on `Ω` (`P` may even have atoms there), so K2's input (E) cannot be asked under `P`. It
can be asked under the conditioned measure `P[·|F]`, under which `F` has full measure. This file proves that this
changes nothing:

* `ae_of_ae_cond`, `ae_cond_of_ae`: almost sure statements under `P[·|F]` are those under `P` on `F`;
* `setIntegral_cond`: `∫_D f d(P[·|F]) = P(F)⁻¹ ∫_{D ∩ F} f dP`;
* **`ae_condExpKernel_cond_eq`**: for `F ∈ 𝒢`, the regular conditional kernels given `𝒢` of `P[·|F]` and of `P` agree
  `P`-almost everywhere on `F`;
* **`hasSafeLaw_cond`**, **`hasSafeMembers_cond`**: K2's inputs (S) and (L) on the live event `F` under `P` are the
  same inputs with live event `univ` under `P[·|F]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Theorem14.BW1Chain

open Restart.DomainMarkov Restart.DomainMarkov.K2

section Cond

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω}

/-- Almost sure statements under the conditioned measure hold almost surely on the event. -/
theorem ae_of_ae_cond [IsFiniteMeasure P] (hF : MeasurableSet F) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂(ProbabilityTheory.cond P F), p ω) : ∀ᵐ ω ∂P, ω ∈ F → p ω := by
  have hc : (P F)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top P F)
  rw [ProbabilityTheory.cond, ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h hc
  · exact (ae_restrict_iff' hF).1 (ae_iff.2 h)

/-- Almost sure statements on the event hold almost surely under the conditioned measure. -/
theorem ae_cond_of_ae (hF : MeasurableSet F) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, ω ∈ F → p ω) :
    ∀ᵐ ω ∂(ProbabilityTheory.cond P F), p ω := by
  rw [ProbabilityTheory.cond]
  exact Measure.ae_smul_measure ((ae_restrict_iff' hF).2 h) _

/-- **Set integrals under the conditioned measure.** -/
theorem setIntegral_cond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {D : Set Ω} (hD : MeasurableSet D)
    (f : Ω → E) :
    ∫ ω in D, f ω ∂(ProbabilityTheory.cond P F) = (P F)⁻¹.toReal • ∫ ω in D ∩ F, f ω ∂P := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure, Measure.restrict_restrict hD]

/-- Integrability transfers to the conditioned measure. -/
theorem integrable_cond {E : Type*} [NormedAddCommGroup E] {f : Ω → E} (hf : Integrable f P) :
    Integrable f (ProbabilityTheory.cond P F) := by
  by_cases hPF : P F = 0
  · rw [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 hPF, smul_zero]
    exact integrable_zero_measure
  · exact (hf.restrict (s := F)).smul_measure (ENNReal.inv_ne_top.2 hPF)

end Cond

section Kernel

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P] {F : Set Ω}

omit [StandardBorelSpace Ω] in
/-- **Conditional probabilities given `𝒢` do not see the conditioning on a `𝒢`-event.** -/
theorem condExp_indicator_cond_ae_eq (h𝒢 : 𝒢 ≤ mΩ) (hF : MeasurableSet[𝒢] F) {A : Set Ω}
    (hA : MeasurableSet A) :
    P[A.indicator (fun _ => (1 : ℝ)) | 𝒢] =ᵐ[ProbabilityTheory.cond P F]
      (ProbabilityTheory.cond P F)[A.indicator (fun _ => (1 : ℝ)) | 𝒢] := by
  have hFm : MeasurableSet F := h𝒢 _ hF
  have hXP : Integrable (A.indicator fun _ => (1 : ℝ)) P := (integrable_const (1 : ℝ)).indicator hA
  refine ae_eq_condExp_of_forall_setIntegral_eq h𝒢 (integrable_cond hXP)
    (fun s _ _ => (integrable_cond integrable_condExp).integrableOn) (fun s hs _ => ?_)
    stronglyMeasurable_condExp.aestronglyMeasurable
  rw [setIntegral_cond (h𝒢 _ hs), setIntegral_cond (h𝒢 _ hs), setIntegral_condExp h𝒢 hXP (hs.inter hF)]

/-- **The regular conditional kernels given `𝒢` of `P[·|F]` and of `P` agree almost everywhere on `F`** (`F ∈ 𝒢`;
per measurable set by `condExp_indicator_cond_ae_eq`, then on a countable generating π-system). -/
theorem ae_condExpKernel_cond_eq (h𝒢 : 𝒢 ≤ mΩ) (hF : MeasurableSet[𝒢] F) :
    ∀ᵐ ω ∂P, ω ∈ F → condExpKernel (ProbabilityTheory.cond P F) 𝒢 ω = condExpKernel P 𝒢 ω := by
  set Q := ProbabilityTheory.cond P F with hQ
  have hFm : MeasurableSet F := h𝒢 _ hF
  have hset : ∀ A : Set Ω, MeasurableSet A → ∀ᵐ ω ∂Q, condExpKernel Q 𝒢 ω A = condExpKernel P 𝒢 ω A := by
    intro A hA
    filter_upwards [condExpKernel_ae_eq_condExp (μ := Q) h𝒢 hA,
      ProbabilityTheory.cond_absolutelyContinuous.ae_le (condExpKernel_ae_eq_condExp (μ := P) h𝒢 hA),
      condExp_indicator_cond_ae_eq h𝒢 hF hA] with ω e1 e2 e3
    have hreal : (condExpKernel Q 𝒢 ω).real A = (condExpKernel P 𝒢 ω).real A := by
      rw [e1, e2]
      exact e3.symm
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal
  have : MeasurableSpace.CountablyGenerated Ω := by
    let := upgradeStandardBorel Ω
    infer_instance
  obtain ⟨Cp, hc, hpi, hgen⟩ := Exist.Param12.exists_countable_isPiSystem_generate Ω
  have hall : ∀ᵐ ω ∂Q, ∀ A ∈ Cp, condExpKernel Q 𝒢 ω A = condExpKernel P 𝒢 ω A :=
    (ae_ball_iff hc).2 fun A hA => hset A (by rw [hgen]; exact MeasurableSpace.measurableSet_generateFrom hA)
  filter_upwards [ae_of_ae_cond hFm hall] with ω hω hωF
  exact ext_of_generate_finite Cp hgen hpi (hω hωF) (by rw [measure_univ, measure_univ])

end Kernel

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {F : Set Ω} {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}

/-- **(S) on the live event is (S) with live event `univ` under the conditioned measure.** -/
theorem hasSafeLaw_cond (hF : MeasurableSet[𝓗 0] F) (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X) :
    HasSafeLaw κ ρL ρR (ProbabilityTheory.cond P F) 𝓗 univ ζ W VL VR X := by
  intro ψ q D hD hDs
  have hFq : MeasurableSet[𝓗 q] F := 𝓗.mono (zero_le (a := q)) _ hF
  have hFm : MeasurableSet F := 𝓗.le 0 _ hF
  have hP : ∀ᵐ ω ∂P, ω ∈ D ∩ F → ω ∈ F ∧ ω ∈ avoidSet W ζ ψ q := by
    filter_upwards [ae_of_ae_cond hFm hDs] with ω hω hωDF
    exact ⟨hωDF.2, (hω hωDF.2 hωDF.1).2⟩
  rw [setIntegral_cond (𝓗.le q _ hD), setIntegral_cond (𝓗.le q _ hD), hlaw ψ q (D ∩ F) (hD.inter hFq) hP]

/-- **(L) on the live event is (L) with live event `univ` under the conditioned measure.** -/
theorem hasSafeMembers_cond (hF : MeasurableSet[𝓗 0] F) (hmem : HasSafeMembers P 𝓗 F ζ W X) :
    HasSafeMembers (ProbabilityTheory.cond P F) 𝓗 univ ζ W X := by
  intro s Fb hFb D hD hDs f Ξ
  have hFs : MeasurableSet[𝓗 s] F := 𝓗.mono (zero_le (a := s)) _ hF
  have hFm : MeasurableSet F := 𝓗.le 0 _ hF
  have hP : ∀ᵐ ω ∂P, ω ∈ D ∩ F → ω ∈ F ∧ (s : ℝ≥0∞) < ζ ω ∧
      Disjoint (Coupling.ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ)) := by
    filter_upwards [ae_of_ae_cond hFm hDs] with ω hω hωDF
    exact ⟨hωDF.2, (hω hωDF.2 hωDF.1).2⟩
  rw [setIntegral_cond (𝓗.le s _ hD), setIntegral_cond (𝓗.le s _ hD),
    hmem s Fb hFb (D ∩ F) (hD.inter hFs) hP f Ξ, mul_smul_comm]

end Safe

end InteractingSLE.Theorem14.BW1Chain
