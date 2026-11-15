/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R45ClockAssembly
import InteractingSLE.Spec.Sec7.Lemma76FStop

/-! # Source predictability from physical first contact -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Sec5.Aux61R45
open Restart

/-- Avoidance before a lifetime and contact at every finite endpoint identify
that lifetime with the raw open-set exit. No measurability is needed here. -/
theorem exitTime_compl_eq_of_first_contact {K : Set ℂ} {X : ℝ≥0 → ℂ} {U : ℝ≥0∞}
    (havoid : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → X t ∉ K)
    (hterminal : ∀ T : ℝ≥0, (T : ℝ≥0∞) = U → X T ∈ K) :
    InteractingSLE.exitTime Kᶜ X = U := by
  apply le_antisymm
  · by_cases hU : U = ⊤
    · rw [hU]; exact le_top
    · have hT : ((U.toNNReal : ℝ≥0) : ℝ≥0∞) = U := ENNReal.coe_toNNReal hU
      exact (InteractingSLE.exitTime_le_of_not_mem
        (not_not.2 (hterminal U.toNNReal hT))).trans_eq hT
  · apply le_iInf₂
    intro t ht
    exact le_of_not_gt fun h => ht (havoid t h)

namespace ClockSource
variable {S : Type u} [MeasurableSpace S] (D : ClockSource S)

/-- The source lifetime is predictable when a continuous physical reader
starts off a closed contact set, avoids it while alive, and reaches it at its
finite endpoint. This proves the clock hypothesis from geometric contact
facts, without any source drift or finite-word law. -/
theorem exists_announcing_of_physical_contact {ψ : ℂ → ℂ}
    (hψ : ContinuousOn ψ QuantumZipper.Hbar) {K : Set ℂ}
    (hK : IsClosed K) (hKn : K.Nonempty) (hstart : ψ (D.y : ℂ) ∉ K)
    (hbar : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → D.Γ ω t ∈ QuantumZipper.Hbar)
    (havoid : ∀ᵐ ω ∂D.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < D.U ω → ψ (D.Γ ω t) ∉ K)
    (hterminal : ∀ᵐ ω ∂D.P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = D.U ω → ψ (D.Γ ω T) ∈ K) :
    ∃ R : ℕ → S → ℝ≥0, Coupling.IsAnnouncingSeq D.driving D.P D.U R := by
  let _ := D.prob
  obtain ⟨Z, hZ0, hZc, hZa, hag⟩ := D.exists_continuous_adapted_trace
  let f : ℂ → ℂ := ψ ∘ Sec7.Lemma76F.hproj
  have hf : Continuous f := hψ.comp_continuous Sec7.Lemma76F.continuous_hproj
    Sec7.Lemma76F.hproj_mem_Hbar
  let X : ℝ≥0 → S → ℂ := fun t ω => f (Z t ω)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω => hf.comp (hZc ω)
  have hXa : ∀ t, Measurable[D.driving t] (X t) := fun t => hf.measurable.comp (hZa t)
  have hX0 : ∀ ω, X 0 ω ∉ K := by
    intro ω
    simpa only [X, f, Function.comp_apply, hZ0, Sec7.Lemma76F.hproj_ofReal] using hstart
  obtain ⟨R, hR⟩ := FlowStopIdentCMI.exists_isAnnouncingSeq_exitTime (P := D.P)
    hXa hXc hK.isOpen_compl (by simpa only [compl_compl] using hKn) hX0
  have he : (fun ω => InteractingSLE.exitTime Kᶜ (X · ω)) =ᵐ[D.P] D.U := by
    filter_upwards [hag, hbar, havoid, hterminal] with ω ha hb hv ht
    have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.U ω → X t ω = ψ (D.Γ ω t) := by
      intro t htu
      dsimp only [X, f, Function.comp_apply]
      rw [ha t htu, Sec7.Lemma76F.hproj_of_im_nonneg (hb t htu)]
    apply exitTime_compl_eq_of_first_contact
    · intro t htu
      rw [hread t htu.le]
      exact hv t htu
    · intro T hT
      rw [hread T hT.le]
      exact ht T hT
  refine ⟨R, hR.1, hR.2.1, fun n => ?_, ?_⟩
  · filter_upwards [hR.2.2.1 n, he] with ω hr heω
    rwa [← heω]
  · filter_upwards [hR.2.2.2, he] with ω hr heω
    rwa [← heω]

end ClockSource
end InteractingSLE.Sec5.Aux61R45
