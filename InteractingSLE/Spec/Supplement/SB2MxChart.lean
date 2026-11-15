/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxGlue
import InteractingSLE.Spec.Supplement.GW3LawEvery

/-!
# Chart inputs of the identification under the upper kernel

Packet PROVE-SB2-LCMEAN, round 14 (item 4: identification with `EL`). `Mx.ae_codeMatch_of_lawCode` asks that, at a
launched conditioning sample `ω₁`, the canonical chart field `Z` be kernel-almost surely the field read in the run
chart at `ω₁`. The canonical chart is the hull chart of a random compact set `K` measurable for the marks, with an
offset measurable for the marks. Two facts reduce that to a statement at `ω₁` alone:

* **`ae_ae_condExpKernel_set_eq`**: a closed random set that is dyadic-hit measurable for `𝓜` is kernel-almost surely
  the set at the conditioning sample (`Restart.iInter_dyadicCover`: a closed set is the intersection of its dyadic
  covers);
* **`isChartTransport_of_eqOn_domain`**: two domain charts of the same domain that agree on it (forward map and lift)
  transport fields alike (`GW3Law.isChartTransport_congr`).

All statements are standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Mx

open Restart

/-- Closed sets meeting the same dyadic squares are equal. -/
theorem eq_of_dyadicIdx_eq {K K' : Set ℂ} (hK : IsClosed K) (hK' : IsClosed K')
    (h : ∀ (n : ℕ) (k : ℤ × ℤ), (dyadicSquare n k ∩ K).Nonempty ↔ (dyadicSquare n k ∩ K').Nonempty) : K = K' := by
  have hc : ∀ n, dyadicCover n K = dyadicCover n K' := fun n => by
    have : dyadicIdx n K = dyadicIdx n K' := by
      ext k
      exact h n k
    simp only [dyadicCover, this]
  rw [← iInter_dyadicCover hK, ← iInter_dyadicCover hK']
  exact iInter_congr hc

/-- **A closed random set measurable for `𝓜` (dyadic hits) is kernel-almost surely the set at the conditioning
sample.** -/
theorem ae_ae_condExpKernel_set_eq {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (h𝓜 : 𝓜 ≤ mΩ) {K : Ω → Set ℂ}
    (hK : @IsDyadicHitMeasurable Ω 𝓜 K) (hKc : ∀ ω, IsClosed (K ω)) :
    ∀ᵐ ω₁ ∂μ, ∀ᵐ ω ∂(condExpKernel μ 𝓜 ω₁), K ω = K ω₁ := by
  have hS : ∀ (n : ℕ) (k : ℤ × ℤ), ∀ᵐ ω₁ ∂μ, ∀ᵐ ω ∂(condExpKernel μ 𝓜 ω₁),
      ((dyadicSquare n k ∩ K ω).Nonempty ↔ (dyadicSquare n k ∩ K ω₁).Nonempty) := by
    intro n k
    set S : Set Ω := {ω | (dyadicSquare n k ∩ K ω).Nonempty} with hSdef
    have hSm : MeasurableSet[𝓜] S := hK n k
    filter_upwards [Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := μ) h𝓜 hSm] with ω₁ hω₁
    by_cases h₁ : ω₁ ∈ S
    · have h1 : condExpKernel μ 𝓜 ω₁ Sᶜ = 0 := by
        rw [measure_compl (h𝓜 _ hSm) (measure_ne_top _ _), hω₁, indicator_of_mem h₁, measure_univ]
        simp
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with ω hω
      have hωS : ω ∈ S := by simpa using hω
      exact ⟨fun _ => h₁, fun _ => hωS⟩
    · have h0 : condExpKernel μ 𝓜 ω₁ S = 0 := by rw [hω₁, indicator_of_notMem h₁]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
      exact ⟨fun h => absurd h hω, fun h => absurd h h₁⟩
  have hS' : ∀ᵐ ω₁ ∂μ, ∀ (n : ℕ) (k : ℤ × ℤ), ∀ᵐ ω ∂(condExpKernel μ 𝓜 ω₁),
      ((dyadicSquare n k ∩ K ω).Nonempty ↔ (dyadicSquare n k ∩ K ω₁).Nonempty) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hS n k
  filter_upwards [hS'] with ω₁ hω₁
  have hall : ∀ᵐ ω ∂(condExpKernel μ 𝓜 ω₁), ∀ (n : ℕ) (k : ℤ × ℤ),
      ((dyadicSquare n k ∩ K ω).Nonempty ↔ (dyadicSquare n k ∩ K ω₁).Nonempty) :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => hω₁ n k
  filter_upwards [hall] with ω hω
  exact eq_of_dyadicIdx_eq (hKc ω) (hKc ω₁) hω

/-- **Two domain charts of the same domain that agree on it (forward map and lift) transport fields alike.** -/
theorem isChartTransport_of_eqOn_domain {D : Set ℂ} {Φ Ψ : Chart} (hΦ : IsDomainChart D Φ)
    (hΨ : IsDomainChart D Ψ) (hfwd : EqOn Φ.1 Ψ.1 D) (hlift : EqOn Φ.2.2 Ψ.2.2 D) {σ a k : ℝ}
    {g g' : DistOn upperHalfPlaneOpens} (ht : IsChartTransport Ψ σ a k g g') : IsChartTransport Φ σ a k g g' := by
  have hinv : EqOn Φ.2.1 Ψ.2.1 H := fun w hw => by
    have h1 := hΨ.inv_mem hw
    calc Φ.2.1 w = Φ.2.1 (Φ.1 (Ψ.2.1 w)) := by rw [hfwd h1, hΨ.fwd_inv hw]
      _ = Ψ.2.1 w := hΦ.inv_fwd h1
  exact GW3Law.isChartTransport_congr hΨ.isOpen (fun w hw => hΨ.inv_mem hw) hinv hfwd hlift ht

end InteractingSLE.Theorem14.SB.Mx
