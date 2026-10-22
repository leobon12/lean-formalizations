import HigherDimLQGMetric.Amplify.ThreeError
import HigherDimLQGMetric.Amplify.TrialFamilyLaw

/-! The finite probability bookkeeping for fine-field amplification. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- Independent fine trials, a finite coarse union bound, and one Gaussian
union bound imply the full-field certificate. -/
theorem amplify_goodTrial_of_failure_data
    {M N : ℕ} (h : Ω → DistRd d)
    (D Dt : DistRd d → ContMetric d)
    (ξ Q cs c1 ℓ δ s r K : ℝ) (w : Fin M → Fin N → Rd d)
    (m : Fin M → Fin N → MeasurableSpace Ω)
    (E B : Fin M → Fin N → Set Ω)
    (G : Set Ω)
    (hm : ∀ i, iIndep (m i) P)
    (hE : ∀ i k, AEEventIn P (m i k) (E i k))
    (hEnull : ∀ i k, NullMeasurableSet (E i k) P)
    (hBmeas : ∀ i k, MeasurableSet (B i k))
    (hGmeas : MeasurableSet G)
    (hGdef : G = {ω | ∃ i : Fin M, ∃ k : Fin N,
      K < |sphereAvg (h ω) s (r • w i k) - sphereAvg (h ω) r 0|})
    {p q η ηG : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hη0 : 0 ≤ η) (hηG0 : 0 ≤ ηG)
    (hbudget : (M : ℝ) * q ^ N + ((M * N : ℕ) : ℝ) * η + ηG ≤ 1 - p)
    (hfail : ∀ i k, P ((E i k)ᶜ) ≤ ENNReal.ofReal q)
    (hosc : ∀ i k, P (B i k) ≤ ENNReal.ofReal η)
    (hgauss : P G ≤ ENNReal.ofReal ηG)
    (htransfer : ∀ᵐ ω ∂P, ∀ i k,
      ω ∈ E i k → ω ∉ B i k →
      h ω ∈ TrialEvent D Dt ξ Q cs c1 ℓ (2 * δ) s (r • w i k)) :
    ENNReal.ofReal p ≤
      P (h ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) s r K w) := by
  let B₁ : Set Ω := {ω | ∃ i : Fin M, ∀ k : Fin N, ω ∉ E i k}
  let B₂ : Set Ω := {ω | ∃ i : Fin M, ∃ k : Fin N, ω ∈ B i k}
  have hB₁ : NullMeasurableSet B₁ P := by
    have heq : B₁ = ⋃ i : Fin M, ⋂ k : Fin N, (E i k)ᶜ := by
      ext ω
      simp only [B₁, mem_ofPred_eq, mem_iUnion, mem_iInter, mem_compl_iff]
    rw [heq]
    apply NullMeasurableSet.iUnion
    intro i
    apply NullMeasurableSet.iInter
    intro k
    exact (hEnull i k).compl
  have hB₂ : MeasurableSet B₂ := by
    have heq : B₂ = ⋃ i : Fin M, ⋃ k : Fin N, B i k := by
      ext ω
      simp only [B₂, mem_ofPred_eq, mem_iUnion]
    rw [heq]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k => hBmeas i k
  have hB₁bound : P B₁ ≤ ENNReal.ofReal ((M : ℝ) * q ^ N) := by
    have hf := amplify_box_fail_le m E hm hE hfail
    calc
      P B₁ ≤ (M : ℝ≥0∞) * (ENNReal.ofReal q) ^ N := hf
      _ = ENNReal.ofReal ((M : ℝ) * q ^ N) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_pow hq0]
            simp
  have hB₂bound : P B₂ ≤ ENNReal.ofReal (((M * N : ℕ) : ℝ) * η) := by
    have hI (i : Fin M) :
        P {ω | ∃ k : Fin N, ω ∈ B i k} ≤ (N : ℝ≥0∞) * ENNReal.ofReal η := by
      have hu := measure_iUnion_fintype_le P (fun k : Fin N => B i k)
      calc
        P {ω | ∃ k : Fin N, ω ∈ B i k} = P (⋃ k : Fin N, B i k) := by
          congr 1
          ext ω
          simp only [mem_ofPred_eq, mem_iUnion]
        _ ≤ ∑ k : Fin N, P (B i k) := hu
        _ ≤ ∑ _k : Fin N, ENNReal.ofReal η :=
          Finset.sum_le_sum fun k _ => hosc i k
        _ = (N : ℝ≥0∞) * ENNReal.ofReal η := by simp
    have hu := measure_iUnion_fintype_le P
      (fun i : Fin M => {ω | ∃ k : Fin N, ω ∈ B i k})
    calc
      P B₂ = P (⋃ i : Fin M, {ω | ∃ k : Fin N, ω ∈ B i k}) := by
        congr 1
        ext ω
        simp only [B₂, mem_ofPred_eq, mem_iUnion]
      _ ≤ ∑ i : Fin M, P {ω | ∃ k : Fin N, ω ∈ B i k} := hu
      _ ≤ ∑ _i : Fin M, (N : ℝ≥0∞) * ENNReal.ofReal η :=
        Finset.sum_le_sum fun i _ => hI i
      _ = ENNReal.ofReal (((M * N : ℕ) : ℝ) * η) := by
        simp [Nat.cast_mul, mul_assoc]
  have hGood : ∀ᵐ ω ∂P, ω ∈ (B₁ ∪ B₂ ∪ G)ᶜ →
      ω ∈ h ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) s r K w := by
    filter_upwards [htransfer] with ω ht hω
    have hω₁ : ω ∉ B₁ := fun hh => hω (Or.inl (Or.inl hh))
    have hω₂ : ω ∉ B₂ := fun hh => hω (Or.inl (Or.inr hh))
    have hω₃ : ω ∉ G := fun hh => hω (Or.inr hh)
    constructor
    · intro i
      have hi : ¬∀ k : Fin N, ω ∉ E i k := by
        intro hf
        exact hω₁ ⟨i, hf⟩
      obtain ⟨k, hk⟩ : ∃ k : Fin N, ω ∈ E i k := by
        simpa only [not_forall, not_not] using hi
      refine ⟨k, ht i k hk ?_⟩
      intro hb
      exact hω₂ ⟨i, k, hb⟩
    · intro i k
      rw [hGdef] at hω₃
      exact le_of_not_gt (fun hgt => hω₃ ⟨i, k, hgt⟩)
  exact amplify_good_of_three_errors P B₁ B₂ G
    (h ⁻¹' AmpGoodTrial D Dt ξ Q cs c1 ℓ (2 * δ) s r K w)
    hB₁ hB₂.nullMeasurableSet hGmeas.nullMeasurableSet
    (by positivity) (by positivity) hηG0 hp hp1 hbudget
    hB₁bound hB₂bound hgauss hGood

end HigherDimLQGMetric
