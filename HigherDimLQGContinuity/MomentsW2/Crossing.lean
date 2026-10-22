import HigherDimLQGContinuity.MomentsW2.Clusters

/-!
# Crossing lower tail from fine-cell clusters and the coarse field

The deterministic crossing reduction is `DGZ.le_acrossDist_of_smallDiam`. The estimate below
keeps the Peierls factor explicit for the later choice of scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt latPt_apply cbox)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- On a good-cluster event, a shell crossing pays one good cell. -/
theorem w2_crossing_lower_tail (hd : 2 ≤ d) (hκ : IsLFPPKernel κ)
    (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H →
        ∀ m n : ℕ, m ≤ n → ∀ r₁ r₂ A : ℝ,
          0 ≤ r₂ → r₂ < r₁ → (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 →
          ∀ N D : ℕ, r₁ / ((2 : ℝ)⁻¹ ^ m) ≤ N →
            (D : ℝ) * ((2 : ℝ)⁻¹ ^ m) + 8 * ((2 : ℝ)⁻¹ ^ m) ≤ r₁ - r₂ →
            P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ <
                c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞) /
                  Real.exp A} ≤
              P {ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), A < -(ξ * H m z ω)} +
                (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) := by
  obtain ⟨c₀, hc₀, hcluster⟩ := w2_bad_clusters hκ hN hQ hb hμ
  refine ⟨c₀, hc₀, ?_⟩
  intro ξ hξ Ω _ P W H hH m n hmn r₁ r₂ A hr₂ hr hs2 N D hN hD
  let s : ℝ := (2 : ℝ)⁻¹ ^ m
  let T : ℝ := c₀ * s * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)
  let closed : Zd d → Set Ω := w2Closed P H ξ c₀ r₁ m n
  have hs : 0 < s := by dsimp [s]; positivity
  have hφ := (hH.band n).continuous
  have hG := DGZ.isBandVersion_sub_of_realization hκ hH hmn
  have hsmall := hcluster ξ hξ Ω P W H hH m n hmn r₁ (by linarith) N D hN
  have hsub : {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ < T / Real.exp A} ⊆
      {ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), A < -(ξ * H m z ω)} ∪
        {ω | ¬ DGZ.SmallClusters {x | ω ∉ closed x} D} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, not_exists, not_and, not_lt] at hno
    obtain ⟨hF, hS⟩ := hno
    have hopen : ∀ x ∈ {x | ω ∉ closed x},
        (∀ i, s * |(x i : ℝ)| ≤ r₁) →
        T / Real.exp A ≤ DGZ.acrossDist ξ (fun z => H n z ω)
          (latPt s x) (2 * s) s := by
      intro x hx hreg
      have hT : T ≤ DGZ.acrossDist ξ (fun z => H n z ω - H m z ω)
          (latPt s x) (2 * s) s := by
        by_contra hlt
        apply hx
        exact ⟨hreg, not_le.1 hlt⟩
      have hcmp := DGZ.acrossDist_le_mul_of_exp_le (hG.continuous ω) (hφ ω)
        (by linarith : s < 2 * s)
        (C := Real.exp A) (c := latPt s x) (ξ := ξ) (Real.exp_pos A).le (by
          intro z hz
          have hz1 : z ∈ cbox (0 : Rd d) (r₁ + 1) := by
            intro i
            have h1 := hz.1 i
            have h2 := hreg i
            simp only [PiLp.zero_apply, sub_zero]
            rw [latPt_apply] at h1
            have h3 := abs_sub_abs_le_abs_sub (z i) (s * (x i : ℝ))
            rw [abs_mul, abs_of_pos hs] at h3
            have hs2' : s ≤ 1 / 2 := hs2
            linarith
          have h1 := hF z hz1
          rw [← Real.exp_add, Real.exp_le_exp]
          nlinarith)
      rw [div_le_iff₀ (Real.exp_pos A)]
      linarith
    have hlow := DGZ.le_acrossDist_of_smallDiam (by omega : 1 ≤ d)
      (hφ ω) hs hr₂ (fun C hC => (hS C hC).2) hD hopen
    exact (not_lt_of_ge hlow) hω
  calc
    P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ < T / Real.exp A}
        ≤ P ({ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), A < -(ξ * H m z ω)} ∪
          {ω | ¬ DGZ.SmallClusters {x | ω ∉ closed x} D}) := measure_mono hsub
    _ ≤ P {ω | ∃ z ∈ cbox (0 : Rd d) (r₁ + 1), A < -(ξ * H m z ω)} +
          P {ω | ¬ DGZ.SmallClusters {x | ω ∉ closed x} D} := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hsmall

end HigherDimLQGContinuity
