import HigherDimLQGContinuity.MomentsW2.Cells

/-!
# Bad fine-cell clusters in a fixed shell

This reuses the certified finite-range product bound and Peierls diameter bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The bad-cell event at scale `m`, with cells outside the relevant box declared open. -/
def w2Closed {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : ℕ → Rd d → Ω → ℝ)
    (ξ c₀ r₁ : ℝ) (m n : ℕ) (x : Zd d) : Set Ω :=
  {ω | (∀ i, (2 : ℝ)⁻¹ ^ m * |(x i : ℝ)| ≤ r₁) ∧
    DGZ.acrossDist ξ (fun z => H n z ω - H m z ω)
      (latPt ((2 : ℝ)⁻¹ ^ m) x) (2 * (2 : ℝ)⁻¹ ^ m) ((2 : ℝ)⁻¹ ^ m) <
      c₀ * (2 : ℝ)⁻¹ ^ m * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)}

/-- The bad clusters have an explicit Peierls bound, uniformly in depth and parameter. -/
theorem w2_bad_clusters (hκ : IsLFPPKernel κ)
    (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
          DGZ.IsDyadicRealization κ P W H →
          ∀ m n : ℕ, m ≤ n → ∀ r₁ : ℝ, 0 ≤ r₁ → ∀ N D : ℕ,
            r₁ / ((2 : ℝ)⁻¹ ^ m) ≤ N →
            P {ω | ¬ DGZ.SmallClusters {x | ω ∉ w2Closed P H ξ c₀ r₁ m n x} D} ≤
              (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ (D / 2) := by
  obtain ⟨ρ, -, hρ⟩ := hκ.exists_radius
  let r : ℕ := ⌈2 * (2 + ρ)⌉₊
  have hθ := HigherDimLQGMetric.DGZ.theta_pow_pos_le_one d r
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hθtop : (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hθ1
  have hθreal : 0 < (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)).toReal :=
    ENNReal.toReal_pos hθ0.ne' hθtop
  obtain ⟨c₀, hc₀, hcell⟩ := w2_cell_cross_low hκ hN hQ hb hμ hθreal
  refine ⟨c₀, hc₀, ?_⟩
  intro ξ hξ Ω _ P W H hH m n hmn r₁ hr₁ N D hN
  let s : ℝ := (2 : ℝ)⁻¹ ^ m
  have hs : 0 < s := by dsimp [s]; positivity
  have hG := DGZ.isBandVersion_sub_of_realization hκ hH hmn
  have hcl : ∀ x, P (w2Closed P H ξ c₀ r₁ m n x) ≤
      ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d) := by
    intro x
    calc
      P (w2Closed P H ξ c₀ r₁ m n x) ≤
          P {ω | DGZ.acrossDist ξ (fun z => H n z ω - H m z ω)
            (latPt s x) (2 * s) s ≤ c₀ * s * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)} := by
              apply measure_mono
              intro ω hω
              exact le_of_lt hω.2
      _ ≤ ENNReal.ofReal (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d)).toReal := by
        simpa only [s] using hcell ξ hξ Ω P W H hH m n hmn (latPt s x)
      _ = _ := ENNReal.ofReal_toReal hθtop
  have hPB : ProductBound P (w2Closed P H ξ c₀ r₁ m n) (r : ℤ) := by
    have hlocal := DGZ.productBound_of_local hκ hH.whiteNoise hρ
      (by positivity) hG hs (le_refl s) (R := 2)
      (w2Closed P H ξ c₀ r₁ m n)
      (fun x => ?_)
    · simpa only [r] using hlocal
    · have hm := DGZ.measurableSet_acrossClosed_comap hG.continuous hs ξ
          (∀ i, s * |(x i : ℝ)| ≤ r₁)
          (c₀ * s * DGZ.aQ P H ξ (n - m) (3 / 4 : ℝ≥0∞)) x
      simpa only [w2Closed, s] using hm
  have hsite : ∀ x ω, ω ∈ w2Closed P H ξ c₀ r₁ m n x → WithinInf (N : ℤ) x 0 := by
    intro x ω hω i
    have hx : s * |(x i : ℝ)| ≤ r₁ := hω.1 i
    have hx' : |(x i : ℝ)| ≤ (N : ℝ) := by
      have hdiv : |(x i : ℝ)| ≤ r₁ / s := (le_div_iff₀ hs).2 (by simpa [mul_comm] using hx)
      exact hdiv.trans hN
    simp only [Pi.zero_apply, sub_zero]
    exact_mod_cast hx'
  exact DGZ.measure_not_smallClusters_le P (w2Closed P H ξ c₀ r₁ m n) r
    (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹ ^ ((r + 1) ^ d))
    (ENNReal.ofReal (2 * 3 ^ d : ℝ)⁻¹) hcl hPB
    (HigherDimLFPP.L33.theta_le_one d) le_rfl (HigherDimLFPP.L33.three_pow_mul_theta_le d)
    N D hsite

end HigherDimLQGContinuity
