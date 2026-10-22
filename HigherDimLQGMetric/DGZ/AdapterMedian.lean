import HigherDimLQGMetric.DGZ.AdapterUniform

/-!
# Real-cutoff median comparison

For all sufficiently small real cutoffs, the whole-space median is comparable to the dyadic
internal median at the nearby cutoff. Constants are uniform over white-noise realizations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

variable {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}

/-- The exact comparison `c λ_N < â_ε ≤ C λ_N` in a nearby dyadic realization. -/
theorem adapter_median_bounds_real (h : DGZHyp d κ ξ Q)
    (hHolder : HolderTightShape d κ ξ Q) (hNondeg : NondegShape d κ ξ Q)
    {β : ℝ} (hβ0 : 0 < β) (hβ : β < ξ * (Q - Real.sqrt (2 * d))) :
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
        {G : ℝ → Rd d → Ω → ℝ}, IsWhiteNoise P W →
        (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (G ε)) →
        ∀ ε ∈ Ioo (0 : ℝ) ε₀,
          ∃ N : ℕ, ∃ s : ℝ, 1 / 2 < s ∧ s ≤ 1 ∧ ε = ((2 : ℝ)⁻¹ ^ N) * s ∧
            ∃ H : ℕ → Rd d → Ω → ℝ,
              ∃ W' : WN d → Ω → ℝ, IsDyadicRealization κ P W' H ∧
              c * aQ P H ξ N 2⁻¹ < aHat P G ξ ε ∧
                aHat P G ξ ε ≤ C * aQ P H ξ N 2⁻¹ := by
  obtain ⟨L, hL, M, hM, δ, hδ, N₀, hbound⟩ :=
    adapter_median_bounds_coupled h hHolder hNondeg hβ0 hβ
  let c : ℝ := (1 / 2 : ℝ) * Real.exp (-(ξ * L)) * δ
  let C : ℝ := Real.exp (ξ * L) * M * (2 : ℝ) ^ β
  let ε₀ : ℝ := (2 : ℝ)⁻¹ ^ N₀
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < M := by linarith
    positivity
  have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hε₀1 : ε₀ ≤ 1 := by
    dsimp [ε₀]
    exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2⁻¹ : ℝ) ≤ 1)
  refine ⟨c, C, ε₀, hc, hC, hε₀, hε₀1, ?_⟩
  intro Ω _ P W G hW hG ε hε
  have hε1 : ε ≤ 1 := (le_of_lt hε.2).trans hε₀1
  have hε1lt : ε < 1 := hε.2.trans_le hε₀1
  obtain ⟨N, s, hs, hs1, hεeq⟩ := adapter_exists_dyadic_scale hε.1 hε1
  have hs0 : 0 < s := by linarith
  have hN : N₀ ≤ N := adapter_index_ge_of_eps_lt hs hεeq hε.2
  obtain ⟨H, hH, B, hB, heq⟩ := adapter_realScale_coupling h.kernel hW hε.1
    (hG ε ⟨hε.1, hε1lt⟩) N hs0 hs1 hεeq
  refine ⟨N, s, hs, hs1, hεeq, H,
    (fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hs0 f)), hH, ?_⟩
  have hb := hbound hW (hG ε ⟨hε.1, hε1lt⟩) hH hB hs hs1 hN heq
  simpa only [c, C, mul_assoc] using hb

end HigherDimLQGMetric.DGZ
