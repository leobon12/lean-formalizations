import HigherDimLQGMetric.Thm16.LfppInput
import HigherDimLQGMetric.Sharp.TightUpper

/-! Two-sided point tails for the full LFPP metric normalized by `aEps`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_full_point_tails {d : ℕ} (hd : 3 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      (normLGFLaw d) {H |
        (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε H)) (0, e₁ d) ≤ m ∨
          M ≤ (toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε H)) (0, e₁ d)} ≤
        (8⁻¹ : ℝ≥0∞) := by
  have hd2 : 2 ≤ d := by omega
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  let X : ℝ → DistRd d → C(Rd d × Rd d, ℝ) :=
    fun ε H => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε H)
  have hT : TightOver (normLGFLaw d) X (Ioo (0 : ℝ) 1) :=
    l9c_tightFamily_toTightOver (l9c_normLfpp_tight hd hκ hξ hsub hB2 hL6a)
  let p : Rd d × Rd d := (0, e₁ d)
  have hpne : p.1 ≠ p.2 := (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
  obtain ⟨m, hm, hlo⟩ := hT.lower_offDiag (A := {p}) isCompact_singleton
    (by intro q hq; simpa only [mem_singleton_iff] using hq ▸ hpne)
    (by norm_num : (0 : ℝ≥0∞) < 16⁻¹)
  let K : Set (Rd d) := {0, e₁ d}
  have hK : IsCompact K := isCompact_singleton.insert _
  obtain ⟨M, hM, hup⟩ := hT.upper_compact hK
    (by norm_num : (0 : ℝ≥0∞) < 16⁻¹)
  refine ⟨m, M, hm, hM, ?_⟩
  intro ε hε
  let E₁ : Set (DistRd d) :=
    {H | ¬ ∀ q ∈ ({p} : Set (Rd d × Rd d)), m < X ε H q}
  let E₂ : Set (DistRd d) :=
    {H | ¬ ∀ u ∈ K, ∀ v ∈ K, X ε H (u, v) < M}
  have hsub : {H | X ε H p ≤ m ∨ M ≤ X ε H p} ⊆ E₁ ∪ E₂ := by
    intro H hH
    rcases hH with hH | hH
    · left
      intro hgood
      exact not_lt_of_ge hH (hgood p (mem_singleton p))
    · right
      intro hgood
      exact not_lt_of_ge hH (hgood 0 (by simp [K]) (e₁ d) (by simp [K]))
  change (normLGFLaw d) {H | X ε H p ≤ m ∨ M ≤ X ε H p} ≤ _
  calc
    (normLGFLaw d) {H | X ε H p ≤ m ∨ M ≤ X ε H p} ≤
        (normLGFLaw d) (E₁ ∪ E₂) := measure_mono hsub
    _ ≤ (normLGFLaw d) E₁ + (normLGFLaw d) E₂ := measure_union_le _ _
    _ ≤ (8⁻¹ : ℝ≥0∞) := by
      have h1 := hlo ε hε
      have h2 := hup ε hε
      change (normLGFLaw d) E₁ < (16⁻¹ : ℝ≥0∞) at h1
      change (normLGFLaw d) E₂ < (16⁻¹ : ℝ≥0∞) at h2
      calc
        (normLGFLaw d) E₁ + (normLGFLaw d) E₂ ≤
            (16⁻¹ : ℝ≥0∞) + 16⁻¹ := add_le_add h1.le h2.le
        _ = (8⁻¹ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_ofNat 16, ← ENNReal.ofReal_ofNat 8,
            ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 16),
            ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          norm_num

end HigherDimLQGMetric
