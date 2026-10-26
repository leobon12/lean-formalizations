import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.B2.Polylog.P8RatioUniform
import SupercriticalLQGUniqueness.B2.Polylog.P2HeatAnnulusTight
import SupercriticalLQGUniqueness.B2.Polylog.P6Closing
import SupercriticalLQGUniqueness.B2.QPos.QPosClosure
import SupercriticalLQGUniqueness.B2.Final.Assembly3
import SupercriticalLQGUniqueness.Implementation.Exists_strongLQGMetric_lfppLimit

/-!
# Scale constants and the uniform median ratio

This file adapts a strong LQG metric to Pfeffer's weak class with the exact power scale
`r ↦ r^(ξQ)`, then specializes the proved polylogarithmic ratio estimate to that scale.
-/

set_option autoImplicit false

noncomputable section

open Set
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Iface
open SupercriticalLQGUniqueness.B2.Polylog
open LQGMetric (DistC)

namespace SupercriticalLFPPAS.Compare

/-- The scale family associated with the strong metric exponent. -/
def powScale (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ) :=
  fun r => ⟨(r : ℝ) ^ ((ξ : ℝ) * Q), Real.rpow_pos_of_pos r.property _⟩

/-- Multiplicativity of `powScale` in its radius argument. -/
lemma powScale_ratio (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (δ : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ)) :
    ((powScale ξ Q ⟨(δ : ℝ) * (r : ℝ), mul_pos δ.property.1 r.property⟩ : Set.Ioi (0 : ℝ)) : ℝ) /
        (powScale ξ Q r : ℝ) = (δ : ℝ) ^ ((ξ : ℝ) * Q) := by
  simp only [powScale]
  rw [Real.mul_rpow δ.property.1.le r.property.le]
  exact mul_div_cancel_right₀ _ (ne_of_gt (Real.rpow_pos_of_pos r.property _))

/-- A strong LQG metric satisfies Pfeffer's weak metric axioms with the power scale
`c_r = r^(ξQ)`. -/
theorem isPfeWeakMetric_of_isStrongLQGMetric {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) :
    IsPfeWeakMetric ξ D (powScale ξ Q) := by
  have hW : IsWeakLQGMetric ξ Q D :=
    SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  rcases hW with ⟨hMeas, hLength, hInternal, hWeyl, hTranslate, hTight⟩
  refine ⟨hMeas, hLength, hInternal, hWeyl, hTranslate, ?_, ?_⟩
  · let Λ : ℝ := |(ξ : ℝ) * Q| + 2
    have hΛ : 1 < Λ := by
      dsimp [Λ]
      have habs : 0 ≤ |(ξ : ℝ) * Q| := abs_nonneg _
      linarith
    refine ⟨Λ, hΛ, ?_⟩
    intro δ r hr
    let rI : Set.Ioi (0 : ℝ) :=
      ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩
    have hratio := powScale_ratio ξ Q δ rI
    have hδpos : 0 < (δ : ℝ) := δ.property.1
    have hδle : (δ : ℝ) ≤ 1 := le_of_lt δ.property.2
    have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
    have hΛlower : Λ⁻¹ ≤ 1 := (inv_le_one₀ hΛpos).2 (le_of_lt hΛ)
    have hΛexp : |(ξ : ℝ) * Q| ≤ Λ := by
      dsimp [Λ]
      linarith
    have hnegexp : -Λ ≤ -|(ξ : ℝ) * Q| := neg_le_neg hΛexp
    rw [hratio]
    constructor
    · calc
        Λ⁻¹ * (δ : ℝ) ^ Λ ≤ 1 * (δ : ℝ) ^ Λ :=
          mul_le_mul_of_nonneg_right hΛlower (Real.rpow_nonneg hδpos.le _)
        _ = (δ : ℝ) ^ Λ := one_mul _
        _ ≤ (δ : ℝ) ^ |(ξ : ℝ) * Q| :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle hΛexp
        _ ≤ (δ : ℝ) ^ ((ξ : ℝ) * Q) :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle (le_abs_self _)
    · calc
        (δ : ℝ) ^ ((ξ : ℝ) * Q) ≤ (δ : ℝ) ^ ( -|(ξ : ℝ) * Q|) :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle (neg_abs_le _)
        _ ≤ (δ : ℝ) ^ (-Λ) :=
          Real.rpow_le_rpow_of_exponent_ge hδpos hδle hnegexp
        _ ≤ Λ * (δ : ℝ) ^ (-Λ) :=
          by
            simpa only [one_mul] using
              (mul_le_mul_of_nonneg_right (le_of_lt hΛ)
                (Real.rpow_nonneg hδpos.le _))
  · intro Ω _ P _ h hh a ha A
    have hpow (r : Set.Ioi (0 : ℝ)) :
        ((powScale ξ Q r : Set.Ioi (0 : ℝ)) : ℝ)⁻¹ =
          (r : ℝ) ^ (-((ξ : ℝ) * Q)) := by
      dsimp [powScale]
      rw [← Real.rpow_neg r.property.le]
    simpa only [hpow] using hTight P h hh a ha A

/-- The scale ratio `κ_ε(r) = r 𝔞_(ε/r) / (r^(ξQ) 𝔞_ε)`. -/
def kappa (ξ Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε r : Set.Ioi (0 : ℝ)) : ℝ :=
  (r : ℝ) * (m ⟨(ε : ℝ) / r, Set.mem_Ioi.mpr (div_pos ε.property r.property)⟩ : ℝ) /
    ((r : ℝ) ^ (ξ * Q) * (m ε : ℝ))

/-- The paper's scale ratio is uniformly bounded on the stated mesoscopic range. -/
theorem kappa_bounds (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε)) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 1 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε r : Set.Ioi (0 : ℝ), (ε : ℝ) ≤ ε₀ →
        100 * (ε : ℝ) ^ (1 - ζ) ≤ r → (r : ℝ) ≤ 1 →
          C⁻¹ ≤ kappa (ξ : ℝ) Q m ε r ∧ kappa (ξ : ℝ) Q m ε r ≤ C := by
  let hI := SupercriticalLQGUniqueness.B2.Final.dg20Interfaces_proved
  have hP2 : PLHeatAnnulusTight := plHeatAnnulusTight_of_inputs hI.2.1 hI.1
  have hP6 : PLCompareSubset :=
    plCompareSubset_of_dg20 hI.2.1 hI.2.2.2.1
      SupercriticalLQGUniqueness.B2.QPos.dg20ExponentPositive_proved
  have hRU : PLRatioUniform := pl_ratio_uniform_of_inputs hP2 hP6 hI.1
  obtain ⟨D, hD, _⟩ :=
    SupercriticalLQGUniqueness.Implementation.exists_strongLQGMetric_lfppLimit_impl ξ Q hQ
  obtain ⟨C, hC, hRatio⟩ :=
    hRU ξ Q hQ D (powScale ξ Q) (isPfeWeakMetric_of_isStrongLQGMetric hD)
      m hm ζ hζ0 hζ1
  obtain ⟨ε₀, hε₀, hBound⟩ := hRatio 1 (by norm_num)
  refine ⟨C, hC, ε₀, hε₀, fun ε r hε hr₀ hr₁ => ?_⟩
  have h := hBound ε r hε hr₀ (le_trans hr₁ (by norm_num : (1 : ℝ) ≤ 1))
  simpa [kappa, powScale] using h

end SupercriticalLFPPAS.Compare
