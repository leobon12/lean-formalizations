import HigherDimLQGContinuity.MarginalEuclid.GridMoment
import HigherDimLQGContinuity.Endpoint.Profile

/-! The marginal Euclidean estimate under the unit pin. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Unit-pin form of Lemma 5.1. -/
theorem marginalEuclid_unit {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hConc : ConcentrationStmt d)
    {R p r : ℝ} (hR : 1 ≤ R) (hp : 1 ≤ p) (hr : 0 < r) (hr1 : r < 1) :
    ∃ ξ₁ C : ℝ, 0 < ξ₁ ∧ 0 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξ₁,
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          ∫⁻ g, supDistLU d R (rho D g).1 (euclidDistC d) ^ p ∂(normLGFLaw d) ≤
            ENNReal.ofReal (C * ξ ^ (r * p)) := by
  let β : ℝ := (1 + r) / 2
  let q : ℝ := p + 4 * d / (1 - r)
  let K : ℝ := (32 * d + 5) * (R + 1)
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hrβ : r ≤ β := by dsimp [β]; linarith
  have hq : 1 ≤ q := by
    dsimp [q]
    have : 0 ≤ 4 * (d : ℝ) / (1 - r) := by positivity
    linarith
  have hpq : p ≤ q := by
    dsimp [q]
    have : 0 ≤ 4 * (d : ℝ) / (1 - r) := by positivity
    linarith
  have hgap : r ≤ 1 - 2 * d / q := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have hden : 0 < 1 - r := by linarith
    have hq0 : 0 < q := by linarith
    have hmul : 4 * (d : ℝ) ≤ q * (1 - r) := by
      dsimp [q]
      rw [add_mul, div_mul_cancel₀ _ hden.ne']
      nlinarith
    have hfrac : 2 * (d : ℝ) / q ≤ 1 - r := by
      rw [div_le_iff₀ hq0]
      nlinarith
    linarith
  have hK : 0 < K := by
    dsimp [K]
    have : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    positivity
  obtain ⟨ξ₃, C₄, hξ₃, hC₄, hpair⟩ :=
    pairEuclid hd hφ hRot hConc (by linarith : 1 ≤ 2 * (R + 1)) hq
  obtain ⟨ξ₅, C₆, hξ₅, hC₆, hholder⟩ :=
    holderMoments hd hφ hRot hConc hR hβ hβ1 hp
  let ξ₁ : ℝ := min 1 (min ξ₃ ξ₅)
  have hξ₁ : 0 < ξ₁ := by dsimp [ξ₁]; simp [hξ₃, hξ₅]
  let Cg : ℝ := K ^ (2 * d / q) * C₄
  have hCg : 0 ≤ Cg := by dsimp [Cg]; positivity
  let E : ℝ≥0∞ := (2 : ℝ≥0∞) ^ p *
    ((2 : ℝ≥0∞) ^ p * (ENNReal.ofReal Cg ^ p + (2 : ℝ≥0∞) ^ p * ENNReal.ofReal C₆) + 1)
  have hE : E ≠ ⊤ := by dsimp [E]; finiteness
  refine ⟨ξ₁, E.toReal, hξ₁, ENNReal.toReal_nonneg, ?_⟩
  intro ξ hξ D hD
  have hξ0 : 0 < ξ := hξ.1
  have hξ1 : ξ ≤ 1 := (le_min_iff.mp hξ.2).1
  have hξ₃' : ξ ∈ Ioc (0 : ℝ) ξ₃ := ⟨hξ0, (le_min_iff.mp (le_min_iff.mp hξ.2).2).1⟩
  have hξ₅' : ξ ∈ Ioc (0 : ℝ) ξ₅ := ⟨hξ0, (le_min_iff.mp (le_min_iff.mp hξ.2).2).2⟩
  let μ := normLGFLaw d
  letI : IsProbabilityMeasure μ := (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  let G : DistRd d → ℝ≥0∞ := fun g => euclidGridSum (rho D g) R ξ q
  let H : DistRd d → ℝ≥0∞ := fun g =>
    holderConstRd (rho D g).1 (closedBall 0 (R + 1)) β
  let t : ℝ≥0∞ := ENNReal.ofReal (ξ ^ r)
  have hξr : 0 ≤ ξ ^ r := (Real.rpow_pos_of_pos hξ0 _).le
  have hmesh : ENNReal.ofReal ((ξ / 8) ^ β) ≤ t := by
    have h1 : ξ / 8 ≤ ξ := by linarith
    have h2 : (ξ / 8) ^ β ≤ ξ ^ β :=
      Real.rpow_le_rpow (by positivity) h1 hβ.le
    have h3 : ξ ^ β ≤ ξ ^ r :=
      Real.rpow_le_rpow_of_exponent_ge hξ0 hξ1 hrβ
    exact ENNReal.ofReal_le_ofReal (h2.trans h3)
  have hb : ENNReal.ofReal (ξ / 4) ≤ t := by
    apply ENNReal.ofReal_le_ofReal
    have h1 : ξ / 4 ≤ ξ := by linarith
    have h2 : ξ ≤ ξ ^ r := by
      calc ξ = ξ ^ (1 : ℝ) := (Real.rpow_one ξ).symm
        _ ≤ ξ ^ r := Real.rpow_le_rpow_of_exponent_ge hξ0 hξ1 (by linarith)
    linarith
  have hpath : ∀ g, supDistLU d R (rho D g).1 (euclidDistC d) ≤
      G g + (2 * t) * H g + t := by
    intro g
    have hfill := supDistLU_le_gridErr_add_holder (by omega : 1 ≤ d)
      (rho D g) hR hξ0 hξ1 hβ
    have hgrid := euclidGridErr_le_sum (rho D g) R ξ (by linarith : 0 < q)
    calc
      supDistLU d R (rho D g).1 (euclidDistC d) ≤
          euclidGridErr (rho D g) R ξ + 2 * H g *
            ENNReal.ofReal ((ξ / 8) ^ β) + ENNReal.ofReal (ξ / 4) := hfill
      _ ≤ G g + (2 * t) * H g + t := by
        have hh : 2 * H g * ENNReal.ofReal ((ξ / 8) ^ β) ≤ (2 * t) * H g := by
          calc
            _ ≤ 2 * H g * t := mul_le_mul_right hmesh _
            _ = _ := by ring
        exact add_le_add (add_le_add hgrid hh) hb
  have hGq : eLpNorm G (ENNReal.ofReal q) μ ≤ ENNReal.ofReal Cg * t := by
    have hraw := eLpNorm_euclidGridSum_le (s := ξ) hD.measurable hq
      (hpair ξ hξ₃' D hD)
    have hcard := euclidGrid_pair_card_le (by omega : 1 ≤ d) hR hξ0 hξ1
    have hbound := n5_grid_card_power_bound hK hC₄ hξ0 hξ1
      (by linarith : 0 < q) hgap hcard
    calc
      eLpNorm G (ENNReal.ofReal q) μ ≤
          (((euclidGrid (d := d) R ξ ×ˢ euclidGrid (d := d) R ξ).card : ℝ≥0∞) ^
            (1 / q)) * ENNReal.ofReal (C₄ * ξ) := hraw
      _ ≤ ENNReal.ofReal (Cg * ξ ^ r) := hbound
      _ = ENNReal.ofReal Cg * t := ENNReal.ofReal_mul hCg
  have hHp : ∫⁻ g, H g ^ p ∂μ ≤ ENNReal.ofReal C₆ := hholder ξ hξ₅' D hD
  have hmain := n5_lintegral_grid_fill μ
    (fun g => supDistLU d R (rho D g).1 (euclidDistC d)) G H
    (measurable_euclidGridSum hD.measurable R ξ q)
    ((measurable_holderConstRd_cont (closedBall 0 (R + 1)) β).comp
      (measurable_rho hD.measurable).subtype_val) hp hpq
    (2 * t) t (ENNReal.ofReal Cg * t) (ENNReal.ofReal C₆)
    (by finiteness) hpath hGq hHp
  have hpow : t ^ p = ENNReal.ofReal (ξ ^ (r * p)) := by
    dsimp [t]
    rw [ENNReal.ofReal_rpow_of_nonneg hξr (by linarith : 0 ≤ p),
      Real.rpow_mul hξ0.le]
  have hEbound : ∫⁻ g, supDistLU d R (rho D g).1 (euclidDistC d) ^ p ∂μ ≤
      E * ENNReal.ofReal (ξ ^ (r * p)) := by
    calc
      _ ≤ (2 : ℝ≥0∞) ^ p *
          ((2 : ℝ≥0∞) ^ p *
            ((ENNReal.ofReal Cg * t) ^ p + (2 * t) ^ p * ENNReal.ofReal C₆) + t ^ p) := hmain
      _ = E * ENNReal.ofReal (ξ ^ (r * p)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p),
          ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p), hpow]
        dsimp [E]
        ring
  calc
    ∫⁻ g, supDistLU d R (rho D g).1 (euclidDistC d) ^ p ∂μ ≤
        E * ENNReal.ofReal (ξ ^ (r * p)) := hEbound
    _ = ENNReal.ofReal (E.toReal * ξ ^ (r * p)) := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hE]

end HigherDimLQGContinuity
