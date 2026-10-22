import HigherDimLQGContinuity.MomentsW1.MomentProduct
import HigherDimLQGContinuity.MomentsW1.Params

/-! The measurable envelope for the confined chain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory HigherDimLFPP HigherDimLQGMetric.DGZ
open scoped ENNReal

variable {d : ℕ}

def wnEnvelope {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (b R Q CZ D : ℝ) (H : ℕ → Rd d → Ω → ℝ)
    (ξ : ℝ) (q : ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (Real.log D + b*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω) +
    4*Real.log 2*(wnBadScale P H ξ R q n ω:ℝ))

theorem measurable_wnEnvelope {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) (b R Q CZ D ξ : ℝ) (q : ℝ≥0∞) (n : ℕ) :
    Measurable (wnEnvelope (d := d) (P := P) b R Q CZ D H ξ q n) := by
  have hZ : Measurable (wnZR (d := d) R Q CZ H) :=
    measurable_wnZR_of_realization hH R Q CZ
  have hM : Measurable (fun ω => (wnBadScale P H ξ R q n ω:ℝ)) :=
    (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_wnBadScale hH ξ R q n)
  unfold wnEnvelope
  exact Real.measurable_exp.comp
    ((measurable_const.add (measurable_const.mul
      (measurable_const.add hZ))).add (measurable_const.mul hM))

theorem wnEnvelope_ge_one {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {b R Q CZ D : ℝ} (hb : 0 ≤ b) (hR : 1 ≤ R) (hCZ : 0 ≤ CZ)
    (hD : 1 ≤ D) (H : ℕ → Rd d → Ω → ℝ) (ξ : ℝ) (q : ℝ≥0∞) (n : ℕ) (ω : Ω) :
    1 ≤ wnEnvelope (d := d) (P := P) b R Q CZ D H ξ q n ω := by
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg (by linarith)
  have hlogR : 0 ≤ Real.log (2+R) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hZ : 0 ≤ wnZR (d := d) R Q CZ H ω := ENNReal.toReal_nonneg
  have hM : 0 ≤ (wnBadScale P H ξ R q n ω:ℝ) := Nat.cast_nonneg _
  unfold wnEnvelope
  have hs : 0 ≤ Real.log D + b*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω) +
    4*Real.log 2*(wnBadScale P H ξ R q n ω:ℝ) := by positivity
  simpa using (Real.exp_le_exp.mpr hs : Real.exp 0 ≤ Real.exp _)

theorem wnEnvelope_factor {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (b R Q CZ D : ℝ) (hD : 0 < D) (H : ℕ → Rd d → Ω → ℝ)
    (ξ : ℝ) (q : ℝ≥0∞) (n : ℕ) (ω : Ω) :
    wnEnvelope (d := d) (P := P) b R Q CZ D H ξ q n ω =
      D*wnCoarseFactor (d := d) b R Q CZ H ω *
        ((2:ℝ)^(wnBadScale P H ξ R q n ω))^4 := by
  let M : ℕ := wnBadScale P H ξ R q n ω
  have hM : Real.exp (4*Real.log 2*(M:ℝ)) = ((2:ℝ)^M)^4 := by
    have hlog : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
    have he : Real.exp ((M:ℝ)*Real.log 2) = (2:ℝ)^M := by
      rw [Real.exp_nat_mul, hlog]
    rw [show 4*Real.log 2*(M:ℝ) = 4*((M:ℝ)*Real.log 2) by ring]
    simpa only [Nat.cast_ofNat, he] using (Real.exp_nat_mul ((M:ℝ)*Real.log 2) 4)
  unfold wnEnvelope wnCoarseFactor
  rw [show Real.log D + b*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω) +
      4*Real.log 2*(M:ℝ) =
      Real.log D + (b*(CZ*Real.log (2+R)+wnZR (d := d) R Q CZ H ω) +
      4*Real.log 2*(M:ℝ)) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log hD, hM]
  ring

theorem wnEnvelope_power {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (b R Q CZ D : ℝ) (H : ℕ → Rd d → Ω → ℝ)
    (ξ : ℝ) (q : ℝ≥0∞) (n : ℕ) (p : ℝ) (ω : Ω) :
    wnEnvelope (d := d) (P := P) b R Q CZ D H ξ q n ω ^ p =
      Real.exp (p*(Real.log D+b*CZ*Real.log (2+R)) +
        p*b*wnZR (d := d) R Q CZ H ω +
        4*p*Real.log 2*(wnBadScale P H ξ R q n ω:ℝ)) := by
  unfold wnEnvelope
  rw [← Real.exp_mul]
  congr 1
  ring

end HigherDimLQGContinuity
