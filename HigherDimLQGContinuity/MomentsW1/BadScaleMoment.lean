import HigherDimLQGContinuity.MomentsW1.BadScaleTail
import LQGMetric.Papers.DDDF.FieldExpTail

/-! Exponential moments of the fine-field bad-scale cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP
open HigherDimLQGMetric.DGZ

private theorem wnQuadratic_exp (l : ℝ) (s : ℕ) :
    (2:ℝ)^(-(s:ℝ)^2/8) ≤
      Real.exp (8*l^2/Real.log 2) * Real.exp (-2*l*s) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsq := sq_nonneg (Real.log 2 * (s:ℝ) - 8*l)
  have hmain : Real.log 2 * (-(s:ℝ)^2/8) ≤
      8*l^2/Real.log 2 + -2*l*s := by
    have haux : Real.log 2 * (-(s:ℝ)^2/8) + 2*l*s ≤
        8*l^2/Real.log 2 := by
      apply (le_div_iff₀ hlog).2
      nlinarith [hsq]
    linarith
  nlinarith

/-- Real-valued form of the quadratic tail. -/
theorem wnBadScale_tail_real {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {ρ : ℝ}
    (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) (ξ : ℝ) {R : ℝ} (hR : 1 ≤ R) {q : ℝ≥0∞}
    (hq0 : 0 < q) (hq1 : q < 1) (n s : ℕ)
    {θ : ℝ≥0∞} (hθ1 : θ ≤ 1)
    (hεθ : (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
      θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d))
    (h3 : (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹) :
    P.real {ω | s < wnBadScale P H ξ R q n ω} ≤
      6*(2:ℝ)^(11000 + 3*(d:ℝ)^2) * (1+R)^d * (2:ℝ)^(-(s:ℝ)^2/8) := by
  have htail := wnBadScale_tail hκ hH hρ ξ hR hq0 hq1 n s hθ1 hεθ h3
  have hright : 6 * ((2:ℝ≥0∞) ^ (11000 + 3*(d:ℝ)^2) *
      ENNReal.ofReal ((1+R)^d) * (2:ℝ≥0∞)^(-(s:ℝ)^2/8)) =
      ENNReal.ofReal (6*(2:ℝ)^(11000 + 3*(d:ℝ)^2) *
        (1+R)^d * (2:ℝ)^(-(s:ℝ)^2/8)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 6*(2:ℝ)^(11000 + 3*(d:ℝ)^2)*(1+R)^d)]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 6*(2:ℝ)^(11000 + 3*(d:ℝ)^2))]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (6:ℝ))]
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ)<2),
      ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [hright] at htail
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
  have hnonneg : 0 ≤ 6*(2:ℝ)^(11000 + 3*(d:ℝ)^2) *
      (1+R)^d * (2:ℝ)^(-(s:ℝ)^2/8) := by positivity
  exact hreal.trans_eq (ENNReal.toReal_ofReal hnonneg)

/-- A quadratic tail for a natural-valued variable gives every exponential moment. -/
private theorem wnNat_expMoment_aux {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : Ω → ℕ) (hM : Measurable M)
    {B l : ℝ} (hB : 0 ≤ B) (hl : 0 < l)
    (htail : ∀ s : ℕ, P.real {ω | s < M ω} ≤ B * (2:ℝ)^(-(s:ℝ)^2/8)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (M ω:ℝ))) ∂P ≤
      ENNReal.ofReal (Real.exp l + B * Real.exp (8*l^2/Real.log 2 + l)) := by
  let D : ℝ := l*B*Real.exp (8*l^2/Real.log 2 + 2*l)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have htailExp (t : ℝ) (ht : 1 < t) :
      l * Real.exp (l*t) * P.real {ω | t ≤ (M ω:ℝ)} ≤ D * Real.exp (-l*t) := by
    let N : ℕ := ⌈t⌉₊
    let s : ℕ := N - 1
    have hN : 1 ≤ N := by
      have : 0 < N := Nat.ceil_pos.mpr (by linarith)
      omega
    have hsN : s + 1 = N := Nat.sub_add_cancel hN
    have hsNr : (s:ℝ)+1 = (N:ℝ) := by exact_mod_cast hsN
    have hslo : t-1 ≤ (s:ℝ) := by
      have := Nat.le_ceil t
      dsimp [N] at hsNr ⊢
      linarith
    have hsub : {ω | t ≤ (M ω:ℝ)} ⊆ {ω | s < M ω} := by
      intro ω hω
      have hceil : N ≤ M ω := Nat.ceil_le.mpr hω
      dsimp [s]
      omega
    have hprob : P.real {ω | t ≤ (M ω:ℝ)} ≤
        B * (2:ℝ)^(-(s:ℝ)^2/8) :=
      (measureReal_mono hsub).trans (htail s)
    have hquad := wnQuadratic_exp l s
    have hexp : Real.exp (-2*l*(s:ℝ)) ≤ Real.exp (2*l) * Real.exp (-2*l*t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hslo]
    have hprob' : P.real {ω | t ≤ (M ω:ℝ)} ≤
        B * Real.exp (8*l^2/Real.log 2) * Real.exp (2*l) * Real.exp (-2*l*t) := by
      calc
        P.real {ω | t ≤ (M ω:ℝ)} ≤ B * (2:ℝ)^(-(s:ℝ)^2/8) := hprob
        _ ≤ B * (Real.exp (8*l^2/Real.log 2) * Real.exp (-2*l*s)) :=
          mul_le_mul_of_nonneg_left hquad hB
        _ ≤ B * Real.exp (8*l^2/Real.log 2) *
            (Real.exp (2*l) * Real.exp (-2*l*t)) := by
              calc
                B * (Real.exp (8*l^2/Real.log 2) * Real.exp (-2*l*s)) =
                    (B * Real.exp (8*l^2/Real.log 2)) * Real.exp (-2*l*s) := by ring
                _ ≤ (B * Real.exp (8*l^2/Real.log 2)) *
                    (Real.exp (2*l) * Real.exp (-2*l*t)) :=
                      mul_le_mul_of_nonneg_left hexp (by positivity)
                _ = _ := by ring
        _ = _ := by ring
    calc
      l * Real.exp (l*t) * P.real {ω | t ≤ (M ω:ℝ)} ≤
          l * Real.exp (l*t) *
            (B * Real.exp (8*l^2/Real.log 2) * Real.exp (2*l) * Real.exp (-2*l*t)) := by
              gcongr
      _ = D * Real.exp (-l*t) := by
        dsimp [D]
        rw [Real.exp_add]
        have he : Real.exp (l*t) * Real.exp (-2*l*t) = Real.exp (-l*t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          l * Real.exp (l*t) *
              (B * Real.exp (8*l^2/Real.log 2) * Real.exp (2*l) * Real.exp (-2*l*t)) =
              l * B * Real.exp (8*l^2/Real.log 2) * Real.exp (2*l) *
                (Real.exp (l*t) * Real.exp (-2*l*t)) := by ring
          _ = _ := by rw [he]; ring
  have hmoment := LQGMetric.DDDF.lintegral_exp_le_of_tail
    (X := fun ω => (M ω:ℝ)) (fun ω => Nat.cast_nonneg _)
    ((measurable_of_countable (fun m : ℕ => (m:ℝ))).comp hM).aemeasurable
    hl (by norm_num : (0:ℝ) ≤ 1) hl hD htailExp
  refine hmoment.trans (ENNReal.ofReal_le_ofReal ?_)
  dsimp [D]
  have hcancel : l * B * Real.exp (8*l^2/Real.log 2 + 2*l) *
      Real.exp (-l) / l = B * Real.exp (8*l^2/Real.log 2 + l) := by
    have hex : Real.exp (8*l^2/Real.log 2 + 2*l) * Real.exp (-l) =
        Real.exp (8*l^2/Real.log 2 + l) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      l * B * Real.exp (8*l^2/Real.log 2 + 2*l) * Real.exp (-l) / l =
          (l*B) * (Real.exp (8*l^2/Real.log 2 + 2*l) * Real.exp (-l)) / l := by ring
      _ = (l*B) * Real.exp (8*l^2/Real.log 2 + l) / l := by rw [hex]
      _ = B * Real.exp (8*l^2/Real.log 2 + l) := by field_simp
  simp only [mul_one] at *
  rw [hcancel]

/-- Every positive exponential moment of the bad-scale cutoff is polynomial in the observation radius. -/
theorem wnBadScale_expMoment {d : ℕ} {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {ρ : ℝ} (hρ : ∀ y, ρ ≤ ‖y‖ → κ y = 0) {l : ℝ} (hl : 0 < l) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
      IsDyadicRealization κ P W H → ∀ (ξ R : ℝ), 1 ≤ R →
      ∀ (q : ℝ≥0∞), 0 < q → q < 1 → ∀ n : ℕ,
      ∀ (θ : ℝ≥0∞), θ ≤ 1 →
        (1 + 3 ^ d) * (2 * (d : ℝ≥0∞) * (1 - q)) ≤
          θ ^ ((⌈2 * (2 + ρ)⌉₊ + 1) ^ d) →
        (3 : ℝ≥0∞) ^ d * θ ≤ 2⁻¹ →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (l * (wnBadScale P H ξ R q n ω:ℝ))) ∂P ≤
        ENNReal.ofReal (C * (1+R)^d) := by
  let B₀ : ℝ := 6*(2:ℝ)^(11000 + 3*(d:ℝ)^2)
  let C : ℝ := Real.exp l + B₀ * Real.exp (8*l^2/Real.log 2 + l)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W H hH ξ R hR q hq0 hq1 n θ hθ1 hεθ h3
  letI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  let Q : ℝ := (1+R)^d
  have hQ : 1 ≤ Q := one_le_pow₀ (by linarith : (1:ℝ) ≤ 1+R)
  have hB : 0 ≤ B₀ * Q := mul_nonneg hB₀ (by linarith)
  have htail (s : ℕ) : P.real {ω | s < wnBadScale P H ξ R q n ω} ≤
      (B₀ * Q) * (2:ℝ)^(-(s:ℝ)^2/8) := by
    simpa [B₀, Q, mul_assoc] using
      (wnBadScale_tail_real hκ hH hρ ξ hR hq0 hq1 n s hθ1 hεθ h3)
  have hm := wnNat_expMoment_aux (wnBadScale P H ξ R q n)
    (measurable_wnBadScale hH ξ R q n) hB hl htail
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  have hfirst : Real.exp l ≤ Real.exp l * Q := by
    nlinarith [mul_nonneg (show 0 ≤ Q-1 by linarith) (Real.exp_pos l).le]
  calc
    Real.exp l + (B₀ * Q) * Real.exp (8*l^2/Real.log 2 + l) ≤
      Real.exp l * Q + (B₀ * Q) * Real.exp (8*l^2/Real.log 2 + l) := by linarith
    _ = C * (1+R)^d := by dsimp [C, Q]; ring

end HigherDimLQGContinuity
