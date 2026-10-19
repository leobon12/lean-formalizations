import LQGMetric.Papers.DDDF.P10Law
import LQGMetric.Papers.DDDF.S6P29Shift

/-!
# The time-shifted white noise and the law transfer for `φ_{m,n}` (Route U, U14; OP-3)

Blueprint Appendix A.6 (source (A.20)–(A.21)): to compare the heat-mollified pinned GFF
`h*_ε = p_{ε²/2} * h` with DDDF's field, the source changes variables `u = t + ε²` in the
white-noise representation of `h` and lets `W̃` be the *shifted white noise*. `LQGMetric`
already provides the shift (`LQGMetric.DDDF.P29WN`, built for DDDF Proposition 29):
`P29WN.tShift a (t, y) = (t + a, y)` is measure preserving, `P29WN.shiftL2 a f = f ∘ tShift a` is
a linear isometry of `L²(ℝ × ℂ)`, and `P29WN.isWhiteNoise_shift`: `f ↦ W (shiftL2 a f)` is a
white noise on the same space. Here:

* `shiftWN a W := fun f => W (P29WN.shiftL2 a f)`, i.e. `W'(dy, du) = W(dy, d(u − a))`, so
  `W'(1_{[a,∞)} k) = W(1_{[0,∞)} k(· + a, ·))`; `isWhiteNoise_shiftWN`;
* law transfer (OP-3): the laws of the continuous fields `phiMN` are the same for any two white
  noises on any two probability spaces, as random elements of `ℂ → ℝ` (`LQGMetric`'s
  `map_phi_eq`) and of `C(ℂ, ℝ)` (`map_contPhiMN_eq`); hence so are the laws of every measurable
  functional of the field (`map_comp_contPhiMN_eq`, moments: `lintegral_comp_contPhiMN_eq`), of
  the crossing lengths
  (`map_lenObs_phiMN_eq`) and the quantile quantities `ellN`, `ellBarN`, `LambdaN`, `lambdaN`
  (`ellN_eq_of_isWhiteNoise`, …). The case of `shiftWN` is `lambdaN_shiftWN` etc.

Standard measure theory; own routine steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace GaussianLQG
namespace FieldCmp

open LQGMetric LQGMetric.WhiteNoise LQGMetric.DDDF

variable {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂] {P : Measure Ω}
  {P₂ : Measure Ω₂}

/-! ### The shifted white noise -/

/-- The white noise shifted in time by `a`: `shiftWN a W f = W (f(· + a, ·))`, i.e.
`W'(dy, du) = W(dy, d(u − a))` (source (A.20)–(A.21), the noise `W̃` after `u = t + ε²`). -/
abbrev shiftWN (a : ℝ) (W : WNSpace → Ω → ℝ) : WNSpace → Ω → ℝ :=
  fun f => W (P29WN.shiftL2 a f)

/-- **The shifted white noise is a white noise** (on the same probability space;
`LQGMetric`'s `P29WN.isWhiteNoise_shift`). -/
theorem isWhiteNoise_shiftWN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a : ℝ) :
    IsWhiteNoise P (shiftWN a W) :=
  P29WN.isWhiteNoise_shift hW a

/-! ### Law transfer for the fields `φ_{m,n}` (OP-3) -/

/-- `φ_{m,n}` as a random element of `C(ℂ, ℝ)` (the chosen continuous version `phiMN`). -/
def contPhiMN (W : WNSpace → Ω → ℝ) (P : Measure Ω) (m n : ℕ) (hc : ∀ ω, Continuous fun x =>
    phiMN W P m n x ω) (ω : Ω) : C(ℂ, ℝ) :=
  ⟨fun x => phiMN W P m n x ω, hc ω⟩

lemma measurable_contPhiMN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {m n : ℕ}
    (hmn : m ≤ n) (hc : ∀ ω, Continuous fun x => phiMN W P m n x ω) :
    Measurable (contPhiMN W P m n hc) := by
  intro S hS
  rw [measurableSpace_continuousMap_eq_comap] at hS
  obtain ⟨T, hT, rfl⟩ := hS
  exact (measurable_pi_iff.2 (isPhiVersion_phiMN hW hmn).meas) hT

/-- **Law transfer on `C(ℂ, ℝ)`**: the law of the continuous field `φ_{m,n}` is the same for
any two white noises, on any two probability spaces. -/
theorem map_contPhiMN_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) {m n : ℕ} (hmn : m ≤ n)
    (hcW : ∀ ω, Continuous fun x => phiMN W P m n x ω)
    (hcV : ∀ ω, Continuous fun x => phiMN V P₂ m n x ω) :
    P.map (contPhiMN W P m n hcW) = P₂.map (contPhiMN V P₂ m n hcV) := by
  have h1 := isPhiVersion_phiMN hW hmn
  have h2 := isPhiVersion_phiMN hV hmn
  have hlaw := map_phi_eq hW hV _ _ h1.meas h2.meas h1.ae_eq h2.ae_eq
  ext S hS
  rw [Measure.map_apply (measurable_contPhiMN hW hmn hcW) hS,
    Measure.map_apply (measurable_contPhiMN hV hmn hcV) hS]
  have hS' := hS
  rw [measurableSpace_continuousMap_eq_comap] at hS'
  obtain ⟨T, hT, rfl⟩ := hS'
  have e1 : contPhiMN W P m n hcW ⁻¹' ((fun f : C(ℂ, ℝ) => (f : ℂ → ℝ)) ⁻¹' T) =
      (fun ω => (phiMN W P m n · ω)) ⁻¹' T := rfl
  have e2 : contPhiMN V P₂ m n hcV ⁻¹' ((fun f : C(ℂ, ℝ) => (f : ℂ → ℝ)) ⁻¹' T) =
      (fun ω => (phiMN V P₂ m n · ω)) ⁻¹' T := rfl
  rw [e1, e2, ← Measure.map_apply (measurable_pi_iff.2 h1.meas) hT,
    ← Measure.map_apply (measurable_pi_iff.2 h2.meas) hT, hlaw]

/-- **Law transfer of `φ`-functionals**: for every measurable functional `F` of a continuous
field, `F(φ_{m,n})` has the same law for any two white noises. -/
theorem map_comp_contPhiMN_eq {β : Type*} [MeasurableSpace β] {F : C(ℂ, ℝ) → β}
    (hF : Measurable F) {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) {m n : ℕ} (hmn : m ≤ n)
    (hcW : ∀ ω, Continuous fun x => phiMN W P m n x ω)
    (hcV : ∀ ω, Continuous fun x => phiMN V P₂ m n x ω) :
    P.map (fun ω => F (contPhiMN W P m n hcW ω)) =
      P₂.map (fun ω => F (contPhiMN V P₂ m n hcV ω)) := by
  have e1 : (fun ω => F (contPhiMN W P m n hcW ω)) = F ∘ contPhiMN W P m n hcW := rfl
  have e2 : (fun ω => F (contPhiMN V P₂ m n hcV ω)) = F ∘ contPhiMN V P₂ m n hcV := rfl
  rw [e1, e2, ← Measure.map_map hF (measurable_contPhiMN hW hmn hcW),
    ← Measure.map_map hF (measurable_contPhiMN hV hmn hcV), map_contPhiMN_eq hW hV hmn hcW hcV]

/-- **Moment transfer**: `E[F(φ_{m,n})]` is the same for any two white noises, for every
measurable `F : C(ℂ, ℝ) → [0, ∞]`. -/
theorem lintegral_comp_contPhiMN_eq {F : C(ℂ, ℝ) → ℝ≥0∞} (hF : Measurable F)
    {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ} (hW : IsWhiteNoise P W)
    (hV : IsWhiteNoise P₂ V) {m n : ℕ} (hmn : m ≤ n)
    (hcW : ∀ ω, Continuous fun x => phiMN W P m n x ω)
    (hcV : ∀ ω, Continuous fun x => phiMN V P₂ m n x ω) :
    ∫⁻ ω, F (contPhiMN W P m n hcW ω) ∂P = ∫⁻ ω, F (contPhiMN V P₂ m n hcV ω) ∂P₂ := by
  rw [← lintegral_map hF (measurable_contPhiMN hW hmn hcW),
    ← lintegral_map hF (measurable_contPhiMN hV hmn hcV), map_contPhiMN_eq hW hV hmn hcW hcV]

/-- **Law transfer of crossing lengths** of `φ_{m,n}`. -/
theorem map_lenObs_phiMN_eq {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (R : MarkedRect) {m n : ℕ}
    (hmn : m ≤ n) :
    P.map (lenObs ξ (phiMN W P m n) R) = P₂.map (lenObs ξ (phiMN V P₂ m n) R) := by
  have h1 := isPhiVersion_phiMN hW hmn
  have h2 := isPhiVersion_phiMN hV hmn
  have hab : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  ext S hS
  rw [Measure.map_apply (measurable_lenObs h1.cont h1.meas R) hS,
    Measure.map_apply (measurable_lenObs h2.cont h2.meas R) hS]
  have hS' : MeasurableSet (ENNReal.toReal ⁻¹' S) := ENNReal.measurable_toReal hS
  exact measure_crossLenIn_phiVer_eq (ξ := ξ) (A := R.side₁) (B := R.side₂) R.isCompact_toSet
    hW hV (by positivity) hab hS'

/-- `ℓ_k(p)` does not depend on the white noise. -/
theorem ellN_eq_of_isWhiteNoise {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (k : ℕ) (p : ℝ≥0∞) :
    ellN ξ W P k p = ellN ξ V P₂ k p := by
  unfold ellN ellQ
  rw [map_lenObs_phiMN_eq hW hV ξ (rectAB 1 1) (Nat.zero_le k)]

/-- `ℓ̄_k(p)` does not depend on the white noise. -/
theorem ellBarN_eq_of_isWhiteNoise {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (k : ℕ) (p : ℝ≥0∞) :
    ellBarN ξ W P k p = ellBarN ξ V P₂ k p := by
  unfold ellBarN ellBarQ ellQ
  rw [map_lenObs_phiMN_eq hW hV ξ (rectAB 1 1) (Nat.zero_le k)]

/-- `Λ_n(p)` does not depend on the white noise. -/
theorem LambdaN_eq_of_isWhiteNoise {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (n : ℕ) (p : ℝ≥0∞) :
    LambdaN ξ W P n p = LambdaN ξ V P₂ n p := by
  unfold LambdaN
  congr 1
  funext k
  rw [ellN_eq_of_isWhiteNoise hW hV, ellBarN_eq_of_isWhiteNoise hW hV]

/-- `λ_n` (the lower median of `L^{(n)}_{1,1}`) does not depend on the white noise. -/
theorem lambdaN_eq_of_isWhiteNoise {W : WNSpace → Ω → ℝ} {V : WNSpace → Ω₂ → ℝ}
    (hW : IsWhiteNoise P W) (hV : IsWhiteNoise P₂ V) (ξ : ℝ) (n : ℕ) :
    lambdaN ξ W P n = lambdaN ξ V P₂ n := by
  unfold lambdaN lenN lenMN
  rw [map_lenObs_phiMN_eq hW hV ξ (rectAB 1 1) (Nat.zero_le n)]

/-! ### The case of the shifted white noise -/

/-- The law of `φ_{m,n}` on `ℂ → ℝ` is the same for `shiftWN a W` and `W`. -/
theorem map_phiMN_shiftWN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a : ℝ) {m n : ℕ}
    (hmn : m ≤ n) :
    P.map (fun ω => (phiMN (shiftWN a W) P m n · ω)) = P.map (fun ω => (phiMN W P m n · ω)) := by
  have h1 := isPhiVersion_phiMN (isWhiteNoise_shiftWN hW a) hmn
  have h2 := isPhiVersion_phiMN hW hmn
  exact map_phi_eq (isWhiteNoise_shiftWN hW a) hW _ _ h1.meas h2.meas h1.ae_eq h2.ae_eq

/-- Moments of measurable functionals of `φ_{m,n}` are the same for `shiftWN a W` and `W`. -/
theorem lintegral_comp_contPhiMN_shiftWN {F : C(ℂ, ℝ) → ℝ≥0∞} (hF : Measurable F)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a : ℝ) {m n : ℕ} (hmn : m ≤ n)
    (hc' : ∀ ω, Continuous fun x => phiMN (shiftWN a W) P m n x ω)
    (hc : ∀ ω, Continuous fun x => phiMN W P m n x ω) :
    ∫⁻ ω, F (contPhiMN (shiftWN a W) P m n hc' ω) ∂P = ∫⁻ ω, F (contPhiMN W P m n hc ω) ∂P :=
  lintegral_comp_contPhiMN_eq hF (isWhiteNoise_shiftWN hW a) hW hmn hc' hc

theorem lambdaN_shiftWN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a ξ : ℝ) (n : ℕ) :
    lambdaN ξ (shiftWN a W) P n = lambdaN ξ W P n :=
  lambdaN_eq_of_isWhiteNoise (isWhiteNoise_shiftWN hW a) hW ξ n

theorem ellN_shiftWN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a ξ : ℝ) (k : ℕ)
    (p : ℝ≥0∞) : ellN ξ (shiftWN a W) P k p = ellN ξ W P k p :=
  ellN_eq_of_isWhiteNoise (isWhiteNoise_shiftWN hW a) hW ξ k p

theorem LambdaN_shiftWN {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (a ξ : ℝ) (n : ℕ)
    (p : ℝ≥0∞) : LambdaN ξ (shiftWN a W) P n p = LambdaN ξ W P n p :=
  LambdaN_eq_of_isWhiteNoise (isWhiteNoise_shiftWN hW a) hW ξ n p

end FieldCmp
end GaussianLQG
