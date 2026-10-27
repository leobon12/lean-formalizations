import MatedCRTHarmonic.GMSCase1.ZeroConeBridge

/-!
# Cases 1–2 of [18] Proposition 4.10 in rate form

Source: [18] : "(4.40) for `h = h₁` … follows from
(4.40) for `h = h₀` (note that here the value of `α` corresponding to `h₁` is equal to `1 − 1/p`
times the value of `α` corresponding to `h₀`). In fact, for small enough `ξ = ξ(γ) > 0`, we have
`P[z ∈ B_{ε^ξ}(0)] ≍ ε^{α/2}` … Hence, (4.40) also holds with `h` sampled from the conditional law
of `h₁` given `{z ∈ B_{ε^ξ}(0)}`."

With Hölder conjugates `p, q` (`1 − 1/p = 1/q`) and the choice `ξ = α/(4q)`
(`P[z ∈ B_{ε^ξ}(0)] = ε^{α/(2q)}`), a Case 0 rate `P[(h₀, aux) ∈ G] ≤ C ε^α` gives

`P⊗λ[(h₁, aux) ∈ G | z ∈ B_{ε^ξ}(0)] ≤ case1Moment^{1/p} · C^{1/q} ε^{α/(2q)}`

(`case1_smallRoot_rate`), and the same for local events of the Case 2 field `h₂`, with the Case 0
input on the whole-plane field or on the 0-cone (`case2_smallRoot_local_rate`,
`case2_smallRoot_local_rate_of_zeroCone`). The constant `case1Moment D hγ p` is finite for
`p < 4/γ²` and depends on neither the event nor `ε`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- The rate bookkeeping: `(C ε^α)^{1/q} / (ε^{α/(4q)})² = C^{1/q} ε^{α/(2q)}`. -/
theorem case1_rate_div_eq {C α ε q : ℝ} (hC : 0 ≤ C) (hε0 : 0 < ε) (hq : 0 < q) :
    (ENNReal.ofReal (C * ε ^ α)) ^ (1 / q) / ENNReal.ofReal ((ε ^ (α / (4 * q))) ^ 2) =
      ENNReal.ofReal (C ^ (1 / q) * ε ^ (α / (2 * q))) := by
  have hεα : 0 ≤ ε ^ α := (Real.rpow_pos_of_pos hε0 α).le
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC hεα) (by positivity),
    ← ENNReal.ofReal_div_of_pos (pow_pos (Real.rpow_pos_of_pos hε0 _) 2)]
  congr 1
  rw [Real.mul_rpow hC hεα, ← Real.rpow_mul hε0.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hε0.le, mul_div_assoc]
  congr 1
  rw [div_eq_iff (Real.rpow_pos_of_pos hε0 _).ne', ← Real.rpow_add hε0]
  congr 1
  field_simp
  ring

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The small-root radius `ε^{α/(4q)}` lies in `[0, 1]`. -/
theorem smallRoot_radius_mem {α ε q : ℝ} (hα : 0 ≤ α) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hq : 0 < q) : 0 ≤ ε ^ (α / (4 * q)) ∧ ε ^ (α / (4 * q)) ≤ 1 :=
  ⟨(Real.rpow_pos_of_pos hε0 _).le, Real.rpow_le_one hε0.le hε1 (by positivity)⟩

/-- **[18] Proposition 4.10, Cases 0 → 1 with the small-root conditioning, in rate form.** -/
theorem case1_smallRoot_rate
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {G : Set WPData} (hG : MeasurableSet G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {C α ε : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : P (wpData X₀ hIG₀ U ηL ⁻¹' G) ≤ ENNReal.ofReal (C * ε ^ α)) :
    (Canon.rootedLaw P)[|smallRootEvent Ω (ε ^ (α / (4 * q)))]
        (rootedWPData γ X₀ hIG₀ U ηL ⁻¹' G) ≤
      case1Moment D hγ p ^ (1 / p) * ENNReal.ofReal (C ^ (1 / q) * ε ^ (α / (2 * q))) := by
  have hq : 0 < q := hpq.symm.pos
  obtain ⟨hr0, hr1⟩ := smallRoot_radius_mem hα hε0 hε1 hq
  refine (case1_smallRoot_event_le D hγ hG hpq hbad hr0 hr1).trans_eq ?_
  rw [mul_div_assoc, case1_rate_div_eq hC hε0 hq]

/-- **Cases 0 → 1 → 2 for local events of `h₂` on `V ⊆ 𝔻`, in rate form.** -/
theorem case2_smallRoot_local_rate
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV : (V : Set ℂ) ⊆ ball (0 : ℂ) 1)
    {G : Set (DistOn V × AuxData)} (hG : MeasurableSet G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {C α ε : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : P ((fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) ≤
      ENNReal.ofReal (C * ε ^ α)) :
    (Canon.rootedLaw P)[|smallRootEvent Ω (ε ^ (α / (4 * q)))]
        ((fun v : Ω × ℂ => restrictData V (case2WPData γ X₀ hIG₀ U ηL v)) ⁻¹' G) ≤
      case1Moment D hγ p ^ (1 / p) * ENNReal.ofReal (C ^ (1 / q) * ε ^ (α / (2 * q))) := by
  have hq : 0 < q := hpq.symm.pos
  obtain ⟨hr0, hr1⟩ := smallRoot_radius_mem hα hε0 hε1 hq
  refine (case2_smallRoot_local_event_le D hγ V hV hG hpq hbad hr0 hr1).trans_eq ?_
  rw [mul_div_assoc, case1_rate_div_eq hC hε0 hq]

/-- **Cases 0 (on the 0-cone) → 1 → 2 for local events, in rate form.** -/
theorem case2_smallRoot_local_rate_of_zeroCone
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV : V ≤ Blueprint.ballO 0 1)
    {G : Set (DistOn V × AuxData)} (hG : MeasurableSet G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {C α ε : ℝ} (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hbad : P ((fun ω => restrictData V (zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω)) ⁻¹' G) ≤
      ENNReal.ofReal (C * ε ^ α)) :
    (Canon.rootedLaw P)[|smallRootEvent Ω (ε ^ (α / (4 * q)))]
        ((fun v : Ω × ℂ => restrictData V (case2WPData γ X₀ hIG₀ U ηL v)) ⁻¹' G) ≤
      case1Moment D hγ p ^ (1 / p) * ENNReal.ofReal (C ^ (1 / q) * ε ^ (α / (2 * q))) := by
  rw [measure_restrictData_zeroConeData_preimage D hγ V hV hG] at hbad
  exact case2_smallRoot_local_rate D hγ V (subset_ball_of_le_ballO hV) hG hpq hC hα hε0 hε1 hbad

end Coupling

end MatedCRTHarmonic.GMSCase1
