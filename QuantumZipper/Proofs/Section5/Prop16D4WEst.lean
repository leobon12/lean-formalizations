import QuantumZipper.Proofs.Section5.Prop16D4WCanon
import QuantumZipper.Proofs.Section5.Prop16WeakPerturb

/-!
# Proposition 1.6, D4⁺ʷ: the deterministic estimate for a perturbed canonical pairing

Decision D24 (`DECISIONS.md`). By `integral_canonicalOn_ofFun_add` and
`integral_canonicalOn_of_locallyGood`, with `μ = μ^U_x`, `a` the local scale of `x` and `a'` that
of `ofFun φ + x`, the difference of the two canonical area pairings of `f` is

  `Δ = ∫ e^{γφ(z)} f(z / a') dμ(z) − ∫ f(z / a) dμ(z)`.

`abs_pairing_sub_le`: if `a' ≤ 2a`, `f` vanishes outside `ball 0 R`, `|f| ≤ B`, `|φ| ≤ ε` on
`U ∩ ball 0 (2aR)`, `|f(z/a') − f(z/a)| ≤ η` and `μ(ball 0 (2aR)) ≤ M`, then
`|Δ| ≤ ((e^{γε} − 1) B + η) M`. (`a/a'` is D24's scale ratio `λ`, `φ(a·)` its `φ`, and
`μ(ball 0 (2aR)) = μ_Z(ball 0 (2R))` the canonical area of the half-ball of radius `2R`.)

`abs_canonical_pairing_sub_le`: the same bound for the canonical pairings themselves.

Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G GoodSample RegClosure LocalRule

/-- The local area measure is concentrated on `U`. -/
theorem qAreaMeasureOn_compl (γ : ℝ) (x : FieldSample) (U : Set ℂ) :
    qAreaMeasureOn γ x U Uᶜ = 0 := by
  unfold qAreaMeasureOn
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- **Deterministic estimate** for the difference of the two pairings. -/
theorem abs_pairing_sub_le {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hμU : μ Uᶜ = 0)
    {γ : ℝ} (hγ : 0 ≤ γ) {φ : ℂ → ℝ} (hφ : ContinuousOn φ U) {f : ℂ → ℝ} (hf : Continuous f)
    {B R : ℝ} (hB : ∀ w, |f w| ≤ B) (hfR : ∀ w, f w ≠ 0 → ‖w‖ < R) {a a' : ℝ} (ha : 0 < a)
    (ha' : 0 < a') (ha'2 : a' ≤ 2 * a) {ε η M : ℝ} (hε0 : 0 ≤ ε) (hM0 : 0 ≤ M)
    (hε : ∀ z ∈ U, ‖z‖ < 2 * a * R → |φ z| ≤ ε)
    (hη : ∀ z, |f (z / (a' : ℂ)) - f (z / (a : ℂ))| ≤ η)
    (hM : μ (ball 0 (2 * a * R)) ≤ ENNReal.ofReal M) :
    |∫ z, Real.exp (γ * φ z) * f (z / (a' : ℂ)) ∂μ - ∫ z, f (z / (a : ℂ)) ∂μ| ≤
      ((Real.exp (γ * ε) - 1) * B + η) * M := by
  set S := ball (0 : ℂ) (2 * a * R)
  have hSm : MeasurableSet S := measurableSet_ball
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hη 0)
  -- the supports lie in `S`
  have hsupp : ∀ (c : ℝ), 0 < c → c ≤ 2 * a → ∀ z, f (z / (c : ℂ)) ≠ 0 → z ∈ S := by
    intro c hc hc2 z hz
    have h1 := hfR _ hz
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, div_lt_iff₀ hc] at h1
    rw [mem_ball, dist_zero_right]
    have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) (hfR _ hz)
    nlinarith
  have hS' : ∀ z, z ∉ S → f (z / (a' : ℂ)) = 0 := fun z hz => by
    by_contra h; exact hz (hsupp a' ha' ha'2 z h)
  have hS : ∀ z, z ∉ S → f (z / (a : ℂ)) = 0 := fun z hz => by
    by_contra h; exact hz (hsupp a ha (by linarith) z h)
  have hfin : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hM.trans_lt ENNReal.ofReal_lt_top⟩
  have hμr : μ.restrict U = μ := Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμU)
  have haeU : ∀ᵐ z ∂μ.restrict S, z ∈ U :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hμU |>.mono fun z hz => by
      simpa using hz)
  have hc1 : ContinuousOn (fun z => Real.exp (γ * φ z) * f (z / (a' : ℂ))) U :=
    (continuousOn_const.mul hφ).rexp.mul
      (hf.comp (continuous_id.div_const _)).continuousOn
  have hm1 : AEStronglyMeasurable (fun z => Real.exp (γ * φ z) * f (z / (a' : ℂ)))
      (μ.restrict S) := by
    have := hc1.aestronglyMeasurable (μ := μ) hU.measurableSet
    rw [hμr] at this
    exact this.restrict
  have hm2 : AEStronglyMeasurable (fun z => f (z / (a : ℂ))) (μ.restrict S) :=
    (hf.comp (continuous_id.div_const _)).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂μ.restrict S,
      ‖Real.exp (γ * φ z) * f (z / (a' : ℂ)) - f (z / (a : ℂ))‖ ≤
        (Real.exp (γ * ε) - 1) * B + η := by
    filter_upwards [haeU, ae_restrict_mem hSm] with z hzU hzS
    have hzS' : ‖z‖ < 2 * a * R := by simpa [S] using hzS
    have hφz : |γ * φ z| ≤ γ * ε := by
      rw [abs_mul, abs_of_nonneg hγ]; exact mul_le_mul_of_nonneg_left (hε z hzU hzS') hγ
    have he : |Real.exp (γ * φ z) - 1| ≤ Real.exp (γ * ε) - 1 :=
      (Prop16Area.abs_exp_sub_one_le _).trans (by linarith [Real.exp_le_exp.2 hφz])
    rw [Real.norm_eq_abs]
    calc |Real.exp (γ * φ z) * f (z / (a' : ℂ)) - f (z / (a : ℂ))|
        = |(Real.exp (γ * φ z) - 1) * f (z / (a' : ℂ)) +
            (f (z / (a' : ℂ)) - f (z / (a : ℂ)))| := by ring_nf
      _ ≤ |Real.exp (γ * φ z) - 1| * |f (z / (a' : ℂ))| +
            |f (z / (a' : ℂ)) - f (z / (a : ℂ))| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (Real.exp (γ * ε) - 1) * B + η :=
          add_le_add (mul_le_mul he (hB _) (abs_nonneg _)
            (by linarith [Real.add_one_le_exp (γ * ε), mul_nonneg hγ hε0])) (hη z)
  have hb2 : ∀ᵐ z ∂μ.restrict S, ‖f (z / (a : ℂ))‖ ≤ B :=
    Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB _
  have hi2 : Integrable (fun z => f (z / (a : ℂ))) (μ.restrict S) := Integrable.of_bound hm2 B hb2
  have hi1 : Integrable (fun z => Real.exp (γ * φ z) * f (z / (a' : ℂ))) (μ.restrict S) := by
    have hd : Integrable (fun z => Real.exp (γ * φ z) * f (z / (a' : ℂ)) - f (z / (a : ℂ)))
        (μ.restrict S) := Integrable.of_bound (hm1.sub hm2) _ hbound
    refine (hd.add hi2).congr (Eventually.of_forall fun z => ?_)
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun z hz => by
      simp [hS' z hz]),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun z hz => hS z hz),
    ← integral_sub hi1 hi2]
  have hK : 0 ≤ (Real.exp (γ * ε) - 1) * B + η :=
    add_nonneg (mul_nonneg (by linarith [Real.add_one_le_exp (γ * ε), mul_nonneg hγ hε0]) hB0)
      hη0
  refine (norm_integral_le_of_norm_le_const hbound).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hK
  rw [measureReal_def, Measure.restrict_apply_univ]
  exact ENNReal.toReal_le_of_le_ofReal hM0 hM

/-- **The estimate for the canonical pairings.** For `x` locally good on `V`, `U ⊆ V ∩ ℍ` open,
`φ` continuous on `V`, positive scales `a` (of `x`) and `a' ≤ 2a` (of `ofFun φ + x`): the canonical
area pairings of `f` differ by at most `((e^{γε} − 1) B + η) M`. -/
theorem abs_canonical_pairing_sub_le {γ : ℝ} (hγ : 0 < γ) {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ V) {f : ℂ → ℝ} (hf : Continuous f) {B R : ℝ} (hB : ∀ w, |f w| ≤ B)
    (hfR : ∀ w, f w ≠ 0 → ‖w‖ < R) (ha : 0 < scaleParamOn γ x U)
    (ha' : 0 < scaleParamOn γ (ofFun φ + x) U)
    (ha'2 : scaleParamOn γ (ofFun φ + x) U ≤ 2 * scaleParamOn γ x U) {ε η M : ℝ} (hε0 : 0 ≤ ε)
    (hM0 : 0 ≤ M) (hε : ∀ z ∈ U, ‖z‖ < 2 * scaleParamOn γ x U * R → |φ z| ≤ ε)
    (hη : ∀ z, |f (z / (scaleParamOn γ (ofFun φ + x) U : ℂ)) -
      f (z / (scaleParamOn γ x U : ℂ))| ≤ η)
    (hM : qAreaMeasureOn γ x U (ball 0 (2 * scaleParamOn γ x U * R)) ≤ ENNReal.ofReal M) :
    |∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ (ofFun φ + x) U)
        (canonicalDomainOn γ (ofFun φ + x) U) -
      ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ x U) (canonicalDomainOn γ x U)| ≤
      ((Real.exp (γ * ε) - 1) * B + η) * M := by
  rw [integral_canonicalOn_ofFun_add hγ hx hU hUH hUV hφ ha' hf,
    integral_canonicalOn_of_locallyGood hγ hx hU hUH hUV ha hf]
  exact abs_pairing_sub_le hU (qAreaMeasureOn_compl γ x U) hγ.le
    (hφ.mono hUV) hf hB hfR ha ha' ha'2 hε0 hM0 hε hη hM

end Prop16Asm

end QuantumZipper
