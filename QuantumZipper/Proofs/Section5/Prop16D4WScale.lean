import QuantumZipper.Proofs.Section5.Prop16D4WClause2

/-!
# Proposition 1.6, D4⁺ʷ input `hscale`: the scale ratio tends to `1`

Decision D24 (`DECISIONS.md`): "`λ → 1` in probability (both fields have unit area in `B₁`, and
the wedge area of `B_s` is continuous and increasing in `s`)". Here:

* `qAreaMeasureOn_ofFun_add_le`, `le_qAreaMeasureOn_ofFun_add`: if `|φ| ≤ ε` on `A ∩ U`, the local
  area measures of `ofFun φ + x` and `x` on `A` agree up to the factors `e^{±γε}`;
* `scale_sandwich`: if the local area of `x` in `B_{(1−κ)a} ∩ ℍ` is `< c⁻¹` and in
  `B_{(1+κ)a} ∩ ℍ` is `> c` (`a` the scale of `x`), and the two measures agree up to the factors
  `c^{±1}` there, then the scale `a'` of the perturbed field satisfies `0 < a'`, `|a' − a| ≤ κa`;
* `tendsto_scale_ratio`: `hscale` of `tendsto_canonical_pairing_close` from `φ(a·) → 0`, the
  positivity of `a` in probability, and a **growth input** `hgrow` on the unperturbed field only:
  for `0 < κ < 1` and `θ > 0` there is `c > 1` with, eventually,
  `Q{¬(μ_x(B_{(1−κ)a} ∩ ℍ) < c⁻¹ ∧ c < μ_x(B_{(1+κ)a} ∩ ℍ))} ≤ θ` (in canonical coordinates:
  the canonical area of `B_s ∩ ℍ` is strictly increasing across `s = 1`, uniformly in
  probability; for the wedge this is the statement "continuous and strictly increasing at 1").

Own elementary argument (AGENT_GUIDE cost rule), following D24.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G GoodSample RegClosure LocalRule

/-- Comparison of local area measures under a bounded perturbation (both directions). -/
theorem qAreaMeasureOn_ofFun_add_le_ge {γ : ℝ} (hγ : 0 ≤ γ) {V U : Set ℂ} {x : FieldSample}
    (hx : IsLocallyGoodOn γ V x) (hU : IsOpen U) (hUH : U ⊆ H) (hUV : U ⊆ V) {φ : ℂ → ℝ}
    (hφ : ContinuousOn φ V) {A : Set ℂ} (hA : MeasurableSet A) {ε : ℝ}
    (hAε : ∀ z ∈ A ∩ U, |φ z| ≤ ε) :
    qAreaMeasureOn γ (ofFun φ + x) U A ≤
        ENNReal.ofReal (Real.exp (γ * ε)) * qAreaMeasureOn γ x U A ∧
      ENNReal.ofReal (Real.exp (-(γ * ε))) * qAreaMeasureOn γ x U A ≤
        qAreaMeasureOn γ (ofFun φ + x) U A := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, h⟩ := hx
  have hUW : U ⊆ W := fun z hz => by rw [← hWV] at hUV; exact (hUV hz).1
  have hψ' : ContinuousOn ψ (W ∩ Hbar) := by rw [hWV]; exact hψ
  have hψφ : ContinuousOn (fun z => ψ z + φ z) (W ∩ Hbar) := by rw [hWV]; exact hψ.add hφ
  rw [qAreaMeasureOn_eq_withDensity_of_agree hWo hy hψφ (circAgree_ofFun_add hWV hψ hφ h) hU hUH
      hUW, qAreaMeasureOn_eq_withDensity_of_agree hWo hy hψ' h hU hUH hUW,
    withDensity_apply _ hA, withDensity_apply _ hA]
  have hae : ∀ᵐ z ∂((qAreaMeasure γ y).restrict U).restrict A, z ∈ A ∩ U := by
    filter_upwards [ae_restrict_mem hA,
      ae_restrict_of_ae (ae_restrict_mem hU.measurableSet)] with z h1 h2
    exact ⟨h1, h2⟩
  have hfac : ∀ z, ENNReal.ofReal (Real.exp (γ * (ψ z + φ z))) =
      ENNReal.ofReal (Real.exp (γ * φ z)) * ENNReal.ofReal (Real.exp (γ * ψ z)) := fun z => by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [hfac]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) _
    exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hAε z hz)) hγ
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [hfac]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) _
    have := neg_abs_le (φ z)
    have h2 := hAε z hz
    nlinarith

/-- **Scale sandwich** (deterministic). -/
theorem scale_sandwich {γ : ℝ} {x x' : FieldSample} {U : Set ℂ} {κ c : ℝ}
    (ha : 0 < scaleParamOn γ x U) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hc : 0 < c)
    (hup : qAreaMeasureOn γ x' U (ball 0 ((1 - κ) * scaleParamOn γ x U) ∩ H) ≤
      ENNReal.ofReal c * qAreaMeasureOn γ x U (ball 0 ((1 - κ) * scaleParamOn γ x U) ∩ H))
    (hlo : ENNReal.ofReal c⁻¹ *
        qAreaMeasureOn γ x U (ball 0 ((1 + κ) * scaleParamOn γ x U) ∩ H) ≤
      qAreaMeasureOn γ x' U (ball 0 ((1 + κ) * scaleParamOn γ x U) ∩ H))
    (h1 : qAreaMeasureOn γ x U (ball 0 ((1 - κ) * scaleParamOn γ x U) ∩ H) < ENNReal.ofReal c⁻¹)
    (h2 : ENNReal.ofReal c < qAreaMeasureOn γ x U (ball 0 ((1 + κ) * scaleParamOn γ x U) ∩ H)) :
    0 < scaleParamOn γ x' U ∧
      |scaleParamOn γ x' U - scaleParamOn γ x U| ≤ κ * scaleParamOn γ x U := by
  set a := scaleParamOn γ x U
  set S := {r : ℝ | 0 < r ∧ 1 ≤ qAreaMeasureOn γ x' U (ball 0 r ∩ H)}
  have hcc : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  -- upper bound: `(1 + κ) a ∈ S`
  have hup_mem : (1 + κ) * a ∈ S := by
    refine ⟨by positivity, ?_⟩
    refine le_trans ?_ hlo
    rw [← hcc]; exact mul_le_mul_right h2.le _
  have hbdd : BddBelow S := ⟨0, fun r hr => hr.1.le⟩
  have hle : scaleParamOn γ x' U ≤ (1 + κ) * a := csInf_le hbdd hup_mem
  -- lower bound: every element of `S` is `≥ (1 - κ) a`
  have hge : (1 - κ) * a ≤ scaleParamOn γ x' U := by
    refine le_csInf ⟨_, hup_mem⟩ fun r hr => ?_
    by_contra hlt
    have hm := measure_mono (μ := qAreaMeasureOn γ x' U)
      (inter_subset_inter_left H (ball_subset_ball (x := (0 : ℂ)) (not_le.1 hlt).le))
    have : qAreaMeasureOn γ x' U (ball 0 ((1 - κ) * a) ∩ H) < 1 := by
      refine hup.trans_lt ?_
      calc ENNReal.ofReal c * qAreaMeasureOn γ x U (ball 0 ((1 - κ) * a) ∩ H)
          < ENNReal.ofReal c * ENNReal.ofReal c⁻¹ :=
            by rw [mul_comm (ENNReal.ofReal c), mul_comm (ENNReal.ofReal c)]
               exact ENNReal.mul_lt_mul_left (by simpa using hc) ENNReal.ofReal_ne_top h1
        _ = 1 := by rw [mul_comm, hcc]
    exact absurd (hr.2.trans hm) (not_le.2 this)
  refine ⟨lt_of_lt_of_le (by nlinarith) hge, abs_le.2 ⟨by nlinarith, by nlinarith⟩⟩

/-- **`hscale` from the growth input** (see the module docstring). -/
theorem tendsto_scale_ratio {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {γ : ℝ} (hγ : 0 < γ) (x : ℝ → Ω → FieldSample) (φ : ℝ → Ω → ℂ → ℝ)
    (U V : ℝ → Ω → Set ℂ)
    (hloc : ∀ C, ∀ᵐ ω ∂Q, IsLocallyGoodOn γ (V C ω) (x C ω) ∧ IsOpen (U C ω) ∧ U C ω ⊆ H ∧
      U C ω ⊆ V C ω ∧ ContinuousOn (φ C ω) (V C ω))
    (hφ : ∀ ρ > 0, ∀ ε > 0, Tendsto (fun C => Q {ω | ¬ ∀ z ∈ U C ω,
      ‖z‖ < ρ * scaleParamOn γ (x C ω) (U C ω) → |φ C ω z| ≤ ε}) atTop (𝓝 0))
    (hpos : Tendsto (fun C => Q {ω | ¬ 0 < scaleParamOn γ (x C ω) (U C ω)}) atTop (𝓝 0))
    (hgrow : ∀ κ > 0, κ < 1 → ∀ θ > 0, ∃ c > 1, ∀ᶠ C in atTop, Q {ω | ¬ (
      qAreaMeasureOn γ (x C ω) (U C ω) (ball 0 ((1 - κ) * scaleParamOn γ (x C ω) (U C ω)) ∩ H) <
        ENNReal.ofReal c⁻¹ ∧ ENNReal.ofReal c <
      qAreaMeasureOn γ (x C ω) (U C ω) (ball 0 ((1 + κ) * scaleParamOn γ (x C ω) (U C ω)) ∩ H))}
        ≤ θ) :
    ∀ κ > 0, Tendsto (fun C => Q {ω | ¬ (0 < scaleParamOn γ (x C ω) (U C ω) ∧
      0 < scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) ∧
      |scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) - scaleParamOn γ (x C ω) (U C ω)| ≤
        κ * scaleParamOn γ (x C ω) (U C ω))}) atTop (𝓝 0) := by
  intro κ0 hκ0
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  have hθ3 : 0 < θ / 3 := ENNReal.div_pos hθ.ne' (by norm_num)
  set κ := min κ0 (1 / 2)
  have hκ : 0 < κ := lt_min hκ0 (by norm_num)
  have hκ2 : κ ≤ 1 / 2 := min_le_right _ _
  obtain ⟨c, hc1, hc⟩ := hgrow κ hκ (by linarith) (θ / 3) hθ3
  have hc0 : 0 < c := by linarith
  set ε := Real.log c / γ
  have hε : 0 < ε := div_pos (Real.log_pos hc1) hγ
  have hγε : γ * ε = Real.log c := mul_div_cancel₀ _ hγ.ne'
  filter_upwards [hc, (ENNReal.tendsto_nhds_zero.1 (hφ 2 two_pos ε hε)) (θ / 3) hθ3,
    (ENNReal.tendsto_nhds_zero.1 hpos) (θ / 3) hθ3] with C h1 h2 h3
  set N := {ω | ¬ (IsLocallyGoodOn γ (V C ω) (x C ω) ∧ IsOpen (U C ω) ∧ U C ω ⊆ H ∧
      U C ω ⊆ V C ω ∧ ContinuousOn (φ C ω) (V C ω))}
  have hN : Q N = 0 := ae_iff.1 (hloc C)
  refine (measure_mono (fun ω hω => ?_ : _ ⊆ ((_ ∪ _) ∪ _) ∪ N)).trans
    (((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2)) h3)) hN.le)).trans
      (le_of_eq ?_))
  · simp only [mem_ofPred_eq] at hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, N] at hcon
    obtain ⟨⟨⟨⟨hg1, hg2⟩, hφz⟩, ha⟩, hx, hU, hUH, hUV, hφc⟩ := hcon
    set a := scaleParamOn γ (x C ω) (U C ω)
    have hbound : ∀ r, r ≤ 2 * a → ∀ z ∈ (ball 0 r ∩ H) ∩ U C ω, |φ C ω z| ≤ ε :=
      fun r hr z hz => hφz z hz.2 (by
        have := hz.1.1; rw [mem_ball, dist_zero_right] at this; linarith)
    have hmeas : ∀ r, MeasurableSet (ball (0 : ℂ) r ∩ H) := fun r =>
      measurableSet_ball.inter isOpen_H.measurableSet
    have hexp : Real.exp (γ * ε) = c := by rw [hγε, Real.exp_log hc0]
    have hexp' : Real.exp (-(γ * ε)) = c⁻¹ := by rw [Real.exp_neg, hexp]
    have hcmp := fun r (hr : r ≤ 2 * a) => qAreaMeasureOn_ofFun_add_le_ge hγ.le hx hU hUH hUV
      hφc (hmeas r) (hbound r hr)
    obtain ⟨hup, -⟩ := hcmp ((1 - κ) * a) (by nlinarith)
    obtain ⟨-, hlo⟩ := hcmp ((1 + κ) * a) (by nlinarith)
    rw [hexp] at hup
    rw [hexp'] at hlo
    obtain ⟨ha', habs⟩ := scale_sandwich ha hκ.le (by linarith) hc0 hup hlo hg1 hg2
    refine hω ⟨ha, ha', habs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) ha.le)⟩
  · rw [add_zero, ENNReal.add_thirds]

end Prop16Asm

end QuantumZipper
