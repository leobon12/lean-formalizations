import QuantumZipper.Proofs.Zipper.B5LocF1Assembly
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.GFF.CircleMeanValue

/-!
# B5 locality for F1, input (R3): the wedge field near `0` from the level-`n` data

Theorem 1.3, node B5 (locality) for F1 (Sheffield, arXiv:1012.4797, §5.4, pp. 70–72).
`wedgeLocalCoordStmt` proves `WedgeLocalCoordStmt γ α κ` of `B5LocF1Assembly.lean`: for every
level `n`, the wedge field `h = h† + Q(-log|·|) + A_{-log|·|}` agrees a.s., on all dyadic folded
circles of radius `≤ 2^{-(2n+1)}` centred in `B(0, 2^{-(2n+1)})`, with the field `locField`
built from

* the lateral part `h†` on these circles (generators of the lateral germ `lateralGerm X P 2⁻ⁿ`:
  the circles are carried by `closedBall 0 4⁻ⁿ ∩ ℍ̄`, and `evalReg` is a.s. exact on them,
  `AllOffsets.ae_evalReg_fc_eq`);
* the radial part, integrated against the circle, with `A` replaced by its dyadic
  right-regularisation `radVer A n` (a jointly measurable version reading only `A_t`, `t ≥ n`),
  which equals `A_{max(·, n)}` on continuous paths; on the circles, `-log|z| ≥ n`.

Own elementary bookkeeping argument (the regularisation `radVer` is the standard dyadic
right-limit construction of a measurable version of a right-continuous process).
-/

noncomputable section

set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open F1

/-! ### A jointly measurable version of the radial process on `[n, ∞)` -/

/-- Dyadic upper rounding `⌈s 2^k⌉ / 2^k`. -/
def dyUp (k : ℕ) (s : ℝ) : ℝ := (⌈s * 2 ^ k⌉ : ℝ) / 2 ^ k

theorem le_dyUp (k : ℕ) (s : ℝ) : s ≤ dyUp k s := by
  unfold dyUp
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

theorem dyUp_le (k : ℕ) (s : ℝ) : dyUp k s ≤ s + (2 ^ k)⁻¹ := by
  unfold dyUp
  rw [div_le_iff₀ (by positivity), add_mul, inv_mul_cancel₀ (by positivity)]
  exact (Int.ceil_lt_add_one _).le

theorem tendsto_dyUp (s : ℝ) : Tendsto (fun k => dyUp k s) atTop (𝓝 s) := by
  have h0 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have h : Tendsto (fun k : ℕ => s + ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 (s + 0)) :=
    tendsto_const_nhds.add h0
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (le_dyUp · s) (dyUp_le · s)

/-- The dyadic right-regularisation of `A` on `[n, ∞)`: `lim_k A_{max(⌈s 2^k⌉/2^k, n)}`. -/
def radVer {Ω : Type*} (A : ℝ → Ω → ℝ) (n : ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  limUnder atTop fun k : ℕ => A (max (dyUp k s) n) ω

theorem measurable_radVer {Ω : Type*} [MeasurableSpace Ω] (A : ℝ → Ω → ℝ) (n : ℝ)
    (hA : ∀ t, n ≤ t → Measurable (A t)) :
    Measurable fun p : Ω × ℝ => radVer A n p.1 p.2 := by
  refine (StronglyMeasurable.limUnder
    (f := fun k (p : Ω × ℝ) => A (max (dyUp k p.2) n) p.1) fun k => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  have hF : Measurable fun q : Ω × ℤ => A (max ((q.2 : ℝ) / 2 ^ k) n) q.1 :=
    measurable_from_prod_countable_left fun m => hA (max ((m : ℝ) / 2 ^ k) n) (le_max_right _ _)
  exact hF.comp (measurable_fst.prodMk (Int.measurable_ceil.comp (measurable_snd.mul_const _)))

theorem radVer_eq {Ω : Type*} {A : ℝ → Ω → ℝ} {n : ℝ} {ω : Ω}
    (hc : ContinuousOn (fun t => A t ω) (Ici n)) (s : ℝ) : radVer A n ω s = A (max s n) ω := by
  unfold radVer
  refine Tendsto.limUnder_eq ?_
  have h1 : Tendsto (fun k => max (dyUp k s) n) atTop (𝓝[Ici n] (max s n)) :=
    tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyUp s).max tendsto_const_nhds,
      Eventually.of_forall fun k => mem_Ici.2 (le_max_right (dyUp k s) n)⟩
  exact (hc _ (le_max_right s n)).tendsto.comp h1

/-- The radial integral against `μ`, with the version `radVer`, is measurable. -/
theorem measurable_radInt {Ω : Type*} [MeasurableSpace Ω] (A : ℝ → Ω → ℝ) (n : ℝ)
    (hA : ∀ t, n ≤ t → Measurable (A t)) (Q : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun ω => ∫ z, (Q * (-Real.log ‖z‖) + radVer A n ω (-Real.log ‖z‖)) ∂μ := by
  have hl : Measurable fun z : ℂ => -Real.log ‖z‖ := (Real.measurable_log.comp measurable_norm).neg
  have hl2 : Measurable fun p : Ω × ℂ => -Real.log ‖p.2‖ := hl.comp measurable_snd
  have hr : Measurable fun p : Ω × ℂ => radVer A n p.1 (-Real.log ‖p.2‖) := by
    have h := (measurable_radVer A n hA).comp (measurable_fst.prodMk hl2)
    exact h
  have hj : Measurable fun p : Ω × ℂ =>
      Q * (-Real.log ‖p.2‖) + radVer A n p.1 (-Real.log ‖p.2‖) :=
    (hl2.const_mul Q).add hr
  have hs := StronglyMeasurable.integral_prod_right' (ν := μ) hj.stronglyMeasurable
  exact hs.measurable

/-! ### The level-`n` local field -/

/-- The level-`n` local field: lateral part plus the regularised radial part, truncated to the
dyadic circles of radius `≤ 2^{-(2n+1)}` centred in `B(0, 2^{-(2n+1)})`. -/
def locField (γ : ℝ) {Ω : Type*} (X : Ω → FieldSample) (A : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    FieldSample :=
  truncField (fun μ => lateralPart (X ω) μ +
      ∫ z, (Qc γ * (-Real.log ‖z‖) + radVer A n ω (-Real.log ‖z‖)) ∂μ)
    (Metric.ball 0 (radius (2 * n + 1))) (2 * n + 1)

/-- Folded circles of radius `≤ 2^{-(2n+1)}` centred in `B(0, 2^{-(2n+1)})` live on
`ℍ ∩ closedBall 0 4⁻ⁿ`. -/
theorem ae_fc_small {c : ℂ} (hc : c ∈ Hbar) {n j : ℕ} (hj : 2 * n + 1 ≤ j)
    (hcS : c ∈ Metric.ball (0 : ℂ) (radius (2 * n + 1))) :
    ∀ᵐ z ∂foldedCircle c (radius j), z ∈ H ∧ ‖z‖ ≤ radius (2 * n) := by
  filter_upwards [LocalRule.ae_fc_mem_closedBall hc (radius_pos j),
    TwoPoint.foldedCircle_ae_mem_H c (radius_pos j)] with z hz hzH
  refine ⟨hzH, ?_⟩
  have h1 : ‖z - c‖ ≤ radius j := by simpa [dist_eq_norm] using hz
  have h2 : ‖c‖ < radius (2 * n + 1) := by simpa using hcS
  have h3 : radius j ≤ radius (2 * n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have h4 : radius (2 * n + 1) = radius (2 * n) / 2 := by unfold radius; rw [pow_succ]; ring
  have h5 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := norm_le_norm_sub_add _ _
  linarith

theorem le_neg_log_of_le_radius {n : ℕ} {z : ℂ} (hz : z ∈ H) (hzn : ‖z‖ ≤ radius (2 * n)) :
    (n : ℝ) ≤ -Real.log ‖z‖ := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (UnzipFull.ne_zero_of_mem_H hz)
  have hlog : Real.log ‖z‖ ≤ Real.log (radius (2 * n)) := Real.log_le_log hz0 hzn
  have hr : Real.log (radius (2 * n)) = -(2 * n * Real.log 2) := by
    unfold radius
    rw [Real.log_pow, Real.log_inv]
    push_cast
    ring
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem measurable_A_radTail {Ω : Type*} (A : ℝ → Ω → ℝ) (n : ℕ) (t : ℝ) (ht : (n : ℝ) ≤ t) :
    Measurable[radTail A n] (A t) := by
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg n) ht
  have hmem : t.toNNReal ∈ Ici (n : ℝ≥0) := by
    rw [mem_Ici, ← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]
    exact_mod_cast ht
  have e : A t = fun ω => A (((⟨t.toNNReal, hmem⟩ : Ici (n : ℝ≥0)) : ℝ≥0) : ℝ) ω := by
    funext ω
    simp [Real.coe_toNNReal _ ht0]
  rw [e]
  exact (measurable_pi_apply (⟨t.toNNReal, hmem⟩ : Ici (n : ℝ≥0))).comp
    (comap_measurable (fun ω (u : Ici (n : ℝ≥0)) => A ((u : ℝ≥0) : ℝ) ω))

section Main

variable {Ω : Type*} [MeasurableSpace Ω]

theorem lateralGerm_le_levelSigma (X : Ω → FieldSample) (P : Measure Ω) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    LateralGerm.lateralGerm X P ((2 : ℝ)⁻¹ ^ n) ≤ levelSigma X P A B n :=
  le_iSup₂_of_le (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => germFam X P A B i n)
    0 (Finset.mem_univ _) le_rfl

theorem radTail_le_levelSigma (X : Ω → FieldSample) (P : Measure Ω) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) : radTail A n ≤ levelSigma X P A B n :=
  le_iSup₂_of_le (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => germFam X P A B i n)
    1 (Finset.mem_univ _) le_rfl

theorem measurable_locField (γ : ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (A : ℝ → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (n : ℕ) : Measurable[levelSigma X P A B n] (locField γ X A n) := by
  refine measurable_truncField (m := levelSigma X P A B n) _ _ _ fun j hj n' z hz hzS => ?_
  set c := dyadicRoundC n' z with hcdef
  have hc : c ∈ Hbar := Positivity.dyadicRoundC_mem_Hbar n' hz
  have hr := radius_pos j
  have hlat : Measurable[LateralGerm.lateralGerm X P ((2 : ℝ)⁻¹ ^ n)]
      fun ω => lateralPart (X ω) (foldedCircle c (radius j)) := by
    refine Measurable.mono (comap_measurable
      (fun ω => lateralPart (X ω) (foldedCircle c (radius j)))) ?_ le_rfl
    refine le_iSup₂_of_le (f := fun (μ : Measure ℂ) (_ : IsAdmissibleH μ ∧
        μ (Metric.closedBall 0 ((2 : ℝ)⁻¹ ^ n) ∩ Hbar)ᶜ = 0 ∧
        ∀ᵐ ω ∂P, evalReg (X ω) μ = X ω μ) =>
        MeasurableSpace.comap (fun ω => lateralPart (X ω) μ) inferInstance)
      (foldedCircle c (radius j)) ⟨isAdmissibleH_foldedCircle hc hr, ?_,
        AllOffsets.ae_evalReg_fc_eq hX hc hr⟩ le_rfl
    have hsupp := ae_fc_small hc hj hzS
    have h0 := ae_iff.1 hsupp
    refine measure_mono_null ?_ h0
    intro w hw hw'
    refine hw ?_
    have h1 : radius (2 * n) ≤ (2 : ℝ)⁻¹ ^ n := by
      unfold radius
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact ⟨Metric.mem_closedBall.2 (by rw [dist_zero_right]; exact hw'.2.trans h1),
      H_subset_Hbar hw'.1⟩
  have hrad : Measurable[radTail A n] fun ω => ∫ w, (Qc γ * (-Real.log ‖w‖) +
      radVer A n ω (-Real.log ‖w‖)) ∂foldedCircle c (radius j) :=
    @measurable_radInt Ω (radTail A n) A n (measurable_A_radTail A n) (Qc γ) _ _
  exact (hlat.mono (lateralGerm_le_levelSigma X P A B n) le_rfl).add
    (hrad.mono (radTail_le_levelSigma X P A B n) le_rfl)

end Main

/-- **(R3) proved**: `WedgeLocalCoordStmt γ α κ`. -/
theorem wedgeLocalCoordStmt (γ α κ : ℝ) : WedgeLocalCoordStmt γ α κ := by
  intro _ _ _ _ Ω _ P X A B hP hX hA _ _ _ _ n
  have := hP
  refine ⟨radius (2 * n + 1), radius_pos _, 2 * n + 1, locField γ X A n,
    measurable_locField γ hX A B n, ?_⟩
  obtain ⟨b, b', hb, -, -, hAb⟩ := hA
  filter_upwards [hb.cont] with ω hbc
  have hform : ∀ t : ℝ, 0 ≤ t →
      A t ω = Real.sqrt 2 * b t.toNNReal ω + (α - Qc γ) * t := fun t ht => by
    rw [hAb ω t]
    simp [wedgePath, ht]
  have hcont : ContinuousOn (fun t => A t ω) (Ici (n : ℝ)) := by
    refine ContinuousOn.congr (f := fun t : ℝ => Real.sqrt 2 * b t.toNNReal ω + (α - Qc γ) * t)
      (Continuous.continuousOn ?_) fun t ht => hform t (le_trans (Nat.cast_nonneg n) ht)
    exact (continuous_const.mul (hbc.comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)
  intro j hj n' z hz hzS
  unfold locField
  rw [← dyCircAgree_truncField _ _ _ j hj n' z hz hzS]
  show lateralPart (X ω) _ + ∫ w, (Qc γ * (-Real.log ‖w‖) + A (-Real.log ‖w‖) ω) ∂_ = _
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_fc_small (Positivity.dyadicRoundC_mem_Hbar n' hz) hj hzS] with w hw
  rw [radVer_eq hcont, max_eq_left (le_neg_log_of_le_radius hw.1 hw.2)]

end B5
end QuantumZipper
