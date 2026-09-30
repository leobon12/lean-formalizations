import QuantumZipper.Proofs.LQG.Measurability
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert
import QuantumZipper.LQG.Local

/-!
# READLEN, tool: a certificate-free measurable reader of `ν [b, c]` from the approximants

For the boundary approximants `bdryApprox γ x k` of a field `x` and an interval `[b, c]`,
`vagueRd γ x b c = limsup_n ofReal (limsup_k ∫ tentₙ d(bdryApprox γ x k))`, where
`tentₙ = tent n b c` is the piecewise linear bump equal to `1` on `[b, c]` and to `0` off
`[b - 1/(n+1), c + 1/(n+1)]`.

* `measurable_vagueRd`: `(x, b, c) ↦ vagueRd γ x b c` is measurable (the approximants have the
  jointly measurable density `exp (γ/2 · avgReg x k t)`, `measurable_avgReg`; parametric
  integrals by `StronglyMeasurable.integral_prod_right'`), with **no** certificate on `x`.
* `vagueRd_eq`: whenever `ν` is a vague limit of the approximants on an open set `U ⊇ [b, c]`
  (`IsVagueLimitOnR U`), `vagueRd γ x b c = ν [b, c]` (vague convergence against the tents whose
  support lies in `U`, then dominated convergence `tentₙ ↓ 1_[b,c]`, `ν` finite on compacts of
  `U`). Hence `vagueRd_eq_qBoundaryMeasureOn`, `vagueRd_eq_qBoundaryMeasure`.

This is the field-side core of `B5.LocLengthsMeasStmt` (local lengths, existence of a local vague
limit only) and an alternative to the `BCert` gate of `ESM.nuSur`. Own elementary argument
(standard: the mass of a closed interval is the decreasing limit of the integrals of continuous
bumps, e.g. Billingsley, *Convergence of Probability Measures*, proof of Thm 2.1).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The tent over `[b, c]` of slope `n + 1`. -/
def tent (n : ℕ) (b c y : ℝ) : ℝ := max 0 (min 1 (1 - ((n : ℝ) + 1) * max (b - y) (y - c)))

theorem continuous_tent_joint (n : ℕ) :
    Continuous fun q : ℝ × ℝ × ℝ => tent n q.1 q.2.1 q.2.2 := by
  unfold tent
  have h1 : Continuous fun q : ℝ × ℝ × ℝ => q.1 := continuous_fst
  have h2 : Continuous fun q : ℝ × ℝ × ℝ => q.2.1 := continuous_fst.comp continuous_snd
  have h3 : Continuous fun q : ℝ × ℝ × ℝ => q.2.2 := continuous_snd.comp continuous_snd
  exact continuous_const.max (continuous_const.min (continuous_const.sub
    (continuous_const.mul ((h1.sub h3).max (h3.sub h2)))))

theorem continuous_tent (n : ℕ) (b c : ℝ) : Continuous (tent n b c) :=
  (continuous_tent_joint n).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))

theorem tent_nonneg (n : ℕ) (b c y : ℝ) : 0 ≤ tent n b c y := le_max_left _ _

theorem tent_le_one (n : ℕ) (b c y : ℝ) : tent n b c y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tent_eq_one {n : ℕ} {b c y : ℝ} (hy : y ∈ Icc b c) : tent n b c y = 1 := by
  have hm : max (b - y) (y - c) ≤ 0 := max_le (by linarith [hy.1]) (by linarith [hy.2])
  have h : 1 ≤ 1 - ((n : ℝ) + 1) * max (b - y) (y - c) := by
    have : 0 ≤ ((n : ℝ) + 1) * -max (b - y) (y - c) := mul_nonneg (by positivity) (by linarith)
    linarith
  unfold tent
  rw [min_eq_left h, max_eq_right zero_le_one]

theorem tent_eq_zero {n : ℕ} {b c y : ℝ}
    (hy : y ∉ Icc (b - 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1))) : tent n b c y = 0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hm : 1 / ((n : ℝ) + 1) < max (b - y) (y - c) := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · exact lt_max_of_lt_left (by linarith)
    · exact lt_max_of_lt_right (by linarith)
  have h : 1 - ((n : ℝ) + 1) * max (b - y) (y - c) ≤ 0 := by
    have := (div_lt_iff₀' hn).1 hm
    linarith
  unfold tent
  exact max_eq_left ((min_le_right _ _).trans h)

theorem tsupport_tent (n : ℕ) (b c : ℝ) :
    tsupport (tent n b c) ⊆ Icc (b - 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1)) :=
  closure_minimal (fun y hy => by
    by_contra h
    exact hy (tent_eq_zero h)) isClosed_Icc

theorem hasCompactSupport_tent (n : ℕ) (b c : ℝ) : HasCompactSupport (tent n b c) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_tent n b c)

theorem tendsto_tent (b c y : ℝ) :
    Tendsto (fun n => tent n b c y) atTop (𝓝 ((Icc b c).indicator (1 : ℝ → ℝ) y)) := by
  by_cases hy : y ∈ Icc b c
  · rw [indicator_of_mem hy]
    exact tendsto_const_nhds.congr fun n => (tent_eq_one hy).symm
  · rw [indicator_of_notMem hy]
    have hm : 0 < max (b - y) (y - c) := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with h | h
      · exact lt_max_of_lt_left (by linarith)
      · exact lt_max_of_lt_right (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hm
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => (tent_eq_zero ?_).symm⟩)
    intro hmem
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := Nat.one_div_le_one_div hn
    have : max (b - y) (y - c) ≤ 1 / ((n : ℝ) + 1) :=
      max_le (by linarith [hmem.1]) (by linarith [hmem.2])
    linarith

/-- **The certificate-free reader** of `ν [b, c]` from the approximants of `x`. -/
def vagueRd (γ : ℝ) (x : FieldSample) (b c : ℝ) : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal
    (limsup (fun k : ℕ => ∫ y, tent n b c y ∂bdryApprox γ x k) atTop)) atTop

theorem measurable_integral_tent (γ : ℝ) (n k : ℕ) :
    Measurable fun q : FieldSample × ℝ × ℝ => ∫ y, tent n q.2.1 q.2.2 y ∂bdryApprox γ q.1 k := by
  let D : FieldSample × ℝ → ℝ := fun p =>
    radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg p.1 k (p.2 : ℂ))
  have hDm : Measurable D :=
    (Real.measurable_exp.comp (((measurable_avgReg k).comp
      (measurable_fst.prodMk (Complex.continuous_ofReal.measurable.comp measurable_snd))).const_mul
        (γ / 2))).const_mul _
  have hD0 : ∀ p, 0 ≤ D p := fun p =>
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have heq : ∀ q : FieldSample × ℝ × ℝ, ∫ y, tent n q.2.1 q.2.2 y ∂bdryApprox γ q.1 k =
      ∫ y, D (q.1, y) * tent n q.2.1 q.2.2 y := fun q =>
    GoodSample.integral_withDensity_ofReal (hDm.comp (measurable_const.prodMk measurable_id))
      (fun t => hD0 _) _
  simp_rw [heq]
  have hT : Measurable fun p : (FieldSample × ℝ × ℝ) × ℝ => tent n p.1.2.1 p.1.2.2 p.2 :=
    (continuous_tent_joint n).measurable.comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : (FieldSample × ℝ × ℝ) × ℝ => D (p.1.1, p.2) * tent n p.1.2.1 p.1.2.2 p.2)
    ((hDm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      hT).stronglyMeasurable).measurable

theorem measurable_vagueRd (γ : ℝ) :
    Measurable fun q : FieldSample × ℝ × ℝ => vagueRd γ q.1 q.2.1 q.2.2 := by
  unfold vagueRd
  exact Measurable.limsup fun n => ENNReal.measurable_ofReal.comp
    (Measurable.limsup fun k => measurable_integral_tent γ n k)

/-- A compact interval inside an open set has a closed neighbourhood `[b - ε, c + ε]` in it. -/
theorem exists_Icc_thick_subset {U : Set ℝ} (hU : IsOpen U) {b c : ℝ} (hbc : Icc b c ⊆ U) :
    ∃ n₀ : ℕ, Icc (b - 1 / ((n₀ : ℝ) + 1)) (c + 1 / ((n₀ : ℝ) + 1)) ⊆ U := by
  rcases le_or_gt b c with hle | hlt
  · obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hU hbc
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hδ
    refine ⟨n₀, fun y hy => hsub ?_⟩
    rw [Metric.mem_thickening_iff]
    set ε := 1 / ((n₀ : ℝ) + 1)
    have hε : 0 ≤ ε := by positivity
    refine ⟨max b (min c y), ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩, ?_⟩
    have hlo : y - ε ≤ max b (min c y) :=
      (le_min (by linarith [hy.2]) (by linarith)).trans (le_max_right _ _)
    have hhi : max b (min c y) ≤ y + ε :=
      (max_le_max le_rfl (min_le_right _ _)).trans (max_le (by linarith [hy.1]) (by linarith))
    rw [Real.dist_eq]
    exact (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩).trans_lt hn₀
  · obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt (half_pos (sub_pos.2 hlt))
    refine ⟨n₀, fun y hy => absurd hy ?_⟩
    intro hmem
    linarith [hmem.1, hmem.2]

/-- **The reader computes the local vague limit** on closed intervals inside `U`. -/
theorem vagueRd_eq {γ : ℝ} {x : FieldSample} {U : Set ℝ} (hU : IsOpen U) {ν : Measure ℝ}
    (h : IsVagueLimitOnR U (bdryApprox γ x) ν) {b c : ℝ} (hbc : Icc b c ⊆ U) :
    vagueRd γ x b c = ν (Icc b c) := by
  obtain ⟨n₀, hn₀⟩ := exists_Icc_thick_subset hU hbc
  set K₀ := Icc (b - 1 / ((n₀ : ℝ) + 1)) (c + 1 / ((n₀ : ℝ) + 1)) with hK₀
  have hsubK : ∀ n ≥ n₀, Icc (b - 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1)) ⊆ K₀ := by
    intro n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) := Nat.one_div_le_one_div hn
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hinner : ∀ n ≥ n₀, limsup (fun k => ∫ y, tent n b c y ∂bdryApprox γ x k) atTop =
      ∫ y, tent n b c y ∂ν := fun n hn =>
    (h.2.2 _ (continuous_tent n b c) (hasCompactSupport_tent n b c)
      (((tsupport_tent n b c).trans (hsubK n hn)).trans hn₀)).limsup_eq
  have hK₀fin : ν K₀ < ⊤ := h.2.1 _ isCompact_Icc hn₀
  have hIfin : ν (Icc b c) < ⊤ :=
    (measure_mono (Icc_subset_Icc (by linarith [show (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) by positivity])
      (by linarith [show (0 : ℝ) < 1 / ((n₀ : ℝ) + 1) by positivity]))).trans_lt hK₀fin
  have hbound : Integrable (K₀.indicator fun _ => (1 : ℝ)) ν :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const hK₀fin.ne)
  have hdom : Tendsto (fun n => ∫ y, tent n b c y ∂ν) atTop
      (𝓝 (∫ y, (Icc b c).indicator (1 : ℝ → ℝ) y ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence _
      (Eventually.of_forall fun n => (continuous_tent n b c).aestronglyMeasurable)
      (eventually_atTop.2 ⟨n₀, fun n hn => ae_of_all _ fun y => ?_⟩) hbound
      (ae_of_all _ fun y => tendsto_tent b c y)
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg n b c y)]
    by_cases hy : y ∈ Icc (b - 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1))
    · rw [indicator_of_mem (hsubK n hn hy)]; exact tent_le_one n b c y
    · rw [tent_eq_zero hy]; exact indicator_nonneg (fun _ _ => zero_le_one) y
  rw [integral_indicator_one measurableSet_Icc] at hdom
  have h1 := ENNReal.tendsto_ofReal hdom
  rw [measureReal_def, ENNReal.ofReal_toReal hIfin.ne] at h1
  unfold vagueRd
  exact (h1.congr' (eventually_atTop.2 ⟨n₀, fun n hn => by rw [hinner n hn]⟩)).limsup_eq

end F1
end QuantumZipper
