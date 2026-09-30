import QuantumZipper.Proofs.GFF.CoordRegLog

/-!
# Proposition 1.7, Palm-zoom node C: RC1 with a logarithmic singularity at a real point (PALM-C)

The translate, to a real pole `t`, of `CoordReg.ae_evalReg_logAdd_eq_frostman` (RC1 with a
logarithmic mean `a · log‖·‖ + g₁`): for a finite Frostman measure `ν` with bounded support in
`Hbar`, almost surely

  `evalReg (ofFun (a · log‖· − t‖ + g₁) + X ω) ν = ∫ (a · log‖· − t‖ + g₁) dν + X ω ν`

(`palmC_ae_evalReg_logAdd`). The proof is that of `CoordRegLog` (own argument there), with the
pole moved from `0` to `t`: the folded-circle mean of `log‖· − t‖` is `log max(r, ‖c − t‖)`
because `‖foldH v − t‖ = ‖v − t‖` for real `t` (classical `∮ log|z − y| = log max(r, |c − y|)`,
`SmoothConv.integral_log_norm_sub_circleUnif_sc`), and the Frostman bound is used at the pole `t`
(`frostman_lintegral_logNeg_le _ _ t`). Own adaptation.
-/

noncomputable section

open MeasureTheory Filter ProbabilityTheory
open scoped Real ComplexConjugate ENNReal NNReal Topology

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open FrostmanReg SmoothConv CoordReg

variable {ν : Measure ℂ} {α C : ℝ}

theorem palmC_norm_foldH_sub_real (v : ℂ) (t : ℝ) : ‖foldH v - (t : ℂ)‖ = ‖v - (t : ℂ)‖ := by
  unfold foldH
  split_ifs
  · rfl
  · rw [show (starRingEnd ℂ) v - (t : ℂ) = (starRingEnd ℂ) (v - t) by
      rw [map_sub, Complex.conj_ofReal], Complex.norm_conj]

theorem palmC_measurable_log_sub (t : ℂ) : Measurable fun v : ℂ => Real.log ‖v - (t : ℂ)‖ :=
  Real.measurable_log.comp (measurable_id.sub_const t).norm

theorem palmC_integral_log_sub_fc (c : ℂ) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ v, Real.log ‖v - (t : ℂ)‖ ∂foldedCircle c r = Real.log (max r ‖c - (t : ℂ)‖) := by
  rw [foldedCircle, integral_map measurable_foldH.aemeasurable
    (palmC_measurable_log_sub _).aestronglyMeasurable]
  simp_rw [palmC_norm_foldH_sub_real]
  exact integral_log_norm_sub_circleUnif_sc c t hr

theorem palmC_integrable_log_sub_fc (c : ℂ) (t : ℝ) (r : ℝ) :
    Integrable (fun v => Real.log ‖v - (t : ℂ)‖) (foldedCircle c r) := by
  rw [foldedCircle, integrable_map_measure (palmC_measurable_log_sub _).aestronglyMeasurable
    measurable_foldH.aemeasurable]
  refine (integrable_log_norm_sub_circleUnif_sc c t r).congr (ae_of_all _ fun v => ?_)
  simp [palmC_norm_foldH_sub_real]

theorem palmC_continuous_log_max_sub {r : ℝ} (hr : 0 < r) (t : ℝ) :
    Continuous fun c : ℂ => Real.log (max r ‖c - (t : ℂ)‖) :=
  (continuous_log_max_norm hr).comp (continuous_id.sub continuous_const)

theorem palmC_avgReg_logAdd (a t : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar)
    {x : FieldSample} {k : ℕ} {z : ℂ}
    (hx : Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (avgReg x k z))) :
    avgReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ + g₁ v) + x) k z =
      a * Real.log (max (radius k) ‖z - (t : ℂ)‖) + GoodSample.smoothFun g₁ z (radius k) +
        avgReg x k z := by
  have hr := radius_pos k
  have ha : Tendsto (fun n => a * Real.log (max (radius k) ‖dyadicRoundC n z - (t : ℂ)‖) +
      GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k)) atTop
      (𝓝 (a * Real.log (max (radius k) ‖z - (t : ℂ)‖) + GoodSample.smoothFun g₁ z (radius k))) :=
    ((((palmC_continuous_log_max_sub hr t).tendsto z).comp
      (RegClosure.tendsto_dyadicRoundC z)).const_mul a).add
      (((GoodSample.continuous_smoothFun hg₁ _).tendsto z).comp
        (RegClosure.tendsto_dyadicRoundC z))
  have e : (fun n => (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ + g₁ v) + x)
      (foldedCircle (dyadicRoundC n z) (radius k))) =
      fun n => (a * Real.log (max (radius k) ‖dyadicRoundC n z - (t : ℂ)‖) +
        GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k)) +
          x (foldedCircle (dyadicRoundC n z) (radius k)) := by
    funext n
    show ofFun _ _ + x _ = _
    simp only [ofFun]
    rw [integral_add ((palmC_integrable_log_sub_fc _ t _).const_mul a)
      (RegClosure.integrable_fc hg₁ _ hr.le), integral_const_mul,
      palmC_integral_log_sub_fc _ t hr]
    rfl
  unfold avgReg
  rw [e]
  exact (ha.add hx).limUnder_eq

theorem palmC_integrable_log_sub_frostman [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (t : ℝ) : Integrable (fun z => Real.log ‖z - (t : ℂ)‖) ν := by
  refine ⟨(palmC_measurable_log_sub _).aestronglyMeasurable, ?_⟩
  have hmem : ∀ᵐ z ∂ν, z ∈ Metric.closedBall 0 R ∩ Hbar := ae_mem_of_compl_null_frostman hsupp
  set M : ℝ := max (Real.log (R + ‖(t : ℂ)‖)) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hpt : ∀ᵐ z ∂ν, ‖Real.log ‖z - (t : ℂ)‖‖ₑ ≤ ENNReal.ofReal (-Real.log (‖z - (t : ℂ)‖ / 1)) +
      ENNReal.ofReal M := by
    filter_upwards [hmem] with z hz
    have hzR : ‖z‖ ≤ R := by simpa using hz.1
    have hzt : ‖z - (t : ℂ)‖ ≤ R + ‖(t : ℂ)‖ := (norm_sub_le _ _).trans (by linarith)
    have hup : Real.log ‖z - (t : ℂ)‖ ≤ M := by
      rcases eq_or_lt_of_le (norm_nonneg (z - t)) with h0 | h0
      · rw [← h0, Real.log_zero]; exact hM0
      · exact (Real.log_le_log h0 hzt).trans (le_max_left _ _)
    rw [div_one, ← ofReal_norm, Real.norm_eq_abs]
    calc ENNReal.ofReal |Real.log ‖z - (t : ℂ)‖| ≤ ENNReal.ofReal (max (-Real.log ‖z - (t : ℂ)‖) 0 + M) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rcases le_total 0 (Real.log ‖z - (t : ℂ)‖) with h1 | h1
          · rw [abs_of_nonneg h1]; linarith [le_max_right (-Real.log ‖z - (t : ℂ)‖) 0]
          · rw [abs_of_nonpos h1]; linarith [le_max_left (-Real.log ‖z - (t : ℂ)‖) 0]
      _ = ENNReal.ofReal (max (-Real.log ‖z - (t : ℂ)‖) 0) + ENNReal.ofReal M :=
          ENNReal.ofReal_add (le_max_right _ _) hM0
      _ = _ := by rw [max_comm, CircleFubini.ofReal_max_zero]
  have hm : Measurable fun z : ℂ => ENNReal.ofReal (-Real.log (‖z - (t : ℂ)‖ / 1)) :=
    (Real.measurable_log.comp ((measurable_id.sub_const _).norm.div_const 1)).neg.ennreal_ofReal
  calc ∫⁻ z, ‖Real.log ‖z - (t : ℂ)‖‖ₑ ∂ν
      ≤ ∫⁻ z, (ENNReal.ofReal (-Real.log (‖z - (t : ℂ)‖ / 1)) + ENNReal.ofReal M) ∂ν :=
        lintegral_mono_ae hpt
    _ = ∫⁻ z, ENNReal.ofReal (-Real.log (‖z - (t : ℂ)‖ / 1)) ∂ν + ENNReal.ofReal M * ν Set.univ := by
        rw [lintegral_add_left hm, lintegral_const]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨lt_of_le_of_lt (frostman_lintegral_logNeg_le h hα _ one_pos)
        ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem palmC_tendsto_integral_log_max_sub [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (t : ℝ) :
    Tendsto (fun k => ∫ z, Real.log (max (radius k) ‖z - (t : ℂ)‖) ∂ν) atTop
      (𝓝 (∫ z, Real.log ‖z - (t : ℂ)‖ ∂ν)) := by
  have hint := palmC_integrable_log_sub_frostman hsupp h hα t
  have hne : ∀ᵐ z ∂ν, z ≠ (t : ℂ) := ae_ne_frostman h hα _
  refine tendsto_integral_of_dominated_convergence (fun z => |Real.log ‖z - (t : ℂ)‖|)
    (fun k => (palmC_continuous_log_max_sub (radius_pos k) t).aestronglyMeasurable) hint.abs
    (fun k => ?_) ?_
  · filter_upwards [hne] with z hz
    have hz0 : 0 < ‖z - (t : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    have hr1 : radius k ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
    rw [Real.norm_eq_abs]
    rcases le_total (radius k) ‖z - (t : ℂ)‖ with h1 | h1
    · rw [max_eq_right h1]
    · rw [max_eq_left h1]
      have a1 := Real.log_le_log hz0 h1
      have a2 := Real.log_nonpos (radius_pos k).le hr1
      rw [abs_of_nonpos a2, abs_of_nonpos (a1.trans a2)]
      linarith
  · filter_upwards [hne] with z hz
    have hz0 : 0 < ‖z - (t : ℂ)‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    have hev : ∀ᶠ k in atTop, radius k ≤ ‖z - (t : ℂ)‖ :=
      ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (ge_mem_nhds hz0))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    rw [max_eq_right hk]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **RC1 with a logarithmic singularity at a real point.** -/
theorem palmC_ae_evalReg_logAdd {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (a t : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar) :
    ∀ᵐ ω ∂P, evalReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ + g₁ v) + X ω) ν =
      (∫ z, (a * Real.log ‖z - (t : ℂ)‖ + g₁ z) ∂ν) + X ω ν := by
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hKH : K ⊆ Hbar := Set.inter_subset_right
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_mem_of_compl_null_frostman hsupp
  have hlog := palmC_integrable_log_sub_frostman hsupp h hα t
  have hg₁i : Integrable g₁ ν := integrable_of_continuousOn_frostman hK hKH hsupp hg₁
  filter_upwards [ae_all_iff.2 fun k => ae_circleAvg_tendsto_frostman hX k,
    ae_tendsto_integral_avgReg_frostman hX hsupp h hα] with ω hc ht
  have heq : ∀ k, ∫ z, avgReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ + g₁ v) + X ω) k z ∂ν =
      a * ∫ z, Real.log (max (radius k) ‖z - (t : ℂ)‖) ∂ν +
        ∫ z, GoodSample.smoothFun g₁ z (radius k) ∂ν + ∫ z, avgReg (X ω) k z ∂ν := by
    intro k
    have i1 : Integrable (fun z => Real.log (max (radius k) ‖z - (t : ℂ)‖)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (palmC_continuous_log_max_sub (radius_pos k) t).continuousOn
    have i2 : Integrable (fun z => GoodSample.smoothFun g₁ z (radius k)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (GoodSample.continuous_smoothFun hg₁ _).continuousOn
    have i3 : Integrable (fun z => avgReg (X ω) k z) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp (hc k).1
    have i12 : Integrable (fun z => a * Real.log (max (radius k) ‖z - (t : ℂ)‖) +
        GoodSample.smoothFun g₁ z (radius k)) ν := (i1.const_mul a).add i2
    rw [← integral_const_mul, ← integral_add (i1.const_mul a) i2, ← integral_add i12 i3]
    exact integral_congr_ae (hae.mono fun z hz =>
      palmC_avgReg_logAdd a t hg₁ ((hc k).2 z (hKH hz)))
  have hval : (∫ z, (a * Real.log ‖z - (t : ℂ)‖ + g₁ z) ∂ν) + X ω ν =
      a * ∫ z, Real.log ‖z - (t : ℂ)‖ ∂ν + ∫ z, g₁ z ∂ν + X ω ν := by
    rw [integral_add (hlog.const_mul a) hg₁i, integral_const_mul]
  rw [hval]
  refine Tendsto.limUnder_eq ?_
  simp only [heq]
  exact (((palmC_tendsto_integral_log_max_sub hsupp h hα t).const_mul a).add
    (tendsto_integral_smoothFun_frostman hg₁ hK hKH hsupp)).add ht

end Raw
end FieldLaw
end S5
end QuantumZipper
