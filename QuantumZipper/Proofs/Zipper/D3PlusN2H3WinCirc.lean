import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinCore
import QuantumZipper.Proofs.Zipper.D3PlusN2RHeart
import QuantumZipper.Proofs.Zipper.D3PlusN2H1Main
import QuantumZipper.Proofs.LQG.WedgeInfGrowth
import QuantumZipper.Proofs.Zipper.WedgeShiftRaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H3': the lateral/radial splitting on the folded circles of the window (PROVED)

Task N2H3-SPLITWIN (Decision D36). `N2H3SplitWinCircStmt` is `N2H3SplitWinStmt`
(`D3PlusN2RHeart.lean`) restricted to the circle part `WinCirc K` of the window index: for a
folded circle `μ = fc(d, ρ)` of the window, a.s. on `{Tc ≥ log K + 1}`,

  `evalReg h_L (μ.map (a ·)) = evalReg h† (μ.map (a ·)) + ∫ (Z_{a|z|}(0) + α(−log(a|z|)) + L/γ) dμ`.

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78 (the
field is its lateral part `h†` plus its radial part `h_{|·|}(0)`); Sheffield, arXiv:1012.4797,
p. 25. The pathwise bookkeeping is own elementary work: on a full-measure event (regular version
of the free field, Markov decomposition and regularization of the local field on the countably
many dyadic circles, continuity and sublinear growth of the radial Brownian motion `zRadB`), the
hypotheses of the deterministic core `evalReg_split_core` (`D3PlusN2H3WinCore.lean`) hold with
`M = h_L`, `Y = h†`, `Z` the local field, `ψ = radPsi` (the radial path, log-dominated by the
strong law of large numbers `BMLLN`), and `ν = fc(a d, a ρ)`, whose regularizations converge by
clause 3 of `IsRegularWith` at every scale simultaneously.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK

/-- The radial path of the local field as a function of the radius. -/
def radPsi {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) (ρ : ℝ) : ℝ :=
  √2 * zRadB X r (Real.log (r / ρ)).toNNReal ω

theorem radAvgReg_eq_radPsi {Ω : Type*} (X : Ω → FieldSample) {r : ℝ} (hr : 0 < r) (ω : Ω)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    radAvgReg (locZField X r ω) ρ = radPsi X r ω ρ := by
  have ht : 0 ≤ Real.log (r / ρ) := Real.log_nonneg ((one_le_div hρ).2 hρr)
  have he : r * Real.exp (-((Real.log (r / ρ)).toNNReal : ℝ)) = ρ := by
    rw [Real.coe_toNNReal _ ht, Real.exp_neg, Real.exp_log (div_pos hr hρ)]
    field_simp
  simp only [radPsi, zRadB, he]
  rw [mul_inv_cancel_left₀ (by positivity)]

theorem logDom_radPsi {Ω : Type*} {X : Ω → FieldSample} {r : ℝ} (hr : 0 < r) {ω : Ω}
    (hc : Continuous fun t => zRadB X r t ω) {K' : ℝ}
    (hK : ∀ s : ℝ≥0, |zRadB X r s ω| ≤ 1 * s + K') :
    LogDom (radPsi X r ω) r (√2 * K') √2 := by
  have hin : Measurable fun ρ : ℝ => (Real.log (r / ρ)).toNNReal :=
    (Real.measurable_log.comp (measurable_const.div measurable_id)).real_toNNReal
  refine ⟨measurable_const.mul (hc.measurable.comp hin), ?_, by positivity, ?_⟩
  · have h1 : ContinuousOn (fun ρ : ℝ => (Real.log (r / ρ)).toNNReal) (Ioi 0) :=
      continuous_real_toNNReal.comp_continuousOn
        ((continuousOn_const.div continuousOn_id fun x hx => ne_of_gt hx).log
          fun x hx => (div_pos hr hx).ne')
    exact (continuous_const.mul hc).comp_continuousOn h1
  · intro ρ hρ hρr
    have ht : 0 ≤ Real.log (r / ρ) := Real.log_nonneg ((one_le_div hρ).2 hρr)
    have h := hK (Real.log (r / ρ)).toNNReal
    rw [Real.coe_toNNReal _ ht] at h
    simp only [radPsi, abs_mul, abs_of_pos (Real.sqrt_pos.2 two_pos)]
    nlinarith [Real.sqrt_pos.2 (two_pos : (0 : ℝ) < 2)]

/-- **N2-H3-SPLIT' on the folded circles of the window** (D36 form of `N2H3SplitStmt`,
restricted to `WinCirc K`). -/
def N2H3SplitWinCircStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K : ℕ, 0 < K → ∀ L, 0 < n2Lev γ α L r → ∀ p : WinCirc K, ∀ᵐ ω ∂P,
      Real.log K + 1 ≤ ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω →
      Integrable (fun z => radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖))
        (winIdx K (Sum.inl p)) ∧
      evalReg (n2Model γ α L r X ω)
          ((winIdx K (Sum.inl p)).map fun z => (n2EmbScale γ α L r X ω : ℂ) * z) =
        evalReg (n2LatY X r ω)
          ((winIdx K (Sum.inl p)).map fun z => (n2EmbScale γ α L r X ω : ℂ) * z) +
        ∫ z, (radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖) +
          α * (-Real.log (n2EmbScale γ α L r X ω * ‖z‖)) + L / γ) ∂(winIdx K (Sum.inl p))

/-- Dyadic circles of the window `closedBall 0 r₁`, `r₁ < r`, are local measures. -/
theorem isLocalH_fc_of_le {r r₁ : ℝ} (hr₁r : r₁ < r) {c : ℂ} {k : ℕ}
    (hc : ‖c‖ + radius k ≤ r₁) : K3.IsLocalH 0 r (foldedCircle c (radius k)) :=
  ⟨isAdmissibleH_foldedCircle' c (radius_pos k), r₁, hr₁r,
    measure_mono_null (compl_subset_compl.2 (Metric.closedBall_subset_closedBall hc))
      (foldedCircle_compl_closedBall (radius_pos k))⟩

/-- A.s. the local field is its own regularization at every local dyadic folded circle. -/
theorem ae_evalReg_locZField_dyadic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {r r₁ : ℝ}
    (hr : 0 < r) (hr₁r : r₁ < r) :
    ∀ᵐ ω ∂P, ∀ n k : ℕ, ∀ c ∈ Set.range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      evalReg (locZField X r ω) (foldedCircle c (radius k)) =
        locZField X r ω (foldedCircle c (radius k)) := by
  rw [ae_all_iff]; intro n
  rw [ae_all_iff]; intro k
  rw [ae_ball_iff (countable_range_dyadicRoundC n)]
  intro c _
  by_cases hc : ‖c‖ + radius k ≤ r₁
  · filter_upwards [ae_evalReg_locZField hX hr (isLocalH_fc_of_le hr₁r hc)
      (regAt_foldedCircle hX c (radius_pos k))] with ω h _
    exact h
  · exact ae_of_all _ fun ω h => absurd h hc

theorem exp_neg_one_lt_half : Real.exp (-1) < 1 / 2 := by
  have h1 : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp one_ne_zero
  have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-1)]

/-- On `{Tc ≥ log K + 1}` the embedding scale maps the window into `ball 0 (r/2)`. -/
theorem n2EmbScale_mul_lt {γ α L r : ℝ} {Ω : Type*} {X : Ω → FieldSample} {ω : Ω} (hr : 0 < r)
    {K : ℕ} (hK : 0 < K)
    (hT : Real.log K + 1 ≤ ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω) :
    n2EmbScale γ α L r X ω * K < r / 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : n2EmbScale γ α L r X ω * K =
      r * Real.exp (-ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω + Real.log K) := by
    rw [n2EmbScale, Real.exp_add, Real.exp_log hKpos]; ring
  have h2 : Real.exp (-ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω + Real.log K) ≤
      Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  rw [h1]
  nlinarith [exp_neg_one_lt_half]

/-- **The splitting on the good event, at any finite measure** carried by a compact part of
`Hbar \ {0}` inside `ball 0 (r/2)` with `log‖·‖` integrable, at which the regularizations of the
regular version converge. -/
theorem n2Split_of_good {γ α L r : ℝ} {Ω : Type*} {X : Ω → FieldSample} {ω : Ω}
    {g : ℂ × ℝ → ℝ} {H : ℂ → ℝ} {x₀ K' : ℝ} (hr : 0 < r) (hF : IsRegularWith (X ω) g)
    (hgc : ContinuousOn g (Hbar ×ˢ Ioi 0)) (hHc : Continuous H)
    (hA : ∀ n k : ℕ, ∀ c ∈ Set.range (dyadicRoundC n), ‖c‖ + radius k ≤ r / 2 →
      locZField X r ω (foldedCircle c (radius k)) = X ω (foldedCircle c (radius k)) -
        ∫ u, H u ∂foldedCircle c (radius k) - x₀)
    (hE : ∀ n k : ℕ, ∀ c ∈ Set.range (dyadicRoundC n), ‖c‖ + radius k ≤ r / 2 →
      evalReg (locZField X r ω) (foldedCircle c (radius k)) =
        locZField X r ω (foldedCircle c (radius k)))
    (hc : Continuous fun t => zRadB X r t ω) (hK' : ∀ s : ℝ≥0, |zRadB X r s ω| ≤ 1 * s + K')
    {ν : Measure ℂ} [IsFiniteMeasure ν] {m : ℝ} (hm : m < r / 2)
    (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) ν) {l : ℝ}
    (hGl : Tendsto (fun k => ∫ w, g (w, radius k) ∂ν) atTop (𝓝 l)) :
    Integrable (fun w : ℂ => radPsi X r ω ‖w‖) ν ∧
      evalReg (n2Model γ α L r X ω) ν = evalReg (n2LatY X r ω) ν +
        ∫ w, (radPsi X r ω ‖w‖ + α * -Real.log ‖w‖ + L / γ) ∂ν := by
  set r₁ := r / 2 with hr₁_def
  have hr₁r : r₁ < r := by linarith
  set Z := locZField X r ω with hZ_def
  set Φ : ℕ → ℂ → ℝ := fun k w => g (w, radius k) - ∫ u, H u ∂foldedCircle w (radius k) - x₀
    with hΦ_def
  set ψ := radPsi X r ω with hψ_def
  have hψ : LogDom ψ r (√2 * K') √2 := logDom_radPsi hr hc hK'
  -- the three fields on the local dyadic circles
  have hM : ∀ n k, ∀ c ∈ range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      n2Model γ α L r X ω (foldedCircle c (radius k)) = Z (foldedCircle c (radius k)) +
        ∫ u, α * -Real.log ‖u‖ ∂foldedCircle c (radius k) + L / γ := by
    intro n k c hc' hck
    obtain ⟨z, rfl⟩ := hc'
    have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet r :=
      ⟨n, k, z, by linarith, rfl⟩
    have hloc := isLocalH_of_mem_circSet hmem
    simp only [n2Model, locModel, dite_eq_left_of_eq_true (eq_true hmem), localZ, circData,
      add_zero]
    rw [hZ_def, locZField_apply_of_local X ω hloc]
  have hY : ∀ n k, ∀ c ∈ range (dyadicRoundC n), ‖c‖ + radius k ≤ r₁ →
      n2LatY X r ω (foldedCircle c (radius k)) = Z (foldedCircle c (radius k)) -
        ∫ u, ψ ‖u‖ ∂foldedCircle c (radius k) := by
    intro n k c hc' hck
    have hloc := isLocalH_fc_of_le hr₁r hck
    simp only [n2LatY, ite_eq_left_of_eq_true _ _ (eq_true hloc), lateralPart]
    rw [hE n k c hc' hck]
    congr 1
    refine integral_congr_ae ?_
    have hb : ∀ᵐ u ∂foldedCircle c (radius k),
        u ∈ Metric.closedBall ((0 : ℝ) : ℂ) (‖c‖ + radius k) :=
      (ae_iff (p := fun u => u ∈ Metric.closedBall ((0 : ℝ) : ℂ) (‖c‖ + radius k))).2
        (by simpa only [Set.compl_def] using foldedCircle_compl_closedBall (d := c) (radius_pos k))
    filter_upwards [F1.ae_ne_zero_fc c (radius_pos k), hb] with u hu0 hu
    have hu' : ‖u‖ ≤ ‖c‖ + radius k := by simpa using hu
    exact radAvgReg_eq_radPsi X hr ω (norm_pos_iff.2 hu0) (by linarith)
  have hZc : ∀ k, ∀ w ∈ Hbar, ‖w‖ + radius k < r₁ →
      Tendsto (fun n => Z (foldedCircle (dyadicRoundC n w) (radius k))) atTop (𝓝 (Φ k w)) := by
    intro k w hw hwk
    have h1 : Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n w) (radius k))) atTop
        (𝓝 (g (w, radius k))) := hF.2.1 k w hw
    have h2 : Tendsto (fun n => ∫ u, H u ∂foldedCircle (dyadicRoundC n w) (radius k)) atTop
        (𝓝 (∫ u, H u ∂foldedCircle w (radius k))) := by
      have hcI : Continuous (fun q : ℂ × ℝ => ∫ u, H u ∂foldedCircle q.1 q.2) :=
        continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun hHc.continuousOn)
      have hp : Tendsto (fun n => (dyadicRoundC n w, radius k)) atTop (𝓝 (w, radius k)) :=
        (RegClosure.tendsto_dyadicRoundC w).prodMk_nhds tendsto_const_nhds
      have h3 := (hcI.tendsto (w, radius k)).comp hp
      simp only [Function.comp_def] at h3
      exact h3
    refine ((h1.sub h2).sub_const x₀).congr' ?_
    filter_upwards [eventually_dyadic_le hwk] with n hn
    rw [hA n k (dyadicRoundC n w) (Set.mem_range_self w) hn]
  -- integrability on the compact support
  set S := Metric.closedBall (0 : ℂ) m ∩ Hbar with hS_def
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hνS : ∀ᵐ w ∂ν, w ∈ S := by
    filter_upwards [hν] with w hw
    exact ⟨by rw [mem_closedBall_zero_iff]; exact hw.2.2, hw.1⟩
  have hint : ∀ f : ℂ → ℝ, ContinuousOn f S → Integrable f ν := fun f hf => by
    have := hf.integrableOn_compact (μ := ν) hSc
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hνS] at this
  have hHcI : Continuous (fun q : ℂ × ℝ => ∫ u, H u ∂foldedCircle q.1 q.2) :=
    continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun hHc.continuousOn)
  have hGi : ∀ k, Integrable (fun w => g (w, radius k)) ν := fun k =>
    hint _ (hgc.comp (continuousOn_id.prodMk continuousOn_const)
      (fun z hz => ⟨hz.2, radius_pos k⟩))
  have hHi : ∀ k, Integrable (fun w => ∫ u, H u ∂foldedCircle w (radius k)) ν := fun k =>
    hint _ (hHcI.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hΦi : ∀ᶠ k in atTop, Integrable (Φ k) ν :=
    Eventually.of_forall fun k => ((hGi k).sub (hHi k)).sub (integrable_const _)
  have hD : Tendsto (fun k => ∫ w, (∫ u, H u ∂foldedCircle w (radius k)) ∂ν)
      atTop (𝓝 (∫ w, H w ∂ν)) := by
    obtain ⟨Mb, hMb⟩ := (isCompact_closedBall (0 : ℂ) (m + 1)).exists_bound_of_continuousOn
      hHc.continuousOn
    refine tendsto_integral_of_dominated_convergence (fun _ => Mb) (fun k => ?_)
      (integrable_const Mb) (fun k => ?_) ?_
    · exact (hHcI.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [hν] with w hw
      have hb : ∀ᵐ u ∂foldedCircle w (radius k), ‖H u‖ ≤ Mb := by
        filter_upwards [ae_iff.2 (foldedCircle_compl_closedBall (d := w) (radius_pos k))]
          with u hu
        have hu' : ‖u‖ ≤ ‖w‖ + radius k := by simpa using hu
        exact hMb u (by
          rw [mem_closedBall_zero_iff]; linarith [radius_le_one' k, hw.2.2])
      have := norm_integral_le_of_norm_le_const hb
      simpa using this
    · filter_upwards [hν] with w hw using tendsto_integral_fc_radius hHc hw.1
  have hΦl : Tendsto (fun k => ∫ w, Φ k w ∂ν) atTop
      (𝓝 (l - ∫ w, H w ∂ν - ν.real univ * x₀)) := by
    refine ((hGl.sub hD).sub_const _).congr fun k => ?_
    rw [hΦ_def]
    simp only
    rw [integral_sub, integral_sub (hGi k) (hHi k), integral_const, smul_eq_mul]
    · exact (hGi k).sub (hHi k)
    · exact integrable_const _
  exact evalReg_split_core (M := n2Model γ α L r X ω) (Y := n2LatY X r ω)
    (Z := Z) (Φ := Φ) (α := α) (c₀ := L / γ) hψ hr hr₁r.le hm hM hY hZc hν hlog hΦi hΦl

/-- **N2-H3-SPLIT' on the folded circles of the window: PROVED.** -/
theorem n2H3SplitWinCircStmt_holds : N2H3SplitWinCircStmt := by
  intro γ α r Ω _ P _ X _ _ _ hr hX K hK L _ p
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hr₁0 : 0 < r / 2 := by positivity
  have hr₁r : r / 2 < r := by linarith
  have hBM := isBrownianReal_zRadB hX hr
  filter_upwards [hG.reg, ae_locZField_dyadic_fc hX hr hr₁0 hr₁r,
    ae_evalReg_locZField_dyadic hX hr hr₁r, hBM.cont,
    WedgeInf.ae_abs_le_of_isBrownianReal hBM] with ω hF hA hE hc hgr
  intro hT
  obtain ⟨K', hK'⟩ := hgr 1 one_pos
  set d := p.1.1 with hd_def
  set ρ := p.1.2 with hρ_def
  have hρ : 0 < ρ := p.2.1
  have hdK : ‖d‖ + ρ < K := p.2.2
  have haK := n2EmbScale_mul_lt (α := α) (L := L) (γ := γ) hr hK hT
  set a := n2EmbScale γ α L r X ω with ha_def
  have ha : 0 < a := mul_pos hr (Real.exp_pos _)
  -- the rescaled circle
  set ν := foldedCircle ((a : ℂ) * d) (a * ρ) with hν_def
  have haρ : 0 < a * ρ := mul_pos ha hρ
  set m := ‖(a : ℂ) * d‖ + a * ρ with hm_def
  have hm : m < r / 2 := by
    have : m = a * (‖d‖ + ρ) := by rw [hm_def, F1.norm_mul_real ha]; ring
    rw [this]; nlinarith
  have hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m := by
    have hb : ∀ᵐ u ∂ν, u ∈ Metric.closedBall ((0 : ℝ) : ℂ) m :=
      (ae_iff (p := fun u => u ∈ Metric.closedBall ((0 : ℝ) : ℂ) m)).2
        (by simpa only [Set.compl_def] using foldedCircle_compl_closedBall (d := (a : ℂ) * d) haρ)
    filter_upwards [RegClosure.fc_ae_mem_Hbar _ _, F1.ae_ne_zero_fc _ haρ, hb] with w h1 h2 h3
    exact ⟨h1, h2, by simpa using h3⟩
  have hlog : Integrable (fun w => Real.log ‖w‖) ν := CoordReg.integrable_log_norm_foldedCircle _ _
  -- convergence of the regularizations at `ν` (clause 3 of `IsRegularWith`)
  have hGl : Tendsto (fun k => ∫ w, G ω (w, radius k) ∂ν) atTop
      (𝓝 (G ω (foldH ((a : ℂ) * d), a * ρ))) := by
    have hp : (foldH ((a : ℂ) * d), a * ρ) ∈ Hbar ×ˢ Ioi (0 : ℝ) :=
      ⟨CircleFubini.foldH_mem_Hbar' _, haρ⟩
    have hT' := (hF.2.2.tendsto_at hp).comp RegClosure.tendsto_radius_nhdsGT
    refine hT'.congr fun k => ?_
    simp only [Function.comp_apply, hν_def, fc_foldH_eq]
  obtain ⟨hint, hsplit⟩ := n2Split_of_good (γ := γ) (α := α) (L := L) hr hF (hG.cont ω)
    (K3.continuous_harmH hX hr hr₁0 hr₁r ω) hA hE hc hK' hm hν hlog hGl
  -- back to the window measure
  have hμ : winIdx K (Sum.inl p) = foldedCircle d ρ := rfl
  have hμb : ∀ᵐ u ∂foldedCircle d ρ, u ≠ 0 ∧ a * ‖u‖ ≤ r := by
    have hb : ∀ᵐ u ∂foldedCircle d ρ, u ∈ Metric.closedBall ((0 : ℝ) : ℂ) (‖d‖ + ρ) :=
      (ae_iff (p := fun u => u ∈ Metric.closedBall ((0 : ℝ) : ℂ) (‖d‖ + ρ))).2
        (by simpa only [Set.compl_def] using foldedCircle_compl_closedBall (d := d) hρ)
    filter_upwards [F1.ae_ne_zero_fc d hρ, hb] with u hu0 hu
    have hu' : ‖u‖ ≤ ‖d‖ + ρ := by simpa using hu
    refine ⟨hu0, ?_⟩
    have : a * ‖u‖ ≤ a * K := by nlinarith
    linarith
  have hpt : ∀ᵐ u ∂foldedCircle d ρ,
      radPsi X r ω ‖(a : ℂ) * u‖ = radAvgReg (locZField X r ω) (a * ‖u‖) := by
    filter_upwards [hμb] with u hu
    rw [F1.norm_mul_real ha, radAvgReg_eq_radPsi X hr ω (mul_pos ha (norm_pos_iff.2 hu.1)) hu.2]
  rw [hμ, fc_map_mul d ρ ha]
  refine ⟨(F1.integrable_fc_mul ha d ρ hint).congr hpt, ?_⟩
  rw [hsplit, F1.integral_fc_mul ha d ρ]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hpt] with u hu
  rw [hu, F1.norm_mul_real ha]

end D3Plus
end QuantumZipper
