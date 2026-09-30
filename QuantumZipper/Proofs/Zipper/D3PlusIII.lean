import QuantumZipper.Proofs.Zipper.D3PlusStmt
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.AtomlessUncond
import QuantumZipper.Proofs.LQG.WedgeFinZeroSum

/-!
# D3⁺(iii): the local scale of the zoom model tends to `0` (proved)

Decision D23; statement `D3Plus.D3PlusIIIStmt` (`D3PlusStmt.lean`). Paper: Sheffield,
arXiv:1012.4797, proof of Prop. 1.6 (p. 25): adding the constant `C/γ` multiplies the quantum area
by `e^C`, so the ball of unit area shrinks to the marked point, because the area measure is finite
near the marked point (`α < Q`) and charges every neighbourhood of it.

## Proof

* `eventually_sInf_pos_lt` (deterministic, own elementary argument): for a measure `ν` that charges
  every half-ball `ball 0 a ∩ ℍ` and is finite on one of them, the radius
  `sInf {a > 0 | 1 ≤ e^L ν(ball 0 a ∩ ℍ)}` is eventually in `(0, ε)`. Upper bound: `ε/2` is in the
  set once `e^L ν(ball 0 (ε/2) ∩ ℍ) ≥ 1`. Positivity: continuity from above gives `δ > 0` with
  `e^L ν(ball 0 δ ∩ ℍ) < 1`, so every element of the set is `≥ δ`.
* `qAreaMeasureOn_zoomModel` (local rule): for a regular sample `x` whose area approximations
  converge vaguely on `ℍ` to `μ`, the local area measure of the model field on the half-disc is
  `e^L · (μ|_U).withDensity (exp(γψ))` with `ψ = α(−log‖·‖) + g − x ρ₀`
  (`LocalRule.isVagueLimitOn_add_ofFun` on `W = ball 0 r \ {0}`, where `ψ` is continuous).
* The inputs for the free field, all proved in the project: `AreaExist.ae_isVagueLimitOn_qAreaMeasure`
  (existence), `AreaOffsets.ae_isLQGGood` (regularity), `PositivityArea.ae_forall_pos_qAreaMeasure`
  (positivity on open sets, M4-P2), `WedgeFinZero.ae_withDensity_ball_lt_top` (finiteness of
  `∫_{B(0,1) ∩ ℍ} ‖z‖^{−αγ} dμ` for `α < Q`, WEDGE-FIN0). The correction `g` is continuous, hence
  bounded, on the compact `closedBall 0 (r/2) ∩ Hbar` (harmonicity of `g ∘ foldH`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The deterministic core -/

/-- **Deterministic core of D3⁺(iii)** (own elementary argument). -/
theorem eventually_sInf_pos_lt {ν : Measure ℂ}
    (hpos : ∀ a : ℝ, 0 < a → 0 < ν (Metric.ball 0 a ∩ H))
    (hfin : ∃ a₀ : ℝ, 0 < a₀ ∧ ν (Metric.ball 0 a₀ ∩ H) ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L in atTop,
      0 < sInf {a : ℝ | 0 < a ∧ 1 ≤ ENNReal.ofReal (Real.exp L) * ν (Metric.ball 0 a ∩ H)} ∧
      sInf {a : ℝ | 0 < a ∧ 1 ≤ ENNReal.ofReal (Real.exp L) * ν (Metric.ball 0 a ∩ H)} < ε := by
  have hm : 0 < ν (Metric.ball 0 (ε / 2) ∩ H) := hpos _ (half_pos hε)
  have ht : Tendsto (fun L : ℝ => ENNReal.ofReal (Real.exp L)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_atTop.comp Real.tendsto_exp_atTop
  have ht2 : Tendsto (fun L : ℝ => ENNReal.ofReal (Real.exp L) * ν (Metric.ball 0 (ε / 2) ∩ H))
      atTop (𝓝 ⊤) := by
    have := ENNReal.Tendsto.mul_const (b := ν (Metric.ball 0 (ε / 2) ∩ H)) ht
      (Or.inl ENNReal.top_ne_zero)
    rwa [ENNReal.top_mul hm.ne'] at this
  have hev : ∀ᶠ L : ℝ in atTop,
      1 ≤ ENNReal.ofReal (Real.exp L) * ν (Metric.ball 0 (ε / 2) ∩ H) :=
    ht2.eventually (eventually_ge_nhds ENNReal.one_lt_top)
  obtain ⟨a₀, ha₀, hfa₀⟩ := hfin
  -- continuity from above along `a₀ / (n + 1)`
  set s : ℕ → Set ℂ := fun n => Metric.ball 0 (a₀ / ((n : ℝ) + 1)) ∩ H with hs
  have hanti : Antitone s := by
    intro m n hmn
    refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have h2 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    exact div_le_div_of_nonneg_left ha₀.le h1 h2
  have hinter : (⋂ n, s n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => by
      have : (0 : ℝ) < z.im := (mem_iInter.1 hz 0).2
      rw [h] at this; simp at this
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hz0 ha₀)
    have hzn := (mem_iInter.1 hz n).1
    rw [Metric.mem_ball, dist_zero_right] at hzn
    have : a₀ / ((n : ℝ) + 1) < ‖z‖ := by
      rw [lt_div_iff₀ ha₀] at hn
      rw [div_eq_inv_mul]; simpa [one_div] using hn
    linarith
  have hfs : ∃ i, ν (s i) ≠ ⊤ := ⟨0, by
    refine ne_top_of_le_ne_top hfa₀ (measure_mono (inter_subset_inter_left _
      (Metric.ball_subset_ball ?_)))
    simp⟩
  have hlim : Tendsto (ν ∘ s) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := ν)
      (fun n => (Metric.isOpen_ball.inter isOpen_H).measurableSet.nullMeasurableSet) hanti hfs
    rwa [hinter, measure_empty] at this
  filter_upwards [hev] with L hL
  set S := {a : ℝ | 0 < a ∧ 1 ≤ ENNReal.ofReal (Real.exp L) * ν (Metric.ball 0 a ∩ H)} with hS
  have hbdd : BddBelow S := ⟨0, fun a ha => ha.1.le⟩
  have hmem : ε / 2 ∈ S := ⟨half_pos hε, hL⟩
  refine ⟨?_, (csInf_le hbdd hmem).trans_lt (half_lt_self hε)⟩
  -- a radius `δ > 0` below every element of `S`
  have hL0 : Tendsto (fun n => ENNReal.ofReal (Real.exp L) * (ν ∘ s) n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.exp L)) hlim
      (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  obtain ⟨n, hn⟩ := (hL0.eventually (gt_mem_nhds zero_lt_one)).exists
  have hδ : 0 < a₀ / ((n : ℝ) + 1) := by positivity
  refine lt_of_lt_of_le hδ (le_csInf ⟨_, hmem⟩ fun a ha => ?_)
  by_contra hlt
  push Not at hlt
  have hle : ν (Metric.ball 0 a ∩ H) ≤ ν (s n) :=
    measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hlt.le))
  have := ha.2.trans (mul_le_mul' le_rfl hle)
  exact absurd (this.trans_lt hn) (lt_irrefl _)

/-! ## The local area measure of the model field -/

/-- The density of the model field at level `0` with respect to the free-field area measure. -/
def zoomDensity (γ α : ℝ) (ρ₀ : Measure ℂ) (x : FieldSample) (g : ℂ → ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * (α * -Real.log ‖z‖ + g z - x ρ₀)))

theorem halfDisc_subset_ball_diff (r : ℝ) : halfDisc r ⊆ Metric.ball (0 : ℂ) r \ {0} :=
  fun z hz => ⟨hz.1, fun h => by
    have h2 : (0 : ℝ) < z.im := hz.2
    rw [Set.mem_singleton_iff.1 h] at h2
    simp at h2⟩

theorem continuousOn_g_of_harm {g : ℂ → ℝ} {r : ℝ}
    (harm : InnerProductSpace.HarmonicOnNhd (fun z => g (foldH z)) (Metric.ball (0 : ℂ) r)) :
    ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar) :=
  (harm.continuousOn.mono inter_subset_left).congr fun z hz =>
    by simp only [CircleFubini.foldH_of_mem' hz.2]

theorem continuousOn_zoomPot {γ α L : ℝ} {ρ₀ : Measure ℂ} {x : FieldSample} {g : ℂ → ℝ} {r : ℝ}
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    ContinuousOn (fun z => α * -Real.log ‖z‖ + g z + (L / γ - x ρ₀))
      ((Metric.ball (0 : ℂ) r \ {0}) ∩ Hbar) := by
  have hlog : ContinuousOn (fun z : ℂ => Real.log ‖z‖) ((Metric.ball (0 : ℂ) r \ {0}) ∩ Hbar) :=
    Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz =>
      norm_ne_zero_iff.2 hz.1.2
  refine ((continuousOn_const.mul hlog.neg).add (hg.mono ?_)).add continuousOn_const
  exact fun z hz => ⟨hz.1.1, hz.2⟩

/-- **Local rule for the model field.** If `x` is regular and its area approximations converge
vaguely on `ℍ` to `μ`, the local area measure of `zoomModel γ α L ρ₀ x g` on `halfDisc r` is
`e^L · (μ|_{halfDisc r}).withDensity (zoomDensity …)`. -/
theorem qAreaMeasureOn_zoomModel {γ α L r : ℝ} (hγ : γ ≠ 0) {ρ₀ : Measure ℂ} {x : FieldSample}
    {g : ℂ → ℝ} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ x) μ)
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    qAreaMeasureOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r) =
      ENNReal.ofReal (Real.exp L) •
        (μ.restrict (halfDisc r)).withDensity (zoomDensity γ α ρ₀ x g) := by
  have hU := isOpen_halfDisc r
  have hres := AtomlessUncond.isVagueLimitOn_restrict hU (halfDisc_subset_H r) hμ
  have hW : IsOpen (Metric.ball (0 : ℂ) r \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  rw [zoomModel, LocalRule.qAreaMeasureOn_eq hU (LocalRule.isVagueLimitOn_add_ofFun hx hU
    (halfDisc_subset_H r) hres hW (halfDisc_subset_ball_diff r) (continuousOn_zoomPot hg)),
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul, zoomDensity]
  rw [← ENNReal.ofReal_mul (Real.exp_pos L).le, ← Real.exp_add]
  congr 2
  field_simp
  ring

/-- The local scale of the model field is the radius of `eventually_sInf_pos_lt`. -/
theorem scaleParamOn_zoomModel {γ α L r : ℝ} (hγ : γ ≠ 0) {ρ₀ : Measure ℂ} {x : FieldSample}
    {g : ℂ → ℝ} (hx : IsRegularSample x) {μ : Measure ℂ}
    (hμ : IsVagueLimitOn H (areaApprox γ x) μ)
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    scaleParamOn γ (zoomModel γ α L ρ₀ x g) (halfDisc r) =
      sInf {a : ℝ | 0 < a ∧ 1 ≤ ENNReal.ofReal (Real.exp L) *
        (μ.restrict (halfDisc r)).withDensity (zoomDensity γ α ρ₀ x g) (Metric.ball 0 a ∩ H)} := by
  rw [scaleParamOn, qAreaMeasureOn_zoomModel hγ hx hμ hg]
  rfl

/-! ## Positivity and finiteness of the model measure near `0` -/

theorem zoomDensity_ne_zero (γ α : ℝ) (ρ₀ : Measure ℂ) (x : FieldSample) (g : ℂ → ℝ) (z : ℂ) :
    zoomDensity γ α ρ₀ x g z ≠ 0 := by
  rw [zoomDensity, Ne, ENNReal.ofReal_eq_zero, not_le]
  exact Real.exp_pos _

theorem continuousOn_zoomDensity {γ α r : ℝ} {ρ₀ : Measure ℂ} {x : FieldSample} {g : ℂ → ℝ}
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    ContinuousOn (zoomDensity γ α ρ₀ x g) ((Metric.ball (0 : ℂ) r \ {0}) ∩ Hbar) := by
  have hlog : ContinuousOn (fun z : ℂ => Real.log ‖z‖) ((Metric.ball (0 : ℂ) r \ {0}) ∩ Hbar) :=
    Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz =>
      norm_ne_zero_iff.2 hz.1.2
  have hpot : ContinuousOn (fun z => α * -Real.log ‖z‖ + g z - x ρ₀)
      ((Metric.ball (0 : ℂ) r \ {0}) ∩ Hbar) :=
    ((continuousOn_const.mul hlog.neg).add (hg.mono fun z hz => ⟨hz.1.1, hz.2⟩)).sub
      continuousOn_const
  exact ENNReal.continuous_ofReal.comp_continuousOn
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hpot))

/-- The model measure charges every half-ball around `0`. -/
theorem zoomMeasure_pos {γ α r : ℝ} (hr : 0 < r) {ρ₀ : Measure ℂ} {x : FieldSample} {g : ℂ → ℝ}
    {μ : Measure ℂ} (hμpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < μ V)
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    ∀ a : ℝ, 0 < a →
      0 < (μ.restrict (halfDisc r)).withDensity (zoomDensity γ α ρ₀ x g) (Metric.ball 0 a ∩ H) := by
  intro a ha
  have hSm : MeasurableSet (Metric.ball (0 : ℂ) a ∩ H) :=
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  rw [withDensity_apply _ hSm, Measure.restrict_restrict hSm]
  set V := (Metric.ball (0 : ℂ) a ∩ H) ∩ halfDisc r with hVdef
  have hVo : IsOpen V := (Metric.isOpen_ball.inter isOpen_H).inter (isOpen_halfDisc r)
  have hVH : V ⊆ H := fun z hz => hz.1.2
  have hVne : V.Nonempty := by
    set t : ℝ := min a r / 2 with ht
    have ht0 : 0 < t := by positivity
    have hta : t < a := by linarith [min_le_left a r]
    have htr : t < r := by linarith [min_le_right a r]
    have hn : ‖(t : ℂ) * Complex.I‖ = t := by simp [abs_of_pos ht0]
    have him : ((t : ℂ) * Complex.I).im = t := by simp
    have hH : (t : ℂ) * Complex.I ∈ H := show 0 < ((t : ℂ) * Complex.I).im by rw [him]; exact ht0
    refine ⟨(t : ℂ) * Complex.I, ⟨?_, hH⟩, ?_, hH⟩
    · rw [Metric.mem_ball, dist_zero_right, hn]; exact hta
    · rw [Metric.mem_ball, dist_zero_right, hn]; exact htr
  have hμV := hμpos V hVo hVH hVne
  have hVsub : V ⊆ (Metric.ball (0 : ℂ) r \ {0}) ∩ Hbar := fun z hz =>
    ⟨halfDisc_subset_ball_diff r hz.2, show (0 : ℝ) ≤ z.im from le_of_lt hz.2.2⟩
  have hmeas : AEMeasurable (zoomDensity γ α ρ₀ x g) (μ.restrict V) :=
    ((continuousOn_zoomDensity hg).mono hVsub).aemeasurable hVo.measurableSet
  refine pos_iff_ne_zero.2 fun h0 => ?_
  rw [lintegral_eq_zero_iff' hmeas] at h0
  have h1 := ae_iff.1 h0
  have e : {z | ¬ zoomDensity γ α ρ₀ x g z = (0 : ℂ → ℝ≥0∞) z} = Set.univ :=
    Set.eq_univ_of_forall fun z => zoomDensity_ne_zero γ α ρ₀ x g z
  rw [e, Measure.restrict_apply_univ] at h1
  exact hμV.ne' h1

/-- The model measure is finite on a half-ball around `0` (`α < Q`, through the free-field bound
`∫_{B(0,1) ∩ ℍ} ‖z‖^{−αγ} dμ < ∞`). -/
theorem zoomMeasure_fin {γ α r : ℝ} (hγ : 0 < γ) (hr : 0 < r) {ρ₀ : Measure ℂ} {x : FieldSample}
    {g : ℂ → ℝ} {μ : Measure ℂ}
    (hfin : (μ.withDensity fun z => ENNReal.ofReal (‖z‖ ^ (-(α * γ))))
      (Metric.ball 0 1 ∩ H) < ⊤)
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (μ.restrict (halfDisc r)).withDensity (zoomDensity γ α ρ₀ x g) (Metric.ball 0 a₀ ∩ H) ≠ ⊤ := by
  have hHbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have hK : IsCompact (Metric.closedBall (0 : ℂ) (r / 2) ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right hHbar
  have hKsub : Metric.closedBall (0 : ℂ) (r / 2) ∩ Hbar ⊆ Metric.ball (0 : ℂ) r ∩ Hbar :=
    fun z hz => ⟨Metric.closedBall_subset_ball (by linarith) hz.1, hz.2⟩
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hg.mono hKsub)
  set a₀ : ℝ := min 1 (r / 2) with ha₀
  refine ⟨a₀, by positivity, ?_⟩
  have hSm : MeasurableSet (Metric.ball (0 : ℂ) a₀ ∩ H) :=
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  have hS1 : MeasurableSet (Metric.ball (0 : ℂ) 1 ∩ H) :=
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  rw [withDensity_apply _ hSm, Measure.restrict_restrict hSm]
  set V := (Metric.ball (0 : ℂ) a₀ ∩ H) ∩ halfDisc r with hVdef
  have hVm : MeasurableSet V := hSm.inter (isOpen_halfDisc r).measurableSet
  set C := ENNReal.ofReal (Real.exp (γ * (M - x ρ₀))) with hC
  set h : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z‖ ^ (-(α * γ))) with hh
  have hle : ∫⁻ z in V, zoomDensity γ α ρ₀ x g z ∂μ ≤ ∫⁻ z in V, C * h z ∂μ := by
    refine setLIntegral_mono' hVm fun z hz => ?_
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (halfDisc_subset_ball_diff r hz.2).2
    have hzK : z ∈ Metric.closedBall (0 : ℂ) (r / 2) ∩ Hbar := by
      refine ⟨?_, show (0 : ℝ) ≤ z.im from le_of_lt hz.1.2⟩
      have := hz.1.1
      rw [Metric.mem_ball, dist_zero_right] at this
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [min_le_right 1 (r / 2)]
    have hgz : g z ≤ M := hM (mem_image_of_mem g hzK)
    simp only [zoomDensity, hC, hh]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_def_of_pos hz0, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : γ * g z ≤ γ * M := mul_le_mul_of_nonneg_left hgz hγ.le
    nlinarith [h1]
  have h2 : ∫⁻ z in V, C * h z ∂μ = C * ∫⁻ z in V, h z ∂μ :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have h3 : ∫⁻ z in V, h z ∂μ ≤ ∫⁻ z in Metric.ball (0 : ℂ) 1 ∩ H, h z ∂μ := by
    refine lintegral_mono_set fun z hz => ⟨?_, hz.1.2⟩
    have := hz.1.1
    rw [Metric.mem_ball, dist_zero_right] at this ⊢
    linarith [min_le_left 1 (r / 2)]
  have h4 : ∫⁻ z in Metric.ball (0 : ℂ) 1 ∩ H, h z ∂μ =
      (μ.withDensity h) (Metric.ball 0 1 ∩ H) := (withDensity_apply _ hS1).symm
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) (hle.trans
    (h2.le.trans (mul_le_mul' le_rfl h3)))
  rw [h4]; exact hfin.ne

/-! ## D3⁺(iii) -/

/-- **D3⁺(iii) holds** (unconditionally): almost surely, for every `ε > 0`, eventually in `L`,
`0 < scaleParamOn γ Y_L (halfDisc r) < ε`. -/
theorem d3PlusIII_holds : D3PlusIIIStmt := by
  intro γ α r ρ₀ Ω _ P _ X E' _ Ξ g hS
  filter_upwards [AreaExist.ae_isVagueLimitOn_qAreaMeasure hS.hX hS.hγ hS.hγ2,
    AreaOffsets.ae_isLQGGood hS.hX hS.hγ hS.hγ2,
    PositivityArea.ae_forall_pos_qAreaMeasure hS.hX hS.hγ hS.hγ2,
    WedgeFinZero.ae_withDensity_ball_lt_top hS.hX hS.hγ hS.hγ2 hS.hα]
    with ω hvag hgood hpos hfin
  intro ε hε
  have hg := continuousOn_g_of_harm (hS.harm ω)
  filter_upwards [eventually_sInf_pos_lt
    (zoomMeasure_pos (γ := γ) (α := α) (ρ₀ := ρ₀) (x := X ω) hS.hr hpos hg)
    (zoomMeasure_fin (ρ₀ := ρ₀) (x := X ω) hS.hγ hS.hr hfin hg) hε] with L hL
  rw [scaleParamOn_zoomModel hS.hγ.ne' hgood.1 hvag hg]
  exact hL

end D3Plus
end QuantumZipper
