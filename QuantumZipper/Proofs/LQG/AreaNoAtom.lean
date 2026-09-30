import QuantumZipper.Proofs.LQG.AreaCircles
import QuantumZipper.Proofs.LQG.AreaLogSing

/-!
# M4-P4, area version with a continuous shift: `AreaLogSingNoAtom` (TASKS.md R14)

Discharges `AreaCircles.AreaLogSingNoAtom` (TASKS.md R14, second theorem; handoff
`handoff/M4-AREA-P3B.md` item 5): for `0 < γ < 2` and a free GFF modulo constants `X`, almost
surely the area approximations of `Z + ofFun (γ(−log ‖· − z‖) + g)`, with `z ∈ ℍ` and `g`
continuous on `Hbar`, converge vaguely on `ℍ` to the quantum area measure of the shifted field,
and that measure charges no mass at `z` (here `Z = aZ X R` is the normalized free field).

Route. The local rule (5.1) is applied in the form used inside
`AtomlessUncond.ae_logSingularity_area`: to the regular field `aZ X R ω` itself, with the
combined potential `logPotC γ z + g`, which is continuous on `Hbar \ {z}`; the result is then
globalized to `H` by `AtomlessUncond.isVagueLimitOn_of_local_of_tight`. The two globalization
hypotheses (finiteness on compacts and tightness near `z`) are obtained from the explicit
decomposition of the smooth factor over folded circles
(`avgReg_add_logPotC_add_ofFun`, `areaApprox_add_logPotC_add_ofFun_apply`) together with the
folded-circle bound `|smoothFun g w 2^{-k}| ≤ M` for a continuous `g` on a compact set of `Hbar`.

Since `ofFun (φ + ψ) ≠ ofFun φ + ofFun ψ` for a field sample (the two sides differ at measures
where one of the integrals is junk), the shift *cannot* be moved out of the `ofFun` by
additivity; the local rule is therefore applied to the combined potential directly.

Own elementary computations (the numerical constant `p` is chosen so that
`γ²(1 + p) < 4`, which is all the tail-sum argument needs); the underlying mathematics is
Duplantier–Sheffield, Invent. Math. 185 (2011), §3 (and Berestycki–Powell, arXiv:2004.04720,
for the fractional moments).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace QuantumZipper
namespace AreaLogSing

open AtomlessUncond
open AreaExist (aZ)
open GoodSample

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-! ### 1. Elementary bounds -/

theorem logFactorA_nonneg' (γ α : ℝ) (z : ℂ) (k : ℕ) (w : ℂ) : 0 ≤ logFactorA γ α z k w := by
  unfold AtomlessUncond.logFactorA
  exact Real.rpow_nonneg (le_trans (radius_pos k).le (le_max_left _ _)) _

theorem mul_le_abs_mul_of_abs_le {γ s M : ℝ} (h : |s| ≤ M) : γ * s ≤ |γ| * M :=
  calc γ * s ≤ |γ * s| := le_abs_self _
    _ = |γ| * |s| := abs_mul γ s
    _ ≤ |γ| * M := mul_le_mul_of_nonneg_left h (abs_nonneg γ)

/-- A continuous function on `Hbar` is bounded by a constant on the folded circles of radius
`2^{-k}` centred in a ball around `z`. -/
theorem exists_abs_smoothFun_le_ball {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (z : ℂ) (δ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w - z‖ ≤ δ → ∀ k : ℕ,
      |smoothFun g w (radius k)| ≤ M := by
  set T : ℝ := ‖z‖ + max δ 0 with hT
  obtain ⟨M₀, hM₀⟩ := (CircleFubini.isCompact_ballH (T + 1)).exists_bound_of_continuousOn
    (hg.mono Set.inter_subset_right)
  refine ⟨max M₀ 0, le_max_right _ _, fun w hw k => ?_⟩
  refine PositivityArea.abs_smooth_le_H (T := T) (M := max M₀ 0) ?_ k ?_
  · intro u hu
    exact le_trans (by simpa [Real.norm_eq_abs] using hM₀ u hu) (le_max_left _ _)
  · calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ T := by
          rw [hT]
          linarith [hw, le_max_left δ 0]

/-- A continuous function on `Hbar` is bounded by a constant on the folded circles of radius
`2^{-k}` centred in a compact subset of `Hbar`. -/
theorem exists_abs_smoothFun_le_compact {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) {K : Set ℂ}
    (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ K, ∀ k : ℕ, |smoothFun g w (radius k)| ≤ M := by
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  set T' : ℝ := max T 0 with hT'
  obtain ⟨M₀, hM₀⟩ := (CircleFubini.isCompact_ballH (T' + 1)).exists_bound_of_continuousOn
    (hg.mono Set.inter_subset_right)
  refine ⟨max M₀ 0, le_max_right _ _, fun w hw k => ?_⟩
  refine PositivityArea.abs_smooth_le_H (T := T') (M := max M₀ 0) ?_ k ?_
  · intro u hu
    exact le_trans (by simpa [Real.norm_eq_abs] using hM₀ u hu) (le_max_left _ _)
  · calc ‖w‖ ≤ T := by simpa using hT w hw
      _ ≤ T' := by rw [hT']; exact le_max_left T 0

/-! ### 2. The folded-circle average of `logPotC α z + g` -/

/-- `logPotC α z` is integrable against a folded circle that does not cross `ℝ`. -/
theorem integrable_logPotC_foldedCircle {α : ℝ} {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hrw : r ≤ w.im) : Integrable (AtomlessUncond.logPotC α z) (foldedCircle w r) := by
  rw [foldedCircle_eq_circleUnif hr.le hrw]
  exact ((CircleMV.integrable_log_norm_sub_circleUnif w z r).neg).const_mul α

/-- Circle average of `logPotC α z + g`: `α(−log max(r, ‖w − z‖)) + ∫ g d(foldedCircle w r)`. -/
theorem integral_logPotC_add_foldedCircle {α : ℝ} {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hrw : r ≤ w.im) {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    ∫ v, (AtomlessUncond.logPotC α z v + g v) ∂foldedCircle w r =
      α * -Real.log (max r ‖w - z‖) + smoothFun g w r := by
  rw [integral_add (integrable_logPotC_foldedCircle hr hrw)
    (RegClosure.integrable_fc hg w hr.le), integral_logPotC_fc hr hrw]
  rfl

/-- The `avgReg` of `x + ofFun (logPotC α z + g)`: the singular part
`α(−log max(2^{-k}, ‖w − z‖))` plus the smoothed continuous shift. -/
theorem avgReg_add_logPotC_add_ofFun {x : FieldSample} {α : ℝ} {z : ℂ} {k : ℕ} {w : ℂ}
    (hx : ∃ l, Tendsto (fun n => x (foldedCircle (dyadicRoundC n w) (radius k))) atTop (𝓝 l))
    (hk : radius k < w.im) {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    avgReg (x + ofFun (fun v => AtomlessUncond.logPotC α z v + g v)) k w =
      avgReg x k w + (α * -Real.log (max (radius k) ‖w - z‖) + smoothFun g w (radius k)) := by
  obtain ⟨l, hl⟩ := hx
  have hr := radius_pos k
  have hd := RegClosure.tendsto_dyadicRoundC w
  have hev : ∀ᶠ n in atTop, radius k < (dyadicRoundC n w).im :=
    ((Complex.continuous_im.tendsto w).comp hd).eventually (lt_mem_nhds hk)
  have hg1 : Continuous fun c : ℂ => α * -Real.log (max (radius k) ‖c - z‖) :=
    continuous_const.mul ((continuous_const.max (continuous_id.sub continuous_const).norm).log
      fun c => (lt_max_of_lt_left hr).ne').neg
  have hlim : Tendsto (fun c : ℂ => α * -Real.log (max (radius k) ‖c - z‖) +
      smoothFun g c (radius k)) (𝓝 w)
      (𝓝 (α * -Real.log (max (radius k) ‖w - z‖) + smoothFun g w (radius k))) :=
    (hg1.tendsto w).add ((continuous_smoothFun hg (radius k)).tendsto w)
  have h2 : Tendsto (fun n => (x + ofFun (fun v => AtomlessUncond.logPotC α z v + g v))
      (foldedCircle (dyadicRoundC n w) (radius k))) atTop
      (𝓝 (l + (α * -Real.log (max (radius k) ‖w - z‖) + smoothFun g w (radius k)))) := by
    refine (hl.add (hlim.comp hd)).congr' ?_
    filter_upwards [hev] with n hn
    simp only [Function.comp, Pi.add_apply, ofFun]
    rw [integral_logPotC_add_foldedCircle hr hn.le hg]
  unfold avgReg
  rw [h2.limUnder_eq, hl.limUnder_eq]

/-! ### 3. The area approximations -/

/-- Decomposition of the area density of `x + ofFun (logPotC α z + g)` against that of `x`: the
log-singular factor `logFactorA γ α z k` times the smoothed shift `e^{γ g_k}`. -/
theorem areaApprox_add_logPotC_add_ofFun_apply {x : FieldSample} (hx : RawConverges' x) (γ α : ℝ)
    (z : ℂ) (k : ℕ) {A : Set ℂ} (hA : MeasurableSet A) (hAk : ∀ w ∈ A, radius k < w.im)
    {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    areaApprox γ (x + ofFun (fun v => AtomlessUncond.logPotC α z v + g v)) k A =
      (areaApprox γ x k).withDensity (fun w => ENNReal.ofReal (logFactorA γ α z k w *
        Real.exp (γ * smoothFun g w (radius k)))) A := by
  have hm : Measurable fun w : ℂ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k w)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((RegClosure.measurable_avgReg_slice x k).const_mul _).exp)
  have hs : Measurable fun w : ℂ =>
      ENNReal.ofReal (Real.exp (γ * smoothFun g w (radius k))) :=
    ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp ((continuous_smoothFun hg (radius k)).const_mul γ)).measurable)
  unfold areaApprox
  rw [show (fun w : ℂ => ENNReal.ofReal (logFactorA γ α z k w *
        Real.exp (γ * smoothFun g w (radius k)))) =
      (fun w : ℂ => ENNReal.ofReal (logFactorA γ α z k w)) *
        (fun w : ℂ => ENNReal.ofReal (Real.exp (γ * smoothFun g w (radius k)))) from
    funext fun w => ENNReal.ofReal_mul (logFactorA_nonneg' γ α z k w)]
  have hfm : Measurable fun w : ℂ => ENNReal.ofReal (logFactorA γ α z k w) :=
    (continuous_logFactorA γ α z k).measurable.ennreal_ofReal
  rw [← withDensity_mul _ hm (hfm.mul hs), withDensity_apply _ hA, withDensity_apply _ hA]
  refine setLIntegral_congr_fun hA fun w hw => ?_
  simp only [Pi.mul_apply]
  have hwH : w ∈ Hbar := show 0 ≤ w.im by linarith [hAk w hw, radius_pos k]
  have hB0 : 0 ≤ radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k w) :=
    mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le
  have hinner : ENNReal.ofReal (logFactorA γ α z k w * Real.exp (γ * smoothFun g w (radius k))) =
      ENNReal.ofReal (logFactorA γ α z k w) *
        ENNReal.ofReal (Real.exp (γ * smoothFun g w (radius k))) :=
    ENNReal.ofReal_mul (logFactorA_nonneg' γ α z k w)
  have houter : ENNReal.ofReal ((radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k w)) *
        (logFactorA γ α z k w * Real.exp (γ * smoothFun g w (radius k)))) =
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k w)) *
        ENNReal.ofReal (logFactorA γ α z k w * Real.exp (γ * smoothFun g w (radius k))) :=
    ENNReal.ofReal_mul hB0
  have hreal : radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * (avgReg x k w + (α * -Real.log (max (radius k) ‖w - z‖) +
        smoothFun g w (radius k)))) =
      (radius k ^ (γ ^ 2 / 2) * Real.exp (γ * avgReg x k w)) *
        (logFactorA γ α z k w * Real.exp (γ * smoothFun g w (radius k))) := by
    have hm0 : 0 < max (radius k) ‖w - z‖ := lt_max_of_lt_left (radius_pos k)
    unfold AtomlessUncond.logFactorA
    rw [Real.rpow_def_of_pos hm0,
      show γ * (avgReg x k w + (α * -Real.log (max (radius k) ‖w - z‖) +
          smoothFun g w (radius k))) =
        γ * avgReg x k w + (Real.log (max (radius k) ‖w - z‖) * (-(α * (2 * γ) / 2)) +
          γ * smoothFun g w (radius k)) by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [avgReg_add_logPotC_add_ofFun (hx k w hwH) (hAk w hw) hg, hreal]
  exact houter.trans (congrArg (fun t => ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
    Real.exp (γ * avgReg x k w)) * t) hinner)

/-! ### 4. Comparison of densities -/

/-- Comparison of `withDensity` measures with a constant: on a set where `ρ₁ ≤ c · ρ₂`. -/
theorem withDensity_le_const_mul {μ : Measure ℂ} {K : Set ℂ} (hKm : MeasurableSet K)
    {ρ₁ ρ₂ : ℂ → ℝ≥0∞} (hρ₂ : Measurable ρ₂) {c : ℝ≥0∞}
    (h : ∀ w ∈ K, ρ₁ w ≤ c * ρ₂ w) :
    μ.withDensity ρ₁ K ≤ c * μ.withDensity ρ₂ K := by
  have h1 : (μ.withDensity ρ₁).restrict K ≤ (μ.restrict K).withDensity (fun w => c * ρ₂ w) := by
    rw [restrict_withDensity hKm]
    exact withDensity_mono ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun w hw => h w hw))
  have h2 : (μ.restrict K).withDensity (fun w => c * ρ₂ w) = c • (μ.restrict K).withDensity ρ₂ := by
    rw [show (fun w : ℂ => c * ρ₂ w) = (fun _ : ℂ => c) * ρ₂ from rfl,
      withDensity_mul _ measurable_const hρ₂, withDensity_const, withDensity_smul_measure]
  calc μ.withDensity ρ₁ K = (μ.withDensity ρ₁).restrict K K :=
        (by rw [Measure.restrict_apply hKm, Set.inter_self])
    _ ≤ ((μ.restrict K).withDensity (fun w => c * ρ₂ w)) K := h1 K
    _ = (c • (μ.restrict K).withDensity ρ₂) K := by rw [h2]
    _ = c * ((μ.restrict K).withDensity ρ₂) K := Measure.smul_apply _ _ _
    _ = c * (μ.withDensity ρ₂) K := by
        rw [← restrict_withDensity hKm (f := ρ₂), Measure.restrict_apply hKm, Set.inter_self]

/-! ### 5. The a.s. vague limit of the shifted field, with no atom at `z` -/

theorem ae_areaLogSingularity_add_ofFun [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) {z : ℂ} (hz : z ∈ H)
    (hP3 : P3bBoundArea P X γ R z) {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) :
    ∀ᵐ ω ∂P,
      IsVagueLimitOn H (areaApprox γ (aZ X R ω +
          ofFun (fun v => AtomlessUncond.logPotC γ z v + g v)))
        (qAreaMeasure γ (aZ X R ω + ofFun (fun v => AtomlessUncond.logPotC γ z v + g v))) ∧
      qAreaMeasure γ (aZ X R ω + ofFun (fun v => AtomlessUncond.logPotC γ z v + g v)) {z} = 0 := by
  -- the exponent `p` of the fractional-moment bound and the tail sum
  set p : ℝ := min (1 / 2) ((4 / γ ^ 2 - 1) / 2) with hpdef
  have hγ2pos : 0 < γ ^ 2 := pow_pos hγ 2
  have h4 : γ ^ 2 < 4 := by nlinarith
  have hp0 : 0 < p := by
    rw [hpdef]
    refine lt_min (by norm_num) (div_pos ?_ two_pos)
    rw [sub_pos, lt_div_iff₀ hγ2pos]
    linarith
  have hp1 : p ≤ 1 := by
    rw [hpdef]; exact le_trans (min_le_left _ _) (by norm_num)
  have hp2 : γ ^ 2 * p ≤ 2 - γ ^ 2 / 2 := by
    rw [hpdef]
    have hval : γ ^ 2 * ((4 / γ ^ 2 - 1) / 2) = 2 - γ ^ 2 / 2 := by
      field_simp; ring
    calc γ ^ 2 * min (1 / 2) ((4 / γ ^ 2 - 1) / 2)
        ≤ γ ^ 2 * ((4 / γ ^ 2 - 1) / 2) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hγ2pos.le
      _ = 2 - γ ^ 2 / 2 := hval
  set e : ℝ := γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2) with he
  have hneg : LogSing.expB (2 * γ) γ * p + e < 0 := by
    have hexp : LogSing.expB (2 * γ) γ = γ ^ 2 := by
      unfold LogSing.expB; rw [max_eq_left hγ.le]; ring
    have hpp : p ^ 2 ≤ p := by nlinarith [hp0, hp1]
    have h3 : γ ^ 2 * p ^ 2 ≤ (2 - γ ^ 2 / 2) * p := by
      have h := mul_le_mul_of_nonneg_right hp2 hp0.le
      nlinarith [h]
    rw [hexp, he]
    nlinarith [h3, hp0, h4]
  obtain ⟨C, hC, n₀, hbd⟩ := hP3 p hp0 hp1
  have hT : ∀ n, Measurable fun ω => annTC (areaApprox γ (aZ X R ω)) z n := fun n =>
    Measurable.iSup fun j => (Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp
      ((measurable_areaApprox γ _).comp (AreaExist.measurable_aZ hX R))
  have hsum := ae_tsum_ne_top_of_moments (P := P) hT hp0 hp1 hneg hC hbd
  filter_upwards [hsum, RegSample.ae_isRegularSample hX,
    AreaExist.ae_isVagueLimitOn_qAreaMeasure_aZ hX hγ hγ2 R] with ω hω hreg hμ
  obtain ⟨N, hN⟩ := hω
  have hz0 : 0 < z.im := hz
  obtain ⟨K1, hK1⟩ := exists_radius_lt (show 0 < z.im / 2 by linarith)
  have hZ : IsRegularSample (aZ X R ω) := hreg.addConst' _
  have hraw : RawConverges' (aZ X R ω) := hZ.rawConverges
  set Y := aZ X R ω + ofFun (fun v => AtomlessUncond.logPotC γ z v + g v) with hY
  set Ys := aZ X R ω + ofFun (AtomlessUncond.logPotC γ z) with hYs
  -- local convergence on `H \ {z}`
  have hU' : IsOpen (H \ {z}) := isOpen_H.sdiff isClosed_singleton
  have hcont : ContinuousOn (fun v : ℂ => AtomlessUncond.logPotC γ z v + g v)
      ({v : ℂ | v ≠ z} ∩ Hbar) := by
    have h1 : ContinuousOn (fun v : ℂ => AtomlessUncond.logPotC γ z v) ({v : ℂ | v ≠ z}) := by
      unfold AtomlessUncond.logPotC
      refine continuousOn_const.mul (ContinuousOn.neg ?_)
      exact ((continuous_id.sub continuous_const).norm.continuousOn).log
        fun u hu => norm_ne_zero_iff.2 (sub_ne_zero.2 hu)
    exact (h1.mono Set.inter_subset_left).add (hg.mono Set.inter_subset_right)
  have hloc0 := LocalRule.isVagueLimitOn_add_ofFun hZ hU' Set.sdiff_subset
    (isVagueLimitOn_restrict hU' Set.sdiff_subset hμ) (W := {v : ℂ | v ≠ z}) isOpen_ne
    (fun w hw => hw.2) (φ := fun v => AtomlessUncond.logPotC γ z v + g v) hcont
  set μ' := ((qAreaMeasure γ (aZ X R ω)).restrict (H \ {z})).withDensity
    (fun w => ENNReal.ofReal (Real.exp (γ * (AtomlessUncond.logPotC γ z w + g w)))) with hμ'
  have hloc : IsVagueLimitOn (H \ {z}) (areaApprox γ Y) μ' := hloc0
  -- finiteness of the approximations on compact subsets of `H`
  have hfin : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ k in atTop, areaApprox γ Y k K < ⊤ := by
    intro K hK hKH
    obtain ⟨F, hF⟩ := hZ
    obtain ⟨d, hd0, -, hdK⟩ := AreaExist.exists_im_lower_bound hK hKH
    obtain ⟨K2, hK2⟩ := exists_radius_lt hd0
    obtain ⟨M, hM0, hM⟩ := exists_abs_smoothFun_le_compact hg hK
    filter_upwards [eventually_ge_atTop K2] with k hk
    have hAk : ∀ w ∈ K, radius k < w.im := fun w hw => (hK2 k hk).trans_le (hdK w hw)
    rw [areaApprox_add_logPotC_add_ofFun_apply hraw γ γ z k hK.measurableSet hAk hg]
    refine lt_of_le_of_lt (withDensity_le_const_mul (μ := areaApprox γ (aZ X R ω) k) hK.measurableSet
      ((continuous_logFactorA γ γ z k).measurable.ennreal_ofReal)
      (ρ₁ := fun w => ENNReal.ofReal (logFactorA γ γ z k w *
        Real.exp (γ * smoothFun g w (radius k))))
      (c := ENNReal.ofReal (Real.exp (|γ| * M))) fun w hw => ?_) ?_
    · rw [ENNReal.ofReal_mul (logFactorA_nonneg' γ γ z k w)]
      calc ENNReal.ofReal (logFactorA γ γ z k w) *
            ENNReal.ofReal (Real.exp (γ * smoothFun g w (radius k)))
          ≤ ENNReal.ofReal (logFactorA γ γ z k w) *
              ENNReal.ofReal (Real.exp (|γ| * M)) :=
            mul_le_mul_of_nonneg_left
              (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_abs_mul_of_abs_le
                (hM w hw k)))) zero_le
        _ = ENNReal.ofReal (Real.exp (|γ| * M)) *
              ENNReal.ofReal (logFactorA γ γ z k w) := mul_comm _ _
    · refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
      refine GoodSample.withDensity_lt_top hK ?_ (continuous_logFactorA γ γ z k).continuousOn
      rw [← GoodSample.areaR_radius γ hF k]
      exact GoodSample.areaR_lt_top γ hF (by rw [one_mul]; exact radius_pos k) hK
  -- smallness near `z`
  have htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop,
      areaApprox γ Y k (Metric.ball z δ) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨M, hM0, hM⟩ := exists_abs_smoothFun_le_ball hg z 1
    obtain ⟨M1, hM1⟩ := exists_radius_lt (show 0 < z.im / 2 by linarith)
    set ε' : ℝ := Real.exp (-(|γ| * M)) * ε with hε'
    have hε'0 : 0 < ε' := by rw [hε']; positivity
    obtain ⟨δ, hδ0, hδ⟩ := tight_of_balls (γ := γ) (α := γ) hγ
      (fun k hk m hm => areaApprox_add_logC_apply hraw γ γ z k
        Metric.isOpen_ball.measurableSet fun w hw => by
          have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
            rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
          rw [Metric.mem_ball, dist_eq_norm] at hw
          have h5 := (abs_le.1 h1).1
          have h6 := hK1 k hk
          have h7 := hM1 m hm
          linarith)
      hN ε' hε'0
    set δ' : ℝ := min δ (min 1 (z.im / 2)) with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ0 (lt_min one_pos (by linarith))
    have hδ'1 : δ' ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ'z : δ' ≤ z.im / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hδ'δ : δ' ≤ δ := min_le_left _ _
    refine ⟨δ', hδ'0, ?_⟩
    filter_upwards [hδ, eventually_ge_atTop K1] with k hk hkK
    have hk1 : radius k < z.im / 2 := hK1 k hkK
    have him : ∀ w ∈ Metric.ball z δ', radius k < w.im := by
      intro w hw
      have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
        rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h5 := (abs_le.1 h1).1
      linarith
    have hcmp := withDensity_le_const_mul (μ := areaApprox γ (aZ X R ω) k)
      Metric.isOpen_ball.measurableSet
      ((continuous_logFactorA γ γ z k).measurable.ennreal_ofReal)
      (ρ₁ := fun w => ENNReal.ofReal (logFactorA γ γ z k w *
        Real.exp (γ * smoothFun g w (radius k))))
      (c := ENNReal.ofReal (Real.exp (|γ| * M))) fun w hw => by
        rw [ENNReal.ofReal_mul (logFactorA_nonneg' γ γ z k w)]
        calc ENNReal.ofReal (logFactorA γ γ z k w) *
              ENNReal.ofReal (Real.exp (γ * smoothFun g w (radius k)))
            ≤ ENNReal.ofReal (logFactorA γ γ z k w) *
                ENNReal.ofReal (Real.exp (|γ| * M)) :=
              mul_le_mul_of_nonneg_left
                (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_abs_mul_of_abs_le
                  (hM w (le_of_lt (lt_of_lt_of_le (by rwa [Metric.mem_ball, dist_eq_norm] at hw)
                    hδ'1)) k)))) zero_le
          _ = ENNReal.ofReal (Real.exp (|γ| * M)) *
                ENNReal.ofReal (logFactorA γ γ z k w) := mul_comm _ _
    have hA4 := areaApprox_add_logPotC_add_ofFun_apply hraw γ γ z k
      Metric.isOpen_ball.measurableSet him hg
    calc areaApprox γ Y k (Metric.ball z δ')
        = (areaApprox γ (aZ X R ω) k).withDensity (fun w => ENNReal.ofReal
            (logFactorA γ γ z k w * Real.exp (γ * smoothFun g w (radius k))))
            (Metric.ball z δ') := hA4
      _ ≤ ENNReal.ofReal (Real.exp (|γ| * M)) *
            (areaApprox γ (aZ X R ω) k).withDensity
              (fun x => ENNReal.ofReal (logFactorA γ γ z k x)) (Metric.ball z δ') := hcmp
      _ = ENNReal.ofReal (Real.exp (|γ| * M)) * areaApprox γ Ys k (Metric.ball z δ') := by
          rw [← areaApprox_add_logC_apply hraw γ γ z k Metric.isOpen_ball.measurableSet him]
      _ ≤ ENNReal.ofReal (Real.exp (|γ| * M)) * ENNReal.ofReal ε' :=
          mul_le_mul' le_rfl ((measure_mono (Metric.ball_subset_ball hδ'δ)).trans hk)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          congr 1
          rw [hε',
            show Real.exp (|γ| * M) * (Real.exp (-(|γ| * M)) * ε) =
              (Real.exp (|γ| * M) * Real.exp (-(|γ| * M))) * ε by ring,
            ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  -- global convergence and no atom at `z`
  have hglob := isVagueLimitOn_of_local_of_tight isOpen_H hz hloc hfin htight
  have hq := qAreaMeasure_eq hglob
  rw [hq]
  exact ⟨hglob, withDensity_absolutelyContinuous _ _
    (by rw [Measure.restrict_apply (measurableSet_singleton z)]
        exact measure_mono_null (fun w hw => by
          rw [Set.mem_inter_iff] at hw
          exact absurd (Set.mem_singleton_iff.mp hw.1) hw.2.2) (measure_empty))⟩

/-- **TASKS.md R14, second theorem**: `AreaCircles.AreaLogSingNoAtom` for `0 < γ < 2`. -/
theorem areaLogSingNoAtom [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : AreaCircles.AreaLogSingNoAtom X P γ := by
  intro R hR z hz hzR g hg
  filter_upwards [ae_areaLogSingularity_add_ofFun hX hγ hγ2 R hz
    (AreaP3b.fracMoment_area_interior hX hγ hγ2 hz hzR) hg] with ω hω
  exact hω

end AreaLogSing
end QuantumZipper
