import HigherDimLQGMetric.Field.Affine
import HigherDimLQGMetric.Frozen.LogCovRd
import HigherDimLFPP.Field.LogEnergy

/-!
# White-noise vectors of bounded densities and the log covariance (packet F2, target 1, part 1)

Source: `source/higher-dimensional-lqg-metric.pdf` l. 50–56 ([1] (1.1)): the LGF modulo constants
has covariance `∫∫ φ(x) log(1/|x - y|) ψ(y) dx dy` on mean-zero functions; MA0 Details (a) D-WN
and (b) (HigherDimLFPP's white-noise representation: `scaleCov_eq_logCov`,
`logPairable_of_growthBound`).

For a function `f : ℝ^d → ℝ` that is measurable, bounded by `M` and vanishes outside `B̄(0, D)`
(`IsBddSupp f M D`) we use the finite measures `posM f = f⁺ dz` and `posM (-f) = f⁻ dz`:

* `posM_apply_le`, `isFiniteMeasure_posM`, `posM_real_closedBall_le` (the small-ball bound
  `posM f (B̄(z, s)) ≤ (M |B(0,1)| + ‖f⁺‖₁) s` for `d ≥ 1`), `integral_eq_posM_sub_posM`;
* `integrable_logKer`: `f(u) g(w) log|u - w|` is integrable on `ℝ^d × ℝ^d` (HigherDimLFPP's
  layer-cake bound `integrable_log_norm_sub_of_smallBall`);
* `logCov_posM`: HigherDimLFPP's four-term `logCov (posM f) (posM (-f)) (posM g) (posM (-g))` is
  `logCovF f g = ∫∫ f(u) g(w) (-log |u - w|) du dw`;
* `gramVec f = bandVecM κ₀ (0, ∞) (posM f) (posM (-f)) ∈ L²(ℝ × ℝ^d)` (the white-noise vector of
  `⟨h, f⟩`, for the fixed admissible kernel `κ₀ = HigherDimLFPP.bumpKernel d`) and the
  **Gram identity** `inner_gramVec`: `⟪gramVec f, gramVec g⟫ = logCovF f g` for mean-zero `f, g`
  (HigherDimLFPP's `scaleCov_eq_logCov`, Frullani);
* `logCovF` is symmetric and bilinear on `IsBddSupp` functions, and `abs_logCovF_self_le` bounds
  `|logCovF f f| ≤ ‖f‖₁ (M |B(0,1)| + ‖f‖₁ (1 + log⁺(2D)))`;
* `logCovRd_eq_logCovF`: for test functions the frozen `logCovRd` is `logCovF` (Fubini).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Bounded functions with bounded support -/

/-- `f` is measurable, bounded by `M`, and vanishes outside `B̄(0, D)`. -/
structure IsBddSupp (f : Rd d → ℝ) (M D : ℝ) : Prop where
  measurable : Measurable f
  abs_le : ∀ z, |f z| ≤ M
  eq_zero : ∀ z, D < ‖z‖ → f z = 0

namespace IsBddSupp

variable {f g : Rd d → ℝ} {M M' D D' : ℝ}

theorem nonneg (hf : IsBddSupp f M D) : 0 ≤ M := (abs_nonneg _).trans (hf.abs_le 0)

theorem mono (hf : IsBddSupp f M D) (hM : M ≤ M') (hD : D ≤ D') : IsBddSupp f M' D' :=
  ⟨hf.measurable, fun z => (hf.abs_le z).trans hM, fun z hz => hf.eq_zero z (hD.trans_lt hz)⟩

theorem neg (hf : IsBddSupp f M D) : IsBddSupp (-f) M D :=
  ⟨hf.measurable.neg, fun z => by simpa only [Pi.neg_apply, abs_neg] using hf.abs_le z,
    fun z hz => by simp only [Pi.neg_apply, hf.eq_zero z hz, neg_zero]⟩

theorem abs (hf : IsBddSupp f M D) : IsBddSupp (fun z => |f z|) M D :=
  ⟨continuous_abs.measurable.comp hf.measurable, fun z => by simpa only [abs_abs] using hf.abs_le z,
    fun z hz => by simp only [hf.eq_zero z hz, abs_zero]⟩

theorem add (hf : IsBddSupp f M D) (hg : IsBddSupp g M' D) : IsBddSupp (f + g) (M + M') D :=
  ⟨hf.measurable.add hg.measurable, fun z => (abs_add_le _ _).trans (add_le_add (hf.abs_le z)
    (hg.abs_le z)), fun z hz => by simp only [Pi.add_apply, hf.eq_zero z hz, hg.eq_zero z hz,
      add_zero]⟩

theorem sub (hf : IsBddSupp f M D) (hg : IsBddSupp g M' D) : IsBddSupp (f - g) (M + M') D := by
  have h := hf.add hg.neg
  rwa [← sub_eq_add_neg] at h

theorem const_mul (hf : IsBddSupp f M D) (c : ℝ) : IsBddSupp (fun z => c * f z) (|c| * M) D :=
  ⟨hf.measurable.const_mul c, fun z => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hf.abs_le z) (abs_nonneg c),
    fun z hz => by simp only [hf.eq_zero z hz, mul_zero]⟩

theorem posPart (hf : IsBddSupp f M D) : IsBddSupp (fun z => max (f z) 0) M D :=
  ⟨hf.measurable.max measurable_const, fun z => by
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hf.abs_le z)) hf.nonneg,
    fun z hz => by simp only [hf.eq_zero z hz, max_self]⟩

theorem norm_le (hf : IsBddSupp f M D) (z : Rd d) : ‖f z‖ ≤ M := by
  rw [Real.norm_eq_abs]; exact hf.abs_le z

theorem eq_zero_of_notMem (hf : IsBddSupp f M D) {z : Rd d} (hz : z ∉ closedBall (0 : Rd d) D) :
    f z = 0 :=
  hf.eq_zero z (by simpa only [mem_closedBall, dist_zero_right, not_le] using hz)

theorem integrable (hf : IsBddSupp f M D) : Integrable f := by
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero (s := closedBall (0 : Rd d) D) ?_
    fun z hz => hf.eq_zero_of_notMem hz
  exact Measure.integrableOn_of_bounded (measure_closedBall_lt_top (x := (0 : Rd d))).ne
    hf.measurable.aestronglyMeasurable (M := M) (ae_of_all _ fun z => hf.norm_le z)

theorem integral_abs_le (hf : IsBddSupp f M D) :
    ∫ z, |f z| ≤ M * (volume (closedBall (0 : Rd d) D)).toReal := by
  have hD : volume (closedBall (0 : Rd d) D) ≠ ⊤ := measure_closedBall_lt_top.ne
  have e : (fun z => |f z|) = (closedBall (0 : Rd d) D).indicator fun z => |f z| := by
    funext z
    by_cases hz : z ∈ closedBall (0 : Rd d) D
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz, hf.eq_zero_of_notMem hz, abs_zero]
  rw [e, integral_indicator measurableSet_closedBall]
  calc ∫ z in closedBall (0 : Rd d) D, |f z| ≤ ∫ _z in closedBall (0 : Rd d) D, M :=
        setIntegral_mono_on hf.abs.integrable.integrableOn
          (integrableOn_const hD) measurableSet_closedBall fun z _ => hf.abs_le z
    _ = M * (volume (closedBall (0 : Rd d) D)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm, Measure.real]

end IsBddSupp

/-- Continuous compactly supported functions (e.g. test functions) are `IsBddSupp`. -/
theorem exists_isBddSupp_of_continuous {f : Rd d → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) : ∃ M D, IsBddSupp f M D := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨D, hD⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, D, hf.measurable, fun z => by simpa only [Real.norm_eq_abs] using hM z,
    fun z hz => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hD h
  rw [mem_closedBall, dist_zero_right] at this
  exact absurd hz (not_lt.2 this)

theorem exists_isBddSupp_testOn (φ : TestRd d) : ∃ M D, IsBddSupp (fun z => φ z) M D :=
  exists_isBddSupp_of_continuous φ.continuous φ.hasCompactSupport

/-! ## The measures `f⁺ dz` -/

/-- The measure `f⁺ dz` (density `ENNReal.ofReal ∘ f`); `posM (-f) = f⁻ dz`. -/
def posM (f : Rd d → ℝ) : Measure (Rd d) := volume.withDensity fun z => ENNReal.ofReal (f z)

variable {f g : Rd d → ℝ} {M M' D D' : ℝ}

theorem posM_apply_le (hf : IsBddSupp f M D) (s : Set (Rd d)) :
    posM f s ≤ ENNReal.ofReal M * volume s := by
  rw [posM, withDensity_apply']
  calc ∫⁻ z in s, ENNReal.ofReal (f z) ≤ ∫⁻ _z in s, ENNReal.ofReal M :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hf.abs_le z))
    _ = ENNReal.ofReal M * volume s := by rw [setLIntegral_const]

theorem posM_compl_closedBall (hf : IsBddSupp f M D) : posM f (closedBall (0 : Rd d) D)ᶜ = 0 := by
  rw [posM, withDensity_apply']
  have h : EqOn (fun z => ENNReal.ofReal (f z)) (fun _ => 0) (closedBall (0 : Rd d) D)ᶜ :=
    fun z hz => by
      simp only
      rw [hf.eq_zero_of_notMem hz, ENNReal.ofReal_zero]
  rw [setLIntegral_congr_fun measurableSet_closedBall.compl h, lintegral_zero]

theorem posM_univ_le (hf : IsBddSupp f M D) :
    posM f univ ≤ ENNReal.ofReal M * volume (closedBall (0 : Rd d) D) := by
  calc posM f univ ≤ posM f (closedBall (0 : Rd d) D) + posM f (closedBall (0 : Rd d) D)ᶜ := by
        rw [← union_compl_self (closedBall (0 : Rd d) D)]
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal M * volume (closedBall (0 : Rd d) D) + 0 :=
        add_le_add (posM_apply_le hf _) (posM_compl_closedBall hf).le
    _ = _ := add_zero _

theorem isFiniteMeasure_posM (hf : IsBddSupp f M D) : IsFiniteMeasure (posM f) :=
  ⟨(posM_univ_le hf).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)⟩

theorem ae_posM_norm_le (hf : IsBddSupp f M D) : ∀ᵐ z ∂(posM f), ‖z‖ ≤ D := by
  rw [ae_iff]
  have e : {a : Rd d | ¬‖a‖ ≤ D} = (closedBall (0 : Rd d) D)ᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, mem_closedBall, dist_zero_right]
  rw [e]
  exact posM_compl_closedBall hf

theorem posM_univ (f : Rd d → ℝ) : posM f univ = ∫⁻ z, ENNReal.ofReal (f z) := by
  rw [posM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- `∫ f = f⁺(ℝ^d) − f⁻(ℝ^d)`. -/
theorem integral_eq_posM_sub_posM (hf : IsBddSupp f M D) :
    ∫ z, f z = (posM f).real univ - (posM (-f)).real univ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf.integrable, Measure.real,
    Measure.real, posM_univ, posM_univ]
  rfl

/-- Equal masses for mean-zero `f`. -/
theorem posM_real_univ_eq (hf : IsBddSupp f M D) (hf0 : ∫ z, f z = 0) :
    (posM f).real univ = (posM (-f)).real univ := by
  have h := integral_eq_posM_sub_posM hf
  rw [hf0] at h
  linarith

/-- The volume of the unit ball. -/
def volBall (d : ℕ) : ℝ := (volume (ball (0 : Rd d) 1)).toReal

theorem volBall_nonneg : 0 ≤ volBall d := ENNReal.toReal_nonneg

theorem volume_closedBall_real (z : Rd d) {s : ℝ} (hs : 0 ≤ s) :
    (volume (closedBall z s)).toReal = s ^ d * volBall d := by
  rw [Measure.addHaar_closedBall volume z hs, finrank_rd, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hs d), volBall]

/-- **Small-ball bound** (`d ≥ 1`): `(f⁺ dz)(B̄(z, s)) ≤ (M |B(0,1)| + f⁺(ℝ^d)) s` for all
`s > 0`. -/
theorem posM_real_closedBall_le [NeZero d] (hf : IsBddSupp f M D) (z : Rd d) {s : ℝ}
    (hs : 0 < s) :
    (posM f).real (closedBall z s) ≤ (M * volBall d + (posM f).real univ) * s := by
  have := isFiniteMeasure_posM hf
  have hM := hf.nonneg
  have hV := volBall_nonneg (d := d)
  have hmass : 0 ≤ (posM f).real univ := measureReal_nonneg
  rcases le_or_gt s 1 with hs1 | hs1
  · have h1 : (posM f).real (closedBall z s) ≤ M * (s ^ d * volBall d) := by
      rw [← volume_closedBall_real z hs.le, Measure.real]
      have h2 := posM_apply_le hf (closedBall z s)
      have h3 : ENNReal.ofReal M * volume (closedBall z s) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
      calc (posM f (closedBall z s)).toReal
          ≤ (ENNReal.ofReal M * volume (closedBall z s)).toReal := ENNReal.toReal_mono h3 h2
        _ = M * (volume (closedBall z s)).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]
    have h4 : s ^ d ≤ s := pow_le_of_le_one hs.le hs1 (NeZero.ne d)
    calc (posM f).real (closedBall z s) ≤ M * (s ^ d * volBall d) := h1
      _ ≤ M * (s * volBall d) := by gcongr
      _ ≤ (M * volBall d + (posM f).real univ) * s := by nlinarith
  · calc (posM f).real (closedBall z s) ≤ (posM f).real univ :=
          measureReal_mono (subset_univ _)
      _ ≤ (posM f).real univ * s := le_mul_of_one_le_right hmass hs1.le
      _ ≤ (M * volBall d + (posM f).real univ) * s :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hM hV)) hs.le

/-- Small-ball bounds add up. -/
theorem real_closedBall_add_le {μ ν : Measure (Rd d)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A B : ℝ} (hμ : ∀ z : Rd d, ∀ s > 0, μ.real (closedBall z s) ≤ A * s)
    (hν : ∀ z : Rd d, ∀ s > 0, ν.real (closedBall z s) ≤ B * s) :
    ∀ z : Rd d, ∀ s > 0, (μ + ν).real (closedBall z s) ≤ (A + B) * s := by
  intro z s hs
  rw [measureReal_add_apply]
  have := hμ z s hs
  have := hν z s hs
  linarith

/-! ## Integrability of the log kernel -/

/-- `∫ F d(f⁺ ⊗ g⁺) = ∫ f⁺(u) g⁺(w) F(u, w) du dw`. -/
theorem integral_prod_posM (hf : Measurable f) (hg : Measurable g) (F : Rd d × Rd d → ℝ) :
    ∫ p, F p ∂((posM f).prod (posM g)) =
      ∫ p : Rd d × Rd d, max (f p.1) 0 * max (g p.2) 0 * F p := by
  rw [posM, posM, prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) F]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', smul_eq_mul]

theorem integrable_prod_posM_iff (hf : Measurable f) (hg : Measurable g) (F : Rd d × Rd d → ℝ) :
    Integrable F ((posM f).prod (posM g)) ↔
      Integrable (fun p : Rd d × Rd d => max (f p.1) 0 * max (g p.2) 0 * F p) := by
  rw [posM, posM, prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  have e : (fun p : Rd d × Rd d => (ENNReal.ofReal (f p.1) * ENNReal.ofReal (g p.2)).toReal • F p) =
      fun p => max (f p.1) 0 * max (g p.2) 0 * F p := by
    funext p
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', smul_eq_mul]
  rw [e]
  exact Iff.rfl

/-- `log |u − w|` is `f⁺ ⊗ f⁺`-integrable (`d ≥ 1`). -/
theorem integrable_log_prod_posM [NeZero d] (hf : IsBddSupp f M D) :
    Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖) ((posM f).prod (posM f)) := by
  have := isFiniteMeasure_posM hf
  exact HigherDimLFPP.integrable_log_norm_sub_of_smallBall
    (A := M * volBall d + (posM f).real univ) (D := D)
    (add_nonneg (mul_nonneg hf.nonneg volBall_nonneg) measureReal_nonneg)
    (fun z s hs => posM_real_closedBall_le hf z hs) (ae_posM_norm_le hf)

/-- **Integrability of the log kernel** (`d ≥ 1`): for bounded boundedly supported `f, g`,
`(u, w) ↦ f(u) g(w) (−log |u − w|)` is integrable on `ℝ^d × ℝ^d`. -/
theorem integrable_logKer [NeZero d] (hf : IsBddSupp f M D) (hg : IsBddSupp g M' D') :
    Integrable (fun p : Rd d × Rd d => f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)) := by
  set a : Rd d → ℝ := fun z => |f z| + |g z| with ha
  have hfa : IsBddSupp f M (max D D') := hf.mono le_rfl (le_max_left _ _)
  have hga : IsBddSupp g M' (max D D') := hg.mono le_rfl (le_max_right _ _)
  have haS : IsBddSupp a (M + M') (max D D') := hfa.abs.add hga.abs
  have h1 := integrable_log_prod_posM haS
  rw [integrable_prod_posM_iff haS.measurable haS.measurable] at h1
  have hm : Measurable fun p : Rd d × Rd d => f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖) :=
    ((hf.measurable.comp measurable_fst).mul (hg.measurable.comp measurable_snd)).mul
      (measurable_fst.sub measurable_snd).norm.log.neg
  refine h1.norm.mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  have ha0 : ∀ z, 0 ≤ a z := fun z => add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [max_eq_left (ha0 p.1), max_eq_left (ha0 p.2)]
  simp only [norm_mul, norm_neg, Real.norm_eq_abs]
  have hfa' : |f p.1| ≤ a p.1 := le_add_of_nonneg_right (abs_nonneg _)
  have hga' : |g p.2| ≤ a p.2 := le_add_of_nonneg_left (abs_nonneg _)
  rw [abs_of_nonneg (ha0 p.1), abs_of_nonneg (ha0 p.2)]
  gcongr

/-! ## The log covariance of densities -/

theorem integral_sub_sub_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F₁ F₂ F₃ F₄ : α → ℝ} (i₁ : Integrable F₁ μ) (i₂ : Integrable F₂ μ) (i₃ : Integrable F₃ μ)
    (i₄ : Integrable F₄ μ) :
    ∫ a, (F₁ a - F₂ a - F₃ a + F₄ a) ∂μ =
      (∫ a, F₁ a ∂μ) - (∫ a, F₂ a ∂μ) - (∫ a, F₃ a ∂μ) + ∫ a, F₄ a ∂μ := by
  have h₁₂ : Integrable (fun a => F₁ a - F₂ a) μ := i₁.sub i₂
  have h₁₂₃ : Integrable (fun a => F₁ a - F₂ a - F₃ a) μ := h₁₂.sub i₃
  rw [integral_add h₁₂₃ i₄, integral_sub h₁₂ i₃, integral_sub i₁ i₂]

instance nullSingletonClass_posM [NeZero d] (f : Rd d → ℝ) : NullSingletonClass (posM f) := by
  unfold posM
  infer_instance

/-- `∫∫ f(u) g(w) (−log |u − w|) du dw`, as an integral over `ℝ^d × ℝ^d`. -/
def logCovF (f g : Rd d → ℝ) : ℝ :=
  ∫ p : Rd d × Rd d, f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)

/-- HigherDimLFPP's four-term `logCov` of the positive and negative parts is `logCovF`. -/
theorem logCov_posM [NeZero d] (hf : IsBddSupp f M D) (hg : IsBddSupp g M' D') :
    HigherDimLFPP.logCov (posM f) (posM (-f)) (posM g) (posM (-g)) = logCovF f g := by
  have hi : ∀ (a b : Rd d → ℝ) (Ma Da Mb Db : ℝ), IsBddSupp a Ma Da → IsBddSupp b Mb Db →
      Integrable (fun p : Rd d × Rd d =>
        max (a p.1) 0 * max (b p.2) 0 * (-Real.log ‖p.1 - p.2‖)) :=
    fun a b Ma Da Mb Db ha hb => integrable_logKer ha.posPart hb.posPart
  have i1 := hi f g M D M' D' hf hg
  have i2 := hi f (-g) M D M' D' hf hg.neg
  have i3 := hi (-f) g M D M' D' hf.neg hg
  have i4 := hi (-f) (-g) M D M' D' hf.neg hg.neg
  rw [HigherDimLFPP.logCov, integral_prod_posM hf.measurable hg.measurable,
    integral_prod_posM hf.measurable hg.measurable.neg,
    integral_prod_posM hf.measurable.neg hg.measurable,
    integral_prod_posM hf.measurable.neg hg.measurable.neg,
    ← integral_sub_sub_add i1 i2 i3 i4]
  unfold logCovF
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hf' : max (f p.1) 0 - max (-f p.1) 0 = f p.1 := max_zero_sub_max_neg_zero_eq_self _
  have hg' : max (g p.2) 0 - max (-g p.2) 0 = g p.2 := max_zero_sub_max_neg_zero_eq_self _
  simp only [Pi.neg_apply]
  rw [show f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖) = (max (f p.1) 0 - max (-f p.1) 0) *
    (max (g p.2) 0 - max (-g p.2) 0) * (-Real.log ‖p.1 - p.2‖) by rw [hf', hg']]
  ring

/-- The fixed admissible kernel `κ₀` of the white-noise realization (HigherDimLFPP's
`bumpKernel`). -/
abbrev kappa0 (d : ℕ) : Rd d → ℝ := HigherDimLFPP.bumpKernel d

/-- The white-noise vector of `⟨h, f⟩`: `bandVecM κ₀ (0, ∞) (f⁺ dz) (f⁻ dz) ∈ L²(ℝ × ℝ^d)`. -/
def gramVec (f : Rd d → ℝ) : HigherDimLFPP.WN d :=
  HigherDimLFPP.bandVecM (kappa0 d) (Ioi 0) (posM f) (posM (-f))

theorem logPairable_posM [NeZero d] (hf : IsBddSupp f M D) (hg : IsBddSupp g M' D') :
    HigherDimLFPP.LogPairable (posM f) (posM (-f)) (posM g) (posM (-g)) := by
  have hf1 := hf.mono le_rfl (le_max_left D D')
  have hg1 := hg.mono le_rfl (le_max_right D D')
  have := isFiniteMeasure_posM hf1
  have := isFiniteMeasure_posM hf1.neg
  have := isFiniteMeasure_posM hg1
  have := isFiniteMeasure_posM hg1.neg
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine HigherDimLFPP.integrable_log_norm_sub_of_smallBall (D := max D D')
    (A := (M * volBall d + (posM f).real univ) + (M * volBall d + (posM (-f)).real univ) +
      (M' * volBall d + (posM g).real univ) + (M' * volBall d + (posM (-g)).real univ))
    (by
      have := hf.nonneg
      have := hg.nonneg
      have := volBall_nonneg (d := d)
      have : 0 ≤ (posM f).real univ := measureReal_nonneg
      have : 0 ≤ (posM (-f)).real univ := measureReal_nonneg
      have : 0 ≤ (posM g).real univ := measureReal_nonneg
      have : 0 ≤ (posM (-g)).real univ := measureReal_nonneg
      positivity) ?_ ?_
  · exact real_closedBall_add_le (real_closedBall_add_le (real_closedBall_add_le
      (fun z s hs => posM_real_closedBall_le hf1 z hs)
      (fun z s hs => posM_real_closedBall_le hf1.neg z hs))
      (fun z s hs => posM_real_closedBall_le hg1 z hs))
      (fun z s hs => posM_real_closedBall_le hg1.neg z hs)
  · simp only [ae_add_measure_iff]
    exact ⟨⟨⟨ae_posM_norm_le hf1, ae_posM_norm_le hf1.neg⟩, ae_posM_norm_le hg1⟩,
      ae_posM_norm_le hg1.neg⟩

/-- **Gram identity**: for mean-zero bounded boundedly supported `f, g` (`d ≥ 1`),
`⟪gramVec f, gramVec g⟫ = ∫∫ f(u) g(w) log |u − w|⁻¹ du dw` (HigherDimLFPP's
`scaleCov_eq_logCov`). -/
theorem inner_gramVec [NeZero d] (hf : IsBddSupp f M D) (hf0 : ∫ z, f z = 0)
    (hg : IsBddSupp g M' D') (hg0 : ∫ z, g z = 0) :
    ⟪gramVec f, gramVec g⟫ = logCovF f g := by
  have := isFiniteMeasure_posM hf
  have := isFiniteMeasure_posM hf.neg
  have := isFiniteMeasure_posM hg
  have := isFiniteMeasure_posM hg.neg
  obtain ⟨-, -, h⟩ := HigherDimLFPP.scaleCov_eq_logCov (HigherDimLFPP.isLFPPKernel_bumpKernel d)
    (posM_real_univ_eq hf hf0) (posM_real_univ_eq hg hg0) (logPairable_posM hf hg)
  rw [← logCov_posM hf hg, ← h]
  rfl

/-! ## Symmetry, bilinearity and a bound for `logCovF` -/

theorem logCovF_comm (f g : Rd d → ℝ) : logCovF f g = logCovF g f := by
  have h := integral_prod_swap (μ := (volume : Measure (Rd d))) (ν := volume)
    (fun p : Rd d × Rd d => g p.1 * f p.2 * (-Real.log ‖p.1 - p.2‖))
  simp only [Prod.fst_swap, Prod.snd_swap] at h
  unfold logCovF
  refine Eq.trans ?_ h
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only
  rw [norm_sub_rev]
  ring

variable {f₁ f₂ : Rd d → ℝ} {M₁ M₂ D₁ D₂ : ℝ}

theorem logCovF_sub_left [NeZero d] (hf₁ : IsBddSupp f₁ M₁ D₁) (hf₂ : IsBddSupp f₂ M₂ D₂)
    (hg : IsBddSupp g M' D') : logCovF (f₁ - f₂) g = logCovF f₁ g - logCovF f₂ g := by
  unfold logCovF
  rw [← integral_sub (integrable_logKer hf₁ hg) (integrable_logKer hf₂ hg)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply]
  ring

theorem logCovF_sub_right [NeZero d] (hf : IsBddSupp f M D) (hg₁ : IsBddSupp f₁ M₁ D₁)
    (hg₂ : IsBddSupp f₂ M₂ D₂) : logCovF f (f₁ - f₂) = logCovF f f₁ - logCovF f f₂ := by
  rw [logCovF_comm, logCovF_sub_left hg₁ hg₂ hf, logCovF_comm f₁, logCovF_comm f₂]

/-- `‖gramVec a − gramVec b‖² = logCovF (a − b) (a − b)` for mean-zero `a, b`. -/
theorem norm_gramVec_sub_sq [NeZero d] (hf₁ : IsBddSupp f₁ M₁ D₁) (h₁ : ∫ z, f₁ z = 0)
    (hf₂ : IsBddSupp f₂ M₂ D₂) (h₂ : ∫ z, f₂ z = 0) :
    ‖gramVec f₁ - gramVec f₂‖ ^ 2 = logCovF (f₁ - f₂) (f₁ - f₂) := by
  rw [norm_sub_sq_real, inner_gramVec hf₁ h₁ hf₂ h₂, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, inner_gramVec hf₁ h₁ hf₁ h₁, inner_gramVec hf₂ h₂ hf₂ h₂,
    logCovF_sub_left hf₁ hf₂ ((hf₁.mono le_rfl (le_max_left D₁ D₂)).sub
      (hf₂.mono le_rfl (le_max_right D₁ D₂))),
    logCovF_sub_right hf₁ hf₁ hf₂, logCovF_sub_right hf₂ hf₁ hf₂, logCovF_comm f₂ f₁]
  ring

/-- For nonnegative `f`, `f⁺(ℝ^d) = ∫ f`. -/
theorem posM_real_univ_of_nonneg (hf : IsBddSupp f M D) (hf0 : ∀ z, 0 ≤ f z) :
    (posM f).real univ = ∫ z, f z := by
  rw [Measure.real, posM_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf.integrable (ae_of_all _ hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0)]

/-- **Layer-cake bound** (`d ≥ 1`): for `‖u‖ ≤ D`,
`∫ |f(w)| |log |u − w|| dw ≤ M |B(0,1)| + ‖f‖₁ (1 + log⁺(2D))`. -/
theorem lintegral_abs_mul_abs_log_le [NeZero d] (hf : IsBddSupp f M D) {u : Rd d}
    (hu : ‖u‖ ≤ D) :
    ∫⁻ w, ENNReal.ofReal (|f w| * |Real.log ‖u - w‖|) ≤
      ENNReal.ofReal (M * volBall d + (∫ z, |f z|) * (1 + max 0 (Real.log (2 * D)))) := by
  set L := max 0 (Real.log (2 * D)) with hL
  set N := ∫ z, |f z| with hNdef
  have hL0 : 0 ≤ L := le_max_left _ _
  have hN0 : 0 ≤ N := integral_nonneg fun z => abs_nonneg _
  have hM0 := hf.nonneg
  have hV0 := volBall_nonneg (d := d)
  have hfa := hf.abs
  have := isFiniteMeasure_posM hfa
  have hN : (posM fun z => |f z|).real univ = N :=
    posM_real_univ_of_nonneg hfa fun z => abs_nonneg _
  have hpt : ∀ w, ENNReal.ofReal (|f w| * |Real.log ‖u - w‖|) ≤
      ENNReal.ofReal (|f w|) * ENNReal.ofReal (max 0 (-Real.log ‖u - w‖)) +
        ENNReal.ofReal (|f w|) * ENNReal.ofReal L := by
    intro w
    by_cases hw : D < ‖w‖
    · rw [hf.eq_zero w hw, abs_zero, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
    · have hw := not_lt.1 hw
      have h2D : ‖u - w‖ ≤ 2 * D := (norm_sub_le _ _).trans (by linarith)
      have hlog := HigherDimLFPP.FieldAux.abs_log_le (norm_nonneg (u - w)) h2D
      rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _),
        ← ENNReal.ofReal_add (mul_nonneg (abs_nonneg _) (le_max_left _ _))
          (mul_nonneg (abs_nonneg _) hL0)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
  have hm1 : Measurable fun w : Rd d => ENNReal.ofReal (|f w|) :=
    (continuous_abs.measurable.comp hf.measurable).ennreal_ofReal
  have hm2 : Measurable fun w : Rd d => ENNReal.ofReal (max 0 (-Real.log ‖u - w‖)) :=
    (measurable_const.max (measurable_const.sub measurable_id).norm.log.neg).ennreal_ofReal
  have hlay := HigherDimLFPP.FieldAux.lintegral_log_inv_le (lam := posM fun z => |f z|)
    (A := M * volBall d + N) (by positivity)
    (fun z s hs => by simpa only [hN] using posM_real_closedBall_le hfa z hs) u
  have hnorm : ∫⁻ w, ENNReal.ofReal (|f w|) = ENNReal.ofReal N :=
    (ofReal_integral_eq_lintegral_ofReal hfa.integrable (ae_of_all _ fun z => abs_nonneg _)).symm
  calc ∫⁻ w, ENNReal.ofReal (|f w| * |Real.log ‖u - w‖|)
      ≤ ∫⁻ w, (ENNReal.ofReal (|f w|) * ENNReal.ofReal (max 0 (-Real.log ‖u - w‖)) +
          ENNReal.ofReal (|f w|) * ENNReal.ofReal L) := lintegral_mono hpt
    _ = ∫⁻ w, ENNReal.ofReal (max 0 (-Real.log ‖u - w‖)) ∂(posM fun z => |f z|) +
          (∫⁻ w, ENNReal.ofReal (|f w|)) * ENNReal.ofReal L := by
        have hm12 : Measurable fun w : Rd d =>
            ENNReal.ofReal (|f w|) * ENNReal.ofReal (max 0 (-Real.log ‖u - w‖)) := hm1.mul hm2
        rw [lintegral_add_left hm12, lintegral_mul_const _ hm1, posM,
          lintegral_withDensity_eq_lintegral_mul _ hm1 hm2]
        rfl
    _ ≤ ENNReal.ofReal (M * volBall d + N) + ENNReal.ofReal N * ENNReal.ofReal L := by
        rw [hnorm]
        exact add_le_add hlay le_rfl
    _ = ENNReal.ofReal (M * volBall d + N * (1 + L)) := by
        rw [← ENNReal.ofReal_mul hN0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **Quadratic bound**: `|logCovF f f| ≤ ‖f‖₁ (M |B(0,1)| + ‖f‖₁ (1 + log⁺(2D)))` (`d ≥ 1`). -/
theorem abs_logCovF_self_le [NeZero d] (hf : IsBddSupp f M D) :
    |logCovF f f| ≤
      (∫ z, |f z|) * (M * volBall d + (∫ z, |f z|) * (1 + max 0 (Real.log (2 * D)))) := by
  set K := M * volBall d + (∫ z, |f z|) * (1 + max 0 (Real.log (2 * D))) with hK
  have hN0 : 0 ≤ ∫ z, |f z| := integral_nonneg fun z => abs_nonneg _
  have hK0 : 0 ≤ K := by
    have := hf.nonneg
    have := volBall_nonneg (d := d)
    have : 0 ≤ max 0 (Real.log (2 * D)) := le_max_left _ _
    positivity
  have hint := integrable_logKer hf hf
  unfold logCovF
  rw [Measure.volume_eq_prod] at hint ⊢
  calc |∫ p, f p.1 * f p.2 * (-Real.log ‖p.1 - p.2‖) ∂(volume.prod volume)|
      ≤ ∫ p, |f p.1 * f p.2 * (-Real.log ‖p.1 - p.2‖)| ∂(volume.prod volume) :=
        abs_integral_le_integral_abs
    _ = ∫ u, ∫ w, |f (u, w).1 * f (u, w).2 * (-Real.log ‖(u, w).1 - (u, w).2‖)| :=
        integral_prod _ hint.abs
    _ ≤ ∫ u, |f u| * K := by
        refine integral_mono hint.abs.integral_prod_left (hf.abs.integrable.mul_const K)
          fun u => ?_
        have e : (fun w => |f (u, w).1 * f (u, w).2 * (-Real.log ‖(u, w).1 - (u, w).2‖)|) =
            fun w => |f u| * (|f w| * |Real.log ‖u - w‖|) := by
          funext w
          simp only [abs_mul, abs_neg]
          ring
        simp only
        rw [e, integral_const_mul]
        by_cases hu : D < ‖u‖
        · rw [hf.eq_zero u hu, abs_zero, zero_mul, zero_mul]
        · have hu := not_lt.1 hu
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have hmeas : AEStronglyMeasurable (fun w : Rd d => |f w| * |Real.log ‖u - w‖|)
              volume :=
            ((continuous_abs.measurable.comp hf.measurable).mul
              (continuous_abs.measurable.comp
                (measurable_const.sub measurable_id).norm.log)).aestronglyMeasurable
          have hnn : (0 : Rd d → ℝ) ≤ᵐ[volume] fun w => |f w| * |Real.log ‖u - w‖| :=
            ae_of_all _ fun w => mul_nonneg (abs_nonneg _) (abs_nonneg _)
          rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas]
          calc (∫⁻ w, ENNReal.ofReal (|f w| * |Real.log ‖u - w‖|)).toReal
              ≤ (ENNReal.ofReal K).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_abs_mul_abs_log_le hf hu)
            _ = K := ENNReal.toReal_ofReal hK0
    _ = (∫ z, |f z|) * K := by rw [integral_mul_const]

/-- For test functions (indeed for any bounded boundedly supported functions) the frozen iterated
integral `logCovRd` equals the product integral `logCovF` (Fubini). -/
theorem logCovRd_eq_logCovF [NeZero d] (hf : IsBddSupp f M D) (hg : IsBddSupp g M' D') :
    logCovRd f g = logCovF f g := by
  have hint := integrable_logKer hf hg
  unfold logCovRd logCovF
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => ?_))
  simp only
  ring

end HigherDimLQGMetric
