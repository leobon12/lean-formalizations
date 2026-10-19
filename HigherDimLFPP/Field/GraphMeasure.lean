import HigherDimLFPP.Field.LogEnergy
import HigherDimLFPP.Lower.Frames
import HigherDimLFPP.Upper.PolygonMeasure
import HigherDimLFPP.Var.Basic

/-!
# Graph measures `μ_{δf}` and the transport bound (3.9) (packet P-F3a, target T1, part 1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.2 (the measures
`μ_{δf} = ∫₀¹ δ_{(x, δ f(x))} dx` and (3.9)); planning audit HA2
(`planning/audits/HA2-section-3.md`), §2.7, Details D6 ("(3.9)") and the Lean block (c)
(`lift`, `graphMeasure`, `Eq39`, `verts`).

For `f : ℝ → ℝ^{d-1}` and `δ ∈ ℝ` the graph point is `graphPt δ f x = x e₁ + (0, δ f(x))`
(horizontal coordinate first, `Lower.embedT` on the transverse coordinates; for `d = m + 1` this is
HA2's `lift x (δ • f x)`, see `Lower.toLp_cons_eq`), and
`graphMeasure d δ f = (Leb|_{[0,1]}).map (graphPt δ f)` is the horizontal Lebesgue measure lifted to
the graph (HA2's `graphMeasure`).

Contents:

* the point geometry `‖(x, δ f x) - (y, δ g y)‖² = (x - y)² + δ² ‖f x - g y‖²`
  (`norm_graphPt_sub_sq`);
* graph measures are probability measures with the growth bound (3.4) at scale `1` and constant
  `2` (`graphMeasure_growthBound`), bounded supports (`ae_norm_le_graphMeasure`), and the
  same-abscissa displacement coupling of size `δ sup ‖f - g‖` (`coupledWithin_graphMeasure`);
* hence they are log-pairable and `Cov(⟨h, ·⟩, ⟨h, ·⟩) = logCov` on them
  (`scaleCov_eq_logCov_graph`);
* **(3.9)**: `δ⁻¹ Var⟨H_S, μ_{δf} - μ_{δg}⟩ ≤ C sup_{[0,1]} ‖f - g‖` for every scale set
  `S ⊆ (0, ∞)` (`graph_scaleCov_le`, HA2's `Eq39` as `eq39`), and its `κ`-free log form
  `graph_logCov_le`;
* vertex values `verts n f` of `f ∈ V_n(E)`, the vertex balls `vertBall E n R`
  (HA3's `B̂_R`), and the facts used for uniformity: the sup bound by the vertex bound
  (`Vg_norm_le_of_verts`), the Lipschitz bound `‖f x - f y‖ ≤ 2 R 2ⁿ |x - y|`
  (`Vg_norm_sub_le`), and injectivity of `verts n` on `V_n(E)` (`injOn_verts`).

2D template: `LQGDimension/LFPP/GraphCov.lean` (`gc`, `graphComb`), where the graph is a list of
segments of `ℂ`; here the graph measure is the pushforward of Lebesgue measure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

/-- Lebesgue measure on `[0,1]` is a probability measure. -/
instance isProbabilityMeasure_restrict_Icc01 :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

section GraphPoint

variable {d : ℕ}

/-- The transverse embedding `ℝ^{d-1} → ℝ^d` is an isometry, hence `1`-Lipschitz. -/
theorem lipschitzWith_embedT : LipschitzWith 1 (Lower.embedT : Rd (d - 1) → Rd d) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [dist_eq_norm, dist_eq_norm, ← Lower.embedT_sub, Lower.norm_embedT, NNReal.coe_one, one_mul]

theorem continuous_embedT : Continuous (Lower.embedT : Rd (d - 1) → Rd d) :=
  lipschitzWith_embedT.continuous

/-- The graph point `(x, δ f(x)) = x e₁ + (0, δ f(x)) ∈ ℝ^d` (horizontal coordinate first). -/
def graphPt (δ : ℝ) (f : ℝ → Rd (d - 1)) (x : ℝ) : Rd d := x • e₁ d + Lower.embedT (δ • f x)

/-- The graph measure `μ_{δf} = ∫₀¹ δ_{(x, δ f(x))} dx` (source §3.2; HA2's `graphMeasure`). -/
def graphMeasure (d : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) : Measure (Rd d) :=
  (volume.restrict (Icc (0 : ℝ) 1)).map (graphPt δ f)

instance (δ : ℝ) (f : ℝ → Rd (d - 1)) : IsProbabilityMeasure (graphMeasure d δ f) := by
  unfold graphMeasure; infer_instance

theorem continuous_graphPt {δ : ℝ} {f : ℝ → Rd (d - 1)} (hf : Continuous f) :
    Continuous (graphPt (d := d) δ f) :=
  (continuous_id.smul continuous_const).add (continuous_embedT.comp (hf.const_smul δ))

theorem measurable_graphPt {δ : ℝ} {f : ℝ → Rd (d - 1)} (hf : Measurable f) :
    Measurable (graphPt (d := d) δ f) :=
  (continuous_id.smul continuous_const).measurable.add
    (continuous_embedT.measurable.comp (hf.const_smul δ))

theorem graphPt_sub (δ : ℝ) (f g : ℝ → Rd (d - 1)) (x y : ℝ) :
    graphPt (d := d) δ f x - graphPt δ g y = (x - y) • e₁ d + Lower.embedT (δ • (f x - g y)) := by
  simp only [graphPt, smul_sub, Lower.embedT_sub, sub_smul]
  abel

/-- `‖(x, δ f x) - (y, δ g y)‖² = (x - y)² + δ² ‖f x - g y‖²`. -/
theorem norm_graphPt_sub_sq (hd : 0 < d) (δ : ℝ) (f g : ℝ → Rd (d - 1)) (x y : ℝ) :
    ‖graphPt (d := d) δ f x - graphPt δ g y‖ ^ 2 = (x - y) ^ 2 + δ ^ 2 * ‖f x - g y‖ ^ 2 := by
  rw [graphPt_sub, Lower.norm_sq_smul_e₁_add_embedT hd, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]

theorem horiz_graphPt (hd : 0 < d) (δ : ℝ) (f : ℝ → Rd (d - 1)) (x : ℝ) :
    Lower.horiz (graphPt (d := d) δ f x) = x :=
  Lower.horiz_smul_e₁_add_embedT hd x _

theorem norm_graphPt_sub_same (δ : ℝ) (f g : ℝ → Rd (d - 1)) (x : ℝ) :
    ‖graphPt (d := d) δ f x - graphPt δ g x‖ = |δ| * ‖f x - g x‖ := by
  rw [graphPt_sub, sub_self, zero_smul, zero_add, Lower.norm_embedT, norm_smul, Real.norm_eq_abs]

theorem norm_graphPt_le (δ : ℝ) (f : ℝ → Rd (d - 1)) (x : ℝ) :
    ‖graphPt (d := d) δ f x‖ ≤ |x| * ‖e₁ d‖ + |δ| * ‖f x‖ := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Lower.norm_embedT, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]

theorem graphPt_zero (δ : ℝ) (x : ℝ) : graphPt (d := d) δ 0 x = x • e₁ d := by
  simp only [graphPt, Pi.zero_apply, smul_zero, Lower.embedT_zero, add_zero]

/-- `μ_{δ0}` is the uniform measure `ν_{[0, e₁]}` on the unit horizontal segment. -/
theorem graphMeasure_zero (δ : ℝ) : graphMeasure d δ 0 = Upper.segMeasure 0 (e₁ d) := by
  unfold graphMeasure Upper.segMeasure
  congr 1
  funext x
  rw [graphPt_zero, zero_add, sub_zero]

/-- **HA2's literal form**: for `d = m + 1`, `μ_{δf}` is the pushforward of Lebesgue measure on
`[0,1]` under `x ↦ lift x (δ f x) = (x, δ f(x))` (`Fin.cons`, horizontal coordinate first). -/
theorem graphMeasure_eq_cons (m : ℕ) (δ : ℝ) (f : ℝ → Rd m) :
    graphMeasure (m + 1) δ f = (volume.restrict (Icc (0 : ℝ) 1)).map fun x =>
      (WithLp.toLp 2 (Fin.cons x (WithLp.ofLp (δ • f x)) : Fin (m + 1) → ℝ) : Rd (m + 1)) := by
  unfold graphMeasure
  congr 1
  funext x
  rw [Lower.toLp_cons_eq]
  rfl

/-- Graph measures only depend on the profile on `[0,1]`. -/
theorem graphMeasure_congr {δ : ℝ} {f g : ℝ → Rd (d - 1)} (h : EqOn f g (Icc 0 1)) :
    graphMeasure d δ f = graphMeasure d δ g := by
  unfold graphMeasure
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  simp only [graphPt, h hx]

end GraphPoint

/-! ## Growth, support and couplings of graph measures -/

section GraphFacts

variable {d : ℕ}

/-- **Growth bound** (3.4) for graph measures, at scale `1` with constant `2`: the horizontal
projection of `μ_{δf}` is Lebesgue measure on `[0,1]`. -/
theorem graphMeasure_growthBound (hd : 0 < d) {δ : ℝ} {f : ℝ → Rd (d - 1)} (hf : Measurable f) :
    GrowthBound (graphMeasure d δ f) 2 1 := by
  intro z t ht
  have hm : Measurable (graphPt (d := d) δ f) := measurable_graphPt hf
  have hB : MeasurableSet (closedBall z t) := isClosed_closedBall.measurableSet
  set h := Lower.horiz z with hh
  have hsub : graphPt δ f ⁻¹' closedBall z t ∩ Icc 0 1 ⊆ Icc (h - t) (h + t) ∩ Icc 0 1 := by
    rintro x ⟨hx, hx01⟩
    refine ⟨?_, hx01⟩
    have h1 := Lower.abs_horiz_le (graphPt (d := d) δ f x - z) hd
    rw [Lower.horiz_sub, horiz_graphPt hd] at h1
    rw [mem_preimage, mem_closedBall, dist_eq_norm] at hx
    have h2 := abs_le.1 (h1.trans hx)
    rw [mem_Icc]
    constructor <;> linarith [h2.1, h2.2]
  have hle : (graphMeasure d δ f) (closedBall z t) ≤
      volume (Icc (h - t) (h + t) ∩ Icc (0 : ℝ) 1) := by
    rw [graphMeasure, Measure.map_apply hm hB, Measure.restrict_apply (hm hB)]
    exact measure_mono hsub
  have h1 : (graphMeasure d δ f).real (closedBall z t) ≤ 2 * t := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (hle.trans ?_)
    refine (measure_mono inter_subset_left).trans (le_of_eq ?_)
    rw [Real.volume_Icc]
    ring_nf
  have h2 : (graphMeasure d δ f).real (closedBall z t) ≤ 1 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  rw [div_one]
  rcases le_total t 1 with htt | htt
  · rw [min_eq_right htt]; exact h1
  · rw [min_eq_left htt]; linarith

/-- A growth bound with constant `B` gives one with every larger constant. -/
theorem GrowthBound.mono_const {μ : Measure (Rd d)} {B B' R : ℝ} (h : GrowthBound μ B R)
    (hR : 0 < R) (hBB : B ≤ B') : GrowthBound μ B' R := by
  intro z t ht
  exact (h z t ht).trans (mul_le_mul_of_nonneg_right hBB
    (le_min zero_le_one (div_nonneg ht.le hR.le)))

/-- Graph measures of profiles bounded by `M` on `[0,1]` are carried by the ball of radius
`1 + |δ| M`. -/
theorem ae_norm_le_graphMeasure (hd : 0 < d) {δ : ℝ} {f : ℝ → Rd (d - 1)} (hf : Measurable f)
    {M : ℝ} (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ M) :
    ∀ᵐ z ∂(graphMeasure d δ f), ‖z‖ ≤ 1 + |δ| * M := by
  rw [graphMeasure, ae_map_iff (measurable_graphPt hf).aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  refine (norm_graphPt_le δ f x).trans ?_
  rw [Lower.norm_e₁ hd, mul_one, abs_of_nonneg hx.1]
  have := mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg δ)
  linarith [hx.2]

/-- **Same-abscissa coupling** (HA2 D6, (3.9)): `μ_{δf}` and `μ_{δg}` are coupled within
`δ M` if `‖f - g‖ ≤ M` on `[0,1]`. -/
theorem coupledWithin_graphMeasure {δ : ℝ} (hδ : 0 ≤ δ) {f g : ℝ → Rd (d - 1)}
    (hf : Measurable f) (hg : Measurable g) {M : ℝ} (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ M) :
    CoupledWithin (graphMeasure d δ f) (graphMeasure d δ g) (δ * M) := by
  have hp : Measurable fun x => (graphPt (d := d) δ f x, graphPt (d := d) δ g x) :=
    (measurable_graphPt hf).prodMk (measurable_graphPt hg)
  refine ⟨(volume.restrict (Icc (0 : ℝ) 1)).map fun x => (graphPt δ f x, graphPt δ g x), ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hp]; rfl
  · rw [Measure.map_map measurable_snd hp]; rfl
  · rw [ae_map_iff hp.aemeasurable (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_graphPt_sub_same, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left (hM x hx) hδ

/-- Graph measures of measurable profiles bounded by `M` on `[0,1]` are log-pairable. -/
theorem logPairable_graphMeasure (hd : 0 < d) {δ M : ℝ} {f₁ f₂ f₃ f₄ : ℝ → Rd (d - 1)}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄)
    (hM₁ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₁ x‖ ≤ M) (hM₂ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₂ x‖ ≤ M)
    (hM₃ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₃ x‖ ≤ M) (hM₄ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₄ x‖ ≤ M) :
    LogPairable (graphMeasure d δ f₁) (graphMeasure d δ f₂) (graphMeasure d δ f₃)
      (graphMeasure d δ f₄) :=
  logPairable_of_growthBound one_pos one_pos (graphMeasure_growthBound hd h₁)
    (graphMeasure_growthBound hd h₂) (graphMeasure_growthBound hd h₃)
    (graphMeasure_growthBound hd h₄) (ae_norm_le_graphMeasure hd h₁ hM₁)
    (ae_norm_le_graphMeasure hd h₂ hM₂) (ae_norm_le_graphMeasure hd h₃ hM₃)
    (ae_norm_le_graphMeasure hd h₄ hM₄)

/-- **(3.2) for graph measures**: the all-scale covariance of graph measures of bounded measurable
profiles is the log covariance. -/
theorem scaleCov_eq_logCov_graph (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {δ M : ℝ}
    {f₁ f₂ f₃ f₄ : ℝ → Rd (d - 1)}
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄)
    (hM₁ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₁ x‖ ≤ M) (hM₂ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₂ x‖ ≤ M)
    (hM₃ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₃ x‖ ≤ M) (hM₄ : ∀ x ∈ Icc (0 : ℝ) 1, ‖f₄ x‖ ≤ M) :
    scaleCov κ (Ioi 0) (graphMeasure d δ f₁) (graphMeasure d δ f₂) (graphMeasure d δ f₃)
      (graphMeasure d δ f₄) =
    logCov (graphMeasure d δ f₁) (graphMeasure d δ f₂) (graphMeasure d δ f₃)
      (graphMeasure d δ f₄) :=
  (scaleCov_eq_logCov_of_growthBound hκ one_pos one_pos (graphMeasure_growthBound hd h₁)
    (graphMeasure_growthBound hd h₂) (graphMeasure_growthBound hd h₃)
    (graphMeasure_growthBound hd h₄) (ae_norm_le_graphMeasure hd h₁ hM₁)
    (ae_norm_le_graphMeasure hd h₂ hM₂) (ae_norm_le_graphMeasure hd h₃ hM₃)
    (ae_norm_le_graphMeasure hd h₄ hM₄)).2.2

end GraphFacts

/-! ## (3.9): the transport bound for graph measures -/

section Eq39

variable {d : ℕ}

/-- **(3.9)**, for every scale set (HA2 D6, "(3.9)"): there is `C = C(d, κ)` such that for every
measurable `S ⊆ (0, ∞)`, `δ > 0` and measurable `f, g` with `‖f - g‖ ≤ M` on `[0,1]`,
`⟨H_S, μ_{δf} - μ_{δg}⟩` is defined and `δ⁻¹ Var⟨H_S, μ_{δf} - μ_{δg}⟩ ≤ C M`.  (Lemma 3.1 with
`R = 1`, growth constant `2` and the same-abscissa coupling of size `δ M`.) -/
theorem graph_scaleCov_le (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Set ℝ), MeasurableSet S → S ⊆ Ioi 0 → ∀ (δ M : ℝ), 0 < δ →
      ∀ f g : ℝ → Rd (d - 1), Measurable f → Measurable g →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ M) →
      IsPairable κ S (graphMeasure d δ f) (graphMeasure d δ g) ∧
      δ⁻¹ * scaleCov κ S (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f)
        (graphMeasure d δ g) ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := transport_var_bound hκ 2
  refine ⟨C, hC0, fun S hS hS0 δ M hδ f g hf hg hM => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  obtain ⟨hp, hb⟩ := hC S hS hS0 (graphMeasure d δ f) (graphMeasure d δ g) 1 (δ * M) one_pos
    (by positivity) (graphMeasure_growthBound hd hf) (graphMeasure_growthBound hd hg)
    (coupledWithin_graphMeasure hδ.le hf hg hM)
  refine ⟨hp, ?_⟩
  calc δ⁻¹ * scaleCov κ S (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f)
        (graphMeasure d δ g) ≤ δ⁻¹ * (C * (δ * M) / 1) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hδ.le)
    _ = C * M := by field_simp

/-- **(3.9)**, exactly HA2's `Eq39` (all scales). -/
theorem eq39 (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C : ℝ, ∀ (δ M : ℝ), 0 < δ → ∀ f g : ℝ → Rd (d - 1), Measurable f → Measurable g →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ M) →
      IsPairable κ (Ioi 0) (graphMeasure d δ f) (graphMeasure d δ g) ∧
      δ⁻¹ * scaleCov κ (Ioi 0) (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f)
        (graphMeasure d δ g) ≤ C * M := by
  obtain ⟨C, -, hC⟩ := graph_scaleCov_le hd hκ
  exact ⟨C, fun δ M hδ f g hf hg hM => hC (Ioi 0) measurableSet_Ioi subset_rfl δ M hδ f g hf hg hM⟩

/-- **(3.9), log form** (`κ`-free; the constant depends only on `d`): for measurable `f, g`
bounded by `B` on `[0,1]` with `‖f - g‖ ≤ M` there, and `μ_k` graph measures of bounded
measurable profiles,
`δ⁻¹ |logCov(μ_{δf} - μ_{δg}, μ₃ - μ₄)| ≤ C √(M M')` whenever `μ₃, μ₄` are graph measures coupled
within `δ M'`.  The variance form is `graph_logCov_le`. -/
theorem graph_logCov_cross_le (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ B M M' : ℝ), 0 < δ → ∀ f g f' g' : ℝ → Rd (d - 1),
      Measurable f → Measurable g → Measurable f' → Measurable g' →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ B) → (∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ B) →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f' x‖ ≤ B) → (∀ x ∈ Icc (0 : ℝ) 1, ‖g' x‖ ≤ B) →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ M) → (∀ x ∈ Icc (0 : ℝ) 1, ‖f' x - g' x‖ ≤ M') →
      δ⁻¹ * |logCov (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f')
        (graphMeasure d δ g')| ≤ C * Real.sqrt (M * M') := by
  obtain ⟨C, hC0, hC⟩ := transport_logCov_bound_of_support d 2
  refine ⟨C, hC0, fun δ B M M' hδ f g f' g' hf hg hf' hg' hBf hBg hBf' hBg' hM hM' => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hM0' : 0 ≤ M' := (norm_nonneg _).trans (hM' 0 ⟨le_rfl, zero_le_one⟩)
  have hb := hC (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f')
    (graphMeasure d δ g') 1 1 (δ * M) (δ * M') (1 + |δ| * B) one_pos one_pos (by positivity)
    (by positivity) (graphMeasure_growthBound hd hf) (graphMeasure_growthBound hd hg)
    (graphMeasure_growthBound hd hf') (graphMeasure_growthBound hd hg')
    (coupledWithin_graphMeasure hδ.le hf hg hM) (coupledWithin_graphMeasure hδ.le hf' hg' hM')
    (ae_norm_le_graphMeasure hd hf hBf) (ae_norm_le_graphMeasure hd hg hBg)
    (ae_norm_le_graphMeasure hd hf' hBf') (ae_norm_le_graphMeasure hd hg' hBg')
  have e : Real.sqrt (δ * M * (δ * M')) = δ * Real.sqrt (M * M') := by
    rw [show δ * M * (δ * M') = δ ^ 2 * (M * M') by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hδ.le]
  calc δ⁻¹ * |logCov (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f')
        (graphMeasure d δ g')| ≤ δ⁻¹ * (C * Real.sqrt (δ * M * (δ * M')) / 1) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hδ.le)
    _ = C * Real.sqrt (M * M') := by rw [e]; field_simp

/-- **(3.9), log form** (`κ`-free): `δ⁻¹ logCov(μ_{δf} - μ_{δg}, μ_{δf} - μ_{δg}) ≤ C M` for
measurable `f, g` bounded on `[0,1]` with `‖f - g‖ ≤ M` there. -/
theorem graph_logCov_le (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ B M : ℝ), 0 < δ → ∀ f g : ℝ → Rd (d - 1),
      Measurable f → Measurable g →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ B) → (∀ x ∈ Icc (0 : ℝ) 1, ‖g x‖ ≤ B) →
      (∀ x ∈ Icc (0 : ℝ) 1, ‖f x - g x‖ ≤ M) →
      δ⁻¹ * |logCov (graphMeasure d δ f) (graphMeasure d δ g) (graphMeasure d δ f)
        (graphMeasure d δ g)| ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := graph_logCov_cross_le (d := d) hd
  refine ⟨C, hC0, fun δ B M hδ f g hf hg hBf hBg hM => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, zero_le_one⟩)
  have := hC δ B M M hδ f g f g hf hg hf hg hBf hBg hBf hBg hM hM
  rwa [Real.sqrt_mul_self hM0] at this

end Eq39

/-! ## Vertex values and vertex balls in `V_n(E)` -/

section Vertices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The vertex values `(f(i 2⁻ⁿ))_{0 ≤ i ≤ 2ⁿ}` (HA2's `verts`). -/
def verts (n : ℕ) (f : ℝ → E) : Fin (2 ^ n + 1) → E := fun i => f ((i : ℝ) / 2 ^ n)

omit [NormedSpace ℝ E] in
theorem verts_sub (n : ℕ) (f g : ℝ → E) : verts n (f - g) = verts n f - verts n g := rfl

/-- The vertex ball `B̂_R = {f ∈ V_n(E) : max_i ‖f(i 2⁻ⁿ)‖ ≤ R}` (HA3 D5, Step 1d; (I5)). -/
def vertBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (R : ℝ) :
    Set (ℝ → E) :=
  {f | f ∈ Vg E n ∧ ∀ i : ℕ, i ≤ 2 ^ n → ‖f ((i : ℝ) / 2 ^ n)‖ ≤ R}

/-- Every point of `[0,1]` lies in a closed mesh interval. -/
theorem exists_mesh_piece (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : ℕ, k < 2 ^ n ∧ x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n) := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hL1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · refine ⟨2 ^ n - 1, by omega, ?_⟩
    have e : ((2 ^ n - 1 : ℕ) : ℝ) = 2 ^ n - 1 := by rw [Nat.cast_sub hL1]; simp
    rw [e, h1]
    constructor
    · rw [div_le_one hL]; linarith
    · rw [sub_add_cancel, div_self hL.ne']
  · set k := ⌊x * 2 ^ n⌋₊ with hk
    have hxL : 0 ≤ x * 2 ^ n := mul_nonneg hx.1 hL.le
    have hk1 : (k : ℝ) ≤ x * 2 ^ n := Nat.floor_le hxL
    have hk2 : x * 2 ^ n < k + 1 := Nat.lt_floor_add_one _
    have hkK : k < 2 ^ n := by
      have : (k : ℝ) < 2 ^ n := lt_of_le_of_lt hk1 (by nlinarith)
      exact_mod_cast this
    refine ⟨k, hkK, ?_, ?_⟩
    · rw [div_le_iff₀ hL]; exact hk1
    · rw [le_div_iff₀ hL]; exact hk2.le

/-- On a mesh interval, `f ∈ V_n(E)` is a convex combination of its two vertex values. -/
theorem Vg_norm_le_of_piece {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) {k : ℕ} (hk : k < 2 ^ n)
    {x : ℝ} (hx : x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)) {R : ℝ}
    (h0 : ‖f ((k : ℝ) / 2 ^ n)‖ ≤ R) (h1 : ‖f (((k : ℝ) + 1) / 2 ^ n)‖ ≤ R) : ‖f x‖ ≤ R := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (2 : ℝ) ^ n * x - k := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by
    have := hx.1; rw [div_le_iff₀ hL] at this; rw [ht]; linarith
  have ht1 : t ≤ 1 := by
    have := hx.2; rw [le_div_iff₀ hL] at this; rw [ht]; linarith
  have e : f x = (1 - t) • f ((k : ℝ) / 2 ^ n) + t • f (((k : ℝ) + 1) / 2 ^ n) := by
    rw [Var.Vg_piece hf hk hx, ← ht]
    module
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  rw [e]
  calc ‖(1 - t) • f ((k : ℝ) / 2 ^ n) + t • f (((k : ℝ) + 1) / 2 ^ n)‖
      ≤ (1 - t) * ‖f ((k : ℝ) / 2 ^ n)‖ + t * ‖f (((k : ℝ) + 1) / 2 ^ n)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0,
          abs_of_nonneg h1t]
    _ ≤ (1 - t) * R + t * R := by gcongr
    _ = R := by ring

/-- **Sup bound by the vertex bound** for `f ∈ V_n(E)`. -/
theorem Vg_norm_le_of_verts {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) {R : ℝ}
    (hR : ∀ i : ℕ, i ≤ 2 ^ n → ‖f ((i : ℝ) / 2 ^ n)‖ ≤ R) (x : ℝ) : ‖f x‖ ≤ R := by
  have hR0 : 0 ≤ R := by
    have := hR 0 (Nat.zero_le _)
    rw [Nat.cast_zero, zero_div, hf.1, norm_zero] at this
    exact this
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := exists_mesh_piece n hx
    refine Vg_norm_le_of_piece hf hk hxk (hR k hk.le) ?_
    have := hR (k + 1) hk
    rwa [Nat.cast_add, Nat.cast_one] at this
  · rw [hf.2.2.1 x hx, norm_zero]; exact hR0

/-- On one closed mesh interval, `‖f x - f y‖ = 2ⁿ |x - y| ‖Δ_k f‖`, bounded by
`2 R 2ⁿ |x - y|` under the vertex bound `R`. -/
theorem Vg_norm_sub_le_of_piece {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) {R : ℝ}
    (hR : ∀ i : ℕ, i ≤ 2 ^ n → ‖f ((i : ℝ) / 2 ^ n)‖ ≤ R) {k : ℕ} (hk : k < 2 ^ n) {x y : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n))
    (hy : y ∈ Icc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)) :
    ‖f x - f y‖ ≤ 2 * R * 2 ^ n * |x - y| := by
  have hΔ : ‖f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)‖ ≤ 2 * R := by
    have h1 := hR (k + 1) hk
    have h2 := hR k hk.le
    rw [Nat.cast_add, Nat.cast_one] at h1
    exact (norm_sub_le _ _).trans (by linarith)
  have e : f x - f y = ((2 : ℝ) ^ n * (x - y)) •
      (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)) := by
    rw [Var.Vg_piece hf hk hx, Var.Vg_piece hf hk hy, add_sub_add_left_eq_sub, ← sub_smul]
    congr 1; ring
  rw [e, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  calc 2 ^ n * |x - y| * ‖f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)‖
      ≤ 2 ^ n * |x - y| * (2 * R) := by gcongr
    _ = 2 * R * 2 ^ n * |x - y| := by ring

/-- Lipschitz bound on `[0, j 2⁻ⁿ]`, by induction on `j`. -/
theorem Vg_norm_sub_le_aux {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) {R : ℝ}
    (hR : ∀ i : ℕ, i ≤ 2 ^ n → ‖f ((i : ℝ) / 2 ^ n)‖ ≤ R) :
    ∀ j : ℕ, j ≤ 2 ^ n → ∀ x ∈ Icc (0 : ℝ) ((j : ℝ) / 2 ^ n), ∀ y ∈ Icc (0 : ℝ) ((j : ℝ) / 2 ^ n),
      ‖f x - f y‖ ≤ 2 * R * 2 ^ n * |x - y| := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hR0 : 0 ≤ R := by
    have := hR 0 (Nat.zero_le _)
    rw [Nat.cast_zero, zero_div, hf.1, norm_zero] at this
    exact this
  set L := 2 * R * 2 ^ n with hLdef
  have hL0 : 0 ≤ L := by positivity
  -- a mixed pair across the knot `c`
  have mixed : ∀ x y c : ℝ, x ≤ c → c ≤ y → ‖f x - f c‖ ≤ L * |x - c| →
      ‖f c - f y‖ ≤ L * |c - y| → ‖f x - f y‖ ≤ L * |x - y| := by
    intro x y c hxc hcy h1 h2
    calc ‖f x - f y‖ ≤ ‖f x - f c‖ + ‖f c - f y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ L * |x - c| + L * |c - y| := add_le_add h1 h2
      _ = L * |x - y| := by
        rw [abs_of_nonpos (by linarith : x - c ≤ 0), abs_of_nonpos (by linarith : c - y ≤ 0),
          abs_of_nonpos (by linarith : x - y ≤ 0)]
        ring
  intro j
  induction j with
  | zero =>
    intro _ x hx y hy
    have hx0 : x = 0 := by
      have := hx.2; rw [Nat.cast_zero, zero_div] at this; exact le_antisymm this hx.1
    have hy0 : y = 0 := by
      have := hy.2; rw [Nat.cast_zero, zero_div] at this; exact le_antisymm this hy.1
    rw [hx0, hy0, sub_self, norm_zero, sub_self, abs_zero, mul_zero]
  | succ j ih =>
    intro hj x hx y hy
    have hj' : j < 2 ^ n := by omega
    have ih' := ih hj'.le
    set c := (j : ℝ) / 2 ^ n with hc
    have hc0 : 0 ≤ c := by positivity
    have hpiece : ∀ z ∈ Icc (0 : ℝ) (((j + 1 : ℕ) : ℝ) / 2 ^ n), c ≤ z →
        z ∈ Icc ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n) := by
      intro z hz hcz
      refine ⟨hcz, ?_⟩
      have := hz.2
      rwa [Nat.cast_add, Nat.cast_one] at this
    have hcmem : c ∈ Icc ((j : ℝ) / 2 ^ n) (((j : ℝ) + 1) / 2 ^ n) :=
      ⟨le_rfl, by rw [hc]; gcongr; linarith⟩
    have hcmem' : c ∈ Icc (0 : ℝ) ((j : ℝ) / 2 ^ n) := ⟨hc0, le_rfl⟩
    rcases le_total x c with hxc | hxc <;> rcases le_total y c with hyc | hyc
    · exact ih' x ⟨hx.1, hxc⟩ y ⟨hy.1, hyc⟩
    · exact mixed x y c hxc hyc (ih' x ⟨hx.1, hxc⟩ c hcmem')
        (Vg_norm_sub_le_of_piece hf hR hj' hcmem (hpiece y hy hyc))
    · rw [← norm_neg, neg_sub, ← abs_neg, neg_sub]
      exact mixed y x c hyc hxc (ih' y ⟨hy.1, hyc⟩ c hcmem')
        (Vg_norm_sub_le_of_piece hf hR hj' hcmem (hpiece x hx hxc))
    · exact Vg_norm_sub_le_of_piece hf hR hj' (hpiece x hx hxc) (hpiece y hy hyc)

/-- **Lipschitz bound** for `f ∈ V_n(E)` with vertex bound `R`:
`‖f x - f y‖ ≤ 2 R 2ⁿ |x - y|` for all `x, y ∈ ℝ`. -/
theorem Vg_norm_sub_le {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) {R : ℝ}
    (hR : ∀ i : ℕ, i ≤ 2 ^ n → ‖f ((i : ℝ) / 2 ^ n)‖ ≤ R) (x y : ℝ) :
    ‖f x - f y‖ ≤ 2 * R * 2 ^ n * |x - y| := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  set c : ℝ → ℝ := fun z => max 0 (min 1 z) with hcdef
  have hc01 : ∀ z, c z ∈ Icc (0 : ℝ) ((((2 ^ n : ℕ) : ℝ)) / 2 ^ n) := by
    intro z
    rw [Nat.cast_pow, Nat.cast_ofNat, div_self hL.ne']
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hfc : ∀ z, f z = f (c z) := by
    intro z
    rcases le_total z 0 with hz | hz
    · have : c z = 0 := by simp only [hcdef]; rw [max_eq_left]; exact (min_le_right _ _).trans hz
      rw [this, Var.Vg_zero_of_le hf (Or.inl hz), hf.1]
    · rcases le_total z 1 with hz1 | hz1
      · have : c z = z := by simp only [hcdef]; rw [min_eq_right hz1, max_eq_right hz]
        rw [this]
      · have : c z = 1 := by simp only [hcdef]; rw [min_eq_left hz1, max_eq_right zero_le_one]
        rw [this, Var.Vg_zero_of_le hf (Or.inr hz1), hf.2.1]
  have hclip : |c x - c y| ≤ |x - y| := by
    have h1 : |min 1 x - min 1 y| ≤ |x - y| := abs_min_sub_min_le_max 1 x 1 y |>.trans
      (by rw [sub_self, abs_zero]; exact max_le (abs_nonneg _) le_rfl)
    exact (abs_max_sub_max_le_max 0 (min 1 x) 0 (min 1 y)).trans
      (max_le (by rw [sub_self, abs_zero]; exact abs_nonneg _) h1)
  rw [hfc x, hfc y]
  have hR0 : 0 ≤ R := by
    have := hR 0 (Nat.zero_le _)
    rw [Nat.cast_zero, zero_div, hf.1, norm_zero] at this
    exact this
  refine (Vg_norm_sub_le_aux hf hR (2 ^ n) le_rfl (c x) (hc01 x) (c y) (hc01 y)).trans ?_
  gcongr

/-- Two members of `V_n(E)` with the same vertex values are equal. -/
theorem Vg_eq_of_verts {n : ℕ} {f g : ℝ → E} (hf : f ∈ Vg E n) (hg : g ∈ Vg E n)
    (h : ∀ i : ℕ, i ≤ 2 ^ n → f ((i : ℝ) / 2 ^ n) = g ((i : ℝ) / 2 ^ n)) : f = g := by
  have hfg : f - g ∈ Vg E n := Var.sub_mem_Vg hf hg
  have hR : ∀ i : ℕ, i ≤ 2 ^ n → ‖(f - g) ((i : ℝ) / 2 ^ n)‖ ≤ 0 := by
    intro i hi
    rw [Pi.sub_apply, h i hi, sub_self, norm_zero]
  funext x
  have := Vg_norm_le_of_verts hfg hR x
  rw [Pi.sub_apply] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- `verts n` is injective on `V_n(E)`. -/
theorem injOn_verts (n : ℕ) : InjOn (verts n) (Vg E n) := by
  intro f hf g hg h
  refine Vg_eq_of_verts hf hg fun i hi => ?_
  have := congrFun h ⟨i, by omega⟩
  simpa [verts] using this

/-- The vertex values control the sup norm: `‖f x‖ ≤ ‖verts n f‖` for `f ∈ V_n(E)`. -/
theorem Vg_norm_le_norm_verts {n : ℕ} {f : ℝ → E} (hf : f ∈ Vg E n) (x : ℝ) :
    ‖f x‖ ≤ ‖verts n f‖ := by
  refine Vg_norm_le_of_verts hf (fun i hi => ?_) x
  have := norm_le_pi_norm (verts n f) ⟨i, by omega⟩
  simpa [verts] using this

/-- A set of `V_n(E)` with bounded vertex values lies in a vertex ball. -/
theorem exists_subset_vertBall {n : ℕ} {K : Set (ℝ → E)} (hK : K ⊆ Vg E n)
    (hb : Bornology.IsBounded (verts n '' K)) : ∃ R : ℝ, K ⊆ vertBall E n R := by
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  refine ⟨R, fun f hf => ⟨hK hf, fun i hi => ?_⟩⟩
  have h1 := norm_le_pi_norm (verts n f) ⟨i, by omega⟩
  have h2 := hR (verts n f) (mem_image_of_mem _ hf)
  simp only [verts] at h1
  exact h1.trans h2

/-- The vertex values of `V_n(E)` form a linear subspace of `Fin (2ⁿ + 1) → E`. -/
def vertsSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    Submodule ℝ (Fin (2 ^ n + 1) → E) where
  carrier := verts n '' Vg E n
  zero_mem' := ⟨0, Var.zero_mem_Vg n, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, Var.add_mem_Vg hf hg, rfl⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨c • f, Var.smul_mem_Vg hf c, rfl⟩

/-- **Vertex balls are compact in vertex coordinates** (HA3 D5, Step 1d: `B̂` is compact in
`ℝ^{m(K-1)}`), so `expectedSupLimit_Vg` applies to `B̂_R`. -/
theorem isCompact_verts_vertBall [FiniteDimensional ℝ E] (n : ℕ) (R : ℝ) :
    IsCompact (verts n '' vertBall E n R) := by
  set S : Set (Fin (2 ^ n + 1) → E) := {v | ∀ i, ‖v i‖ ≤ R} with hS
  have hSc : IsClosed S := by
    rw [hS, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (continuous_norm.comp (continuous_apply i))
      continuous_const
  have hW : IsClosed ((vertsSubmodule E n : Set (Fin (2 ^ n + 1) → E))) :=
    Submodule.closed_of_finiteDimensional _
  have heq : verts n '' vertBall E n R = (vertsSubmodule E n : Set (Fin (2 ^ n + 1) → E)) ∩ S := by
    ext v
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨⟨f, hf.1, rfl⟩, fun i => ?_⟩
      exact hf.2 i (by have := i.isLt; omega)
    · rintro ⟨⟨f, hf, rfl⟩, hv⟩
      refine ⟨f, ⟨hf, fun i hi => ?_⟩, rfl⟩
      exact hv ⟨i, by omega⟩
  have hb : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin (2 ^ n + 1) → E)) (r := max R 0)).subset
      fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg (le_max_right R 0)).2 fun i => (hv i).trans (le_max_left _ _)
  rw [heq]
  exact Metric.isCompact_of_isClosed_isBounded (hW.inter hSc) (hb.subset inter_subset_right)

end Vertices

end HigherDimLFPP
