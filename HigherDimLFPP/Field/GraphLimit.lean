import HigherDimLFPP.Field.GraphMeasure
import LQGDimension.LFPP.GraphCov

/-!
# Lemma 3.2: the transverse graph limit (3.8) and its uniform form (3.8′) (packet P-F3a, T1)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §3.2, Lemma 3.2 ((3.8)); planning audit HA2
(`planning/audits/HA2-section-3.md`), §2.7, findings HA2-09, HA2-10, Details D6 ("(3.8)",
"(3.8′)") and the Lean block (c) (`Lemma32Var`).

**Statement.**  For continuous profiles `F₁, F₂, F₃, F₄ : [0,1] → ℝ^{d-1}`,
`δ⁻¹ logCov(μ_{δF₁} - μ_{δF₂}, μ_{δF₃} - μ_{δF₄}) → fourLim F₁ F₂ F₃ F₄` as `δ ↓ 0`, where
`fourLim F₁ F₂ F₃ F₄ = π ∫₀¹ (|F₁ - F₄| + |F₂ - F₃| - |F₁ - F₃| - |F₂ - F₄|)`.  In particular

* (3.8): `δ⁻¹ Var⟨h, μ_{δf} - μ_{δg}⟩ → 2π ∫₀¹ |f - g|` (`tendsto_graph_logCov_var`, and the
  `scaleCov` form `lemma32Var` = HA2's `Lemma32Var`);
* polarized: `δ⁻¹ Cov(⟨h, μ_{δf} - μ_{δ0}⟩, ⟨h, μ_{δg} - μ_{δ0}⟩) → gCov f g`
  (`tendsto_graph_logCov_cov`);
* (3.8′): the last convergence is uniform for `f, g` in a vertex ball of `V_n(ℝ^{d-1})`
  (`tendstoUniformlyOn_graph_logCov`), hence on every subset of `V_n(ℝ^{d-1})` with bounded
  (e.g. compact) vertex image (`tendstoUniformlyOn_graph_logCov_of_bounded`).

The coefficient `2π` (resp. `π`) is the same in every dimension: the dimension enters only through
the norms `|F_a(x) - F_b(y)|`.

**Proof** (HA2 D6).  The general statement `tendsto_graph_logCov_sub_fourLim` is asymptotic
equivalence along an arbitrary countably generated filter, for families of profiles that are
uniformly bounded and equicontinuous in the sense needed by dominated convergence.  Steps:

1. each of the four terms of `logCov` is the double integral
   `∫₀¹∫₀¹ -log|(x, δF_a x) - (y, δF_b y)| dy dx` (`integral_graph_prod`, using that graph
   measures are log-pairable);
2. the substitution `y = x + δ u` and
   `-log|(x, δa) - (x + δu, δb)| = -log δ - log|u| - lk(|a - b|, u)/2` with
   `lk(c, u) = log(1 + c²/u²)` (`neglog_norm_graphPt`) turn `δ⁻¹ logCov` into
   `∫₀¹ ∫_{-x/δ}^{(1-x)/δ} Kf σ4 u (gvec …) du dx` (`logCov_graph_eq_integral`);
3. dominated convergence (2D `LQGDimension.GraphCov.core_tendsto`, reused as is, with the vector
   norms `|F_a(x) - F_b(x + δu)|` as the scalar inputs) and `∫ lk(c, u) du = 2π|c|`
   (`LQGDimension.GraphCov.integral_lk`, via `core_tendsto`).

2D template: `LQGDimension/LFPP/GraphCov.lean` (`graphCovLimit`, `inner_subst`, `neglog_norm_eq`),
with `ℂ` replaced by `ℝ × ℝ^{d-1}` and segment combinations replaced by graph measures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

open LQGDimension.GraphCov (lk Kf σ4)

/-! ## The four profile distances and the limit functional -/

section Defs

variable {E : Type*} [NormedAddCommGroup E]

/-- The four profile distances `(|F₁ x - F₃ y|, |F₁ x - F₄ y|, |F₂ x - F₃ y|, |F₂ x - F₄ y|)` of
the four-term covariance `(μ₁ - μ₂) ⊗ (μ₃ - μ₄)` (the vector analogue of 2D `GraphCov.bvec`). -/
def gvec (F₁ F₂ F₃ F₄ : ℝ → E) (x y : ℝ) : Fin 4 → ℝ :=
  ![‖F₁ x - F₃ y‖, ‖F₁ x - F₄ y‖, ‖F₂ x - F₃ y‖, ‖F₂ x - F₄ y‖]

/-- The limit of the four-term graph covariance:
`π ∫₀¹ (|F₁ - F₄| + |F₂ - F₃| - |F₁ - F₃| - |F₂ - F₄|)`. -/
def fourLim (F₁ F₂ F₃ F₄ : ℝ → E) : ℝ :=
  Real.pi * ∫ x in (0 : ℝ)..1,
    (‖F₁ x - F₄ x‖ + ‖F₂ x - F₃ x‖ - ‖F₁ x - F₃ x‖ - ‖F₂ x - F₄ x‖)

theorem Kf_σ4_gvec (F₁ F₂ F₃ F₄ : ℝ → E) (x y w : ℝ) :
    Kf σ4 w (gvec F₁ F₂ F₃ F₄ x y) = -lk ‖F₁ x - F₃ y‖ w / 2 + lk ‖F₁ x - F₄ y‖ w / 2 +
      lk ‖F₂ x - F₃ y‖ w / 2 - lk ‖F₂ x - F₄ y‖ w / 2 := by
  simp only [Kf, σ4, gvec, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem limSum_gvec (F₁ F₂ F₃ F₄ : ℝ → E) (x : ℝ) :
    2 * Real.pi * ∑ k, σ4 k * |gvec F₁ F₂ F₃ F₄ x x k| =
      Real.pi * (‖F₁ x - F₄ x‖ + ‖F₂ x - F₃ x‖ - ‖F₁ x - F₃ x‖ - ‖F₂ x - F₄ x‖) := by
  simp only [σ4, gvec, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, abs_norm]
  ring

theorem continuous_gvec {α : Type*} [TopologicalSpace α] {F₁ F₂ F₃ F₄ : ℝ → E}
    (h₁ : Continuous F₁) (h₂ : Continuous F₂) (h₃ : Continuous F₃) (h₄ : Continuous F₄)
    {X Y : α → ℝ} (hX : Continuous X) (hY : Continuous Y) (k : Fin 4) :
    Continuous fun a => gvec F₁ F₂ F₃ F₄ (X a) (Y a) k := by
  fin_cases k <;> simp only [gvec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] <;> fun_prop

theorem abs_gvec_le {F₁ F₂ F₃ F₄ : ℝ → E} {x y M : ℝ}
    (hx : ‖F₁ x‖ ≤ M ∧ ‖F₂ x‖ ≤ M ∧ ‖F₃ x‖ ≤ M ∧ ‖F₄ x‖ ≤ M)
    (hy : ‖F₁ y‖ ≤ M ∧ ‖F₂ y‖ ≤ M ∧ ‖F₃ y‖ ≤ M ∧ ‖F₄ y‖ ≤ M) (k : Fin 4) :
    |gvec F₁ F₂ F₃ F₄ x y k| ≤ 2 * M := by
  obtain ⟨a₁, a₂, -, -⟩ := hx
  obtain ⟨-, -, b₃, b₄⟩ := hy
  fin_cases k <;> simp only [gvec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, abs_norm]
  · exact (norm_sub_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by linarith)
  · exact (norm_sub_le _ _).trans (by linarith)

theorem abs_gvec_sub_le (F₁ F₂ F₃ F₄ : ℝ → E) (x y : ℝ) (k : Fin 4) :
    |gvec F₁ F₂ F₃ F₄ x y k - gvec F₁ F₂ F₃ F₄ x x k| ≤ ‖F₃ y - F₃ x‖ + ‖F₄ y - F₄ x‖ := by
  have e : ∀ a b c : E, |‖a - b‖ - ‖a - c‖| ≤ ‖b - c‖ := fun a b c => by
    refine (abs_norm_sub_norm_le _ _).trans (le_of_eq ?_)
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
  have h₃ := norm_nonneg (F₃ y - F₃ x)
  have h₄ := norm_nonneg (F₄ y - F₄ x)
  fin_cases k <;> simp only [gvec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  · linarith [e (F₁ x) (F₃ y) (F₃ x)]
  · linarith [e (F₁ x) (F₄ y) (F₄ x)]
  · linarith [e (F₂ x) (F₃ y) (F₃ x)]
  · linarith [e (F₂ x) (F₄ y) (F₄ x)]

/-- `fourLim f g f g = 2π ∫₀¹ |f - g|` (the variance (3.8)). -/
theorem fourLim_self (f g : ℝ → E) :
    fourLim f g f g = 2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖f x - g x‖ := by
  unfold fourLim
  have h : ∫ x in (0 : ℝ)..1, (‖f x - g x‖ + ‖g x - f x‖ - ‖f x - f x‖ - ‖g x - g x‖) =
      ∫ x in (0 : ℝ)..1, 2 * ‖f x - g x‖ := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [sub_self, norm_zero, norm_sub_rev (g x) (f x)]
    ring
  rw [h, intervalIntegral.integral_const_mul]
  ring

/-- `fourLim` only depends on the profiles on `[0,1]`. -/
theorem fourLim_congr {F₁ F₂ F₃ F₄ G₁ G₂ G₃ G₄ : ℝ → E} (h₁ : EqOn F₁ G₁ (Icc 0 1))
    (h₂ : EqOn F₂ G₂ (Icc 0 1)) (h₃ : EqOn F₃ G₃ (Icc 0 1)) (h₄ : EqOn F₄ G₄ (Icc 0 1)) :
    fourLim F₁ F₂ F₃ F₄ = fourLim G₁ G₂ G₃ G₄ := by
  unfold fourLim
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le zero_le_one] at hx
  simp only [h₁ hx, h₂ hx, h₃ hx, h₄ hx]

end Defs

section DefsNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `fourLim f 0 g 0 = gCov f g` (the covariance (1.5)). -/
theorem fourLim_zero (f g : ℝ → E) : fourLim f 0 g 0 = gCov f g := by
  unfold fourLim gCov
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [Pi.zero_apply, sub_zero, zero_sub, norm_neg, norm_zero]

end DefsNormed

/-! ## Step 1: the four terms as double integrals -/

section DoubleIntegral

variable {d : ℕ}

/-- One term of `logCov` for graph measures as a double integral over `[0,1]²`, with
integrability. -/
theorem integral_graph_prod (hd : 0 < d) {δ M : ℝ} {F G : ℝ → Rd (d - 1)} (hF : Measurable F)
    (hG : Measurable G) (hMF : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ M)
    (hMG : ∀ x ∈ Icc (0 : ℝ) 1, ‖G x‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => -Real.log ‖graphPt (d := d) δ F p.1 - graphPt δ G p.2‖)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) ∧
      ∫ q, -Real.log ‖q.1 - q.2‖ ∂((graphMeasure d δ F).prod (graphMeasure d δ G)) =
        ∫ p, -Real.log ‖graphPt (d := d) δ F p.1 - graphPt δ G p.2‖
          ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
  set ν := volume.restrict (Icc (0 : ℝ) 1) with hν
  have mF := measurable_graphPt (d := d) (δ := δ) hF
  have mG := measurable_graphPt (d := d) (δ := δ) hG
  have hprod : (graphMeasure d δ F).prod (graphMeasure d δ G) =
      (ν.prod ν).map (Prod.map (graphPt δ F) (graphPt δ G)) :=
    Measure.map_prod_map ν ν mF mG
  have hφ : Measurable (Prod.map (graphPt (d := d) δ F) (graphPt (d := d) δ G)) := mF.prodMap mG
  have hgm : Measurable fun q : Rd d × Rd d => -Real.log ‖q.1 - q.2‖ :=
    (continuous_fst.sub continuous_snd).norm.measurable.log.neg
  have hlog := logPairable_graphMeasure (δ := δ) hd hF hG hF hG hMF hMG hMF hMG
  have hint : Integrable (fun q : Rd d × Rd d => -Real.log ‖q.1 - q.2‖)
      ((graphMeasure d δ F).prod (graphMeasure d δ G)) :=
    (LogPairable.integrable_prod hlog (FieldAux.le_add_four₁ _ _ _ _)
      (FieldAux.le_add_four₂ _ _ _ _)).neg
  rw [hprod] at hint ⊢
  refine ⟨(integrable_map_measure hgm.aestronglyMeasurable hφ.aemeasurable).1 hint, ?_⟩
  rw [integral_map hφ.aemeasurable hgm.aestronglyMeasurable]
  rfl

/-- The log kernel after the substitution `y = x + δ u`:
`-log|(x, δ F x) - (x + δu, δ G(x + δu))| = -log δ - log|u| - lk(|F x - G(x + δu)|, u)/2`. -/
theorem neglog_norm_graphPt (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) (F G : ℝ → Rd (d - 1)) (x : ℝ)
    {u : ℝ} (hu : u ≠ 0) :
    -Real.log ‖graphPt (d := d) δ F x - graphPt δ G (δ * u + x)‖ =
      -Real.log δ - Real.log |u| - lk ‖F x - G (δ * u + x)‖ u / 2 := by
  have h2 := norm_graphPt_sub_sq hd δ F G x (δ * u + x)
  obtain ⟨c, hc⟩ : ∃ c, c = ‖F x - G (δ * u + x)‖ := ⟨_, rfl⟩
  rw [← hc] at h2 ⊢
  have hu2 : 0 < u ^ 2 := by positivity
  have e : (x - (δ * u + x)) ^ 2 + δ ^ 2 * c ^ 2 = δ ^ 2 * u ^ 2 * (1 + c ^ 2 / u ^ 2) := by
    field_simp
    ring
  have hpos : 0 < 1 + c ^ 2 / u ^ 2 := by positivity
  have k1 : Real.log (‖graphPt (d := d) δ F x - graphPt δ G (δ * u + x)‖ ^ 2) =
      2 * Real.log ‖graphPt (d := d) δ F x - graphPt δ G (δ * u + x)‖ := by
    rw [Real.log_pow]; push_cast; ring
  have k2 : Real.log (δ ^ 2) = 2 * Real.log δ := by rw [Real.log_pow]; push_cast; ring
  have k3 : Real.log (u ^ 2) = 2 * Real.log |u| := by
    rw [Real.log_pow, Real.log_abs]; push_cast; ring
  have key : 2 * Real.log ‖graphPt (d := d) δ F x - graphPt δ G (δ * u + x)‖ =
      2 * Real.log δ + 2 * Real.log |u| + lk c u := by
    rw [← k1, h2, e, Real.log_mul (by positivity) hpos.ne',
      Real.log_mul (by positivity) hu2.ne', k2, k3]
    rfl
  linarith

/-- **Steps 1–2 of HA2 D6**: for continuous profiles bounded on `[0,1]` and `δ > 0`,
`δ⁻¹ logCov(μ_{δF₁} - μ_{δF₂}, μ_{δF₃} - μ_{δF₄}) = ∫₀¹ ∫_{-x/δ}^{(1-x)/δ} Kf σ4 u (gvec …) du dx`. -/
theorem logCov_graph_eq_integral (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) {F₁ F₂ F₃ F₄ : ℝ → Rd (d - 1)}
    (h₁ : Measurable F₁) (h₂ : Measurable F₂) (h₃ : Measurable F₃) (h₄ : Measurable F₄) {M : ℝ}
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖F₁ x‖ ≤ M ∧ ‖F₂ x‖ ≤ M ∧ ‖F₃ x‖ ≤ M ∧ ‖F₄ x‖ ≤ M) :
    δ⁻¹ * logCov (graphMeasure d δ F₁) (graphMeasure d δ F₂) (graphMeasure d δ F₃)
        (graphMeasure d δ F₄) =
      ∫ x in (0 : ℝ)..1, ∫ u in (-x / δ)..((1 - x) / δ),
        Kf σ4 u (gvec F₁ F₂ F₃ F₄ x (δ * u + x)) := by
  have hM₁ : ∀ x ∈ Icc (0 : ℝ) 1, ‖F₁ x‖ ≤ M := fun x hx => (hM x hx).1
  have hM₂ : ∀ x ∈ Icc (0 : ℝ) 1, ‖F₂ x‖ ≤ M := fun x hx => (hM x hx).2.1
  have hM₃ : ∀ x ∈ Icc (0 : ℝ) 1, ‖F₃ x‖ ≤ M := fun x hx => (hM x hx).2.2.1
  have hM₄ : ∀ x ∈ Icc (0 : ℝ) 1, ‖F₄ x‖ ≤ M := fun x hx => (hM x hx).2.2.2
  have g13 := integral_graph_prod (δ := δ) hd h₁ h₃ hM₁ hM₃
  have g14 := integral_graph_prod (δ := δ) hd h₁ h₄ hM₁ hM₄
  have g23 := integral_graph_prod (δ := δ) hd h₂ h₃ hM₂ hM₃
  have g24 := integral_graph_prod (δ := δ) hd h₂ h₄ hM₂ hM₄
  have i13 := g13.1
  have i14 := g14.1
  have i23 := g23.1
  have i24 := g24.1
  have e13 := g13.2
  have e14 := g14.2
  have e23 := g23.2
  have e24 := g24.2
  -- the combined kernel `Ψ`
  set Ψ : ℝ → ℝ → ℝ := fun x y =>
    -Real.log ‖graphPt (d := d) δ F₁ x - graphPt δ F₃ y‖ -
      -Real.log ‖graphPt (d := d) δ F₁ x - graphPt δ F₄ y‖ -
      -Real.log ‖graphPt (d := d) δ F₂ x - graphPt δ F₃ y‖ +
      -Real.log ‖graphPt (d := d) δ F₂ x - graphPt δ F₄ y‖ with hΨ
  have iΨ : Integrable (fun p : ℝ × ℝ => Ψ p.1 p.2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) :=
    ((i13.sub' i14).sub' i23).fun_add i24
  have hlog : logCov (graphMeasure d δ F₁) (graphMeasure d δ F₂) (graphMeasure d δ F₃)
      (graphMeasure d δ F₄) = ∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) 1, Ψ x y := by
    have h1 : ∫ p, Ψ p.1 p.2
        ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) =
        logCov (graphMeasure d δ F₁) (graphMeasure d δ F₂) (graphMeasure d δ F₃)
          (graphMeasure d δ F₄) := by
      simp only [hΨ]
      rw [integral_add ((i13.sub' i14).sub' i23) i24,
        integral_sub (i13.sub' i14) i23, integral_sub i13 i14, logCov, e13, e14, e23, e24]
    rw [← h1]
    exact integral_prod (fun p : ℝ × ℝ => Ψ p.1 p.2) iΨ
  have hinner : ∀ x : ℝ, δ⁻¹ * ∫ y in Icc (0 : ℝ) 1, Ψ x y =
      ∫ u in (-x / δ)..((1 - x) / δ), Kf σ4 u (gvec F₁ F₂ F₃ F₄ x (δ * u + x)) := by
    intro x
    have hsub := intervalIntegral.integral_comp_mul_add (a := -x / δ) (b := (1 - x) / δ)
      (fun y => Ψ x y) hδ.ne' x
    have e0 : δ * (-x / δ) + x = 0 := by field_simp; ring
    have e1 : δ * ((1 - x) / δ) + x = 1 := by field_simp; ring
    rw [e0, e1, smul_eq_mul, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr_ae
      ((LQGDimension.GraphCov.ae_ne_real 0).mono fun u hu _ => ?_)
    simp only [hΨ]
    rw [neglog_norm_graphPt hd hδ F₁ F₃ x hu, neglog_norm_graphPt hd hδ F₁ F₄ x hu,
      neglog_norm_graphPt hd hδ F₂ F₃ x hu, neglog_norm_graphPt hd hδ F₂ F₄ x hu, Kf_σ4_gvec]
    ring
  rw [hlog, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun x _ => hinner x

end DoubleIntegral

/-! ## Step 3: dominated convergence -/

section Limit

variable {d : ℕ}

/-- **Lemma 3.2, general form** (HA2 D6, Steps 1–3): along any countably generated filter `l`,
if `δ → 0⁺`, the profiles are continuous and bounded by `M` on `[0,1]`, and the second pair of
profiles is equicontinuous in the sense `F(δ w + x) - F(x) → 0` (`x ∈ (0,1)`, `w ∈ ℝ`), then
`δ⁻¹ logCov(μ_{δF₁} - μ_{δF₂}, μ_{δF₃} - μ_{δF₄}) - fourLim F₁ F₂ F₃ F₄ → 0`.  Taking `l` a
product filter `𝓝[>] 0 ×ˢ 𝓟 S` gives uniformity over `S`; taking moving profiles gives the
moving-family form. -/
theorem tendsto_graph_logCov_sub_fourLim (hd : 0 < d) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {δ : ι → ℝ} (hδ : Tendsto δ l (𝓝[>] 0))
    (F₁ F₂ F₃ F₄ : ι → ℝ → Rd (d - 1)) (M : ℝ)
    (hc : ∀ᶠ i in l, Continuous (F₁ i) ∧ Continuous (F₂ i) ∧ Continuous (F₃ i) ∧
      Continuous (F₄ i))
    (hM : ∀ᶠ i in l, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖F₁ i x‖ ≤ M ∧ ‖F₂ i x‖ ≤ M ∧ ‖F₃ i x‖ ≤ M ∧ ‖F₄ i x‖ ≤ M)
    (h₃ : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w : ℝ,
      Tendsto (fun i => F₃ i (δ i * w + x) - F₃ i x) l (𝓝 0))
    (h₄ : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w : ℝ,
      Tendsto (fun i => F₄ i (δ i * w + x) - F₄ i x) l (𝓝 0)) :
    Tendsto (fun i => (δ i)⁻¹ * logCov (graphMeasure d (δ i) (F₁ i))
        (graphMeasure d (δ i) (F₂ i)) (graphMeasure d (δ i) (F₃ i))
        (graphMeasure d (δ i) (F₄ i)) - fourLim (F₁ i) (F₂ i) (F₃ i) (F₄ i)) l (𝓝 0) := by
  have hδpos : ∀ᶠ i in l, 0 < δ i := hδ self_mem_nhdsWithin
  have hinv : Tendsto (fun i => (δ i)⁻¹) l atTop := tendsto_inv_nhdsGT_zero.comp hδ
  obtain ⟨hII, hT⟩ := LQGDimension.GraphCov.core_tendsto (l := l) σ4 (2 * M)
    (fun i x w => gvec (F₁ i) (F₂ i) (F₃ i) (F₄ i) x (δ i * w + x))
    (fun i x => gvec (F₁ i) (F₂ i) (F₃ i) (F₄ i) x x)
    (fun i x => -x / δ i) (fun i x => (1 - x) / δ i)
    (by
      filter_upwards [hc] with i hci
      obtain ⟨c₁, c₂, c₃, c₄⟩ := hci
      refine ⟨fun k => (continuous_gvec c₁ c₂ c₃ c₄ continuous_fst
        ((continuous_const.mul continuous_snd).add continuous_fst) k).measurable,
        fun k => (continuous_gvec c₁ c₂ c₃ c₄ continuous_id continuous_id k).measurable,
        (continuous_neg.div_const _).measurable,
        ((continuous_const.sub continuous_id).div_const _).measurable⟩)
    (by
      filter_upwards [hδpos] with i hi x _
      exact div_le_div_of_nonneg_right (by linarith) hi.le)
    (by
      filter_upwards [hδpos, hM] with i hi hMi x hx
      refine ⟨fun w hw k => abs_gvec_le (hMi x hx) (hMi _ ?_) k,
        fun k => abs_gvec_le (hMi x hx) (hMi x hx) k⟩
      have h1 := mul_le_mul_of_nonneg_left hw.1 hi.le
      have h2 := mul_le_mul_of_nonneg_left hw.2 hi.le
      rw [mul_div_cancel₀ _ hi.ne'] at h1 h2
      constructor <;> linarith)
    (by
      intro x hx w k
      refine squeeze_zero_norm (fun i => ?_) (((h₃ x hx w).norm.add (h₄ x hx w).norm).trans ?_)
      · rw [Real.norm_eq_abs]
        exact abs_gvec_sub_le _ _ _ _ x _ k
      · rw [norm_zero, add_zero])
    (fun x hx => (hinv.const_mul_atTop_of_neg (neg_neg_of_pos hx.1)).congr fun i => by
      rw [div_eq_mul_inv])
    (fun x hx => (hinv.const_mul_atTop (sub_pos.2 hx.2)).congr fun i => by
      rw [div_eq_mul_inv])
  refine hT.congr' ?_
  filter_upwards [hδpos, hc, hM, hII] with i hi hci hMi hIIi
  obtain ⟨c₁, c₂, c₃, c₄⟩ := hci
  have hB : IntervalIntegrable (fun x => 2 * Real.pi *
      ∑ k, σ4 k * |gvec (F₁ i) (F₂ i) (F₃ i) (F₄ i) x x k|) volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    exact continuous_const.mul (continuous_finsetSum _ fun k _ => continuous_const.mul
      (continuous_gvec c₁ c₂ c₃ c₄ continuous_id continuous_id k).abs)
  have hA := hIIi.add hB
  simp only [sub_add_cancel] at hA
  rw [intervalIntegral.integral_sub hA hB, logCov_graph_eq_integral hd hi c₁.measurable
    c₂.measurable c₃.measurable c₄.measurable hMi]
  congr 1
  unfold fourLim
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun x _ => limSum_gvec _ _ _ _ x

/-- A continuous extension of a profile that is continuous on `[0,1]`. -/
theorem exists_continuous_extension {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (hf : ContinuousOn f (Icc 0 1)) : ∃ g : ℝ → E, Continuous g ∧ EqOn f g (Icc 0 1) :=
  ⟨IccExtend zero_le_one (fun t : Icc (0 : ℝ) 1 => f t),
    continuous_IccExtend_iff.2 (hf.comp_continuous continuous_subtype_val fun t => t.2),
    fun _ hx => (IccExtend_of_mem zero_le_one (fun t : Icc (0 : ℝ) 1 => f t) hx).symm⟩

/-- Pointwise form of the general limit: four fixed profiles, continuous on `[0,1]`. -/
theorem tendsto_graph_logCov_fourLim (hd : 0 < d) {F₁ F₂ F₃ F₄ : ℝ → Rd (d - 1)}
    (h₁ : ContinuousOn F₁ (Icc 0 1)) (h₂ : ContinuousOn F₂ (Icc 0 1))
    (h₃ : ContinuousOn F₃ (Icc 0 1)) (h₄ : ContinuousOn F₄ (Icc 0 1)) :
    Tendsto (fun δ => δ⁻¹ * logCov (graphMeasure d δ F₁) (graphMeasure d δ F₂)
        (graphMeasure d δ F₃) (graphMeasure d δ F₄)) (𝓝[>] 0)
      (𝓝 (fourLim F₁ F₂ F₃ F₄)) := by
  obtain ⟨G₁, c₁, e₁⟩ := exists_continuous_extension h₁
  obtain ⟨G₂, c₂, e₂⟩ := exists_continuous_extension h₂
  obtain ⟨G₃, c₃, e₃⟩ := exists_continuous_extension h₃
  obtain ⟨G₄, c₄, e₄⟩ := exists_continuous_extension h₄
  -- a common bound on `[0,1]`
  have hb : ∀ G : ℝ → Rd (d - 1), Continuous G → ∃ C, ∀ x ∈ Icc (0 : ℝ) 1, ‖G x‖ ≤ C :=
    fun G hG => isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  obtain ⟨C₁, hC₁⟩ := hb G₁ c₁
  obtain ⟨C₂, hC₂⟩ := hb G₂ c₂
  obtain ⟨C₃, hC₃⟩ := hb G₃ c₃
  obtain ⟨C₄, hC₄⟩ := hb G₄ c₄
  set M := max (max C₁ C₂) (max C₃ C₄) with hMdef
  have hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖G₁ x‖ ≤ M ∧ ‖G₂ x‖ ≤ M ∧ ‖G₃ x‖ ≤ M ∧ ‖G₄ x‖ ≤ M :=
    fun x hx => ⟨(hC₁ x hx).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hC₂ x hx).trans ((le_max_right _ _).trans (le_max_left _ _)),
      (hC₃ x hx).trans ((le_max_left _ _).trans (le_max_right _ _)),
      (hC₄ x hx).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  have hcont : ∀ G : ℝ → Rd (d - 1), Continuous G → ∀ x : ℝ, ∀ w : ℝ,
      Tendsto (fun δ : ℝ => G (δ * w + x) - G x) (𝓝[>] 0) (𝓝 0) := by
    intro G hG x w
    have h1 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝 0) (𝓝 x) := by
      have h0 : Tendsto (fun δ : ℝ => δ * w + x) (𝓝 0) (𝓝 (0 * w + x)) :=
        ((continuous_id.mul continuous_const).add continuous_const).tendsto 0
      rwa [zero_mul, zero_add] at h0
    have := (((hG.tendsto x).comp h1).sub_const (G x)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [sub_self] at this
  have h := tendsto_graph_logCov_sub_fourLim hd (l := 𝓝[>] (0 : ℝ)) tendsto_id
    (fun _ => G₁) (fun _ => G₂) (fun _ => G₃) (fun _ => G₄) M
    (Eventually.of_forall fun _ => ⟨c₁, c₂, c₃, c₄⟩) (Eventually.of_forall fun _ => hM)
    (fun x _ w => hcont G₃ c₃ x w) (fun x _ w => hcont G₄ c₄ x w)
  have h' := h.add_const (fourLim G₁ G₂ G₃ G₄)
  simp only [id, sub_add_cancel, zero_add] at h'
  rw [fourLim_congr e₁ e₂ e₃ e₄]
  refine h'.congr fun δ => ?_
  rw [graphMeasure_congr e₁, graphMeasure_congr e₂, graphMeasure_congr e₃,
    graphMeasure_congr e₄]

/-- **(3.8)** (HA2 D6): for profiles continuous on `[0,1]`,
`δ⁻¹ Var⟨h, μ_{δf} - μ_{δg}⟩ = δ⁻¹ logCov(μ_{δf} - μ_{δg}, μ_{δf} - μ_{δg}) → 2π ∫₀¹ |f - g|`. -/
theorem tendsto_graph_logCov_var (hd : 0 < d) {f g : ℝ → Rd (d - 1)}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto (fun δ => δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ g)
        (graphMeasure d δ f) (graphMeasure d δ g)) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖f x - g x‖)) := by
  rw [← fourLim_self]
  exact tendsto_graph_logCov_fourLim hd hf hg hf hg

/-- **(3.8), polarized** (HA2 D6, "Polarization"): for profiles continuous on `[0,1]`,
`δ⁻¹ Cov(⟨h, μ_{δf} - μ_{δ0}⟩, ⟨h, μ_{δg} - μ_{δ0}⟩) → gCov f g = π ∫₀¹ (|f| + |g| - |f - g|)`. -/
theorem tendsto_graph_logCov_cov (hd : 0 < d) {f g : ℝ → Rd (d - 1)}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto (fun δ => δ⁻¹ * logCov (graphMeasure d δ f) (graphMeasure d δ 0)
        (graphMeasure d δ g) (graphMeasure d δ 0)) (𝓝[>] 0) (𝓝 (gCov f g)) := by
  rw [← fourLim_zero]
  exact tendsto_graph_logCov_fourLim hd hf continuousOn_const hg continuousOn_const

/-- **(3.8), HA2's `Lemma32Var`** (all-scale covariance form): for an admissible kernel and
profiles continuous on `[0,1]`, `δ⁻¹ Var⟨h, μ_{δf} - μ_{δg}⟩ → 2π ∫₀¹ |f - g|`. -/
theorem lemma32Var (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {f g : ℝ → Rd (d - 1)}
    (hf : ContinuousOn f (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    Tendsto (fun δ => δ⁻¹ * scaleCov κ (Ioi 0) (graphMeasure d δ f) (graphMeasure d δ g)
        (graphMeasure d δ f) (graphMeasure d δ g)) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * ∫ x in (0 : ℝ)..1, ‖f x - g x‖)) := by
  obtain ⟨F, cF, eF⟩ := exists_continuous_extension hf
  obtain ⟨G, cG, eG⟩ := exists_continuous_extension hg
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn cF.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn cG.continuousOn
  have hF : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ max C₁ C₂ := fun x hx =>
    (hC₁ x hx).trans (le_max_left _ _)
  have hG : ∀ x ∈ Icc (0 : ℝ) 1, ‖G x‖ ≤ max C₁ C₂ := fun x hx =>
    (hC₂ x hx).trans (le_max_right _ _)
  refine (tendsto_graph_logCov_var hd hf hg).congr fun δ => ?_
  rw [graphMeasure_congr eF, graphMeasure_congr eG,
    scaleCov_eq_logCov_graph hd hκ cF.measurable cG.measurable cF.measurable cG.measurable hF hG
      hF hG]

end Limit

/-! ## (3.8′): uniformity on vertex balls of `V_n(ℝ^{d-1})` -/

section Uniform

variable {d : ℕ}

/-- Asymptotic equivalence along `p ×ˢ 𝓟 S` is uniform convergence on `S`. -/
theorem tendstoUniformlyOn_of_tendsto_sub {α β : Type*} {p : Filter α} {S : Set β}
    {F : α → β → ℝ} {f : β → ℝ}
    (h : Tendsto (fun q : α × β => F q.1 q.2 - f q.2) (p ×ˢ 𝓟 S) (𝓝 0)) :
    TendstoUniformlyOn F f p S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h1 := (Metric.tendsto_nhds.1 h) ε hε
  rw [eventually_prod_principal_iff] at h1
  filter_upwards [h1] with a ha x hx
  have := ha x hx
  rwa [Real.dist_eq, sub_zero, abs_sub_comm, ← Real.dist_eq] at this

/-- **(3.8′)** (HA2 D6, HA2-10; HA3 (I5) for graph measures): uniformly for `f, g` in the vertex
ball `B̂_R = {f ∈ V_n(ℝ^{d-1}) : max_i |f(i 2⁻ⁿ)| ≤ R}`,
`δ⁻¹ logCov(μ_{δf} - μ_{δ0}, μ_{δg} - μ_{δ0}) → gCov f g` as `δ ↓ 0`. -/
theorem tendstoUniformlyOn_graph_logCov (hd : 0 < d) (n : ℕ) (R : ℝ) :
    TendstoUniformlyOn (fun δ (p : (ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        δ⁻¹ * logCov (graphMeasure d δ p.1) (graphMeasure d δ 0) (graphMeasure d δ p.2)
          (graphMeasure d δ 0))
      (fun p => gCov p.1 p.2) (𝓝[>] 0)
      (vertBall (Rd (d - 1)) n R ×ˢ vertBall (Rd (d - 1)) n R) := by
  set S := vertBall (Rd (d - 1)) n R ×ˢ vertBall (Rd (d - 1)) n R with hS
  set l := 𝓝[>] (0 : ℝ) ×ˢ 𝓟 S with hl
  have hmem : ∀ᶠ i in l, i.2 ∈ S := by
    rw [hl, eventually_prod_principal_iff]
    exact Eventually.of_forall fun _ y hy => hy
  have hδ : Tendsto (fun i : ℝ × _ => i.1) l (𝓝[>] 0) := tendsto_fst
  set L := 2 * R * 2 ^ n with hL
  have hlip : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ w : ℝ,
      Tendsto (fun i : ℝ × ((ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        i.2.2 (i.1 * w + x) - i.2.2 x) l (𝓝 0) := by
    intro x _ w
    have h0 : Tendsto (fun i : ℝ × ((ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        L * |i.1 * w|) l (𝓝 0) := by
      have := ((hδ.mono_right nhdsWithin_le_nhds).mul_const w).abs.const_mul L
      simpa using this
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [hmem] with i hi
    have := Vg_norm_sub_le hi.2.1 hi.2.2 (i.1 * w + x) x
    rwa [add_sub_cancel_right] at this
  have h := tendsto_graph_logCov_sub_fourLim hd (l := l) hδ (fun i => i.2.1) (fun _ => 0)
    (fun i => i.2.2) (fun _ => 0) (max R 0)
    (by
      filter_upwards [hmem] with i hi
      exact ⟨Var.Vg_continuous hi.1.1, continuous_const, Var.Vg_continuous hi.2.1,
        continuous_const⟩)
    (by
      filter_upwards [hmem] with i hi x _
      refine ⟨(Vg_norm_le_of_verts hi.1.1 hi.1.2 x).trans (le_max_left _ _), ?_,
        (Vg_norm_le_of_verts hi.2.1 hi.2.2 x).trans (le_max_left _ _), ?_⟩ <;>
      simp only [Pi.zero_apply, norm_zero, le_max_right])
    hlip (fun x _ w => by simpa using tendsto_const_nhds (x := (0 : Rd (d - 1))))
  refine tendstoUniformlyOn_of_tendsto_sub ?_
  refine h.congr' ?_
  filter_upwards [hmem] with i _
  rw [fourLim_zero]

/-- **(3.8′)** on every subset of `V_n(ℝ^{d-1})` with bounded vertex image (e.g. compact
`verts n '' K`, as in HA2's `Lemma32ESup`). -/
theorem tendstoUniformlyOn_graph_logCov_of_bounded (hd : 0 < d) {n : ℕ}
    {K : Set (ℝ → Rd (d - 1))} (hK : K ⊆ Vg (Rd (d - 1)) n)
    (hb : Bornology.IsBounded (verts n '' K)) :
    TendstoUniformlyOn (fun δ (p : (ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        δ⁻¹ * logCov (graphMeasure d δ p.1) (graphMeasure d δ 0) (graphMeasure d δ p.2)
          (graphMeasure d δ 0))
      (fun p => gCov p.1 p.2) (𝓝[>] 0) (K ×ˢ K) := by
  obtain ⟨R, hR⟩ := exists_subset_vertBall hK hb
  exact (tendstoUniformlyOn_graph_logCov hd n R).mono (prod_mono hR hR)

/-- **(3.8′)** on every compact subset of `V_n(ℝ^{d-1})` (compact for the topology of pointwise
convergence of `ℝ → ℝ^{d-1}`; the vertex map is continuous). -/
theorem tendstoUniformlyOn_graph_logCov_of_isCompact (hd : 0 < d) {n : ℕ}
    {K : Set (ℝ → Rd (d - 1))} (hK : K ⊆ Vg (Rd (d - 1)) n) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun δ (p : (ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        δ⁻¹ * logCov (graphMeasure d δ p.1) (graphMeasure d δ 0) (graphMeasure d δ p.2)
          (graphMeasure d δ 0))
      (fun p => gCov p.1 p.2) (𝓝[>] 0) (K ×ˢ K) := by
  have hv : Continuous (verts (E := Rd (d - 1)) n) :=
    continuous_pi fun i => continuous_apply _
  exact tendstoUniformlyOn_graph_logCov_of_bounded hd hK (hKc.image hv).isBounded

/-- **(3.8′)**, all-scale covariance form: for an admissible kernel `κ`,
`δ⁻¹ Cov(⟨h, μ_{δf} - μ_{δ0}⟩, ⟨h, μ_{δg} - μ_{δ0}⟩) → gCov f g` uniformly on vertex balls. -/
theorem tendstoUniformlyOn_graph_scaleCov (hd : 0 < d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    (n : ℕ) (R : ℝ) :
    TendstoUniformlyOn (fun δ (p : (ℝ → Rd (d - 1)) × (ℝ → Rd (d - 1))) =>
        δ⁻¹ * scaleCov κ (Ioi 0) (graphMeasure d δ p.1) (graphMeasure d δ 0)
          (graphMeasure d δ p.2) (graphMeasure d δ 0))
      (fun p => gCov p.1 p.2) (𝓝[>] 0)
      (vertBall (Rd (d - 1)) n R ×ˢ vertBall (Rd (d - 1)) n R) := by
  refine (tendstoUniformlyOn_graph_logCov hd n R).congr (Eventually.of_forall fun δ p hp => ?_)
  have h0 : ∀ x ∈ Icc (0 : ℝ) 1, ‖(0 : ℝ → Rd (d - 1)) x‖ ≤ max R 0 := fun x _ => by
    simp only [Pi.zero_apply, norm_zero, le_max_right]
  have h1 : ∀ x ∈ Icc (0 : ℝ) 1, ‖p.1 x‖ ≤ max R 0 := fun x _ =>
    (Vg_norm_le_of_verts hp.1.1 hp.1.2 x).trans (le_max_left _ _)
  have h2 : ∀ x ∈ Icc (0 : ℝ) 1, ‖p.2 x‖ ≤ max R 0 := fun x _ =>
    (Vg_norm_le_of_verts hp.2.1 hp.2.2 x).trans (le_max_left _ _)
  have e := scaleCov_eq_logCov_graph (δ := δ) (f₁ := p.1) (f₂ := 0) (f₃ := p.2) (f₄ := 0) hd hκ
    (Var.Vg_continuous hp.1.1).measurable measurable_const (Var.Vg_continuous hp.2.1).measurable
    measurable_const h1 h0 h2 h0
  simp only at e ⊢
  rw [← e]

end Uniform

end HigherDimLFPP
