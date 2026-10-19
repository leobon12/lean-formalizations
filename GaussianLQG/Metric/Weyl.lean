import GaussianLQG.Metric.Geodesic

/-!
# Weyl comparisons (blueprint Lemma `lem:weyl-compare`)

Let `D` be a continuous length metric on `ℂ` (`LQGMetric.ContMetric` with `ContMetric.IsLength`)
and let `f, g` be bounded continuous functions. With `e^{ξ f}·D = LQGMetric.weylScale ξ f D` and
`ξ ≥ 0`, blueprint Lemma `lem:weyl-compare`:

* (a) `e^{ξ inf f} D(z, w) ≤ (e^{ξ f}·D)(z, w) ≤ e^{ξ sup f} D(z, w)`
  (`weylScale_mem_Icc_iInf_iSup`);
* (b) for `z ≠ w`, `|log (e^{ξ f}·D)(z, w) - log (e^{ξ g}·D)(z, w)| ≤ ξ sup |f - g|`
  (`abs_log_weylScale_sub_le`);
* (c) along a constant-speed geodesic `η`, `(e^{ξ f}·D)(z, w) ≤ D(z, w) ∫_0^1 e^{ξ f(η s)} ds`:
  this is blueprint `lem:geodesic-props` (d), `GaussianLQG.weylScale_le_of_isGeod01`.

The blueprint's `e^f·d` corresponds to `weylScale 1 f D`; here the Weyl exponent `ξ` is kept
explicit, as in GM (1.6). Proofs: (a) is `LQGMetric.weylScale_mem_Icc_of_isLength` with
`a = ξ inf f` and `b = ξ sup f`; (b) compares the Weyl integrals path by path
(`weylScale_le_exp_mul_weylScale`), then uses positivity and finiteness from (a) and
`LQGMetric.weylScale_ne_top`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

variable {D : ContMetric} {ξ : ℝ} {f g : C(ℂ, ℝ)} {z w : ℂ}

/-- A bounded function is bounded below. -/
theorem bddBelow_range_of_abs_le {F : ℂ → ℝ} (hF : ∃ M, ∀ x, |F x| ≤ M) : BddBelow (range F) := by
  obtain ⟨M, hM⟩ := hF
  refine ⟨-M, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.1 (hM x)).1

/-- A bounded function is bounded above. -/
theorem bddAbove_range_of_abs_le {F : ℂ → ℝ} (hF : ∃ M, ∀ x, |F x| ≤ M) : BddAbove (range F) := by
  obtain ⟨M, hM⟩ := hF
  refine ⟨M, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.1 (hM x)).2

/-- **Blueprint `lem:weyl-compare` (a).** For a continuous length metric `D`, `ξ ≥ 0` and a
bounded continuous `f`: `e^{ξ inf f} D(z, w) ≤ (e^{ξ f}·D)(z, w) ≤ e^{ξ sup f} D(z, w)`. -/
theorem weylScale_mem_Icc_iInf_iSup (hD : D.IsLength) (hξ : 0 ≤ ξ)
    (hf : ∃ M, ∀ x, |f x| ≤ M) (z w : ℂ) :
    ENNReal.ofReal (Real.exp (ξ * ⨅ x, f x) * D.1 (z, w)) ≤ weylScale ξ f D z w ∧
      weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp (ξ * ⨆ x, f x) * D.1 (z, w)) :=
  weylScale_mem_Icc_of_isLength hD
    (fun x => mul_le_mul_of_nonneg_left (ciInf_le (bddBelow_range_of_abs_le hf) x) hξ)
    (fun x => mul_le_mul_of_nonneg_left (le_ciSup (bddAbove_range_of_abs_le hf) x) hξ)

/-- Path-by-path comparison: if `ξ f ≤ ξ g + c` everywhere, then
`(e^{ξ f}·D)(z, w) ≤ e^c (e^{ξ g}·D)(z, w)`. No length-space assumption is needed. -/
theorem weylScale_le_exp_mul_weylScale (D : ContMetric) {c : ℝ}
    (hfg : ∀ x, ξ * f x ≤ ξ * g x + c) (z w : ℂ) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp c) * weylScale ξ g D z w := by
  have hk0 : ENNReal.ofReal (Real.exp c) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos c
  have hkt : ENNReal.ofReal (Real.exp c) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← weylScaleOn_univ, ← weylScaleOn_univ, mul_comm, ← ENNReal.div_le_iff hk0 hkt]
  refine le_weylScaleOn fun L P hL hc hu h0 h1 hU => ?_
  rw [ENNReal.div_le_iff hk0 hkt]
  calc weylScaleOn ξ f D univ z w
      ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        weylScaleOn_le hL hc hu h0 h1 hU
    _ ≤ ∫⁻ t in Icc 0 L,
          ENNReal.ofReal (Real.exp c) * ENNReal.ofReal (Real.exp (ξ * g (P t))) := by
        refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos c).le, ← Real.exp_add]
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hfg (P t)]))
    _ = (∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * g (P t)))) *
          ENNReal.ofReal (Real.exp c) := by
        rw [lintegral_const_mul' _ _ hkt, mul_comm]

/-- For a continuous length metric and `z ≠ w`, the Weyl distance is positive and finite. -/
theorem toReal_weylScale_pos (hD : D.IsLength) (hf : ∃ M, ∀ x, |f x| ≤ M) (hzw : z ≠ w) :
    0 < (weylScale ξ f D z w).toReal := by
  obtain ⟨M, hM⟩ := hf
  have hdist : 0 < D.1 (z, w) :=
    lt_of_le_of_ne (ContMetric.nonneg D z w) fun h => hzw (D.2.eq_of_eq_zero z w h.symm)
  have hlow := (weylScale_mem_Icc_of_isLength (ξ := ξ) (f := f) (z := z) (w := w) hD
    (a := -(|ξ| * M)) (b := |ξ| * M)
    (fun x => by
      have := abs_le.1 ((abs_mul ξ (f x)).trans_le
        (mul_le_mul_of_nonneg_left (hM x) (abs_nonneg ξ)))
      linarith [this.1])
    (fun x => by
      have := abs_le.1 ((abs_mul ξ (f x)).trans_le
        (mul_le_mul_of_nonneg_left (hM x) (abs_nonneg ξ)))
      linarith [this.2])).1
  have hpos : 0 < ENNReal.ofReal (Real.exp (-(|ξ| * M)) * D.1 (z, w)) :=
    ENNReal.ofReal_pos.2 (mul_pos (Real.exp_pos _) hdist)
  exact ENNReal.toReal_pos (lt_of_lt_of_le hpos hlow).ne' (weylScale_ne_top hD z w)

/-- One-sided form of blueprint `lem:weyl-compare` (b). -/
theorem log_weylScale_le_add (hD : D.IsLength) (hξ : 0 ≤ ξ) (hf : ∃ M, ∀ x, |f x| ≤ M)
    (hg : ∃ M, ∀ x, |g x| ≤ M) {c : ℝ} (hc : ∀ x, |f x - g x| ≤ c) (hzw : z ≠ w) :
    Real.log (weylScale ξ f D z w).toReal ≤ ξ * c + Real.log (weylScale ξ g D z w).toReal := by
  have hfg : ∀ x, ξ * f x ≤ ξ * g x + ξ * c := fun x => by
    have h1 : f x - g x ≤ c := (le_abs_self _).trans (hc x)
    nlinarith
  have hle := weylScale_le_exp_mul_weylScale D hfg z w
  have hfpos := toReal_weylScale_pos (ξ := ξ) hD hf hzw
  have hgpos := toReal_weylScale_pos (ξ := ξ) hD hg hzw
  have hle' : (weylScale ξ f D z w).toReal ≤
      Real.exp (ξ * c) * (weylScale ξ g D z w).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (weylScale_ne_top hD z w)) hle
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  calc Real.log (weylScale ξ f D z w).toReal
      ≤ Real.log (Real.exp (ξ * c) * (weylScale ξ g D z w).toReal) :=
        Real.log_le_log hfpos hle'
    _ = ξ * c + Real.log (weylScale ξ g D z w).toReal := by
        rw [Real.log_mul (Real.exp_pos _).ne' hgpos.ne', Real.log_exp]

/-- **Blueprint `lem:weyl-compare` (b).** For a continuous length metric `D`, `ξ ≥ 0`, bounded
continuous `f, g` and `z ≠ w`:
`|log (e^{ξ f}·D)(z, w) - log (e^{ξ g}·D)(z, w)| ≤ ξ sup |f - g|`. -/
theorem abs_log_weylScale_sub_le (hD : D.IsLength) (hξ : 0 ≤ ξ) (hf : ∃ M, ∀ x, |f x| ≤ M)
    (hg : ∃ M, ∀ x, |g x| ≤ M) (hzw : z ≠ w) :
    |Real.log (weylScale ξ f D z w).toReal - Real.log (weylScale ξ g D z w).toReal| ≤
      ξ * ⨆ x, |f x - g x| := by
  have hbdd : BddAbove (range fun x => |f x - g x|) := by
    obtain ⟨Mf, hMf⟩ := hf
    obtain ⟨Mg, hMg⟩ := hg
    refine bddAbove_range_of_abs_le ⟨Mf + Mg, fun x => ?_⟩
    rw [abs_abs]
    exact (abs_sub _ _).trans (add_le_add (hMf x) (hMg x))
  have hc : ∀ x, |f x - g x| ≤ ⨆ x, |f x - g x| := fun x => le_ciSup hbdd x
  have hc' : ∀ x, |g x - f x| ≤ ⨆ x, |f x - g x| := fun x => by
    rw [abs_sub_comm]; exact hc x
  have h1 := log_weylScale_le_add hD hξ hf hg hc hzw
  have h2 := log_weylScale_le_add hD hξ hg hf hc' hzw
  rw [abs_sub_le_iff]
  constructor <;> linarith

end GaussianLQG
