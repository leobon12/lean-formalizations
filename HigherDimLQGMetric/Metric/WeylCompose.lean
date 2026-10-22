import HigherDimLQGMetric.Metric.WeylBridge

/-!
# Weyl scaling on `ℝ^d`: constants, composition, continuity in the weight

Packet M1 (Phase A, block A2), on top of the bridge `weylScaleOn_eq_iInf_curve` and the length
identity `curveLength_eq_weightedLength_of_weyl` ([S] Lemma 2.1(c)).

* **Constants**: `e^{ξ (f + c)}·D = e^{ξ c} (e^{ξ f}·D)` (`weylScaleOn_add_const`,
  `weylScale_add_const`); no hypothesis on `D`.
* **Composition**: if `D' = e^{ξ g}·D` then `e^{ξ f}·D' = e^{ξ (f + g)}·D`
  (`weylScaleOn_of_eq_weylScale`, `weylScale_of_eq_weylScale`; for the continuous metric:
  `weylScale_weylMetric`, `weylMetric_weylMetric`). Proof: along every curve, the weighted
  `D'`-length with weight `e^{ξ f}` is the weighted `D`-length with weight `e^{ξ (f + g)}`
  (`weightedLength_weyl_chain`): reduce to the parametrization by `D`-length, where
  `len(·; D') = ∫ e^{ξ g}` on subintervals (Lemma 2.1(c)), and apply the chain rule
  `weightedLength_eq_lintegral_of_curveLength`.
* **Continuity in the weight**: the ratio bound `(e^{ξ f}·D)_U ≤ e^c (e^{ξ g}·D)_U` whenever
  `ξ f ≤ ξ g + c` on `U` (`weylScaleOn_le_exp_mul`; on internal metrics:
  `weylMetric_internal_le_exp_mul`), and **uniform** convergence `f_n → f` gives
  `e^{ξ f_n}·D → e^{ξ f}·D` in `ContMetric d`, i.e. locally uniformly (`tendsto_weylMetric`).
  Locally uniform convergence of `f_n` does not suffice for the global metric (escape to infinity
  through regions where `f_n ≪ f`; see the M1 handoff); on a bounded set `U` it gives uniform
  convergence of the weights on `U` and the ratio bound applies to `(e^{ξ f_n}·D)_U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### Constants -/

/-- **Weyl scaling by a constant**: `e^{ξ (f + c)}·D = e^{ξ c} (e^{ξ f}·D)` (paths in `U`). -/
theorem weylScaleOn_add_const (ξ : ℝ) (f : C(Rd d, ℝ)) (c : ℝ) (D : ContMetric d)
    (U : Set (Rd d)) (z w : Rd d) :
    weylScaleOn ξ (f + ContinuousMap.const (Rd d) c) D U z w =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaleOn ξ f D U z w := by
  have h0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 := by simpa using Real.exp_pos (ξ * c)
  simp only [weylScaleOn, ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun L => iInf_congr fun P => iInf_congr fun _ => iInf_congr fun _ =>
    iInf_congr fun _ => iInf_congr fun _ => iInf_congr fun _ => iInf_congr fun _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ContinuousMap.add_apply,
    ContinuousMap.const_apply, mul_add, add_comm]

/-- **Weyl scaling by a constant**: `e^{ξ (f + c)}·D = e^{ξ c} (e^{ξ f}·D)`. -/
theorem weylScale_add_const (ξ : ℝ) (f : C(Rd d, ℝ)) (c : ℝ) (D : ContMetric d) (z w : Rd d) :
    weylScale ξ (f + ContinuousMap.const (Rd d) c) D z w =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScale ξ f D z w := by
  simp only [← weylScaleOn_univ]; exact weylScaleOn_add_const ξ f c D univ z w

/-! ### Composition -/

section Compose

variable {ξ : ℝ} {f g : C(Rd d, ℝ)} {D D' : ContMetric d}

/-- **Chain rule along a curve**: if `D' = e^{ξ g}·D`, then for every Euclidean-continuous curve
on `[0, 1]`, `∫_P e^{ξ f} ds_{D'} = ∫_P e^{ξ (f + g)} ds_D`. -/
theorem weightedLength_weyl_chain
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ g D x y) {P : ℝ → Rd d}
    (hP : ContinuousOn P (Icc 0 1)) :
    weightedLength (D'.weylWeight ξ f) (D'.pt ∘ P) 0 1 =
      weightedLength (D.weylWeight ξ (f + g)) (D.pt ∘ P) 0 1 := by
  set Q : ℝ → D.Space := D.pt ∘ P with hQ
  have hQc : ContinuousOn Q (Icc 0 1) := D.continuous_pt.comp_continuousOn hP
  have hQ'c : ContinuousOn (D'.pt ∘ P) (Icc 0 1) := D'.continuous_pt.comp_continuousOn hP
  by_cases hL : curveLength Q 0 1 = ⊤
  · -- both weighted lengths are infinite
    obtain ⟨m, M, hm, hmM⟩ := exists_bounds_along (U := univ)
      (D.continuous_weylWeight ξ (f + g)).continuousOn
      (fun x _ => D.weylWeight_pos ξ (f + g) x) zero_le_one hQc (mapsTo_univ _ _)
    rw [weightedLength_eq_top hm zero_le_one (fun s hs => (hmM s hs).1) hL]
    have hL' : curveLength (D'.pt ∘ P) 0 1 = ⊤ := by
      by_contra hne
      exact (curveLength_weyl_ne_top_iff hD' zero_le_one hP).1 hne hL
    obtain ⟨m', M', hm', hmM'⟩ := exists_bounds_along (U := univ)
      (D'.continuous_weylWeight ξ f).continuousOn (fun x _ => D'.weylWeight_pos ξ f x)
      zero_le_one hQ'c (mapsTo_univ _ _)
    exact weightedLength_eq_top hm' zero_le_one (fun s hs => (hmM' s hs).1) hL'
  -- reduction to the parametrization by `D`-length
  set ℓ := (curveLength Q 0 1).toReal with hℓ
  obtain ⟨hu, hcP, -, -, -⟩ := lengthParam_props zero_le_one hQc hL (mapsTo_univ Q _)
  set Pn := lengthParam Q 0 1 with hPn
  set R : ℝ → Rd d := D.unpt ∘ Pn with hR
  have hRc : ContinuousOn R (Icc 0 ℓ) := D.continuous_unpt.comp_continuousOn hcP
  have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
  have hRHS : weightedLength (D.weylWeight ξ (f + g)) Q 0 1 =
      ∫⁻ τ in Icc 0 ℓ, ENNReal.ofReal (Real.exp (ξ * (f + g) (R τ))) := by
    rw [weightedLength_eq_lengthParam zero_le_one hQc hL,
      weightedLength_of_hasUnitSpeedOn hℓ0 hu
        ((D.continuous_weylWeight ξ (f + g)).comp_continuousOn hcP)]
    rfl
  set σ := variationOnFromTo Q (Icc 0 1) 0 with hσ
  have hbv : BoundedVariationOn Q (Icc 0 1) := hL
  have hσm : MonotoneOn σ (Icc 0 1) :=
    variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn ⟨le_rfl, zero_le_one⟩
  have hσc : ContinuousOn σ (Icc 0 1) := continuousOn_variationOnFromTo zero_le_one hQc hL
  have hσ0 : σ 0 = 0 := variationOnFromTo.self _ _ _
  have hσ1 : σ 1 = ℓ := by
    rw [hσ, variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self]; rfl
  have hLHS : weightedLength (D'.weylWeight ξ f) (D'.pt ∘ P) 0 1 =
      weightedLength (D'.weylWeight ξ f) (D'.pt ∘ R) 0 ℓ := by
    have hcomp := weightedLength_comp_monotoneOn (w := D'.weylWeight ξ f) (P := D'.pt ∘ R)
      zero_le_one hσc hσm
    rw [hσ0, hσ1] at hcomp
    rw [← hcomp]
    refine weightedLength_congr fun t ht => ?_
    show D'.pt (P t) = D'.pt (D.unpt (Pn (σ t)))
    rw [hPn, lengthParam_variationOnFromTo hL ht]
    rfl
  have hlen : ∀ u t, 0 ≤ u → u ≤ t → t ≤ ℓ → curveLength (D'.pt ∘ R) u t =
      ∫⁻ τ in Icc u t, ENNReal.ofReal (Real.exp (ξ * g (R τ))) := by
    intro u t hu0 hut htℓ
    rw [curveLength_eq_weightedLength_of_weyl hD' (hRc.mono (Icc_subset_Icc hu0 htℓ))]
    exact weightedLength_of_hasUnitSpeedOn (X := D.Space) (w := D.weylWeight ξ g)
      (P := D.pt ∘ R) hut (hasUnitSpeedOn_mono_Icc hu hu0 htℓ)
      (((D.continuous_weylWeight ξ g).comp_continuousOn hcP).mono (Icc_subset_Icc hu0 htℓ))
  have hfin : curveLength (D'.pt ∘ R) 0 ℓ ≠ ⊤ := by
    rw [curveLength_eq_weightedLength_of_weyl hD' hRc]
    obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn
      ((D.continuous_weylWeight ξ g).comp_continuousOn hcP)).bddAbove
    refine weightedLength_ne_top (M := M) (fun s hs => hM ⟨s, hs, rfl⟩) ?_
    rw [show D.pt ∘ R = Pn from rfl, hPn, curveLength_lengthParam zero_le_one hQc hL]
    exact hL
  rw [hLHS, weightedLength_eq_lintegral_of_curveLength hℓ0 hlen hfin
    ((D'.continuous_weylWeight ξ f).comp_continuousOn (D'.continuous_pt.comp_continuousOn hRc)),
    hRHS]
  refine setLIntegral_congr_fun measurableSet_Icc fun τ _ => ?_
  show ENNReal.ofReal (Real.exp (ξ * f (R τ))) * ENNReal.ofReal (Real.exp (ξ * g (R τ))) = _
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ContinuousMap.add_apply, mul_add]

/-- **Composition** (paths in `U`): if `D' = e^{ξ g}·D` then `(e^{ξ f}·D')_U = (e^{ξ (f + g)}·D)_U`. -/
theorem weylScaleOn_of_eq_weylScale
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ g D x y) (f : C(Rd d, ℝ))
    (U : Set (Rd d)) (z w : Rd d) :
    weylScaleOn ξ f D' U z w = weylScaleOn ξ (f + g) D U z w := by
  rw [weylScaleOn_eq_iInf_curve, weylScaleOn_eq_iInf_curve]
  exact iInf_congr fun P => iInf_congr fun hc => iInf_congr fun _ => iInf_congr fun _ =>
    iInf_congr fun _ => weightedLength_weyl_chain hD' hc

/-- **Composition**: if `D' = e^{ξ g}·D` then `e^{ξ f}·D' = e^{ξ (f + g)}·D`. -/
theorem weylScale_of_eq_weylScale
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ g D x y) (f : C(Rd d, ℝ))
    (z w : Rd d) : weylScale ξ f D' z w = weylScale ξ (f + g) D z w := by
  simp only [← weylScaleOn_univ]; exact weylScaleOn_of_eq_weylScale hD' f univ z w

/-- **Composition** with the continuous metric `e^{ξ g}·D` (`D` a length metric):
`e^{ξ f}·(e^{ξ g}·D) = e^{ξ (f + g)}·D`. -/
theorem weylScale_weylMetric (hD : D.IsLength) (f : C(Rd d, ℝ)) (z w : Rd d) :
    weylScale ξ f (weylMetric ξ g D hD) z w = weylScale ξ (f + g) D z w :=
  weylScale_of_eq_weylScale (weylMetric_spec hD) f z w

/-- **Composition** of the continuous metrics: `e^{ξ f}·(e^{ξ g}·D) = e^{ξ (f + g)}·D`. -/
theorem weylMetric_weylMetric (hD : D.IsLength) (f : C(Rd d, ℝ)) :
    weylMetric ξ f (weylMetric ξ g D hD) (weylMetric_isLength hD) = weylMetric ξ (f + g) D hD := by
  apply Subtype.ext
  apply ContinuousMap.ext
  rintro ⟨z, w⟩
  show (weylScale ξ f (weylMetric ξ g D hD) z w).toReal = (weylScale ξ (f + g) D z w).toReal
  rw [weylScale_weylMetric]

end Compose

/-! ### Pathwise consequences of Axiom (III) -/

section Pathwise

variable {ξ : ℝ} {D D' E E' : ContMetric d}

/-- **Axiom (III) with a constant**, pathwise: if `D` is a length metric and `D' = e^{ξ c}·D`,
then `D' = e^{ξ c} D`. -/
theorem apply_eq_exp_mul_of_weyl_const (hD : D.IsLength) {c : ℝ}
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) =
      weylScale ξ (ContinuousMap.const (Rd d) c) D x y) (x y : Rd d) :
    D'.1 (x, y) = Real.exp (ξ * c) * D.1 (x, y) := by
  have h := hD' x y
  rw [weylScale_const_of_isLength hD] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (D'.nonneg x y)
    (mul_nonneg (Real.exp_pos _).le (D.nonneg x y))).1 h

/-- **Axiom (III), two-sided bound**, pathwise: `a ≤ ξ f ≤ b` ⇒ `e^a D ≤ D' ≤ e^b D` for
`D' = e^{ξ f}·D` and `D` a length metric. -/
theorem apply_mem_Icc_of_weyl (hD : D.IsLength) {f : C(Rd d, ℝ)}
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y) {a b : ℝ}
    (ha : ∀ x, a ≤ ξ * f x) (hb : ∀ x, ξ * f x ≤ b) (x y : Rd d) :
    Real.exp a * D.1 (x, y) ≤ D'.1 (x, y) ∧ D'.1 (x, y) ≤ Real.exp b * D.1 (x, y) := by
  obtain ⟨h1, h2⟩ := weylScale_mem_Icc_of_isLength (z := x) (w := y) hD ha hb
  rw [← hD'] at h1 h2
  exact ⟨(ENNReal.ofReal_le_ofReal_iff (D'.nonneg x y)).1 h1,
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le (D.nonneg x y))).1 h2⟩

/-- **Comparison passes to Weyl scalings** (MA1 A1.2 (v)): if `E ≤ C D` (`C > 0`), then
`e^{ξ f}·E ≤ C (e^{ξ f}·D)` for every continuous `f`, in real form. -/
theorem apply_le_mul_of_weyl {C : ℝ} (hC : 0 < C) (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y))
    {f : C(Rd d, ℝ)} (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
    (hE' : ∀ x y : Rd d, ENNReal.ofReal (E'.1 (x, y)) = weylScale ξ f E x y) (x y : Rd d) :
    E'.1 (x, y) ≤ C * D'.1 (x, y) := by
  have h1 := weylScale_le_mul_of_le (ξ := ξ) (f := f) hC h x y
  rw [← hD', ← hE', ← ENNReal.ofReal_mul hC.le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (D'.nonneg x y))] at h1
  exact h1

/-- **Comparison passes to Weyl scalings**: if `c D ≤ E`, then `c (e^{ξ f}·D) ≤ e^{ξ f}·E`. -/
theorem mul_apply_le_of_weyl {c : ℝ} (hc : 0 ≤ c) (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    {f : C(Rd d, ℝ)} (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
    (hE' : ∀ x y : Rd d, ENNReal.ofReal (E'.1 (x, y)) = weylScale ξ f E x y) (x y : Rd d) :
    c * D'.1 (x, y) ≤ E'.1 (x, y) := by
  have h1 := mul_weylScale_le_of_le (ξ := ξ) (f := f) h x y
  rw [← hD', ← hE', ← ENNReal.ofReal_mul hc, ENNReal.ofReal_le_ofReal_iff (E'.nonneg x y)] at h1
  exact h1

end Pathwise

/-! ### Continuity in the weight -/

section Continuity

variable {ξ : ℝ} {f g : C(Rd d, ℝ)} {D : ContMetric d} {U : Set (Rd d)} {z w : Rd d}

/-- **Ratio bound**: if `ξ f ≤ ξ g + c` on `U`, then `(e^{ξ f}·D)_U ≤ e^c (e^{ξ g}·D)_U`. -/
theorem weylScaleOn_le_exp_mul {c : ℝ} (h : ∀ x ∈ U, ξ * f x ≤ ξ * g x + c) :
    weylScaleOn ξ f D U z w ≤ ENNReal.ofReal (Real.exp c) * weylScaleOn ξ g D U z w := by
  calc weylScaleOn ξ f D U z w
      ≤ weylScaleOn 1 (ξ • g + ContinuousMap.const (Rd d) c) D U z w :=
        weylScaleOn_mono fun x hx => by
          simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
            ContinuousMap.const_apply, one_mul]
          exact h x hx
    _ = ENNReal.ofReal (Real.exp (1 * c)) * weylScaleOn 1 (ξ • g) D U z w :=
        weylScaleOn_add_const 1 (ξ • g) c D U z w
    _ = ENNReal.ofReal (Real.exp c) * weylScaleOn ξ g D U z w := by
        rw [one_mul, weylScaleOn_congr (η := ξ) (g := g) fun x _ => by
          simp only [ContinuousMap.smul_apply, smul_eq_mul, one_mul]]

theorem weylScale_le_exp_mul {c : ℝ} (h : ∀ x, ξ * f x ≤ ξ * g x + c) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp c) * weylScale ξ g D z w := by
  simp only [← weylScaleOn_univ]; exact weylScaleOn_le_exp_mul fun x _ => h x

/-- Ratio bound on internal metrics of the continuous metrics `e^{ξ f}·D` (open `U`). -/
theorem weylMetric_internal_le_exp_mul (hD : D.IsLength) (hU : IsOpen U) {c : ℝ}
    (h : ∀ x ∈ U, ξ * f x ≤ ξ * g x + c) :
    (weylMetric ξ f D hD).internal U z w ≤
      ENNReal.ofReal (Real.exp c) * (weylMetric ξ g D hD).internal U z w := by
  rw [weylMetric_internal hD hU, weylMetric_internal hD hU]
  exact weylScaleOn_le_exp_mul h

/-- **Continuity of Weyl scaling in the weight**: if `F i → f` uniformly on `ℝ^d`, then
`e^{ξ F i}·D → e^{ξ f}·D` in `ContMetric d` (locally uniformly), for a length metric `D`. -/
theorem tendsto_weylMetric {ι : Type*} {l : Filter ι} {F : ι → C(Rd d, ℝ)}
    (hF : TendstoUniformly (fun i => ⇑(F i)) (⇑f) l) (hD : D.IsLength) :
    Tendsto (fun i => weylMetric ξ (F i) D hD) l (𝓝 (weylMetric ξ f D hD)) := by
  rw [ContMetric.tendsto_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_weylDist (ξ := ξ) (f := f) hD).continuousOn
  set B' := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  set c : ℝ := min 1 (ε / (6 * B' + 6)) with hc
  have hc0 : 0 < c := lt_min one_pos (div_pos hε (by positivity))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcε : 6 * c * B' < ε := by
    have h1 : c ≤ ε / (6 * B' + 6) := min_le_right _ _
    have h2 : c * (6 * B' + 6) ≤ ε := (le_div_iff₀ (by positivity)).1 h1
    nlinarith
  have hexp : Real.exp c - 1 ≤ 2 * c := by
    have := Real.abs_exp_sub_one_le (x := c) (by rw [abs_of_pos hc0]; exact hc1)
    rw [abs_of_pos hc0] at this
    exact (le_abs_self _).trans this
  set δ : ℝ := c / (|ξ| + 1) with hδ
  have hδ0 : 0 < δ := div_pos hc0 (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.1 hF δ hδ0] with i hi p hp
  -- the ratio bounds `b ≤ e^c a`, `a ≤ e^c b`
  have hξ : ∀ x, |ξ * F i x - ξ * f x| ≤ c := by
    intro x
    rw [← mul_sub, abs_mul]
    have h1 : |F i x - f x| < δ := by rw [abs_sub_comm, ← Real.dist_eq]; exact hi x
    calc |ξ| * |F i x - f x| ≤ |ξ| * δ := mul_le_mul_of_nonneg_left h1.le (abs_nonneg ξ)
      _ ≤ c := by
          rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [abs_nonneg ξ]
  set a := weylDist ξ f D p with ha
  set b := weylDist ξ (F i) D p with hb
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have haB : a ≤ B' := (hB ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hba : b ≤ Real.exp c * a := by
    have h1 := weylScale_le_exp_mul (ξ := ξ) (f := F i) (g := f) (D := D) (z := p.1) (w := p.2)
      (c := c) fun x => by linarith [(abs_le.1 (hξ x)).2]
    rw [← ofReal_weylDist hD, ← ofReal_weylDist hD, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    exact h1
  have hab : a ≤ Real.exp c * b := by
    have h1 := weylScale_le_exp_mul (ξ := ξ) (f := f) (g := F i) (D := D) (z := p.1) (w := p.2)
      (c := c) fun x => by linarith [(abs_le.1 (hξ x)).1]
    rw [← ofReal_weylDist hD, ← ofReal_weylDist hD, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    exact h1
  have hexp3 : Real.exp c ≤ 3 := by linarith
  show dist ((weylMetric ξ f D hD).1 p) ((weylMetric ξ (F i) D hD).1 p) < ε
  rw [weylMetric_apply, weylMetric_apply, Real.dist_eq]
  change |a - b| < ε
  rw [abs_lt]
  constructor
  · -- `b - a ≤ (e^c - 1) a ≤ 2 c B'`
    nlinarith [mul_le_mul_of_nonneg_right hexp ha0]
  · -- `a - b ≤ (e^c - 1) b ≤ (e^c - 1) e^c a ≤ 6 c B'`
    have hb' : b ≤ 3 * a := hba.trans (mul_le_mul_of_nonneg_right hexp3 ha0)
    nlinarith [mul_le_mul_of_nonneg_right hexp hb0]

end Continuity

end HigherDimLQGMetric
