import HigherDimLQGMetric.Metric.Internal
import HigherDimLQGMetric.Frozen.WeylScale
import LQGMetric.Metric.WeylCont
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Weyl scaling `e^{ξ f}·D` on `ℝ^d`: basic identities, scaling, concatenation, symmetry

Packet M1 (Phase A, block A2). Port of LQGMetric's ℂ-typed `Metric/WeylBasic.lean`,
`Metric/WeylScaling.lean`, `Metric/WeylConcat.lean` and the symmetry part of `Metric/WeylCont.lean`
from `ℂ` to `Rd d` (ruling M10); the generic lemmas of those files (`exists_unitSpeed_of_path`,
`hasUnitSpeedOn_*`, `eVariationOn_le_lintegral`, `setLIntegral_Icc_comp_add`, ...) are imported.

`weylScale ξ f D` (frozen) is the source's `e^{ξ f}·D` ([S] l. 69–74, [1] (1.4)): the infimum, over
paths `P` from `z` to `w` parametrized by `D`-length on `[0, L]`, of `∫_0^L e^{ξ f(P t)} dt`.
`weylScaleOn ξ f D U` is the same infimum over paths staying in `U` (`weylScaleOn_univ`).

* Monotonicity in `ξ f` (`weylScaleOn_mono`, `weylScale_mono`), locality in `f`
  (`weylScaleOn_congr`), antitone in `U` (`weylScaleOn_anti`).
* Constants: if `ξ f ≡ a` on `U`, `(e^{ξ f}·D)_U = e^a D(·,·;U)` (`weylScaleOn_of_eq_const`); for a
  length metric `e^{ξ c}·D = e^{ξ c} D` (`weylScale_const_of_isLength`); two-sided bounds
  `e^a D(·,·;U) ≤ (e^{ξ f}·D)_U ≤ e^b D(·,·;U)` when `a ≤ ξ f ≤ b` on `U`
  (`le_weylScaleOn_of_le`, `weylScaleOn_le_of_le`, `weylScale_mem_Icc_of_isLength`).
* Scaling the metric: `e^{ξ f}·(C D) = C (e^{ξ f}·D)` (`weylScaleOn_smul`, `weylScale_smul`); affine
  change of coordinates `x ↦ r x + a` (`weylScaleOn_affine`, `weylScale_affine`).
* Sub-paths and concatenation: `weylScaleOn_le_sub`, `weylScaleOn_self`, `weylScaleOn_triangle`,
  `weylScaleOn_le_sum`; symmetry `weylScaleOn_comm`.

Own elementary proofs, as in the 2D layer (GM uses these facts without proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- Weyl scaling with paths constrained to `U`: the infimum of `∫_0^L e^{ξ f(P t)} dt` over
continuous paths `P ⊂ U` from `z` to `w` parametrized by `D`-length on `[0, L]`.
`weylScaleOn ξ f D univ = weylScale ξ f D` (`weylScaleOn_univ`). -/
def weylScaleOn (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (U : Set (Rd d)) (z w : Rd d) :
    ℝ≥0∞ :=
  ⨅ (L : ℝ) (P : ℝ → Rd d) (_ : 0 ≤ L) (_ : ContinuousOn (D.pt ∘ P) (Icc 0 L))
    (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = z) (_ : P L = w)
    (_ : ∀ t ∈ Icc 0 L, P t ∈ U),
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))

variable {ξ η : ℝ} {f g : C(Rd d, ℝ)} {D : ContMetric d} {U V : Set (Rd d)} {z w : Rd d}

theorem weylScaleOn_univ (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (z w : Rd d) :
    weylScaleOn ξ f D univ z w = weylScale ξ f D z w := by
  simp only [weylScaleOn, weylScale, mem_univ, implies_true, iInf_pos]

theorem weylScaleOn_le {L : ℝ} {P : ℝ → Rd d} (hL : 0 ≤ L)
    (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (h0 : P 0 = z) (h1 : P L = w) (hU : ∀ t ∈ Icc 0 L, P t ∈ U) :
    weylScaleOn ξ f D U z w ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
  iInf_le_of_le L <| iInf_le_of_le P <| iInf_le_of_le hL <| iInf_le_of_le hc <|
    iInf_le_of_le hu <| iInf_le_of_le h0 <| iInf_le_of_le h1 <| iInf_le_of_le hU le_rfl

theorem le_weylScaleOn {c : ℝ≥0∞}
    (h : ∀ (L : ℝ) (P : ℝ → Rd d), 0 ≤ L → ContinuousOn (D.pt ∘ P) (Icc 0 L) →
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) → P 0 = z → P L = w → (∀ t ∈ Icc 0 L, P t ∈ U) →
      c ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) :
    c ≤ weylScaleOn ξ f D U z w := by
  simp only [weylScaleOn, le_iInf_iff]
  exact h

theorem weylScale_le {L : ℝ} {P : ℝ → Rd d} (hL : 0 ≤ L)
    (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (h0 : P 0 = z) (h1 : P L = w) :
    weylScale ξ f D z w ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  rw [← weylScaleOn_univ]
  exact weylScaleOn_le hL hc hu h0 h1 fun _ _ => mem_univ _

theorem le_weylScale {c : ℝ≥0∞}
    (h : ∀ (L : ℝ) (P : ℝ → Rd d), 0 ≤ L → ContinuousOn (D.pt ∘ P) (Icc 0 L) →
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L) → P 0 = z → P L = w →
      c ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))) :
    c ≤ weylScale ξ f D z w := by
  rw [← weylScaleOn_univ]
  exact le_weylScaleOn fun L P hL hc hu h0 h1 _ => h L P hL hc hu h0 h1

/-- **Monotonicity in the weight**: if `ξ f ≤ η g` on `U`, then `(e^{ξ f}·D)_U ≤ (e^{η g}·D)_U`. -/
theorem weylScaleOn_mono (hfg : ∀ x ∈ U, ξ * f x ≤ η * g x) :
    weylScaleOn ξ f D U z w ≤ weylScaleOn η g D U z w :=
  le_weylScaleOn fun _ _ hL hc hu h0 h1 hU =>
    (weylScaleOn_le hL hc hu h0 h1 hU).trans <| setLIntegral_mono' measurableSet_Icc
      fun t ht => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hfg _ (hU t ht)))

/-- Locality in `f`: `(e^{ξ f}·D)_U` depends only on `ξ f` restricted to `U`. -/
theorem weylScaleOn_congr (hfg : ∀ x ∈ U, ξ * f x = η * g x) :
    weylScaleOn ξ f D U z w = weylScaleOn η g D U z w :=
  le_antisymm (weylScaleOn_mono fun x hx => (hfg x hx).le)
    (weylScaleOn_mono fun x hx => (hfg x hx).ge)

/-- **Anti-monotonicity in the domain**: fewer admissible paths for a smaller set. -/
theorem weylScaleOn_anti (hUV : U ⊆ V) : weylScaleOn ξ f D V z w ≤ weylScaleOn ξ f D U z w :=
  le_weylScaleOn fun _ _ hL hc hu h0 h1 hU =>
    weylScaleOn_le hL hc hu h0 h1 fun t ht => hUV (hU t ht)

theorem weylScale_le_weylScaleOn : weylScale ξ f D z w ≤ weylScaleOn ξ f D U z w := by
  rw [← weylScaleOn_univ]; exact weylScaleOn_anti (subset_univ U)

/-- **Global monotonicity in the weight**: `ξ f ≤ η g` everywhere ⇒ `e^{ξ f}·D ≤ e^{η g}·D`. -/
theorem weylScale_mono (hfg : ∀ x, ξ * f x ≤ η * g x) :
    weylScale ξ f D z w ≤ weylScale η g D z w := by
  rw [← weylScaleOn_univ, ← weylScaleOn_univ]; exact weylScaleOn_mono fun x _ => hfg x

/-- `f ≤ g` and `ξ ≥ 0` ⇒ `e^{ξ f}·D ≤ e^{ξ g}·D`. -/
theorem weylScale_mono_of_le (hξ : 0 ≤ ξ) (hfg : ∀ x, f x ≤ g x) :
    weylScale ξ f D z w ≤ weylScale ξ g D z w :=
  weylScale_mono fun x => mul_le_mul_of_nonneg_left (hfg x) hξ

/-- The `D`-internal distance in `U` is at most the length `L` of a unit-speed path in `U`. -/
theorem ContMetric.internal_le_of_unitSpeed {L : ℝ} {P : ℝ → Rd d} (hL : 0 ≤ L)
    (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hU : ∀ t ∈ Icc 0 L, P t ∈ U) : D.internal U (P 0) (P L) ≤ ENNReal.ofReal L := by
  obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hL hc
  have hlen : curveLength (D.pt ∘ P) 0 L = ENNReal.ofReal L := by
    rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ ⟨hL, le_rfl⟩, sub_zero]
  refine (internalEDist_le_pathLength γ fun t => ?_).trans (hγ.trans hlen).le
  obtain ⟨s, hs, hst⟩ := hrange (mem_range_self t)
  exact ⟨P s, hU s hs, hst⟩

/-- A path inside `D.pt '' U` of finite length `ℓ` yields an admissible unit-speed path. -/
theorem ContMetric.exists_unitSpeed_of_path (γ : Path (D.pt z) (D.pt w))
    (hγ : ∀ t, γ t ∈ D.pt '' U) (hL : pathLength γ ≠ ∞) :
    ∃ P : ℝ → Rd d, ContinuousOn (D.pt ∘ P) (Icc 0 (pathLength γ).toReal) ∧
      HasUnitSpeedOn (D.pt ∘ P) (Icc 0 (pathLength γ).toReal) ∧ P 0 = z ∧
      P (pathLength γ).toReal = w ∧ ∀ t ∈ Icc 0 (pathLength γ).toReal, P t ∈ U := by
  obtain ⟨P, hu, hc, h0, h1, hr⟩ := LQGMetric.MetricGeometry.exists_unitSpeed_of_path γ hL
  refine ⟨D.unpt ∘ P, hc, hu, h0, h1, fun t ht => ?_⟩
  obtain ⟨s, hs⟩ := hr t ht
  obtain ⟨x, hx, hxs⟩ := hγ s
  have : x = D.unpt (P t) := hxs.trans hs
  show D.unpt (P t) ∈ U
  exact this ▸ hx

/-- **Constant Weyl factor**: if `ξ f ≡ a` on `U`, then `(e^{ξ f}·D)_U(z, w) = e^a · D(z, w; U)`. -/
theorem weylScaleOn_of_eq_const {a : ℝ} (hf : ∀ x ∈ U, ξ * f x = a) :
    weylScaleOn ξ f D U z w = ENNReal.ofReal (Real.exp a) * D.internal U z w := by
  have hea0 : ENNReal.ofReal (Real.exp a) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact Real.exp_pos a
  apply le_antisymm
  · unfold ContMetric.internal internalEDist
    rw [ENNReal.mul_iInf_of_ne hea0 ENNReal.ofReal_ne_top]
    refine le_iInf fun γ => ?_
    by_cases hL : pathLength γ.1 = ∞
    · rw [hL, ENNReal.mul_top hea0]; exact le_top
    obtain ⟨P, hc, hu, h0, h1, hU⟩ := ContMetric.exists_unitSpeed_of_path γ.1 γ.2 hL
    refine (weylScaleOn_le ENNReal.toReal_nonneg hc hu h0 h1 hU).trans_eq ?_
    rw [LQGMetric.setLIntegral_exp_of_eq_const fun t ht => hf _ (hU t ht),
      ENNReal.ofReal_toReal hL]
  · refine le_weylScaleOn fun L P hL hc hu h0 h1 hU => ?_
    rw [LQGMetric.setLIntegral_exp_of_eq_const fun t ht => hf _ (hU t ht)]
    gcongr
    rw [← h0, ← h1]
    exact ContMetric.internal_le_of_unitSpeed hL hc hu hU

/-- `e^{ξ f}·D` for `ξ f ≡ a` is `e^a` times the induced length metric `D(·,·;ℝ^d)`. -/
theorem weylScale_of_eq_const {a : ℝ} (hf : ∀ x, ξ * f x = a) :
    weylScale ξ f D z w = ENNReal.ofReal (Real.exp a) * D.internal univ z w := by
  rw [← weylScaleOn_univ]; exact weylScaleOn_of_eq_const fun x _ => hf x

/-- **Weyl scaling by a constant** ([S] Axiom (III) with `f ≡ c`): for a length metric `D`,
`e^{ξ c}·D = e^{ξ c} D`. -/
theorem weylScale_const_of_isLength (hD : D.IsLength) (ξ c : ℝ) (z w : Rd d) :
    weylScale ξ (ContinuousMap.const (Rd d) c) D z w =
      ENNReal.ofReal (Real.exp (ξ * c) * D.1 (z, w)) := by
  rw [weylScale_of_eq_const (a := ξ * c) (fun _ => rfl), D.internal_univ_of_isLength hD,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Lower bound: `a ≤ ξ f` on `U` ⇒ `e^a D(·,·;U) ≤ (e^{ξ f}·D)_U`. -/
theorem le_weylScaleOn_of_le {a : ℝ} (hf : ∀ x ∈ U, a ≤ ξ * f x) :
    ENNReal.ofReal (Real.exp a) * D.internal U z w ≤ weylScaleOn ξ f D U z w := by
  rw [← weylScaleOn_of_eq_const (ξ := 1) (f := ContinuousMap.const (Rd d) a)
    (fun _ _ => one_mul a)]
  exact weylScaleOn_mono fun x hx => (one_mul a).trans_le (hf x hx)

/-- Upper bound: `ξ f ≤ b` on `U` ⇒ `(e^{ξ f}·D)_U ≤ e^b D(·,·;U)`. -/
theorem weylScaleOn_le_of_le {b : ℝ} (hf : ∀ x ∈ U, ξ * f x ≤ b) :
    weylScaleOn ξ f D U z w ≤ ENNReal.ofReal (Real.exp b) * D.internal U z w := by
  rw [← weylScaleOn_of_eq_const (ξ := 1) (f := ContinuousMap.const (Rd d) b)
    (fun _ _ => one_mul b)]
  exact weylScaleOn_mono fun x hx => (hf x hx).trans (one_mul b).ge

/-- **Global two-sided bound** for a length metric: `a ≤ ξ f ≤ b` ⇒
`e^a D ≤ e^{ξ f}·D ≤ e^b D`. -/
theorem weylScale_mem_Icc_of_isLength (hD : D.IsLength) {a b : ℝ}
    (ha : ∀ x, a ≤ ξ * f x) (hb : ∀ x, ξ * f x ≤ b) :
    ENNReal.ofReal (Real.exp a * D.1 (z, w)) ≤ weylScale ξ f D z w ∧
      weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp b * D.1 (z, w)) := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← D.internal_univ_of_isLength hD, ← weylScaleOn_univ]
  exact ⟨le_weylScaleOn_of_le fun x _ => ha x, weylScaleOn_le_of_le fun x _ => hb x⟩

/-! ### Scaling the metric by a constant -/

/-- If `D₂ = k D₁` (as distances) then `(e^{ξ f}·D₂)_U ≤ k (e^{ξ f}·D₁)_U`. -/
theorem weylScaleOn_le_mul_of_edist {D₁ D₂ : ContMetric d} {k : ℝ} (hk : 0 < k)
    (h : ∀ x y, edist (D₂.pt x) (D₂.pt y) = ENNReal.ofReal k * edist (D₁.pt x) (D₁.pt y)) :
    weylScaleOn ξ f D₂ U z w ≤ ENNReal.ofReal k * weylScaleOn ξ f D₁ U z w := by
  have hk0 : ENNReal.ofReal k ≠ 0 := by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hk
  rw [mul_comm, ← ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top]
  refine le_weylScaleOn fun L P hL _ hu h0 h1 hU => ?_
  rw [ENNReal.div_le_iff hk0 ENNReal.ofReal_ne_top, mul_comm]
  have huQ : HasUnitSpeedOn (D₂.pt ∘ (P ∘ fun t => t / k)) (Icc 0 (k * L)) :=
    hasUnitSpeedOn_rescale (F := D₂.pt ∘ P) (G := D₁.pt ∘ P) hk (fun s t => h _ _) hu
  refine (weylScaleOn_le (mul_nonneg hk.le hL) (continuousOn_of_hasUnitSpeedOn huQ) huQ
    (by simp [h0]) (by simp [hk.ne', h1]) (fun t ht => hU _
      ⟨div_nonneg ht.1 hk.le, (div_le_iff₀ hk).2 (by linarith [ht.2])⟩)).trans_eq ?_
  have himg : (fun x => k * x) '' Icc 0 L = Icc 0 (k * L) := by
    rw [image_mul_left_Icc hk.le hL, mul_zero]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc (f' := fun _ => k)
    (fun x _ => by simpa using ((hasDerivAt_id x).const_mul k).hasDerivWithinAt)
    (fun x _ y _ hxy => mul_left_cancel₀ hk.ne' hxy)]
  rw [setLIntegral_congr_fun measurableSet_Icc
    (g := fun x => ENNReal.ofReal |k| * ENNReal.ofReal (Real.exp (ξ * f (P x))))
    (fun x _ => by simp [hk.ne'])]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, abs_of_pos hk]

/-- **Scaling the metric**: `e^{ξ f}·(C D) = C (e^{ξ f}·D)` for `C > 0` (paths in `U`). -/
theorem weylScaleOn_smul (C : ℝ) (hC : 0 < C) (D : ContMetric d) :
    weylScaleOn ξ f (D.smul C hC) U z w = ENNReal.ofReal C * weylScaleOn ξ f D U z w := by
  refine le_antisymm (weylScaleOn_le_mul_of_edist hC (D.edist_smul C hC)) ?_
  have h2 : weylScaleOn ξ f D U z w ≤
      ENNReal.ofReal C⁻¹ * weylScaleOn ξ f (D.smul C hC) U z w := by
    refine weylScaleOn_le_mul_of_edist (inv_pos.2 hC) fun x y => ?_
    rw [D.edist_smul C hC, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hC).le,
      inv_mul_cancel₀ hC.ne', ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal C * weylScaleOn ξ f D U z w
      ≤ ENNReal.ofReal C * (ENNReal.ofReal C⁻¹ * weylScaleOn ξ f (D.smul C hC) U z w) := by
        gcongr
    _ = weylScaleOn ξ f (D.smul C hC) U z w := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hC.le, mul_inv_cancel₀ hC.ne', ENNReal.ofReal_one,
          one_mul]

/-- **Scaling the metric**: `e^{ξ f}·(C D) = C (e^{ξ f}·D)` for `C > 0`. -/
theorem weylScale_smul (C : ℝ) (hC : 0 < C) (D : ContMetric d) :
    weylScale ξ f (D.smul C hC) z w = ENNReal.ofReal C * weylScale ξ f D z w := by
  rw [← weylScaleOn_univ, ← weylScaleOn_univ, weylScaleOn_smul]

/-! ### Affine change of coordinates -/

/-- The affine map `x ↦ r x + a` as a continuous map. -/
def ContMetric.affineMap (r : ℝ) (a : Rd d) : C(Rd d, Rd d) := ⟨fun x => r • x + a, by fun_prop⟩

theorem ContMetric.affineMap_apply (r : ℝ) (a x : Rd d) :
    ContMetric.affineMap r a x = r • x + a := rfl

theorem ContMetric.affineMap_inv {r : ℝ} (hr : r ≠ 0) (a y : Rd d) :
    ContMetric.affineMap r a (r⁻¹ • (y - a)) = y := by
  rw [ContMetric.affineMap_apply, smul_inv_smul₀ hr, sub_add_cancel]

theorem ContMetric.affineMap_inv' {r : ℝ} (hr : r ≠ 0) (a x : Rd d) :
    r⁻¹ • (ContMetric.affineMap r a x - a) = x := by
  rw [ContMetric.affineMap_apply, add_sub_cancel_right, inv_smul_smul₀ hr]

theorem hasUnitSpeedOn_congr_edist {F : ℝ → Rd d} {D₁ D₂ : ContMetric d} {G : ℝ → Rd d} {L : ℝ}
    (h : ∀ s t, edist (D₂.pt (F s)) (D₂.pt (F t)) = edist (D₁.pt (G s)) (D₁.pt (G t)))
    (hu : HasUnitSpeedOn (D₁.pt ∘ G) (Icc 0 L)) : HasUnitSpeedOn (D₂.pt ∘ F) (Icc 0 L) :=
  fun x hx y hy => (eVariationOn_eq_mul_of_edist (F := D₂.pt ∘ F) (G := D₁.pt ∘ G) (c := 1)
    (fun s t => by rw [one_mul]; exact h s t) _).trans (by rw [one_mul]; exact hu hx hy)

/-- **Coordinate change**: with `φ x = r x + a`,
`(e^{ξ f∘φ}·D(φ·,φ·))_{φ⁻¹V}(u, v) = (e^{ξ f}·D)_V(φ u, φ v)`. -/
theorem weylScaleOn_affine {r : ℝ} (hr : r ≠ 0) (a : Rd d) (D : ContMetric d) (V : Set (Rd d))
    (u v : Rd d) :
    weylScaleOn ξ (f.comp (ContMetric.affineMap r a)) (D.affine r hr a)
        (ContMetric.affineMap r a ⁻¹' V) u v =
      weylScaleOn ξ f D V (ContMetric.affineMap r a u) (ContMetric.affineMap r a v) := by
  apply le_antisymm
  · refine le_weylScaleOn fun L Q hL _ hu h0 h1 hU => ?_
    have huP : HasUnitSpeedOn ((D.affine r hr a).pt ∘ fun t => r⁻¹ • (Q t - a)) (Icc 0 L) :=
      hasUnitSpeedOn_congr_edist (fun s t => by
        rw [ContMetric.edist_affine, ← ContMetric.affineMap_apply, ← ContMetric.affineMap_apply,
          ContMetric.affineMap_inv hr, ContMetric.affineMap_inv hr]) hu
    refine (weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn huP) huP
      (by rw [h0, ContMetric.affineMap_inv' hr]) (by rw [h1, ContMetric.affineMap_inv' hr])
      (fun t ht => by simpa [mem_preimage, ContMetric.affineMap_inv hr] using hU t ht)).trans_eq ?_
    simp only [ContinuousMap.comp_apply, ContMetric.affineMap_inv hr]
  · refine le_weylScaleOn fun L P hL _ hu h0 h1 hU => ?_
    have huQ : HasUnitSpeedOn (D.pt ∘ fun t => ContMetric.affineMap r a (P t)) (Icc 0 L) :=
      hasUnitSpeedOn_congr_edist (fun s t => (ContMetric.edist_affine hr a D _ _).symm) hu
    exact weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn huQ) huQ (by rw [h0]) (by rw [h1])
      (fun t ht => hU t ht)

/-- **Coordinate change** (`V = ℝ^d`): `(e^{ξ f∘φ}·D(φ·,φ·))(u, v) = (e^{ξ f}·D)(φ u, φ v)`. -/
theorem weylScale_affine {r : ℝ} (hr : r ≠ 0) (a : Rd d) (D : ContMetric d) (u v : Rd d) :
    weylScale ξ (f.comp (ContMetric.affineMap r a)) (D.affine r hr a) u v =
      weylScale ξ f D (ContMetric.affineMap r a u) (ContMetric.affineMap r a v) := by
  rw [← weylScaleOn_univ, ← weylScaleOn_univ, ← weylScaleOn_affine hr a D univ u v,
    preimage_univ]

/-! ### Sub-paths, concatenation, triangle inequality, symmetry -/

/-- The Weyl cost of the sub-path `P|[s, t]` bounds `(e^{ξ f}·D)_U(P s, P t)`. -/
theorem weylScaleOn_le_sub {L : ℝ} {P : ℝ → Rd d} (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    (hU : ∀ t ∈ Icc 0 L, P t ∈ U) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ L) :
    weylScaleOn ξ f D U (P s) (P t) ≤
      ∫⁻ τ in Icc s t, ENNReal.ofReal (Real.exp (ξ * f (P τ))) := by
  have hu' : HasUnitSpeedOn (D.pt ∘ (P ∘ fun τ => τ + s)) (Icc 0 (t - s)) := by
    have := hasUnitSpeedOn_comp_add s (hasUnitSpeedOn_mono_Icc hu hs ht)
    rwa [sub_self] at this
  refine (weylScaleOn_le (sub_nonneg.2 hst) (continuousOn_of_hasUnitSpeedOn hu') hu'
    (by simp) (by simp) (fun τ hτ => hU _ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩)).trans_eq ?_
  simp only [Function.comp_apply]
  rw [LQGMetric.setLIntegral_Icc_comp_add (fun τ => ENNReal.ofReal (Real.exp (ξ * f (P τ)))),
    zero_add, sub_add_cancel]

theorem weylScaleOn_self {x : Rd d} (hx : x ∈ U) : weylScaleOn ξ f D U x x = 0 := by
  have hu : HasUnitSpeedOn (D.pt ∘ fun _ : ℝ => x) (Icc 0 0) :=
    hasConstantSpeedOnWith_of_subsingleton _ (by rw [Icc_self]; exact subsingleton_singleton) 1
  refine le_antisymm ((weylScaleOn_le le_rfl (continuousOn_of_hasUnitSpeedOn hu) hu rfl rfl
    (fun _ _ => hx)).trans_eq ?_) bot_le
  simp

/-- Concatenation of two admissible paths. -/
theorem weylScaleOn_le_add_of_paths {x y z : Rd d} {L₁ L₂ : ℝ} {P Q : ℝ → Rd d} (hL₁ : 0 ≤ L₁)
    (hL₂ : 0 ≤ L₂) (hu₁ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L₁))
    (hu₂ : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L₂)) (hP0 : P 0 = x) (hP1 : P L₁ = y)
    (hQ0 : Q 0 = y) (hQ1 : Q L₂ = z) (hPU : ∀ t ∈ Icc 0 L₁, P t ∈ U)
    (hQU : ∀ t ∈ Icc 0 L₂, Q t ∈ U) :
    weylScaleOn ξ f D U x z ≤ (∫⁻ t in Icc 0 L₁, ENNReal.ofReal (Real.exp (ξ * f (P t)))) +
      ∫⁻ t in Icc 0 L₂, ENNReal.ofReal (Real.exp (ξ * f (Q t))) := by
  set R : ℝ → Rd d := fun t => if t ≤ L₁ then P t else Q (t + -L₁) with hR
  have hR1 : EqOn (D.pt ∘ R) (D.pt ∘ P) (Icc 0 L₁) := fun t ht => by
    simp only [Function.comp_apply, hR, ite_eq_left ht.2]
  have hR2 : EqOn R (Q ∘ fun t => t + -L₁) (Icc L₁ (L₁ + L₂)) := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h; simp [hR, hP1, hQ0]
    · simp [hR, not_le.2 h]
  have hu₂' : HasUnitSpeedOn (D.pt ∘ (Q ∘ fun t => t + -L₁)) (Icc L₁ (L₁ + L₂)) := by
    have := hasUnitSpeedOn_comp_add (-L₁) hu₂
    rw [zero_sub, neg_neg, sub_neg_eq_add, add_comm L₂] at this
    exact this
  have hu : HasUnitSpeedOn (D.pt ∘ R) (Icc 0 (L₁ + L₂)) :=
    HasUnitSpeedOn.Icc_Icc (hasUnitSpeedOn_congr hR1 hu₁)
      (hasUnitSpeedOn_congr (fun t ht => congrArg D.pt (hR2 ht)) hu₂')
  have hR0 : R 0 = x := by simp [hR, hL₁, hP0]
  have hRL : R (L₁ + L₂) = z := by
    rw [hR2 ⟨le_add_of_nonneg_right hL₂, le_rfl⟩]; simp [hQ1]
  have hRU : ∀ t ∈ Icc 0 (L₁ + L₂), R t ∈ U := by
    intro t ht
    by_cases h : t ≤ L₁
    · simp only [hR, ite_eq_left h]; exact hPU t ⟨ht.1, h⟩
    · simp only [hR, ite_eq_right h]
      exact hQU _ ⟨by linarith [not_le.1 h], by linarith [ht.2]⟩
  refine (weylScaleOn_le (add_nonneg hL₁ hL₂) (continuousOn_of_hasUnitSpeedOn hu) hu hR0 hRL
    hRU).trans_eq ?_
  rw [← Icc_union_Ioc_eq_Icc hL₁ (le_add_of_nonneg_right hL₂),
    lintegral_union measurableSet_Ioc
      (Set.disjoint_left.2 fun t h1 h2 => not_le.2 h2.1 h1.2)]
  congr 1
  · exact setLIntegral_congr_fun measurableSet_Icc fun t ht => by
      simp only [hR, ite_eq_left ht.2]
  · rw [setLIntegral_congr Ioc_ae_eq_Icc, setLIntegral_congr_fun measurableSet_Icc
      (g := fun t => ENNReal.ofReal (Real.exp (ξ * f (Q (t + -L₁)))))
      (fun t ht => by simp only [hR2 ht, Function.comp_apply]),
      LQGMetric.setLIntegral_Icc_comp_add (fun τ => ENNReal.ofReal (Real.exp (ξ * f (Q τ)))),
      add_neg_cancel, show L₁ + L₂ + -L₁ = L₂ by ring]

/-- **Triangle inequality** for `(e^{ξ f}·D)_U` (concatenation of paths). -/
theorem weylScaleOn_triangle (x y z : Rd d) :
    weylScaleOn ξ f D U x z ≤ weylScaleOn ξ f D U x y + weylScaleOn ξ f D U y z := by
  rw [← tsub_le_iff_right]
  refine le_weylScaleOn fun L₁ P hL₁ _ hu₁ hP0 hP1 hPU => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_weylScaleOn fun L₂ Q hL₂ _ hu₂ hQ0 hQ1 hQU => ?_
  rw [tsub_le_iff_left]
  exact weylScaleOn_le_add_of_paths hL₁ hL₂ hu₁ hu₂ hP0 hP1 hQ0 hQ1 hPU hQU

/-- Chained triangle inequality along points `q 0, …, q n`. -/
theorem weylScaleOn_le_sum (q : ℕ → Rd d) (hq : q 0 ∈ U) (n : ℕ) :
    weylScaleOn ξ f D U (q 0) (q n) ≤
      ∑ i ∈ Finset.range n, weylScaleOn ξ f D U (q i) (q (i + 1)) := by
  induction n with
  | zero => rw [weylScaleOn_self hq]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact (weylScaleOn_triangle (q 0) (q n) (q (n + 1))).trans (by gcongr)

theorem weylScaleOn_symm_le (z w : Rd d) :
    weylScaleOn ξ f D U z w ≤ weylScaleOn ξ f D U w z := by
  refine le_weylScaleOn fun L P hL _ hu h0 h1 hU => ?_
  have hu' : HasUnitSpeedOn (D.pt ∘ (P ∘ fun t => L - t)) (Icc 0 L) := by
    rw [hasUnitSpeedOn_Icc_iff] at hu ⊢
    intro s t hs hst ht
    show curveLength ((D.pt ∘ P) ∘ fun t => L - t) s t = _
    rw [curveLength_comp_of_continuousOn_antitoneOn (D.pt ∘ P) hst (by fun_prop)
      (fun x _ y _ hxy => sub_le_sub_left hxy L), hu _ _ (by linarith) (by linarith) (by linarith)]
    congr 1; ring
  refine (weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn hu') hu' (by simp [h1])
    (by simp [h0]) (fun t ht => hU _ ⟨by linarith [ht.2], by linarith [ht.1]⟩)).trans_eq ?_
  simp only [Function.comp_apply]
  exact LQGMetric.setLIntegral_Icc_comp_sub (fun τ => ENNReal.ofReal (Real.exp (ξ * f (P τ)))) L

/-- **Symmetry** of `(e^{ξ f}·D)_U` (reversal of paths). -/
theorem weylScaleOn_comm (z w : Rd d) : weylScaleOn ξ f D U z w = weylScaleOn ξ f D U w z :=
  le_antisymm (weylScaleOn_symm_le z w) (weylScaleOn_symm_le w z)

theorem weylScale_comm (z w : Rd d) : weylScale ξ f D z w = weylScale ξ f D w z := by
  rw [← weylScaleOn_univ, weylScaleOn_comm, weylScaleOn_univ]

theorem weylScale_self (z : Rd d) : weylScale ξ f D z z = 0 := by
  rw [← weylScaleOn_univ]; exact weylScaleOn_self (mem_univ z)

theorem weylScale_triangle (x y z : Rd d) :
    weylScale ξ f D x z ≤ weylScale ξ f D x y + weylScale ξ f D y z := by
  simp only [← weylScaleOn_univ]; exact weylScaleOn_triangle x y z

end HigherDimLQGMetric
