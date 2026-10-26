import SupercriticalConformalCovariance.Domain.Forward
import SupercriticalConformalCovariance.Frozen.WeylScaleOn
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylBridge

/-!
# The domain Weyl metric as an exhaustion infimum of whole-plane internal metrics

Deterministic core of realization independence (GMU Remark 1.5's
bump-function argument, GM 1905.00384v2 l. 310–321), for one sample.

Let `D₀` be a lower semicontinuous metric with continuous identity `(ℂ, D₀) → ℂ` that is a length
space, `V ⊆ ℂ`, `f ∈ C(V)` (possibly unbounded near `∂V`), and `W n ⊆ V` a family such that every
Euclidean-compact subset of `V` lies in some `W n`. Let `F n ∈ C(ℂ)` (not necessarily bounded) with `F n = f` on
`W n`, and `E n` the LSC metric `e^{ξ F n} · D₀` (`weylScale`). Then for `x, y ∈ V`

  `(e^{ξ f} · D₀)(x, y; V) = inf_n E n (x, y; W n)`   (`weylScaleOn_eq_iInf_internal`),

the infimum over the `n` with `x, y ∈ W n`. Ingredients: Euclidean compactness of `D₀`-curves; the
Weyl length formula `len(P; e^{ξF}·D₀) = ∫_P e^{ξF} ds_{D₀}` (sealed
`Toolkit.WeylLength.weylCurveLength_eq_weightedLength`); the unit-speed form of the weighted distance
(`HigherDimLQGMetric.weylDistOn_eq_iInf_unitSpeed`); curve transfer between `D₀` and `E n`
(`isCurve_weyl_forward`, `curve_back_all_continuous`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open SupercriticalLQGUniqueness (LSCMetric weylScale)
open SupercriticalConformalCovariance (weylScaleOn)

/-- The Weyl weight `z ↦ e^{ξ F(z)}` on `(ℂ, D)`. -/
def wt (D : LSCMetric) (ξ : ℝ) (F : C(ℂ, ℝ)) : D.Space → ℝ := fun z => Real.exp (ξ * F (forget D z))

theorem continuous_wt (D : LSCMetric) (ξ : ℝ) (F : C(ℂ, ℝ)) (hforget : Continuous (forget D)) :
    Continuous (wt D ξ F) :=
  Real.continuous_exp.comp (continuous_const.mul (F.continuous.comp hforget))

/-- Every `D`-curve is Euclidean-continuous when `(ℂ, D) → ℂ` is continuous. -/
theorem continuousOn_of_isCurve {D : LSCMetric} (hforget : Continuous (forget D)) {P : ℝ → ℂ}
    {a b : ℝ} (hP : D.IsCurve P a b) : ContinuousOn P (Icc a b) :=
  hforget.comp_continuousOn hP.2

/-- **Weyl length formula** for an LSC metric `E` equal to `e^{ξ F} · D`: the `E`-length of a
`D`-curve is its `e^{ξ F}`-weighted `D`-length. -/
theorem len_eq_weightedLength {D E : LSCMetric} {ξ : ℝ} {F : C(ℂ, ℝ)}
    (hforget : Continuous (forget D)) (hE : ∀ q : ℂ × ℂ, E q = weylScale ξ F D q)
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    E.len P a b = HigherDimLQGMetric.weightedLength (wt D ξ F) (D.pt ∘ P) a b := by
  have h1 : E.len P a b =
      HigherDimLQGMetric.curveLengthWith (fun x y : D.Space => E (x, y)) (D.pt ∘ P) a b := by
    rw [E.len_eq_curveLength]
    exact (HigherDimLQGMetric.curveLengthWith_edist (E.pt ∘ P) a b).symm
  have h2 : (fun x y : D.Space => E (x, y)) =
      (fun x y : D.Space => weylScale ξ F D (forget D x, forget D y)) := by
    funext x y
    exact hE (x, y)
  rw [h1, h2]
  exact SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.weylCurveLength_eq_weightedLength
    D ξ F hforget hP

/-- Unit speed only depends on the values on the set. -/
theorem hasUnitSpeedOn_congr {α : Type*} [PseudoEMetricSpace α] {f g : ℝ → α} {s : Set ℝ}
    (hfg : EqOn f g s) (hf : HasUnitSpeedOn f s) : HasUnitSpeedOn g s := by
  intro x hx y hy
  rw [← eVariationOn.eq_of_eqOn (hfg.mono inter_subset_left)]
  exact hf hx hy

/-- **Exhaustion formula** (deterministic): the domain Weyl metric is the infimum over an exhaustion
of the internal metrics of whole-plane Weyl metrics with continuous weights extending `f`. -/
theorem weylScaleOn_eq_iInf_internal (D₀ : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (hforget : Continuous (forget D₀)) (hL : D₀.IsLengthSpace)
    {V : Set ℂ} (f : C(V, ℝ)) (W : ℕ → Set ℂ) (hWV : ∀ n, W n ⊆ V)
    (hcover : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ n, K ⊆ W n)
    (F : ℕ → C(ℂ, ℝ)) (hFf : ∀ n z (hz : z ∈ W n), F n z = f ⟨z, hWV n hz⟩)
    (E : ℕ → LSCMetric) (hE : ∀ n q, E n q = weylScale ξ (F n) D₀ q) (p : V × V) :
    weylScaleOn ξ f D₀ p = ⨅ (n : ℕ) (hx : (p.1 : ℂ) ∈ W n) (hy : (p.2 : ℂ) ∈ W n),
      (E n).internal (W n) (⟨p.1, hx⟩, ⟨p.2, hy⟩) := by
  apply le_antisymm
  · -- `≤`: every internal competitor of `E n` in `W n` gives a domain Weyl competitor
    refine le_iInf fun n => le_iInf fun hx => le_iInf fun hy => ?_
    unfold LSCMetric.internal
    refine le_iInf fun γ => le_iInf fun a => le_iInf fun b => le_iInf fun hcE =>
      le_iInf fun hγW => le_iInf fun ha => le_iInf fun hb => ?_
    have hcD : D₀.IsCurve γ a b :=
      SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.curve_back_all_continuous D₀ (E n)
        ξ hξ (F n) hforget (hE n) hcE
    rw [len_eq_weightedLength hforget (hE n) hcD]
    set S : Set D₀.Space := {z | forget D₀ z ∈ W n} with hS
    have hmaps : MapsTo (D₀.pt ∘ γ) (Icc a b) S := fun t ht => hγW t ht
    refine le_trans ?_ (HigherDimLQGMetric.weylDistOn_le_of_curve hcD.1 hcD.2 hmaps)
    rw [HigherDimLQGMetric.weylDistOn_eq_iInf_unitSpeed
      (continuous_wt D₀ ξ (F n) hforget).continuousOn (fun z _ => Real.exp_pos _)]
    refine le_iInf fun L => le_iInf fun Q => le_iInf fun hL0 => le_iInf fun hcQ =>
      le_iInf fun huQ => le_iInf fun hQ0 => le_iInf fun hQ1 => le_iInf fun hQS => ?_
    classical
    -- the `V`-valued version of `Q`
    let P' : ℝ → V := fun t => if h : forget D₀ (Q t) ∈ V then ⟨forget D₀ (Q t), h⟩ else p.1
    have hP'eq : EqOn (fun t => (P' t : ℂ)) (fun t => forget D₀ (Q t)) (Icc 0 L) := by
      intro t ht
      have h : forget D₀ (Q t) ∈ V := hWV n (hQS t ht)
      simp only [P', h, dite_true]
    have hP'Q : EqOn (D₀.pt ∘ fun t => (P' t : ℂ)) Q (Icc 0 L) := fun t ht => hP'eq ht
    have hc' : D₀.IsCurve (fun t => (P' t : ℂ)) 0 L := ⟨hL0, hcQ.congr hP'Q⟩
    have hu' : HasUnitSpeedOn (D₀.pt ∘ fun t => (P' t : ℂ)) (Icc 0 L) :=
      hasUnitSpeedOn_congr (fun t ht => (hP'Q ht).symm) huQ
    have h0 : P' 0 = p.1 := by
      apply Subtype.ext
      calc (P' 0 : ℂ) = forget D₀ (Q 0) := hP'eq (left_mem_Icc.2 hL0)
        _ = γ a := congrArg (forget D₀) hQ0
        _ = p.1 := ha
    have h1 : P' L = p.2 := by
      apply Subtype.ext
      calc (P' L : ℂ) = forget D₀ (Q L) := hP'eq (right_mem_Icc.2 hL0)
        _ = γ b := congrArg (forget D₀) hQ1
        _ = p.2 := hb
    unfold weylScaleOn
    refine iInf_le_of_le P' <| iInf_le_of_le L <| iInf_le_of_le hc' <| iInf_le_of_le hu' <|
      iInf_le_of_le h0 <| iInf_le_of_le h1 (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have hW : forget D₀ (Q t) ∈ W n := hQS t ht
    have hV : forget D₀ (Q t) ∈ V := hWV n hW
    have hP't : P' t = ⟨forget D₀ (Q t), hV⟩ := by simp only [P', hV, dite_true]
    show ENNReal.ofReal (Real.exp (ξ * f (P' t))) =
      ENNReal.ofReal (Real.exp (ξ * F n (forget D₀ (Q t))))
    rw [hP't, hFf n _ hW]
  · -- `≥`: every domain Weyl competitor lies in some `W n`
    unfold weylScaleOn
    refine le_iInf fun P => le_iInf fun L => le_iInf fun hc => le_iInf fun hu =>
      le_iInf fun h0 => le_iInf fun h1 => ?_
    set γ : ℝ → ℂ := fun t => (P t : ℂ) with hγ
    have hcE : ContinuousOn γ (Icc 0 L) := continuousOn_of_isCurve hforget hc
    have hK : IsCompact (γ '' Icc 0 L) := isCompact_Icc.image_of_continuousOn hcE
    have hKV : γ '' Icc 0 L ⊆ V := by
      rintro _ ⟨t, -, rfl⟩
      exact (P t).2
    obtain ⟨n, hn⟩ := hcover _ hK hKV
    have hγW : ∀ t ∈ Icc 0 L, γ t ∈ W n := fun t ht => hn ⟨t, ht, rfl⟩
    have hx : (p.1 : ℂ) ∈ W n := by
      have := hγW 0 (left_mem_Icc.2 hc.1)
      simpa [hγ, h0] using this
    have hy : (p.2 : ℂ) ∈ W n := by
      have := hγW L (right_mem_Icc.2 hc.1)
      simpa [hγ, h1] using this
    refine iInf_le_of_le n <| iInf_le_of_le hx <| iInf_le_of_le hy ?_
    have hcEn : (E n).IsCurve γ 0 L := isCurve_weyl_forward hξ hforget hL (hE n) hc
    have hint : (E n).internal (W n) (⟨p.1, hx⟩, ⟨p.2, hy⟩) ≤ (E n).len γ 0 L := by
      unfold LSCMetric.internal
      exact iInf_le_of_le γ <| iInf_le_of_le 0 <| iInf_le_of_le L <| iInf_le_of_le hcEn <|
        iInf_le_of_le hγW <| iInf_le_of_le (by simp [hγ, h0]) <|
        iInf_le_of_le (by simp [hγ, h1]) le_rfl
    refine hint.trans (le_of_eq ?_)
    rw [len_eq_weightedLength hforget (hE n) hc,
      HigherDimLQGMetric.weightedLength_of_hasUnitSpeedOn hc.1 hu
        ((continuous_wt D₀ ξ (F n) hforget).comp_continuousOn hc.2)]
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    show ENNReal.ofReal (Real.exp (ξ * F n (γ t))) = ENNReal.ofReal (Real.exp (ξ * f (P t)))
    rw [hFf n _ (hγW t ht)]

end SupercriticalConformalCovariance.Domain
