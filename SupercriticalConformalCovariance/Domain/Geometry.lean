import SupercriticalConformalCovariance.Domain.Exhaust
import SupercriticalConformalCovariance.Domain.Chain

/-!
# Deterministic geometry of the domain Weyl metric

Fix one sample: an LSC metric `D₀` (in applications `D_{h₀}`) whose
identity `(ℂ, D₀) → ℂ` is continuous, a set `V ⊆ ℂ` and `f ∈ C(V)`. On the carrier `(ℂ, D₀)` the
domain metric `weylScaleOn ξ f D₀` is the weighted path distance `dV = (w_f · D₀)_V` of
`HigherDimLQGMetric` (`weylScaleOn_eq_dV`), with weight `w_f = e^{ξ f}` on `V`. Consequences:

* `curveLengthWith_dV` (**Weyl length formula on the domain**): for a `D₀`-continuous curve in an
  open `V`, `len(P; d_f) = ∫_P e^{ξ f} ds_{D₀}`;
* `internalWith_dV` (**length space**): `d_f` is the length metric it induces on `V`;
* `weylScaleOn_resC_eq_internalWith` (**restriction**): for any `W ⊆ V` (open, closed, compact…),
  `d_{f|W}(·, ·; W)` is the internal metric of `d_f` on `W`;
* `weylScaleOn_add_eq_weylDistOnWith` (**domain Weyl scaling, simultaneous in `g`**):
  `d_{f+g} = (e^{ξ g} · d_f)_V`, for every `g ∈ C(V)` (open `V`);
* `weylScaleOn_add_le`, `le_weylScaleOn_add` (**Weyl bounds**): `m ≤ g ≤ M` gives
  `e^{ξm} d_f ≤ d_{f+g} ≤ e^{ξM} d_f` (`ξ ≥ 0`, no hypothesis on `D₀`);
* `weylScaleOn_self`, `weylScaleOn_comm`, `weylScaleOn_triangle`, `eq_of_weylScaleOn_eq_zero`:
  `d_f` is an extended metric on `V` (open `V`);
* `weylScaleOn_eq_internal_of_extension` (**consistency with the whole-plane metric**): if
  `F ∈ C(ℂ)` extends `f ∈ C(K)` (any `K`) and `E = e^{ξ F} · D₀`, then `d_f = E(·, ·; K)`
  (`D₀` a length space).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open SupercriticalLQGUniqueness (LSCMetric weylScale)
open SupercriticalConformalCovariance (weylScaleOn)
open HigherDimLQGMetric

/-- `V` as a subset of the carrier `(ℂ, D₀)`. -/
def SV (D₀ : LSCMetric) (V : Set ℂ) : Set D₀.Space := forget D₀ ⁻¹' V

open Classical in
/-- The weight `e^{ξ f}` on `V` (junk `1` off `V`). -/
def wV (D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (f : C(V, ℝ)) : D₀.Space → ℝ := fun z =>
  if h : forget D₀ z ∈ V then Real.exp (ξ * f ⟨forget D₀ z, h⟩) else 1

/-- The restriction of `f ∈ C(V)` to `W ⊆ V`. -/
def resC {W V : Set ℂ} (hWV : W ⊆ V) (f : C(V, ℝ)) : C(W, ℝ) :=
  f.comp ⟨Set.inclusion hWV, continuous_inclusion hWV⟩

variable {D₀ : LSCMetric} {ξ : ℝ} {V : Set ℂ}

theorem wV_of_mem (f : C(V, ℝ)) {z : D₀.Space} (hz : forget D₀ z ∈ V) :
    wV D₀ ξ f z = Real.exp (ξ * f ⟨forget D₀ z, hz⟩) := dif_pos hz

theorem wV_pos (f : C(V, ℝ)) (z : D₀.Space) : 0 < wV D₀ ξ f z := by
  unfold wV; split_ifs <;> positivity

theorem continuousOn_wV (hforget : Continuous (forget D₀)) (f : C(V, ℝ)) :
    ContinuousOn (wV D₀ ξ f) (SV D₀ V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (SV D₀ V).domRestrict (wV D₀ ξ f) =
      fun z : SV D₀ V => Real.exp (ξ * f ⟨forget D₀ z.1, z.2⟩) := by
    funext z; exact wV_of_mem f z.2
  rw [he]
  exact Real.continuous_exp.comp (continuous_const.mul (f.continuous.comp
    ((hforget.comp continuous_subtype_val).subtype_mk _)))

theorem isOpen_SV (hforget : Continuous (forget D₀)) (hV : IsOpen V) : IsOpen (SV D₀ V) :=
  hV.preimage hforget

/-- The domain metric on the carrier `(ℂ, D₀)`: `(e^{ξ f} · D₀)_V`. -/
def dV (D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (f : C(V, ℝ)) : D₀.Space → D₀.Space → ℝ≥0∞ :=
  weylDistOn (wV D₀ ξ f) (SV D₀ V)

/-- **The domain metric is the weighted path distance** `(e^{ξ f}·D₀)_V` of `HigherDimLQGMetric`. -/
theorem weylScaleOn_eq_dV (hforget : Continuous (forget D₀)) (f : C(V, ℝ)) (p : V × V) :
    weylScaleOn ξ f D₀ p = dV D₀ ξ f (D₀.pt p.1) (D₀.pt p.2) := by
  rw [dV, weylDistOn_eq_iInf_unitSpeed (continuousOn_wV hforget f) (fun z _ => wV_pos f z)]
  apply le_antisymm
  · refine le_iInf fun L => le_iInf fun Q => le_iInf fun hL0 => le_iInf fun hcQ =>
      le_iInf fun huQ => le_iInf fun hQ0 => le_iInf fun hQ1 => le_iInf fun hQS => ?_
    classical
    let P' : ℝ → V := fun t => if h : forget D₀ (Q t) ∈ V then ⟨forget D₀ (Q t), h⟩ else p.1
    have hP'eq : EqOn (fun t => (P' t : ℂ)) (fun t => forget D₀ (Q t)) (Icc 0 L) := by
      intro t ht
      have h : forget D₀ (Q t) ∈ V := hQS t ht
      simp only [P', h, dite_true]
    have hP'Q : EqOn (D₀.pt ∘ fun t => (P' t : ℂ)) Q (Icc 0 L) := fun t ht => hP'eq ht
    have hc' : D₀.IsCurve (fun t => (P' t : ℂ)) 0 L := ⟨hL0, hcQ.congr hP'Q⟩
    have hu' : HasUnitSpeedOn (D₀.pt ∘ fun t => (P' t : ℂ)) (Icc 0 L) :=
      hasUnitSpeedOn_congr (fun t ht => (hP'Q ht).symm) huQ
    have h0 : P' 0 = p.1 := by
      apply Subtype.ext
      calc (P' 0 : ℂ) = forget D₀ (Q 0) := hP'eq (left_mem_Icc.2 hL0)
        _ = p.1 := congrArg (forget D₀) hQ0
    have h1 : P' L = p.2 := by
      apply Subtype.ext
      calc (P' L : ℂ) = forget D₀ (Q L) := hP'eq (right_mem_Icc.2 hL0)
        _ = p.2 := congrArg (forget D₀) hQ1
    unfold weylScaleOn
    refine iInf_le_of_le P' <| iInf_le_of_le L <| iInf_le_of_le hc' <| iInf_le_of_le hu' <|
      iInf_le_of_le h0 <| iInf_le_of_le h1 (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have hV : forget D₀ (Q t) ∈ V := hQS t ht
    have hP't : P' t = ⟨forget D₀ (Q t), hV⟩ := by simp only [P', hV, dite_true]
    rw [wV_of_mem f hV, hP't]
  · unfold weylScaleOn
    refine le_iInf fun P => le_iInf fun L => le_iInf fun hc => le_iInf fun hu =>
      le_iInf fun h0 => le_iInf fun h1 => ?_
    refine iInf_le_of_le L <| iInf_le_of_le (D₀.pt ∘ fun t => (P t : ℂ)) <|
      iInf_le_of_le hc.1 <| iInf_le_of_le hc.2 <| iInf_le_of_le hu <|
      iInf_le_of_le (by simp [h0]) <| iInf_le_of_le (by simp [h1]) <|
      iInf_le_of_le (fun t _ => (P t).2) (le_of_eq ?_)
    refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    show ENNReal.ofReal (wV D₀ ξ f (P t : ℂ)) = _
    rw [wV_of_mem f (P t).2]
    rfl

/-- **Weyl length formula on the domain.** -/
theorem curveLengthWith_dV (hforget : Continuous (forget D₀)) (hV : IsOpen V) (f : C(V, ℝ))
    {P : ℝ → D₀.Space} {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    (hPS : MapsTo P (Icc a b) (SV D₀ V)) :
    curveLengthWith (dV D₀ ξ f) P a b = weightedLength (wV D₀ ξ f) P a b :=
  curveLengthWith_weylDistOn (isOpen_SV hforget hV) (continuousOn_wV hforget f) hP hPS

/-- **Length space.** The domain metric is the length metric it induces on `V`. -/
theorem internalWith_dV (hforget : Continuous (forget D₀)) (hV : IsOpen V) (f : C(V, ℝ))
    (x y : D₀.Space) : internalWith (dV D₀ ξ f) (SV D₀ V) x y = dV D₀ ξ f x y :=
  weylDistOn_isLength (isOpen_SV hforget hV) (continuousOn_wV hforget f) x y

/-- **Restriction.** For `W ⊆ V` (any subset), the domain metric of `f|_W` on `W` is the internal
metric on `W` of the domain metric of `f` on `V`. -/
theorem weylScaleOn_resC_eq_internalWith (hforget : Continuous (forget D₀)) (hV : IsOpen V)
    {W : Set ℂ} (hWV : W ⊆ V) (f : C(V, ℝ)) (p : W × W) :
    weylScaleOn ξ (resC hWV f) D₀ p =
      internalWith (dV D₀ ξ f) (SV D₀ W) (D₀.pt p.1) (D₀.pt p.2) := by
  rw [weylScaleOn_eq_dV hforget]
  unfold dV
  rw [weylDistOn_internal (isOpen_SV hforget hV) (continuousOn_wV hforget f)
    (show SV D₀ W ⊆ SV D₀ V from preimage_mono hWV)]
  refine weylDistOn_congr_weight fun z hz => ?_
  have hz' : forget D₀ z ∈ W := hz
  rw [wV_of_mem _ hz', wV_of_mem f (hWV hz')]
  rfl

/-- **Domain Weyl scaling**, simultaneously for every `g ∈ C(V)`:
`d_{f + g} = (e^{ξ g} · d_f)_V`. -/
theorem weylScaleOn_add_eq_weylDistOnWith (hforget : Continuous (forget D₀)) (hV : IsOpen V)
    (f g : C(V, ℝ)) (p : V × V) :
    weylScaleOn ξ (f + g) D₀ p =
      weylDistOnWith (dV D₀ ξ f) (wV D₀ ξ g) (SV D₀ V) (D₀.pt p.1) (D₀.pt p.2) := by
  rw [weylScaleOn_eq_dV hforget]
  unfold dV
  rw [weylDistOnWith_weylDistOn_eq (isOpen_SV hforget hV)
    (continuousOn_wV hforget f) (fun z _ => (wV_pos f z).le) (continuousOn_wV hforget g)
    (fun z _ => wV_pos g z)]
  refine weylDistOn_congr_weight fun z hz => ?_
  have hz' : forget D₀ z ∈ V := hz
  rw [wV_of_mem _ hz', wV_of_mem f hz', wV_of_mem g hz', ← Real.exp_add, ContinuousMap.add_apply,
    mul_add]

/-- **Weyl bounds**, upper half: `g ≤ M` gives `d_{f+g} ≤ e^{ξ M} d_f` (`ξ ≥ 0`). -/
theorem weylScaleOn_add_le (hξ : 0 ≤ ξ) (f g : C(V, ℝ)) {M : ℝ} (hM : ∀ z, g z ≤ M)
    (p : V × V) :
    weylScaleOn ξ (f + g) D₀ p ≤ ENNReal.ofReal (Real.exp (ξ * M)) * weylScaleOn ξ f D₀ p := by
  have h0 : ENNReal.ofReal (Real.exp (ξ * M)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold weylScaleOn
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => iInf_mono fun L => iInf_mono fun _ => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono fun _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [ContinuousMap.add_apply, mul_add, add_comm]
  linarith [mul_le_mul_of_nonneg_left (hM (P t)) hξ]

/-- **Weyl bounds**, lower half: `m ≤ g` gives `e^{ξ m} d_f ≤ d_{f+g}` (`ξ ≥ 0`). -/
theorem le_weylScaleOn_add (hξ : 0 ≤ ξ) (f g : C(V, ℝ)) {m : ℝ} (hm : ∀ z, m ≤ g z)
    (p : V × V) :
    ENNReal.ofReal (Real.exp (ξ * m)) * weylScaleOn ξ f D₀ p ≤ weylScaleOn ξ (f + g) D₀ p := by
  have h0 : ENNReal.ofReal (Real.exp (ξ * m)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold weylScaleOn
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_mono fun P => iInf_mono fun L => iInf_mono fun _ => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono fun _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [ContinuousMap.add_apply, mul_add, add_comm]
  linarith [mul_le_mul_of_nonneg_left (hm (P t)) hξ]

/-! ## The domain metric is an extended metric on `V` -/

theorem weylScaleOn_self (hforget : Continuous (forget D₀)) (f : C(V, ℝ)) (x : V) :
    weylScaleOn ξ f D₀ (x, x) = 0 := by
  rw [weylScaleOn_eq_dV hforget]
  exact weylDistOn_self (show D₀.pt (x : ℂ) ∈ SV D₀ V from x.2)

theorem weylScaleOn_comm (hforget : Continuous (forget D₀)) (f : C(V, ℝ)) (x y : V) :
    weylScaleOn ξ f D₀ (x, y) = weylScaleOn ξ f D₀ (y, x) := by
  rw [weylScaleOn_eq_dV hforget, weylScaleOn_eq_dV hforget]
  exact weylDistOn_comm _ _

theorem weylScaleOn_triangle (hforget : Continuous (forget D₀)) (f : C(V, ℝ)) (x y z : V) :
    weylScaleOn ξ f D₀ (x, z) ≤ weylScaleOn ξ f D₀ (x, y) + weylScaleOn ξ f D₀ (y, z) := by
  rw [weylScaleOn_eq_dV hforget, weylScaleOn_eq_dV hforget, weylScaleOn_eq_dV hforget]
  exact weylDistOn_triangle _ _ _

theorem eq_of_weylScaleOn_eq_zero (hforget : Continuous (forget D₀)) (hV : IsOpen V)
    (f : C(V, ℝ)) {x y : V} (h : weylScaleOn ξ f D₀ (x, y) = 0) : x = y := by
  rw [weylScaleOn_eq_dV hforget] at h
  have hx : D₀.pt (x : ℂ) ∈ SV D₀ V := x.2
  have hc : ContinuousAt (wV D₀ ξ f) (D₀.pt (x : ℂ)) :=
    (continuousOn_wV hforget f).continuousAt ((isOpen_SV hforget hV).mem_nhds hx)
  have hz := edist_eq_zero_of_weylDistOn_eq_zero hc (wV_pos f _) h
  exact Subtype.ext (D₀.isExtMetric.2.1 _ _ hz)

/-! ## Consistency with the whole-plane metric -/

/-- **Consistency.** If `F ∈ C(ℂ)` extends `f ∈ C(K)` and `E = e^{ξ F} · D₀`, the domain metric of
`f` on `K` is the internal metric of `E` on `K` (any `K ⊆ ℂ`; `D₀` a length space). -/
theorem weylScaleOn_eq_internal_of_extension (hξ : 0 ≤ ξ) (hforget : Continuous (forget D₀))
    (hL : D₀.IsLengthSpace) {K : Set ℂ} (f : C(K, ℝ)) (F : C(ℂ, ℝ))
    (hFf : ∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) (E : LSCMetric)
    (hE : ∀ q, E q = weylScale ξ F D₀ q) (p : K × K) :
    weylScaleOn ξ f D₀ p = E.internal K p := by
  rw [weylScaleOn_eq_iInf_internal D₀ ξ hξ hforget hL f (fun _ => K) (fun _ => subset_rfl)
    (fun _ _ h => ⟨0, h⟩) (fun _ => F) (fun _ z hz => hFf z hz) (fun _ => E) (fun _ => hE) p]
  simp only [Subtype.coe_prop, iInf_pos, Subtype.coe_eta, iInf_const]

end SupercriticalConformalCovariance.Domain
