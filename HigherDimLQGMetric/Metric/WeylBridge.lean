import HigherDimLQGMetric.Metric.WeylMetric
import HigherDimLQGMetric.Metric.Reparam

/-!
# Weyl scaling on `ℝ^d` as a weighted distance: bridge, length identity, comparison

Packet M1 (Phase A, block A2). Connects the frozen `weylScale` (Axiom (III), [S] l. 69–74: paths
parametrized by `D`-length) with the generic weighted distance `weylDistOn` of Lemma 2.1, and
derives the Weyl-scaling API on `ℝ^d`.

* **Bridge** (`weylScaleOn_eq_weylDistOn`, curve form `weylScaleOn_eq_iInf_curve`):
  `(e^{ξ f}·D)_U = (w·D)_{D.pt '' U}` for `w = e^{ξ f}` (`ContMetric.weylWeight`) on `(ℝ^d, D)`;
  equivalently the infimum over Euclidean-continuous curves `P : [0, 1] → U` of `∫_P e^{ξ f} ds_D`.
* **[S] Lemma 2.1(c) for Axiom (III)** (`curveLength_eq_weightedLength_of_weyl`): if
  `D' = e^{ξ g}·D` then `len(P; D') = ∫_P e^{ξ g} ds_D` for every continuous curve, and the two
  metrics have the same rectifiable curves (`curveLength_weyl_ne_top_iff`).
* **Comparison** ([S] Lemma 2.1(d) on `ℝ^d`): `c D ≤ E ≤ C D` passes to curve lengths, internal
  metrics and Weyl scalings (`ContMetric.len_le_mul_of_le`, `ContMetric.internal_le_mul_of_le`,
  `weylScaleOn_le_mul_of_le`, and the lower bounds).

Constants, composition and continuity in the weight are in `HigherDimLQGMetric.Metric.WeylCompose`.
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

/-! ### The weight `e^{ξ f}` on `(ℝ^d, D)` and the bridge -/

/-- The weight `e^{ξ f}` on `(ℝ^d, D)`. -/
def ContMetric.weylWeight (D : ContMetric d) (ξ : ℝ) (f : C(Rd d, ℝ)) : D.Space → ℝ :=
  fun x => Real.exp (ξ * f (D.unpt x))

theorem ContMetric.weylWeight_pt (D : ContMetric d) (ξ : ℝ) (f : C(Rd d, ℝ)) (z : Rd d) :
    D.weylWeight ξ f (D.pt z) = Real.exp (ξ * f z) := rfl

theorem ContMetric.continuous_weylWeight (D : ContMetric d) (ξ : ℝ) (f : C(Rd d, ℝ)) :
    Continuous (D.weylWeight ξ f) :=
  Real.continuous_exp.comp (continuous_const.mul (f.continuous.comp D.continuous_unpt))

theorem ContMetric.weylWeight_pos (D : ContMetric d) (ξ : ℝ) (f : C(Rd d, ℝ)) (x : D.Space) :
    0 < D.weylWeight ξ f x :=
  Real.exp_pos _

theorem ContMetric.image_pt_univ (D : ContMetric d) : D.pt '' univ = univ :=
  image_univ_of_surjective fun x => ⟨D.unpt x, rfl⟩

/-- **Bridge**: the frozen Weyl scaling with paths in `U` is the weighted distance of
[S] Lemma 2.1 on `(ℝ^d, D)` with the weight `e^{ξ f}`. -/
theorem weylScaleOn_eq_weylDistOn (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (U : Set (Rd d))
    (z w : Rd d) :
    weylScaleOn ξ f D U z w = weylDistOn (D.weylWeight ξ f) (D.pt '' U) (D.pt z) (D.pt w) := by
  rw [weylDistOn_eq_iInf_unitSpeed (D.continuous_weylWeight ξ f).continuousOn
    (fun x _ => D.weylWeight_pos ξ f x)]
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro L P hL hc hu h0 h1 hS
    refine (weylScaleOn_le (P := D.unpt ∘ P) hL hc hu (by simp [h0]) (by simp [h1])
      fun t ht => ?_).trans_eq rfl
    obtain ⟨x, hx, hxt⟩ := hS t ht
    show D.unpt (P t) ∈ U
    rw [← hxt]
    exact hx
  · refine le_weylScaleOn fun L P hL hc hu h0 h1 hU => ?_
    exact iInf_le_of_le L <| iInf_le_of_le (D.pt ∘ P) <| iInf_le_of_le hL <| iInf_le_of_le hc <|
      iInf_le_of_le hu <| iInf_le_of_le (by simp [h0]) <| iInf_le_of_le (by simp [h1]) <|
      iInf_le_of_le (fun t ht => ⟨P t, hU t ht, rfl⟩) le_rfl

theorem weylScale_eq_weylDistOn (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (z w : Rd d) :
    weylScale ξ f D z w = weylDistOn (D.weylWeight ξ f) univ (D.pt z) (D.pt w) := by
  rw [← weylScaleOn_univ, weylScaleOn_eq_weylDistOn, D.image_pt_univ]

/-- **Curve form** of `(e^{ξ f}·D)_U`: the infimum over Euclidean-continuous curves
`P : [0, 1] → U` from `z` to `w` of the weighted length `∫_P e^{ξ f} ds_D`. -/
theorem weylScaleOn_eq_iInf_curve (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (U : Set (Rd d))
    (z w : Rd d) :
    weylScaleOn ξ f D U z w = ⨅ (P : ℝ → Rd d) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = z)
      (_ : P 1 = w) (_ : MapsTo P (Icc 0 1) U), weightedLength (D.weylWeight ξ f) (D.pt ∘ P) 0 1 := by
  rw [weylScaleOn_eq_weylDistOn]
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro P hc h0 h1 hU
    exact weylDistOn_le (D.continuous_pt.comp_continuousOn hc) (by simp [h0]) (by simp [h1])
      fun t ht => ⟨P t, hU ht, rfl⟩
  · refine le_weylDistOn fun Q hc h0 h1 hS => ?_
    refine iInf_le_of_le (D.unpt ∘ Q) <| iInf_le_of_le (D.continuous_unpt.comp_continuousOn hc) <|
      iInf_le_of_le (by simp [h0]) <| iInf_le_of_le (by simp [h1]) <|
      iInf_le_of_le (fun t ht => ?_) le_rfl
    obtain ⟨x, hx, hxt⟩ := hS ht
    show D.unpt (Q t) ∈ U
    rw [← hxt]
    exact hx

/-- Every Euclidean-continuous curve in `U` bounds the Weyl distance by its weighted length. -/
theorem weylScaleOn_le_curve {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d} {U : Set (Rd d)}
    {z w : Rd d} {P : ℝ → Rd d} (hc : ContinuousOn P (Icc 0 1)) (h0 : P 0 = z) (h1 : P 1 = w)
    (hU : MapsTo P (Icc 0 1) U) :
    weylScaleOn ξ f D U z w ≤ weightedLength (D.weylWeight ξ f) (D.pt ∘ P) 0 1 := by
  rw [weylScaleOn_eq_iInf_curve]
  exact iInf_le_of_le P <| iInf_le_of_le hc <| iInf_le_of_le h0 <| iInf_le_of_le h1 <|
    iInf_le_of_le hU le_rfl

theorem weylScale_eq_iInf_curve (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (z w : Rd d) :
    weylScale ξ f D z w = ⨅ (P : ℝ → Rd d) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = z)
      (_ : P 1 = w) (_ : MapsTo P (Icc 0 1) univ),
        weightedLength (D.weylWeight ξ f) (D.pt ∘ P) 0 1 := by
  rw [← weylScaleOn_univ, weylScaleOn_eq_iInf_curve]

/-- [S] Lemma 2.1, "(w·D)(x, y; U) = inf_{P ⊂ U} ∫_P w ds_D": for a length metric `D` and an open
`U`, the internal metric of the continuous metric `e^{ξ f}·D` on `U` is the weighted distance of
Lemma 2.1 with paths in `U`. -/
theorem weylMetric_internal_eq_weylDistOn {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d}
    (hD : D.IsLength) {U : Set (Rd d)} (hU : IsOpen U) (z w : Rd d) :
    (weylMetric ξ f D hD).internal U z w =
      weylDistOn (D.weylWeight ξ f) (D.pt '' U) (D.pt z) (D.pt w) := by
  rw [weylMetric_internal hD hU, weylScaleOn_eq_weylDistOn]

/-! ### [S] Lemma 2.1(c) for Axiom (III): lengths for `e^{ξ g}·D` -/

section LengthIdentity

variable {ξ : ℝ} {g : C(Rd d, ℝ)} {D D' : ContMetric d}

/-- **[S] Lemma 2.1(c), Axiom (III) setting**: if `D' = e^{ξ g}·D`, then for every
Euclidean-continuous curve, `len(P; D') = ∫_P e^{ξ g} ds_D` in `[0, ∞]`. -/
theorem curveLength_eq_weightedLength_of_weyl
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ g D x y) {P : ℝ → Rd d}
    {a b : ℝ} (hP : ContinuousOn P (Icc a b)) :
    curveLength (D'.pt ∘ P) a b = weightedLength (D.weylWeight ξ g) (D.pt ∘ P) a b := by
  have hedist : ∀ x y : Rd d, edist (D'.pt x) (D'.pt y) =
      weylDistOn (D.weylWeight ξ g) univ (D.pt x) (D.pt y) := by
    intro x y
    rw [ContMetric.edist_pt, hD', weylScale_eq_weylDistOn]
  calc curveLength (D'.pt ∘ P) a b = curveLengthWith edist (D'.pt ∘ P) a b :=
        (curveLengthWith_edist _ _ _).symm
    _ = curveLengthWith (weylDistOn (D.weylWeight ξ g) univ) (D.pt ∘ P) a b :=
        partitionSup_congr fun u v _ _ _ => hedist (P u) (P v)
    _ = weightedLength (D.weylWeight ξ g) (D.pt ∘ P) a b :=
        curveLengthWith_weylDistOn isOpen_univ (D.continuous_weylWeight ξ g).continuousOn
          (D.continuous_pt.comp_continuousOn hP) (mapsTo_univ _ _)

/-- `D' = e^{ξ g}·D` and `D` have the same rectifiable curves. -/
theorem curveLength_weyl_ne_top_iff
    (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ g D x y) {P : ℝ → Rd d}
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    curveLength (D'.pt ∘ P) a b ≠ ⊤ ↔ curveLength (D.pt ∘ P) a b ≠ ⊤ := by
  rw [curveLength_eq_weightedLength_of_weyl hD' hP]
  have hc : ContinuousOn (D.pt ∘ P) (Icc a b) := D.continuous_pt.comp_continuousOn hP
  obtain ⟨m, M, hm, hmM⟩ := exists_bounds_along (U := univ)
    (D.continuous_weylWeight ξ g).continuousOn (fun x _ => D.weylWeight_pos ξ g x) hab hc
    (mapsTo_univ _ _)
  constructor
  · intro h hL
    exact h (weightedLength_eq_top hm hab (fun s hs => (hmM s hs).1) hL)
  · exact weightedLength_ne_top (M := M) fun s hs => (hmM s hs).2

end LengthIdentity

/-! ### Comparison of metrics ([S] Lemma 2.1(d) on `ℝ^d`) -/

section Compare

variable {D E : ContMetric d}

theorem curveLength_pt_le_of_le {C : ℝ} (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y))
    (P : ℝ → Rd d) (a b : ℝ) :
    curveLength (E.pt ∘ P) a b ≤ ENNReal.ofReal C * curveLength (D.pt ∘ P) a b := by
  rw [← curveLengthWith_edist, ← curveLengthWith_edist, ← curveLengthWith_const_mul]
  refine partitionSup_mono fun u v _ _ _ => ?_
  show edist (E.pt (P u)) (E.pt (P v)) ≤ ENNReal.ofReal C * edist (D.pt (P u)) (D.pt (P v))
  rw [ContMetric.edist_pt, ContMetric.edist_pt, ← ENNReal.ofReal_mul' (D.nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal (h _ _)

theorem le_curveLength_pt_of_le {c : ℝ} (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    (P : ℝ → Rd d) (a b : ℝ) :
    ENNReal.ofReal c * curveLength (D.pt ∘ P) a b ≤ curveLength (E.pt ∘ P) a b := by
  rw [← curveLengthWith_edist, ← curveLengthWith_edist, ← curveLengthWith_const_mul]
  refine partitionSup_mono fun u v _ _ _ => ?_
  show ENNReal.ofReal c * edist (D.pt (P u)) (D.pt (P v)) ≤ edist (E.pt (P u)) (E.pt (P v))
  rw [ContMetric.edist_pt, ContMetric.edist_pt, ← ENNReal.ofReal_mul' (D.nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal (h _ _)

/-- `E ≤ C D` ⇒ `len(P; E) ≤ C len(P; D)`. -/
theorem ContMetric.len_le_mul_of_le {C : ℝ} (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y))
    (P : ℝ → Rd d) (a b : ℝ) : E.len P a b ≤ ENNReal.ofReal C * D.len P a b :=
  curveLength_pt_le_of_le h P a b

/-- `c D ≤ E` ⇒ `c len(P; D) ≤ len(P; E)`. -/
theorem ContMetric.mul_len_le_of_le {c : ℝ} (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    (P : ℝ → Rd d) (a b : ℝ) : ENNReal.ofReal c * D.len P a b ≤ E.len P a b :=
  le_curveLength_pt_of_le h P a b

/-- `c D ≤ E` ⇒ `c D(·,·;U) ≤ E(·,·;U)`. -/
theorem ContMetric.mul_internal_le_of_le {c : ℝ} (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    (U : Set (Rd d)) (z w : Rd d) :
    ENNReal.ofReal c * D.internal U z w ≤ E.internal U z w := by
  refine E.le_internal fun P hc h0 h1 hU => ?_
  calc ENNReal.ofReal c * D.internal U z w ≤ ENNReal.ofReal c * D.len P 0 1 := by
        refine mul_le_mul' le_rfl ?_
        have := D.internal_le_len zero_le_one hc hU
        rwa [h0, h1] at this
    _ ≤ E.len P 0 1 := ContMetric.mul_len_le_of_le h P 0 1

/-- `E ≤ C D` (`C > 0`) ⇒ `E(·,·;U) ≤ C D(·,·;U)`. -/
theorem ContMetric.internal_le_mul_of_le {C : ℝ} (hC : 0 < C)
    (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y)) (U : Set (Rd d)) (z w : Rd d) :
    E.internal U z w ≤ ENNReal.ofReal C * D.internal U z w := by
  rw [D.internal_eq_iInf_len]
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top,
    le_iInf_iff]
  intro P hc h0 h1 hU
  calc E.internal U z w ≤ E.len P 0 1 := by
        have := E.internal_le_len zero_le_one hc hU
        rwa [h0, h1] at this
    _ ≤ ENNReal.ofReal C * D.len P 0 1 := ContMetric.len_le_mul_of_le h P 0 1

variable {ξ : ℝ} {f : C(Rd d, ℝ)}

/-- The `E`-weighted length of a curve is at most `C` times its `D`-weighted length. -/
theorem weightedLength_weyl_le_mul_of_le {C : ℝ} (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y))
    (P : ℝ → Rd d) (a b : ℝ) :
    weightedLength (E.weylWeight ξ f) (E.pt ∘ P) a b ≤
      ENNReal.ofReal C * weightedLength (D.weylWeight ξ f) (D.pt ∘ P) a b := by
  unfold weightedLength
  rw [← partitionSup_const_mul]
  refine partitionSup_mono fun u v _ _ _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul' (le_of_eq rfl) (curveLength_pt_le_of_le h P u v)

theorem le_weightedLength_weyl_of_le {c : ℝ} (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    (P : ℝ → Rd d) (a b : ℝ) :
    ENNReal.ofReal c * weightedLength (D.weylWeight ξ f) (D.pt ∘ P) a b ≤
      weightedLength (E.weylWeight ξ f) (E.pt ∘ P) a b := by
  unfold weightedLength
  rw [← partitionSup_const_mul]
  refine partitionSup_mono fun u v _ _ _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul' (le_of_eq rfl) (le_curveLength_pt_of_le h P u v)

/-- **[S] Lemma 2.1(d)** for Weyl scaling: `E ≤ C D` (`C > 0`) ⇒ `(e^{ξ f}·E)_U ≤ C (e^{ξ f}·D)_U`. -/
theorem weylScaleOn_le_mul_of_le {C : ℝ} (hC : 0 < C)
    (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y)) (U : Set (Rd d)) (z w : Rd d) :
    weylScaleOn ξ f E U z w ≤ ENNReal.ofReal C * weylScaleOn ξ f D U z w := by
  rw [weylScaleOn_eq_iInf_curve, weylScaleOn_eq_iInf_curve]
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top]
  exact iInf_mono fun P => iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ =>
    iInf_mono fun _ => weightedLength_weyl_le_mul_of_le h P 0 1

/-- **[S] Lemma 2.1(d)** for Weyl scaling: `c D ≤ E` ⇒ `c (e^{ξ f}·D)_U ≤ (e^{ξ f}·E)_U`. -/
theorem mul_weylScaleOn_le_of_le {c : ℝ} (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    (U : Set (Rd d)) (z w : Rd d) :
    ENNReal.ofReal c * weylScaleOn ξ f D U z w ≤ weylScaleOn ξ f E U z w := by
  conv_rhs => rw [weylScaleOn_eq_iInf_curve]
  simp only [le_iInf_iff]
  intro P hc h0 h1 hU
  exact (mul_le_mul' le_rfl (weylScaleOn_le_curve hc h0 h1 hU)).trans
    (le_weightedLength_weyl_of_le h P 0 1)

theorem weylScale_le_mul_of_le {C : ℝ} (hC : 0 < C)
    (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y)) (z w : Rd d) :
    weylScale ξ f E z w ≤ ENNReal.ofReal C * weylScale ξ f D z w := by
  simp only [← weylScaleOn_univ]; exact weylScaleOn_le_mul_of_le hC h univ z w

theorem mul_weylScale_le_of_le {c : ℝ} (h : ∀ x y : Rd d, c * D.1 (x, y) ≤ E.1 (x, y))
    (z w : Rd d) : ENNReal.ofReal c * weylScale ξ f D z w ≤ weylScale ξ f E z w := by
  simp only [← weylScaleOn_univ]; exact mul_weylScaleOn_le_of_le h univ z w

end Compare

end HigherDimLQGMetric
