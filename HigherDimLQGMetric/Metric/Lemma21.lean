import HigherDimLQGMetric.Metric.WeightedLength
import LQGMetric.Metric.InternalOps

/-!
# The source's Lemma 2.1: lengths under a continuous weight

Packet M1 (Phase A, block A2). [S] Lemma 2.1 (l. 179–238) in the corrected form of the blueprint
(`s2-compact.tex`, Lemma `lem:21`; MA1 A2, item 12), for a pseudo-extended-metric space `(X, D)`
(`D = edist`), a set `U ⊆ X` and a weight `w : X → ℝ` (continuous on `U` where needed).

`weylDistOn w U x y = (w·D)_U(x, y)` (MA1's `weylDistOn`): the infimum of the weighted lengths
`∫_P w ds_D` (`weightedLength`) of continuous curves `P : [0, 1] → U` from `x` to `y`.

* (a) `weylDistOn_ge_of_ball`: if `w ≥ m` on `U ∩ B̄(x₀, 3r)`, then `(w·D)_U(x, y) ≥ m D(x, y)` for
  `x, y ∈ B(x₀, r)` (first-exit barrier `exists_exit_weightedLength`; no hypothesis on `D`);
  the centred form `weylDistOn_ge_min`.
* (b) `(w·D)_U` is an extended pseudometric on `U` (`weylDistOn_self`, `weylDistOn_comm`,
  `weylDistOn_triangle`), positive off the diagonal (`edist_eq_zero_of_weylDistOn_eq_zero`), finite
  between points joined by a rectifiable curve in `U` (`weylDistOn_ne_top`).
* (c) **Length identity** `lemma21_length` (MA1's shape; `curveLengthWith_weylDistOn`): for every
  continuous curve `P` in the open set `U`, `len(P; (w·D)_U) = ∫_P w ds_D` in `[0, ∞]`; in
  particular `P` is `(w·D)_U`-rectifiable iff it is `D`-rectifiable (`curveLengthWith_weylDistOn_ne_top_iff`).
* (d) Comparison of metrics: `lemma21_compare` (MA1's first step, for curve lengths),
  `weightedLengthWith_compare` (weighted lengths) and `weylDistOnWith_compare` (distances).
* (e) `weylDistOn_internal`: for `V ⊆ U`, the internal distance of `V` induced by `(w·D)_U` is
  `(w·D)_V`; `weylDistOn_congr_weight`: it depends only on `w|_V`.
* (f) For a locally length `(U, D)` (`IsLocallyLengthOn`): the local upper bound
  `weylDistOn_le_of_ball`, the topology (`exists_weylDistOn_lt_of_isLocallyLengthOn` together with
  `exists_edist_lt_of_weylDistOn_lt`: `(w·D)_U` and `D` induce the same topology on `U`), and the
  length property (`weylDistOn_internal` with `V = U`).

Proofs follow the blueprint (MA1 A2): subcurves as competitors for "≤" in (c); for "≥", a uniform
local lower bound `(w·D)_U ≥ (min w − η) D` near the compact image (from (a) and a thickening of
the image inside `{w > c} ∩ U`), applied on the pieces of a fine uniform partition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### The weighted distance -/

/-- `(w·D)(x, y; S)`: the infimum of the weighted lengths `∫_P w ds` of continuous curves
`P : [0, 1] → S` from `x` to `y` (`∞` if there is none; MA1's `weylDistOn`). -/
def weylDistOn (w : X → ℝ) (S : Set X) (x y : X) : ℝ≥0∞ :=
  ⨅ (P : ℝ → X) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = x) (_ : P 1 = y)
    (_ : MapsTo P (Icc 0 1) S), weightedLength w P 0 1

variable {w w' : X → ℝ} {S T U V : Set X} {x y z : X}

theorem weylDistOn_le {P : ℝ → X} (hc : ContinuousOn P (Icc 0 1)) (h0 : P 0 = x) (h1 : P 1 = y)
    (hS : MapsTo P (Icc 0 1) S) : weylDistOn w S x y ≤ weightedLength w P 0 1 :=
  iInf_le_of_le P <| iInf_le_of_le hc <| iInf_le_of_le h0 <| iInf_le_of_le h1 <|
    iInf_le_of_le hS le_rfl

theorem le_weylDistOn {e : ℝ≥0∞}
    (h : ∀ P : ℝ → X, ContinuousOn P (Icc 0 1) → P 0 = x → P 1 = y → MapsTo P (Icc 0 1) S →
      e ≤ weightedLength w P 0 1) : e ≤ weylDistOn w S x y := by
  simp only [weylDistOn, le_iInf_iff]
  exact h

/-- Curves on any parameter interval `[a, b]` are competitors. -/
theorem weylDistOn_le_of_curve {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn P (Icc a b)) (hS : MapsTo P (Icc a b) S) :
    weylDistOn w S (P a) (P b) ≤ weightedLength w P a b := by
  have hφ : MapsTo (fun s : ℝ => a + s * (b - a)) (Icc 0 1) (Icc a b) := fun s hs =>
    ⟨by nlinarith [hs.1, sub_nonneg.2 hab], by nlinarith [hs.2, sub_nonneg.2 hab]⟩
  rw [← weightedLength_affine hab]
  exact weylDistOn_le (hc.comp (by fun_prop) hφ) (by simp) (by simp) (hS.comp hφ)

theorem weylDistOn_anti (hST : S ⊆ T) : weylDistOn w T x y ≤ weylDistOn w S x y :=
  le_weylDistOn fun _ hc h0 h1 hS => weylDistOn_le hc h0 h1 (hS.mono_right hST)

theorem weylDistOn_mono_weight (h : ∀ x ∈ S, w x ≤ w' x) :
    weylDistOn w S x y ≤ weylDistOn w' S x y :=
  le_weylDistOn fun _ hc h0 h1 hS => (weylDistOn_le hc h0 h1 hS).trans
    (weightedLength_mono_weight fun _ hs => h _ (hS hs))

/-- Locality in the weight (Lemma 2.1(e), second clause): only `w|_S` matters. -/
theorem weylDistOn_congr_weight (h : ∀ x ∈ S, w x = w' x) :
    weylDistOn w S x y = weylDistOn w' S x y :=
  le_antisymm (weylDistOn_mono_weight fun x hx => (h x hx).le)
    (weylDistOn_mono_weight fun x hx => (h x hx).ge)

/-! ### (b) An extended pseudometric -/

theorem weylDistOn_self (hx : x ∈ S) : weylDistOn w S x x = 0 := by
  refine le_antisymm ((weylDistOn_le (P := fun _ => x) continuousOn_const rfl rfl
    fun _ _ => hx).trans ?_) bot_le
  refine (weightedLength_le_ofReal_mul_curveLength (M := w x) fun _ _ => le_rfl).trans ?_
  rw [show curveLength (fun _ : ℝ => x) 0 1 = 0 from
    eVariationOn.constant_on (by rintro _ ⟨_, -, rfl⟩ _ ⟨_, -, rfl⟩; rfl), mul_zero]

theorem weylDistOn_comm_le (x y : X) : weylDistOn w S y x ≤ weylDistOn w S x y := by
  refine le_weylDistOn fun P hc h0 h1 hS => ?_
  have hφ : MapsTo (fun t : ℝ => 0 + 1 - t) (Icc 0 1) (Icc 0 1) := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine (weylDistOn_le (P := fun t => P (0 + 1 - t)) (hc.comp (by fun_prop) hφ)
    (by simpa using h1) (by simpa using h0) (hS.comp hφ)).trans_eq ?_
  exact weightedLength_comp_reflect 0 1

/-- **Symmetry** (reversal of curves). -/
theorem weylDistOn_comm (x y : X) : weylDistOn w S x y = weylDistOn w S y x :=
  le_antisymm (weylDistOn_comm_le y x) (weylDistOn_comm_le x y)

/-- **Triangle inequality** (concatenation of curves). -/
theorem weylDistOn_triangle (x y z : X) :
    weylDistOn w S x z ≤ weylDistOn w S x y + weylDistOn w S y z := by
  rw [← tsub_le_iff_right]
  refine le_weylDistOn fun P₁ hc₁ h₁0 h₁1 hS₁ => ?_
  rw [tsub_le_iff_right, ← tsub_le_iff_left]
  refine le_weylDistOn fun P₂ hc₂ h₂0 h₂1 hS₂ => ?_
  rw [tsub_le_iff_left]
  -- the concatenation on `[0, 2]`
  set Q : ℝ → X := fun t => P₂ (t - 1) with hQ
  have hQc : ContinuousOn Q (Icc 1 2) :=
    hc₂.comp (by fun_prop) fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hPQ : P₁ 1 = Q 1 := by simp [hQ, h₁1, h₂0]
  set R : ℝ → X := fun t => if t ≤ 1 then P₁ t else Q t with hR
  have hRc : ContinuousOn R (Icc 0 2) := continuousOn_concat zero_le_one one_le_two hPQ hc₁ hQc
  have hRS : MapsTo R (Icc 0 2) S := by
    intro t ht
    by_cases h : t ≤ 1
    · simp only [hR, ite_eq_left h]; exact hS₁ ⟨ht.1, h⟩
    · simp only [hR, ite_eq_right h, hQ]
      exact hS₂ ⟨by linarith [not_le.1 h], by linarith [ht.2]⟩
  have hR0 : R 0 = x := by simp [hR, h₁0]
  have hR2 : R 2 = z := by simp [hR, hQ, show ¬(2 : ℝ) ≤ 1 by norm_num, show (2 : ℝ) - 1 = 1 by
    norm_num, h₂1]
  have h1 : weightedLength w R 0 1 = weightedLength w P₁ 0 1 :=
    weightedLength_congr fun t ht => by simp [hR, ht.2]
  have h2 : weightedLength w R 1 2 = weightedLength w P₂ 0 1 := by
    rw [weightedLength_congr (Q := Q) fun t ht => ?_]
    · have := weightedLength_comp_monotoneOn (w := w) (P := P₂) (φ := fun t => t - 1)
        one_le_two (by fun_prop) (fun s _ t _ hst => by simp only; linarith)
      simpa [hQ, Function.comp_def, show (2 : ℝ) - 1 = 1 by norm_num] using this
    · rcases eq_or_lt_of_le ht.1 with h | h
      · subst h; simp [hR, hPQ]
      · simp [hR, not_le.2 h]
  calc weylDistOn w S x z = weylDistOn w S (R 0) (R 2) := by rw [hR0, hR2]
    _ ≤ weightedLength w R 0 2 := weylDistOn_le_of_curve zero_le_two hRc hRS
    _ = weightedLength w R 0 1 + weightedLength w R 1 2 :=
        (weightedLength_add zero_le_one one_le_two).symm
    _ = weightedLength w P₁ 0 1 + weightedLength w P₂ 0 1 := by rw [h1, h2]

/-- Finite between points joined by a rectifiable curve in `S` along which `w` is continuous. -/
theorem weylDistOn_ne_top {P : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn P (Icc a b))
    (hS : MapsTo P (Icc a b) S) (hw : ContinuousOn (fun t => w (P t)) (Icc a b))
    (hL : curveLength P a b ≠ ⊤) : weylDistOn w S (P a) (P b) ≠ ⊤ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hw).bddAbove
  exact ne_top_of_le_ne_top (weightedLength_ne_top (M := M) (fun s hs => hM ⟨s, hs, rfl⟩) hL)
    (weylDistOn_le_of_curve hab hc hS)

/-! ### (a) The first-exit barrier -/

/-- **First-exit barrier**: if the curve `P` reaches distance `≥ R` from `c`, there is a first such
time `τ`; up to `τ` the curve stays in the closed ball `B̄(c, R)`, so if `w ≥ m` there along `P`,
`∫_P w ds ≥ m D(P a, P τ)`. -/
theorem exists_exit_weightedLength {P : ℝ → X} {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    {c : X} {R : ℝ≥0∞} {m : ℝ} (hm : ∀ t ∈ Icc a b, edist c (P t) ≤ R → m ≤ w (P t))
    (hexit : ∃ t ∈ Icc a b, R ≤ edist c (P t)) :
    ∃ τ ∈ Icc a b, R ≤ edist c (P τ) ∧
      ENNReal.ofReal m * edist (P a) (P τ) ≤ weightedLength w P a b := by
  have hA : IsClosed {z : X | R ≤ edist c z} :=
    isClosed_le continuous_const (continuous_const.edist continuous_id)
  obtain ⟨τ, hτ, hτA, hbefore⟩ := exists_first_hit hP hA hexit
  refine ⟨τ, hτ, hτA, ?_⟩
  rcases hτ.1.eq_or_lt with hτa | hτa
  · rw [← hτa, edist_self, mul_zero]; exact bot_le
  -- before `τ` the curve is in the open ball, at `τ` on its boundary
  have hlt : ∀ t ∈ Ico a τ, edist c (P t) < R := fun t ht => not_le.1 (hbefore t ht)
  have hcont : ContinuousWithinAt (fun t => edist c (P t)) (Ico a τ) τ :=
    (continuous_const.edist continuous_id).continuousAt.comp_continuousWithinAt
      ((hP τ hτ).mono fun t ht => ⟨ht.1, ht.2.le.trans hτ.2⟩)
  have hne : (𝓝[Ico a τ] τ).NeBot := right_nhdsWithin_Ico_neBot hτa
  have hτR : edist c (P τ) ≤ R :=
    le_of_tendsto hcont (eventually_nhdsWithin_of_forall fun t ht => (hlt t ht).le)
  have hmaτ : ∀ s ∈ Icc a τ, m ≤ w (P s) := by
    intro s hs
    rcases hs.2.eq_or_lt with hsτ | hsτ
    · rw [hsτ]; exact hm τ hτ hτR
    · exact hm s ⟨hs.1, hs.2.trans hτ.2⟩ (hlt s ⟨hs.1, hsτ⟩).le
  calc ENNReal.ofReal m * edist (P a) (P τ) ≤ ENNReal.ofReal m * curveLength P a τ :=
        mul_le_mul' le_rfl (edist_le_curveLength P hτ.1)
    _ ≤ weightedLength w P a τ := ofReal_mul_curveLength_le_weightedLength hτ.1 hmaτ
    _ ≤ weightedLength w P a b := weightedLength_mono_interval le_rfl hτ.1 hτ.2

/-- **[S] Lemma 2.1(a)** (first-exit barrier): if `w ≥ m` on `U ∩ B̄(x₀, 3r)`, then
`(w·D)_U(x, y) ≥ m D(x, y)` for `x, y ∈ B(x₀, r)`. (No hypothesis on `D` or on the size of `U`.) -/
theorem weylDistOn_ge_of_ball {x₀ : X} {r : ℝ≥0∞} {m : ℝ}
    (hm : ∀ y ∈ U, edist x₀ y ≤ 3 * r → m ≤ w y) (hx : edist x₀ x < r) (hy : edist x₀ y < r) :
    ENNReal.ofReal m * edist x y ≤ weylDistOn w U x y := by
  refine le_weylDistOn fun P hc h0 h1 hU => ?_
  by_cases hexit : ∃ t ∈ Icc (0 : ℝ) 1, 3 * r ≤ edist x₀ (P t)
  · obtain ⟨τ, hτ, hτR, hτw⟩ := exists_exit_weightedLength (w := w) hc
      (fun t ht h => hm _ (hU ht) h) hexit
    rw [h0] at hτw
    refine le_trans (mul_le_mul' le_rfl ?_) hτw
    -- `D(x, y) < 2r ≤ D(x, P τ)`
    have hxy : edist x y ≤ 2 * r := by
      calc edist x y ≤ edist x x₀ + edist x₀ y := edist_triangle _ _ _
        _ ≤ r + r := add_le_add (by rw [edist_comm]; exact hx.le) hy.le
        _ = 2 * r := (two_mul r).symm
    have h3 : 3 * r ≤ r + edist x (P τ) :=
      hτR.trans ((edist_triangle _ _ _).trans (add_le_add hx.le le_rfl))
    by_cases hrt : r = ⊤
    · have hxne : edist x₀ x ≠ ⊤ := ne_top_of_lt hx
      have : edist x (P τ) = ⊤ := by
        by_contra hne
        have := (edist_triangle x₀ x (P τ)).trans_lt
          (ENNReal.add_lt_top.2 ⟨hxne.lt_top, lt_top_iff_ne_top.2 hne⟩)
        rw [hrt, show (3 : ℝ≥0∞) * ⊤ = ⊤ from ENNReal.mul_top (by norm_num)] at hτR
        exact absurd (hτR.trans_lt this) (lt_irrefl _)
      rw [this]; exact le_top
    · refine hxy.trans ?_
      have : r + 2 * r ≤ r + edist x (P τ) := by
        rw [show r + 2 * r = 3 * r by ring]; exact h3
      exact (ENNReal.add_le_add_iff_left hrt).1 this
  · push Not at hexit
    have hall : ∀ s ∈ Icc (0 : ℝ) 1, m ≤ w (P s) := fun s hs =>
      hm _ (hU hs) (hexit s hs).le
    calc ENNReal.ofReal m * edist x y = ENNReal.ofReal m * edist (P 0) (P 1) := by rw [h0, h1]
      _ ≤ ENNReal.ofReal m * curveLength P 0 1 := mul_le_mul' le_rfl (edist_le_curveLength P zero_le_one)
      _ ≤ weightedLength w P 0 1 := ofReal_mul_curveLength_le_weightedLength zero_le_one hall

/-- Centred form of (a): if `w ≥ m` on `U ∩ B̄(x, R)`, then `(w·D)_U(x, y) ≥ m min(D(x, y), R)`. -/
theorem weylDistOn_ge_min {R : ℝ≥0∞} {m : ℝ} (hm : ∀ y ∈ U, edist x y ≤ R → m ≤ w y) (y : X) :
    ENNReal.ofReal m * min (edist x y) R ≤ weylDistOn w U x y := by
  refine le_weylDistOn fun P hc h0 h1 hU => ?_
  by_cases hexit : ∃ t ∈ Icc (0 : ℝ) 1, R ≤ edist x (P t)
  · obtain ⟨τ, hτ, hτR, hτw⟩ := exists_exit_weightedLength (w := w) (c := x) hc
      (fun t ht h => hm _ (hU ht) h) hexit
    rw [h0] at hτw
    exact (mul_le_mul' le_rfl ((min_le_right _ _).trans hτR)).trans hτw
  · push Not at hexit
    have hall : ∀ s ∈ Icc (0 : ℝ) 1, m ≤ w (P s) := fun s hs => hm _ (hU hs) (hexit s hs).le
    calc ENNReal.ofReal m * min (edist x y) R ≤ ENNReal.ofReal m * edist (P 0) (P 1) := by
          rw [h0, h1]; exact mul_le_mul' le_rfl (min_le_left _ _)
      _ ≤ ENNReal.ofReal m * curveLength P 0 1 :=
          mul_le_mul' le_rfl (edist_le_curveLength P zero_le_one)
      _ ≤ weightedLength w P 0 1 := ofReal_mul_curveLength_le_weightedLength zero_le_one hall

/-- Near a point of `U` where `w` is continuous and positive, `w ≥ w(x)/2` on a closed ball. -/
theorem exists_ball_half_le (hw : ContinuousAt w x) (hpos : 0 < w x) :
    ∃ R : ℝ≥0∞, 0 < R ∧ ∀ y, edist x y ≤ R → w x / 2 ≤ w y := by
  have hev : ∀ᶠ y in 𝓝 x, w x / 2 < w y := hw.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.1 hev
  obtain ⟨R, hR0, hRε⟩ := exists_between hε
  refine ⟨R, hR0, fun y hy => (hball ?_).le⟩
  rw [Metric.mem_eball, edist_comm]
  exact hy.trans_lt hRε

/-- **(b) positivity**: `(w·D)_U(x, y) = 0` forces `D(x, y) = 0` when `w` is continuous and
positive at `x`. -/
theorem edist_eq_zero_of_weylDistOn_eq_zero (hw : ContinuousAt w x) (hpos : 0 < w x)
    (h : weylDistOn w U x y = 0) : edist x y = 0 := by
  obtain ⟨R, hR0, hR⟩ := exists_ball_half_le hw hpos
  have hle := weylDistOn_ge_min (U := U) (fun y _ hy => hR y hy) y
  rw [h, nonpos_iff_eq_zero, mul_eq_zero] at hle
  rcases hle with h1 | h2
  · exact absurd h1 (by simpa using half_pos hpos)
  · rcases min_eq_bot.1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 hR0.ne'

/-- `(w·D)_U`-small implies `D`-small (half of "same topology", no length hypothesis). -/
theorem exists_edist_lt_of_weylDistOn_lt (hw : ContinuousAt w x) (hpos : 0 < w x) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y, weylDistOn w U x y < δ → edist x y < ε := by
  obtain ⟨R, hR0, hR⟩ := exists_ball_half_le hw hpos
  refine ⟨ENNReal.ofReal (w x / 2) * min ε R,
    ENNReal.mul_pos (by simpa using half_pos hpos) (lt_min hε hR0).ne', fun y hy => ?_⟩
  by_contra hge
  push Not at hge
  have := (mul_le_mul' le_rfl (min_le_min_right R hge)).trans
    (weylDistOn_ge_min (U := U) (fun y _ hy => hR y hy) y)
  exact absurd (this.trans_lt hy) (lt_irrefl _)

/-! ### (c) The length identity -/

/-- Key estimate for (c): on a piece `[u, v]` of a curve in the open set `U`,
`(inf_{[u, v]} w ∘ P) · len(P) ≤ len(P; (w·D)_U)`. -/
theorem infAlong_mul_curveLength_le (hU : IsOpen U) (hw : ContinuousOn w U) {P : ℝ → X}
    {u v : ℝ} (huv : u ≤ v) (hP : ContinuousOn P (Icc u v)) (hPU : MapsTo P (Icc u v) U) :
    infAlong w P u v * curveLength P u v ≤ curveLengthWith (weylDistOn w U) P u v := by
  set m := infAlong w P u v with hm
  refine ENNReal.le_of_forall_lt_one_mul_le fun e he => ?_
  rcases eq_or_ne m 0 with hm0 | hm0
  · rw [hm0, zero_mul, mul_zero]; exact bot_le
  have hmtop : m ≠ ⊤ := infAlong_ne_top huv
  have hcm : e * m < m := by
    calc e * m < 1 * m := ENNReal.mul_lt_mul_left hm0 hmtop he
      _ = m := one_mul m
  have hctop : e * m ≠ ⊤ := ne_top_of_lt hcm
  set c' : ℝ := (e * m).toReal with hc'
  have hc'eq : ENNReal.ofReal c' = e * m := ENNReal.ofReal_toReal hctop
  have hc'w : ∀ s ∈ Icc u v, c' < w (P s) := by
    intro s hs
    have h1 : ENNReal.ofReal c' < ENNReal.ofReal (w (P s)) :=
      hc'eq ▸ hcm.trans_le (infAlong_le hs)
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  rw [← mul_assoc, ← hc'eq]
  -- a thickening of the image inside `{w > c'} ∩ U`
  set O : Set X := U ∩ w ⁻¹' Ioi c' with hO
  have hOo : IsOpen O := hw.isOpen_inter_preimage hU isOpen_Ioi
  have hK : IsCompact (P '' Icc u v) := isCompact_Icc.image_of_continuousOn hP
  have hKO : P '' Icc u v ⊆ O := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hPU hs, hc'w s hs⟩
  obtain ⟨ρ, hρ, hthick⟩ := hK.exists_thickening_subset_open hOo hKO
  set r : ℝ≥0∞ := ENNReal.ofReal (ρ / 4) with hr
  have hr0 : 0 < r := ENNReal.ofReal_pos.2 (by linarith)
  have hloc : ∀ s ∈ Icc u v, ∀ y ∈ U, edist (P s) y ≤ 3 * r → c' ≤ w y := by
    intro s hs y _ hy
    have hy' : y ∈ Metric.thickening ρ (P '' Icc u v) := by
      rw [Metric.mem_thickening_iff_infEDist_lt]
      refine (Metric.infEDist_le_edist_of_mem (mem_image_of_mem P hs)).trans_lt ?_
      rw [edist_comm]
      refine hy.trans_lt ?_
      rw [hr, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
      exact (ENNReal.ofReal_lt_ofReal_iff hρ).2 (by linarith)
    exact (hthick hy').2.le
  -- uniform continuity of `P` and a fine uniform partition of `[u, v]`
  obtain ⟨δ, hδ, hδ'⟩ := EMetric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) r hr0
  obtain ⟨δ', -, hδ'0, hδ'δ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hδ'pos : 0 < δ' := ENNReal.ofReal_pos.1 hδ'0
  obtain ⟨N, hN, hNδ⟩ := exists_uniform_fine huv hδ'pos
  set p := IccPartition.uniform huv N hN with hp
  have hstep : ∀ k, p.t (k + 1) - p.t k = (v - u) / N := IccPartition.uniform_step huv N hN
  have hpiece : ∀ k < N, ENNReal.ofReal c' * curveLength P (p.t k) (p.t (k + 1)) ≤
      curveLengthWith (weylDistOn w U) P (p.t k) (p.t (k + 1)) := by
    intro k hk
    have hk0 : p.t k ∈ Icc u v := p.mem_Icc hk.le
    have hk1 : p.t (k + 1) ∈ Icc u v := p.mem_Icc (Nat.succ_le_of_lt hk)
    have hnear : ∀ σ ∈ Icc (p.t k) (p.t (k + 1)), edist (P (p.t k)) (P σ) < r := by
      intro σ hσ
      refine hδ' hk0 ⟨hk0.1.trans hσ.1, hσ.2.trans hk1.2⟩ ?_
      rw [edist_dist, Real.dist_eq]
      refine (ENNReal.ofReal_lt_ofReal_iff hδ'pos).2 ?_ |>.trans hδ'δ
      rw [abs_lt]
      have := hstep k
      constructor <;> linarith [hσ.1, hσ.2]
    refine le_curveLengthWith_of_le fun σ σ' h1 _ h3 => ?_
    have hσ : σ ∈ Icc (p.t k) (p.t (k + 1)) := ⟨h1, (‹σ ≤ σ'›).trans h3⟩
    have hσ' : σ' ∈ Icc (p.t k) (p.t (k + 1)) := ⟨h1.trans ‹σ ≤ σ'›, h3⟩
    exact weylDistOn_ge_of_ball (x₀ := P (p.t k)) (r := r)
      (fun y hy h3r => hloc _ hk0 y hy h3r) (hnear σ hσ) (hnear σ' hσ')
  calc ENNReal.ofReal c' * curveLength P u v
      = ∑ k ∈ Finset.range N, ENNReal.ofReal c' * curveLength P (p.t k) (p.t (k + 1)) := by
        rw [← Finset.mul_sum]
        congr 1
        have hmono : Monotone p.t := fun i j hij => by
          show u + (i : ℝ) * ((v - u) / N) ≤ u + (j : ℝ) * ((v - u) / N)
          have : 0 ≤ (v - u) / N := div_nonneg (sub_nonneg.2 huv) (Nat.cast_nonneg N)
          gcongr
        rw [sum_curveLength_eq P hmono N]
        congr 1
        · exact p.zero.symm
        · exact p.last.symm
    _ ≤ ∑ k ∈ Finset.range N, curveLengthWith (weylDistOn w U) P (p.t k) (p.t (k + 1)) :=
        Finset.sum_le_sum fun k hk => hpiece k (Finset.mem_range.1 hk)
    _ ≤ curveLengthWith (weylDistOn w U) P u v := p.sum_partitionSup_le _

/-- **[S] Lemma 2.1(c)** (length identity): for every continuous curve `P` in the open set `U`,
`len(P; (w·D)_U) = ∫_P w ds_D` in `[0, ∞]` (`w` continuous on `U`; positivity is not needed). -/
theorem curveLengthWith_weylDistOn (hU : IsOpen U) (hw : ContinuousOn w U) {P : ℝ → X}
    {a b : ℝ} (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) :
    curveLengthWith (weylDistOn w U) P a b = weightedLength w P a b := by
  apply le_antisymm
  · refine partitionSup_le fun p => ?_
    calc p.sum (fun u v => weylDistOn w U (P u) (P v))
        ≤ ∑ i ∈ Finset.range p.n, weightedLength w P (p.t i) (p.t (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
          have hsub : Icc (p.t i) (p.t (i + 1)) ⊆ Icc a b := Icc_subset_Icc h1 h3
          exact weylDistOn_le_of_curve h2 (hP.mono hsub) (hPU.mono_left hsub)
      _ ≤ weightedLength w P a b := p.sum_partitionSup_le _
  · refine partitionSup_le fun p => ?_
    calc p.sum (fun u v => infAlong w P u v * curveLength P u v)
        ≤ ∑ i ∈ Finset.range p.n, curveLengthWith (weylDistOn w U) P (p.t i) (p.t (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
          have hsub : Icc (p.t i) (p.t (i + 1)) ⊆ Icc a b := Icc_subset_Icc h1 h3
          exact infAlong_mul_curveLength_le hU hw h2 (hP.mono hsub) (hPU.mono_left hsub)
      _ ≤ curveLengthWith (weylDistOn w U) P a b := p.sum_partitionSup_le _

/-- **[S] Lemma 2.1(c)**, MA1's shape (`lemma21_length`). -/
theorem lemma21_length (U : Set X) (hU : IsOpen U) (w : X → ℝ) (hw : ContinuousOn w U)
    (_hpos : ∀ x ∈ U, 0 < w x) {P : ℝ → X} {a b : ℝ} (_hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) :
    curveLengthWith (weylDistOn w U) P a b = weightedLength w P a b :=
  curveLengthWith_weylDistOn hU hw hP hPU

/-- Positive continuous weights are bounded above and below by positive constants along a curve. -/
theorem exists_bounds_along (hw : ContinuousOn w U) (hpos : ∀ x ∈ U, 0 < w x) {P : ℝ → X}
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) :
    ∃ m M : ℝ, 0 < m ∧ ∀ s ∈ Icc a b, m ≤ w (P s) ∧ w (P s) ≤ M := by
  have hc : ContinuousOn (fun s => w (P s)) (Icc a b) := hw.comp hP hPU
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hc
  obtain ⟨s₁, hs₁, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hab) hc
  exact ⟨w (P s₀), w (P s₁), hpos _ (hPU hs₀), fun s hs => ⟨hmin hs, hmax hs⟩⟩

/-- **[S] Lemma 2.1(c)**, rectifiability: a curve in `U` is `(w·D)_U`-rectifiable iff it is
`D`-rectifiable (positive continuous weight). -/
theorem curveLengthWith_weylDistOn_ne_top_iff (hU : IsOpen U) (hw : ContinuousOn w U)
    (hpos : ∀ x ∈ U, 0 < w x) {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hPU : MapsTo P (Icc a b) U) :
    curveLengthWith (weylDistOn w U) P a b ≠ ⊤ ↔ curveLength P a b ≠ ⊤ := by
  rw [curveLengthWith_weylDistOn hU hw hP hPU]
  obtain ⟨m, M, hm, hmM⟩ := exists_bounds_along hw hpos hab hP hPU
  constructor
  · intro h hL
    exact h (weightedLength_eq_top hm hab (fun s hs => (hmM s hs).1) hL)
  · exact weightedLength_ne_top (M := M) fun s hs => (hmM s hs).2

/-! ### (d) Comparison of metrics -/

/-- **[S] Lemma 2.1(d)**, first step: `m D ≤ E ≤ M D` gives
`m len(P; D) ≤ len(P; E) ≤ M len(P; D)`. -/
theorem curveLengthWith_compare (E : X → X → ℝ≥0∞) (m M : ℝ≥0∞)
    (hmE : ∀ x y, m * edist x y ≤ E x y) (hEM : ∀ x y, E x y ≤ M * edist x y) (P : ℝ → X)
    (a b : ℝ) :
    m * curveLength P a b ≤ curveLengthWith E P a b ∧
      curveLengthWith E P a b ≤ M * curveLength P a b :=
  ⟨le_curveLengthWith_of_le fun _ _ _ _ _ => hmE _ _,
    curveLengthWith_le_of_le fun _ _ _ _ _ => hEM _ _⟩

/-- **[S] Lemma 2.1(d)**, first step, MA1's shape (`lemma21_compare`; the weight data `U`, `w`,
`hpos` of the shape are not used). -/
theorem lemma21_compare (U : Set X) (w : X → ℝ) (_hpos : ∀ x ∈ U, 0 < w x)
    (E : X → X → ℝ≥0∞) (m M : ℝ≥0∞) (hmE : ∀ x y, m * edist x y ≤ E x y)
    (hEM : ∀ x y, E x y ≤ M * edist x y) (P : ℝ → X) (a b : ℝ) :
    m * curveLength P a b ≤ curveLengthWith E P a b ∧
      curveLengthWith E P a b ≤ M * curveLength P a b :=
  curveLengthWith_compare E m M hmE hEM P a b

/-- **[S] Lemma 2.1(d)**, weighted lengths: if `m D ≤ E ≤ M D` on `U`, then for every curve in `U`,
`m ∫_P w ds_D ≤ ∫_P w ds_E ≤ M ∫_P w ds_D`. -/
theorem weightedLengthWith_compare {E : X → X → ℝ≥0∞} {m M : ℝ≥0∞}
    (hmE : ∀ x ∈ U, ∀ y ∈ U, m * edist x y ≤ E x y)
    (hEM : ∀ x ∈ U, ∀ y ∈ U, E x y ≤ M * edist x y) {P : ℝ → X} {a b : ℝ}
    (hPU : MapsTo P (Icc a b) U) :
    m * weightedLength w P a b ≤ weightedLengthWith E w P a b ∧
      weightedLengthWith E w P a b ≤ M * weightedLength w P a b := by
  unfold weightedLength weightedLengthWith
  rw [← partitionSup_const_mul, ← partitionSup_const_mul]
  constructor
  · refine partitionSup_mono fun u v hu _ hv => ?_
    rw [mul_left_comm]
    exact mul_le_mul' le_rfl (le_curveLengthWith_of_le fun s t h1 _ h3 =>
      hmE _ (hPU ⟨hu.trans h1, (‹s ≤ t›.trans h3).trans hv⟩) _
        (hPU ⟨hu.trans (h1.trans ‹s ≤ t›), h3.trans hv⟩))
  · refine partitionSup_mono fun u v hu _ hv => ?_
    rw [mul_left_comm]
    exact mul_le_mul' le_rfl (curveLengthWith_le_of_le fun s t h1 _ h3 =>
      hEM _ (hPU ⟨hu.trans h1, (‹s ≤ t›.trans h3).trans hv⟩) _
        (hPU ⟨hu.trans (h1.trans ‹s ≤ t›), h3.trans hv⟩))

/-- `(w·E)(x, y; S)` for a distance function `E` (curves continuous for the topology of `D`). -/
def weylDistOnWith (E : X → X → ℝ≥0∞) (w : X → ℝ) (S : Set X) (x y : X) : ℝ≥0∞ :=
  ⨅ (P : ℝ → X) (_ : ContinuousOn P (Icc 0 1)) (_ : P 0 = x) (_ : P 1 = y)
    (_ : MapsTo P (Icc 0 1) S), weightedLengthWith E w P 0 1

theorem weylDistOnWith_le {E : X → X → ℝ≥0∞} {P : ℝ → X} (hc : ContinuousOn P (Icc 0 1))
    (h0 : P 0 = x) (h1 : P 1 = y) (hS : MapsTo P (Icc 0 1) S) :
    weylDistOnWith E w S x y ≤ weightedLengthWith E w P 0 1 :=
  iInf_le_of_le P <| iInf_le_of_le hc <| iInf_le_of_le h0 <| iInf_le_of_le h1 <|
    iInf_le_of_le hS le_rfl

theorem weylDistOnWith_edist (w : X → ℝ) (S : Set X) (x y : X) :
    weylDistOnWith edist w S x y = weylDistOn w S x y := by
  simp only [weylDistOnWith, weylDistOn, weightedLengthWith_edist]

/-- **[S] Lemma 2.1(d)**, distances: if `m D ≤ E ≤ M D` on `U` (`0 < M < ∞`), then
`m (w·D)_U ≤ (w·E)_U ≤ M (w·D)_U`. -/
theorem weylDistOnWith_compare {E : X → X → ℝ≥0∞} {m M : ℝ≥0∞}
    (hmE : ∀ x ∈ U, ∀ y ∈ U, m * edist x y ≤ E x y)
    (hEM : ∀ x ∈ U, ∀ y ∈ U, E x y ≤ M * edist x y) (hM0 : M ≠ 0) (hMt : M ≠ ⊤) (x y : X) :
    m * weylDistOn w U x y ≤ weylDistOnWith E w U x y ∧
      weylDistOnWith E w U x y ≤ M * weylDistOn w U x y := by
  constructor
  · simp only [weylDistOnWith, le_iInf_iff]
    intro P hc h0 h1 hU
    exact (mul_le_mul' le_rfl (weylDistOn_le hc h0 h1 hU)).trans
      (weightedLengthWith_compare hmE hEM hU).1
  · simp only [weylDistOn, ENNReal.mul_iInf_of_ne hM0 hMt, le_iInf_iff]
    intro P hc h0 h1 hU
    exact (weylDistOnWith_le hc h0 h1 hU).trans (weightedLengthWith_compare hmE hEM hU).2

/-! ### (e) Internal distances -/

/-- **[S] Lemma 2.1(e)**: for `V ⊆ U` (`U` open, `w` continuous on `U`), the internal distance of
`V` induced by `(w·D)_U` is `(w·D)_V`; it depends only on `w|_V` (`weylDistOn_congr_weight`) and
on the `D`-lengths of curves in `V` (by definition). -/
theorem weylDistOn_internal (hU : IsOpen U) (hw : ContinuousOn w U) (hVU : V ⊆ U) (x y : X) :
    internalWith (weylDistOn w U) V x y = weylDistOn w V x y := by
  unfold internalWith weylDistOn
  refine iInf_congr fun P => iInf_congr fun hc => iInf_congr fun _ => iInf_congr fun _ =>
    iInf_congr fun hV => ?_
  exact curveLengthWith_weylDistOn hU hw hc (hV.mono_right hVU)

/-- **[S] Lemma 2.1(f)**, length property: `(w·D)_U` is the length distance it induces on `U`. -/
theorem weylDistOn_isLength (hU : IsOpen U) (hw : ContinuousOn w U) (x y : X) :
    internalWith (weylDistOn w U) U x y = weylDistOn w U x y :=
  weylDistOn_internal hU hw subset_rfl x y

/-! ### (f) Locally length spaces: local upper bound and topology -/

/-- `(U, D)` is **locally length** (blueprint Lemma 2.1(f)): every `x₀ ∈ U` has `r > 0` with
`B(x₀, 4r) ⊆ U` such that any two points of `B(x₀, r)` are joined, for every `ε > 0`, by continuous
curves in `B(x₀, 3r)` of length `≤ D(x, y) + ε`. -/
def IsLocallyLengthOn (U : Set X) : Prop :=
  ∀ x₀ ∈ U, ∃ r : ℝ≥0∞, 0 < r ∧ Metric.eball x₀ (4 * r) ⊆ U ∧
    ∀ x y, edist x₀ x < r → edist x₀ y < r → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ P : ℝ → X, ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧ P 1 = y ∧
        MapsTo P (Icc 0 1) (Metric.eball x₀ (3 * r)) ∧ curveLength P 0 1 ≤ edist x y + ε

/-- `a ≤ K (b + ε)` for all small real `ε > 0` gives `a ≤ K b` when `K < ∞`. -/
theorem le_mul_of_forall_lt_add {a b K : ℝ≥0∞} (hK : K ≠ ⊤) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (h : ∀ ε : ℝ, 0 < ε → ε < ε₀ → a ≤ K * (b + ENNReal.ofReal ε)) : a ≤ K * b := by
  have h1 : Tendsto (fun ε : ℝ => b + ENNReal.ofReal ε) (𝓝 0) (𝓝 (b + ENNReal.ofReal 0)) :=
    tendsto_const_nhds.add (ENNReal.continuous_ofReal.tendsto 0)
  rw [ENNReal.ofReal_zero, add_zero] at h1
  have ht : Tendsto (fun ε : ℝ => K * (b + ENNReal.ofReal ε)) (𝓝[>] 0) (𝓝 (K * b)) :=
    ENNReal.Tendsto.const_mul (h1.mono_left nhdsWithin_le_nhds) (Or.inr hK)
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε using h ε hε.1 hε.2

/-- **[S] Lemma 2.1(f)**, local upper bound: if any two points of `B(x₀, r)` are joined by
near-geodesic curves in `B(x₀, 3r) ⊆ U`, then `(w·D)_U ≤ (sup_{B(x₀, 3r)} w) D` on `B(x₀, r)`. -/
theorem weylDistOn_le_of_ball {x₀ : X} {r : ℝ≥0∞} (h3r : Metric.eball x₀ (3 * r) ⊆ U)
    (hcurve : ∀ x y, edist x₀ x < r → edist x₀ y < r → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ P : ℝ → X, ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧ P 1 = y ∧
        MapsTo P (Icc 0 1) (Metric.eball x₀ (3 * r)) ∧ curveLength P 0 1 ≤ edist x y + ε)
    {M : ℝ} (hM : ∀ y ∈ Metric.eball x₀ (3 * r), w y ≤ M) (hx : edist x₀ x < r)
    (hy : edist x₀ y < r) : weylDistOn w U x y ≤ ENNReal.ofReal M * edist x y := by
  refine le_mul_of_forall_lt_add ENNReal.ofReal_ne_top one_pos fun ε hε _ => ?_
  obtain ⟨P, hc, h0, h1, hP3, hlen⟩ := hcurve x y hx hy (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  calc weylDistOn w U x y ≤ weightedLength w P 0 1 := weylDistOn_le hc h0 h1 (hP3.mono_right h3r)
    _ ≤ ENNReal.ofReal M * curveLength P 0 1 :=
        weightedLength_le_ofReal_mul_curveLength fun s hs => hM _ (hP3 hs)
    _ ≤ ENNReal.ofReal M * (edist x y + ENNReal.ofReal ε) := mul_le_mul' le_rfl hlen

/-- **[S] Lemma 2.1(f)**, local Lipschitz bound at a point of a locally length `U` where `w` is
continuous: `(w·D)_U(x, y) ≤ (w(x) + 1) D(x, y)` for `y` near `x`. -/
theorem exists_weylDistOn_le_mul (hloc : IsLocallyLengthOn U) (hx : x ∈ U)
    (hw : ContinuousAt w x) :
    ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ∀ y, edist x y < ρ →
      weylDistOn w U x y ≤ ENNReal.ofReal (w x + 1) * edist x y := by
  obtain ⟨r, hr0, h4r, hcurve⟩ := hloc x hx
  have hev : ∀ᶠ y in 𝓝 x, w y < w x + 1 := hw.eventually (gt_mem_nhds (by linarith))
  obtain ⟨R, hR0, hRball⟩ := EMetric.mem_nhds_iff.1 hev
  have hR2 : 0 < R / 2 := ENNReal.half_pos hR0.ne'
  obtain ⟨ε₀, -, hε₀0, hε₀R⟩ := ENNReal.lt_iff_exists_real_btwn.1 hR2
  have hε₀ : 0 < ε₀ := ENNReal.ofReal_pos.1 hε₀0
  have h3r4r : Metric.eball x (3 * r) ⊆ U := fun z hz => h4r (by
    rw [Metric.mem_eball] at hz ⊢
    exact hz.trans_le (mul_le_mul' (by norm_num) le_rfl))
  refine ⟨min r (R / 2), lt_min hr0 hR2, fun y hy => ?_⟩
  have hyr : edist x y < r := hy.trans_le (min_le_left _ _)
  have hyR : edist x y < R / 2 := hy.trans_le (min_le_right _ _)
  refine le_mul_of_forall_lt_add ENNReal.ofReal_ne_top hε₀ fun ε hε hεε₀ => ?_
  obtain ⟨P, hc, h0, h1, hP3, hlen⟩ := hcurve x y (by simpa using hr0) hyr (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε)
  have hlenR : curveLength P 0 1 < R := by
    refine hlen.trans_lt ?_
    calc edist x y + ENNReal.ofReal ε < R / 2 + R / 2 :=
          ENNReal.add_lt_add hyR ((ENNReal.ofReal_le_ofReal hεε₀.le).trans_lt hε₀R)
      _ = R := ENNReal.add_halves R
  have hw1 : ∀ s ∈ Icc (0 : ℝ) 1, w (P s) ≤ w x + 1 := by
    intro s hs
    have hd : edist (P s) x < R := by
      rw [edist_comm, ← h0]
      exact ((edist_le_curveLength P hs.1).trans (curveLength_mono P le_rfl hs.2)).trans_lt hlenR
    exact (hRball (Metric.mem_eball.2 hd)).le
  calc weylDistOn w U x y ≤ weightedLength w P 0 1 := weylDistOn_le hc h0 h1 (hP3.mono_right h3r4r)
    _ ≤ ENNReal.ofReal (w x + 1) * curveLength P 0 1 := weightedLength_le_ofReal_mul_curveLength hw1
    _ ≤ ENNReal.ofReal (w x + 1) * (edist x y + ENNReal.ofReal ε) := mul_le_mul' le_rfl hlen

/-- **[S] Lemma 2.1(f)**, topology: on a locally length `U`, `D`-small implies `(w·D)_U`-small at
every point where `w` is continuous. With `exists_edist_lt_of_weylDistOn_lt` (the converse, at
points where `w > 0`), `(w·D)_U` and `D` induce the same topology on `U`. -/
theorem exists_weylDistOn_lt_of_isLocallyLengthOn (hloc : IsLocallyLengthOn U) (hx : x ∈ U)
    (hw : ContinuousAt w x) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y, edist x y < δ → weylDistOn w U x y < ε := by
  obtain ⟨ρ, hρ, hle⟩ := exists_weylDistOn_le_mul hloc hx hw
  set K := ENNReal.ofReal (w x + 1) with hK
  have hK1 : K + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by simp
  refine ⟨min ρ (ε / (K + 1)), lt_min hρ (ENNReal.div_pos_iff.2 ⟨hε.ne', hK1⟩), fun y hy => ?_⟩
  calc weylDistOn w U x y ≤ K * edist x y := hle y (hy.trans_le (min_le_left _ _))
    _ ≤ (K + 1) * edist x y := mul_le_mul' le_self_add le_rfl
    _ < (K + 1) * (ε / (K + 1)) :=
        ENNReal.mul_lt_mul_right hK0 hK1 (hy.trans_le (min_le_right _ _))
    _ = ε := ENNReal.mul_div_cancel hK0 hK1

end HigherDimLQGMetric


