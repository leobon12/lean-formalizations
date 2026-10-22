import HigherDimLQGMetric.Trap.BaseII

/-!
# The trap for the base configuration ([S] Lemma 4.2, MA1 A17: construction, (i) and (ii) for `ξ₀`)

Packet S3. Metric form: `Z` is a metric space whose distance is the base coordinate `ζ`; `E` is the
comparison coordinate `ζ̃` (`E ≤ M ζ`). The graph `K` and its marked arcs `σ i` are given in the
form of the hypotheses of S1c's `lemma32_shortcut` (finite rectifiable graph, marked arcs in `K`
with endpoint distance `≥ a₁` and `E`-length ratio `≤ c₀`, and the forcing property
`TrapForcing` at threshold `b/4` for every horizon). For a weight sequence `w_n` with the collapse
properties of MA1 A13 and `w_n = 1` off `V`, `trap_base` chooses one index `N` and proves:

* (i) for `ξ₀`: every two points of `closure V` are joined by three pieces (an access curve, a
  shortest graph curve, a reversed access curve) inside `Y₀ = trapSet A V (a_col/2)`, each of
  `ζ`-length `≤ L₀`, of total `w_N`-weighted cost `≤ 3ε₀ - 2η_*`;
* (ii) for `ξ₀`: every `(w_N·ζ)`-minimizer between points of `closure V` at distance `≥ b/2` has a
  subcurve of weighted length `≥ 2c` and a shortcut of `E`-weighted cost `≤ ĉ` times that length
  inside `Y′ = trapSet A V a_col`, with `c₀ < ĉ < c'`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- The marked-arc **forcing property** of S1c's `lemma32_shortcut` (its hypothesis `hforce`,
verbatim) at horizon `T` and threshold `b`: every unit-speed `d_K`-geodesic between points of `K`
at distance `≥ b` traverses some marked arc completely, in one of the two orientations. -/
def TrapForcing {Z I : Type*} [MetricSpace Z] (K : Set Z) (σ : I → ℝ → Z) (b T : ℝ)
    (hT : 0 ≤ T) : Prop :=
  ∀ (p q : Z) (_hp : p ∈ K) (_hq : q ∈ K), b ≤ dist p q →
    ∀ (Q : Icc (0 : ℝ) T →ᵇ Z) (_hQK : ∀ t, Q t ∈ K)
      (_hQ0 : (Set.IccExtend hT Q) 0 = p)
      (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T),
      Q ⟨ℓ, ⟨hℓ0, hℓT⟩⟩ = q →
      (∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
        internalEDist K ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) =
          ENNReal.ofReal (t - s)) →
      ∃ i : I, TraversesMarkedArc hℓT Q (σ i) ∨
        TraversesMarkedArc hℓT Q (fun r => σ i (1 - r))

/-- An access curve from `closure V` of length `≤ ε₀ < r` stays in `Y_r` (collar width `≥ r`). -/
theorem trap_access_mapsTo {Z : Type*} [MetricSpace Z] {A V : Set Z} (hA : IsOpen A)
    (hV : IsOpen V) (hVA : closure V ⊆ A) {r ε₀ : ℝ} (hr : 0 < r) (hε₀r : ε₀ < r)
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, r ≤ dist x y) {P : ℝ → Z}
    (hPc : ContinuousOn P (Icc 0 1)) (hP0 : P 0 ∈ closure V)
    (hPlen : curveLength P 0 1 ≤ ENNReal.ofReal ε₀) :
    MapsTo P (Icc 0 1) (trapSet A V r) := by
  apply trap_mapsTo_trapSet hA hV hVA (w := fun _ => (1 : ℝ)) (fun _ _ => rfl) hcol hPc hP0
  calc weightedLength (fun _ => (1 : ℝ)) P 0 1 ≤ ENNReal.ofReal 1 * curveLength P 0 1 :=
        weightedLength_le_ofReal_mul_curveLength fun _ _ => le_rfl
    _ ≤ ENNReal.ofReal ε₀ := by rw [ENNReal.ofReal_one, one_mul]; exact hPlen
    _ < ENNReal.ofReal r := (ENNReal.ofReal_lt_ofReal_iff hr).2 hε₀r

/-- A finite rectifiable graph is nonempty (it is connected). -/
theorem trap_graph_nonempty {Z : Type*} [MetricSpace Z] {K : Set Z} (hK : IsFiniteRectGraph K) :
    K.Nonempty := by
  obtain ⟨_, _, _, _, _, _, hconn⟩ := hK
  exact hconn.nonempty

/-- Three chained pieces bound the confined weighted distance. -/
theorem trap_weylDistOn_le_three {Z : Type*} [MetricSpace Z] {w : Z → ℝ} {S : Set Z}
    {P₁ P₂ P₃ : ℝ → Z} (h1 : ContinuousOn P₁ (Icc 0 1)) (h2 : ContinuousOn P₂ (Icc 0 1))
    (h3 : ContinuousOn P₃ (Icc 0 1)) (hS1 : MapsTo P₁ (Icc 0 1) S)
    (hS2 : MapsTo P₂ (Icc 0 1) S) (hS3 : MapsTo P₃ (Icc 0 1) S)
    (h12 : P₁ 1 = P₂ 0) (h23 : P₂ 1 = P₃ 0) :
    weylDistOn w S (P₁ 0) (P₃ 1) ≤
      weightedLength w P₁ 0 1 + weightedLength w P₂ 0 1 + weightedLength w P₃ 0 1 := by
  calc weylDistOn w S (P₁ 0) (P₃ 1)
      ≤ weylDistOn w S (P₁ 0) (P₂ 1) + weylDistOn w S (P₂ 1) (P₃ 1) := weylDistOn_triangle _ _ _
    _ ≤ (weylDistOn w S (P₁ 0) (P₁ 1) + weylDistOn w S (P₁ 1) (P₂ 1)) +
          weylDistOn w S (P₂ 1) (P₃ 1) := add_le_add (weylDistOn_triangle _ _ _) le_rfl
    _ ≤ weightedLength w P₁ 0 1 + weightedLength w P₂ 0 1 + weightedLength w P₃ 0 1 := by
        gcongr
        · exact weylDistOn_le h1 rfl rfl hS1
        · rw [h12]
          exact weylDistOn_le h2 rfl rfl hS2
        · rw [h23]
          exact weylDistOn_le h3 rfl rfl hS3

/-- **[S] Lemma 4.2′ for the base configuration** (MA1 A17: construction of the index `N`,
(i) and (ii) for `ξ₀`), metric form. The distance of `Z` is the base coordinate `ζ`; `E` is the
comparison coordinate `ζ̃ ≤ M ζ`; `w n` are the weights `e^{-ξ f_n}` of the construction (here
abstract: the collapse properties of MA1 A13 and `w n = 1` off `V`). -/
theorem trap_base {Z I : Type*} [MetricSpace Z] [Fintype I]
    {A V K : Set Z} (hA : IsOpen A) (hAc : IsCompact (closure A)) (hV : IsOpen V)
    (hVA : closure V ⊆ A) (hK : IsFiniteRectGraph K) (hKV : K ⊆ V)
    {acol b ε₀ a₀ : ℝ} (ha₀ : 0 < a₀)
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, 4 * acol ≤ dist x y)
    (hb : 0 < b) (hε₀ : 0 < ε₀) (hε₀b : ε₀ < a₀ * b / 200) (hε₀col : ε₀ < acol / 12)
    (haccess : ∀ x ∈ closure V, ∃ P : ℝ → Z, ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧ P 1 ∈ K ∧
      curveLength P 0 1 ≤ ENNReal.ofReal ε₀)
    (hreal : ∃ a : ℝ, 0 < a ∧ ∀ p ∈ trapSet A V acol, ∀ q ∈ trapSet A V acol, dist p q < a →
      ∃ R : ℝ → Z, ContinuousOn R (Icc 0 1) ∧ R 0 = p ∧ R 1 = q ∧
        MapsTo R (Icc 0 1) (closure A) ∧ curveLength R 0 1 = edist p q)
    (E : Z → Z → ℝ≥0∞) (hEtri : ∀ p q r, E p r ≤ E p q + E q r)
    (hEsymm : ∀ p q, E p q = E q p)
    {M : ℝ} (hM : 0 < M) (hEM : ∀ p q, E p q ≤ ENNReal.ofReal M * edist p q)
    (σ : I → ℝ → Z) (hσc : ∀ i, ContinuousOn (σ i) (Icc 0 1))
    (hσK : ∀ i, MapsTo (σ i) (Icc 0 1) K)
    {c₀ c' a₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₀c' : c₀ < c') (ha₁ : 0 < a₁)
    (hσlen : ∀ i, curveLengthWith E (σ i) 0 1 ≤ ENNReal.ofReal c₀ * edist (σ i 0) (σ i 1))
    (hσsep : ∀ i, a₁ ≤ dist (σ i 0) (σ i 1))
    (hforce : ∀ (T : ℝ) (hT : 0 ≤ T), TrapForcing K σ (b / 4) T hT)
    {lam eta : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n) (hlam : Tendsto lam atTop (𝓝 0))
    (heta0 : ∀ n, 0 < eta n) (heta : Tendsto (fun n => eta n / lam n) atTop (𝓝 0))
    (w : ℕ → Z → ℝ) (hw : ∀ n, Continuous (w n)) (hw1 : ∀ n p, lam n ≤ w n p ∧ w n p ≤ 1)
    (hwK : ∀ n, ∀ p ∈ K, w n p = lam n)
    (hwoff : ∀ n p, eta n ≤ Metric.infDist p K → a₀ ≤ w n p)
    (hwV : ∀ n p, p ∉ V → w n p = 1) :
    ∃ N : ℕ, ∃ c ĉ ηs L₀ : ℝ, 0 < c ∧ c₀ < ĉ ∧ ĉ < c' ∧ 0 < ηs ∧ ηs ≤ ε₀ ∧ 0 ≤ L₀ ∧
      (∀ x ∈ closure V, ∀ y ∈ closure V, ∃ P₁ P₂ P₃ : ℝ → Z,
        (ContinuousOn P₁ (Icc 0 1) ∧ MapsTo P₁ (Icc 0 1) (trapSet A V (acol / 2)) ∧
          curveLength P₁ 0 1 ≤ ENNReal.ofReal L₀) ∧
        (ContinuousOn P₂ (Icc 0 1) ∧ MapsTo P₂ (Icc 0 1) (trapSet A V (acol / 2)) ∧
          curveLength P₂ 0 1 ≤ ENNReal.ofReal L₀) ∧
        (ContinuousOn P₃ (Icc 0 1) ∧ MapsTo P₃ (Icc 0 1) (trapSet A V (acol / 2)) ∧
          curveLength P₃ 0 1 ≤ ENNReal.ofReal L₀) ∧
        P₁ 0 = x ∧ P₁ 1 = P₂ 0 ∧ P₂ 1 = P₃ 0 ∧ P₃ 1 = y ∧
        weightedLength (w N) P₁ 0 1 + weightedLength (w N) P₂ 0 1 +
          weightedLength (w N) P₃ 0 1 ≤ ENNReal.ofReal (3 * ε₀ - 2 * ηs)) ∧
      (∀ Q : ℝ → Z, ContinuousOn Q (Icc 0 1) → Q 0 ∈ closure V → Q 1 ∈ closure V →
        weightedLength (w N) Q 0 1 = weylDistOn (w N) univ (Q 0) (Q 1) →
        b / 2 ≤ dist (Q 0) (Q 1) →
        ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧
          ENNReal.ofReal (2 * c) ≤ weightedLength (w N) Q u v ∧
          ∃ S : ℝ → Z, ContinuousOn S (Icc 0 1) ∧ S 0 = Q u ∧ S 1 = Q v ∧
            MapsTo S (Icc 0 1) (trapSet A V acol) ∧
            weightedLengthWith E (w N) S 0 1 ≤ ENNReal.ofReal ĉ * weightedLength (w N) Q u v) := by
  have hacol : 0 < acol := by linarith
  have hKc : IsCompact K := hK.isCompact
  have hKne : K.Nonempty := trap_graph_nonempty hK
  obtain ⟨D, hD0, hD⟩ := trap_graph_bound hK
  obtain ⟨a, ha, hrealA⟩ := hreal
  set Y := trapSet A V acol with hY_def
  have hYc : IsCompact Y := isCompact_trapSet hAc
  have hKY : K ⊆ Y := fun p hp => closure_subset_trapSet hVA hacol.le (subset_closure (hKV hp))
  set δ := min a acol with hδ_def
  have hδ : 0 < δ := lt_min ha hacol
  -- realization from `Y` to `K` inside `Y`
  have hrealY : ∀ p ∈ Y, ∀ q ∈ K, dist p q < δ → ∃ R : ℝ → Z, ContinuousOn R (Icc 0 1) ∧
      R 0 = p ∧ R 1 = q ∧ MapsTo R (Icc 0 1) Y ∧ curveLength R 0 1 = edist p q := by
    intro p hp q hq hpq
    obtain ⟨R, hRc, hR0, hR1, hRA, hRlen⟩ :=
      hrealA p hp q (hKY hq) (hpq.trans_le (min_le_left _ _))
    refine ⟨R, hRc, hR0, hR1, fun τ hτ => ⟨hRA hτ, ?_⟩, hRlen⟩
    have h1 : edist (R τ) (R 1) ≤ curveLength R τ 1 := edist_le_curveLength R hτ.2
    have h2 : curveLength R τ 1 ≤ curveLength R 0 1 := curveLength_mono R hτ.1 le_rfl
    have h3 : edist (R τ) q ≤ edist p q := by
      calc edist (R τ) q = edist (R τ) (R 1) := by rw [hR1]
        _ ≤ curveLength R τ 1 := h1
        _ ≤ curveLength R 0 1 := h2
        _ = edist p q := hRlen
    rw [edist_dist, edist_dist] at h3
    have h4 : dist (R τ) q ≤ dist p q := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1 h3
    show Metric.infDist (R τ) (closure V) ≤ acol
    calc Metric.infDist (R τ) (closure V) ≤ dist (R τ) q :=
          Metric.infDist_le_dist_of_mem (subset_closure (hKV hq))
      _ ≤ dist p q := h4
      _ ≤ acol := hpq.le.trans (min_le_right _ _)
  -- the ratio `ĉ` and the horizon `T`
  set ĉ := (c₀ + c') / 2 with hĉ_def
  have hc₀ĉ : c₀ < ĉ := by rw [hĉ_def]; linarith
  have hĉc' : ĉ < c' := by rw [hĉ_def]; linarith
  set T := D + 1 with hT_def
  have hT : 0 ≤ T := by positivity
  -- S1c's uniform shortcut transfer
  have hev := lemma32_shortcut Y K hYc hKc hKY (fun p hp q hq => hK.internal_finite hp hq)
    hK.continuousOn_internal δ hδ hrealY lam eta hlam0 hlam heta0 heta a₀ ha₀ w hw hw1 hwK
    hwoff T hT (b / 4) E (fun p _ q _ r _ => hEtri p q r) (fun p _ q _ => hEsymm p q) M hM
    (fun p _ q _ => hEM p q) σ hσc hσK c₀ ĉ a₁ hc₀ hc₀ĉ ha₁ hσlen hσsep (hforce T hT)
  have hev2 : ∀ᶠ n in atTop, lam n * D ≤ ε₀ / 2 := by
    have h : Tendsto (fun n => lam n * D) atTop (𝓝 0) := by
      simpa using hlam.mul_const D
    exact h.eventually (ge_mem_nhds (by positivity))
  have hev3 : ∀ᶠ n in atTop, eta n / lam n ≤ 1 / 2 :=
    heta.eventually (ge_mem_nhds (by norm_num))
  have hev4 : ∀ᶠ n in atTop, eta n < δ := by
    have h : Tendsto eta atTop (𝓝 0) := by
      have h0 := heta.mul hlam
      rw [zero_mul] at h0
      refine h0.congr' (Eventually.of_forall fun n => ?_)
      field_simp [(hlam0 n).ne']
    exact h.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN1, hN2, hN3, hN4⟩ := (hev.and (hev2.and (hev3.and hev4))).exists
  -- (i) for the base configuration: the pieces
  set ηs := ε₀ / 4 with hηs_def
  set L₀ := ε₀ + D with hL₀_def
  have hcolhalf : ∀ x ∈ closure V, ∀ y ∈ frontier A, acol / 2 ≤ dist x y :=
    fun x hx y hy => le_trans (by linarith) (hcol x hx y hy)
  have hpieces : ∀ x ∈ closure V, ∀ y ∈ closure V, ∃ P₁ P₂ P₃ : ℝ → Z,
      (ContinuousOn P₁ (Icc 0 1) ∧ MapsTo P₁ (Icc 0 1) (trapSet A V (acol / 2)) ∧
        curveLength P₁ 0 1 ≤ ENNReal.ofReal L₀) ∧
      (ContinuousOn P₂ (Icc 0 1) ∧ MapsTo P₂ (Icc 0 1) (trapSet A V (acol / 2)) ∧
        curveLength P₂ 0 1 ≤ ENNReal.ofReal L₀) ∧
      (ContinuousOn P₃ (Icc 0 1) ∧ MapsTo P₃ (Icc 0 1) (trapSet A V (acol / 2)) ∧
        curveLength P₃ 0 1 ≤ ENNReal.ofReal L₀) ∧
      P₁ 0 = x ∧ P₁ 1 = P₂ 0 ∧ P₂ 1 = P₃ 0 ∧ P₃ 1 = y ∧
      weightedLength (w N) P₁ 0 1 + weightedLength (w N) P₂ 0 1 +
        weightedLength (w N) P₃ 0 1 ≤ ENNReal.ofReal (3 * ε₀ - 2 * ηs) := by
    intro x hx y hy
    obtain ⟨P, hPc, hP0, hP1, hPlen⟩ := haccess x hx
    obtain ⟨P', hP'c, hP'0, hP'1, hP'len⟩ := haccess y hy
    obtain ⟨G, hGc, hG0, hG1, hGK, hGlen⟩ := trap_graph_curve hK hP1 hP'1
    have hPY : MapsTo P (Icc 0 1) (trapSet A V (acol / 2)) :=
      trap_access_mapsTo hA hV hVA (by positivity) (by linarith) hcolhalf hPc (hP0 ▸ hx) hPlen
    have hP'Y : MapsTo P' (Icc 0 1) (trapSet A V (acol / 2)) :=
      trap_access_mapsTo hA hV hVA (by positivity) (by linarith) hcolhalf hP'c (hP'0 ▸ hy) hP'len
    have hKY2 : K ⊆ trapSet A V (acol / 2) :=
      fun p hp => closure_subset_trapSet hVA (by positivity) (subset_closure (hKV hp))
    have hrefl : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) :=
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
    set P₃ : ℝ → Z := fun t => P' (1 - t) with hP₃_def
    have hP₃c : ContinuousOn P₃ (Icc 0 1) :=
      hP'c.comp (continuous_const.sub continuous_id).continuousOn hrefl
    have hP₃len : curveLength P₃ 0 1 = curveLength P' 0 1 := by
      have h := curveLengthWith_reflect_of_symm (E := edist) (Y := univ) (arc := P')
        (fun p _ q _ => edist_comm p q) (mapsTo_univ _ _)
      rwa [curveLengthWith_edist, curveLengthWith_edist] at h
    have hP₃wl : weightedLength (w N) P₃ 0 1 = weightedLength (w N) P' 0 1 := by
      simpa using weightedLength_comp_reflect (w := w N) (P := P') 0 1
    have hcostP : ∀ R : ℝ → Z, curveLength R 0 1 ≤ ENNReal.ofReal ε₀ →
        weightedLength (w N) R 0 1 ≤ ENNReal.ofReal ε₀ := by
      intro R hR
      calc weightedLength (w N) R 0 1 ≤ ENNReal.ofReal 1 * curveLength R 0 1 :=
            weightedLength_le_ofReal_mul_curveLength fun t _ => (hw1 N (R t)).2
        _ ≤ ENNReal.ofReal ε₀ := by rw [ENNReal.ofReal_one, one_mul]; exact hR
    have hGlenD : curveLength G 0 1 ≤ ENNReal.ofReal D := hGlen ▸ hD _ hP1 _ hP'1
    have hcostG : weightedLength (w N) G 0 1 ≤ ENNReal.ofReal (lam N * D) := by
      calc weightedLength (w N) G 0 1 ≤ ENNReal.ofReal (lam N) * curveLength G 0 1 :=
            weightedLength_le_ofReal_mul_curveLength fun t ht => (hwK N _ (hGK ht)).le
        _ ≤ ENNReal.ofReal (lam N) * ENNReal.ofReal D := mul_le_mul' le_rfl hGlenD
        _ = ENNReal.ofReal (lam N * D) := (ENNReal.ofReal_mul (hlam0 N).le).symm
    have hL₀ε : ENNReal.ofReal ε₀ ≤ ENNReal.ofReal L₀ :=
      ENNReal.ofReal_le_ofReal (by rw [hL₀_def]; linarith)
    have hL₀D : ENNReal.ofReal D ≤ ENNReal.ofReal L₀ :=
      ENNReal.ofReal_le_ofReal (by rw [hL₀_def]; linarith)
    refine ⟨P, G, P₃, ⟨hPc, hPY, hPlen.trans hL₀ε⟩, ⟨hGc, hGK.mono_right hKY2, hGlenD.trans hL₀D⟩,
      ⟨hP₃c, hP'Y.comp hrefl, hP₃len ▸ hP'len.trans hL₀ε⟩, hP0, hG0.symm, ?_, ?_, ?_⟩
    · rw [hG1]
      show P' 1 = P' (1 - 0)
      rw [sub_zero]
    · show P' (1 - 1) = y
      rw [sub_self, hP'0]
    · rw [hP₃wl]
      calc weightedLength (w N) P 0 1 + weightedLength (w N) G 0 1 + weightedLength (w N) P' 0 1
          ≤ ENNReal.ofReal ε₀ + ENNReal.ofReal (lam N * D) + ENNReal.ofReal ε₀ :=
            add_le_add (add_le_add (hcostP P hPlen) hcostG) (hcostP P' hP'len)
        _ = ENNReal.ofReal (ε₀ + lam N * D + ε₀) := by
            have hlamD : 0 ≤ lam N * D := mul_nonneg (hlam0 N).le hD0
            rw [ENNReal.ofReal_add (add_nonneg hε₀.le hlamD) hε₀.le,
              ENNReal.ofReal_add hε₀.le hlamD]
        _ ≤ ENNReal.ofReal (3 * ε₀ - 2 * ηs) :=
            ENNReal.ofReal_le_ofReal (by rw [hηs_def]; linarith)
  -- the distance bound `(i)` used by the minimizer argument
  have hi : ∀ x ∈ closure V, ∀ y ∈ closure V,
      weylDistOn (w N) univ x y < ENNReal.ofReal (3 * ε₀) := by
    intro x hx y hy
    obtain ⟨P₁, P₂, P₃, ⟨h1c, -, -⟩, ⟨h2c, -, -⟩, ⟨h3c, -, -⟩, h10, h12, h23, h31, hsum⟩ :=
      hpieces x hx y hy
    have h := trap_weylDistOn_le_three (w := w N) (S := univ) h1c h2c h3c (mapsTo_univ _ _)
      (mapsTo_univ _ _) (mapsTo_univ _ _) h12 h23
    rw [h10, h31] at h
    exact (h.trans hsum).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by rw [hηs_def]; linarith))
  -- the horizon bounds every normalized confined distance in the tube
  have hLT : ∀ x ∈ Y, ∀ y ∈ Y, Metric.infDist x K ≤ eta N → Metric.infDist y K ≤ eta N →
      ((ENNReal.ofReal (lam N))⁻¹ * weylDistOn (w N) Y x y).toReal ≤ T := by
    intro x hx y hy hxK hyK
    obtain ⟨u, hu, hxu⟩ := hKc.exists_infDist_eq_dist hKne x
    obtain ⟨v, hv, hyv⟩ := hKc.exists_infDist_eq_dist hKne y
    have hrec := collapse_recovery_bound hKY hrealY (fun z => (hw1 N z).2) (hlam0 N) (hwK N)
      hx hy hu hv (hxu ▸ hxK) (hyv ▸ hyK) hN4
    have hnorm := normalized_recovery_real_le (hlam0 N) (heta0 N).le
      (hK.internal_finite hu hv) hrec
    have hd : (internalEDist K u v).toReal ≤ D :=
      ENNReal.toReal_le_of_le_ofReal hD0 (hD u hu v hv)
    rw [hT_def]
    linarith
  -- (ii) for the base configuration
  have hii := trap_base_ii hA hV hVA hKc hKne ha₀ hcol hb hε₀ hε₀b hε₀col (hlam0 N) (hw N)
    (fun p => (hw1 N p).1) (hwoff N) (hwV N) hLT hi E hN1
  refine ⟨N, lam N * a₁ / 4, ĉ, ηs, L₀, by have := hlam0 N; positivity, hc₀ĉ, hĉc',
    by positivity, by rw [hηs_def]; linarith, by positivity, hpieces, ?_⟩
  intro Q hQc hQ0 hQ1 hmin hsep
  obtain ⟨u, v, hu, huv, hv, hcost, S, hSc, hS0, hS1, hSY, hSb⟩ := hii Q hQc hQ0 hQ1 hmin hsep
  refine ⟨u, v, hu, huv, hv, ?_, S, hSc, hS0, hS1, hSY, hSb⟩
  convert hcost using 2
  ring

end HigherDimLQGMetric
