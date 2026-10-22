import HigherDimLQGMetric.Metric.WeylBasic

/-!
# The Weyl-scaled metric `e^{ξ f}·D` on `ℝ^d`: internal metrics, the continuous metric, lengths

Packet M1 (Phase A, block A2). Port of LQGMetric's ℂ-typed `Metric/WeylLength.lean`,
`Metric/WeylCont.lean`, `Metric/WeylMetric.lean`, `Metric/WeylPathLength.lean` and
`Metric/WeylLocal.lean` from `ℂ` to `Rd d` (ruling M10).

Let `D, D'` be continuous metrics with `D' = e^{ξ f}·D` (the frozen `weylScale`; for a metric
assignment `D' = D_{h+f}` by Axiom (III)).

* **Internal metrics** (`weylScaleOn_eq_internal`): for every open `U`, `D'(·,·;U)` is the Weyl
  infimum over `D`-length-parametrized paths in `U`; hence `D'(·,·;U) = e^c D(·,·;U)` if
  `ξ f ≡ c` on `U` (`internal_eq_of_eq_const`) and the **comparison on internal metrics**
  `e^a D(·,·;U) ≤ D'(·,·;U) ≤ e^b D(·,·;U)` when `a ≤ ξ f ≤ b` on `U` (`internal_mem_Icc_of_le`);
  `D'` is a length metric (`isLength_of_eq_weylScale`).
* **The continuous metric** `weylMetric ξ f D hD` (for a length metric `D`):
  `weylMetric_spec` (`= e^{ξ f}·D`), `weylMetric_isLength`, `weylMetric_internal`; finiteness
  (`weylScale_ne_top`), the local bound (`exists_weylScale_le_near`) and the Euclidean topology
  (`weylScale_euclidean_of_small`).
* **Lengths**: `len(P; D') ≤ e^b len(P; D)` if `ξ f ≤ b` along `P` (`curveLength_weyl_le`) and
  `e^a len(P; D) ≤ len(P; D')` if `a ≤ ξ f` on an open set containing `P` (`le_curveLength_weyl`).
* **Locality**: `(e^{ξ f}·D)(·,·;U)` depends only on `D(·,·;U)` and `ξ f|_U`
  (`weylScaleOn_eq_of_internal_eq`, `internal_weyl_eq_of_internal_eq`).

Own elementary proofs, as in the 2D layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

section Internal

variable {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d} {U : Set (Rd d)}

/-- A length-parametrized path leaving the open set `V` (on which `ξ f ≥ a`) has Weyl cost at
least `e^a D(P 0, Vᶜ)`. -/
theorem le_weylCost_of_exit {L : ℝ} {P : ℝ → Rd d} (hL : 0 ≤ L)
    (hc : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L))
    {V : Set (Rd d)} (hV : IsOpen V) {a : ℝ} (ha : ∀ x ∈ V, a ≤ ξ * f x)
    (hexit : ∃ t ∈ Icc 0 L, P t ∉ V) :
    ENNReal.ofReal (Real.exp a) * infEDist (D.pt (P 0)) (D.pt '' Vᶜ) ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  have hcP : ContinuousOn P (Icc 0 L) := D.continuousOn_pt_comp_iff.1 hc
  set S := Icc 0 L ∩ P ⁻¹' Vᶜ
  have hS : IsClosed S := hcP.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl
  obtain ⟨t, ht, htV⟩ := hexit
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hmem := hS.csInf_mem ⟨t, ht, htV⟩ hbdd
  set s₀ := sInf S
  have hbefore : ∀ τ ∈ Ico 0 s₀, P τ ∈ V := fun τ hτ => by
    by_contra hτV
    exact absurd hτ.2 (not_lt.2 (csInf_le hbdd ⟨⟨hτ.1, hτ.2.le.trans hmem.1.2⟩, hτV⟩))
  calc ENNReal.ofReal (Real.exp a) * infEDist (D.pt (P 0)) (D.pt '' Vᶜ)
      ≤ ENNReal.ofReal (Real.exp a) * ENNReal.ofReal s₀ := by
        gcongr
        refine (infEDist_le_edist_of_mem (y := D.pt (P s₀))
          (⟨P s₀, hmem.2, rfl⟩ : D.pt (P s₀) ∈ D.pt '' Vᶜ)).trans ?_
        have := edist_le_curveLength (D.pt ∘ P) hmem.1.1
        rw [curveLength_of_hasUnitSpeedOn hu ⟨le_rfl, hL⟩ hmem.1, sub_zero] at this
        exact this
    _ = ∫⁻ _ in Ico 0 s₀, ENNReal.ofReal (Real.exp a) := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero]
    _ ≤ ∫⁻ t in Ico 0 s₀, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        setLIntegral_mono' measurableSet_Ico fun τ hτ =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (ha _ (hbefore τ hτ)))
    _ ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        lintegral_mono_set (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hmem.1.2))

/-- Near-optimal paths of small cost started at `x` stay in `V ⊆ U`, so
`(e^{ξ f}·D)_U(x, y) ≤ (e^{ξ f}·D)(x, y)` when the latter is `< e^a D(x, Vᶜ)`. -/
theorem weylScaleOn_le_weylScale_of_lt {V : Set (Rd d)} (hV : IsOpen V) (hVU : V ⊆ U) {a : ℝ}
    (ha : ∀ x ∈ V, a ≤ ξ * f x) {x y : Rd d}
    (hlt : weylScale ξ f D x y < ENNReal.ofReal (Real.exp a) * infEDist (D.pt x) (D.pt '' Vᶜ)) :
    weylScaleOn ξ f D U x y ≤ weylScale ξ f D x y := by
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  have hlt' := lt_min hc hlt
  simp only [weylScale, iInf_lt_iff] at hlt'
  obtain ⟨L, P, hL, hcP, hu, h0, h1, hcost⟩ := hlt'
  have hin : ∀ t ∈ Icc 0 L, P t ∈ U := by
    intro t ht
    by_contra htU
    have := le_weylCost_of_exit hL hcP hu hV ha ⟨t, ht, fun h => htU (hVU h)⟩
    rw [h0] at this
    exact lt_irrefl _ (this.trans_lt (hcost.trans_le (min_le_right _ _)))
  exact (weylScaleOn_le hL hcP hu h0 h1 hin).trans (hcost.trans_le (min_le_left _ _)).le

variable (D' : ContMetric d)
  (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
include hD'

/-- `≤`: the `D'`-internal metric is at most the Weyl cost of any admissible path in `U`. -/
theorem internal_le_weylScaleOn (z w : Rd d) : D'.internal U z w ≤ weylScaleOn ξ f D U z w := by
  refine le_weylScaleOn fun L P hL hc hu h0 h1 hU => ?_
  have hcP : ContinuousOn P (Icc 0 L) := D.continuousOn_pt_comp_iff.1 hc
  have hc' : ContinuousOn (D'.pt ∘ P) (Icc 0 L) := D'.continuousOn_pt_comp_iff.2 hcP
  have hlen : curveLength (D'.pt ∘ P) 0 L ≤
      ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
    refine eVariationOn_le_lintegral fun s t hs hst ht => ?_
    rw [setLIntegral_congr Ioc_ae_eq_Icc]
    show edist (D'.pt (P s)) (D'.pt (P t)) ≤ _
    rw [edist_dist]
    refine le_of_eq_of_le (hD' (P s) (P t)) ?_
    rw [← weylScaleOn_univ]
    exact weylScaleOn_le_sub hu (fun _ _ => mem_univ _) hs hst ht
  obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hL hc'
  rw [← h0, ← h1]
  refine (internalEDist_le_pathLength γ fun t => ?_).trans (hγ.trans_le hlen)
  obtain ⟨s, hs, hst⟩ := hrange (mem_range_self t)
  exact ⟨P s, hU s hs, hst⟩

/-- `≥`: Weyl cost with paths in the open set `U` is at most the `D'`-internal metric on `U`. -/
theorem weylScaleOn_le_internal (hU : IsOpen U) (z w : Rd d) :
    weylScaleOn ξ f D U z w ≤ D'.internal U z w := by
  unfold ContMetric.internal internalEDist
  refine le_iInf fun γ' => ?_
  obtain ⟨γ, hγU⟩ := γ'
  by_cases hfin : pathLength γ = ∞
  · rw [hfin]; exact le_top
  -- the range of `γ` in `ℝ^d`, a compact subset of a bounded open `V ⊆ U`
  set g : unitInterval → Rd d := fun t => D'.unpt (γ t)
  have hg : Continuous g := D'.continuous_unpt.comp γ.continuous
  have hK : IsCompact (range g) := isCompact_range hg
  have hKU : range g ⊆ U := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨x, hx, hxt⟩ := hγU t
    have : x = g t := hxt
    exact this ▸ hx
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  set V := U ∩ ball (0 : Rd d) R
  have hV : IsOpen V := hU.inter isOpen_ball
  have hKV : range g ⊆ V := fun x hx => ⟨hKU hx, hR hx⟩
  obtain ⟨a, ha⟩ : ∃ a, ∀ x ∈ V, a ≤ ξ * f x := by
    obtain ⟨a, ha⟩ := (isCompact_closedBall (0 : Rd d) R).bddBelow_image
      (f := fun x => ξ * f x) (by fun_prop : Continuous fun x => ξ * f x).continuousOn
    exact ⟨a, fun x hx => ha ⟨x, ball_subset_closedBall hx.2, rfl⟩⟩
  -- `ρ = min_{range γ} D(·, Vᶜ) > 0`
  set Φ : Rd d → ℝ≥0∞ := fun x => infEDist (D.pt x) (D.pt '' Vᶜ)
  have hΦc : Continuous Φ := continuous_infEDist.comp D.continuous_pt
  have hclosed : IsClosed (D.pt '' Vᶜ) := D.isClosed_pt_image_compl hV
  have hΦpos : ∀ x ∈ V, 0 < Φ x := fun x hx => by
    refine infEDist_pos_iff_notMem_closure.2 ?_
    rw [hclosed.closure_eq]
    rintro ⟨y, hy, hyx⟩
    have : y = x := hyx
    exact hy (this ▸ hx)
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ∀ x ∈ range g, ρ ≤ Φ x := by
    obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn (range_nonempty g) hΦc.continuousOn
    exact ⟨Φ x0, hΦpos x0 (hKV hx0), fun x hx => hmin hx⟩
  set η := ENNReal.ofReal (Real.exp a) * ρ
  have hη : 0 < η := ENNReal.mul_pos (by simpa using Real.exp_pos a) hρpos.ne'
  -- uniform continuity of `γ` and a fine subdivision `u i = min (i / n) 1`
  have huc : UniformContinuousOn γ.extend (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous γ.continuous_extend.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := EMetric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hδ.ne'
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn0)
  set u : ℕ → ℝ := fun i => min ((i : ℝ) / n) 1
  have humono : Monotone u := fun i j hij =>
    min_le_min_right _ (div_le_div_of_nonneg_right (Nat.cast_le.2 hij) hnpos.le)
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (div_nonneg (Nat.cast_nonneg i) hnpos.le) zero_le_one, min_le_right _ _⟩
  have hu0 : u 0 = 0 := by simp [u]
  have hun : u n = 1 := by simp [u, div_self hnpos.ne']
  have hstep : ∀ i, edist (u i) (u (i + 1)) < δ := by
    intro i
    refine lt_of_le_of_lt ?_ hn
    rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hnpos]
    refine ENNReal.ofReal_le_ofReal ((abs_min_sub_min_le_max _ _ _ _).trans ?_)
    rw [sub_self, abs_zero, Nat.cast_succ, ← sub_div, sub_add_cancel_left, abs_div, abs_neg,
      abs_one, abs_of_pos hnpos, one_div]
    exact max_le le_rfl (inv_nonneg.2 hnpos.le)
  set q : ℕ → Rd d := fun i => D'.unpt (γ.extend (u i))
  have hq : ∀ i, q i ∈ range g := fun i => ⟨⟨u i, humem i⟩, by
    simp only [g, q, Path.extend_extends' γ ⟨u i, humem i⟩]⟩
  have hq0 : q 0 = z := by simp only [q, hu0, Path.extend_zero]; rfl
  have hqn : q n = w := by simp only [q, hun, Path.extend_one]; rfl
  have hDq : ∀ i, weylScale ξ f D (q i) (q (i + 1)) =
      edist (γ.extend (u (i + 1))) (γ.extend (u i)) := by
    intro i
    rw [← hD', edist_comm, edist_dist]
    rfl
  calc weylScaleOn ξ f D U z w = weylScaleOn ξ f D U (q 0) (q n) := by rw [hq0, hqn]
    _ ≤ ∑ i ∈ Finset.range n, weylScaleOn ξ f D U (q i) (q (i + 1)) :=
        weylScaleOn_le_sum q (hKU (hq 0)) n
    _ ≤ ∑ i ∈ Finset.range n, weylScale ξ f D (q i) (q (i + 1)) := by
        refine Finset.sum_le_sum fun i _ => weylScaleOn_le_weylScale_of_lt hV inter_subset_left
          ha ?_
        rw [hDq, edist_comm]
        refine (hδ' (humem i) (humem (i + 1)) (hstep i)).trans_le ?_
        show ENNReal.ofReal (Real.exp a) * ρ ≤ ENNReal.ofReal (Real.exp a) * Φ (q i)
        exact mul_le_mul' le_rfl (hρ _ (hq i))
    _ = ∑ i ∈ Finset.range n, edist (γ.extend (u (i + 1))) (γ.extend (u i)) :=
        Finset.sum_congr rfl fun i _ => hDq i
    _ ≤ eVariationOn γ.extend (Icc 0 1) := eVariationOn.sum_le humono humem
    _ = pathLength γ := rfl

/-- **Internal metrics of `e^{ξ f}·D`**: if the continuous metric `D'` equals `e^{ξ f}·D`, then
for every open `U`, `D'(·,·;U)` is the Weyl infimum over length-parametrized paths in `U`. -/
theorem weylScaleOn_eq_internal (hU : IsOpen U) (z w : Rd d) :
    weylScaleOn ξ f D U z w = D'.internal U z w :=
  le_antisymm (weylScaleOn_le_internal D' hD' hU z w) (internal_le_weylScaleOn D' hD' z w)

/-- If `D' = e^{ξ f}·D` and `ξ f ≡ c` on the open set `U`, then `D'(·,·;U) = e^c D(·,·;U)`. -/
theorem internal_eq_of_eq_const (hU : IsOpen U) {c : ℝ} (hf : ∀ x ∈ U, ξ * f x = c)
    (z w : Rd d) :
    D'.internal U z w = ENNReal.ofReal (Real.exp c) * D.internal U z w := by
  rw [← weylScaleOn_eq_internal D' hD' hU, weylScaleOn_of_eq_const hf]

/-- **Comparison on internal metrics**: `a ≤ ξ f ≤ b` on the open set `U` ⇒
`e^a D(·,·;U) ≤ D'(·,·;U) ≤ e^b D(·,·;U)`. -/
theorem internal_mem_Icc_of_le (hU : IsOpen U) {a b : ℝ} (ha : ∀ x ∈ U, a ≤ ξ * f x)
    (hb : ∀ x ∈ U, ξ * f x ≤ b) (z w : Rd d) :
    ENNReal.ofReal (Real.exp a) * D.internal U z w ≤ D'.internal U z w ∧
      D'.internal U z w ≤ ENNReal.ofReal (Real.exp b) * D.internal U z w := by
  rw [← weylScaleOn_eq_internal D' hD' hU]
  exact ⟨le_weylScaleOn_of_le ha, weylScaleOn_le_of_le hb⟩

/-- `e^{ξ f}·D` is a length metric whenever it is a continuous metric. -/
theorem isLength_of_eq_weylScale : D'.IsLength := by
  rw [ContMetric.isLength_iff_internal_univ]
  intro z w
  rw [hD', ← weylScaleOn_univ]
  exact (weylScaleOn_eq_internal D' hD' isOpen_univ z w).symm

end Internal

/-! ### Finiteness, local bounds, the Euclidean topology -/

section Cont

variable {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d}

/-- Weyl cost along a path on which `ξ f ≤ b`. -/
theorem weylScale_le_of_path {z w : Rd d} (γ : Path (D.pt z) (D.pt w)) {b : ℝ}
    (hb : ∀ t, ξ * f (D.unpt (γ t)) ≤ b) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp b) * pathLength γ := by
  calc weylScale ξ f D z w ≤ weylScaleOn ξ f D {x | ξ * f x ≤ b} z w := weylScale_le_weylScaleOn
    _ ≤ ENNReal.ofReal (Real.exp b) * D.internal {x | ξ * f x ≤ b} z w :=
        weylScaleOn_le_of_le fun x hx => hx
    _ ≤ ENNReal.ofReal (Real.exp b) * pathLength γ := by
        gcongr
        exact internalEDist_le_pathLength γ fun t => ⟨D.unpt (γ t), hb t, rfl⟩

/-- For a length metric, `e^{ξ f}·D` is finite. -/
theorem weylScale_ne_top (hD : D.IsLength) (z w : Rd d) : weylScale ξ f D z w ≠ ∞ := by
  obtain ⟨γ, hγ⟩ := hD (D.pt z) (D.pt w) 1 one_pos
  have hK : IsCompact (range fun t => D.unpt (γ t)) :=
    isCompact_range (D.continuous_unpt.comp γ.continuous)
  obtain ⟨b, hb⟩ := (hK.image (by fun_prop : Continuous fun x => ξ * f x)).bddAbove
  refine ne_top_of_le_ne_top ?_ (weylScale_le_of_path γ (b := b) fun t => hb ⟨_, ⟨t, rfl⟩, rfl⟩)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨edist_ne_top _ _, ENNReal.ofReal_ne_top⟩) hγ)

/-- Local Lipschitz-type bound near `z`. -/
theorem exists_weylScale_le_near (hD : D.IsLength) (z : Rd d) :
    ∃ r > 0, ∃ b : ℝ, ∀ z', D.1 (z, z') < r →
      weylScale ξ f D z z' ≤ ENNReal.ofReal (Real.exp b) * ENNReal.ofReal (2 * D.1 (z, z')) := by
  obtain ⟨δ, hδ, hsmall⟩ := D.2.euclidean_of_small z 1 one_pos
  obtain ⟨b, hb⟩ := ((isCompact_closedBall z 1).image
    (by fun_prop : Continuous fun x => ξ * f x)).bddAbove
  refine ⟨δ / 2, half_pos hδ, b, fun z' hz' => ?_⟩
  have hnn : 0 ≤ D.1 (z, z') := D.nonneg z z'
  rcases hnn.eq_or_lt with h0 | hpos
  · have : z = z' := D.2.eq_of_eq_zero z z' h0.symm
    subst this
    rw [weylScale_self]; exact bot_le
  obtain ⟨γ, hγ⟩ := hD (D.pt z) (D.pt z') (D.1 (z, z')) hpos
  have hlen : pathLength γ ≤ ENNReal.ofReal (2 * D.1 (z, z')) := by
    refine hγ.trans (le_of_eq ?_)
    rw [edist_dist, show dist (D.pt z) (D.pt z') = D.1 (z, z') from rfl,
      ← ENNReal.ofReal_add hnn hnn, two_mul]
  have hrange : ∀ t, ξ * f (D.unpt (γ t)) ≤ b := by
    intro t
    refine hb ⟨_, ?_, rfl⟩
    have h1 := (LQGMetric.edist_le_pathLength_apply' γ t).trans hlen
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by linarith)] at h1
    have h2 : D.1 (z, D.unpt (γ t)) < δ := lt_of_le_of_lt h1 (by linarith)
    have h3 := hsmall _ h2
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h3.le
  exact (weylScale_le_of_path γ hrange).trans (by gcongr)

/-- Small Weyl distance ⇒ small Euclidean distance. -/
theorem weylScale_euclidean_of_small (z : Rd d) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ y, weylScale ξ f D z y < δ → ‖z - y‖ < ε := by
  obtain ⟨a, ha⟩ := ((isCompact_closedBall z ε).image
    (by fun_prop : Continuous fun x => ξ * f x)).bddBelow
  have ha' : ∀ x ∈ ball z ε, a ≤ ξ * f x := fun x hx => ha ⟨x, ball_subset_closedBall hx, rfl⟩
  have hpos : 0 < infEDist (D.pt z) (D.pt '' (ball z ε)ᶜ) := by
    refine infEDist_pos_iff_notMem_closure.2 ?_
    rw [(D.isClosed_pt_image_compl isOpen_ball).closure_eq]
    rintro ⟨y, hy, hyz⟩
    have : y = z := hyz
    exact hy (this ▸ mem_ball_self hε)
  refine ⟨ENNReal.ofReal (Real.exp a) * infEDist (D.pt z) (D.pt '' (ball z ε)ᶜ),
    ENNReal.mul_pos (by simpa using Real.exp_pos a) hpos.ne', fun y hy => ?_⟩
  by_contra hyε
  have hyV : y ∉ ball z ε := by
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hyε
  refine absurd hy (not_lt.2 ?_)
  rw [← weylScaleOn_univ]
  refine le_weylScaleOn fun L P hL hc hu h0 h1 _ => ?_
  have := le_weylCost_of_exit hL hc hu isOpen_ball ha' ⟨L, ⟨hL, le_rfl⟩, h1 ▸ hyV⟩
  rwa [h0] at this

end Cont

/-! ### The continuous metric `e^{ξ f}·D` -/

section Metric

variable {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d}

/-- `e^{ξ f}·D` as a real function on `ℝ^d × ℝ^d`. -/
def weylDist (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (p : Rd d × Rd d) : ℝ :=
  (weylScale ξ f D p.1 p.2).toReal

theorem ofReal_weylDist (hD : D.IsLength) (z w : Rd d) :
    ENNReal.ofReal (weylDist ξ f D (z, w)) = weylScale ξ f D z w :=
  ENNReal.ofReal_toReal (weylScale_ne_top hD z w)

theorem weylDist_comm (z w : Rd d) : weylDist ξ f D (z, w) = weylDist ξ f D (w, z) := by
  simp only [weylDist, weylScale_comm z w]

theorem weylDist_triangle (hD : D.IsLength) (x y z : Rd d) :
    weylDist ξ f D (x, z) ≤ weylDist ξ f D (x, y) + weylDist ξ f D (y, z) :=
  ENNReal.toReal_le_add (weylScale_triangle x y z) (weylScale_ne_top hD x y)
    (weylScale_ne_top hD y z)

theorem weylDist_le_near (hD : D.IsLength) (z : Rd d) :
    ∃ r > 0, ∃ b : ℝ, ∀ z', D.1 (z, z') < r →
      weylDist ξ f D (z, z') ≤ Real.exp b * (2 * D.1 (z, z')) := by
  obtain ⟨r, hr, b, h⟩ := exists_weylScale_le_near (ξ := ξ) (f := f) hD z
  refine ⟨r, hr, b, fun z' hz' => ?_⟩
  have hnn : 0 ≤ D.1 (z, z') := D.nonneg z z'
  have h' := h z' hz'
  rw [← ENNReal.ofReal_mul (Real.exp_pos b).le] at h'
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (Real.exp_pos b).le (mul_nonneg zero_le_two hnn)) h'

theorem continuous_weylDist (hD : D.IsLength) : Continuous (weylDist ξ f D) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨z, w⟩
  obtain ⟨r₁, hr₁, b₁, h₁⟩ := weylDist_le_near (ξ := ξ) (f := f) hD z
  obtain ⟨r₂, hr₂, b₂, h₂⟩ := weylDist_le_near (ξ := ξ) (f := f) hD w
  have c1 : Continuous fun q : Rd d × Rd d => D.1 (z, q.1) :=
    D.1.continuous.comp (continuous_const.prodMk continuous_fst)
  have c2 : Continuous fun q : Rd d × Rd d => D.1 (w, q.2) :=
    D.1.continuous.comp (continuous_const.prodMk continuous_snd)
  set g : Rd d × Rd d → ℝ := fun q => Real.exp b₁ * (2 * D.1 (z, q.1)) +
    Real.exp b₂ * (2 * D.1 (w, q.2))
  have hg : Continuous g := by
    simp only [g]
    exact ((continuous_const.mul (continuous_const.mul c1))).add
      (continuous_const.mul (continuous_const.mul c2))
  have hg0 : g (z, w) = 0 := by simp [g, D.2.self_eq_zero]
  have hev1 : ∀ᶠ q in 𝓝 (z, w), D.1 (z, q.1) < r₁ :=
    c1.continuousAt.eventually_lt continuousAt_const (by simpa [D.2.self_eq_zero] using hr₁)
  have hev2 : ∀ᶠ q in 𝓝 (z, w), D.1 (w, q.2) < r₂ :=
    c2.continuousAt.eventually_lt continuousAt_const (by simpa [D.2.self_eq_zero] using hr₂)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ((hev1.and hev2).mono fun q hq => ?_) (hg0 ▸ hg.tendsto (z, w)))
  obtain ⟨q₁, q₂⟩ := q
  have e1 := h₁ q₁ hq.1
  have e2 := h₂ q₂ hq.2
  have t1 := weylDist_triangle (ξ := ξ) (f := f) hD q₁ z q₂
  have t2 := weylDist_triangle (ξ := ξ) (f := f) hD z w q₂
  have t3 := weylDist_triangle (ξ := ξ) (f := f) hD z q₁ w
  have t4 := weylDist_triangle (ξ := ξ) (f := f) hD q₁ q₂ w
  rw [weylDist_comm q₁ z] at t1
  rw [weylDist_comm q₂ w] at t4
  rw [Real.dist_eq, abs_sub_le_iff]
  simp only [g]
  constructor <;> linarith

/-- **`e^{ξ f}·D` as a continuous metric**, for a continuous length metric `D`. -/
def weylMetric (ξ : ℝ) (f : C(Rd d, ℝ)) (D : ContMetric d) (hD : D.IsLength) : ContMetric d :=
  ⟨⟨weylDist ξ f D, continuous_weylDist hD⟩,
    { self_eq_zero := fun x => by
        show (weylScale ξ f D x x).toReal = 0
        rw [weylScale_self]; rfl
      eq_of_eq_zero := fun x y h => by
        have h' : weylScale ξ f D x y = 0 := by
          rw [← ofReal_weylDist hD]
          exact ENNReal.ofReal_eq_zero.2 (le_of_eq h)
        by_contra hxy
        obtain ⟨δ, hδ, hsm⟩ := weylScale_euclidean_of_small (ξ := ξ) (f := f) (D := D) x
          ‖x - y‖ (norm_pos_iff.2 (sub_ne_zero.2 hxy))
        exact lt_irrefl _ (hsm y (h' ▸ hδ))
      symm := fun x y => weylDist_comm x y
      triangle := fun x y z => weylDist_triangle hD x y z
      euclidean_of_small := fun x ε hε => by
        obtain ⟨δ, hδ, hsm⟩ := weylScale_euclidean_of_small (ξ := ξ) (f := f) (D := D) x ε hε
        by_cases htop : δ = ⊤
        · exact ⟨1, one_pos, fun y _ =>
            hsm y (htop ▸ lt_top_iff_ne_top.2 (weylScale_ne_top hD x y))⟩
        · refine ⟨δ.toReal, ENNReal.toReal_pos hδ.ne' htop, fun y hy => hsm y ?_⟩
          exact (ENNReal.toReal_lt_toReal (weylScale_ne_top hD x y) htop).1 hy }⟩

theorem weylMetric_apply (hD : D.IsLength) (p : Rd d × Rd d) :
    (weylMetric ξ f D hD).1 p = (weylScale ξ f D p.1 p.2).toReal := rfl

theorem weylMetric_spec (hD : D.IsLength) (z w : Rd d) :
    ENNReal.ofReal ((weylMetric ξ f D hD).1 (z, w)) = weylScale ξ f D z w :=
  ofReal_weylDist hD z w

/-- `e^{ξ f}·D` is a length metric. -/
theorem weylMetric_isLength (hD : D.IsLength) : (weylMetric ξ f D hD).IsLength :=
  isLength_of_eq_weylScale _ (weylMetric_spec hD)

/-- Internal metrics of `e^{ξ f}·D` on open sets. -/
theorem weylMetric_internal (hD : D.IsLength) {U : Set (Rd d)} (hU : IsOpen U) (z w : Rd d) :
    (weylMetric ξ f D hD).internal U z w = weylScaleOn ξ f D U z w :=
  (weylScaleOn_eq_internal _ (weylMetric_spec hD) hU z w).symm

end Metric

/-! ### Lengths of paths for a Weyl-scaled metric -/

section PathLength

variable {ξ : ℝ} {f : C(Rd d, ℝ)} {D : ContMetric d} (D' : ContMetric d)
  (hD' : ∀ x y : Rd d, ENNReal.ofReal (D'.1 (x, y)) = weylScale ξ f D x y)
include hD'

/-- The `D'`-length of a `D`-length-parametrized path is at most its Weyl cost. -/
theorem curveLength_le_weylCost {L : ℝ} {P : ℝ → Rd d}
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) :
    curveLength (D'.pt ∘ P) 0 L ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t))) := by
  refine eVariationOn_le_lintegral fun s t hs hst ht => ?_
  rw [setLIntegral_congr Ioc_ae_eq_Icc]
  show edist (D'.pt (P s)) (D'.pt (P t)) ≤ _
  rw [edist_dist]
  refine le_of_eq_of_le (hD' (P s) (P t)) ?_
  rw [← weylScaleOn_univ]
  exact weylScaleOn_le_sub hu (fun _ _ => mem_univ _) hs hst ht

/-- **Upper bound**: if `ξ f ≤ b` on `V ⊇ P([s, t])` then `len(P; D') ≤ e^b len(P; D)`. -/
theorem curveLength_weyl_le {P : ℝ → Rd d} {s t : ℝ} (hst : s ≤ t)
    (hc : ContinuousOn (D.pt ∘ P) (Icc s t)) {V : Set (Rd d)} (hPV : ∀ τ ∈ Icc s t, P τ ∈ V)
    {b : ℝ} (hb : ∀ x ∈ V, ξ * f x ≤ b) :
    curveLength (D'.pt ∘ P) s t ≤ ENNReal.ofReal (Real.exp b) * curveLength (D.pt ∘ P) s t := by
  by_cases hfin : curveLength (D.pt ∘ P) s t = ∞
  · rw [hfin, ENNReal.mul_top (by simpa using Real.exp_pos b)]; exact le_top
  set ℓ := curveLength (D.pt ∘ P) s t
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → Rd d, D.pt ∘ Q = lengthParam (D.pt ∘ P) s t :=
    ⟨D.unpt ∘ lengthParam (X := D.Space) (D.pt ∘ P) s t, rfl⟩
  set σ := variationOnFromTo (D.pt ∘ P) (Icc s t) s
  have hbv : BoundedVariationOn (D.pt ∘ P) (Icc s t) := hfin
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hσmono : MonotoneOn σ (Icc s t) :=
    variationOnFromTo.monotoneOn hbv.locallyBoundedVariationOn hs
  have himg : σ '' Icc s t = Icc 0 ℓ.toReal := variationOnFromTo_image_Icc hst hc hfin
  have hu : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 ℓ.toReal) := by
    rw [hQ]; exact hasUnitSpeedOn_lengthParam hst hc hfin
  have hQσ : ∀ τ ∈ Icc s t, Q (σ τ) = P τ := fun τ hτ => by
    have h := lengthParam_variationOnFromTo hfin hτ
    rw [← hQ] at h
    exact h
  have hQP : EqOn (D'.pt ∘ P) ((D'.pt ∘ Q) ∘ σ) (Icc s t) := fun τ hτ => by
    simp only [Function.comp_apply, hQσ τ hτ]
  have hQV : ∀ u ∈ Icc 0 ℓ.toReal, Q u ∈ V := by
    intro u hu'
    rw [← himg] at hu'
    obtain ⟨τ, hτ, rfl⟩ := hu'
    rw [hQσ τ hτ]; exact hPV τ hτ
  rw [curveLength_congr hQP, curveLength_comp_of_monotoneOn _ hσmono himg]
  refine (curveLength_le_weylCost D' hD' hu).trans ?_
  calc ∫⁻ u in Icc 0 ℓ.toReal, ENNReal.ofReal (Real.exp (ξ * f (Q u)))
      ≤ ∫⁻ _ in Icc 0 ℓ.toReal, ENNReal.ofReal (Real.exp b) :=
        setLIntegral_mono' measurableSet_Icc fun u hu' =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hb _ (hQV u hu')))
    _ = ENNReal.ofReal (Real.exp b) * ℓ := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hfin]

/-- **Lower bound**: if `a ≤ ξ f` on an open `V ⊇ P([s, t])` then `e^a len(P; D) ≤ len(P; D')`. -/
theorem le_curveLength_weyl {P : ℝ → Rd d} {s t : ℝ}
    (hc : ContinuousOn (D.pt ∘ P) (Icc s t)) {V : Set (Rd d)} (hV : IsOpen V)
    (hPV : ∀ τ ∈ Icc s t, P τ ∈ V) {a : ℝ} (ha : ∀ x ∈ V, a ≤ ξ * f x) :
    ENNReal.ofReal (Real.exp a) * curveLength (D.pt ∘ P) s t ≤ curveLength (D'.pt ∘ P) s t := by
  have hcP : ContinuousOn P (Icc s t) := D.continuousOn_pt_comp_iff.1 hc
  have hc' : ContinuousOn (D'.pt ∘ P) (Icc s t) := D'.continuousOn_pt_comp_iff.2 hcP
  unfold curveLength eVariationOn
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  rw [Finset.mul_sum]
  refine le_trans ?_ (le_trans (le_of_eq (sum_curveLength_eq (D'.pt ∘ P) hu n))
    (curveLength_mono _ (hus 0).1 (hus n).2))
  refine Finset.sum_le_sum fun i _ => ?_
  have hi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
  have hsub : Icc (u i) (u (i + 1)) ⊆ Icc s t := Icc_subset_Icc (hus i).1 (hus (i + 1)).2
  obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hi (hc'.mono hsub)
  have hint : D'.internal V (P (u i)) (P (u (i + 1))) ≤
      curveLength (D'.pt ∘ P) (u i) (u (i + 1)) :=
    (internalEDist_le_pathLength γ fun τ => by
      obtain ⟨r, hr, hrτ⟩ := hrange (mem_range_self τ)
      exact ⟨P r, hPV r (hsub hr), hrτ⟩).trans hγ.le
  have hlow : ENNReal.ofReal (Real.exp a) * D.internal V (P (u i)) (P (u (i + 1))) ≤
      D'.internal V (P (u i)) (P (u (i + 1))) := by
    rw [← weylScaleOn_eq_internal D' hD' hV]; exact le_weylScaleOn_of_le ha
  refine le_trans ?_ (hlow.trans hint)
  rw [edist_comm]
  gcongr
  exact edist_le_internalEDist _ _ _

end PathLength

/-! ### Locality of Weyl scaling -/

section Local

variable {ξ : ℝ} {D₁ D₂ : ContMetric d} {U : Set (Rd d)}

theorem curveLength_le_of_internal_eq
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y)
    {P : ℝ → Rd d} {s t : ℝ} (hc : ContinuousOn P (Icc s t)) (hPU : ∀ τ ∈ Icc s t, P τ ∈ U) :
    curveLength (D₁.pt ∘ P) s t ≤ curveLength (D₂.pt ∘ P) s t := by
  have hc₂ : ContinuousOn (D₂.pt ∘ P) (Icc s t) := D₂.continuousOn_pt_comp_iff.2 hc
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  calc ∑ i ∈ Finset.range n, edist (D₁.pt (P (u (i + 1)))) (D₁.pt (P (u i)))
      ≤ ∑ i ∈ Finset.range n, D₂.internal U (P (u i)) (P (u (i + 1))) :=
        Finset.sum_le_sum fun i _ => by
          rw [edist_comm, ← hD _ (hPU _ (hus i)) _ (hPU _ (hus (i + 1)))]
          exact edist_le_internalEDist _ _ _
    _ ≤ ∑ i ∈ Finset.range n, curveLength (D₂.pt ∘ P) (u i) (u (i + 1)) :=
        Finset.sum_le_sum fun i _ => by
          have hi : u i ≤ u (i + 1) := hu (Nat.le_succ i)
          have hsub : Icc (u i) (u (i + 1)) ⊆ Icc s t := Icc_subset_Icc (hus i).1 (hus (i + 1)).2
          obtain ⟨γ, hγ, hrange⟩ := exists_path_of_curve hi (hc₂.mono hsub)
          refine (internalEDist_le_pathLength γ fun τ => ?_).trans hγ.le
          obtain ⟨r, hr, hrτ⟩ := hrange (mem_range_self τ)
          exact ⟨P r, hPU r (hsub hr), hrτ⟩
    _ = curveLength (D₂.pt ∘ P) (u 0) (u n) := sum_curveLength_eq _ hu n
    _ ≤ curveLength (D₂.pt ∘ P) s t := curveLength_mono _ (hus 0).1 (hus n).2

/-- Same internal metric on `U` ⇒ same lengths of paths in `U`. -/
theorem curveLength_eq_of_internal_eq
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y)
    {P : ℝ → Rd d} {s t : ℝ} (hc : ContinuousOn P (Icc s t)) (hPU : ∀ τ ∈ Icc s t, P τ ∈ U) :
    curveLength (D₁.pt ∘ P) s t = curveLength (D₂.pt ∘ P) s t :=
  le_antisymm (curveLength_le_of_internal_eq hD hc hPU)
    (curveLength_le_of_internal_eq (fun x hx y hy => (hD x hx y hy).symm) hc hPU)

theorem weylScaleOn_le_of_internal_eq {f : C(Rd d, ℝ)} {z w : Rd d}
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y) :
    weylScaleOn ξ f D₁ U z w ≤ weylScaleOn ξ f D₂ U z w := by
  refine le_weylScaleOn fun L P hL hc hu h0 h1 hPU => ?_
  have hcP : ContinuousOn P (Icc 0 L) := D₂.continuousOn_pt_comp_iff.1 hc
  have hu₁ : HasUnitSpeedOn (D₁.pt ∘ P) (Icc 0 L) := by
    rw [hasUnitSpeedOn_Icc_iff] at hu ⊢
    intro s t hs hst ht
    rw [curveLength_eq_of_internal_eq hD (hcP.mono (Icc_subset_Icc hs ht))
      (fun τ hτ => hPU τ ⟨hs.trans hτ.1, hτ.2.trans ht⟩)]
    exact hu s t hs hst ht
  exact weylScaleOn_le hL (continuousOn_of_hasUnitSpeedOn hu₁) hu₁ h0 h1 hPU

/-- `(e^{ξ f}·D)_U` depends on `D` only through `D(·,·;U)`. -/
theorem weylScaleOn_eq_of_internal_eq {f : C(Rd d, ℝ)} {z w : Rd d}
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y) :
    weylScaleOn ξ f D₁ U z w = weylScaleOn ξ f D₂ U z w :=
  le_antisymm (weylScaleOn_le_of_internal_eq hD)
    (weylScaleOn_le_of_internal_eq fun x hx y hy => (hD x hx y hy).symm)

/-- **Locality of Weyl scaling**: if `D₁(·,·;U) = D₂(·,·;U)` and `ξ f₁ = ξ f₂` on the open set
`U`, then `(e^{ξ f₁}·D₁)(·,·;U) = (e^{ξ f₂}·D₂)(·,·;U)`. -/
theorem internal_weyl_eq_of_internal_eq (hU : IsOpen U) {f₁ f₂ : C(Rd d, ℝ)}
    {D₁' D₂' : ContMetric d}
    (h₁ : ∀ x y : Rd d, ENNReal.ofReal (D₁'.1 (x, y)) = weylScale ξ f₁ D₁ x y)
    (h₂ : ∀ x y : Rd d, ENNReal.ofReal (D₂'.1 (x, y)) = weylScale ξ f₂ D₂ x y)
    (hD : ∀ x ∈ U, ∀ y ∈ U, D₁.internal U x y = D₂.internal U x y)
    (hf : ∀ x ∈ U, ξ * f₁ x = ξ * f₂ x) (z w : Rd d) :
    D₁'.internal U z w = D₂'.internal U z w := by
  rw [← weylScaleOn_eq_internal D₁' h₁ hU, ← weylScaleOn_eq_internal D₂' h₂ hU,
    weylScaleOn_eq_of_internal_eq hD, weylScaleOn_congr hf]

end Local

end HigherDimLQGMetric
