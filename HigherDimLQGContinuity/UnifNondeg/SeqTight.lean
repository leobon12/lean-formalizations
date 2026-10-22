import HigherDimLQGContinuity.UnifNondeg.SeqZeroOne

/-!
# Sequence zero-one law, part 3: tightness, Prokhorov and bounded zero sets along arrays (packet U5)

Blueprint Part D, `d:prop-u69` steps (μ0) and (μ5), and `d:prop-u64`(a) (NA3 R11).

**Inputs at a quantile `q`.** The argument runs with the normalization `a^ξ_n(q)` for one quantile `q ∈ (0, 1)`
(NA3 R11: `q ∈ (q₂, 1)`, never the median, see ruling N28). It needs two uniform inputs, stated here for fixed
`(b, μ, q)`:
* `UHolderTightAt d κ b μ q β`: the shape of `UHolderTightShape` (interface I8) with `λ_n = a_n(½)` replaced by
  `a_n(q)` (Part D `d:lem-u61`(b));
* `UDistInfAt d κ b μ q`: the shape of `UDistInfShape` (interface I10) with `a_n(q)` (Part D `d:lem-u65`(c), `G = 0`).
The high-quantile forms `UHolderTightAQShape`, `UDistInfAQShape` give them at every `q` close to `1`; packet U4
proves both (`holderTightAQShape_unif`, `distInfAQShape_unif`, `UnifTight/Exports.lean`). The median-normalized I8
is not an input: it needs (A.4) = I7, which this packet proves (ruling N28).

**Results.**
* (μ0) `u5_isTightMeasureSet_joint`: under `UHolderTightAt`, the joint laws `nd_jointLaw P _ H ξ q r n` over all
  `ξ ∈ S(b, μ)` and all `n` are tight; the coarse field `h_m` is deleted at the cost `e^{b sup|h_m|}` (`ξ`-free);
  `u5_exists_joint_limit`: every parameter array has a weakly convergent subsequence of joint laws.
* (μ5) `u5_ae_boundedZeroEvent`: a distance-to-infinity bound along an array makes the zero sets of `∂B_r(0)`
  almost surely bounded in every array limit (port of `DGZ.nd_ae_boundedZeroEvent_of_tendsto`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### The input shapes at a quantile `q` -/

/-- **Uniform Hölder tightness at the quantile `q`**: the shape of `UHolderTightShape` (I8) for fixed `(b, μ, β)`,
normalized by `a^ξ_n(q)` instead of `λ_n` (Part D `d:lem-u61`(b)). -/
def UHolderTightAt (d : ℕ) (κ : Rd d → ℝ) (b μ : ℝ) (q : ℝ≥0∞) (β : ℝ) : Prop :=
  ∀ U V : Set (Rd d), IsOpen U → IsOpen V → IsConnected V → Bornology.IsBounded V →
    closure V ⊆ U → ∀ θ : ℝ, 0 < θ → ∃ M : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
        (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ,
          P {ω | ∃ x ∈ V, ∃ y ∈ V, M * DGZ.aQ P H ξ n q * ‖x - y‖ ^ β <
            HigherDimLFPP.lfppDistOn ξ (fun w => H n w ω) U x y} ≤ ENNReal.ofReal θ

/-- **Uniform distance to infinity at the quantile `q`**: the shape of `UDistInfShape` (I10) for fixed `(b, μ)`,
normalized by `a^ξ_n(q)` (Part D `d:lem-u65`(c) with `G = 0`). -/
def UDistInfAt (d : ℕ) (κ : Rd d → ℝ) (b μ : ℝ) (q : ℝ≥0∞) : Prop :=
  ∀ r T θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧ ∃ N : ℕ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : HigherDimLFPP.WN d → Ω → ℝ)
      (H : ℕ → Rd d → Ω → ℝ), DGZ.IsDyadicRealization κ P W H → ∀ n : ℕ, N ≤ n →
        P {ω | DGZ.acrossDist ξ (fun w => H n w ω) 0 R r ≤ T * DGZ.aQ P H ξ n q} ≤
          ENNReal.ofReal θ

/-- **The high-quantile Hölder shape** (Part D `d:lem-u61`(b), the form of packet U4's `holderTightAQ_unif`): for
`0 < β < μ` the Hölder bound holds at every quantile `q` close to `1`. -/
def UHolderTightAQShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ → ∀ β : ℝ, 0 < β → β < μ →
    ∃ q₁ : ℝ≥0∞, 0 < q₁ ∧ q₁ < 1 ∧ ∀ q : ℝ≥0∞, q₁ ≤ q → q < 1 → UHolderTightAt d κ b μ q β

/-- **The high-quantile distance-to-infinity shape** (Part D `d:lem-u65`(c) with `G = 0`, the form of packet U4's
port of `DGZ.distInf_aq`). -/
def UDistInfAQShape (d : ℕ) (κ : Rd d → ℝ) : Prop :=
  ∀ b μ : ℝ, 0 < b → 0 < μ →
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 → UDistInfAt d κ b μ q

/-- The Hölder shape passes to higher quantiles (`a_n(q) ≤ a_n(q')`; the constant is replaced by `max M 0`). -/
theorem UHolderTightAt.mono {κ : Rd d → ℝ} {b μ β : ℝ} {q q' : ℝ≥0∞} (hT : UHolderTightAt d κ b μ q β)
    (hq0 : 0 < q) (hqq' : q ≤ q') (hq'1 : q' < 1) : UHolderTightAt d κ b μ q' β := by
  intro U V hU hV hVc hVb hVU θ hθ
  obtain ⟨M, hM⟩ := hT U V hU hV hVc hVb hVU θ hθ
  refine ⟨max M 0, fun ξ hξ Ω _ P W H hH n => le_trans (measure_mono ?_) (hM ξ hξ Ω P W H hH n)⟩
  rintro ω ⟨x, hx, y, hy, hlt⟩
  refine ⟨x, hx, y, hy, lt_of_le_of_lt ?_ hlt⟩
  have hd0 : 0 < d := by have := hξ.dim; omega
  have ha : 0 ≤ aQ P H ξ n q := (tight_aQ_pos hd0 hH ξ n hq0 (hqq'.trans_lt hq'1)).le
  have haa : aQ P H ξ n q ≤ aQ P H ξ n q' := tight_aQ_mono hH ξ n hq0 hqq' hq'1
  have hn : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
  calc M * aQ P H ξ n q * ‖x - y‖ ^ β ≤ max M 0 * aQ P H ξ n q * ‖x - y‖ ^ β := by
        gcongr
        exact le_max_left _ _
    _ ≤ max M 0 * aQ P H ξ n q' * ‖x - y‖ ^ β := by
        have hM0 : 0 ≤ max M 0 := le_max_right _ _
        gcongr

/-- The distance-to-infinity shape passes to lower quantiles. -/
theorem UDistInfAt.anti {κ : Rd d → ℝ} {b μ : ℝ} {q q' : ℝ≥0∞} (hI : UDistInfAt d κ b μ q')
    (hq0 : 0 < q) (hqq' : q ≤ q') (hq'1 : q' < 1) : UDistInfAt d κ b μ q := by
  intro r T θ hr hθ
  obtain ⟨R, hrR, N, hN⟩ := hI r (max T 0) θ hr hθ
  refine ⟨R, hrR, N, fun ξ hξ Ω _ P W H hH n hn => le_trans (measure_mono ?_) (hN ξ hξ Ω P W H hH n hn)⟩
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  have hd0 : 0 < d := by have := hξ.dim; omega
  have ha : 0 ≤ aQ P H ξ n q := (tight_aQ_pos hd0 hH ξ n hq0 (hqq'.trans_lt hq'1)).le
  have haa : aQ P H ξ n q ≤ aQ P H ξ n q' := tight_aQ_mono hH ξ n hq0 hqq' hq'1
  calc acrossDist ξ (fun w => H n w ω) 0 R r ≤ T * aQ P H ξ n q := hω
    _ ≤ max T 0 * aQ P H ξ n q := mul_le_mul_of_nonneg_right (le_max_left _ _) ha
    _ ≤ max T 0 * aQ P H ξ n q' := mul_le_mul_of_nonneg_left haa (le_max_right _ _)

/-! ### Geometry: an open connected neighbourhood with closure inside an open set -/

/-- A union of balls centred on a preconnected set is preconnected (the `Rd d` form of
`LQGMetric`'s `isPreconnected_biUnion_ball`). -/
theorem u5_isPreconnected_biUnion_ball {C : Set (Rd d)} (hC : IsPreconnected C) (ε : ℝ) (hε : 0 < ε) :
    IsPreconnected (⋃ x ∈ C, ball x ε) := by
  rcases C.eq_empty_or_nonempty with h | ⟨c, hc⟩
  · subst h; simpa using isPreconnected_empty
  refine isPreconnected_of_forall c fun y hy => ?_
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hy
  refine ⟨C ∪ ball x ε, union_subset (fun z hz => mem_iUnion₂.2 ⟨z, hz, mem_ball_self hε⟩)
    (subset_iUnion₂ (s := fun x _ => ball x ε) x hx), Or.inl hc, Or.inr hyx, ?_⟩
  exact IsPreconnected.union x hx (mem_ball_self hε) hC (convex_ball x ε).isPreconnected

/-- **An open connected bounded neighbourhood**: a nonempty compact preconnected `T` inside an open `U` lies in an
open, connected, bounded `V` with `closure V ⊆ U` (a small thickening of `T`). -/
theorem u5_exists_open_connected_nhds {U T : Set (Rd d)} (hU : IsOpen U) (hT : IsCompact T)
    (hTc : IsPreconnected T) (hTne : T.Nonempty) (hTU : T ⊆ U) :
    ∃ V : Set (Rd d), IsOpen V ∧ IsConnected V ∧ Bornology.IsBounded V ∧ closure V ⊆ U ∧ T ⊆ V := by
  obtain ⟨δ, hδ, hδU⟩ := hT.exists_cthickening_subset_open hU hTU
  refine ⟨thickening δ T, isOpen_thickening, ⟨hTne.mono (self_subset_thickening hδ T), ?_⟩,
    hT.isBounded.thickening, (closure_thickening_subset_cthickening δ T).trans hδU,
    self_subset_thickening hδ T⟩
  rw [thickening_eq_biUnion_ball]
  exact u5_isPreconnected_biUnion_ball hTc δ hδ

/-! ### (μ0): tightness of the joint laws over `S(b, μ) × ℕ` -/

section Tight

variable {κ : Rd d → ℝ} {b μ β : ℝ} {q : ℝ≥0∞}

/-- **Tightness of the whole-space coordinate** over all `ξ ∈ S(b, μ)` and all `n` (normalization `a^ξ_n(q)`). -/
theorem u5_isTightMeasureSet_whole (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β)
    (hq0 : 0 < q) (hq1 : q < 1) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ) (hH : IsDyadicRealization κ P W H) :
    IsTightMeasureSet {ν : Measure C(Rd d × Rd d, ℝ) | ∃ ξ : ℝ, UHyp d κ b μ ξ ∧ ∃ n : ℕ,
      ν = P.map (fun ω => normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))} := by
  refine isTightMeasureSet_of_holderBounds (β := β) tc_closedBall_mono tc_closedBall_mem_nhds hβ ?_ ?_
  · rintro ν ⟨ξ, hξ, n, rfl⟩
    have hd0 : 0 < d := by have := hξ.dim; omega
    have hFm := measurable_normMetricC (H := H n) (hH.band n).continuous (hH.band n).measurable
      ξ (aQ P H ξ n q)
    have hmeasA : MeasurableSet {f : C(Rd d × Rd d, ℝ) |
        ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} :=
      tc_isClosed_metricCond.isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasA]
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    apply hω
    have hφ := (hH.band n).continuous ω
    have ha0 : 0 ≤ (aQ P H ξ n q)⁻¹ := (inv_pos.2 (tight_aQ_pos hd0 hH ξ n hq0 hq1)).le
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [normMetricC_apply hφ, lfppMetric_self, mul_zero]
    · rw [normMetricC_apply hφ, normMetricC_apply hφ, normMetricC_apply hφ, ← mul_add]
      exact mul_le_mul_of_nonneg_left (lfppMetric_triangle hφ x y z) ha0
  · intro j θ hθ
    have hV : IsConnected (ball (0 : Rd d) ((j : ℝ) + 1)) :=
      ⟨nonempty_ball.2 (by positivity), (convex_ball _ _).isPreconnected⟩
    obtain ⟨M, hM⟩ := hT univ (ball (0 : Rd d) ((j : ℝ) + 1)) isOpen_univ isOpen_ball hV
      isBounded_ball (subset_univ _) θ hθ
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    rintro ν ⟨ξ, hξ, n, rfl⟩
    have hd0 : 0 < d := by have := hξ.dim; omega
    have hFm := measurable_normMetricC (H := H n) (hH.band n).continuous (hH.band n).measurable
      ξ (aQ P H ξ n q)
    have hmeasB : MeasurableSet {f : C(Rd d × Rd d, ℝ) | ¬ ∀ x ∈ closedBall (0 : Rd d) j,
        ∀ y ∈ closedBall (0 : Rd d) j, f (x, y) ≤ max M 0 * dist x y ^ β} :=
      (tc_isClosed_holderCond _ _).isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasB]
    refine le_trans (measure_mono fun ω hω => ?_) (hM ξ hξ Ω P W H hH n)
    simp only [mem_preimage, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨x, hx, y, hy, hlt⟩ := hω
    have ha0 := tight_aQ_pos hd0 hH ξ n hq0 hq1
    rw [normMetricC_apply ((hH.band n).continuous ω), dist_eq_norm] at hlt
    have hball : closedBall (0 : Rd d) j ⊆ ball (0 : Rd d) ((j : ℝ) + 1) :=
      closedBall_subset_ball (by linarith)
    refine ⟨x, hball hx, y, hball hy, ?_⟩
    have h1 := (lt_inv_mul_iff₀ ha0).1 hlt
    have hn : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : M * aQ P H ξ n q * ‖x - y‖ ^ β ≤ aQ P H ξ n q * (max M 0 * ‖x - y‖ ^ β) := by
      calc M * aQ P H ξ n q * ‖x - y‖ ^ β ≤ max M 0 * aQ P H ξ n q * ‖x - y‖ ^ β := by
            gcongr
            exact le_max_left _ _
        _ = aQ P H ξ n q * (max M 0 * ‖x - y‖ ^ β) := by ring
    change M * aQ P H ξ n q * ‖x - y‖ ^ β < lfppMetric ξ (fun z => H n z ω) x y
    exact lt_of_le_of_lt h2 h1

/-- **Tightness of one internal coordinate with the coarse field deleted** (`h_n - h_m` on a bounded open connected
`U`), over all `ξ ∈ S(b, μ)` and all `n`: the Hölder bound of `h_n` on a neighbourhood of each exhaustion piece, and
`D(h_n - h_m) ≤ e^{b L} D(h_n)` on `{sup_U |h_m| ≤ L}` (`ξ ≤ b`; NA3 R11 (μ0)). -/
theorem u5_isTightMeasureSet_internal (hκ : IsLFPPKernel κ) (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β)
    (hq0 : 0 < q) (hq1 : q < 1) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ) (hH : IsDyadicRealization κ P W H)
    (U : Set (Rd d)) (hU : IsOpen U) (hUc : IsConnected U) (hUb : Bornology.IsBounded U) (m : ℕ) :
    IsTightMeasureSet {ν : Measure C(U × U, ℝ) | ∃ ξ : ℝ, UHyp d κ b μ ξ ∧ ∃ n : ℕ,
      ν = P.map (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U (aQ P H ξ n q))} := by
  have hUp : IsPreconnected U := hUc.isPreconnected
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  -- the domain lies in a closed box
  obtain ⟨R₀', hR₀'⟩ := hUb.subset_closedBall (0 : Rd d)
  set R₀ : ℝ := max R₀' 0 with hR₀def
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  have hUbox : U ⊆ cbox (0 : Rd d) R₀ := by
    intro z hz k
    have hnorm : ‖z‖ ≤ R₀' := by simpa only [mem_closedBall, dist_zero_right] using hR₀' hz
    have hk := HigherDimLFPP.DGZ.abs_apply_le_norm z k
    simp only [PiLp.zero_apply, sub_zero]
    exact hk.trans (hnorm.trans (le_max_left _ _))
  -- compact preconnected hulls of the exhaustion
  have hTj : ∀ j : ℕ, ∃ T : Set (Rd d), IsCompact T ∧ IsPreconnected T ∧ tcExhaust U j ⊆ T ∧
      T ⊆ U := fun j => exists_isCompact_isPreconnected_superset hU hUc
        (tcExhaust_isCompact U j) (tcExhaust_subset U j)
  choose T hTc hTp hKT hTU using hTj
  refine isTightMeasureSet_of_holderBounds (β := β) (tcExhaustU_mono U) (tcExhaustU_mem_nhds hU) hβ ?_ ?_
  · rintro ν ⟨ξ, hξ, n, rfl⟩
    have hd0 : 0 < d := by have := hξ.dim; omega
    have hφc : ∀ ω, Continuous fun z => H n z ω - H m z ω := fun ω =>
      ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
    have hFm := measurable_internalMetricC (H := fun z ω => H n z ω - H m z ω) hφc
      (fun z => ((hH.band n).measurable z).sub ((hH.band m).measurable z)) ξ hU hUp (aQ P H ξ n q)
    have hmeasA : MeasurableSet {f : C(U × U, ℝ) |
        ¬ ((∀ x, f (x, x) = 0) ∧ ∀ x y z, f (x, z) ≤ f (x, y) + f (y, z))} :=
      tc_isClosed_metricCond.isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasA]
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    apply hω
    have ha0 : 0 ≤ (aQ P H ξ n q)⁻¹ := (inv_pos.2 (tight_aQ_pos hd0 hH ξ n hq0 hq1)).le
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [internalMetricC_apply (hφc ω) hU hUp, lfppDistOn_self, mul_zero]
    · rw [internalMetricC_apply (hφc ω) hU hUp, internalMetricC_apply (hφc ω) hU hUp,
        internalMetricC_apply (hφc ω) hU hUp, ← mul_add]
      exact mul_le_mul_of_nonneg_left (lfppDistOn_triangle_of_isPreconnected hU hUp (hφc ω)
        x.2 y.2 z.2) ha0
  · intro j θ hθ
    rcases (T j).eq_empty_or_nonempty with hTe | hTne
    · -- an empty exhaustion piece: nothing to bound
      refine ⟨0, le_rfl, ?_⟩
      rintro ν ⟨ξ, hξ, n, rfl⟩
      have h0 : (P.map (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U
          (aQ P H ξ n q))) {f : C(U × U, ℝ) | ¬ ∀ x ∈ tcExhaustU U j, ∀ y ∈ tcExhaustU U j,
            f (x, y) ≤ 0 * dist x y ^ β} = 0 := by
        refine measure_mono_null (fun f hf => ?_) measure_empty
        apply hf
        intro x hx
        have hxT := hKT j hx
        rw [hTe] at hxT
        exact absurd hxT (Set.notMem_empty _)
      rw [h0]
      exact zero_le
    obtain ⟨V, hVo, hVc, hVb, hVU, hTV⟩ := u5_exists_open_connected_nhds hU (hTc j) (hTp j) hTne (hTU j)
    obtain ⟨M, hM⟩ := hT U V hU hVo hVc hVb hVU (θ / 2) (by positivity)
    obtain ⟨L, hL0, hL⟩ := exists_sup_tail_level_tight hκ m hR₀ (θ := θ / 2) (by positivity)
    refine ⟨max M 0 * Real.exp (b * L), mul_nonneg (le_max_right _ _) (Real.exp_pos _).le, ?_⟩
    rintro ν ⟨ξ, hξ, n, rfl⟩
    have hd0 : 0 < d := by have := hξ.dim; omega
    have hφc : ∀ ω, Continuous fun z => H n z ω - H m z ω := fun ω =>
      ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
    have hFm := measurable_internalMetricC (H := fun z ω => H n z ω - H m z ω) hφc
      (fun z => ((hH.band n).measurable z).sub ((hH.band m).measurable z)) ξ hU hUp (aQ P H ξ n q)
    have hmeasB : MeasurableSet {f : C(U × U, ℝ) | ¬ ∀ x ∈ tcExhaustU U j, ∀ y ∈ tcExhaustU U j,
        f (x, y) ≤ max M 0 * Real.exp (b * L) * dist x y ^ β} :=
      (tc_isClosed_holderCond _ _).isOpen_compl.measurableSet
    rw [Measure.map_apply hFm hmeasB]
    have ha0 := tight_aQ_pos hd0 hH ξ n hq0 hq1
    have hsub : (fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U (aQ P H ξ n q)) ⁻¹'
        {f : C(U × U, ℝ) | ¬ ∀ x ∈ tcExhaustU U j, ∀ y ∈ tcExhaustU U j,
          f (x, y) ≤ max M 0 * Real.exp (b * L) * dist x y ^ β} ⊆
        {ω | ∃ x ∈ V, ∃ y ∈ V, M * aQ P H ξ n q * ‖x - y‖ ^ β <
          lfppDistOn ξ (fun w => H n w ω) U x y} ∪
        {ω | ∃ z ∈ cbox (0 : Rd d) R₀, L < |H m z ω|} := by
      intro ω hω
      simp only [mem_preimage, mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨x, hx, y, hy, hlt⟩ := hω
      by_contra hgood
      simp only [mem_union, mem_ofPred_eq, not_or, not_exists, not_and, not_lt] at hgood
      obtain ⟨hhol, hsup⟩ := hgood
      rw [internalMetricC_apply (hφc ω) hU hUp, Subtype.dist_eq, dist_eq_norm] at hlt
      have hxV : (x : Rd d) ∈ V := hTV (hKT j hx)
      have hyV : (y : Rd d) ∈ V := hTV (hKT j hy)
      have h1 : lfppDistOn ξ (fun z => H n z ω - H m z ω) U x y ≤
          Real.exp (|ξ| * L) * lfppDistOn ξ (fun z => H n z ω) U x y :=
        lfppDistOn_le_exp_mul (hφc ω) ((hH.band n).continuous ω) fun z hz => by
          have heq : H n z ω - H m z ω - H n z ω = -H m z ω := by ring
          rw [heq, abs_neg]
          exact hsup z (hUbox hz)
      have h2 := hhol x hxV y hyV
      have hexp : Real.exp (|ξ| * L) ≤ Real.exp (b * L) := by
        rw [abs_of_pos hξ.xi_pos]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hξ.le_b hL0)
      have hn : 0 ≤ ‖(x : Rd d) - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) _
      have hD : 0 ≤ lfppDistOn ξ (fun z => H n z ω) U x y := lfppDistOn_nonneg _ _ _ _ _
      have h3 : lfppDistOn ξ (fun z => H n z ω - H m z ω) U x y ≤
          max M 0 * Real.exp (b * L) * ‖(x : Rd d) - y‖ ^ β * aQ P H ξ n q := by
        calc lfppDistOn ξ (fun z => H n z ω - H m z ω) U x y
            ≤ Real.exp (|ξ| * L) * lfppDistOn ξ (fun z => H n z ω) U x y := h1
          _ ≤ Real.exp (b * L) * (max M 0 * aQ P H ξ n q * ‖(x : Rd d) - y‖ ^ β) := by
              apply mul_le_mul hexp _ hD (Real.exp_pos _).le
              exact h2.trans (by gcongr; exact le_max_left _ _)
          _ = max M 0 * Real.exp (b * L) * ‖(x : Rd d) - y‖ ^ β * aQ P H ξ n q := by ring
      have h4 := (lt_inv_mul_iff₀ ha0).1 hlt
      linarith
    calc P ((fun ω => internalMetricC ξ (fun z => H n z ω - H m z ω) U (aQ P H ξ n q)) ⁻¹'
          {f : C(U × U, ℝ) | ¬ ∀ x ∈ tcExhaustU U j, ∀ y ∈ tcExhaustU U j,
            f (x, y) ≤ max M 0 * Real.exp (b * L) * dist x y ^ β})
        ≤ P ({ω | ∃ x ∈ V, ∃ y ∈ V, M * aQ P H ξ n q * ‖x - y‖ ^ β <
            lfppDistOn ξ (fun w => H n w ω) U x y} ∪
          {ω | ∃ z ∈ cbox (0 : Rd d) R₀, L < |H m z ω|}) := measure_mono hsub
      _ ≤ ENNReal.ofReal (θ / 2) + ENNReal.ofReal (θ / 2) :=
          (measure_union_le _ _).trans (add_le_add (hM ξ hξ Ω P W H hH n)
            (hL hH.whiteNoise (hH.band m) 0))
      _ = ENNReal.ofReal θ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

/-- **(μ0) Tightness of the joint laws** over all `ξ ∈ S(b, μ)` and all depths `n` (port of
`DGZ.nd_isTightMeasureSet_joint`; NA3 R11 (μ0): tightness of each coordinate by the uniform Hölder bound, then
countable-product tightness). -/
theorem u5_isTightMeasureSet_joint (hκ : IsLFPPKernel κ) (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β)
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ) (hH : IsDyadicRealization κ P W H) :
    IsTightMeasureSet {ν : Measure (nd_Joint d r) | ∃ ξ : ℝ, UHyp d κ b μ ξ ∧ ∃ n : ℕ,
      ν = P.map (nd_jointSample P H ξ q r n)} := by
  let S : Set (Measure (nd_Joint d r)) :=
    {ν | ∃ ξ : ℝ, UHyp d κ b μ ξ ∧ ∃ n : ℕ, ν = P.map (nd_jointSample P H ξ q r n)}
  change IsTightMeasureSet S
  have hS0 : IsTightMeasureSet (Measure.fst '' S) := by
    refine (u5_isTightMeasureSet_whole hT hβ hq0 hq1 P W H hH).subset ?_
    rintro ν ⟨ν', ⟨ξ, hξ, n, rfl⟩, rfl⟩
    refine ⟨ξ, hξ, n, ?_⟩
    change (P.map (nd_jointSample P H ξ q r n)).map Prod.fst = _
    exact Measure.map_map measurable_fst (nd_measurable_jointSample hH ξ q r n)
  have hS1 : IsTightMeasureSet (Measure.snd '' S) := by
    apply nd_isTightMeasureSet_pi
    intro i
    refine (u5_isTightMeasureSet_internal hκ hT hβ hq0 hq1 P W H hH (nd_domain r i.1)
      (nd_isOpen_domain r i.1) (nd_isConnected_domain r i.1) (nd_isBounded_domain r i.1) i.2).subset ?_
    rintro ν ⟨ν', ⟨ν₀, ⟨ξ, hξ, n, rfl⟩, rfl⟩, rfl⟩
    refine ⟨ξ, hξ, n, ?_⟩
    let F := nd_jointSample P H ξ q r n
    have hF : Measurable F := nd_measurable_jointSample hH ξ q r n
    change ((P.map F).map Prod.snd).map (fun f => f i) = _
    rw [Measure.map_map (measurable_pi_apply i) measurable_snd,
      Measure.map_map ((measurable_pi_apply i).comp measurable_snd) hF]
    rfl
  exact IsTightMeasureSet.prodMk hS0 hS1

/-- **(μ0) Prokhorov along parameter arrays**: for every array `ξs k ∈ S(b, μ)` and depths `ns k` there are a
strictly increasing `ψ` and a probability measure `μ₀` with `nd_jointLaw (ξs (ψ k)) (ns (ψ k)) → μ₀` (port of
`DGZ.nd_exists_joint_limit`). -/
theorem u5_exists_joint_limit (hκ : IsLFPPKernel κ) (hT : UHolderTightAt d κ b μ q β) (hβ : 0 < β)
    (hq0 : 0 < q) (hq1 : q < 1) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ) (hH : IsDyadicRealization κ P W H)
    (ξs : ℕ → ℝ) (hU : ∀ k, UHyp d κ b μ (ξs k)) (ns : ℕ → ℕ) :
    ∃ μ₀ : ProbabilityMeasure (nd_Joint d r), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs (ψ k)) q r (ns (ψ k)))
        atTop (𝓝 μ₀) := by
  let law : ℕ → ProbabilityMeasure (nd_Joint d r) :=
    fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q r (ns k)
  have hTs : IsTightMeasureSet
      {((ν : ProbabilityMeasure (nd_Joint d r)) : Measure (nd_Joint d r)) | ν ∈ range law} := by
    refine (u5_isTightMeasureSet_joint hκ hT hβ hq0 hq1 r P W H hH).subset ?_
    rintro ν ⟨ν', ⟨k, rfl⟩, rfl⟩
    exact ⟨ξs k, hU k, ns k, rfl⟩
  obtain ⟨μ₀, -, ψ, hψ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet hTs).tendsto_subseq (x := law)
      (fun k => subset_closure ⟨k, rfl⟩)
  exact ⟨μ₀, ψ, hψ, hlim⟩

end Tight

/-! ### (μ5): bounded zero sets along arrays -/

section Bounded

variable {κ : Rd d → ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ} {b μ : ℝ} {ξs : ℕ → ℝ} {q : ℝ≥0∞}

/-- **Bounded zero sets in array limits** (port of `DGZ.nd_ae_boundedZeroEvent_of_tendsto`; NA3 R11 (μ5)): if along
the array the normalized crossing of `B_R(0) \ B_r(0)` exceeds `1` with probability `≥ 1 - θ` for a suitable `R`
(eventually in `k`), then the points at `D̃`-distance zero from `∂B_r(0)` are almost surely bounded. -/
theorem u5_ae_boundedZeroEvent (hH : IsDyadicRealization κ P W H) (hU : ∀ k, UHyp d κ b μ (ξs k))
    (hq0 : 0 < q) (hq1 : q < 1) (rGrid r : ℝ) (hr : 0 < r) (ns : ℕ → ℕ)
    {μ₀ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H (ξs k) q rGrid (ns k))
      atTop (𝓝 μ₀))
    (hB : ∀ θ : ℝ, 0 < θ → ∃ R : ℝ, r < R ∧ ∀ᶠ k in atTop,
      P {ω | acrossDist (ξs k) (fun z => H (ns k) z ω) 0 R r ≤ aQ P H (ξs k) (ns k) q} ≤
        ENNReal.ofReal θ) :
    ∀ᵐ s ∂(μ₀ : Measure (nd_Joint d rGrid)), s ∈ nd_boundedZeroEvent rGrid r := by
  have hd0 : 0 < d := by have := (hU 0).dim; omega
  have : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  rw [ae_iff]
  have hzero : (μ₀ : Measure (nd_Joint d rGrid)) {s | ¬s ∈ nd_boundedZeroEvent rGrid r} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨R, hR, hbound⟩ := hB (ε : ℝ) (by exact_mod_cast hε)
    let F := nd_crossGeOneSet (d := d) rGrid R r
    have hFc : IsClosed F := nd_isClosed_crossGeOneSet rGrid R r
    -- every level: `P[crossing ≥ 1] ≥ 1 - ε`
    have hpre : ∀ᶠ k in atTop, (1 : ℝ≥0∞) - ENNReal.ofReal (ε : ℝ) ≤
        P (nd_jointSample P H (ξs k) q rGrid (ns k) ⁻¹' F) := by
      filter_upwards [hbound] with k hk
      let X := nd_jointSample P H (ξs k) q rGrid (ns k)
      have hX : Measurable X := nd_measurable_jointSample hH (ξs k) q rGrid (ns k)
      have ha : 0 < aQ P H (ξs k) (ns k) q := tight_aQ_pos hd0 hH (ξs k) (ns k) hq0 hq1
      have hsub : (X ⁻¹' F)ᶜ ⊆
          {ω | acrossDist (ξs k) (fun z => H (ns k) z ω) 0 R r ≤ aQ P H (ξs k) (ns k) q} := by
        intro ω hω
        have hlt : nd_crossPhi 0 R r (X ω).1 < 1 := lt_of_not_ge hω
        change nd_crossPhi 0 R r
          (normMetricC (ξs k) (fun z => H (ns k) z ω) (aQ P H (ξs k) (ns k) q)) < 1 at hlt
        rw [nd_crossPhi_normMetricC ((hH.band (ns k)).continuous ω) ha (ξs k) 0 R r] at hlt
        change acrossDist (ξs k) (fun z => H (ns k) z ω) 0 R r ≤ aQ P H (ξs k) (ns k) q
        simpa only [mul_one] using ((inv_mul_lt_iff₀ ha).1 hlt).le
      have hcompl : P (X ⁻¹' F)ᶜ ≤ ENNReal.ofReal (ε : ℝ) := (measure_mono hsub).trans hk
      apply tsub_le_iff_right.2
      calc (1 : ℝ≥0∞) = P (X ⁻¹' F) + P (X ⁻¹' F)ᶜ :=
            (prob_add_prob_compl (hX hFc.measurableSet)).symm
        _ ≤ P (X ⁻¹' F) + ENNReal.ofReal (ε : ℝ) := add_le_add le_rfl hcompl
    have hlimF := u5_le_measure_of_eventually hH hlim hFc hpre
    have hbarrier := u5_ae_globalOutsideBarrierSet hH hU hq0 hq1 rGrid r hr R hR ns hlim
    have hle : (μ₀ : Measure (nd_Joint d rGrid)) {s | ¬s ∈ nd_boundedZeroEvent rGrid r} ≤
        (μ₀ : Measure (nd_Joint d rGrid)) Fᶜ := by
      apply measure_mono_ae
      filter_upwards [hbarrier] with s hs hbad hFs
      apply hbad
      refine ⟨R, hR, fun x hx => ?_⟩
      have h1 : 1 ≤ nd_crossPhi 0 R r s.1 := hFs
      have h2 : nd_crossPhi 0 R r s.1 ≤ nd_setInf {x} (lsph 0 r) s.1 := hs x hx
      exact lt_of_lt_of_le one_pos (h1.trans h2)
    have hcomp : (μ₀ : Measure (nd_Joint d rGrid)) Fᶜ ≤ (ε : ℝ≥0∞) := by
      rw [prob_compl_eq_one_sub hFc.measurableSet]
      have hsum := tsub_le_iff_right.mp hlimF
      apply tsub_le_iff_right.2
      simpa only [ENNReal.ofReal_coe_nnreal, add_comm] using hsum
    simpa only [zero_add] using hle.trans hcomp
  exact le_antisymm hzero bot_le

end Bounded

end HigherDimLQGContinuity
