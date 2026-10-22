import HigherDimLQGContinuity.MetricVersion.Basic

/-!
# Metric-valued versions (packet E5): the deterministic core

Part C, `c:lem-opt-metric` (the closed metric axioms), `c:lem-opt-proper` (Euclidean topology and properness from the
barrier) and `c:lem-opt-geod` (midpoints and the length property), in deterministic form: a family
`Y : ℝ → C(ℝ^d × ℝ^d, ℝ)` that is

* continuous on an open parameter set `S`,
* a continuous length metric at every rational parameter of `S`,
* positive off the diagonal at every parameter of `S`, and
* uniformly large on far annuli for the parameters of a closed window around each parameter,

is a continuous length metric at every parameter of `S`, and `(ℝ^d, Y ξ)` is proper (`mv_metric_of_family`). The
probabilistic files check these four conditions almost surely for every family with `PosVersionStmt` (files `Weyl`,
`Nondeg`, `Dilation`, `Barrier`), and `Main` assembles `metricVersion_of`.

Route changes (recorded in the handoff): the Euclidean topology (`euclidean_of_small`) is obtained from the first-exit
inequality around each point (no barrier at infinity is needed for it); the barrier at infinity is used for properness
(hence completeness) and to confine approximate midpoints; the length property comes from approximate midpoints of the
rational-parameter metrics (Menger's criterion), and exact midpoints are recovered afterwards from properness
(`Main`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

section Family

variable {S : Set ℝ} {Y : ℝ → C(Rd d × Rd d, ℝ)}

theorem mv_continuousOn_eval (hcont : ContinuousOn Y S) (p : Rd d × Rd d) :
    ContinuousOn (fun ξ => Y ξ p) S :=
  (continuous_eval_const p).comp_continuousOn hcont

theorem mv_continuousOn_mvInf (hcont : ContinuousOn Y S) {K : Set (Rd d × Rd d)} (hK : IsCompact K) :
    ContinuousOn (fun ξ => mvInf K (Y ξ)) S :=
  (continuous_mvInf hK).comp_continuousOn hcont

/-- `c:lem-opt-metric`, deterministic form: the metric axioms at every parameter (closed conditions from the rational
parameters; positivity is a hypothesis). -/
theorem mv_isMetricFn_of_family (hS : IsOpen S) (hcont : ContinuousOn Y S)
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ S → ∃ G : ContMetric d, G.1 = Y q ∧ G.IsLength)
    (hpos : ∀ ξ ∈ S, ∀ x y : Rd d, x ≠ y → 0 < Y ξ (x, y)) {ξ : ℝ} (hξ : ξ ∈ S) :
    IsMetricFn (Y ξ) := by
  refine ⟨fun x => ?_, fun x y hxy => ?_, fun x y => ?_, fun x y z => ?_⟩
  · exact mv_mem_of_rat (C := {F : C(Rd d × Rd d, ℝ) | F (x, x) = 0}) hS hcont
      (isClosed_eq (continuous_eval_const _) continuous_const)
      (fun q hq => by
        obtain ⟨G, hG, -⟩ := hrat q hq
        show Y q (x, x) = 0
        rw [← hG]
        exact G.apply_self x) ξ hξ
  · by_contra hne
    exact (hpos ξ hξ x y hne).ne' hxy
  · exact mv_mem_of_rat (C := {F : C(Rd d × Rd d, ℝ) | F (x, y) = F (y, x)}) hS hcont
      (isClosed_eq (continuous_eval_const _) (continuous_eval_const _))
      (fun q hq => by
        obtain ⟨G, hG, -⟩ := hrat q hq
        show Y q (x, y) = Y q (y, x)
        rw [← hG]
        exact G.apply_comm x y) ξ hξ
  · exact mv_mem_of_rat (C := {F : C(Rd d × Rd d, ℝ) | F (x, z) ≤ F (x, y) + F (y, z)}) hS hcont
      (isClosed_le (continuous_eval_const _) ((continuous_eval_const _).add (continuous_eval_const _)))
      (fun q hq => by
        obtain ⟨G, hG, -⟩ := hrat q hq
        show Y q (x, z) ≤ Y q (x, y) + Y q (y, z)
        rw [← hG]
        exact G.apply_triangle x y z) ξ hξ

/-- The first-exit inequality at every parameter (closed in the parameter; proved at the rational ones, where the
family is a length metric). -/
theorem mv_exit_of_family (hS : IsOpen S) (hcont : ContinuousOn Y S)
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ S → ∃ G : ContMetric d, G.1 = Y q ∧ G.IsLength) {ξ : ℝ} (hξ : ξ ∈ S)
    (c x y : Rd d) {a b : ℝ} (hxa : dist x c ≤ a) (hab : a ≤ b) (hby : b ≤ dist y c) :
    mvInf (sphere c a ×ˢ sphere c b) (Y ξ) ≤ Y ξ (x, y) := by
  have hK : IsCompact (sphere c a ×ˢ sphere c b) := (isCompact_sphere c a).prod (isCompact_sphere c b)
  exact mv_mem_of_rat (C := {F : C(Rd d × Rd d, ℝ) | mvInf (sphere c a ×ˢ sphere c b) F ≤ F (x, y)}) hS
    hcont (isClosed_le (continuous_mvInf hK) (continuous_eval_const _))
    (fun q hq => by
      obtain ⟨G, hG, hGL⟩ := hrat q hq
      show mvInf (sphere c a ×ˢ sphere c b) (Y q) ≤ Y q (x, y)
      rw [← hG]
      exact mvInf_sphere_exit_le hGL c x y hxa hab hby) ξ hξ

/-- `c:lem-opt-proper`, the Euclidean topology (`euclidean_of_small`): small values force small Euclidean
distances, by the first exit from the sphere `∂B_ε(x)` and positivity on the compact set `{x} × ∂B_ε(x)`. -/
theorem mv_euclidean_of_small (hS : IsOpen S) (hcont : ContinuousOn Y S)
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ S → ∃ G : ContMetric d, G.1 = Y q ∧ G.IsLength)
    (hpos : ∀ ξ ∈ S, ∀ x y : Rd d, x ≠ y → 0 < Y ξ (x, y)) {ξ : ℝ} (hξ : ξ ∈ S) :
    ∀ x : Rd d, ∀ ε > 0, ∃ δ > 0, ∀ y : Rd d, Y ξ (x, y) < δ → ‖x - y‖ < ε := by
  intro x ε hε
  by_cases hex : ∃ y₀ : Rd d, ε ≤ ‖x - y₀‖
  · obtain ⟨y₀, hy₀⟩ := hex
    have hxy₀ : x ≠ y₀ := by
      intro h
      rw [h, sub_self, norm_zero] at hy₀
      linarith
    have : Nontrivial (Rd d) := nontrivial_of_ne x y₀ hxy₀
    have hK : IsCompact (sphere x 0 ×ˢ sphere x ε) := (isCompact_sphere x 0).prod (isCompact_sphere x ε)
    obtain ⟨w₀, hw₀⟩ : (sphere x ε).Nonempty := NormedSpace.sphere_nonempty.2 hε.le
    have hx0 : x ∈ sphere x 0 := by rw [mem_sphere, dist_self]
    have hne : (sphere x 0 ×ˢ sphere x ε).Nonempty := ⟨(x, w₀), hx0, hw₀⟩
    obtain ⟨p, hp, hpe⟩ := exists_eq_mvInf hK hne (Y ξ)
    have hδ : 0 < mvInf (sphere x 0 ×ˢ sphere x ε) (Y ξ) := by
      rw [← hpe]
      have h1 : dist p.1 x = 0 := hp.1
      have h2 : dist p.2 x = ε := hp.2
      have hne' : p.1 ≠ p.2 := by
        intro h
        rw [h] at h1
        linarith
      have := hpos ξ hξ p.1 p.2 hne'
      rwa [Prod.mk.eta] at this
    refine ⟨mvInf (sphere x 0 ×ˢ sphere x ε) (Y ξ), hδ, fun y hy => ?_⟩
    by_contra hcon
    push Not at hcon
    have hexit := mv_exit_of_family hS hcont hrat hξ x x y (a := 0) (b := ε) (by rw [dist_self])
      hε.le (by rwa [dist_eq_norm, norm_sub_rev])
    linarith
  · push Not at hex
    exact ⟨1, one_pos, fun y _ => hex y⟩

/-- The point barrier: a uniform annulus barrier on a window and the first exit give, for every `L`, a radius beyond
which all points are at distance `> L` from the origin, for every parameter of the window. -/
theorem mv_point_barrier (hS : IsOpen S) (hcont : ContinuousOn Y S)
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ S → ∃ G : ContMetric d, G.1 = Y q ∧ G.IsLength) {c c' : ℝ}
    (hJ : Icc c c' ⊆ S)
    (hbar : ∀ L : ℝ, ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ ξ ∈ Icc c c', ∀ u w : Rd d, ‖u‖ = a → ‖w‖ = b → L < Y ξ (u, w)) :
    ∀ L : ℝ, ∃ R : ℝ, ∀ ξ ∈ Icc c c', ∀ y : Rd d, R ≤ ‖y‖ → L < Y ξ (0, y) := by
  intro L
  obtain ⟨a, b, ha, hab, h⟩ := hbar L
  refine ⟨b, fun ξ hξ y hy => ?_⟩
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy
    linarith
  have : Nontrivial (Rd d) := nontrivial_of_ne y 0 hy0
  have hK : IsCompact (sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) b) :=
    (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hne : (sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) b).Nonempty :=
    (NormedSpace.sphere_nonempty.2 ha.le).prod (NormedSpace.sphere_nonempty.2 (ha.trans hab).le)
  have hlt : L < mvInf (sphere (0 : Rd d) a ×ˢ sphere (0 : Rd d) b) (Y ξ) := by
    rw [lt_mvInf_iff hK hne]
    rintro ⟨u, w⟩ ⟨hu, hw⟩
    exact h ξ hξ u w (mem_sphere_zero_iff_norm.1 hu) (mem_sphere_zero_iff_norm.1 hw)
  have hexit := mv_exit_of_family hS hcont hrat (hJ hξ) 0 0 y (a := a) (b := b)
    (by rw [dist_self]; exact ha.le) hab.le (by rwa [dist_zero_right])
  linarith

end Family

/-- `c:lem-opt-proper`, properness: if `M(0, y) → ∞` as `|y| → ∞`, every closed `M`-ball is a closed Euclidean-bounded
set, hence compact (`(ℝ^d, M)` carries the Euclidean topology). -/
theorem mv_properSpace {M : ContMetric d}
    (hbar : ∀ L : ℝ, ∃ R : ℝ, ∀ y : Rd d, R ≤ ‖y‖ → L < M.1 (0, y)) : ProperSpace M.Space := by
  refine ⟨fun x r => ?_⟩
  obtain ⟨R, hR⟩ := hbar (M.1 (0, M.unpt x) + r)
  have hA : IsCompact (M.pt ⁻¹' Metric.closedBall x r) := by
    refine (isCompact_closedBall (0 : Rd d) R).of_isClosed_subset
      (Metric.isClosed_closedBall.preimage M.continuous_pt) ?_
    intro v hv
    have hv' : M.1 (M.unpt x, v) ≤ r := by
      have hv0 := Metric.mem_closedBall.mp hv
      change M.1 (v, M.unpt x) ≤ r at hv0
      rwa [M.apply_comm] at hv0
    have htri := M.apply_triangle 0 (M.unpt x) v
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    have := hR v hcon.le
    linarith
  have himg := hA.image M.continuous_pt
  rwa [Set.image_preimage_eq _ (fun y => ⟨M.unpt y, rfl⟩)] at himg

section Family

variable {S : Set ℝ} {Y : ℝ → C(Rd d × Rd d, ℝ)}

/-- `c:lem-opt-geod`, midpoints: approximate midpoints of the rational-parameter metrics (length metrics) near `ξ`,
confined to a fixed ball by the point barrier, are approximate midpoints of the metric at `ξ` (locally uniform
convergence in the parameter). -/
theorem mv_hasApproxMidpoints (hS : IsOpen S) (hcont : ContinuousOn Y S)
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ S → ∃ G : ContMetric d, G.1 = Y q ∧ G.IsLength)
    {ξ c c' : ℝ} (hcξ : c < ξ) (hξc : ξ < c') (hJ : Icc c c' ⊆ S)
    (hbar : ∀ L : ℝ, ∃ R : ℝ, ∀ ξ' ∈ Icc c c', ∀ y : Rd d, R ≤ ‖y‖ → L < Y ξ' (0, y))
    {M : ContMetric d} (hM : M.1 = Y ξ) : HasApproxMidpoints M.Space := by
  intro x y ε hε
  set x' : Rd d := M.unpt x with hx'
  set y' : Rd d := M.unpt y with hy'
  have hξS : ξ ∈ S := hJ ⟨hcξ.le, hξc.le⟩
  set η : ℝ := min (ε / 4) 1 with hηdef
  have hη : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hMxy : 0 ≤ Y ξ (x', y') := by rw [← hM]; exact M.nonneg x' y'
  set L : ℝ := Y ξ (0, x') + Y ξ (x', y') + 3 with hL
  obtain ⟨R, hR⟩ := hbar L
  set R' : ℝ := max R (max ‖x'‖ ‖y'‖) with hR'
  set K : Set (Rd d × Rd d) := closedBall 0 R' ×ˢ closedBall 0 R' with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hx'K : x' ∈ closedBall (0 : Rd d) R' := by
    rw [mem_closedBall, dist_zero_right]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hy'K : y' ∈ closedBall (0 : Rd d) R' := by
    rw [mem_closedBall, dist_zero_right]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have h0K : (0 : Rd d) ∈ closedBall (0 : Rd d) R' := by
    rw [mem_closedBall, dist_self]
    exact (norm_nonneg x').trans ((le_max_left _ _).trans (le_max_right _ _))
  -- rational parameters near `ξ`
  set l : Filter ℝ := 𝓝[S ∩ range ((↑) : ℚ → ℝ)] ξ with hl
  have : l.NeBot := mem_closure_iff_nhdsWithin_neBot.1 (mv_subset_closure_rat hS hξS)
  have hYt : Tendsto Y l (𝓝 (Y ξ)) := (hcont ξ hξS).mono inter_subset_left
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hYt) K hKc
  have h1 : ∀ᶠ q in l, ∀ p ∈ K, dist (Y ξ p) (Y q p) < η :=
    (Metric.tendstoUniformlyOn_iff.1 hunif) η hη
  have h2 : ∀ᶠ q in l, q ∈ Ioo c c' :=
    mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ⟨hcξ, hξc⟩)
  have h3 : ∀ᶠ q in l, q ∈ S ∩ range ((↑) : ℚ → ℝ) := self_mem_nhdsWithin
  obtain ⟨q, hq1, hq2, hq3⟩ := (h1.and (h2.and h3)).exists
  obtain ⟨hqS, r, rfl⟩ := hq3
  have hqJ : (r : ℝ) ∈ Icc c c' := ⟨hq2.1.le, hq2.2.le⟩
  obtain ⟨G, hG, hGL⟩ := hrat r hqS
  obtain ⟨z, hz1, hz2⟩ := hasApproxMidpoints_of_isLengthSpace hGL (G.pt x') (G.pt y') η hη
  set z' : Rd d := G.unpt z with hz'
  -- the midpoint inequalities for `G = Y q`
  have hz1' : Y r (x', z') ≤ Y r (x', y') / 2 + η := by
    have : G.1 (x', z') ≤ G.1 (x', y') / 2 + η := hz1
    rwa [hG] at this
  have hz2' : Y r (y', z') ≤ Y r (x', y') / 2 + η := by
    have : G.1 (y', z') ≤ G.1 (x', y') / 2 + η := hz2
    rwa [hG] at this
  have htri : Y r (0, z') ≤ Y r (0, x') + Y r (x', z') := by
    rw [← hG]
    exact G.apply_triangle 0 x' z'
  -- closeness on `K`
  have hclose : ∀ p ∈ K, |Y ξ p - Y r p| < η := fun p hp => by
    have := hq1 p hp
    rwa [Real.dist_eq] at this
  have e0x := abs_sub_lt_iff.1 (hclose (0, x') ⟨h0K, hx'K⟩)
  have exy := abs_sub_lt_iff.1 (hclose (x', y') ⟨hx'K, hy'K⟩)
  -- the approximate midpoint lies in the ball
  have hz'K : z' ∈ closedBall (0 : Rd d) R' := by
    rw [mem_closedBall, dist_zero_right]
    by_contra hcon
    push Not at hcon
    have hlarge := hR r hqJ z' ((le_max_left _ _).trans hcon.le)
    linarith
  have exz := abs_sub_lt_iff.1 (hclose (x', z') ⟨hx'K, hz'K⟩)
  have eyz := abs_sub_lt_iff.1 (hclose (y', z') ⟨hy'K, hz'K⟩)
  refine ⟨M.pt z', ?_, ?_⟩
  · show M.1 (x', z') ≤ M.1 (x', y') / 2 + ε
    rw [hM]
    linarith
  · show M.1 (y', z') ≤ M.1 (x', y') / 2 + ε
    rw [hM]
    linarith

/-- **The deterministic core of §§5.3–5.4** (`c:lem-opt-metric`, `c:lem-opt-proper`, `c:lem-opt-geod`): a family that
is continuous on an open parameter set, a continuous length metric at its rational parameters, positive off the
diagonal, and uniformly large on far annuli over a rational window around each parameter, is a continuous length
metric at every parameter, and `(ℝ^d, Y ξ)` is proper. -/
theorem mv_metric_of_family (hS : IsOpen S) (hcont : ContinuousOn Y S)
    (hrat : ∀ q : ℚ, (q : ℝ) ∈ S → ∃ G : ContMetric d, G.1 = Y q ∧ G.IsLength)
    (hpos : ∀ ξ ∈ S, ∀ x y : Rd d, x ≠ y → 0 < Y ξ (x, y))
    (hbar : ∀ ξ ∈ S, ∃ c c' : ℝ, c < ξ ∧ ξ < c' ∧ Icc c c' ⊆ S ∧ ∀ L : ℝ, ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ ξ' ∈ Icc c c', ∀ u w : Rd d, ‖u‖ = a → ‖w‖ = b → L < Y ξ' (u, w)) :
    ∀ ξ ∈ S, ∃ M : ContMetric d, M.1 = Y ξ ∧ M.IsLength ∧ ProperSpace M.Space := by
  intro ξ hξ
  let M : ContMetric d :=
    ⟨Y ξ, ⟨mv_isMetricFn_of_family hS hcont hrat hpos hξ, mv_euclidean_of_small hS hcont hrat hpos hξ⟩⟩
  obtain ⟨c, c', hcξ, hξc, hJ, hb⟩ := hbar ξ hξ
  have hpb := mv_point_barrier hS hcont hrat hJ hb
  have hprop : ProperSpace M.Space := mv_properSpace (M := M) (fun L => by
    obtain ⟨R, hR⟩ := hpb L
    exact ⟨R, fun y hy => hR ξ ⟨hcξ.le, hξc.le⟩ y hy⟩)
  refine ⟨M, rfl, ?_, hprop⟩
  exact isLengthSpace_of_hasApproxMidpoints (mv_hasApproxMidpoints hS hcont hrat hcξ hξc hJ hpb (M := M) rfl)

end Family

end HigherDimLQGContinuity
