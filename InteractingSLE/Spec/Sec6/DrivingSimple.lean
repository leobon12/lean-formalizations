import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# Section 6.2: simple paths satisfy the criteria of Proposition 6.12

Specification §6.2 (`source/spec/p193-240.md`, pp. 215–219): the deterministic reductions in the
proofs of Lemma 6.13 and Remarks 6.14–6.15 (and their reuse in the proof of Aux. lemma 76, p. 280).
A continuous injective path in `ℍ̄` from `0` to `∞` (for instance the image of a simple flow line
under a Jordan boundary homeomorphism) satisfies

* the non-crossing convention (Aux. lemma 44, `hasSimpleApproxOn_of_injOn`);
* criterion (a): "If this mapped curve entered a bounded component cut off by one of its initial
  segments and the real boundary, its remaining tail could reach infinity only by crossing that
  initial segment or revisiting one of its attachment points" (p. 216);
* criterion (b) as soon as its real-boundary times have empty interior: "Injectivity already
  excludes retracing of the mapped curve's own past" (p. 217).

## Main results

* `subset_closure_H_diff_fillH`: a preconnected unbounded subset of `ℍ̄` avoiding a compact set `A`
  lies in the closure of the unbounded component `ℍ \ fillH A` of `ℍ \ A`.
* `image_Ioi_subset_closure_of_injOn`, `drivingCriterionA_of_injOn`: criterion (a) for injective
  paths with unbounded futures; `drivingCriterionB_of_injOn`: criterion (b) from empty interior of
  the real-boundary times.
* `drivingCriteria_of_injOn`: all three hypotheses of Proposition 6.12 on every `[0, S] ⊆ D`, for a
  path on an interval `D ∋ 0`; specializations `drivingCriteria_of_injOn_Ici` (`[0, ∞)`, `η → ∞`)
  and `drivingCriteria_of_injOn_Ico` (`[0, T)`, `η(t) → ∞` as `t ↑ T`).
* `drivingCriteria_comp_of_injOn`: the conformal transport in Lemma 6.13 and Remarks 6.14–6.15: the
  image `Ψ ∘ γ` of a simple path `γ` under a continuous injective `Ψ` (the boundary extension of the
  map of a Jordan component `C` onto `ℍ`) satisfies the hypotheses of Proposition 6.12 once the
  times at which `γ` leaves the open component `C` have empty interior.
* `interior_setOf_not_mem_eq_empty_of_frontier_subset`: when `∂C ⊆ K ∪ ℝ` and `γ` stays in `ℍ`
  after time `0`, those times are contact times with `K` (Lemma 6.13: `K` = the range of the other
  flow line; the nowhere density of these contact times is the probabilistic content of
  Lemma 6.13, (MD1)–(MD2), and is a hypothesis here).
* `interior_setOf_mem_union_eq_empty`: Remark 6.14, "Their union is nowhere dense": contact times
  with two closed sets.
* `exists_driver_of_injOn_of_yuanDriverInput`: the continuous driver of such a path, conditional on
  `YuanDriverInput`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec6

/-! ### The unbounded side of a compact set -/

/-- Points of `ℍ̄` far from a bounded set `A` lie in the closure of `ℍ \ fillH A`. -/
theorem mem_closure_H_diff_fillH_of_le_norm {A : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hAR : closure A ⊆ ball 0 R) {z : ℂ} (hz : z ∈ Hbar) (hzR : R ≤ ‖z‖) :
    z ∈ closure (H \ fillH A) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨z + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
  · have hzim : (0 : ℝ) ≤ z.im := hz
    have hwH : z + ((ε / 2 : ℝ) : ℂ) * I ∈ H := by
      show 0 < (z + ((ε / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith
    rw [H_diff_fillH hR hAR]
    refine mem_connectedComponentIn_of_le_norm hR hAR hwH (hzR.trans ?_)
    have h1 : ‖z‖ ^ 2 ≤ ‖z + ((ε / 2 : ℝ) : ℂ) * I‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, normSq_apply, normSq_apply]
      simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
        add_im, mul_im, add_zero]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    exact half_lt_self hε

/-- **The future of a path that never returns stays on the unbounded side** (the topological core of
criterion (a) for simple paths; Specification pp. 216, 218): a preconnected unbounded subset `Q` of
`ℍ̄` disjoint from a compact set `A` lies in the closure of the unbounded component `ℍ \ fillH A`
of `ℍ \ A`. Near a point `q ∈ Q ∩ closure (ℍ \ fillH A)`, a half-disc avoiding `A` is a connected
subset of `ℍ \ A` meeting the unbounded component, so `Q ∩ closure (ℍ \ fillH A)` is relatively
open in `Q`; it is relatively closed, and nonempty because `Q` reaches beyond any disc containing
`A`. -/
theorem subset_closure_H_diff_fillH {A Q : Set ℂ} (hA : IsCompact A) (hQ : IsPreconnected Q)
    (hQH : Q ⊆ Hbar) (hQA : Disjoint Q A) (hQb : ¬ Bornology.IsBounded Q) :
    Q ⊆ closure (H \ fillH A) := by
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball hA.isBounded
  set U := H \ fillH A with hU
  set u : Set ℂ := {z | ∃ r > 0, ball z r ∩ Hbar ⊆ closure U} with hu
  have huo : IsOpen u := by
    rw [Metric.isOpen_iff]
    rintro z ⟨r, hr, hzr⟩
    refine ⟨r / 2, half_pos hr, fun w hw => ⟨r / 2, half_pos hr, fun x hx => hzr ⟨?_, hx.2⟩⟩⟩
    have h1 := mem_ball.1 hx.1
    have h2 := mem_ball.1 hw
    rw [mem_ball]
    calc dist x z ≤ dist x w + dist w z := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add h1 h2
      _ = r := by ring
  have hQuv : Q ⊆ u ∪ (closure U)ᶜ := by
    intro q hq
    by_cases hqc : q ∈ closure U
    · left
      have hqA : q ∉ A := fun h => Set.disjoint_left.1 hQA hq h
      obtain ⟨r, hr, hrA⟩ : ∃ r > 0, ball q r ⊆ Aᶜ :=
        Metric.isOpen_iff.1 hA.isClosed.isOpen_compl q hqA
      refine ⟨r, hr, ?_⟩
      -- the half-disc `ball q r ∩ ℍ` is a connected subset of `ℍ \ A` meeting `U`
      have hconv : Convex ℝ (ball q r ∩ H) := (convex_ball q r).inter
        (convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0)
      obtain ⟨p, hpU, hpB⟩ := Metric.mem_closure_iff.1 hqc r hr
      have hpU' := hpU
      rw [hU, H_diff_fillH hR hAR] at hpU'
      have hsub : ball q r ∩ H ⊆ U := by
        rw [hU, H_diff_fillH hR hAR, connectedComponentIn_eq hpU']
        refine hconv.isPreconnected.subset_connectedComponentIn ⟨?_, hpU.1⟩ ?_
        · rw [mem_ball, dist_comm]; exact hpB
        · rintro w ⟨hwB, hwH⟩
          refine ⟨hwH, ?_⟩
          rw [hA.isClosed.closure_eq]
          exact hrA hwB
      intro w hw
      have h1 : w ∈ closure (ball q r ∩ H) := by
        refine isOpen_ball.inter_closure ⟨hw.1, ?_⟩
        rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hw.2
      exact closure_mono hsub h1
    · exact Or.inr hqc
  have hQuv' : Q ∩ (u ∩ (closure U)ᶜ) = ∅ := by
    ext q
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
    rintro hq ⟨r, hr, hqr⟩
    exact hqr ⟨mem_ball_self hr, hQH hq⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hQ u _ huo isClosed_closure.isOpen_compl
    hQuv hQuv' with h | h
  · intro q hq
    obtain ⟨r, hr, hqr⟩ := h hq
    exact hqr ⟨mem_ball_self hr, hQH hq⟩
  · exfalso
    have hsub : ¬ Q ⊆ ball 0 R := fun h' => hQb (isBounded_ball.subset h')
    obtain ⟨q, hq, hqR⟩ := not_subset.1 hsub
    have hqR' : R ≤ ‖q‖ := not_lt.1 fun h' => hqR (mem_ball_zero_iff.2 h')
    exact h hq (mem_closure_H_diff_fillH_of_le_norm hR hAR (hQH hq) hqR')


/-! ### Criteria (a) and (b) for injective paths -/

/-- A path tending to `∞` along a nontrivial filter `l` has unbounded image of every set in `l`. -/
theorem not_isBounded_image_of_tendsto {η : ℝ → ℂ} {l : Filter ℝ} [l.NeBot] {s : Set ℝ}
    (h : Tendsto η l (Bornology.cobounded ℂ)) (hs : s ∈ l) : ¬ Bornology.IsBounded (η '' s) := by
  intro hb
  obtain ⟨x, hx1, hx2⟩ := Filter.nonempty_of_mem (inter_mem (h.eventually_mem hb) hs)
  exact hx1 (mem_image_of_mem η hx2)

variable {η : ℝ → ℂ} {D : Set ℝ}

/-- **Criterion (a) for injective paths** (Specification p. 216, proof of Lemma 6.13; p. 218,
Remarks 6.14 and 6.15): let `η` be continuous and injective on an interval `D ∋ 0`, with values in
`ℍ̄`, and with unbounded futures `η(D ∩ [u, ∞))`. For `t ∈ D`, the future `η(D ∩ (t, ∞))` lies in
the closure of the unbounded component `ℍ \ K_t` of `ℍ \ η([0, t])`: each future
`η(D ∩ [u, ∞))`, `u > t`, is connected, unbounded and (by injectivity) disjoint from `η([0, t])`. -/
theorem image_Ioi_subset_closure_of_injOn (hD : D.OrdConnected) (hc : ContinuousOn η D)
    (hinj : InjOn η D) (hH : MapsTo η D Hbar) (h0D : (0 : ℝ) ∈ D)
    (hunb : ∀ u ∈ D, ¬ Bornology.IsBounded (η '' (D ∩ Ici u))) {t : ℝ} (ht : t ∈ D) :
    η '' (D ∩ Ioi t) ⊆ closure (H \ fillH (η '' Icc 0 t)) := by
  rintro _ ⟨u, ⟨huD, htu⟩, rfl⟩
  have hIcc : Icc 0 t ⊆ D := hD.out h0D ht
  have hA : IsCompact (η '' Icc 0 t) := isCompact_Icc.image_of_continuousOn (hc.mono hIcc)
  have hQ : IsPreconnected (η '' (D ∩ Ici u)) :=
    (hD.inter ordConnected_Ici).isPreconnected.image η (hc.mono inter_subset_left)
  have hQH : η '' (D ∩ Ici u) ⊆ Hbar := (hH.mono_left inter_subset_left).image_subset
  have hQA : Disjoint (η '' (D ∩ Ici u)) (η '' Icc 0 t) := by
    rw [Set.disjoint_left]
    rintro _ ⟨v, ⟨hvD, huv⟩, rfl⟩ ⟨w, hw, hwv⟩
    have := hinj (hIcc hw) hvD hwv
    have hwt : w ≤ t := hw.2
    have huv' : u ≤ v := huv
    have htu' : t < u := htu
    linarith
  exact subset_closure_H_diff_fillH hA hQ hQH hQA (hunb u huD)
    ⟨u, ⟨huD, show u ≤ u from le_rfl⟩, rfl⟩

/-- Criterion (a) of Proposition 6.12 on `[0, S] ⊆ D` for a path as in
`image_Ioi_subset_closure_of_injOn`. -/
theorem drivingCriterionA_of_injOn (hD : D.OrdConnected) (hc : ContinuousOn η D)
    (hinj : InjOn η D) (hH : MapsTo η D Hbar) (h0D : (0 : ℝ) ∈ D)
    (hunb : ∀ u ∈ D, ¬ Bornology.IsBounded (η '' (D ∩ Ici u))) {S : ℝ} (hSD : Icc 0 S ⊆ D) :
    DrivingCriterionA η S := by
  intro t ht
  have hsub : Ioc t S ⊆ D ∩ Ioi t := fun u hu =>
    ⟨hSD ⟨by linarith [ht.1, hu.1], hu.2⟩, hu.1⟩
  exact (image_mono hsub).trans
    (image_Ioi_subset_closure_of_injOn hD hc hinj hH h0D hunb (hSD ⟨ht.1.le, ht.2.le⟩))

/-- **Criterion (b) for injective paths** (Specification p. 217, "Injectivity already excludes
retracing of the mapped curve's own past"): if `η` is injective on `[0, S]` and its real-boundary
times in `(0, S)` have empty interior, criterion (b) holds. -/
theorem drivingCriterionB_of_injOn {S : ℝ} (hinj : InjOn η (Icc 0 S))
    (hR : interior {u ∈ Ioo 0 S | (η u).im = 0} = ∅) : DrivingCriterionB η S := by
  intro t ht
  refine subset_empty_iff.1 (hR ▸ interior_mono ?_)
  rintro u ⟨hu, h | h⟩
  · exfalso
    obtain ⟨w, hw, hwu⟩ := h
    have := hinj ⟨hw.1, hw.2.trans ht.2.le⟩ ⟨by linarith [ht.1, hu.1], hu.2.le⟩ hwu
    linarith [hw.2, hu.1]
  · exact ⟨⟨by linarith [ht.1, hu.1], hu.2⟩, h⟩

/-- **The hypotheses of Proposition 6.12 for a simple path** (Specification pp. 215–219: the proof
of Lemma 6.13 and Remarks 6.14–6.15; p. 280): let `η` be continuous and injective on an interval
`D ∋ 0` with values in `ℍ̄`, `η 0 = 0`, unbounded futures, and real-boundary times (after `0`) with
empty interior. Then on every `[0, S] ⊆ D`, `S > 0`, `η` is non-crossing (Aux. lemma 44) and
satisfies criteria (a) and (b). -/
theorem drivingCriteria_of_injOn (hD : D.OrdConnected) (hc : ContinuousOn η D)
    (hinj : InjOn η D) (hH : MapsTo η D Hbar) (h0D : (0 : ℝ) ∈ D) (h0 : η 0 = 0)
    (hunb : ∀ u ∈ D, ¬ Bornology.IsBounded (η '' (D ∩ Ici u)))
    (hR : interior {u ∈ D | 0 < u ∧ (η u).im = 0} = ∅) {S : ℝ} (hS : 0 < S) (hSD : S ∈ D) :
    HasSimpleApproxOn η S ∧ DrivingCriterionA η S ∧ DrivingCriterionB η S := by
  have hSD' : Icc 0 S ⊆ D := hD.out h0D hSD
  refine ⟨hasSimpleApproxOn_of_injOn hS (hc.mono hSD') (hinj.mono hSD') h0 (hH.mono_left hSD'),
    drivingCriterionA_of_injOn hD hc hinj hH h0D hunb hSD',
    drivingCriterionB_of_injOn (hinj.mono hSD') (subset_empty_iff.1 (hR ▸ interior_mono ?_))⟩
  rintro u ⟨hu, h⟩
  exact ⟨Ioo_subset_Icc_self.trans hSD' hu, hu.1, h⟩

/-- `drivingCriteria_of_injOn` on `[0, ∞)` for a path tending to `∞`. -/
theorem drivingCriteria_of_injOn_Ici (hc : ContinuousOn η (Ici 0)) (hinj : InjOn η (Ici 0))
    (hH : MapsTo η (Ici 0) Hbar) (h0 : η 0 = 0) (hlim : Tendsto η atTop (Bornology.cobounded ℂ))
    (hR : interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (η u).im = 0} = ∅) {S : ℝ} (hS : 0 < S) :
    HasSimpleApproxOn η S ∧ DrivingCriterionA η S ∧ DrivingCriterionB η S := by
  refine drivingCriteria_of_injOn ordConnected_Ici hc hinj hH self_mem_Ici h0 (fun u _ => ?_) hR
    hS hS.le
  refine not_isBounded_image_of_tendsto hlim (mem_of_superset (Ici_mem_atTop (max 0 u)) ?_)
  intro v hv
  have hv' : max 0 u ≤ v := hv
  exact ⟨show (0 : ℝ) ≤ v from le_trans (le_max_left _ _) hv',
    show u ≤ v from le_trans (le_max_right _ _) hv'⟩

/-- `drivingCriteria_of_injOn` on `[0, T)` for a path with `η(t) → ∞` as `t ↑ T` (the mapped
segments of Remark 6.14 and of Aux. lemma 76, whose terminal point is sent to `∞`). -/
theorem drivingCriteria_of_injOn_Ico {T : ℝ} (hc : ContinuousOn η (Ico 0 T))
    (hinj : InjOn η (Ico 0 T)) (hH : MapsTo η (Ico 0 T) Hbar) (hT : 0 < T) (h0 : η 0 = 0)
    (hlim : Tendsto η (𝓝[<] T) (Bornology.cobounded ℂ))
    (hR : interior {u ∈ Ico (0 : ℝ) T | 0 < u ∧ (η u).im = 0} = ∅) {S : ℝ} (hS : 0 < S)
    (hST : S < T) : HasSimpleApproxOn η S ∧ DrivingCriterionA η S ∧ DrivingCriterionB η S := by
  refine drivingCriteria_of_injOn ordConnected_Ico hc hinj hH ⟨le_rfl, hT⟩ h0 (fun u hu => ?_) hR
    hS ⟨hS.le, hST⟩
  refine not_isBounded_image_of_tendsto hlim (mem_of_superset (Ico_mem_nhdsLT hu.2) ?_)
  intro v hv
  exact ⟨⟨hu.1.trans hv.1, hv.2⟩, hv.1⟩

/-- **A continuous driver for a simple path, conditional on `YuanDriverInput`** (Lemma 6.13 and
Remarks 6.14–6.15 after their geometric reductions; distinct name). -/
theorem exists_driver_of_injOn_of_yuanDriverInput (hY : YuanDriverInput) (hD : D.OrdConnected)
    (hc : ContinuousOn η D) (hinj : InjOn η D) (hH : MapsTo η D Hbar) (h0D : (0 : ℝ) ∈ D)
    (h0 : η 0 = 0) (hunb : ∀ u ∈ D, ¬ Bornology.IsBounded (η '' (D ∩ Ici u)))
    (hR : interior {u ∈ D | 0 < u ∧ (η u).im = 0} = ∅) {S : ℝ} (hS : 0 < S) (hSD : S ∈ D) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ ∃ σ : ℝ → ℝ, σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 S) ∧
      ContinuousOn σ (Icc 0 S) ∧ ∀ t ∈ Icc 0 S, 0 ≤ σ t ∧
        QuantumZipper.fwdHull W (σ t) = fillH (η '' Icc 0 t) ∧
        IsMapOut (fillH (η '' Icc 0 t)) (fun z => QuantumZipper.fwdMap W (σ t) z + W (σ t)) := by
  obtain ⟨h1, h2, h3⟩ := drivingCriteria_of_injOn hD hc hinj hH h0D h0 hunb hR hS hSD
  exact exists_driver_of_drivingCriteria_of_yuanDriverInput hY hS
    (hc.mono (hD.out h0D hSD)) h0 h1 h2 h3

/-! ### Conformal transport: Lemma 6.13 and Remarks 6.14–6.15 -/

/-- If a map `Ψ` sends the open component `C` into `ℍ`, the real-boundary times of `Ψ ∘ γ` are
times at which `γ` is outside `C`. -/
theorem setOf_im_comp_eq_zero_subset {Ψ : ℂ → ℂ} {C : Set ℂ} {γ : ℝ → ℂ} (hΨC : MapsTo Ψ C H) :
    {u ∈ D | 0 < u ∧ ((Ψ ∘ γ) u).im = 0} ⊆ {u ∈ D | 0 < u ∧ γ u ∉ C} := by
  rintro u ⟨hu, hu0, h⟩
  exact ⟨hu, hu0, fun hC => (show (0 : ℝ) < (Ψ (γ u)).im from hΨC hC).ne' h⟩

/-- The transported path tends to `∞` when `γ` does and `Ψ` is proper at `∞` on `E`
(`Ψ(z) → ∞` as `z → ∞` in `E`; for the maps of Lemma 6.13, `ψ(∞) = ∞`). -/
theorem tendsto_comp_cobounded {Ψ : ℂ → ℂ} {E : Set ℂ} {γ : ℝ → ℂ} {l : Filter ℝ}
    (hΨ : Tendsto Ψ (Bornology.cobounded ℂ ⊓ 𝓟 E) (Bornology.cobounded ℂ))
    (hγ : Tendsto γ l (Bornology.cobounded ℂ)) (hγE : ∀ᶠ u in l, γ u ∈ E) :
    Tendsto (Ψ ∘ γ) l (Bornology.cobounded ℂ) :=
  hΨ.comp (tendsto_inf.2 ⟨hγ, tendsto_principal.2 hγE⟩)

/-- **The geometric reduction of Lemma 6.13 and Remarks 6.14–6.15** (Specification pp. 215–219):
let `γ` be a simple path on an interval `D ∋ 0` (continuous, injective) with values in a set `E`,
and let `Ψ` be continuous and injective on `E` with values in `ℍ̄`, mapping the open component
`C ⊆ E` into `ℍ`, with `Ψ(γ 0) = 0` (in the source, `E = C̄` and `Ψ = ψ` is the Jordan boundary
homeomorphism of `C` onto `ℍ̄` with `ψ(0) = 0`, `ψ(∞) = ∞`). If the transported futures are
unbounded and the set of times at which `γ` is outside `C` has empty interior, then on every
`[0, S] ⊆ D` the path `Ψ ∘ γ` is non-crossing (Aux. lemma 44) and satisfies criteria (a) and (b) of
Proposition 6.12. -/
theorem drivingCriteria_comp_of_injOn {Ψ : ℂ → ℂ} {E C : Set ℂ} {γ : ℝ → ℂ}
    (hD : D.OrdConnected) (h0D : (0 : ℝ) ∈ D) (hc : ContinuousOn γ D) (hinj : InjOn γ D)
    (hγE : MapsTo γ D E) (hΨc : ContinuousOn Ψ E) (hΨi : InjOn Ψ E) (hΨE : MapsTo Ψ E Hbar)
    (hΨC : MapsTo Ψ C H) (h0 : Ψ (γ 0) = 0)
    (hunb : ∀ u ∈ D, ¬ Bornology.IsBounded ((Ψ ∘ γ) '' (D ∩ Ici u)))
    (hC : interior {u ∈ D | 0 < u ∧ γ u ∉ C} = ∅) {S : ℝ} (hS : 0 < S) (hSD : S ∈ D) :
    HasSimpleApproxOn (Ψ ∘ γ) S ∧ DrivingCriterionA (Ψ ∘ γ) S ∧
      DrivingCriterionB (Ψ ∘ γ) S :=
  drivingCriteria_of_injOn hD (hΨc.comp hc hγE) (hΨi.comp hinj hγE) (hΨE.comp hγE) h0D h0 hunb
    (subset_empty_iff.1 (hC ▸ interior_mono (setOf_im_comp_eq_zero_subset hΨC))) hS hSD

/-- **Times outside the component are contact times** (Lemma 6.13: "It remains to exclude an
interval spent on the real boundary"): if `γ` stays in `closure C`, lies in `ℍ` after time `0`, and
`∂C ⊆ K ∪ ℝ` (for the right component of `ℍ \ η_{θ₂}`, `K` = the range of `η_{θ₂}`), then every
time `u > 0` at which `γ` is outside `C` is a time at which `γ` is on `K`. -/
theorem setOf_not_mem_subset_of_frontier_subset {C K : Set ℂ} {γ : ℝ → ℂ}
    (hγC : MapsTo γ D (closure C)) (hγH : ∀ u ∈ D, 0 < u → γ u ∈ H)
    (hfr : frontier C ⊆ K ∪ {z : ℂ | z.im = 0}) :
    {u ∈ D | 0 < u ∧ γ u ∉ C} ⊆ {u ∈ D | γ u ∈ K} := by
  rintro u ⟨hu, hu0, hC⟩
  refine ⟨hu, ?_⟩
  rcases hfr ⟨hγC hu, fun h => hC (interior_subset h)⟩ with h | h
  · exact h
  · exact absurd h (show (0 : ℝ) < (γ u).im from hγH u hu hu0).ne'

/-- The interior form of `setOf_not_mem_subset_of_frontier_subset`: if the contact times with `K`
have empty interior (the probabilistic content of Lemma 6.13, (MD1)–(MD2)), so do the times outside
`C`. -/
theorem interior_setOf_not_mem_eq_empty_of_frontier_subset {C K : Set ℂ} {γ : ℝ → ℂ}
    (hγC : MapsTo γ D (closure C)) (hγH : ∀ u ∈ D, 0 < u → γ u ∈ H)
    (hfr : frontier C ⊆ K ∪ {z : ℂ | z.im = 0}) (hK : interior {u ∈ D | γ u ∈ K} = ∅) :
    interior {u ∈ D | 0 < u ∧ γ u ∉ C} = ∅ :=
  subset_empty_iff.1 (hK ▸ interior_mono (setOf_not_mem_subset_of_frontier_subset hγC hγH hfr))

/-- **Remark 6.14, "Their union is nowhere dense"**: for a path continuous on `D` and closed `K₁`,
if the contact times with `K₁` and with `K₂` both have empty interior, so do the contact times with
`K₁ ∪ K₂`. (Inside the open set `X` of the union, the times off `K₁` form an open set of contact
times with `K₂`, hence are empty; so `X` consists of contact times with `K₁`.) -/
theorem interior_setOf_mem_union_eq_empty {γ : ℝ → ℂ} {K₁ K₂ : Set ℂ} (hc : ContinuousOn γ D)
    (hK₁ : IsClosed K₁) (h₁ : interior {u ∈ D | γ u ∈ K₁} = ∅)
    (h₂ : interior {u ∈ D | γ u ∈ K₂} = ∅) : interior {u ∈ D | γ u ∈ K₁ ∪ K₂} = ∅ := by
  set X := interior {u ∈ D | γ u ∈ K₁ ∪ K₂} with hX
  have hXD : X ⊆ D := fun u hu => (interior_subset hu).1
  have hO : IsOpen (X ∩ γ ⁻¹' K₁ᶜ) :=
    (hc.mono hXD).isOpen_inter_preimage isOpen_interior hK₁.isOpen_compl
  have hO₂ : X ∩ γ ⁻¹' K₁ᶜ ⊆ interior {u ∈ D | γ u ∈ K₂} := by
    refine interior_maximal ?_ hO
    rintro u ⟨hu, hu1⟩
    obtain ⟨huD, h | h⟩ := interior_subset hu
    · exact absurd h hu1
    · exact ⟨huD, h⟩
  rw [h₂, subset_empty_iff] at hO₂
  have hX₁ : X ⊆ interior {u ∈ D | γ u ∈ K₁} := by
    refine interior_maximal (fun u hu => ⟨hXD hu, ?_⟩) isOpen_interior
    by_contra h
    have : u ∈ X ∩ γ ⁻¹' K₁ᶜ := ⟨hu, h⟩
    rw [hO₂] at this
    exact this
  rw [h₁] at hX₁
  exact subset_empty_iff.1 hX₁

/-- **The rational-interval reduction of (MD1)** (Lemma 6.13: "If it had nonempty interior …, some
fixed rational `0 < a < b < ∞` would satisfy `η_{θ₁}([a, b]) ⊆ η_{θ₂}`"): a set of positive times
has empty interior as soon as it contains no interval `[a, b]` with rational endpoints
`0 < a < b`. -/
theorem interior_eq_empty_of_forall_rat {X : Set ℝ} (hX : X ⊆ Ioi 0)
    (h : ∀ a b : ℚ, 0 < a → a < b → ¬ Icc (a : ℝ) b ⊆ X) : interior X = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
  have hx0 : 0 < x := hX (interior_subset hx)
  obtain ⟨ε, hε, hεX⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set δ := min ε x with hδ
  have hδ0 : 0 < δ := lt_min hε hx0
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x - δ / 2 < x by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x < x + δ / 2 by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδx : δ ≤ x := min_le_right _ _
  refine h a b (by exact_mod_cast (show (0 : ℝ) < a by linarith))
    (by exact_mod_cast ha2.trans hb1) fun u hu => interior_subset (hεX ?_)
  rw [mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hu.1, hu.2]

/-- The converse direction of `interior_eq_empty_of_forall_rat` (a set with empty interior contains
no nondegenerate interval). -/
theorem not_Icc_subset_of_interior_eq_empty {X : Set ℝ} (hX : interior X = ∅) {a b : ℝ}
    (hab : a < b) : ¬ Icc a b ⊆ X := fun h => by
  have := interior_mono (Ioo_subset_Icc_self.trans h)
  rw [isOpen_Ioo.interior_eq, hX] at this
  exact (nonempty_Ioo.2 hab).ne_empty (subset_empty_iff.1 this)

end InteractingSLE.Sec6
