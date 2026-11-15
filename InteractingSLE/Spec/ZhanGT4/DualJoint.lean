/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.FrozenMeas

/-!
# Measurability of the factors of `M̃` with a **random** frozen hull

Packet PROVE-ZHAN-GT4-A13. Source: Astra, *Follow-up proofs*, §A.1.2–A.1.4 (`ig1_followup_proofs.txt` L268–L380, R38).
The density `M(s, t)` of §A.1.3–A.1.4 is a function of **both** curves. With curve `1` growing and curve `2` stopped,
the hull `A = K₂(t)`, its chart `φ = g^{(2)}_t` and the marks `ζ₀ = W₂(t)`, `ζ_m = g^{(2)}_t(p_m)` are random, and the
factors `A_{1,k}`, `A_{2,0}`, `A_{2,1}`, `B_{m,0}`, `B_{m,1}`, `log F` must be measurable on the space carrying both
curves. `FrozenMeas.lean` (A8) proves this for a deterministic hull, where the closure of the random image
`E_t = g_t(A)` is dyadic-hit measurable because `A` has a fixed countable dense subset.

Here the hull, the chart and the marks are arbitrary functions of `ω`. The inputs are bundled in `FrzMeasR`:

* the dyadic-hit measurability of `closure E_t` (`hit`; supplied for two independent Loewner hulls in
  `DualJointHit.lean`);
* the joint measurability, in the point and `ω`, of the alive event and the forward map of curve `1` (`alive`,
  `fwd`), so that the forward map can be evaluated at random points;
* for each real mark `ζ` of the `φ`-chart, a sequence of random points `q n ω ∈ ℍ \ A ω` of the original chart with
  `φ(q n) → ζ` (`MarkSeq`): this replaces A8's fixed points `φ⁻¹(ζ + i/(n+1))`.

The values are A8's choice-based factors (`frzA`, `frzImg`, `frzImgD`, `frzLogF`) for **any** choice of the image
data `W' ω`, `a ω`; their measurability comes from canonical identifications (the mapping-out function of `E_t`,
forward limits), exactly as in A8.

## Main results

* `FrzMeasR.measurable_mapOut`, `FrzMeasR.measurable_frzA` (`A_{1,k}`);
* `FrzMeasR.measurable_frzImg`, `FrzMeasR.measurable_frzImgD` (`A_{2,0}`, `B_{m,0}`, `A_{2,1}`, `B_{m,1}/φ'(p_m)`);
* `FrzMeasR.measurable_frzRate`, `measurable_frzLogFR` (`log F`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull)

section OwnR

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The alive pairs `(z, ω)`, `ω ∈ G`, `z ∈ ℍ` not swallowed by time `t` under `W ω`. -/
def aliveR (W : Ω → ℝ → ℝ) (G : Set Ω) (t : ℝ) : Set (ℂ × Ω) :=
  {p | p.2 ∈ G ∧ p.1 ∈ H ∧ ∃ u, IsForwardSol (W p.2) p.1 t u}

open scoped Classical in
/-- The random compact set `closure E_t` (`∅` off `G`), `E_t = g_t(A ω)`. -/
def hullKR (W : Ω → ℝ → ℝ) (A : Ω → Set ℂ) (G : Set Ω) (t : ℝ) (ω : Ω) : Set ℂ :=
  if ω ∈ G then closure (imgHull (W ω) (A ω) t) else ∅

/-- **The measurability inputs at time `t`, random hull.** On a measurable event `G`, `OwnData` holds up to
`T ω ≥ t` for the random hull `A ω` with chart `φ ω`; the driver value `W_t` is measurable; the alive event and the
forward map are jointly measurable in the point and `ω`; the closure of `E_t = g_t(A ω)` is dyadic-hit
measurable. -/
structure FrzMeasR (W W' a : Ω → ℝ → ℝ) (A : Ω → Set ℂ) (φ : Ω → ℂ → ℂ) (T : Ω → ℝ) (G : Set Ω) (t : ℝ) :
    Prop where
  meas : MeasurableSet G
  own : ∀ ω ∈ G, OwnData (W ω) (A ω) (φ ω) (T ω) (a ω) (W' ω)
  mem : ∀ ω ∈ G, t ∈ Icc 0 (T ω)
  drv : Measurable fun ω => W ω t
  alive : MeasurableSet (aliveR W G t)
  fwd : Measurable ((aliveR W G t).indicator fun p => fwdMap (W p.2) t p.1)
  hit : Restart.IsDyadicHitMeasurable (hullKR W A G t)

/-- **A real mark of the `φ`-chart seen from the original chart**: measurable random points `q n ω ∈ ℍ`, eventually
off `A ω` (a measurable event for each `n`), with `φ ω (q n ω)` measurable (on `G`) and tending to the mark `ζ ω`. -/
structure MarkSeq (A : Ω → Set ℂ) (φ : Ω → ℂ → ℂ) (G : Set Ω) (ζ : Ω → ℝ) (q : ℕ → Ω → ℂ) : Prop where
  memH : ∀ ω ∈ G, ∀ n, q n ω ∈ H
  measA : ∀ n, MeasurableSet {ω | q n ω ∈ A ω}
  ev : ∀ ω ∈ G, ∀ᶠ n in atTop, q n ω ∉ A ω
  meas : ∀ n, Measurable (q n)
  img : ∀ n, Measurable (G.indicator fun ω => φ ω (q n ω))
  lim : ∀ ω ∈ G, Tendsto (fun n => φ ω (q n ω)) atTop (𝓝 (ζ ω : ℂ))

/-- The mark is measurable (on `G`): the limit of the measurable `φ(q n)`. -/
theorem MarkSeq.measurable_mark {A : Ω → Set ℂ} {φ : Ω → ℂ → ℂ} {G : Set Ω} {ζ : Ω → ℝ} {q : ℕ → Ω → ℂ}
    (hq : MarkSeq A φ G ζ q) : Measurable (G.indicator fun ω => (ζ ω : ℂ)) := by
  refine measurable_of_tendsto_metrizable (f := fun n => G.indicator fun ω => φ ω (q n ω)) hq.img ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
    exact hq.lim ω hω
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

namespace FrzMeasR

variable {W W' a : Ω → ℝ → ℝ} {A : Ω → Set ℂ} {φ : Ω → ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {t : ℝ}
  (hM : FrzMeasR W W' a A φ T G t)
include hM

theorem isHPHull {ω : Ω} (hω : ω ∈ G) : IsHPHull (imgHull (W ω) (A ω) t) :=
  (hM.own ω hω).isHPHull_E (hM.mem ω hω)

theorem notMem_fwdHull {ω : Ω} (hω : ω ∈ G) {z : ℂ} (hz : z ∈ A ω) : z ∉ fwdHull (W ω) t :=
  fun hK => Set.disjoint_left.1 ((hM.own ω hω).disjoint_A_K (hM.mem ω hω)) hz hK

omit [MeasurableSpace Ω] hM in
theorem setOf_alive_at_eq {q : Ω → ℂ} (hqH : ∀ ω ∈ G, q ω ∈ H) :
    {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (q ω) t u} = (fun ω => (q ω, ω)) ⁻¹' aliveR W G t := by
  ext ω
  simp only [mem_ofPred_eq, mem_preimage, aliveR]
  exact ⟨fun h => ⟨h.1, hqH ω h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

/-- The alive event of a measurable random point of `ℍ` is measurable. -/
theorem measurableSet_alive_at {q : Ω → ℂ} (hq : Measurable q) (hqH : ∀ ω ∈ G, q ω ∈ H) :
    MeasurableSet {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (q ω) t u} := by
  rw [setOf_alive_at_eq hqH]
  exact (hq.prodMk measurable_id) hM.alive

/-- The forward map at a measurable random point of `ℍ` is measurable on its alive event. -/
theorem measurable_fwd_at {q : Ω → ℂ} (hq : Measurable q) (hqH : ∀ ω ∈ G, q ω ∈ H) :
    Measurable ({ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (q ω) t u}.indicator fun ω => fwdMap (W ω) t (q ω)) := by
  have h := hM.fwd.comp (hq.prodMk (measurable_id (α := Ω)))
  rw [setOf_alive_at_eq hqH]
  convert h using 1
  funext ω
  by_cases hω : ω ∈ (fun ω => (q ω, ω)) ⁻¹' aliveR W G t
  · rw [indicator_of_mem hω, Function.comp_apply, id_eq, indicator_of_mem (show (q ω, ω) ∈ aliveR W G t from hω)]
  · rw [indicator_of_notMem hω, Function.comp_apply, id_eq,
      indicator_of_notMem (show (q ω, ω) ∉ aliveR W G t from hω)]

omit hM in
theorem isCompact_hullKR (hM : FrzMeasR W W' a A φ T G t) (ω : Ω) : IsCompact (hullKR W A G t ω) := by
  unfold hullKR
  split_ifs with hω
  · exact (hM.isHPHull hω).2.1.isCompact_closure
  · exact isCompact_empty

omit hM in
theorem isPreconnected_hullKR (hM : FrzMeasR W W' a A φ T G t) (ω : Ω) :
    IsPreconnected (hullKR W A G t ω ∪ Restart.lowerHalf) := by
  unfold hullKR
  split_ifs with hω
  · have h := (hM.isHPHull hω).isPreconnected_union_lowerHalf.closure
    rw [closure_union, (_root_.InteractingSLE.isClosed_lowerHalf).closure_eq] at h
    exact h
  · rw [empty_union]
    exact _root_.InteractingSLE.isPreconnected_lowerHalf

theorem fillH_hullKR {ω : Ω} (hω : ω ∈ G) : fillH (hullKR W A G t ω) = imgHull (W ω) (A ω) t := by
  simp only [hullKR, hω, ↓reduceIte]
  have h1 : fillH (closure (imgHull (W ω) (A ω) t)) = fillH (imgHull (W ω) (A ω) t) :=
    fillH_congr (by rw [closure_closure])
  rw [h1]
  exact (hM.isHPHull hω).fillH_eq

theorem measurableSet_mem_diff (z : ℂ) : MeasurableSet {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t} := by
  have heq : {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t} = G ∩ {ω | z ∈ H \ fillH (hullKR W A G t ω)} := by
    ext ω
    constructor
    · rintro ⟨hω, hz⟩
      exact ⟨hω, by rwa [mem_ofPred_eq, hM.fillH_hullKR hω]⟩
    · rintro ⟨hω, hz⟩
      rw [mem_ofPred_eq, hM.fillH_hullKR hω] at hz
      exact ⟨hω, hz⟩
  rw [heq]
  exact hM.meas.inter (Restart.measurableSet_mem_H_diff_fillH hM.hit hM.isCompact_hullKR z)

/-- The mapping-out function of `E_t` is measurable at fixed points of its domain. -/
theorem measurable_mapOut (z : ℂ) :
    Measurable ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t}.indicator fun ω =>
      ConformalImage.mapOut (imgHull (W ω) (A ω) t) z) := by
  have heq : ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t}.indicator fun ω =>
      ConformalImage.mapOut (imgHull (W ω) (A ω) t) z) = G.indicator ({ω | z ∈ H \ fillH (hullKR W A G t ω)}.indicator
        fun ω => ConformalImage.mapOut (fillH (hullKR W A G t ω)) z) := by
    funext ω
    by_cases hω : ω ∈ G
    · have hf := hM.fillH_hullKR hω
      by_cases hz : z ∈ H \ imgHull (W ω) (A ω) t
      · have h1 : ω ∈ {ω | z ∈ H \ fillH (hullKR W A G t ω)} := by rw [mem_ofPred_eq, hf]; exact hz
        rw [indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t} from ⟨hω, hz⟩),
          indicator_of_mem hω, indicator_of_mem h1, hf]
      · have h1 : ω ∉ {ω | z ∈ H \ fillH (hullKR W A G t ω)} := by rw [mem_ofPred_eq, hf]; exact hz
        rw [indicator_of_notMem (fun h => hz h.2), indicator_of_mem hω, indicator_of_notMem h1]
    · rw [indicator_of_notMem (fun h => hω h.1), indicator_of_notMem hω]
  rw [heq]
  exact (Restart.measurable_indicator_mapOut hM.hit hM.isCompact_hullKR hM.isPreconnected_hullKR z).indicator
    hM.meas

/-- Iterated derivatives of the mapping-out function of `E_t` are measurable at fixed points. -/
theorem measurable_iterDeriv_mapOut (k : ℕ) (z : ℂ) :
    Measurable ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t}.indicator fun ω =>
      deriv^[k] (ConformalImage.mapOut (imgHull (W ω) (A ω) t)) z) :=
  measurable_indicator_iterDeriv (fun _ hω => (hM.isHPHull hω).2.2.1) hM.measurableSet_mem_diff
    (fun _ hω => (ConformalImage.isMapOut_mapOut (hM.isHPHull hω)).1.1) hM.measurable_mapOut k z

/-- **`F_t^{(k)}(W_t)` is measurable**, `F_t = ownExt … t`: a forward limit of `R_t^{(k)}` at `W_t` along `ℍ \ E_t`
(`R_t` the mapping-out function of `E_t`). As `FrozenMeas.FrzMeas.measurable_iterDeriv_ownExt`. -/
theorem measurable_iterDeriv_ownExt (k : ℕ) :
    Measurable (G.indicator fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t) (W ω t)) := by
  refine measurable_indicator_of_tendsto' hM.meas (D := fun ω => H \ imgHull (W ω) (A ω) t)
    (f := fun ω => deriv^[k] (ConformalImage.mapOut (imgHull (W ω) (A ω) t))) (q := fun ω => (W ω t : ℂ))
    (fun ω hω => (hM.isHPHull hω).2.2.1) hM.measurableSet_mem_diff (hM.measurable_iterDeriv_mapOut k)
    ((Complex.measurable_ofReal.comp hM.drv).indicator hM.meas) (fun ω hω => ?_) (fun ω hω => ?_)
  · obtain ⟨ρ, hρ, hcl⟩ := (hM.own ω hω).exists_clearance
    have hdisj := hcl t (hM.mem ω hω)
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hs : 0 < min ε ρ / 2 := by positivity
    have hlt : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have hlt' : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hd : dist (W ω t : ℂ) ((W ω t : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I) = min ε ρ / 2 := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    refine ⟨(W ω t : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I, ⟨?_, fun hE => ?_⟩, by rw [hd]; exact hlt'⟩
    · show 0 < ((W ω t : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      exact hs
    · refine Set.disjoint_left.1 hdisj ?_ hE
      rw [mem_ball, dist_comm, hd]
      exact hlt
  · obtain ⟨ρ, hρ, hcl⟩ := (hM.own ω hω).exists_clearance
    obtain ⟨hd, -, -, -, -, hR⟩ := (hM.own ω hω).ownExt_props (hM.mem ω hω) (hcl t (hM.mem ω hω))
    have hR' := hR _ (ConformalImage.isMapOut_mapOut (hM.isHPHull hω))
    have hc : ContinuousAt (deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t)) (W ω t) :=
      (differentiableOn_iterate_deriv hd isOpen_ball k).continuousOn.continuousAt
        (ball_mem_nhds _ (half_pos hρ))
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (W ω t : ℂ) (half_pos hρ)),
      self_mem_nhdsWithin] with z hz1 hz2
    have hU : IsOpen (ball (W ω t : ℂ) (ρ / 2) ∩ H) := isOpen_ball.inter QuantumZipper.isOpen_H
    exact (eventuallyEq_iterate_deriv (Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hz1, hz2.1⟩) hR') k).eq_of_nhds

/-- **`A_{1,k}(t) = frzA … k t` is measurable** (on `G`), random hull. -/
theorem measurable_frzA (k : ℕ) : Measurable (G.indicator fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) k t) := by
  have heq : (G.indicator fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) k t) = fun ω =>
      (G.indicator (fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) (φ ω) t) (W ω t)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzA]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_iterDeriv_ownExt k)

/-! #### The image chain at a real mark -/

theorem mem_Icc_clock {ω : Ω} (hω : ω ∈ G) : a ω t ∈ Icc 0 (a ω (T ω)) := by
  have h := hM.own ω hω
  have ht := hM.mem ω hω
  have hT : 0 ≤ T ω := ht.1.trans ht.2
  refine ⟨?_, h.mono.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
  rw [← h.a0]
  exact h.mono.monotoneOn ⟨le_rfl, hT⟩ ht ht.1

/-- At a real mark `ζ` alive for the image chain up to `a(T)`, along points `q n ∈ ℍ`, eventually off `A`, with
`φ(q n) → ζ`: eventually `q n ∉ A` is alive at `t`, `g̃_{a(t)}(φ(q n)) → g̃_{a(t)}(ζ)`, and `g̃_{a(t)}` is complex
differentiable at `ζ`. -/
theorem mark_facts {ζ : ℝ} {ω : Ω} (hω : ω ∈ G) (hv : ∃ v, IsForwardSol (W' ω) (ζ : ℂ) (a ω (T ω)) v)
    {q : ℕ → ℂ} (hqH : ∀ n, q n ∈ H) (hqA : ∀ᶠ n in atTop, q n ∉ A ω)
    (hlim : Tendsto (fun n => φ ω (q n)) atTop (𝓝 (ζ : ℂ))) :
    (∀ᶠ n in atTop, q n ∉ A ω ∧ ∃ u, IsForwardSol (W ω) (q n) t u) ∧
    Tendsto (fun n => fwdMap (W' ω) (a ω t) (φ ω (q n))) atTop (𝓝 (fwdMap (W' ω) (a ω t) ζ)) ∧
    HasDerivAt (fwdMap (W' ω) (a ω t)) (deriv (fwdMap (W' ω) (a ω t)) ζ) ζ := by
  obtain ⟨v, hv⟩ := hv
  have h := hM.own ω hω
  have ht := hM.mem ω hω
  have hat := hM.mem_Icc_clock hω
  have hS : 0 ≤ a ω (T ω) := hat.1.trans hat.2
  obtain ⟨δ, hδ, hlow, hmem⟩ := exists_aliveDisc_self hv hS
  have hder := hasDerivAt_fwdMap_aliveDisc h.contW' hv hδ hlow hmem hat
  refine ⟨?_, hder.continuousAt.tendsto.comp hlim, hder.differentiableAt.hasDerivAt⟩
  filter_upwards [hlim.eventually (ball_mem_nhds (ζ : ℂ) (aliveRad_pos hδ)), hqA] with n hn hnA
  refine ⟨hnA, QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht.1 (hqH n) fun hK => ?_⟩
  have h1 : φ ω (q n) ∈ fwdHull (W' ω) (a ω t) := by rw [h.img t ht]; exact ⟨_, hK, rfl⟩
  have hyH : φ ω (q n) ∈ H := h.mapOut.1.2.mapsTo ⟨hqH n, hnA⟩
  obtain ⟨v', hv', -⟩ := exists_sol_aliveDisc h.contW' hv hδ hlow hn
  exact Ito.notMem_fwdHull_of_isForwardSol h.contW' hyH hS hv' (QuantumZipper.fwdHull_mono.1 hat.2 h1)

/-- On the event that `q` is alive at `t`: `g_t(q) + W_t ∈ ℍ \ E_t`, and the mapping-out function of `E_t` there is
`g̃_{a(t)}(φ(q)) + W'(a(t))` (the rate identity of `OwnData`). -/
theorem mark_eval {ω : Ω} (hω : ω ∈ G) {q : ℂ} (hqA : q ∈ H \ A ω) (hal : ∃ u, IsForwardSol (W ω) q t u) :
    fwdMap (W ω) t q + (W ω t : ℂ) ∈ H \ imgHull (W ω) (A ω) t ∧
      ConformalImage.mapOut (imgHull (W ω) (A ω) t) (fwdMap (W ω) t q + (W ω t : ℂ)) =
        fwdMap (W' ω) (a ω t) (φ ω q) + (W' ω (a ω t) : ℂ) := by
  have h := hM.own ω hω
  have ht := hM.mem ω hω
  obtain ⟨u, hu⟩ := hal
  have hzK : q ∉ fwdHull (W ω) t := Ito.notMem_fwdHull_of_isForwardSol h.cont hqA.1 ht.1 hu
  have hbij := (isMapOut_fwdMap h.cont h.zero ht.1).1.2
  refine ⟨⟨hbij.mapsTo ⟨hqA.1, hzK⟩, ?_⟩, ?_⟩
  · rintro ⟨b, hb, hbe⟩
    have := hbij.injOn ⟨h.hull.1 hb, hM.notMem_fwdHull hω hb⟩ ⟨hqA.1, hzK⟩ hbe
    exact hqA.2 (this ▸ hb)
  · have hr := (h.rate t ht _ (ConformalImage.isMapOut_mapOut (hM.isHPHull hω))).1 q
      ⟨hqA.1, fun h' => h'.elim hqA.2 hzK⟩
    exact hr.symm

variable {ζ : Ω → ℝ} {q : ℕ → Ω → ℂ}

/-- The alive event of `q n` off `A`. -/
def markEv (W : Ω → ℝ → ℝ) (A : Ω → Set ℂ) (G : Set Ω) (t : ℝ) (q : Ω → ℂ) : Set Ω :=
  {ω | ω ∈ G ∧ q ω ∉ A ω ∧ ∃ u, IsForwardSol (W ω) (q ω) t u}

theorem measurableSet_markEv (hq : MarkSeq A φ G ζ q) (n : ℕ) : MeasurableSet (markEv W A G t (q n)) := by
  have heq : markEv W A G t (q n) = {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (q n ω) t u} ∩ {ω | q n ω ∈ A ω}ᶜ := by
    ext ω
    simp only [markEv, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    tauto
  rw [heq]
  exact (hM.measurableSet_alive_at (hq.meas n) fun ω hω => hq.memH ω hω n).inter (hq.measA n).compl

/-- The value of the mapping-out function of `E_t` at `g_t(q n) + W_t`, on the event that `q n ∉ A` is alive. -/
theorem measurable_markVal (hq : MarkSeq A φ G ζ q) (n : ℕ) :
    Measurable ((markEv W A G t (q n)).indicator fun ω =>
      ConformalImage.mapOut (imgHull (W ω) (A ω) t) (fwdMap (W ω) t (q n ω) + (W ω t : ℂ))) := by
  set Gn := markEv W A G t (q n) with hGn
  have hS : MeasurableSet Gn := hM.measurableSet_markEv hq n
  have hGnsub : Gn ⊆ {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (q n ω) t u} := fun ω hω => ⟨hω.1, hω.2.2⟩
  refine measurable_indicator_eval (D := fun ω => H \ imgHull (W ω) (A ω) t)
    (f := fun ω => ConformalImage.mapOut (imgHull (W ω) (A ω) t)) hS (fun _ hω => (hM.isHPHull hω.1).2.2.1)
    (fun z => ?_) (fun z => ?_) (fun _ hω => (ConformalImage.isMapOut_mapOut (hM.isHPHull hω.1)).1.1.continuousOn)
    ?_ fun ω hω => (hM.mark_eval hω.1 ⟨hq.memH ω hω.1 n, hω.2.1⟩ hω.2.2).1
  · have heq : {ω | ω ∈ Gn ∧ z ∈ H \ imgHull (W ω) (A ω) t} =
        Gn ∩ {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t} := by
      ext ω
      exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [heq]
    exact hS.inter (hM.measurableSet_mem_diff z)
  · have heq : ({ω | ω ∈ Gn ∧ z ∈ H \ imgHull (W ω) (A ω) t}.indicator fun ω =>
        ConformalImage.mapOut (imgHull (W ω) (A ω) t) z) =
        Gn.indicator ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t}.indicator
          fun ω => ConformalImage.mapOut (imgHull (W ω) (A ω) t) z) := by
      funext ω
      by_cases hω : ω ∈ Gn
      · by_cases hz : z ∈ H \ imgHull (W ω) (A ω) t
        · rw [indicator_of_mem (show ω ∈ {ω | ω ∈ Gn ∧ z ∈ H \ imgHull (W ω) (A ω) t} from ⟨hω, hz⟩),
            indicator_of_mem hω,
            indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) (A ω) t} from ⟨hω.1, hz⟩)]
        · rw [indicator_of_notMem (fun h => hz h.2), indicator_of_mem hω, indicator_of_notMem (fun h => hz h.2)]
      · rw [indicator_of_notMem (fun h => hω h.1), indicator_of_notMem hω]
    rw [heq]
    exact (hM.measurable_mapOut z).indicator hS
  · have heq : (Gn.indicator fun ω => fwdMap (W ω) t (q n ω) + (W ω t : ℂ)) = Gn.indicator fun ω =>
        {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (q n ω) t u}.indicator (fun ω => fwdMap (W ω) t (q n ω)) ω +
          (W ω t : ℂ) := by
      funext ω
      by_cases hω : ω ∈ Gn
      · simp only [indicator_of_mem hω, indicator_of_mem (hGnsub hω)]
      · simp only [indicator_of_notMem hω]
    rw [heq]
    exact ((hM.measurable_fwd_at (hq.meas n) fun ω hω => hq.memH ω hω n).add
      (Complex.measurable_ofReal.comp hM.drv)).indicator hS

/-- **The image chain at a random real mark is measurable**: `g̃_{a(t)}(ζ) + W'(a(t))`, on `G`, for a mark alive for
the image chain up to `a(T)`. -/
theorem measurable_imgC (hq : MarkSeq A φ G ζ q)
    (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ ω : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => fwdMap (W' ω) (a ω t) (ζ ω) + (W' ω (a ω t) : ℂ)) := by
  refine measurable_of_tendsto_metrizable (f := fun n =>
      (markEv W A G t (q n)).indicator fun ω =>
        ConformalImage.mapOut (imgHull (W ω) (A ω) t) (fwdMap (W ω) t (q n ω) + (W ω t : ℂ)))
    (fun n => hM.measurable_markVal hq n) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · obtain ⟨hev, hlim, -⟩ := hM.mark_facts hω (hv ω hω) (hq.memH ω hω) (hq.ev ω hω) (hq.lim ω hω)
    rw [indicator_of_mem hω]
    refine (hlim.add_const (W' ω (a ω t) : ℂ)).congr' ?_
    filter_upwards [hev] with n hn
    rw [indicator_of_mem (show ω ∈ markEv W A G t (q n) from ⟨hω, hn⟩),
      (hM.mark_eval hω ⟨hq.memH ω hω n, hn.1⟩ hn.2).2]
  · rw [indicator_of_notMem hω]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    beta_reduce
    rw [indicator_of_notMem (fun h : ω ∈ markEv W A G t (q n) => hω h.1)]

/-- **`frzImg` at a random mark is measurable** (`A_{2,0}`, `B_{m,0}`), on `G`. -/
theorem measurable_frzImg (hq : MarkSeq A φ G ζ q)
    (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ ω : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => frzImg (W' ω) (a ω) (ζ ω) t) := by
  have heq : (G.indicator fun ω => frzImg (W' ω) (a ω) (ζ ω) t) = fun ω =>
      (G.indicator (fun ω => fwdMap (W' ω) (a ω t) (ζ ω) + (W' ω (a ω t) : ℂ)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzImg, add_re, ofReal_re]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_imgC hq hv)

/-- The derivative of the image chain at a random real mark is measurable (on `G`): the limit of the difference
quotients along `φ(q n) → ζ`. -/
theorem measurable_derivImg (hq : MarkSeq A φ G ζ q)
    (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ ω : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => deriv (fwdMap (W' ω) (a ω t)) (ζ ω)) := by
  refine measurable_of_tendsto_metrizable (f := fun n => G.indicator fun ω =>
      (G.indicator (fun ω => φ ω (q n ω)) ω - G.indicator (fun ω => (ζ ω : ℂ)) ω)⁻¹ *
      ((markEv W A G t (q n)).indicator (fun ω =>
        ConformalImage.mapOut (imgHull (W ω) (A ω) t) (fwdMap (W ω) t (q n ω) + (W ω t : ℂ))) ω -
        G.indicator (fun ω => fwdMap (W' ω) (a ω t) (ζ ω) + (W' ω (a ω t) : ℂ)) ω))
    (fun n => ((((hq.img n).sub hq.measurable_mark).inv).mul ((hM.measurable_markVal hq n).sub
      (hM.measurable_imgC hq hv))).indicator hM.meas) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · obtain ⟨hev, -, hder⟩ := hM.mark_facts hω (hv ω hω) (hq.memH ω hω) (hq.ev ω hω) (hq.lim ω hω)
    have h := hM.own ω hω
    have hne : ∀ᶠ n in atTop, φ ω (q n ω) - (ζ ω : ℂ) ≠ 0 := by
      filter_upwards [hq.ev ω hω] with n hn hz
      have hyH : φ ω (q n ω) ∈ H := h.mapOut.1.2.mapsTo ⟨hq.memH ω hω n, hn⟩
      have h0 : (φ ω (q n ω) - (ζ ω : ℂ)).im = 0 := by rw [hz, zero_im]
      rw [sub_im, ofReal_im, sub_zero] at h0
      exact (ne_of_gt hyH) h0
    have hstep : Tendsto (fun n => φ ω (q n ω) - (ζ ω : ℂ)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, hne⟩
      have := (hq.lim ω hω).sub_const (ζ ω : ℂ)
      rwa [sub_self] at this
    simp only [indicator_of_mem hω]
    refine (hder.tendsto_slope_zero.comp hstep).congr' ?_
    filter_upwards [hev] with n hn
    rw [indicator_of_mem (show ω ∈ markEv W A G t (q n) from ⟨hω, hn⟩),
      (hM.mark_eval hω ⟨hq.memH ω hω n, hn.1⟩ hn.2).2, Function.comp_apply, smul_eq_mul, add_sub_cancel]
    ring
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- **`frzImgD` at a random mark is measurable** (`A_{2,1}`, `B_{m,1}/φ'(p_m)`), on `G`. -/
theorem measurable_frzImgD (hq : MarkSeq A φ G ζ q)
    (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ ω : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => frzImgD (W' ω) (a ω) (ζ ω) t) := by
  have heq : (G.indicator fun ω => frzImgD (W' ω) (a ω) (ζ ω) t) = fun ω =>
      (G.indicator (fun ω => deriv (fwdMap (W' ω) (a ω t)) (ζ ω)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzImgD]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_derivImg hq hv)

omit hM in
/-- **`frzRate` is measurable** (on `G`), random hull. -/
theorem measurable_frzRate (hM : FrzMeasR W W' a A φ T G t) :
    Measurable (G.indicator fun ω => frzRate (W ω) (W' ω) (a ω) (φ ω) t) := by
  have heq : (G.indicator fun ω => frzRate (W ω) (W' ω) (a ω) (φ ω) t) = fun ω =>
      1 / 4 * (G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) 2 t) ω /
        G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) 1 t) ω) ^ 2 -
      1 / 6 * (G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) 3 t) ω /
        G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) 1 t) ω) := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzRate]
    · simp only [indicator_of_notMem hω, div_zero]
      norm_num
  rw [heq]
  exact (measurable_const.mul (((hM.measurable_frzA 2).div (hM.measurable_frzA 1)).pow_const 2)).sub
    (measurable_const.mul ((hM.measurable_frzA 3).div (hM.measurable_frzA 1)))

end FrzMeasR

/-- **`log F = frzLogF … t` is measurable** (on `G`), random hull, given the measurability inputs at every time
`u ∈ [0, t]`. -/
theorem measurable_frzLogFR {W W' a : Ω → ℝ → ℝ} {A : Ω → Set ℂ} {φ : Ω → ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω}
    {t : ℝ} (ht : 0 ≤ t) (hM : ∀ u ∈ Icc (0 : ℝ) t, FrzMeasR W W' a A φ T G u) :
    Measurable (G.indicator fun ω => frzLogF (W ω) (W' ω) (a ω) (φ ω) t) := by
  have heq : (G.indicator fun ω => frzLogF (W ω) (W' ω) (a ω) (φ ω) t) = fun ω =>
      ∫ r in (0 : ℝ)..t, G.indicator (fun ω => frzRate (W ω) (W' ω) (a ω) (φ ω) r) ω := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzLogF]
    · simp only [indicator_of_notMem hω, intervalIntegral.integral_zero]
  rw [heq]
  refine Ito.measurable_intervalIntegral_of_continuousOn ht (fun r hr => (hM r hr).measurable_frzRate)
    fun ω => ?_
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
    have htT := (hM t ⟨ht, le_rfl⟩).mem ω hω
    exact ((hM t ⟨ht, le_rfl⟩).own ω hω).continuousOn_frzRate.mono (Icc_subset_Icc_right htT.2)
  · simp only [indicator_of_notMem hω]
    exact continuousOn_const

/-- The frozen data of `M̃` along `ω`, random hull: driver `W ω`, image data `W' ω`, `a ω`, chart `φ ω`, other source
`ζ₀ ω` and marks `ζ m ω` of the `φ`-chart. -/
def frzDataR {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (W W' a : Ω → ℝ → ℝ) (φ : Ω → ℂ → ℂ) (ζ₀ : Ω → ℝ)
    (ζ : Fin n → Ω → ℝ) (ω : Ω) : FrzData n :=
  ⟨W ω, W' ω, a ω, φ ω, κ, rr, ζ₀ ω, fun m => ζ m ω⟩

/-- **`log M̃(s)` is measurable** (on `G`), random hull: `ℓ(s, W_s)` of the frozen data, given the measurability
inputs at every time `u ∈ [0, s]` and mark sequences for the other source and the marks, alive for the image chain. -/
theorem measurable_ell_R {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) {W W' a : Ω → ℝ → ℝ} {A : Ω → Set ℂ}
    {φ : Ω → ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {s : ℝ} (hs : 0 ≤ s)
    (hM : ∀ u ∈ Icc (0 : ℝ) s, FrzMeasR W W' a A φ T G u) {ζ₀ : Ω → ℝ} {ζ : Fin n → Ω → ℝ}
    {q₀ : ℕ → Ω → ℂ} {q : Fin n → ℕ → Ω → ℂ} (hq₀ : MarkSeq A φ G ζ₀ q₀) (hq : ∀ m, MarkSeq A φ G (ζ m) (q m))
    (hv₀ : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ₀ ω : ℂ) (a ω (T ω)) v)
    (hv : ∀ m, ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ m ω : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => (frzDataR κ rr W W' a φ ζ₀ ζ ω).ell s (W ω s)) := by
  have hMs := hM s ⟨hs, le_rfl⟩
  have hG := hMs.meas
  set f0 := G.indicator fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) 0 s with hf0
  set f1 := G.indicator fun ω => frzA (W ω) (W' ω) (a ω) (φ ω) 1 s with hf1
  set i0 := G.indicator fun ω => frzImg (W' ω) (a ω) (ζ₀ ω) s with hi0
  set im := fun m => G.indicator fun ω => frzImg (W' ω) (a ω) (ζ m ω) s with him
  set d0 := G.indicator fun ω => frzImgD (W' ω) (a ω) (ζ₀ ω) s with hd0
  set dm := fun m => G.indicator fun ω => frzImgD (W' ω) (a ω) (ζ m ω) s with hdm
  set lf := G.indicator fun ω => frzLogF (W ω) (W' ω) (a ω) (φ ω) s with hlf
  have hA0 : Measurable f0 := hMs.measurable_frzA 0
  have hA1 : Measurable f1 := hMs.measurable_frzA 1
  have hI0 : Measurable i0 := hMs.measurable_frzImg hq₀ hv₀
  have hIm : ∀ m, Measurable (im m) := fun m => hMs.measurable_frzImg (hq m) (hv m)
  have hD0 : Measurable d0 := hMs.measurable_frzImgD hq₀ hv₀
  have hDm : ∀ m, Measurable (dm m) := fun m => hMs.measurable_frzImgD (hq m) (hv m)
  have hF : Measurable lf := measurable_frzLogFR hs hM
  have hmeas : Measurable fun ω => dualLogTime κ rr (d0 ω) (lf ω) (i0 ω) (fun m => im m ω)
      (fun m => dm m ω) + dualLogSpace κ rr (f0 ω) (f1 ω) (i0 ω) (fun m => im m ω) := by
    unfold dualLogTime dualLogSpace pairSum; fun_prop
  convert hmeas.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · rw [indicator_of_mem hω, indicator_of_mem hω]
    simp only [hf0, hf1, hi0, him, hd0, hdm, hlf, indicator_of_mem hω]
    rfl
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

end OwnR

end InteractingSLE.ZhanGT4
