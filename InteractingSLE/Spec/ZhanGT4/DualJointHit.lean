/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualJoint
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# Hits of Loewner hulls, and the dyadic hits of the image of one hull in the chart of another

Packet PROVE-ZHAN-GT4-A13. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L380,
R38): the density `M(s, t)` must be a measurable function of both curves. The one missing measurability input of
`FrzMeasR` (`DualJoint.lean`) is that the closure of the image `E = g^{(1)}_s(K₂)` of the hull of curve `2` under the
map of curve `1` is dyadic-hit measurable on a space carrying both curves. A deterministic hull has a fixed countable
dense subset (A8); a random Loewner hull need not have interior (a simple curve), so the dense-subset route fails.

Instead:

* **compact hits of a hull** (`hit_iff`, `measurableSet_hit`): a compact `L ⊆ ℍ` meets `K_t` iff for every `k` some
  point of a fixed dense sequence within `1/(k+1)` of `L` has its `1/(k+1)`-tamed flow below height `2/(k+1)` at a
  rational time `≤ t` (QuantumZipper's tamed description of the hull, `NonSwallow.mem_fwdHull_iff_tamed`, made uniform
  near a compact set of alive points by the monotone imaginary part of the flow);
* **dyadic hits of `closure (g(A))`** (`isDyadicHitMeasurable_closure_imgHull`): a dyadic square `Q` meets the closure of
  `g(A)` iff for every `j` some rational closed disc of `ℍ \ K` that meets `A` is mapped within `1/(j+2)` of `Q` — a
  countable condition in the compact hits of `K` and `A` and the values of `g` at points of the dense sequence.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull tamedZ)

/-! ### The tamed flow and the hull near a compact set of alive points -/

section Deterministic

variable {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
include hW

/-- The tamed flow at a fixed time is (Lipschitz) continuous in the starting point. -/
theorem continuous_tamedZ_point {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : 0 ≤ q) :
    Continuous fun a => tamedZ W c a q := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨Real.exp (4 * q / c ^ 2), (Real.exp_pos _).le⟩)
    fun a a' => ?_).continuous
  have h := QuantumZipper.dist_tamedZ_le hW hW hc hq a a' (ε := 0) (fun r _ => by simp) q ⟨hq, le_rfl⟩
  rw [add_zero, add_zero, mul_comm] at h
  exact h

include ht in
/-- **Near a compact set of alive points the flow stays uniformly high.** If the compact `L ⊆ ℍ` misses `K_t`, there
are `ρ, m > 0` such that every `a ∈ ℍ` within `ρ` of `L` has a forward solution on `[0, t]` with imaginary part `≥ m`. -/
theorem exists_im_flow_ge_of_disjoint {L : Set ℂ} (hL : IsCompact L) (hLne : L.Nonempty) (hLH : L ⊆ H)
    (hLK : ¬ (L ∩ fwdHull W t).Nonempty) :
    ∃ ρ > 0, ∃ m > 0, ∀ a ∈ H, infDist a L < ρ → ∃ v, IsForwardSol W a t v ∧ ∀ r ∈ Icc 0 t, m ≤ (v r).im := by
  have hD : IsOpen (H \ fwdHull W t) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hc : ContinuousOn (fun a => (fwdMap W t a).im) (H \ fwdHull W t) :=
    Complex.continuous_im.comp_continuousOn (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn
  have hLD : L ⊆ H \ fwdHull W t := fun l hl => ⟨hLH hl, fun hK => hLK ⟨l, hl, hK⟩⟩
  -- positivity of the height at alive points
  have hpos : ∀ a ∈ H \ fwdHull W t, 0 < (fwdMap W t a).im := fun a ha => by
    obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht ha.1 ha.2
    rw [QuantumZipper.fwdMap_eq hW ha.1 hu ⟨ht, le_rfl⟩]
    exact (QuantumZipper.im_isForwardSol_le hW ha.1 hu).2 t ⟨ht, le_rfl⟩
  obtain ⟨l₀, hl₀, hmin⟩ := hL.exists_isMinOn hLne (hc.mono hLD)
  set m₀ := (fwdMap W t l₀).im with hm₀
  have hm₀p : 0 < m₀ := hpos l₀ (hLD hl₀)
  set O := (H \ fwdHull W t) ∩ (fun a => (fwdMap W t a).im) ⁻¹' Ioi (m₀ / 2) with hO
  have hOo : IsOpen O := hc.isOpen_inter_preimage hD isOpen_Ioi
  have hLO : L ⊆ O := fun l hl => ⟨hLD hl, by
    show m₀ / 2 < (fwdMap W t l).im
    have : m₀ ≤ (fwdMap W t l).im := isMinOn_iff.1 hmin l hl
    linarith⟩
  obtain ⟨ρ, hρ, hth⟩ := hL.exists_thickening_subset_open hOo hLO
  refine ⟨ρ, hρ, m₀ / 2, half_pos hm₀p, fun a ha hda => ?_⟩
  have haO : a ∈ O := hth ((mem_thickening_iff_infDist_lt hLne).2 hda)
  obtain ⟨u, hu⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht ha haO.1.2
  obtain ⟨hanti, -⟩ := QuantumZipper.im_isForwardSol_le hW ha hu
  have hut : (u t).im = (fwdMap W t a).im := by rw [QuantumZipper.fwdMap_eq hW ha hu ⟨ht, le_rfl⟩]
  refine ⟨u, hu, fun r hr => ?_⟩
  have h1 : m₀ / 2 < (u t).im := by rw [hut]; exact haO.2
  have h2 : (u t).im ≤ (u r).im := hanti hr ⟨ht, le_rfl⟩ hr.2
  linarith

include ht in
/-- **Compact hits of a Loewner hull, countably.** For a nonempty compact `L ⊆ ℍ`: `L` meets `K_t` iff for every `k`
some point `e j` of the dense sequence of `ℂ` in `ℍ`, within `1/(k+1)` of `L`, has its `1/(k+1)`-tamed flow below
height `2/(k+1)` at some rational time in `[0, t]`. -/
theorem hit_iff {L : Set ℂ} (hL : IsCompact L) (hLne : L.Nonempty) (hLH : L ⊆ H) :
    (L ∩ fwdHull W t).Nonempty ↔ ∀ k : ℕ, ∃ j : ℕ, ∃ q : ℚ, (0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t) ∧
      0 < (TopologicalSpace.denseSeq ℂ j).im ∧ infDist (TopologicalSpace.denseSeq ℂ j) L < 1 / ((k : ℝ) + 1) ∧
      (tamedZ W (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ j) q).im < 2 * (1 / ((k : ℝ) + 1)) := by
  constructor
  · rintro ⟨z, hzL, hzK⟩ k
    obtain ⟨-, hk⟩ := (QuantumZipper.NonSwallow.mem_fwdHull_iff_tamed hW ht).1 hzK
    obtain ⟨q, hq0, hqt, hqz⟩ := hk k
    have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    set U := {a : ℂ | 0 < a.im} ∩ {a | infDist a L < 1 / ((k : ℝ) + 1)} ∩
      {a | (tamedZ W (1 / ((k : ℝ) + 1)) a q).im < 2 * (1 / ((k : ℝ) + 1))} with hU
    have hUo : IsOpen U :=
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt (continuous_infDist_pt L) continuous_const)).inter
        (isOpen_lt (Complex.continuous_im.comp (continuous_tamedZ_point hW hc hq0)) continuous_const)
    have hzU : z ∈ U := ⟨⟨hzK.1, by rw [mem_ofPred_eq, infDist_zero_of_mem hzL]; exact hc⟩, hqz⟩
    obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open hUo ⟨z, hzU⟩
    exact ⟨j, q, ⟨hq0, hqt⟩, hj.1.1, hj.1.2, hj.2⟩
  · intro h
    by_contra hLK
    obtain ⟨ρ, hρ, m, hm, hflow⟩ := exists_im_flow_ge_of_disjoint hW ht hL hLne hLH hLK
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (lt_min hρ (show 0 < m / 4 by positivity))
    obtain ⟨j, q, hq, hjH, hjL, hjq⟩ := h k
    have hc : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hk1 : 1 / ((k : ℝ) + 1) < ρ := hk.trans_le (min_le_left _ _)
    have hk2 : 1 / ((k : ℝ) + 1) < m / 4 := hk.trans_le (min_le_right _ _)
    obtain ⟨v, hv, hvm⟩ := hflow _ hjH (hjL.trans hk1)
    have hteq := QuantumZipper.tamedZ_eq_of_isForwardSol hW hc ht hv
      (fun r hr => by have := hvm r hr; linarith) q hq
    rw [hteq] at hjq
    have := hvm q hq
    linarith

end Deterministic

/-! ### Measurability of compact hits -/

section Hit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The event that a Loewner hull meets a compact subset of `ℍ` is measurable**, for continuous drivers whose tamed
flows at rational times are measurable at fixed points. -/
theorem measurableSet_hit {W : Ω → ℝ → ℝ} (hWc : ∀ ω, Continuous (W ω)) {t : ℝ} (ht : 0 ≤ t)
    (hWm : ∀ (k : ℕ) (q : ℚ), 0 ≤ (q : ℝ) → (q : ℝ) ≤ t → ∀ a : ℂ,
      Measurable fun ω => tamedZ (W ω) (1 / ((k : ℝ) + 1)) a q)
    {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) : MeasurableSet {ω | (L ∩ fwdHull (W ω) t).Nonempty} := by
  rcases L.eq_empty_or_nonempty with hL0 | hLne
  · simp [hL0]
  have heq : {ω | (L ∩ fwdHull (W ω) t).Nonempty} = ⋂ k : ℕ, ⋃ j : ℕ, ⋃ q : ℚ,
      {ω : Ω | (0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t) ∧ 0 < (TopologicalSpace.denseSeq ℂ j).im ∧
        infDist (TopologicalSpace.denseSeq ℂ j) L < 1 / ((k : ℝ) + 1)} ∩
      {ω | (tamedZ (W ω) (1 / ((k : ℝ) + 1)) (TopologicalSpace.denseSeq ℂ j) q).im < 2 * (1 / ((k : ℝ) + 1))} := by
    ext ω
    simp only [mem_ofPred_eq, hit_iff (hWc ω) ht hL hLne hLH, mem_iInter, mem_iUnion, mem_inter_iff, and_assoc]
  rw [heq]
  refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun q => ?_
  by_cases hq : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t
  · exact (MeasurableSet.const _).inter (measurableSet_lt (Complex.measurable_im.comp
      (hWm k q hq.1 hq.2 _)) measurable_const)
  · have : {ω : Ω | (0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t) ∧ 0 < (TopologicalSpace.denseSeq ℂ j).im ∧
        infDist (TopologicalSpace.denseSeq ℂ j) L < 1 / ((k : ℝ) + 1)} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]; exact fun h => absurd h hq
    rw [this, empty_inter]
    exact MeasurableSet.empty

end Hit

/-! ### Dyadic hits of the closure of `g(A)` -/

section Image

/-- **A compact set meets the closure of `g_s(A)`, countably.** For a hull-free set `A ⊆ ℍ \ K_s` and a nonempty
compact `Q`: `Q` meets `closure (g_s(A) + W_s)` iff for every `j` some closed disc `B̄(e i', 1/(i+1))` of `ℍ \ K_s`
centred at a point of the dense sequence meets `A`, and the dense points of its interior are mapped within `1/(j+2)`
of `Q`. -/
theorem closure_imgHull_hit_iff {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {A : Set ℂ} (hAH : A ⊆ H)
    (hAK : Disjoint A (fwdHull W s)) {Q : Set ℂ} (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    (Q ∩ closure (imgHull W A s)).Nonempty ↔ ∀ j : ℕ, ∃ i i' : ℕ,
      closedBall (TopologicalSpace.denseSeq ℂ i') (1 / ((i : ℝ) + 1)) ⊆ H ∧
      ¬ (closedBall (TopologicalSpace.denseSeq ℂ i') (1 / ((i : ℝ) + 1)) ∩ fwdHull W s).Nonempty ∧
      (closedBall (TopologicalSpace.denseSeq ℂ i') (1 / ((i : ℝ) + 1)) ∩ A).Nonempty ∧
      ∀ l : ℕ, TopologicalSpace.denseSeq ℂ l ∈ ball (TopologicalSpace.denseSeq ℂ i') (1 / ((i : ℝ) + 1)) →
        infDist (fwdMap W s (TopologicalSpace.denseSeq ℂ l) + (W s : ℂ)) Q ≤ 1 / ((j : ℝ) + 2) := by
  set e := TopologicalSpace.denseSeq ℂ with he
  have hden : Dense (range e) := TopologicalSpace.denseRange_denseSeq ℂ
  set D := H \ fwdHull W s with hD
  have hDo : IsOpen D := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs
  set ψ : ℂ → ℂ := fun z => fwdMap W s z + (W s : ℂ) with hψ
  have hψc : ContinuousOn ψ D :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn.add continuousOn_const
  set f : ℂ → ℝ := fun z => infDist (ψ z) Q with hf
  have hfc : ContinuousOn f D := (continuous_infDist_pt Q).comp_continuousOn hψc
  have himg : imgHull W A s = ψ '' A := rfl
  rw [himg]
  constructor
  · intro hne j
    obtain ⟨y, ⟨z, hzA, rfl⟩, hy⟩ := (inter_closure_nonempty_iff hQ hQne).1 hne (j + 2)
    have hzD : z ∈ D := ⟨hAH hzA, Set.disjoint_left.1 hAK hzA⟩
    have hj : 1 / (((j + 2 : ℕ) : ℝ) + 1) < 1 / ((j : ℝ) + 2) := by
      rw [one_div_lt_one_div (by positivity) (by positivity)]; push_cast; linarith
    set O := D ∩ f ⁻¹' Iio (1 / ((j : ℝ) + 2)) with hO
    have hOo : IsOpen O := hfc.isOpen_inter_preimage hDo isOpen_Iio
    have hzO : z ∈ O := ⟨hzD, show f z < _ from hy.trans hj⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOo z hzO
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt (half_pos hε)
    set r := 1 / ((i : ℝ) + 1) with hr
    have hr0 : 0 < r := by positivity
    obtain ⟨_, ⟨i', rfl⟩, hi'z⟩ := hden.exists_mem_open isOpen_ball ⟨z, mem_ball_self hr0⟩
    have hsub : closedBall (e i') r ⊆ O := fun w hw => hball (by
      rw [mem_ball] at hi'z ⊢
      rw [mem_closedBall] at hw
      calc dist w z ≤ dist w (e i') + dist (e i') z := dist_triangle _ _ _
        _ < r + r := by linarith
        _ < ε := by linarith)
    refine ⟨i, i', fun w hw => (hsub hw).1.1, fun ⟨w, hw, hwK⟩ => (hsub hw).1.2 hwK,
      ⟨z, ?_, hzA⟩, fun l hl => (hsub (ball_subset_closedBall hl)).2.le⟩
    rw [mem_closedBall, dist_comm]
    exact (mem_ball.1 hi'z).le
  · intro h
    refine (inter_closure_nonempty_iff hQ hQne).2 fun j => ?_
    obtain ⟨i, i', c1, c2, ⟨z, hzB, hzA⟩, c4⟩ := h j
    refine ⟨ψ z, ⟨z, hzA, rfl⟩, ?_⟩
    set r := 1 / ((i : ℝ) + 1) with hr
    have hr0 : 0 < r := by positivity
    have hBD : closedBall (e i') r ⊆ D := fun w hw => ⟨c1 hw, fun hK => c2 ⟨w, hw, hK⟩⟩
    set S := ball (e i') r ∩ range e with hS
    have hzS : z ∈ closure S := by
      have h1 : ball (e i') r ⊆ closure S := hden.open_subset_closure_inter isOpen_ball
      have h2 : closure (ball (e i') r) ⊆ closure S := closure_minimal h1 isClosed_closure
      rw [closure_ball _ hr0.ne'] at h2
      exact h2 hzB
    have hSD : closure S ⊆ D :=
      (closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall).trans hBD
    have hle : f z ≤ 1 / ((j : ℝ) + 2) := le_on_closure (f := f) (g := fun _ => 1 / ((j : ℝ) + 2))
      (fun x hx => by obtain ⟨hxb, l, rfl⟩ := hx; exact c4 l hxb) (hfc.mono hSD) continuousOn_const hzS
    have hj : 1 / ((j : ℝ) + 2) < 1 / ((j : ℝ) + 1) := by
      rw [one_div_lt_one_div (by positivity) (by positivity)]; linarith
    exact hle.trans_lt hj

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped Classical in
/-- **The closure of `g_s(A)` is dyadic-hit measurable** (`∅` off the measurable event `G`), for a random set `A ω`
with measurable compact hits, lying in `ℍ \ K_s` on `G`, and a driver with measurable compact hits of its hull and
forward map at fixed points (on the alive events). -/
theorem isDyadicHitMeasurable_closure_imgHull {W : Ω → ℝ → ℝ} (hWc : ∀ ω, Continuous (W ω)) {s : ℝ} (hs : 0 ≤ s)
    (hK : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ fwdHull (W ω) s).Nonempty})
    (hfwd : ∀ z ∈ H, Measurable ({ω | ∃ u, IsForwardSol (W ω) z s u}.indicator fun ω => fwdMap (W ω) s z))
    (hdrv : Measurable fun ω => W ω s) {A : Ω → Set ℂ}
    (hA : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ A ω).Nonempty}) {G : Set Ω}
    (hG : MeasurableSet G) (hAH : ∀ ω ∈ G, A ω ⊆ H) (hAK : ∀ ω ∈ G, Disjoint (A ω) (fwdHull (W ω) s)) :
    Restart.IsDyadicHitMeasurable fun ω => if ω ∈ G then closure (imgHull (W ω) (A ω) s) else ∅ := by
  intro n k
  set e := TopologicalSpace.denseSeq ℂ with he
  set Q := Restart.dyadicSquare n k with hQdef
  have hQ : IsCompact Q := Restart.isCompact_dyadicSquare n k
  have hQne : Q.Nonempty := Restart.PairData.dyadicSquare_nonempty n k
  -- the per-disc events
  set B : ℕ → ℕ → Set ℂ := fun i i' => closedBall (e i') (1 / ((i : ℝ) + 1)) with hB
  set Ev : ℕ → ℕ → ℕ → Set Ω := fun j i i' =>
    {ω | B i i' ⊆ H ∧ ¬ (B i i' ∩ fwdHull (W ω) s).Nonempty ∧ (B i i' ∩ A ω).Nonempty ∧
      ∀ l : ℕ, e l ∈ ball (e i') (1 / ((i : ℝ) + 1)) →
        infDist ({ω | ∃ u, IsForwardSol (W ω) (e l) s u}.indicator (fun ω => fwdMap (W ω) s (e l)) ω +
          (W ω s : ℂ)) Q ≤ 1 / ((j : ℝ) + 2)} with hEv
  have hEvm : ∀ j i i', MeasurableSet (Ev j i i') := by
    intro j i i'
    by_cases hBH : B i i' ⊆ H
    · have hBc : IsCompact (B i i') := isCompact_closedBall _ _
      have hEq : Ev j i i' = {ω | (B i i' ∩ fwdHull (W ω) s).Nonempty}ᶜ ∩ {ω | (B i i' ∩ A ω).Nonempty} ∩
          ⋂ l : ℕ, {ω | e l ∈ ball (e i') (1 / ((i : ℝ) + 1)) →
            infDist ({ω | ∃ u, IsForwardSol (W ω) (e l) s u}.indicator (fun ω => fwdMap (W ω) s (e l)) ω +
              (W ω s : ℂ)) Q ≤ 1 / ((j : ℝ) + 2)} := by
        ext ω
        simp only [hEv, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_iInter, hBH, true_and, and_assoc]
      rw [hEq]
      refine ((hK _ hBc hBH).compl.inter (hA _ hBc hBH)).inter (MeasurableSet.iInter fun l => ?_)
      by_cases hl : e l ∈ ball (e i') (1 / ((i : ℝ) + 1))
      · have hlH : e l ∈ H := hBH (ball_subset_closedBall hl)
        simp only [hl, true_implies]
        exact measurableSet_le ((continuous_infDist_pt Q).measurable.comp ((hfwd _ hlH).add
          (Complex.measurable_ofReal.comp hdrv))) measurable_const
      · simp only [hl, false_implies, ofPred_true, MeasurableSet.univ]
    · have : Ev j i i' = ∅ := by
        ext ω; simp only [hEv, mem_ofPred_eq, hBH, false_and, mem_empty_iff_false]
      rw [this]
      exact MeasurableSet.empty
  have heq : {ω | (Q ∩ (if ω ∈ G then closure (imgHull (W ω) (A ω) s) else ∅)).Nonempty} =
      G ∩ ⋂ j : ℕ, ⋃ i : ℕ, ⋃ i' : ℕ, Ev j i i' := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, hω, ↓reduceIte, mem_inter_iff, true_and, mem_iInter, mem_iUnion]
      rw [closure_imgHull_hit_iff (hWc ω) hs (hAH ω hω) (hAK ω hω) hQ hQne]
      refine forall_congr' fun j => exists_congr fun i => exists_congr fun i' => ?_
      simp only [hEv, mem_ofPred_eq]
      refine and_congr_right fun hBH => and_congr_right fun hBK => and_congr_right fun _ =>
        forall_congr' fun l => imp_congr_right fun hl => ?_
      have hal : ω ∈ {ω | ∃ u, IsForwardSol (W ω) (e l) s u} :=
        QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hs (hBH (ball_subset_closedBall hl))
          fun hK' => hBK ⟨e l, ball_subset_closedBall hl, hK'⟩
      rw [indicator_of_mem hal]
    · simp [hω]
  rw [heq]
  exact hG.inter (MeasurableSet.iInter fun j => MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun i' =>
    hEvm j i i')

end Image

end InteractingSLE.ZhanGT4
