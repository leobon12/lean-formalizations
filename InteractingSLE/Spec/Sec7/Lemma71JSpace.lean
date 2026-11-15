/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71JPocket
import InteractingSLE.Spec.Sec7.Lemma72BMain

/-!
# Lemma 7.1's pocket on a given three-curve space: the domain, measurable for the outer curves

Packet PROVE-LEMMA71J; interface of `planning/handoffs/PROVE-LEMMA72B.md` ("expose the pocket construction as a theorem
on a given three-curve space … with conclusion `IsPocketChartData`, including (S1)–(S3)"). This file gives the **domain
part** of that construction on every space satisfying `Lemma72B.IsThreeCurveSpace`, for exactly the σ-algebra
`σ(β, α) = comap (β, α)` of `Lemma72B.IsPocketChartData`'s clause (S1), and the clause (S2):

* `measurableSet_disjoint_closure_range`: `{ω | closedBall c r ∩ closure (range (R ω)) = ∅}` is measurable for any
  σ-algebra making the coordinates of a continuous random path measurable;
* `isSimplyConnected_connectedComponentIn_closure`: every component of `ℍ ∖ cl(R ∪ L)` is simply connected when `R`,
  `L` are continuous curves from `0` (for **every** `ω`, no simplicity needed);
* `frontier_connectedComponentIn_inter_H_subset`: the frontier in `ℍ` of a component of `ℍ ∖ S` (`S` closed) lies in
  `S`;
* `exists_measurable_pocketDomain`: the pocket through the first rational between-point, defined for every `ω`;
* **`exists_pocketDomain_of_isThreeCurveSpace`**: on a three-curve space there are a dense sequence `e`, a
  `σ(β, α)`-measurable index `Np` and a random domain `C` (open, connected, simply connected, in `ℍ`, for every `ω`)
  with `σ(β, α)`-measurable closed-ball events (S1, domain part) and `e (Np ω) ∈ C ω`, which is almost surely a
  component between the outer curves with `frontier C ∩ ℍ ⊆ β ∪ α` (S2).

The remaining clauses of `IsPocketChartData` (the chart on `C`, the mapped segment, the pocket filtration (S3) and the
chart coupling clause) are not produced here; see the handoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71Pin

open QuantumZipper (H)
open LocalSets Lemma71I

/-! ### Closures of random ranges -/

section Closure

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- **A compact set misses the closure of the range of a random continuous path: a measurable event.** -/
theorem measurableSet_disjoint_closure_range {R : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (R ω))
    (hm : ∀ t, Measurable[m] fun ω => R ω t) (c : ℂ) (r : ℝ) :
    MeasurableSet[m] {ω | Disjoint (closedBall c r) (closure (range (R ω)))} := by
  rcases lt_or_ge r 0 with hr | hr
  · have e : {ω | Disjoint (closedBall c r) (closure (range (R ω)))} = univ := by
      ext ω
      simp [closedBall_eq_empty.2 hr]
    rw [e]
    exact @MeasurableSet.univ _ m
  have hKne : (closedBall c r).Nonempty := nonempty_closedBall.2 hr
  have hKc : IsCompact (closedBall c r) := isCompact_closedBall c r
  have e : {ω | Disjoint (closedBall c r) (closure (range (R ω)))} =
      ⋃ n : ℕ, ⋂ q : ℚ≥0, {ω | 1 / ((n : ℝ) + 1) ≤ infDist (R ω q) (closedBall c r)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro hd
      -- the distance from the ball to the closed set `cl(range R)` is positive
      have hpos : ∀ x ∈ closedBall c r, 0 < infDist x (closure (range (R ω))) := fun x hx =>
        (isClosed_closure.notMem_iff_infDist_pos (⟨R ω 0, subset_closure ⟨0, rfl⟩⟩ :
          (closure (range (R ω))).Nonempty)).1
          (Set.disjoint_left.1 hd hx)
      obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hKne (continuous_infDist_pt _).continuousOn
      have hδ := hpos x₀ hx₀
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      refine ⟨n, fun q => ?_⟩
      refine (le_infDist hKne).2 fun x hx => ?_
      have h1 : infDist x₀ (closure (range (R ω))) ≤ infDist x (closure (range (R ω))) := hmin hx
      have h2 : infDist x (closure (range (R ω))) ≤ dist x (R ω q) :=
        infDist_le_dist_of_mem (subset_closure ⟨q, rfl⟩)
      rw [dist_comm] at h2
      linarith
    · rintro ⟨n, hn⟩
      have hclosed : IsClosed {y : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist y (closedBall c r)} :=
        isClosed_le continuous_const (continuous_infDist_pt _)
      have hall : ∀ t : ℝ≥0, 1 / ((n : ℝ) + 1) ≤ infDist (R ω t) (closedBall c r) := by
        intro t
        have hT : IsClosed {t : ℝ≥0 | 1 / ((n : ℝ) + 1) ≤ infDist (R ω t) (closedBall c r)} :=
          hclosed.preimage (hc ω)
        have hdense : Dense (range ((↑) : ℚ≥0 → ℝ≥0)) := by
          refine Metric.dense_iff.2 fun u δ hδ => ?_
          obtain ⟨q, -, hq⟩ := exists_nnrat_le_dist_lt u hδ
          exact ⟨q, mem_ball.2 hq, q, rfl⟩
        have hsub : range ((↑) : ℚ≥0 → ℝ≥0) ⊆ {t | 1 / ((n : ℝ) + 1) ≤ infDist (R ω t) (closedBall c r)} := by
          rintro _ ⟨q, rfl⟩
          exact hn q
        exact hT.closure_subset_iff.2 hsub (hdense.closure_eq ▸ mem_univ t)
      have hcl : closure (range (R ω)) ⊆ {y : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist y (closedBall c r)} :=
        hclosed.closure_subset_iff.2 (by rintro _ ⟨t, rfl⟩; exact hall t)
      refine Set.disjoint_left.2 fun x hx hxcl => ?_
      have h1 := hcl hxcl
      rw [mem_ofPred_eq, infDist_zero_of_mem hx] at h1
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  rw [e]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q =>
    measurableSet_le measurable_const ((continuous_infDist_pt _).measurable.comp (hm q))

/-- The closed balls inside `ℍ ∖ cl(R ∪ L)` for two random continuous paths: measurable events. -/
theorem measurableSet_closedBall_subset_H_diff_closure {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hRm : ∀ t, Measurable[m] fun ω => R ω t)
    (hLm : ∀ t, Measurable[m] fun ω => L ω t) (c : ℂ) (r : ℝ) :
    MeasurableSet[m] {ω | closedBall c r ⊆ H \ closure (range (R ω) ∪ range (L ω))} := by
  have e : {ω | closedBall c r ⊆ H \ closure (range (R ω) ∪ range (L ω))} =
      {_ω | closedBall c r ⊆ H} ∩ ({ω | Disjoint (closedBall c r) (closure (range (R ω)))} ∩
        {ω | Disjoint (closedBall c r) (closure (range (L ω)))}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, subset_sdiff, closure_union, disjoint_union_right]
  rw [e]
  exact (MeasurableSet.const _).inter ((measurableSet_disjoint_closure_range hRc hRm c r).inter
    (measurableSet_disjoint_closure_range hLc hLm c r))

/-- **Every component of `ℍ ∖ cl(R ∪ L)` is simply connected** for continuous curves `R`, `L` from `0`. -/
theorem isSimplyConnected_connectedComponentIn_closure {R L : ℝ≥0 → ℂ} (hRc : Continuous R) (hLc : Continuous L)
    (hR0 : R 0 = 0) (hL0 : L 0 = 0) {y : ℂ} (hy : y ∈ H \ closure (range R ∪ range L)) :
    IsSimplyConnected (connectedComponentIn (H \ closure (range R ∪ range L)) y) := by
  have hS : IsOpen (H \ closure (range R ∪ range L)) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  refine isSimplyConnected_connectedComponentIn_compl hS (fun z hz => ?_) hy
  have hlow : IsPreconnected {w : ℂ | w.im ≤ 0} := isPreconnected_lowerHalf
  have h0R : (0 : ℂ) ∈ range R := ⟨0, hR0⟩
  have h0L : (0 : ℂ) ∈ range L := ⟨0, hL0⟩
  have h0l : (0 : ℂ) ∈ {w : ℂ | w.im ≤ 0} := by simp
  have hRLpc : IsPreconnected (range R ∪ range L) :=
    (isPreconnected_range hRc).union (0 : ℂ) h0R h0L (isPreconnected_range hLc)
  have hpc : IsPreconnected (lowerUnion (closure (range R ∪ range L))) :=
    hRLpc.closure.union (0 : ℂ) (subset_closure (Or.inl h0R)) h0l hlow
  rw [hpc.connectedComponentIn hz]
  intro hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hm : ((-(|M| + 1) : ℝ) : ℂ) * I ∈ lowerUnion (closure (range R ∪ range L)) := Or.inr (by
    show ((((-(|M| + 1) : ℝ)) : ℂ) * I).im ≤ 0
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    linarith [abs_nonneg M])
  have := hM _ hm
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (by linarith [abs_nonneg M])] at this
  linarith [le_abs_self M]

/-- **The frontier in `ℍ` of a component of `ℍ ∖ S` lies in `S`** (`S` closed): a point of `ℍ ∖ S` adherent to the
component has a ball in `ℍ ∖ S` meeting it, hence inside it. -/
theorem frontier_connectedComponentIn_inter_H_subset {S : Set ℂ} (hS : IsClosed S) (z₀ : ℂ) :
    frontier (connectedComponentIn (H \ S) z₀) ∩ H ⊆ S := by
  rintro z ⟨hzf, hzH⟩
  by_contra hzS
  have hU : IsOpen (H \ S) := QuantumZipper.isOpen_H.sdiff hS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z ⟨hzH, hzS⟩
  obtain ⟨w, hwC, hwb⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hzf) ε hε
  have hbC : ball z ε ⊆ connectedComponentIn (H \ S) z₀ := by
    rw [connectedComponentIn_eq hwC]
    exact (isPreconnected_ball).subset_connectedComponentIn (mem_ball.2 (by rwa [dist_comm])) hball
  have hint : z ∈ interior (connectedComponentIn (H \ S) z₀) :=
    mem_interior.2 ⟨ball z ε, hbC, isOpen_ball, mem_ball_self hε⟩
  exact hzf.2 hint

end Closure

/-! ### The pocket domain for every `ω` -/

section Domain

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A between-point is off the closure of the walls. -/
theorem mem_H_diff_closure_of_isBetweenPt {A B : Set ℂ} {z : ℂ} (hz : IsBetweenPt A B z) :
    z ∈ H \ closure (A ∪ B) := by
  obtain ⟨hzH, hzA, -, -⟩ := hz
  refine ⟨hzH, fun hcl => hzA ⟨hzH, ?_⟩⟩
  have hsplit : closure (A ∪ B) ⊆ closure ((A ∪ B) ∩ H) ∪ closure ((A ∪ B) \ H) := by
    rw [← closure_union, inter_union_sdiff]
  rcases hsplit hcl with h | h
  · exact h
  · have hlow : closure ((A ∪ B) \ H) ⊆ {w : ℂ | w.im ≤ 0} :=
      closure_minimal (fun w hw => show w.im ≤ 0 from not_lt.1 hw.2) (isClosed_le continuous_im continuous_const)
    have h1 : z.im ≤ 0 := hlow h
    have h2 : 0 < z.im := hzH
    linarith

/-- **The pocket domain through the first rational between-point, for every `ω`.** For random continuous curves
`R ω`, `L ω` from `0` with `m`-measurable coordinates and a dense sequence `e`: an `m`-measurable index `Np` and a
random domain `C` (open, connected, simply connected, in `ℍ`, containing `e (Np ω)`, with `m`-measurable closed-ball
events) which, whenever some `e k` is between the walls, is the component of `ℍ ∖ cl(R ∪ L)` through the first such
point. -/
theorem exists_measurable_pocketDomain {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω))
    (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0) (hL0 : ∀ ω, L ω 0 = 0)
    (hRm : ∀ t, Measurable[m] fun ω => R ω t) (hLm : ∀ t, Measurable[m] fun ω => L ω t)
    {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ (C : Ω → Set ℂ) (Np : Ω → ℕ), Measurable[m] Np ∧
      (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
      (∀ (c : ℂ) (r : ℝ), MeasurableSet[m] {ω | closedBall c r ⊆ C ω}) ∧ (∀ ω, e (Np ω) ∈ C ω) ∧
      ∀ ω, (∃ k, IsBetweenPt (range (R ω)) (range (L ω)) (e k)) →
        IsBetweenPt (range (R ω)) (range (L ω)) (e (Np ω)) ∧
          C ω = connectedComponentIn (H \ closure (range (R ω) ∪ range (L ω))) (e (Np ω)) := by
  classical
  let _ : MeasurableSpace Ω := m
  set B : ℕ → Set Ω := fun k => {ω | IsBetweenPt (range (R ω)) (range (L ω)) (e k)} with hBdef
  have hBm : ∀ k, MeasurableSet (B k) := fun k => measurableSet_isBetweenPt hRc hLc hRm hLm (e k)
  set G : Set Ω := ⋃ k, B k with hGdef
  have hGm : MeasurableSet G := MeasurableSet.iUnion hBm
  set p : Ω → ℕ → Prop := fun ω k => ω ∈ B k ∨ ∀ j, ω ∉ B j with hpdef
  have hp : ∀ ω, ∃ k, p ω k := fun ω => by
    by_cases h : ∃ j, ω ∈ B j
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, Or.inl hj⟩
    · push Not at h
      exact ⟨0, Or.inr h⟩
  have hpm : ∀ k, MeasurableSet {ω | p ω k} := fun k => by
    have e' : {ω | p ω k} = B k ∪ ⋂ j, (B j)ᶜ := by
      ext ω
      simp only [hpdef, mem_ofPred_eq, mem_union, mem_iInter, mem_compl_iff]
    rw [e']
    exact (hBm k).union (MeasurableSet.iInter fun j => (hBm j).compl)
  have hNf : Measurable fun ω => Nat.find (hp ω) := measurable_find hp hpm
  obtain ⟨k₀, hk₀⟩ := he.exists_mem_open isOpen_ball ⟨2 * I, mem_ball_self one_pos⟩
  set Np : Ω → ℕ := fun ω => if ω ∈ G then Nat.find (hp ω) else k₀ with hNpdef
  have hNp : Measurable Np := Measurable.ite hGm hNf measurable_const
  have hGB : ∀ ω ∈ G, IsBetweenPt (range (R ω)) (range (L ω)) (e (Np ω)) := by
    intro ω hω
    simp only [hNpdef, hω, ↓reduceIte]
    obtain ⟨j, hj⟩ := mem_iUnion.1 hω
    rcases Nat.find_spec (hp ω) with h | h
    · exact h
    · exact absurd hj (h j)
  set S : Ω → Set ℂ := fun ω => closure (range (R ω) ∪ range (L ω)) with hSdef
  set U : Ω → Set ℂ := fun ω => if ω ∈ G then H \ S ω else univ with hUdef
  have hUo : ∀ ω, IsOpen (U ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hUdef, hω, ↓reduceIte]
      exact QuantumZipper.isOpen_H.sdiff isClosed_closure
    · simp only [hUdef, hω, ↓reduceIte]
      exact isOpen_univ
  have hUm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω} := by
    intro c r
    have e' : {ω | closedBall c r ⊆ U ω} =
        (G ∩ {ω | closedBall c r ⊆ H \ closure (range (R ω) ∪ range (L ω))}) ∪ Gᶜ := by
      ext ω
      by_cases hω : ω ∈ G <;> simp [hUdef, hSdef, hω]
    rw [e']
    exact (hGm.inter (measurableSet_closedBall_subset_H_diff_closure hRc hLc hRm hLm c r)).union hGm.compl
  have hpU : ∀ ω, e (Np ω) ∈ U ω := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hUdef, hω, ↓reduceIte]
      exact mem_H_diff_closure_of_isBetweenPt (hGB ω hω)
    · simp only [hUdef, hω, ↓reduceIte, mem_univ]
  set C : Ω → Set ℂ := fun ω => if ω ∈ G then connectedComponentIn (U ω) (e (Np ω)) else defaultPocket
    with hCdef
  refine ⟨C, Np, hNp, fun ω => ?_, fun c r => ?_, fun ω => ?_, fun ω hex => ?_⟩
  · by_cases hω : ω ∈ G
    · have hpU' := hpU ω
      simp only [hUdef, hω, ↓reduceIte] at hpU'
      simp only [hCdef, hUdef, hω, ↓reduceIte]
      refine ⟨(QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn,
        isConnected_connectedComponentIn_iff.2 hpU',
        isSimplyConnected_connectedComponentIn_closure (hRc ω) (hLc ω) (hR0 ω) (hL0 ω) hpU',
        (connectedComponentIn_subset _ _).trans sdiff_subset⟩
    · simp only [hCdef, hω, ↓reduceIte]
      exact ⟨isOpen_ball, isConnected_defaultPocket, isSimplyConnected_ball _ one_pos, defaultPocket_subset_H⟩
  · have hc := Lemma71E.measurableSet_closedBall_subset_component hUo hUm hNp hpU c r
    have e' : {ω | closedBall c r ⊆ C ω} =
        (G ∩ {ω | closedBall c r ⊆ connectedComponentIn (U ω) (e (Np ω))}) ∪
          (Gᶜ ∩ {_ω | closedBall c r ⊆ defaultPocket}) := by
      ext ω
      by_cases hω : ω ∈ G <;> simp [hCdef, hω]
    rw [e']
    exact (hGm.inter hc).union (hGm.compl.inter (MeasurableSet.const _))
  · by_cases hω : ω ∈ G
    · simp only [hCdef, hω, ↓reduceIte]
      exact mem_connectedComponentIn (hpU ω)
    · simp only [hCdef, hNpdef, hω, ↓reduceIte]
      exact hk₀
  · have hω : ω ∈ G := mem_iUnion.2 hex
    refine ⟨hGB ω hω, ?_⟩
    simp only [hCdef, hUdef, hSdef, hω, ↓reduceIte]

end Domain

/-! ### The pocket domain on the three-curve space -/

section Space

/-- A point of the middle curve off both walls is between them (for ordered simple proper arcs). -/
theorem isBetweenPt_of_middle {β α γ : ℝ≥0 → ℂ} (hβ : IsSimpleProper β) (hα : IsSimpleProper α)
    (hγ : IsSimpleProper γ) (hord : WangWu.IsOrderedArcs (realPath α) (realPath γ) (realPath β)) {t : ℝ≥0}
    (ht : 0 < t) (htw : γ t ∉ range α ∪ range β) : IsBetweenPt (range α) (range β) (γ t) := by
  have hzH : γ t ∈ H := hγ.2.2.2.1 t ht
  have hzHbar : γ t ∈ QuantumZipper.Hbar := le_of_lt (show (0 : ℝ) < (γ t).im from hzH)
  have hzM : γ t ∈ WangWu.arcRange (realPath γ) := by rw [arcRange_realPath]; exact ⟨t, rfl⟩
  refine (isBetweenPt_iff hα hβ).2 ⟨⟨hzH, htw⟩, fun hR => ?_, fun hL => ?_⟩
  · rw [← arcRange_realPath] at hR
    exact Set.disjoint_left.1 hord.right_middle hzM hR
  · rw [← arcRange_realPath] at hL
    have hd := (WangWu.disjoint_rightSideOf_iff hγ.isProperArc hβ.isProperArc).1 hord.middle_left
    have hsw := WangWu.IsDiscCrosscut.disjoint_crossRange_crossSide_swap hγ.isProperArc.isDiscCrosscut_toDisc
      hβ.isProperArc.isDiscCrosscut_toDisc hd
    exact Set.disjoint_left.1 hsw ((hγ.isProperArc.cayley_mem_crossRange_iff hzHbar).2 hzM)
      ((hβ.isProperArc.mem_leftSideOf_iff hzH).1 hL)

/-- **On ordered simple proper curves with no common arcs of the middle curve, some point of the middle curve is between
the walls** (the contact times with the walls have empty interior, `Sec6.interior_setOf_mem_union_eq_empty`). -/
theorem exists_isBetweenPt_middle {β α γ : ℝ≥0 → ℂ} (hβ : IsSimpleProper β) (hα : IsSimpleProper α)
    (hγ : IsSimpleProper γ) (hord : WangWu.IsOrderedArcs (realPath α) (realPath γ) (realPath β))
    (hγα : NoCommonArc γ α) (hγβ : NoCommonArc γ β) :
    ∃ t : ℝ≥0, 0 < t ∧ IsBetweenPt (range α) (range β) (γ t) := by
  have h1 := interior_contact_eq_empty hγα
  have h2 := interior_contact_eq_empty hγβ
  have hcl : IsClosed (WangWu.arcRange (realPath α)) := hα.isProperArc.isClosed_arcRange
  have hu := Sec6.interior_setOf_mem_union_eq_empty hγ.isProperArc.cont hcl h1 h2
  have hnot : ¬ Ioo (1 : ℝ) 2 ⊆ {u ∈ Ici (0 : ℝ) | realPath γ u ∈
      WangWu.arcRange (realPath α) ∪ WangWu.arcRange (realPath β)} := by
    intro hsub
    have := interior_mono hsub
    rw [interior_Ioo, hu] at this
    exact (nonempty_Ioo.2 one_lt_two).ne_empty (subset_empty_iff.1 this)
  obtain ⟨u, hu12, hun⟩ := not_subset.1 hnot
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu12.1
  refine ⟨u.toNNReal, Real.toNNReal_pos.2 hu0, isBetweenPt_of_middle hβ hα hγ hord (Real.toNNReal_pos.2 hu0) ?_⟩
  intro hw
  refine hun ⟨hu0.le, ?_⟩
  rw [arcRange_realPath, arcRange_realPath]
  exact hw

variable {κ θ₁ θ₂ a b : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

/-- **The pocket domain of Lemma 7.1 on a given three-curve space**, measurable for the outer curves (the domain part
of `Lemma72B.IsPocketChartData`'s clause (S1), and its clause (S2)). On every space satisfying
`Lemma72B.IsThreeCurveSpace` there are a dense sequence `e`, a `σ(β, α)`-measurable index `Np` and a random domain `C`
— open, connected, simply connected and contained in `ℍ` for every `ω` — with `σ(β, α)`-measurable closed-ball events
and `e (Np ω) ∈ C ω`, which almost surely is a component of `ℍ ∖ (β ∪ α)` between the outer curves (`α` on the
right, `β` on the left), with `∂C ∩ ℍ ⊆ β ∪ α`. Here `σ(β, α)` is exactly the σ-algebra of `IsPocketChartData`. -/
theorem exists_pocketDomain_of_isThreeCurveSpace
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) :
    ∃ (e : ℕ → ℂ) (C : Ω → Set ℂ) (Np : Ω → ℕ), DenseRange e ∧
      Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] Np ∧
      (∀ ω, IsOpen (C ω) ∧ IsConnected (C ω) ∧ IsSimplyConnected (C ω) ∧ C ω ⊆ H) ∧
      (∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
        {ω | closedBall z r ⊆ C ω}) ∧
      (∀ ω, e (Np ω) ∈ C ω) ∧
      (∀ᵐ ω ∂P, C ω ∈ betweenComponents (range (α ω)) (range (β ω))) ∧
      (∀ᵐ ω ∂P, frontier (C ω) ∩ H ⊆ range (β ω) ∪ range (α ω)) := by
  obtain ⟨-, -, -, -, -, -, hβ, hα, -, hae⟩ := hS
  set m : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance with hm
  have hβm : ∀ t, Measurable[m] fun ω => β ω t := fun t =>
    ((measurable_pi_apply t).comp measurable_fst).comp (comap_measurable (fun ω => (β ω, α ω)))
  have hαm : ∀ t, Measurable[m] fun ω => α ω t := fun t =>
    ((measurable_pi_apply t).comp measurable_snd).comp (comap_measurable (fun ω => (β ω, α ω)))
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨C, Np, hNp, hC, hCm, hNpC, hCeq⟩ := exists_measurable_pocketDomain (m := m) hα.1 hβ.1 hα.2.1 hβ.2.1
    hαm hβm he
  -- almost surely the selected domain is a pocket
  have hgood : ∀ᵐ ω ∂P, IsSimpleProper (α ω) ∧ IsSimpleProper (β ω) ∧
      C ω = connectedComponentIn (H \ (range (α ω) ∪ range (β ω))) (e (Np ω)) ∧
      IsBetweenPt (range (α ω)) (range (β ω)) (e (Np ω)) := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, -, -, -, -, -, hβs, hαs, hγs, hord, hγα, hγβ⟩ := hω
    obtain ⟨t, ht, htB⟩ := exists_isBetweenPt_middle hβs hαs hγs hord hγα hγβ
    have hC₀ : connectedComponentIn (H \ (range (α ω) ∪ range (β ω))) (γ ω t) ∈
        betweenComponents (range (α ω)) (range (β ω)) := by
      obtain ⟨hz, hzR, hzL⟩ := (isBetweenPt_iff hαs hβs).1 htB
      exact ⟨γ ω t, hz, hzR, hzL, rfl⟩
    have hC₀o : IsOpen (connectedComponentIn (H \ (range (α ω) ∪ range (β ω))) (γ ω t)) :=
      (QuantumZipper.isOpen_H.sdiff ((IsSimpleProper.isClosed_range hαs).union
        (IsSimpleProper.isClosed_range hβs))).connectedComponentIn
    obtain ⟨k, hk⟩ := he.exists_mem_open hC₀o
      ⟨γ ω t, mem_connectedComponentIn ((isBetweenPt_iff hαs hβs).1 htB).1⟩
    obtain ⟨hB, hCω⟩ := hCeq ω ⟨k, isBetweenPt_of_mem hαs hβs hC₀ hk⟩
    have hcl : closure (range (α ω) ∪ range (β ω)) = range (α ω) ∪ range (β ω) :=
      ((IsSimpleProper.isClosed_range hαs).union (IsSimpleProper.isClosed_range hβs)).closure_eq
    rw [hcl] at hCω
    exact ⟨hαs, hβs, hCω, hB⟩
  refine ⟨e, C, Np, he, hNp, hC, hCm, hNpC, ?_, ?_⟩
  · filter_upwards [hgood] with ω hω
    obtain ⟨hαs, hβs, hCω, hB⟩ := hω
    obtain ⟨hz, hzR, hzL⟩ := (isBetweenPt_iff hαs hβs).1 hB
    rw [hCω]
    exact ⟨e (Np ω), hz, hzR, hzL, rfl⟩
  · filter_upwards [hgood] with ω hω
    obtain ⟨hαs, hβs, hCω, -⟩ := hω
    rw [hCω, union_comm (range (β ω))]
    exact frontier_connectedComponentIn_inter_H_subset
      ((IsSimpleProper.isClosed_range hαs).union (IsSimpleProper.isClosed_range hβs)) _

end Space

end InteractingSLE.Sec7.Lemma71Pin
