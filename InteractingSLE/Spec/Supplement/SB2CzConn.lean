/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfFill

/-!
# The event "the closure of a random set together with the lower half-plane is preconnected" is measurable

Packet PROVE-SB2-CANON. `Mz.TailCanonAt` asks for a retained hull `K` that is dyadic-hit measurable for the
(uncompleted) retained past `Ms.stageMarks ℓ`, compact at every sample and with `K ∪ {Im ≤ 0}` preconnected at every
sample. The landed constructions (`Nc.exists_retHull`) mask the filled stage set by a good event that is only
measurable for the completed σ-algebra. This file gives a mask in the uncompleted σ-algebra: for a random subset `B` of
`ℍ` that is measurable for the hitting σ-algebra, the event

`{ω | B ω is bounded and closure (B ω) ∪ {Im ≤ 0} is preconnected}`

is measurable (**`measurableSet_bounded_conn`**).

The key is a countable characterization (**`isPreconnected_iff_forall_ratBalls`**): for a compact `Y ⊆ {Im ≥ 0}`,
`Y ∪ {Im ≤ 0}` fails to be preconnected iff some finite union `U` of open balls with rational centres and radii has
`closure U ⊆ ℍ`, meets `Y`, and has frontier disjoint from `Y`. (If `Y ∪ L` splits into disjoint closed pieces, the
lower half-plane `L` lies in one of them; the other is a nonempty compact subset `A` of `Y` at positive distance from
it, and a finite cover of `A` by small rational balls is the required `U`.)

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Cz

/-! ### Finite unions of rational balls -/

/-- The centre `x + i y` of a rational ball `(x, y, r)`. -/
def ratCentre (p : ℚ × ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩

/-- The union of the open balls with the rational centres and radii of `s`. -/
def ratBalls (s : Finset (ℚ × ℚ × ℚ)) : Set ℂ := ⋃ p ∈ s, ball (ratCentre p) (p.2.2 : ℝ)

theorem isOpen_ratBalls (s : Finset (ℚ × ℚ × ℚ)) : IsOpen (ratBalls s) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem closure_ratBalls_subset (s : Finset (ℚ × ℚ × ℚ)) :
    closure (ratBalls s) ⊆ ⋃ p ∈ s, closedBall (ratCentre p) (p.2.2 : ℝ) := by
  refine closure_minimal (iUnion₂_mono fun p _ => ball_subset_closedBall) ?_
  exact s.finite_toSet.isClosed_biUnion fun p _ => isClosed_closedBall

theorem isBounded_ratBalls (s : Finset (ℚ × ℚ × ℚ)) : Bornology.IsBounded (ratBalls s) :=
  (Bornology.isBounded_biUnion s.finite_toSet).2 fun _ _ => isBounded_ball

theorem isCompact_frontier_ratBalls (s : Finset (ℚ × ℚ × ℚ)) : IsCompact (frontier (ratBalls s)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    ((isBounded_ratBalls s).closure.subset frontier_subset_closure)

/-! ### The countable characterization -/

theorem isClosed_lowerHalf : IsClosed Restart.lowerHalf :=
  isClosed_le Complex.continuous_im continuous_const

theorem isPreconnected_lowerHalf : IsPreconnected Restart.lowerHalf := by
  have hc : Convex ℝ Restart.lowerHalf := by
    intro x hx y hy a c ha hc hac
    change (a • x + c • y).im ≤ 0
    have hx' : x.im ≤ 0 := hx
    have hy' : y.im ≤ 0 := hy
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero]
    nlinarith
  exact hc.isPreconnected

/-- **Easy direction**: a rational-ball union with closure in `ℍ`, meeting `Y` and with frontier disjoint from `Y`,
disconnects `Y ∪ {Im ≤ 0}`. -/
theorem not_isPreconnected_of_ratBalls {Y : Set ℂ} {s : Finset (ℚ × ℚ × ℚ)} (hsH : closure (ratBalls s) ⊆ H)
    (hne : (Y ∩ ratBalls s).Nonempty) (hdis : Disjoint Y (frontier (ratBalls s))) :
    ¬ IsPreconnected (Y ∪ Restart.lowerHalf) := by
  intro hc
  have hU : IsOpen (ratBalls s) := isOpen_ratBalls s
  have hL : ∀ z ∈ Restart.lowerHalf, z ∉ closure (ratBalls s) := fun z hz hzc => by
    have h1 : 0 < z.im := hsH hzc
    have h2 : z.im ≤ 0 := hz
    linarith
  have hcov : Y ∪ Restart.lowerHalf ⊆ ratBalls s ∪ (closure (ratBalls s))ᶜ := by
    rintro z (hz | hz)
    · by_cases hzU : z ∈ ratBalls s
      · exact Or.inl hzU
      · refine Or.inr fun hzc => hdis.ne_of_mem hz ?_ rfl
        rw [hU.frontier_eq]
        exact ⟨hzc, hzU⟩
    · exact Or.inr (hL z hz)
  obtain ⟨y, hyY, hyU⟩ := hne
  obtain ⟨z, -, hzU, hzc⟩ := hc (ratBalls s) (closure (ratBalls s))ᶜ hU isClosed_closure.isOpen_compl hcov
    ⟨y, Or.inl hyY, hyU⟩ ⟨0, Or.inr Restart.zero_mem_lowerHalf, hL 0 Restart.zero_mem_lowerHalf⟩
  exact hzc (subset_closure hzU)

/-- The hard direction for one splitting (with the lower half-plane in `v`). -/
theorem exists_ratBalls_aux {Y u v : Set ℂ} (hYc : IsCompact Y) (hu : IsClosed u) (hv : IsClosed v)
    (hcov : Y ∪ Restart.lowerHalf ⊆ u ∪ v) (hdisj : Disjoint u v) (hnv : ¬ Y ∪ Restart.lowerHalf ⊆ v)
    (hLv : Restart.lowerHalf ⊆ v) :
    ∃ s : Finset (ℚ × ℚ × ℚ), closure (ratBalls s) ⊆ H ∧ (Y ∩ ratBalls s).Nonempty ∧
      Disjoint Y (frontier (ratBalls s)) := by
  classical
  set A := Y ∩ u with hAdef
  have hAc : IsCompact A := hYc.inter_right hu
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := by
    rw [not_subset] at hnv
    obtain ⟨z, hz, hzv⟩ := hnv
    rcases hz with hz | hz
    · exact ⟨z, hz, (hcov (Or.inl hz)).resolve_right hzv⟩
    · exact absurd (hLv hz) hzv
  have hAv : A ⊆ vᶜ := fun z hz hzv => hdisj.ne_of_mem hz.2 hzv rfl
  obtain ⟨δ, hδ, hδsub⟩ := hAc.exists_thickening_subset_open hv.isOpen_compl hAv
  set good : ℚ × ℚ × ℚ → Prop := fun p =>
    (∃ a ∈ A, dist (ratCentre p) a < δ / 8) ∧ δ / 8 < (p.2.2 : ℝ) ∧ (p.2.2 : ℝ) < δ / 4 with hgood
  set V : ℚ × ℚ × ℚ → Set ℂ := fun p => if good p then ball (ratCentre p) (p.2.2 : ℝ) else ∅ with hVdef
  have hVo : ∀ p, IsOpen (V p) := fun p => by
    by_cases hp : good p
    · simp only [hVdef, hp, ↓reduceIte]; exact isOpen_ball
    · simp only [hVdef, hp, ↓reduceIte]; exact isOpen_empty
  have hAV : A ⊆ ⋃ p, V p := by
    intro a ha
    obtain ⟨x, hx1, hx2⟩ := exists_rat_btwn (show a.re - δ / 16 < a.re + δ / 16 by linarith)
    obtain ⟨y, hy1, hy2⟩ := exists_rat_btwn (show a.im - δ / 16 < a.im + δ / 16 by linarith)
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show δ / 8 < δ / 4 by linarith)
    have hd : dist (ratCentre (x, y, r)) a < δ / 8 := by
      rw [Complex.dist_eq]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
      simp only [ratCentre, Complex.sub_re, Complex.sub_im]
      have h1 : |(x : ℝ) - a.re| < δ / 16 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      have h2 : |(y : ℝ) - a.im| < δ / 16 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      linarith
    have hg : good (x, y, r) := ⟨⟨a, ha, hd⟩, hr1, hr2⟩
    refine mem_iUnion.2 ⟨(x, y, r), ?_⟩
    simp only [hVdef, hg, ↓reduceIte, mem_ball]
    rw [dist_comm]
    exact hd.trans hr1
  obtain ⟨t, ht⟩ := hAc.elim_finite_subcover V hVo hAV
  set s := t.filter good with hsdef
  have hAs : A ⊆ ratBalls s := by
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 (ht hz)
    by_cases hg : good p
    · simp only [hVdef, hg, ↓reduceIte] at hzp
      exact mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨hp, hg⟩, hzp⟩
    · simp only [hVdef, hg, ↓reduceIte] at hzp
      exact absurd hzp (notMem_empty z)
  have hcl : closure (ratBalls s) ⊆ thickening δ A := by
    refine (closure_ratBalls_subset s).trans ?_
    intro z hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 hz
    obtain ⟨-, ⟨a, ha, had⟩, -, hr⟩ := Finset.mem_filter.1 hp
    rw [mem_thickening_iff]
    refine ⟨a, ha, ?_⟩
    have h1 : dist z (ratCentre p) ≤ (p.2.2 : ℝ) := mem_closedBall.1 hzp
    calc dist z a ≤ dist z (ratCentre p) + dist (ratCentre p) a := dist_triangle _ _ _
      _ < δ := by linarith
  have hclv : closure (ratBalls s) ⊆ vᶜ := hcl.trans hδsub
  refine ⟨s, fun z hz => ?_, ⟨a₀, ha₀.1, hAs ha₀⟩, ?_⟩
  · have hzv : z ∉ v := hclv hz
    have : z ∉ Restart.lowerHalf := fun hzL => hzv (hLv hzL)
    change 0 < z.im
    exact lt_of_not_ge this
  · rw [Set.disjoint_left]
    intro z hzY hzf
    have hzc : z ∈ closure (ratBalls s) := frontier_subset_closure hzf
    have hzu : z ∈ u := (hcov (Or.inl hzY)).resolve_right (hclv hzc)
    have hzU : z ∈ ratBalls s := hAs ⟨hzY, hzu⟩
    rw [(isOpen_ratBalls s).frontier_eq] at hzf
    exact hzf.2 hzU

/-- **Hard direction**: if `Y ∪ {Im ≤ 0}` is not preconnected (`Y` compact), a rational-ball union witnesses it. -/
theorem exists_ratBalls_of_not_isPreconnected {Y : Set ℂ} (hYc : IsCompact Y)
    (hnc : ¬ IsPreconnected (Y ∪ Restart.lowerHalf)) :
    ∃ s : Finset (ℚ × ℚ × ℚ), closure (ratBalls s) ⊆ H ∧ (Y ∩ ratBalls s).Nonempty ∧
      Disjoint Y (frontier (ratBalls s)) := by
  have hsc : IsClosed (Y ∪ Restart.lowerHalf) := hYc.isClosed.union isClosed_lowerHalf
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hsc] at hnc
  push Not at hnc
  obtain ⟨u, v, hu, hv, hcov, hdisj, hnu, hnv⟩ := hnc
  have hL := (isPreconnected_iff_subset_of_disjoint_closed.1 isPreconnected_lowerHalf) u v hu hv
    (subset_union_right.trans hcov) (by rw [hdisj.inter_eq, inter_empty])
  rcases hL with hLu | hLv
  · refine exists_ratBalls_aux hYc hv hu (fun z hz => ?_) hdisj.symm hnu hLu
    rcases hcov hz with h | h
    exacts [Or.inr h, Or.inl h]
  · exact exists_ratBalls_aux hYc hu hv hcov hdisj hnv hLv

/-- **The countable characterization of preconnectedness with the lower half-plane** (`Y` compact). -/
theorem isPreconnected_iff_forall_ratBalls {Y : Set ℂ} (hYc : IsCompact Y) :
    IsPreconnected (Y ∪ Restart.lowerHalf) ↔
      ∀ s : Finset (ℚ × ℚ × ℚ), closure (ratBalls s) ⊆ H → (Y ∩ ratBalls s).Nonempty →
        ¬ Disjoint Y (frontier (ratBalls s)) := by
  constructor
  · intro hc s hsH hne hdis
    exact not_isPreconnected_of_ratBalls hsH hne hdis hc
  · intro h
    by_contra hnc
    obtain ⟨s, hsH, hne, hdis⟩ := exists_ratBalls_of_not_isPreconnected hYc hnc
    exact h s hsH hne hdis

/-! ### Measurability -/

/-- Disjointness of a closure from a compact subset of `ℍ`, through the open thickenings. -/
theorem disjoint_closure_iff {B F : Set ℂ} (hF : IsCompact F) (hFH : F ⊆ H) :
    Disjoint (closure B) F ↔ ∃ n : ℕ, Disjoint B (thickening (1 / ((n : ℝ) + 1)) F ∩ H) := by
  constructor
  · intro hd
    obtain ⟨δ, hδ, hsub⟩ := hF.exists_thickening_subset_open isClosed_closure.isOpen_compl hd.subset_compl_left
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, Set.disjoint_left.2 fun z hzB hz => ?_⟩
    exact hsub (thickening_mono hn.le F hz.1) (subset_closure hzB)
  · rintro ⟨n, hn⟩
    rw [Set.disjoint_left]
    intro z hzc hzF
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hopen : IsOpen (thickening (1 / ((n : ℝ) + 1)) F ∩ H) := isOpen_thickening.inter QuantumZipper.isOpen_H
    obtain ⟨w, hw, hwB⟩ := mem_closure_iff.1 hzc _ hopen ⟨self_subset_thickening hpos F hzF, hFH hzF⟩
    exact hn.ne_of_mem hwB hw rfl

/-- **The bounded-and-connected event is measurable** for the marks of a hitting-measurable random subset of `ℍ`. -/
theorem measurableSet_bounded_conn {Ω : Type*} {𝒢 : MeasurableSpace Ω} {B : Ω → Set ℂ} (hBH : ∀ ω, B ω ⊆ H)
    (hBm : Measurable[𝒢, hittingSigma] B) :
    MeasurableSet[𝒢] {ω | Bornology.IsBounded (B ω) ∧ IsPreconnected (closure (B ω) ∪ Restart.lowerHalf)} := by
  have hav : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝒢] {ω | Disjoint (B ω) U} := fun U hU hUH =>
    hBm (LocalSets.measurableSet_avoid hU hUH)
  have hbd : MeasurableSet[𝒢] {ω | Bornology.IsBounded (B ω)} :=
    Lv.measurableSet_isBounded_of_avoid hBH fun U hUH => hav U U.isOpen hUH
  set S := {s : Finset (ℚ × ℚ × ℚ) // closure (ratBalls s) ⊆ H}
  set E : S → Set Ω := fun s => {ω | (closure (B ω) ∩ ratBalls s.1).Nonempty ∧
    Disjoint (closure (B ω)) (frontier (ratBalls s.1))} with hEdef
  have hE : ∀ s : S, MeasurableSet[𝒢] (E s) := by
    intro s
    have hFH : frontier (ratBalls s.1) ⊆ H := frontier_subset_closure.trans s.2
    have hUH : ratBalls s.1 ⊆ H := subset_closure.trans s.2
    have e1 : {ω | (closure (B ω) ∩ ratBalls s.1).Nonempty} = {ω | Disjoint (B ω) (ratBalls s.1)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, closure_inter_open_nonempty_iff (isOpen_ratBalls s.1),
        not_disjoint_iff_nonempty_inter]
    have e2 : {ω | Disjoint (closure (B ω)) (frontier (ratBalls s.1))} =
        ⋃ n : ℕ, {ω | Disjoint (B ω) (thickening (1 / ((n : ℝ) + 1)) (frontier (ratBalls s.1)) ∩ H)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      exact disjoint_closure_iff (isCompact_frontier_ratBalls s.1) hFH
    have hEe : E s = {ω | (closure (B ω) ∩ ratBalls s.1).Nonempty} ∩
        {ω | Disjoint (closure (B ω)) (frontier (ratBalls s.1))} := rfl
    rw [hEe, e1, e2]
    refine (hav _ (isOpen_ratBalls s.1) hUH).compl.inter (MeasurableSet.iUnion fun n => hav _ ?_ inter_subset_right)
    exact isOpen_thickening.inter QuantumZipper.isOpen_H
  have e : {ω | Bornology.IsBounded (B ω) ∧ IsPreconnected (closure (B ω) ∪ Restart.lowerHalf)} =
      {ω | Bornology.IsBounded (B ω)} ∩ (⋃ s : S, E s)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_iUnion, not_exists, hEdef]
    constructor
    · rintro ⟨hb, hc⟩
      refine ⟨hb, fun s ⟨hne, hdis⟩ => ?_⟩
      rw [isPreconnected_iff_forall_ratBalls hb.isCompact_closure] at hc
      exact hc s.1 s.2 hne hdis
    · rintro ⟨hb, hn⟩
      refine ⟨hb, (isPreconnected_iff_forall_ratBalls hb.isCompact_closure).2 fun s hsH hne hdis => ?_⟩
      exact hn ⟨s, hsH⟩ ⟨hne, hdis⟩
  rw [e]
  exact hbd.inter (MeasurableSet.iUnion hE).compl

end InteractingSLE.Theorem14.SB.Cz
