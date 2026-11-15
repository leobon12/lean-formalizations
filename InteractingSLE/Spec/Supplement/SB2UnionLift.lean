/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UnionChart

/-!
# Lemma SB2 at a junction: landing, transition and the single lift through the free collar

Packet PROVE-T14-SB2UNION. The single-lift argument of the landed union mean (`Supp8.Q3Rel`, PROVE-RELTRANS) works on
the set `U` of real points whose joint landing point is off the closed retained set `cl A`; that set contains the whole
relative hull image `[a_L, a_R]` only when the explored hull misses `cl A`. At a junction the two base points of the
relative hull land on `A`: SB2(1)'s relative curve starts at the prime end over `L = min (A ∩ ℝ)`, and its current right
record junction is on `A` (p. 632).

The local integer lemma (`Sec7.Lemma71O.exists_int_wall`) only needs the joint parametrization to land **off `ℍ ∖ K_t`**
near the point, not off `cl A`. The source's "free left collar" gives exactly that at the left base: to its left the
landing points are untouched original real points, at the base the point `L` itself, to its right the curve's left side.
So this file works with an open set `V` of real points that are good and land off `ℍ ∖ K_t` (`IsJLand`):

* `exists_tendsto_transition_rel`, `isRealBoundaryConformal_transition_rel`, `hasDerivAt_transBdry_rel`,
  `strictMonoOn_transBdry_rel`: the transition `τ = f_t ∘ Ψi ∘ f̃_u⁻¹` on `V` (the landed proofs on `relComp`);
* `continuousOn_transBdry_insert_zero`: its boundary values are continuous on `V ∪ {0}` (the tip identity at `0`);
* **`tendsto_liftDiff_zero_of_isPreconnected`**: the single-lift argument on any preconnected subset of `V` that
  contains one point where the argument difference tends to `0`;
* **`tendsto_liftDiff_zero_of_free_collar`**: SB2's form — if `V ⊇ [x₀, a_R)` for a point `x₀ < a_L` landing at an
  untouched real point ("the far-left original-real interval anchors the derivative logarithm at zero. The upper flow
  has a free left collar, which joins that anchor", p. 632), the argument difference tends to `0` at every point of
  `[x₀, a_R)`, the whole relative hull image except its right base;
* `transBdry_pos_iff_rel`, `strictMonoOn_transBdry_Ico`: the sign and injectivity of the transition on `[a_L, a_R)`.

Deterministic. Conditional helpers with distinct names; they replace no source theorem. R48: serves Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Theorem14.SB.Union

open Supp8.BHMean (jointInv jointFwd jointLift jointChart jointLog)
open Supp8.Q3Rel (IsRetainedChartOff IsGoodPt)
open Supp8.RelTrans (nhdsWithin_H_neBot_of_mem_Hbar ofReal_mem_Hbar transBdry liftDiff)
open WangWu (chartAL chartAR)

/-- **A real point of the joint chart landing off `ℍ ∖ K_t`**: it is good (its relative landing point is not
exceptional) and its joint landing point is not a point of `ℍ ∖ K_t` (a real point or a point of `K_t`). -/
def IsJLand (Sb : Finset ℝ) (Ψi : ℂ → ℂ) (w Wr : ℝ → ℝ) (t u : ℝ) (s : ℝ) : Prop :=
  IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ H \ fwdHull w t

/-- A point of the closed explored hull is not a point of `ℍ ∖ K_t`. -/
theorem notMem_compl_of_mem_closure {w : ℝ → ℝ} {t : ℝ} (hw : Continuous w) (ht : 0 ≤ t) {p : ℂ}
    (hp : p ∈ closure (fwdHull w t)) : p ∉ H \ fwdHull w t := by
  intro hpC
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht) p hpC
  obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hp r hr
  exact (hball (by rw [mem_ball, dist_comm]; exact hzb)).2 hzK

section Landing

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **A real good landing point is not a point of the relative component.** -/
theorem extendFrom_jointInv_notMem_relComp (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) {z : ℂ} (hz : z.im = 0) (hg : IsGoodPt Sb Wr u z) :
    extendFrom H (jointInv Ψi Wr u) z ∉ relComp A Ψ Wr u := by
  intro hp
  have hzb : z ∈ Hbar := show (0 : ℝ) ≤ z.im from hz.ge
  have hJ := (Supp8.Q3Rel.tendsto_jointInv hΨ hWr hWr0 hηr hu hzb hg).1
  have hc : ContinuousAt (jointFwd Ψ Wr u) (extendFrom H (jointInv Ψi Wr u) z) :=
    (differentiableAt_jointFwd_rel hΨ hWr hWr0 hu hp).continuousAt
  have h1 : Tendsto (fun y => jointFwd Ψ Wr u (jointInv Ψi Wr u y)) (𝓝[H] z)
      (𝓝 (jointFwd Ψ Wr u (extendFrom H (jointInv Ψi Wr u) z))) := hc.tendsto.comp hJ
  have h2 : Tendsto (fun y => jointFwd Ψ Wr u (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 z) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      (jointFwd_jointInv_rel hΨ hWr hWr0 hu hy).symm)
  have := nhdsWithin_H_neBot_of_mem_Hbar hzb
  have he := tendsto_nhds_unique h1 h2
  have hpos : (0 : ℝ) < (jointFwd Ψ Wr u (extendFrom H (jointInv Ψi Wr u) z)).im :=
    jointFwd_mem_of_relComp hΨ hWr hWr0 hu hp
  rw [he, hz] at hpos
  exact lt_irrefl _ hpos

/-- **Around a point of an open set of `IsJLand` points**, every real point is good and lands off `ℍ ∖ K_t`. -/
theorem exists_ball_jland {V : Set ℝ} (hV : IsOpen V) (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) {x : ℝ}
    (hx : x ∈ V) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hV x hx
  refine ⟨r, hr, fun z hz hz0 => ?_⟩
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
  have hmem : z.re ∈ ball x r := by
    rw [mem_ball, ← Complex.isometry_ofReal.dist_eq, ← hzr]
    exact hz
  have h : IsJLand Sb Ψi w Wr t u z.re := hVl _ (hsub hmem)
  rw [IsJLand, ← hzr] at h
  exact h

/-- The landing hypothesis of the local integer lemma on such a ball. -/
theorem hland_of_ball_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) {x r : ℝ}
    (hball : ∀ z ∈ ball (x : ℂ) r, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t) :
    ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull w t ∧ Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p) :=
  fun z hz hz0 => ⟨_, (hball z hz hz0).2, (Supp8.Q3Rel.tendsto_jointInv hΨ hWr hWr0 hηr hu
    (show (0 : ℝ) ≤ z.im from hz0.ge) (hball z hz hz0).1).1⟩

end Landing

/-! ### The transition on `V` -/

section Transition

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The transition has a real limit** at every good real point landing off `ℍ ∖ K_t`, and the inverse explored map
sends it to the joint landing point. -/
theorem exists_tendsto_transition_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    {z : ℂ} (hz : z.im = 0) (hg : IsGoodPt Sb Wr u z) (hzK : extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t) :
    ∃ v : ℂ, v.im = 0 ∧ extendFrom H (fwdMapInv w t) v = extendFrom H (jointInv Ψi Wr u) z ∧
      Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 v) := by
  have hzb : z ∈ Hbar := show (0 : ℝ) ≤ z.im from hz.ge
  have hc := isConformal_jointChart_rel (LΨ := LΨ) hΨ hWr hWr0 hu
  have hCt : ((jointChart Ψ Ψi LΨ Wr u).dom : Set ℂ) ⊆ H \ fwdHull w t := by
    rw [coe_dom_jointChart_rel hΨ hWr hWr0 hu]
    exact fun y hy => ⟨(relComp_subset hKin hy).1, fun h => (relComp_subset hKin hy).2 (Or.inr h)⟩
  obtain ⟨v, hv, hFv, hT⟩ := Sec7.Lemma71O.exists_tendsto_fwdMap_comp hη hw hw0 ht hc hCt hzb
    (Supp8.Q3Rel.tendsto_jointInv hΨ hWr hWr0 hηr hu hzb hg).1
  exact ⟨v, Sec7.Lemma71O.im_eq_zero_of_land hw hw0 ht hv hFv hzK, hFv, hT⟩

/-- **The transition is real-boundary conformal** on a half-disc whose real points are good and land off
`ℍ ∖ K_t`. -/
theorem isRealBoundaryConformal_transition_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) {x r : ℝ}
    (hball : ∀ z ∈ ball (x : ℂ) r, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t) :
    R16.IsRealBoundaryConformal (extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y)) x r :=
  Sec7.Lemma71O.isRealBoundaryConformal_extendFrom (c := jointChart Ψ Ψi LΨ Wr u)
    (D := H \ fwdHull w t)
    (isConformal_jointChart_rel hΨ hWr hWr0 hu) (coe_dom_jointChart_rel hΨ hWr hWr0 hu)
    (fun y hy => ⟨(relComp_subset hKin hy).1, fun h => (relComp_subset hKin hy).2 (Or.inr h)⟩)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw ht) (QuantumZipper.FwdHolo.injOn_fwdMap hw ht)
    (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz) fun z hz hz0 => by
      obtain ⟨v, hv, -, hT⟩ := exists_tendsto_transition_rel hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hz0
        (hball z hz hz0).1 (hball z hz hz0).2
      exact ⟨v, hv, hT⟩

/-- **The boundary values of the transition have a positive derivative** at every point of an open set of `IsJLand`
points. -/
theorem hasDerivAt_transBdry_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) {V : Set ℝ} (hV : IsOpen V)
    (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) {x : ℝ} (hx : x ∈ V) :
    ∃ d > 0, HasDerivAt (transBdry Ψi w Wr t u) d x := by
  obtain ⟨r, hr, hball⟩ := exists_ball_jland hV hVl hx
  have hrbc := isRealBoundaryConformal_transition_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hball
  set φ : ℂ → ℂ := extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y) with hφdef
  have hxb : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hdiff : HasDerivAt (schwarzReflect φ) (deriv (schwarzReflect φ) x) x :=
    ((hrbc.differentiableOn_schwarzReflect).differentiableAt (isOpen_ball.mem_nhds hxb)).hasDerivAt
  have heq : transBdry Ψi w Wr t u = fun s : ℝ => (schwarzReflect φ s).re := by
    funext s
    simp only [transBdry, schwarzReflect, Complex.ofReal_im, le_refl, ↓reduceIte, hφdef]
  refine ⟨(deriv (schwarzReflect φ) x).re, (hrbc.deriv_schwarzReflect_pos hxb).2, ?_⟩
  rw [heq]
  exact hdiff.real_of_complex

/-- **The boundary values of the transition are continuous on `V ∪ {0}`** (on `V` by the transition limits, at `0` by
the tip identity). -/
theorem continuousOn_transBdry_insert_zero (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    {V : Set ℝ} (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s)
    (htip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)) :
    ContinuousOn (transBdry Ψi w Wr t u) (insert 0 V) := by
  set B : Set ℂ := (fun s : ℝ => (s : ℂ)) '' insert 0 V with hBdef
  have hB : B ⊆ closure H := by
    rintro _ ⟨s, -, rfl⟩
    rw [closure_H]
    exact ofReal_mem_Hbar s
  have hlim : ∀ z ∈ B, ∃ v, Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 v) := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with rfl | hs
    · exact ⟨0, by simpa [jointInv] using htip⟩
    · obtain ⟨v, -, -, hT⟩ := exists_tendsto_transition_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin
        (show ((s : ℂ)).im = 0 by simp) (hVl s hs).1 (hVl s hs).2
      exact ⟨v, hT⟩
  have hc : ContinuousOn (extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y)) B := continuousOn_extendFrom hB hlim
  have hc' : ContinuousOn (fun s : ℝ => extendFrom H (fun y => fwdMap w t (jointInv Ψi Wr u y)) (s : ℂ))
      (insert 0 V) :=
    hc.comp Complex.continuous_ofReal.continuousOn fun s hs => ⟨s, hs, rfl⟩
  exact continuous_re.comp_continuousOn hc'

/-- **The boundary values of the transition increase strictly on every interval inside `V`.** -/
theorem strictMonoOn_transBdry_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) {V : Set ℝ} (hV : IsOpen V)
    (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) {a b : ℝ} (hab : Icc a b ⊆ V) :
    StrictMonoOn (transBdry Ψi w Wr t u) (Icc a b) := by
  have hder : ∀ s ∈ Icc a b, ∃ d > 0, HasDerivAt (transBdry Ψi w Wr t u) d s := fun s hs =>
    hasDerivAt_transBdry_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl (hab hs)
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨d, -, hd'⟩ := hder s hs
    exact hd'.continuousAt.continuousWithinAt
  · obtain ⟨d, hd0, hd'⟩ := hder s (interior_subset hs)
    rw [hd'.deriv]
    exact hd0

end Transition

/-! ### The single lift through the free collar -/

section Lift

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The local integer on `V`**: around a point of `V` the argument difference tends to `2πn` at the real points of a
ball inside `V`, for one integer `n`. -/
theorem exists_int_nhds_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) {V : Set ℝ} (hV : IsOpen V)
    (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) {s : ℝ} (hs : s ∈ V) :
    ∃ n : ℤ, ∃ ε > 0, ∀ s' : ℝ, dist s' s < ε → s' ∈ V ∧
      Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s' : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.1 hV s hs
  obtain ⟨r, hr, hball⟩ := exists_ball_jland hV hVl hs
  set ρ := min r r₀ with hρ
  have hρ0 : 0 < ρ := lt_min hr hr₀
  have hball' : ∀ z ∈ ball (s : ℂ) ρ, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t := fun z hz hz0 =>
    hball z (ball_subset_ball (min_le_left _ _) hz) hz0
  obtain ⟨n, ε, hε, hερ, hlim⟩ := exists_int_jointChart_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hu hKin hρ0
    (hland_of_ball_rel hΨ hWr hWr0 hηr hu hball')
  refine ⟨n, ε, hε, fun s' hs' => ⟨hsub ?_, ?_⟩⟩
  · rw [mem_ball]
    exact lt_of_lt_of_le hs' (hερ.trans (min_le_right _ _))
  · have hmem : (s' : ℂ) ∈ ball (s : ℂ) ε := by
      rw [mem_ball, Complex.isometry_ofReal.dist_eq]; exact hs'
    exact hlim _ hmem (by simp)

/-- **The single-lift argument on a preconnected subset of `V`**: if the argument difference tends to `0` at one point
of a preconnected set `S ⊆ V`, it tends to `0` at every point of `S`. -/
theorem tendsto_liftDiff_zero_of_isPreconnected (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    {V : Set ℝ} (hV : IsOpen V) (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) {S : Set ℝ} (hSV : S ⊆ V)
    (hS : IsPreconnected S) {x₀ : ℝ} (hx₀ : x₀ ∈ S)
    (h0 : Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (x₀ : ℂ)) (𝓝 0)) {x : ℝ} (hx : x ∈ S) :
    Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set Z : Set ℝ := {s | s ∈ V ∧ Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0)} with hZ
  set N : Set ℝ := {s | s ∈ V ∧ ¬ Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0)} with hN
  have hZo : IsOpen Z := by
    rw [Metric.isOpen_iff]
    rintro s ⟨hs, hlim0⟩
    obtain ⟨n, ε, hε, hn⟩ := exists_int_nhds_rel hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hs
    have := nhdsWithin_H_neBot_of_mem_Hbar (ofReal_mem_Hbar s)
    have hn0 : (2 * Real.pi * n : ℝ) = 0 := tendsto_nhds_unique (hn s (by simpa using hε)).2 hlim0
    refine ⟨ε, hε, fun s' hs' => ⟨(hn s' hs').1, ?_⟩⟩
    have h := (hn s' hs').2
    rwa [hn0] at h
  have hNo : IsOpen N := by
    rw [Metric.isOpen_iff]
    rintro s ⟨hs, hlim0⟩
    obtain ⟨n, ε, hε, hn⟩ := exists_int_nhds_rel hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hs
    have hn0 : (2 * Real.pi * n : ℝ) ≠ 0 := fun h => hlim0 (h ▸ (hn s (by simpa using hε)).2)
    refine ⟨ε, hε, fun s' hs' => ⟨(hn s' hs').1, fun h => hn0 ?_⟩⟩
    have := nhdsWithin_H_neBot_of_mem_Hbar (ofReal_mem_Hbar s')
    exact tendsto_nhds_unique (hn s' hs').2 h
  have hsub := hS.subset_left_of_subset_union hZo hNo (Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2)
    (fun s hs => (em (Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0))).imp
      (fun h => ⟨hSV hs, h⟩) (fun h => ⟨hSV hs, h⟩))
    ⟨x₀, hx₀, hSV hx₀, h0⟩
  exact (hsub hx).2

/-- **The single lift through the free collar** (SB2, p. 632: "The far-left original-real interval anchors the
derivative logarithm at zero. The upper flow has a free left collar, which joins that anchor"). If `V` contains
`[x₀, a_R)` for a point `x₀ < a_L` landing at an untouched real point `p₀ ≠ 0` (off `cl A` and `cl K_t`), the argument
difference tends to `0` at every point of `[x₀, a_R)`: the whole relative hull image except its right base. -/
theorem tendsto_liftDiff_zero_of_free_collar (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u)
    {V : Set ℝ} (hV : IsOpen V) (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) {x₀ : ℝ}
    (hx₀ : x₀ < chartAL Wr u) (hIV : Ico x₀ (chartAR Wr u) ⊆ V)
    (hp₀A : extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ∉ closure A)
    (hp₀K : extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ∉ closure (fwdHull w t))
    (hp₀0 : extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ≠ 0) {x : ℝ} (hx : x ∈ Ico x₀ (chartAR Wr u)) :
    Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hx₀AR : x₀ < chartAR Wr u := hx₀.trans_le ((WangWu.chartAL_nonpos hWr hu).trans
    (WangWu.chartAR_nonneg hWr hu))
  have hx₀V : x₀ ∈ V := hIV ⟨le_rfl, hx₀AR⟩
  have hy : extendFrom H (fwdMapInv Wr u) (x₀ : ℂ) ∉ closure (fwdHull Wr u) :=
    Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hηr hWr hWr0 hu hx₀
  have hJ := (Supp8.Q3Rel.tendsto_jointInv hΨ hWr hWr0 hηr hu (ofReal_mem_Hbar x₀) (hVl x₀ hx₀V).1).1
  -- the landing point at `x₀` is real: it is not in `ℍ ∖ K_t` and not in `cl K_t`
  have hpim : (extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ)).im = 0 := by
    have hpbar : extendFrom H (jointInv Ψi Wr u) (x₀ : ℂ) ∈ Hbar := by
      rw [← closure_H]
      have := nhdsWithin_H_neBot_of_mem_Hbar (ofReal_mem_Hbar x₀)
      exact mem_closure_of_tendsto hJ (eventually_nhdsWithin_of_forall fun y hy =>
        (jointInv_mem_relComp hΨ hWr hWr0 hu hy).1.1)
    refine le_antisymm (not_lt.1 fun hpos => ?_) hpbar
    exact (hVl x₀ hx₀V).2 ⟨hpos, fun hK => hp₀K (subset_closure hK)⟩
  have h0 := tendsto_lift_sub_zero_of_untouched_rel (LΨ := LΨ) hΨ hw hw0 ht hWr hWr0 hηr hu hy hJ hpim hp₀A hp₀K
    hp₀0
  exact tendsto_liftDiff_zero_of_isPreconnected hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hIV isPreconnected_Ico
    ⟨le_rfl, hx₀AR⟩ h0 hx

/-- **The transition increases strictly on `[a_L, a_R)`** when `V` contains it. -/
theorem strictMonoOn_transBdry_Ico (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) {V : Set ℝ} (hV : IsOpen V)
    (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) (hIV : Ico (chartAL Wr u) (chartAR Wr u) ⊆ V) :
    StrictMonoOn (transBdry Ψi w Wr t u) (Ico (chartAL Wr u) (chartAR Wr u)) := by
  intro a ha b hb hab
  have hsub : Icc a b ⊆ V := fun s hs => hIV ⟨ha.1.trans hs.1, hs.2.trans_lt hb.2⟩
  exact strictMonoOn_transBdry_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hsub
    ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab

/-- **The sign of the transition on `[a_L, a_R)`**: with the tip identity, `T x` has the sign of `x`. -/
theorem transBdry_pos_iff_rel (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hKin : ∀ z ∈ fwdHull w t, z ∉ A → Ψ z ∈ fwdHull Wr u) {V : Set ℝ} (hV : IsOpen V)
    (hVl : ∀ s ∈ V, IsJLand Sb Ψi w Wr t u s) (hIV : Ico (chartAL Wr u) (chartAR Wr u) ⊆ V)
    (htip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0))
    {x : ℝ} (hx : x ∈ Ico (chartAL Wr u) (chartAR Wr u)) (hx0 : x ≠ 0) :
    (0 < transBdry Ψi w Wr t u x ↔ 0 < x) ∧ transBdry Ψi w Wr t u x ≠ 0 := by
  have hT0 : transBdry Ψi w Wr t u 0 = 0 := Supp8.RelTrans.transBdry_zero htip
  have hAL : chartAL Wr u ≤ 0 := WangWu.chartAL_nonpos hWr hu
  have hcont := continuousOn_transBdry_insert_zero (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hVl htip
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · -- `x < 0`: strict monotonicity on `[x, 0]`, continuous there, positive derivative inside
    have hsub : Icc x 0 ⊆ insert 0 V := by
      intro s hs
      rcases hs.2.eq_or_lt with h | h
      · exact Or.inl h
      · exact Or.inr (hIV ⟨hx.1.trans hs.1, h.trans_le (WangWu.chartAR_nonneg hWr hu)⟩)
    have hmono : StrictMonoOn (transBdry Ψi w Wr t u) (Icc x 0) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc x 0) (hcont.mono hsub) fun s hs => ?_
      rw [interior_Icc] at hs
      obtain ⟨d, hd0, hd'⟩ := hasDerivAt_transBdry_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl
        (hIV ⟨hx.1.trans hs.1.le, hs.2.trans_le (WangWu.chartAR_nonneg hWr hu)⟩)
      rw [hd'.deriv]
      exact hd0
    have hlt := hmono ⟨le_rfl, hneg.le⟩ ⟨hneg.le, le_rfl⟩ hneg
    rw [hT0] at hlt
    exact ⟨⟨fun h => absurd h (not_lt.2 hlt.le), fun h => absurd h (not_lt.2 hneg.le)⟩, hlt.ne⟩
  · have hsub : Icc 0 x ⊆ V := fun s hs => hIV ⟨hAL.trans hs.1, hs.2.trans_lt hx.2⟩
    have hlt := strictMonoOn_transBdry_rel (LΨ := LΨ) hΨ hw hw0 hη ht hWr hWr0 hηr hu hKin hV hVl hsub
      ⟨le_rfl, hpos.le⟩ ⟨hpos.le, le_rfl⟩ hpos
    rw [hT0] at hlt
    exact ⟨⟨fun _ => hpos, fun _ => hlt⟩, hlt.ne'⟩

end Lift

end InteractingSLE.Theorem14.SB.Union
