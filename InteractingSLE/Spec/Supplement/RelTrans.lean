/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelTransLand

/-!
# The relative transition: `RelTransitionStatement` PROVED

Packet PROVE-RELTRANS. Astra's follow-up 3, Q3 §3.3 ("the transition from its own chart to the relative chart
reflects across the connected interval containing the entire old counterflow base. Its derivative is positive …
`N(t) = 0`", `source/external/AstraIG1/ig1_followup3_audited.txt` L796–L872) and follow-up 5 §4.3 (L839–L842: "On each
positive-separation buffer, the transition chart reflects with positive derivative across the exposed counterflow
base. The one inherited logarithm has its initial zero phase and keeps that phase by continuity").

In the setting of `BHMean.RelTransitionStatement`, let `I = [a_L, a_R]` be the relative hull image
(`RelTransHull`; nonempty off `0` only if `u > 0` and `a_L < a_R`). Then:

* `I ⊆ U` (the joint parametrization lands on `cl K_t` there, which misses `cl A`), so the boundary values `T` of the
  transition increase strictly on `I` (`strictMonoOn_transBdry`) with `T 0 = 0` (the tip identity): `T` is
  injective on `I` and `T x` has the sign of `x`;
* at each `x ∈ I` the transition tends to the real point `T x`, whose landing point under the inverse explored map is
  the joint landing point, in `cl K_t`;
* **the integer lift is `0` on `I`** (the single-lift argument): the integer of `BHMean.exists_int_jointChart` is
  locally constant on the open set `U`, so the sets of points of `U` where the argument difference tends to `0`,
  resp. does not, are open (`isOpen_liftZero`, `isOpen_liftNeZero`); the interval `[a_L, a_R + δ/2] ⊆ U` is
  preconnected and its right end `a_R + δ/2` is an untouched real point (it lands off the relative hull, at a real
  point off `cl A ∪ cl K_t`), where the difference tends to `0` (`BHMean.tendsto_lift_sub_zero_of_untouched`).

Main results: **`relTransition_of_setting`**, **`relTransitionStatement : BHMean.RelTransitionStatement`** and
**`relUnionWordBoundaryStatement : BHMean.RelUnionWordBoundaryStatement`** (PROVE-BHMEAN's reduction
`BHMean.relUnionWordBoundaryStatement_of_transition`).

Deterministic. R48: nothing here takes Theorem 1.2/1.3 or a `*_of_param` result; the statements serve Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.Supp8.RelTrans

open BHMean (IsRetainedChart jointInv jointFwd jointLift jointChart)
open WangWu (chartAL chartAR)

/-- The inherited argument difference `Im log f_t' ∘ J − jointLift ∘ J` along the joint parametrization. -/
def liftDiff (Ψ Ψi LΨ : ℂ → ℂ) (w Wr : ℝ → ℝ) (t u : ℝ) (y : ℂ) : ℝ :=
  (logDerivFwd w t (jointInv Ψi Wr u y)).im - jointLift Ψ LΨ Wr u (jointInv Ψi Wr u y)

section Integer

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The local integer around a point of `U`**: one integer `n` and a radius on which every real point lies in `U`
and the argument difference tends to `2πn` (`BHMean.exists_int_jointChart`). -/
theorem exists_int_nhds (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {s : ℝ} (hs : extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A) :
    ∃ n : ℤ, ∃ ε > 0, ∀ s' : ℝ, dist s' s < ε → extendFrom H (jointInv Ψi Wr u) (s' : ℂ) ∉ closure A ∧
      Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s' : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_land hΨ hWr hWr0 hηr hu hs
  obtain ⟨n, ε, hε, hεr, hlim⟩ := BHMean.exists_int_jointChart hΨ hw hw0 hη ht hWr hWr0 hu hK hd hr
    (hland_of_ball hΨ hw ht hWr hWr0 hηr hu hK hd hball)
  refine ⟨n, ε, hε, fun s' hs' => ?_⟩
  have hmem : (s' : ℂ) ∈ ball (s : ℂ) ε := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq]; exact hs'
  exact ⟨hball _ (ball_subset_ball hεr hmem) (by simp), hlim _ hmem (by simp)⟩

/-- The points of `U` where the argument difference tends to `0` form an open set. -/
theorem isOpen_liftZero (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    IsOpen {s : ℝ | extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A ∧
      Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0)} := by
  rw [Metric.isOpen_iff]
  rintro s ⟨hs, hlim0⟩
  obtain ⟨n, ε, hε, hn⟩ := exists_int_nhds hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hs
  have := nhdsWithin_H_neBot_of_mem_Hbar (ofReal_mem_Hbar s)
  have hn0 : (2 * Real.pi * n : ℝ) = 0 :=
    tendsto_nhds_unique (hn s (by simpa using hε)).2 hlim0
  refine ⟨ε, hε, fun s' hs' => ⟨(hn s' hs').1, ?_⟩⟩
  have h := (hn s' hs').2
  rwa [hn0] at h

/-- The points of `U` where the argument difference does not tend to `0` form an open set. -/
theorem isOpen_liftNeZero (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    IsOpen {s : ℝ | extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A ∧
      ¬ Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0)} := by
  rw [Metric.isOpen_iff]
  rintro s ⟨hs, hlim0⟩
  obtain ⟨n, ε, hε, hn⟩ := exists_int_nhds hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hs
  have hn0 : (2 * Real.pi * n : ℝ) ≠ 0 := fun h => hlim0 (h ▸ (hn s (by simpa using hε)).2)
  refine ⟨ε, hε, fun s' hs' => ⟨(hn s' hs').1, fun h => hn0 ?_⟩⟩
  have := nhdsWithin_H_neBot_of_mem_Hbar (ofReal_mem_Hbar s')
  exact tendsto_nhds_unique (hn s' hs').2 h

/-- **The relative hull image lies in `U`**: there the joint parametrization lands on `cl K_t`, which misses
`cl A`. -/
theorem landOff_of_mem_Icc (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 < u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hlt : chartAL Wr u < chartAR Wr u) {s : ℝ} (hs : s ∈ Icc (chartAL Wr u) (chartAR Wr u)) :
    extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A :=
  Set.disjoint_left.1 hd (extendFrom_jointInv_mem_closure hΨ hw ht hWr hWr0 hηr hu.le hK hd (ofReal_mem_Hbar s)
    (Icc_subset_hullImage hηr hWr hWr0 hu hlt hs))

/-- **The integer lift is `0` on the relative hull image** (the single-lift argument). -/
theorem tendsto_liftDiff_zero_of_mem_Icc (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 < u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hlt : chartAL Wr u < chartAR Wr u) {x : ℝ} (hx : x ∈ Icc (chartAL Wr u) (chartAR Wr u)) :
    Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set U : Set ℝ := {s : ℝ | extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A} with hUdef
  have hIU : Icc (chartAL Wr u) (chartAR Wr u) ⊆ U := fun s hs =>
    landOff_of_mem_Icc hΨ hw ht hWr hWr0 hηr hu hK hd hlt hs
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 (isOpen_landOff hΨ hWr hWr0 hηr hu.le) _
    (hIU ⟨hlt.le, le_rfl⟩)
  set x' : ℝ := chartAR Wr u + δ / 2 with hx'def
  have hS : Icc (chartAL Wr u) x' ⊆ U := fun s hs => by
    rcases le_or_gt s (chartAR Wr u) with h | h
    · exact hIU ⟨hs.1, h⟩
    · apply hδU
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hs.2]
  have hx'U : x' ∈ U := hS ⟨by linarith, le_rfl⟩
  -- the untouched real point `x'` right of the relative hull image
  have hx'0 : Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
    have hy := extendFrom_notMem_closure_of_chartAR_lt hηr hWr hWr0 hu.le (x := x') (by linarith)
    obtain ⟨hpim, hpK⟩ := landing_real_of_notMem hΨ hw ht hWr hWr0 hηr hu.le hK hd hy hx'U
    exact BHMean.tendsto_lift_sub_zero_of_untouched hΨ hw hw0 ht hWr hWr0 hηr hu.le hK hd hy
      (tendsto_jointInv hΨ hWr hWr0 hηr hu.le (ofReal_mem_Hbar x')).1 hpim hx'U hpK
  have hsub := (isPreconnected_Icc (a := chartAL Wr u) (b := x')).subset_left_of_subset_union
    (isOpen_liftZero hΨ hw hw0 hη ht hWr hWr0 hηr hu.le hK hd)
    (isOpen_liftNeZero hΨ hw hw0 hη ht hWr hWr0 hηr hu.le hK hd)
    (Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2)
    (fun s hs => (em (Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0))).imp
      (fun h => ⟨hS hs, h⟩) (fun h => ⟨hS hs, h⟩))
    ⟨x', ⟨by linarith, le_rfl⟩, hx'U, hx'0⟩
  exact (hsub ⟨hx.1, hx.2.trans (by linarith)⟩).2

end Integer

/-! ### Assembly -/

section Assembly

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- A point of the relative hull image other than `0` forces `u > 0` and `a_L < a_R`, and lies in `[a_L, a_R]`. -/
theorem pos_and_lt_of_mem_hullImage (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) {x : ℝ} (hx0 : x ≠ 0)
    (hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)) :
    0 < u ∧ chartAL Wr u < chartAR Wr u ∧ x ∈ Icc (chartAL Wr u) (chartAR Wr u) := by
  have hxI := hullImage_subset_Icc hηr hWr hWr0 hu hxK
  have h1 := WangWu.chartAL_nonpos hWr hu
  have h2 := WangWu.chartAR_nonneg hWr hu
  refine ⟨?_, ?_, hxI⟩
  · rcases hu.eq_or_lt with h | h
    · rw [← h, QuantumZipper.RS.fwdHull_zero_eq_empty hWr, closure_empty] at hxK
      exact absurd hxK (notMem_empty _)
    · exact h
  · rcases lt_or_gt_of_ne hx0 with h | h
    · linarith [hxI.1]
    · linarith [hxI.2]

/-- **The transition facts of the relative configuration** (`BHMean.RelTransition`), in the setting of
`BHMean.RelTransitionStatement`. -/
theorem relTransition_of_setting (hΨ : IsRetainedChart A Ψ Ψi LΨ) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (htip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)) :
    BHMean.RelTransition Ψ Ψi LΨ w Wr t u := by
  refine ⟨transBdry Ψi w Wr t u, ?_, fun x hx0 hxK => ?_⟩
  · rintro x₁ ⟨hx₁0, hx₁K⟩ x₂ ⟨-, hx₂K⟩ he
    obtain ⟨hu', hlt, hx₁I⟩ := pos_and_lt_of_mem_hullImage hWr hWr0 hηr hu hx₁0 hx₁K
    have hx₂I := hullImage_subset_Icc hηr hWr hWr0 hu hx₂K
    exact (strictMonoOn_transBdry hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd fun s hs =>
      landOff_of_mem_Icc hΨ hw ht hWr hWr0 hηr hu' hK hd hlt hs).injOn hx₁I hx₂I he
  · obtain ⟨hu', hlt, hxI⟩ := pos_and_lt_of_mem_hullImage hWr hWr0 hηr hu hx0 hxK
    have hIU : ∀ s ∈ Icc (chartAL Wr u) (chartAR Wr u), extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A :=
      fun s hs => landOff_of_mem_Icc hΨ hw ht hWr hWr0 hηr hu' hK hd hlt hs
    have hmono := strictMonoOn_transBdry hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hIU
    have h0I : (0 : ℝ) ∈ Icc (chartAL Wr u) (chartAR Wr u) :=
      ⟨WangWu.chartAL_nonpos hWr hu, WangWu.chartAR_nonneg hWr hu⟩
    have hT0 : transBdry Ψi w Wr t u 0 = 0 := transBdry_zero htip
    have hsign : 0 < transBdry Ψi w Wr t u x ↔ 0 < x := by
      constructor
      · intro h
        by_contra hle
        have := (hmono.le_iff_le hxI h0I).2 (not_lt.1 hle)
        linarith
      · intro h
        have := hmono h0I hxI h
        linarith
    have hTne : transBdry Ψi w Wr t u x ≠ 0 := by
      intro h
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have := hmono hxI h0I hneg; linarith
      · have := hmono h0I hxI hpos; linarith
    obtain ⟨v, hv, hFv, hTl⟩ := exists_tendsto_transition hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd
      (z := (x : ℂ)) (by simp) (hIU x hxI)
    have hφ : extendFrom H (fun y => fwdMap w t (jointInv Ψi Wr u y)) (x : ℂ) = v :=
      extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar x) hTl
    have hvT : v = ((transBdry Ψi w Wr t u x : ℝ) : ℂ) := by
      simp only [transBdry, hφ]
      exact Complex.ext (by simp) (by simp [hv])
    refine ⟨hsign, hTne, ?_, ?_, ?_⟩
    · rw [← hvT, hFv]
      exact extendFrom_jointInv_mem_closure hΨ hw ht hWr hWr0 hηr hu hK hd (ofReal_mem_Hbar x) hxK
    · rw [← hvT]
      exact hTl
    · exact tendsto_liftDiff_zero_of_mem_Icc hΨ hw hw0 hη ht hWr hWr0 hηr hu' hK hd hlt hxI

end Assembly

/-- **`RelTransitionStatement` PROVED**: the transition facts of every relative configuration (curves allowed to hit
`ℝ`). -/
theorem relTransitionStatement : BHMean.RelTransitionStatement := by
  intro A Ψ Ψi LΨ w Wr η ηr t u hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd htip
  exact relTransition_of_setting hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd htip

/-- **The boundary-hitting mean identification PROVED** (`BHMean.RelUnionWordBoundaryStatement`, Astra Q3 §3.3 and
follow-up 5 §4.3; GB6, GW2's joint (Det)). -/
theorem relUnionWordBoundaryStatement : BHMean.RelUnionWordBoundaryStatement :=
  BHMean.relUnionWordBoundaryStatement_of_transition relTransitionStatement

end InteractingSLE.Supp8.RelTrans
