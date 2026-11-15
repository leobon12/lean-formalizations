/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelBHLand
import InteractingSLE.Spec.Supplement.BHMeanLaw

/-!
# The boundary-hitting mean identification with a retained chart landing off a finite set

Packet PROVE-Q3-REL. **`relUnionWordBoundaryOffStatement : RelUnionWordBoundaryOffStatement`**: PROVE-BHMEAN's
`RelUnionWordBoundaryStatement` (proved by PROVE-RELTRANS) for retained charts whose inverse lands only off a finite set
`Sb` of real points (`IsRetainedChartOff`), provided the exceptional points lie off the closed relative hull. This is
the form GB6 and GW2 need: there the retained set is the inversion of the other curve's hull, which is unbounded, and
the inverse chart tends to `∞` at the images of the two sides of that curve's base (see `Q3RelBHChart`).

* the single-lift argument at good points (`tendsto_liftDiff_zero_of_mem_Icc`) and the transition facts
  (`relTransition_of_setting`: `BHMean.RelTransition` with the same proof as PROVE-RELTRANS's);
* `finite_badPts`: the real points of the joint chart landing at exceptional points are finitely many (each is
  determined by its landing point);
* **`hasUnionWordBoundary_of_relTransition`**: the union datum, with the exceptional set enlarged by the Cayley images
  of these points;
* **`RelUnionWordBoundaryOffStatement`** and its proof; `relUnionWordBoundaryStatement_of_off` (the old statement is the
  case `Sb = ∅`);
* `IsRelConfigOff`, **`ae_eqOn_unionMean_of_relConfigOff`**: the probabilistic form (as `BHMean.ae_eqOn_unionMean_of_
  relConfig`).

Deterministic except the last item. Conditional helpers with distinct names; they replace no source theorem. R48: serves
Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Supp8.Q3Rel

open BHMean (jointInv jointFwd jointLift jointChart IsSideWord IsFlowedWord RelTransition)
open RelTrans (nhdsWithin_H_neBot_of_mem_Hbar ofReal_mem_Hbar transBdry liftDiff)
open WangWu (chartAL chartAR)
open Theorem14.SB.SewGerm (HasUnionWordBoundary)

/-! ### The single-lift argument at good points -/

section Integer

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The local integer around a good point landing off `cl A`**. -/
theorem exists_int_nhds (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {s : ℝ} (hs : IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A) :
    ∃ n : ℤ, ∃ ε > 0, ∀ s' : ℝ, dist s' s < ε →
      (IsGoodPt Sb Wr u (s' : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s' : ℂ) ∉ closure A) ∧
      Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s' : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_land hΨ hWr hWr0 hηr hu hs.1 hs.2
  obtain ⟨n, ε, hε, hεr, hlim⟩ := exists_int_jointChart hΨ hw hw0 hη ht hWr hWr0 hu hK hd hr
    (hland_of_ball hΨ hw ht hWr hWr0 hηr hu hK hd hball)
  refine ⟨n, ε, hε, fun s' hs' => ?_⟩
  have hmem : (s' : ℂ) ∈ ball (s : ℂ) ε := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq]; exact hs'
  exact ⟨hball _ (ball_subset_ball hεr hmem) (by simp), hlim _ hmem (by simp)⟩

/-- The good points of `U` where the argument difference tends to `0` form an open set. -/
theorem isOpen_liftZero (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    IsOpen {s : ℝ | (IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A) ∧
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

/-- The good points of `U` where the argument difference does not tend to `0` form an open set. -/
theorem isOpen_liftNeZero (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) :
    IsOpen {s : ℝ | (IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A) ∧
      ¬ Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0)} := by
  rw [Metric.isOpen_iff]
  rintro s ⟨hs, hlim0⟩
  obtain ⟨n, ε, hε, hn⟩ := exists_int_nhds hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hs
  have hn0 : (2 * Real.pi * n : ℝ) ≠ 0 := fun h => hlim0 (h ▸ (hn s (by simpa using hε)).2)
  refine ⟨ε, hε, fun s' hs' => ⟨(hn s' hs').1, fun h => hn0 ?_⟩⟩
  have := nhdsWithin_H_neBot_of_mem_Hbar (ofReal_mem_Hbar s')
  exact tendsto_nhds_unique (hn s' hs').2 h

/-- **The relative hull image lies in `U`**: its points are good and the joint parametrization lands on `cl K_t`, which
misses `cl A`. -/
theorem landOff_of_mem_Icc (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 < u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u))
    (hlt : chartAL Wr u < chartAR Wr u) {s : ℝ} (hs : s ∈ Icc (chartAL Wr u) (chartAR Wr u)) :
    IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A := by
  have hsK := RelTrans.Icc_subset_hullImage hηr hWr hWr0 hu hlt hs
  exact ⟨goodPt_of_mem_closure hSbK hsK, Set.disjoint_left.1 hd
    (extendFrom_jointInv_mem_closure hΨ hw ht hWr hWr0 hηr hu.le hK hd hSbK (ofReal_mem_Hbar s) hsK)⟩

/-- **The integer lift is `0` on the relative hull image** (the single-lift argument). -/
theorem tendsto_liftDiff_zero_of_mem_Icc (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 < u) (hK : Ψ '' fwdHull w t = fwdHull Wr u)
    (hd : Disjoint (closure (fwdHull w t)) (closure A)) (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u))
    (hlt : chartAL Wr u < chartAR Wr u) {x : ℝ} (hx : x ∈ Icc (chartAL Wr u) (chartAR Wr u)) :
    Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  set U : Set ℝ := {s : ℝ | IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A}
    with hUdef
  have hIU : Icc (chartAL Wr u) (chartAR Wr u) ⊆ U := fun s hs =>
    landOff_of_mem_Icc hΨ hw ht hWr hWr0 hηr hu hK hd hSbK hlt hs
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
    have hy := RelTrans.extendFrom_notMem_closure_of_chartAR_lt hηr hWr hWr0 hu.le (x := x') (by linarith)
    obtain ⟨hpim, hpK⟩ := landing_real_of_notMem hΨ hw ht hWr hWr0 hηr hu.le hK hd hx'U.1 hy hx'U.2
    -- the explored hull is nonempty (its image is the relative hull at `u > 0`), so `t > 0` and `0 ∈ cl K_t`
    have ht0 : 0 < t := by
      rcases ht.eq_or_lt with h0 | h0
      · exfalso
        obtain ⟨y, hy'⟩ := QuantumZipper.CaraR.fwdHull_nonempty hWr hWr0 hu
        rw [← hK, ← h0, QuantumZipper.RS.fwdHull_zero_eq_empty hw, image_empty] at hy'
        exact hy'
      · exact h0
    have hp0 : extendFrom H (jointInv Ψi Wr u) (x' : ℂ) ≠ 0 := fun h0 =>
      hpK (h0 ▸ ConformalImageFull.zero_mem_closure_fwdHull hw hw0 ht0)
    exact tendsto_lift_sub_zero_of_untouched hΨ hw hw0 ht hWr hWr0 hηr hu.le hK hd hy
      (tendsto_jointInv hΨ hWr hWr0 hηr hu.le (ofReal_mem_Hbar x') hx'U.1).1 hpim hx'U.2 hpK hp0
  have hsub := (isPreconnected_Icc (a := chartAL Wr u) (b := x')).subset_left_of_subset_union
    (isOpen_liftZero hΨ hw hw0 hη ht hWr hWr0 hηr hu.le hK hd)
    (isOpen_liftNeZero hΨ hw hw0 hη ht hWr hWr0 hηr hu.le hK hd)
    (Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2)
    (fun s hs => (em (Tendsto (liftDiff Ψ Ψi LΨ w Wr t u) (𝓝[H] (s : ℂ)) (𝓝 0))).imp
      (fun h => ⟨hS hs, h⟩) (fun h => ⟨hS hs, h⟩))
    ⟨x', ⟨by linarith, le_rfl⟩, hx'U, hx'0⟩
  exact (hsub ⟨hx.1, hx.2.trans (by linarith)⟩).2

end Integer

/-! ### The transition facts -/

section Assembly

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The transition facts of the relative configuration** (`BHMean.RelTransition`) for a retained chart landing off
`Sb`, the exceptional points lying off the closed relative hull. -/
theorem relTransition_of_setting (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u))
    (htip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)) :
    RelTransition Ψ Ψi LΨ w Wr t u := by
  refine ⟨transBdry Ψi w Wr t u, ?_, fun x hx0 hxK => ?_⟩
  · rintro x₁ ⟨hx₁0, hx₁K⟩ x₂ ⟨-, hx₂K⟩ he
    obtain ⟨hu', hlt, hx₁I⟩ := RelTrans.pos_and_lt_of_mem_hullImage hWr hWr0 hηr hu hx₁0 hx₁K
    have hx₂I := RelTrans.hullImage_subset_Icc hηr hWr hWr0 hu hx₂K
    exact (strictMonoOn_transBdry hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd fun s hs =>
      landOff_of_mem_Icc hΨ hw ht hWr hWr0 hηr hu' hK hd hSbK hlt hs).injOn hx₁I hx₂I he
  · obtain ⟨hu', hlt, hxI⟩ := RelTrans.pos_and_lt_of_mem_hullImage hWr hWr0 hηr hu hx0 hxK
    have hIU : ∀ s ∈ Icc (chartAL Wr u) (chartAR Wr u),
        IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A :=
      fun s hs => landOff_of_mem_Icc hΨ hw ht hWr hWr0 hηr hu' hK hd hSbK hlt hs
    have hmono := strictMonoOn_transBdry hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hIU
    have h0I : (0 : ℝ) ∈ Icc (chartAL Wr u) (chartAR Wr u) :=
      ⟨WangWu.chartAL_nonpos hWr hu, WangWu.chartAR_nonneg hWr hu⟩
    have hT0 : transBdry Ψi w Wr t u 0 = 0 := RelTrans.transBdry_zero htip
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
      (z := (x : ℂ)) (by simp) (hIU x hxI).1 (hIU x hxI).2
    have hφ : extendFrom H (fun y => fwdMap w t (jointInv Ψi Wr u y)) (x : ℂ) = v :=
      extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar x) hTl
    have hvT : v = ((transBdry Ψi w Wr t u x : ℝ) : ℂ) := by
      simp only [transBdry, hφ]
      exact Complex.ext (by simp) (by simp [hv])
    refine ⟨hsign, hTne, ?_, ?_, ?_⟩
    · rw [← hvT, hFv]
      exact extendFrom_jointInv_mem_closure hΨ hw ht hWr hWr0 hηr hu hK hd hSbK (ofReal_mem_Hbar x) hxK
    · rw [← hvT]
      exact hTl
    · exact tendsto_liftDiff_zero_of_mem_Icc hΨ hw hw0 hη ht hWr hWr0 hηr hu' hK hd hSbK hlt hxI

/-- **The real points of the joint chart landing at exceptional points are finitely many**: a landing point off the
closed relative hull determines its real point (`BHMean.eq_fwdMap_of_extendFrom_notMem_closure`). -/
theorem finite_badPts (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u)) :
    {x : ℝ | ∃ b ∈ Sb, extendFrom H (fwdMapInv Wr u) (x : ℂ) = (b : ℂ)}.Finite := by
  refine ((Sb.finite_toSet).union ((Sb.finite_toSet).image fun s : ℝ => (fwdMap Wr u (s : ℂ)).re)).subset ?_
  rintro x ⟨b, hb, hxb⟩
  rcases hu.eq_or_lt with rfl | hpos
  · left
    rw [BHMean.extendFrom_fwdMapInv_zero hWr hWr0 (ofReal_mem_Hbar x)] at hxb
    have : x = b := by exact_mod_cast hxb
    rw [this]
    exact hb
  · right
    have hbK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u) := by rw [hxb]; exact hSbK b hb
    have hre : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re = b := by rw [hxb]; simp
    have hb0 : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ≠ 0 := by
      rw [hre]
      intro h0
      apply hSbK b hb
      rw [h0]
      exact_mod_cast ConformalImageFull.zero_mem_closure_fwdHull hWr hWr0 hpos
    have hx := BHMean.eq_fwdMap_of_extendFrom_notMem_closure hηr hWr hWr0 hu hbK hb0
    rw [hre] at hx
    exact ⟨b, hb, hx.symm⟩

variable {χ lam : ℝ} {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ} {G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ}

/-- **The union word boundary datum of the relative configuration, from the transition facts**, for a retained chart
landing off `Sb` (the Cayley images of the real points landing at `Sb` join the exceptional set). -/
theorem hasUnionWordBoundary_of_relTransition (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb)
    (hw : Continuous w) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u))
    (hG₀ : IsBoundedHarmonicExtension β₀ S₀ G₀) (hGE : IsBoundedHarmonicExtension βE SE GE)
    (hG : IsBoundedHarmonicExtension βu Su G)
    (hsE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam)
    (hsu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam)
    (hflow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u))
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t))
    (hv : ∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im))
    (hT : RelTransition Ψ Ψi LΨ w Wr t u) :
    HasUnionWordBoundary A (fwdHull w t) u₀ v w₁ w₂ χ βu Su := by
  obtain ⟨T, hTinj, hTx⟩ := hT
  set R' : Set ℝ := {x : ℝ | x ≠ 0 ∧ extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)} with hR'
  set φ : ℝ → ℝ := fun s => (fwdMap Wr u (s : ℂ)).re with hφ
  set Xb : Set ℝ := {x : ℝ | ∃ b ∈ Sb, extendFrom H (fwdMapInv Wr u) (x : ℂ) = (b : ℂ)} with hXb
  set X : Set ℝ := insert 0 ((↑Su : Set ℝ) ∪ φ '' (↑S₀ : Set ℝ) ∪ (R' ∩ T ⁻¹' (↑SE : Set ℝ)) ∪ Xb) with hX
  have hXf : X.Finite := by
    refine Set.Finite.insert _ ((((Su.finite_toSet).union ((S₀.finite_toSet).image φ)).union ?_).union
      (finite_badPts hWr hWr0 hηr hu hSbK))
    refine Set.Finite.of_finite_image ((SE.finite_toSet).subset ?_) (hTinj.mono inter_subset_left)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  set E : Set ℂ := insert (1 : ℂ) ((fun x : ℝ => cayley (x : ℂ)) '' X) with hE
  have hEf : E.Finite := (hXf.image _).insert _
  intro z₀ hz₀
  rw [connectedComponentIn_C hΨ hw ht hWr hWr0 hu hK hd hz₀]
  refine ⟨fun ζ => jointInv Ψi Wr u (cayleyInv ζ), jointFwd Ψ Wr u, G, jointLift Ψ LΨ Wr u, E,
    isConformalBijection_diskInv hΨ hw ht hWr hWr0 hu hK hd, isConformalBijection_jointFwd hΨ hw ht hWr hWr0 hu hK hd,
    hG, continuousOn_jointLift hΨ hw ht hWr hWr0 hu hK hd,
    fun z hz => deriv_jointFwd hΨ hw ht hWr hWr0 hu hK hd hz, hEf, fun z _ => hv z, ?_⟩
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h => hqE (h ▸ mem_insert _ _)
  obtain ⟨hre, hcay⟩ := BHMean.tendsto_cayleyInv_sphere hq hq1
  set x : ℝ := (cayleyInv q).re with hxdef
  have hxX : x ∉ X := fun hx => hqE (mem_insert_of_mem _ ⟨x, hx, by
    simp only
    rw [← hre, QuantumZipper.CA.cayley_cayleyInv hq1]⟩)
  have hx0 : x ≠ 0 := fun h => hxX (h ▸ mem_insert _ _)
  have hxS : x ∉ Su := fun h => hxX (mem_insert_of_mem _ (Or.inl (Or.inl (Or.inl h))))
  have hxb : x ∉ Xb := fun h => hxX (mem_insert_of_mem _ (Or.inr h))
  by_cases hxK : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∈ closure (fwdHull Wr u)
  · -- the explored side
    obtain ⟨hsign, hT0, hTK, hTl, hLl⟩ := hTx x hx0 hxK
    have hTS : T x ∉ SE := fun h => hxX (mem_insert_of_mem _ (Or.inl (Or.inr ⟨⟨hx0, hxK⟩, h⟩)))
    obtain ⟨p, hp, hpK, hr, hlim⟩ := explored_side hΨ hw ht hWr hWr0 hηr hu hK hd hSbK hGE hG hsE hsu hw₂ hx0 hxK
      hxS hTS hsign hT0 hTK hTl hLl
    exact Or.inr ⟨p, hp.comp hcay, hpK, hr, hlim.comp hcay⟩
  · -- the retained side
    have hyim := BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hxK
    have hyr : extendFrom H (fwdMapInv Wr u) (x : ℂ) = ((extendFrom H (fwdMapInv Wr u) (x : ℂ)).re : ℂ) :=
      Complex.ext (by simp) (by simp [hyim])
    have hyS : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ S₀ := by
      intro hS
      have hre0 : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ≠ 0 := by
        intro h0
        have hy0 : extendFrom H (fwdMapInv Wr u) (x : ℂ) = 0 := Complex.ext h0 hyim
        rcases hu.eq_or_lt with rfl | hpos
        · rw [BHMean.extendFrom_fwdMapInv_zero hWr hWr0 (show (0 : ℝ) ≤ (x : ℂ).im by simp)] at hy0
          exact hx0 (by exact_mod_cast hy0)
        · exact hxK (hy0 ▸ ConformalImageFull.zero_mem_closure_fwdHull hWr hWr0 hpos)
      have hxφ := BHMean.eq_fwdMap_of_extendFrom_notMem_closure hηr hWr hWr0 hu hxK hre0
      exact hxX (mem_insert_of_mem _ (Or.inl (Or.inl (Or.inr ⟨_, hS, hxφ.symm⟩))))
    have hyb : (extendFrom H (fwdMapInv Wr u) (x : ℂ)).re ∉ Sb := fun hb => hxb ⟨_, hb, hyr⟩
    obtain ⟨p, hp, hpA, hr, hlim⟩ := retained_side hΨ hw ht hWr hWr0 hηr hu hK hd hG₀ hG hflow hw₁ hxS hxK hyS
      hyb
    exact Or.inl ⟨p, hp.comp hcay, hpA, hr, hlim.comp hcay⟩

end Assembly

/-! ### The statement -/

/-- **The boundary-hitting mean identification for relative explorations, with a retained chart landing off a finite
set** (`BHMean.RelUnionWordBoundaryStatement` with `IsRetainedChartOff A Ψ Ψi LΨ Sb` in place of
`IsRetainedChart A Ψ Ψi LΨ`, and the exceptional points off the closed relative hull). -/
def RelUnionWordBoundaryOffStatement : Prop :=
  ∀ (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (Sb : Finset ℝ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ) (t u χ lam : ℝ)
    (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ),
    IsRetainedChartOff A Ψ Ψi LΨ Sb →
    Continuous w → w 0 = 0 → IsLoewnerTrace w η → 0 ≤ t →
    Continuous Wr → Wr 0 = 0 → IsLoewnerTrace Wr ηr → 0 ≤ u →
    Ψ '' fwdHull w t = fwdHull Wr u →
    Disjoint (closure (fwdHull w t)) (closure A) →
    (∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u)) →
    Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0) →
    IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
    IsBoundedHarmonicExtension βu Su G →
    IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam →
    IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam →
    IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u) →
    EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A) →
    EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im) (H \ fwdHull w t) →
    (∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im)) →
    HasUnionWordBoundary A (fwdHull w t) u₀ v w₁ w₂ χ βu Su

/-- **`RelUnionWordBoundaryOffStatement` PROVED.** -/
theorem relUnionWordBoundaryOffStatement : RelUnionWordBoundaryOffStatement := by
  intro A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G u₀ w₁ w₂ v hΨ hw hw0 hη ht hWr hWr0 hηr hu hK
    hd hSbK htip hG₀ hGE hG hsE hsu hflow hw₁ hw₂ hv
  exact hasUnionWordBoundary_of_relTransition hΨ hw ht hWr hWr0 hηr hu hK hd hSbK hG₀ hGE hG hsE hsu hflow hw₁ hw₂
    hv (relTransition_of_setting hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hSbK htip)

/-- The landed statement is the case `Sb = ∅` (a second proof of `RelTrans.relUnionWordBoundaryStatement`). -/
theorem relUnionWordBoundaryStatement_of_off (h : RelUnionWordBoundaryOffStatement) :
    BHMean.RelUnionWordBoundaryStatement := by
  intro A Ψ Ψi LΨ w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G u₀ w₁ w₂ v hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd
    htip hG₀ hGE hG hsE hsu hflow hw₁ hw₂ hv
  exact h A Ψ Ψi LΨ ∅ w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G u₀ w₁ w₂ v hΨ.off hw hw0 hη ht hWr hWr0 hηr hu
    hK hd (fun b hb => absurd hb (Finset.notMem_empty b)) htip hG₀ hGE hG hsE hsu hflow hw₁ hw₂ hv

/-! ### The probabilistic form -/

open LocalSets

/-- **The deterministic relative configuration with a retained chart landing off `Sb`**, bundled
(`BHMean.IsRelConfig` with `IsRetainedChartOff` and the exceptional points off the closed relative hull). -/
structure IsRelConfigOff (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (Sb : Finset ℝ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ)
    (t u χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ) : Prop where
  chart : IsRetainedChartOff A Ψ Ψi LΨ Sb
  hw : Continuous w
  hw0 : w 0 = 0
  hη : IsLoewnerTrace w η
  ht : 0 ≤ t
  hWr : Continuous Wr
  hWr0 : Wr 0 = 0
  hηr : IsLoewnerTrace Wr ηr
  hu : 0 ≤ u
  hull : Ψ '' fwdHull w t = fwdHull Wr u
  disj : Disjoint (closure (fwdHull w t)) (closure A)
  bad : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u)
  tip : Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0)
  bhe₀ : IsBoundedHarmonicExtension β₀ S₀ G₀
  bheE : IsBoundedHarmonicExtension βE SE GE
  bheu : IsBoundedHarmonicExtension βu Su G
  sideE : IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam
  sideu : IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam
  flow : IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u)
  cand : ∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im)

theorem IsRelConfigOff.hasUnionWordBoundary {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ}
    {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u χ lam : ℝ} {β₀ βE βu : ℝ → ℝ} {S₀ SE Su : Finset ℝ}
    {G₀ GE G v : ℂ → ℝ} (hc : IsRelConfigOff A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G v)
    {u₀ w₁ w₂ : ℂ → ℝ}
    (hw₁ : EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A))
    (hw₂ : EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im)
      (H \ fwdHull w t)) :
    HasUnionWordBoundary A (fwdHull w t) u₀ v w₁ w₂ χ βu Su :=
  relUnionWordBoundaryOffStatement A Ψ Ψi LΨ Sb w Wr η ηr t u χ lam β₀ βE βu S₀ SE Su G₀ GE G u₀ w₁ w₂ v hc.chart
    hc.hw hc.hw0 hc.hη hc.ht hc.hWr hc.hWr0 hc.hηr hc.hu hc.hull hc.disj hc.bad hc.tip hc.bhe₀ hc.bheE hc.bheu
    hc.sideE hc.sideu hc.flow hw₁ hw₂ hc.cand

/-- **The conditional mean of the union of a retained set and an explored hull, for retained charts landing off a
finite set** (`BHMean.ae_eqOn_unionMean_of_relConfig` with `IsRelConfigOff`; same proof:
`SB.SewGerm.ae_survivingWordBoundary_union` and `SB.SewGerm.ae_eqOn_physicalMean_of_boundary`). -/
theorem ae_eqOn_unionMean_of_relConfigOff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M)
    {A : Ω → Set ℂ} {Ψ Ψi LΨ : Ω → ℂ → ℂ} {Sb : Ω → Finset ℝ} {w Wr : Ω → ℝ → ℝ} {η ηr : Ω → ℝ → ℂ}
    {t u : Ω → ℝ} {χ lam : ℝ}
    {β₀ βE βu : Ω → ℝ → ℝ} {S₀ SE Su : Ω → Finset ℝ} {G₀ GE G v : Ω → ℂ → ℝ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hKm : Measurable[mΩ, hittingSigma] fun ω => fwdHull (w ω) (t ω))
    (hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    (hlA : IsLocalSet A (WholeField.centredField h u₀) P)
    (hlK : IsLocalSet (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hlU : IsLocalSet (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P)
    (hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z))
    (hunbK : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fwdHull (w ω) (t ω)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fwdHull (w ω) (t ω))) z))
    {g g₁ g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (fun ω => A ω ∪ fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g)
    (hg₁ : IsLocalSetMean A (WholeField.centredField h u₀) P g₁)
    (hg₂ : IsLocalSetMean (fun ω => fwdHull (w ω) (t ω)) (WholeField.centredField h u₀) P g₂)
    {D : Set Ω}
    (hcfg : ∀ᵐ ω ∂P, ω ∈ D → IsRelConfigOff (A ω) (Ψ ω) (Ψi ω) (LΨ ω) (Sb ω) (w ω) (Wr ω) (η ω) (ηr ω) (t ω)
      (u ω) χ lam (β₀ ω) (βE ω) (βu ω) (S₀ ω) (SE ω) (Su ω) (G₀ ω) (GE ω) (G ω) (v ω))
    (hind₁ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ ω (Ψ ω z) - χ * (LΨ ω z).im) (H \ A ω))
    (hind₂ : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      EqOn (fun z => w₂ z + u₀ z) (fun z => GE ω (fwdMap (w ω) (t ω) z) - χ * (logDerivFwd (w ω) (t ω) z).im)
        (H \ fwdHull (w ω) (t ω))) :
    ∀ᵐ ω ∂P, ω ∈ D → ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ fwdHull (w ω) (t ω))) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ fwdHull (w ω) (t ω)) →
        g ω φ = ∫ z, wU z * φ z) →
      EqOn (fun z => wU z + u₀ z) (v ω) (H \ (A ω ∪ fwdHull (w ω) (t ω))) := by
  have hword : ∀ᵐ ω ∂P, ω ∈ D → ∀ w₁ w₂ : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
      InnerProductSpace.HarmonicOnNhd w₂ (H \ fwdHull (w ω) (t ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fwdHull (w ω) (t ω) → g₂ ω φ = ∫ z, w₂ z * φ z) →
      HasUnionWordBoundary (A ω) (fwdHull (w ω) (t ω)) u₀ (v ω) w₁ w₂ χ (βu ω) (Su ω) := by
    filter_upwards [hcfg, hind₁, hind₂] with ω hc h1 h2 hωD w₁ w₂ hw₁ hr₁ hw₂ hr₂
    exact (hc hωD).hasUnionWordBoundary (h1 hωD w₁ hw₁ hr₁) (h2 hωD w₂ hw₂ hr₂)
  have hsurv := Theorem14.SB.SewGerm.ae_survivingWordBoundary_union hh0 hAm hKm hdA hlA hlK hunbA hunbK hg hg₁ hg₂
    u₀ v χ βu Su hword
  exact Theorem14.SB.SewGerm.ae_eqOn_physicalMean_of_boundary hh0 hu₀ hu₀b (measurable_union_hitting hAm hKm) hlU
    hg χ hsurv

end InteractingSLE.Supp8.Q3Rel
