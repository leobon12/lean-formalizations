/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJw
import InteractingSLE.Spec.Supplement.SB2WeFinal

/-!
# Reading the junction fact off the walk's invariants

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). At a state of the lower walk with round 2's invariants
(`LWO`) and the junction invariant (`JW`), every chart point `r` right of the entry `m = leftEntry c L` (`L` the
leftmost real point of the prefix with the bridge `[u, 0]`) at which the word continues with the lower-side height
reads back to a real point `p ≥ L` which, right of `u`, is not upper-bad (`junction_of_jw`):

* `r` right of the whole left-ray image: `JW` and `L ≤ stRecL` (`realMin_le_stRecL`);
* otherwise `r = rProf c x₀` for a left-ray point `x₀` (`LLeft.exists_eq`), `x₀ ≥ L` because `r > m` and `m` is the
  left limit of the profile at `L`, `g r = x₀` (free point), and the data right of `x₀` are the lower-side height.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.Staged Exist.StagedLaw Restart GW1W Lv
open PiecewiseConstantBoundaryData (rightLim leftLim)

variable {κ ψ u : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The junction fact at a state of the walk** (from `LWO` and `JW`). -/
theorem junction_of_jw (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθψ : θ < ψ)
    {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hRL : LuM.RegLaunches κ b jumps spec D)
    {n : ℕ} (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone)
    (hc : IsRealChart (stChart (ExplState.run κ b jumps spec D n))) {β : BoundaryWord}
    (hI : LWO κ θ b jumps β (ExplState.run κ b jumps spec D n))
    (hJ : JW κ θ ψ u b β (ExplState.run κ b jumps spec D n)) (hu : u ≤ 0)
    (hAc : IsCompact (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0))
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart (ExplState.run κ b jumps spec D n)).2.1 H) {r : ℝ}
    (hrm : Lx.leftEntry (stChart (ExplState.run κ b jumps spec D n))
      (realMin (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0)) < r)
    (hlow : ∃ ε > 0, ∀ y ∈ Ioo r (r + ε), y ∉ β.jumps → β.fn y = -sleLambda κ - θ * chiC κ) {p : ℝ}
    (hp : g (r : ℂ) = p) :
    realMin (prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0) ≤ p ∧
      (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)) := by
  classical
  set s := ExplState.run κ b jumps spec D n with hsdef
  set c := stChart s with hcdef
  set A := prefixPhysSet κ b jumps spec D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0 with hAdef
  set L := realMin A with hLdef
  set m := Lx.leftEntry c L with hmdef
  obtain ⟨⟨hs, -, -, hC, -, -⟩, ⟨S, Fx, Fy, hSL, -, hSm, hSc, hSo, -, -⟩, hRB⟩ := hI
  have hLr : L ≤ stRecL s := realMin_le_stRecL hu hAc hRB
  -- `m` is the left limit of the profile at `L` (as in `secondClause_of_lwo`)
  have hLA : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y := fun y hy => FinRel.realMin_le_of_mem hAc hy
  have hAf : fillH A = fillH (prefixPhysSet κ b jumps spec D n) := Lw.fillH_union_real _ _
  obtain ⟨M, hK⟩ := Lw.exists_hullModel_fill spec D hRL n hnot
  have hcc := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D n
    fun j _ c θ h => hRL j c θ h).1
  obtain ⟨g₀, hg₀c, hg₀i, -, -⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc
    (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hRL n).1
  have hfree : ∀ x : ℝ, x < L → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) M.hull := fun x hx => by
    obtain ⟨ρ, hρ, hd⟩ := Lw.exists_ball_disjoint_fillH hAc fun y hy => lt_of_lt_of_le hx (hLA y hy)
    rw [hAf, ← hK] at hd
    exact ⟨ρ, hρ, hd⟩
  obtain ⟨he, -, -⟩ := GW1Ext.bdryValue_facts hcc M hg₀c hg₀i hfree
  have hm := Lx.isLeftEntryValue_runChart spec D hRL n hnot hAc hAf hLA
  have hlim : Tendsto (Lx.bdryValue c) (𝓝[<] L) (𝓝 m) := by
    obtain ⟨e, he', hlim⟩ := hm
    refine hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
    have h1 := Lx.tendsto_bdryValue (he' x hx) (by simp)
    rw [h1.1, Complex.ofReal_re]
  have hbv : ∀ x, x < L → Lx.bdryValue c x = rProf c x := fun x hxL => by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 := tendsto_nhds_unique (he x hxL)
      ((hC x (lt_of_lt_of_le hxL hLr)).tendsto.mono_left nhdsWithin_le_nhds)
    rw [hc.eq_ofReal x] at h1
    exact_mod_cast h1
  have hlimr : Tendsto (rProf c) (𝓝[<] L) (𝓝 m) :=
    hlim.congr' (eventually_nhdsWithin_of_forall fun x hx => hbv x hx)
  by_cases hright : ∀ x, x < stRecL s → rProf c x < r
  · obtain ⟨h1, h2⟩ := hJ g hgc hgi r hright hlow p hp
    exact ⟨hLr.trans h1, h2⟩
  push Not at hright
  obtain ⟨x₁, hx₁, hle⟩ := hright
  obtain ⟨x₀, hx₀, -, hx₀e⟩ := LLeft.exists_eq hs hx₁ hle
  have hx₀S : x₀ ∈ S := hSL x₀ hx₀
  have hgx₀ : g (r : ℂ) = x₀ := by
    have h := bdry_eq_of_chartFree hcc hgc hgi (hSc x₀ hx₀S).1 (hSc x₀ hx₀S).2 (hc x₀)
    rwa [hc.eq_ofReal x₀, hx₀e] at h
  have hpx : p = x₀ := by rw [hp] at hgx₀; exact_mod_cast hgx₀
  subst hpx
  refine ⟨?_, fun _ => ?_⟩
  · -- `L ≤ x₀`: otherwise the image would be left of `m`
    by_contra hlt
    push Not at hlt
    obtain ⟨x', hx'1, hx'2⟩ := exists_between hlt
    have h1 : rProf c p < rProf c x' :=
      hs.strictMonoOn (show p ∈ Iio (stRecL s) from hx₀)
        (show x' ∈ Iio (stRecL s) from lt_of_lt_of_le hx'2 hLr) hx'1
    have h2 : rProf c x' ≤ m :=
      ge_of_tendsto hlimr (Filter.mem_of_superset (Ioo_mem_nhdsLT hx'2) fun z hz =>
        (hs.strictMonoOn (show x' ∈ Iio (stRecL s) from lt_of_lt_of_le hx'2 hLr)
          (show z ∈ Iio (stRecL s) from lt_of_lt_of_le hz.2 hLr) hz.1).le)
    rw [hx₀e] at h1
    linarith
  · -- the data right of `x₀` are the lower-side height
    refine cumWeightRight_gt_of_lowSide hκ hκ4 hθψ ?_
    obtain ⟨ε, hε, hεl⟩ := hlow
    have hcont : ContinuousAt (rProf c) p :=
      Complex.continuous_re.continuousAt.comp ((hC p hx₀).comp Complex.continuous_ofReal.continuousAt)
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont ε hε
    set x₂ := p + min δ (stRecL s - p) / 2 with hx₂
    have hm2 : 0 < min δ (stRecL s - p) := lt_min hδ (by linarith)
    have hpx₂ : p < x₂ := by linarith
    have hx₂L : x₂ < stRecL s := by linarith [min_le_right δ (stRecL s - p)]
    set Ex : Set ℝ := {x | x < stRecL s ∧ rProf c x ∈ (β.jumps : Set ℝ)} with hEx
    have hExf : Ex.Finite :=
      Set.Finite.of_finite_image (f := rProf c)
        (β.jumps.finite_toSet.subset (by rintro _ ⟨x, hx, rfl⟩; exact hx.2))
        (hs.strictMonoOn.injOn.mono fun x hx => hx.1)
    refine Sec4.rightLim_eq_of_forall_notMem (jumps ∪ Fx ∪ hExf.toFinset) (a := x₂) hpx₂ fun t ht htJ => ?_
    have htj : t ∉ jumps := fun h => htJ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have htF : t ∉ Fx := fun h => htJ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have htL : t < stRecL s := lt_trans ht.2 hx₂L
    have htβ : rProf c t ∉ β.jumps := fun h =>
      htJ (Finset.mem_union_right _ (hExf.mem_toFinset.2 ⟨htL, h⟩))
    have hty : rProf c t ∈ Ioo r (r + ε) := by
      refine ⟨?_, ?_⟩
      · rw [← hx₀e]; exact hs.strictMonoOn (show p ∈ Iio (stRecL s) from hx₀) (show t ∈ Iio (stRecL s) from htL)
          ht.1
      · have h1 : dist t p < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]
          linarith [ht.2, min_le_left δ (stRecL s - p)]
        have h2 := hδc h1
        rw [Real.dist_eq, hx₀e] at h2
        linarith [(abs_lt.1 h2).2]
    rw [← hSo t (hSL t htL) htj htF htβ]
    exact hεl _ hty htβ

end InteractingSLE.Theorem14.SB.Wf
