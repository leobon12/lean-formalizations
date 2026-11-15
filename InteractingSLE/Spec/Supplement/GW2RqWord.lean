/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqInv
import InteractingSLE.Spec.Supplement.GW2WxMap

/-!
# The optimal shell of a raised stage word along a split-free past (decision D33)

PROVE-GW2-ROOTX round 8. GEOM2's stage word at a root `x` is `upW (θa χ) (stageWord W₀ θ n past)`. Along a past whose
pieces are split-free against SDE's junctions, with both junction regions nonempty:

* `rkR_upW`, `rkL_upW`: raising a word does not change its ranks;
* **`abs_fn_stageWord_le`**: every stage word has heights bounded by `max H₀ (λ + (π/2)χ)` if the root words have
  heights bounded by `H₀` (SDE's side invariant `GW2Sdp.sideInv_stageWord`, the root heights beyond the junctions);
* **`regionFact_upW`**: the raised word has the two angle regions of `GW2RqFar` (bands from the side invariant, the
  pairing and the far counts from `GW2RqInv.StageQ`);
* **`optShell_stageWord`**: the optimal shell of the raised stage word presents it, has separated angles, and has drift
  at most `driftC κ (max H₀ (λ + (π/2)χ) + (π/2)χ) N₀`, a constant of the root word's shape only.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset Filter Topology
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist.Staged Exist.StagedLaw GW2Sdf GW2TipSystem GW2TipSystem.RootH10 GW2TipSystem.RootL6 Sec5
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

theorem rkR_upW (a : ℝ) (c : BoundaryWord) (u : ℝ) : rkR (GW2Rd.upW a c) u = rkR c u := by
  unfold rkR
  rw [GW2Rd.upW_fn, GW2Rd.upW_jumps, GW2Rd.jumpSet_add_const c.isPiecewiseConstantBoundaryData]

theorem rkL_upW (a : ℝ) (c : BoundaryWord) (v : ℝ) : rkL (GW2Rd.upW a c) v = rkL c v := by
  unfold rkL
  rw [GW2Rd.upW_fn, GW2Rd.upW_jumps, GW2Rd.jumpSet_add_const c.isPiecewiseConstantBoundaryData]

/-- A bound off the jumps and finitely many more points is a bound off the jumps. -/
theorem abs_fn_le_of_off {c : BoundaryWord} {F : Finset ℝ} {H : ℝ}
    (h : ∀ z, z ∉ c.jumps → z ∉ F → |c.fn z| ≤ H) (z : ℝ) (hz : z ∉ c.jumps) : |c.fn z| ≤ H := by
  have h1 : ∀ᶠ y in 𝓝[≠] z, c.fn y = c.fn z := by
    filter_upwards [nhdsWithin_le_nhds (BoundaryWord.eventually_index_eq hz)] with y hy
    unfold BoundaryWord.fn
    rw [hy]
  have h2 : ∀ᶠ y in 𝓝[≠] z, y ∉ ((c.jumps ∪ F : Finset ℝ) : Set ℝ) :=
    GW1W.eventually_notMem_of_finite (Finset.finite_toSet _) z
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  rw [Finset.mem_coe, Finset.mem_union, not_or] at hy2
  rw [← hy1]
  exact h y hy2.1 hy2.2

/-- **The heights of every stage word are bounded** by the root bound and the piece-side band. -/
theorem abs_fn_stageWord_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {S : Type*} (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {H₀ : ℝ}
    (h0 : ∀ x z, z ∉ (W₀ x).jumps → |(W₀ x).fn z| ≤ H₀) (n : ℕ) (x : GW2JDetR5.Past S n) (z : ℝ)
    (hz : z ∉ (GW2JDetR5.stageWord (κ := κ) W₀ θ n x).jumps) :
    |(GW2JDetR5.stageWord (κ := κ) W₀ θ n x).fn z| ≤ max H₀ (sleLambda κ + Real.pi / 2 * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hlam := Sec4.sleLambda_pos hκ
  have hS := GW2Sdp.sideInv_stageWord hκ W₀ θ hθ n x
  refine abs_fn_le_of_off (F := {GW2Sdp.junctionL n x, 0, GW2Sdp.junctionR n x}) (fun z hzJ hzF => ?_) z hz
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzF
  obtain ⟨hzL, hz0, hzR⟩ := hzF
  have hband : ∀ α ∈ Icc (-(Real.pi / 2)) (Real.pi / 2), |α * chiC κ| ≤ Real.pi / 2 * chiC κ := fun α hα => by
    rw [abs_mul, abs_of_pos hχ]
    exact mul_le_mul_of_nonneg_right (abs_le.2 hα) hχ.le
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · rcases lt_or_gt_of_ne hzL with hlt | hgt
    · obtain ⟨y, hy0, hyJ, hye⟩ := hS.rootL z hlt hzJ
      rw [← hye]
      exact (h0 _ y hyJ).trans (le_max_left _ _)
    · obtain ⟨α, hα, he⟩ := hS.oldL z hgt hneg hzJ
      rw [← he]
      refine le_trans ?_ (le_max_right _ _)
      have := hband α hα
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2]
  · rcases lt_or_gt_of_ne hzR with hlt | hgt
    · obtain ⟨α, hα, he⟩ := hS.oldR z hpos hlt hzJ
      rw [← he]
      refine le_trans ?_ (le_max_right _ _)
      have := hband α hα
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2]
    · obtain ⟨y, hy0, hyJ, hye⟩ := hS.rootR z hgt hzJ
      rw [← hye]
      exact (h0 _ y hyJ).trans (le_max_left _ _)

/-- **The raised word has the two angle regions.** -/
theorem regionFact_upW {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} {aL aR : ℝ} {HL HR : Set ℝ}
    (hS : GW2Sdp.SideInv κ c aL aR HL HR) {N : ℕ} (hQ : StageQ κ c aL aR N) {H : ℝ}
    (hH : ∀ z, z ∉ c.jumps → |c.fn z| ≤ H) {θa : ℝ} (hθa : θa ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (haL : aL < 0) (haR : 0 < aR) :
    RegionFact κ (GW2Rd.upW (θa * chiC κ) c) θa aL aR (H + Real.pi / 2 * chiC κ) N := by
  have hχ := Sec4.chiC_pos hκ hκ4
  refine ⟨haL, haR, hθa, fun z hz0 hza hzJ => ?_, fun z hza hz0 hzJ => ?_, fun u v hu0 hua huJ hva hv0 hvJ hrk => ?_,
    fun z hzJ => ?_, hQ.farR, hQ.farL⟩
  · obtain ⟨α, hα, he⟩ := hS.oldR z hz0 hza hzJ
    rw [GW2Rd.upW_fn]
    simp only
    rw [← he]
    have e : θa + (sleLambda κ - (sleLambda κ - α * chiC κ + θa * chiC κ)) / chiC κ = α := by
      field_simp; ring
    rw [e]; exact hα
  · obtain ⟨α, hα, he⟩ := hS.oldL z hza hz0 hzJ
    rw [GW2Rd.upW_fn]
    simp only
    rw [← he]
    have e : θa - (sleLambda κ + (-sleLambda κ - α * chiC κ + θa * chiC κ)) / chiC κ = α := by
      field_simp; ring
    rw [e]; exact hα
  · rw [rkR_upW, rkL_upW] at hrk
    rw [GW2Rd.upW_fn]
    have := hQ.pair u v hu0 hua huJ hva hv0 hvJ hrk
    simp only
    linarith
  · rw [GW2Rd.upW_fn]
    simp only
    have h1 := hH z hzJ
    have h2 : |θa * chiC κ| ≤ Real.pi / 2 * chiC κ := by
      rw [abs_mul, abs_of_pos hχ]
      exact mul_le_mul_of_nonneg_right (abs_le.2 hθa) hχ.le
    calc |c.fn z + θa * chiC κ| ≤ |c.fn z| + |θa * chiC κ| := abs_add_le _ _
      _ ≤ H + Real.pi / 2 * chiC κ := add_le_add h1 h2

/-- **The optimal shell of a raised stage word along a split-free past.** -/
theorem optShell_stageWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {S : Type*} (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {H₀ : ℝ}
    (h0 : ∀ x z, z ∉ (W₀ x).jumps → |(W₀ x).fn z| ≤ H₀) {N₀ : ℕ} (hN₀ : ∀ x, (W₀ x).jumps.card ≤ N₀)
    (n : ℕ) (x : GW2JDetR5.Past S n) (hx : SplitFreePast n x) (haL : GW2Sdp.junctionL n x < 0)
    (haR : 0 < GW2Sdp.junctionR n x) {θa : ℝ} (hθa : θa ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {β : BoundaryWord}
    (hβ : β = GW2Rd.upW (θa * chiC κ) (GW2JDetR5.stageWord (κ := κ) W₀ θ n x)) (k : ℕ) (start : ℝ) :
    PresentsO κ β (rootScale k) false (optShell κ β θa k start).xL
      (angleWordL κ (optShell κ β θa k start).φ (optShell κ β θa k start).mL (optShell κ β θa k start).ρL₀)
      (optShell κ β θa k start).xR
      (angleWordR κ (optShell κ β θa k start).φ (optShell κ β θa k start).mR (optShell κ β θa k start).ρR₀) ∧
    (∀ i, (optShell κ β θa k start).φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
    Prop59Stage.stageDriftBound κ (optShell κ β θa k start).ρL₀ (optShell κ β θa k start).ρR₀ ≤
      driftC κ (max H₀ (sleLambda κ + Real.pi / 2 * chiC κ) + Real.pi / 2 * chiC κ) N₀ := by
  have hS := GW2Sdp.sideInv_stageWord hκ W₀ θ hθ n x
  have hQ := stageQ_stageWord hκ W₀ θ hN₀ n x hx
  have hR := regionFact_upW hκ hκ4 hS hQ (abs_fn_stageWord_le hκ hκ4 W₀ θ hθ h0 n x) hθa haL haR
  rw [← hβ] at hR
  exact optShell_of_region hκ hκ4 hR k start

end InteractingSLE.Theorem14.GW2Rq
