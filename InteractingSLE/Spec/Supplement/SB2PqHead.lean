/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YiCap
import InteractingSLE.Spec.Supplement.SB2MkFib

/-!
# The post-head chart's boundary map: continuity, bounded distance, finite fibres

Packet PROVE-GW2-NOTHR (round 8, decision D67 (3): D66's (P), the root pull-back). For a launch of the boundary walk at
stage `n` and an own time `τ < ζ_n`, the walk capped at `τ` (`WalkSide.capSpec`) has, after its last instruction,
B's **post-head chart** `(stage chart).loewner (headDrv e τ) (headTime e τ)` (`WalkSide.chart_run_capSpec_succ`):

* **`pinv_capSucc`**: the capped prefix `P_n ∪ gc(α[0, τ])` with the bridge at `0` is a finite-fibre prefix path
  (`LuM.pinv_prefix_walk` at `n`, joined with the head path, as in its piece step with `T := τ`);
* **`postHead_chart_facts`**: the post-head chart is a domain chart of `ℍ ∖ fill (P_n ∪ head)` whose inverse has a
  boundary map continuous on `ℍ̄`, within bounded distance of the identity, with finite fibres on `ℍ̄`
  (`S3.Canon.runChart_package` for the capped program, `Lk.finite_fibre_of_pinv`).

Deterministic; the walk inputs (`RegLaunches`, injective traces, GW1's tip coordinates) hold almost surely
(`LuM.ae_injOn_trOf_walk`, `Ml.ae_walkTipCoordinates_amb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Pq

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide GW1Bookkeep Lk LuM Lx Sx

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ}

/-- **The capped prefix is a finite-fibre prefix path**: `P_n ∪ gc(α[0, τ])` with the bridge `{0}` satisfies
`PInv 0`. -/
theorem pinv_capSucc {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hinj : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      InjOn (trOf (D j)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2})
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c₀ : Chart}
    {θ' : ℝ} (hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c₀, θ'))
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < (D n).2) :
    PInv 0 (SB.prefixPhysSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) n θ τ) D (n + 1) ∪
      ((↑) : ℝ → ℂ) '' Icc 0 0) := by
  set w := boundaryWalkSpec b jumps θ true with hw
  set A := SB.prefixPhysSet κ b jumps w D n with hAdef
  set U := ((↑) : ℝ → ℂ) '' Icc (0 : ℝ) 0 with hU
  have hl : (ExplState.run κ b jumps w D (n + 1)).2.2.2.1 n ≠ none := by rw [hl']; simp
  have hnd : stStatus (ExplState.run κ b jumps w D n) ≠ GW1Conn.stDone :=
    WalkIntRunChron.not_done_of_launch w D hl'
  obtain ⟨ih, ihpt⟩ := pinv_prefix_walk hP hinj htip le_rfl n hnd
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hcc := isConformal_runChart_of_reg w hP n
  have hcb := (GW1P.isClosed_pieces_run w D hP n).1
  obtain ⟨g, hgc, hgi, hgb, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hfib := finite_fibre_bdry_walk hP hnd ih hgc hgi hgb
  have hc₀ : c₀ = stChart (ExplState.run κ b jumps w D n) := (eq_launch_of_launches w D hl').2.2
  have hgi' : EqOn g c₀.2.1 H := by rw [hc₀]; exact hgi
  have hpre := S3.Asm.prefixPhysSet_capSpec_succ hl' hgc hgi' hα hPR.1 hPR.2.1 hτ
  have hst : statePhysicalSet 0 (ExplState.run κ b jumps w D n) = A := by
    simp only [hAdef, SB.prefixPhysSet, statePhysicalSet, hw, boundaryWalkSpec]
  rw [hpre, hst]
  have hαH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) s).im := fun s hs =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 hs
  have hsζ : ∀ s : ℝ≥0, s ≤ τ → (s : ℝ≥0∞) ≤ (D n).2 := fun s hs => (ENNReal.coe_le_coe.2 hs).trans hτ.le
  -- the seed of the head is the current point
  have htip0 : g (trOf (D n) 0) = stPt (ExplState.run κ b jumps w D n) := by
    rw [← bdVal_eq_of_tendsto (hαH 0 (by simp)) (hgt _ (hαH 0 (by simp)))]
    exact (bdVal_tip_walk hP htip hl).1
  have e : A ∪ g '' (trOf (D n) '' Icc 0 τ) ∪ U = (A ∪ U) ∪ g '' (trOf (D n) '' Icc 0 τ) := by
    ext z; simp only [mem_union]; tauto
  rw [e]
  rcases eq_or_ne τ 0 with hτ0 | hτ0
  · refine ih.union_of_subset ?_
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    rw [hτ0] at hs
    rw [le_antisymm hs.2 hs.1, htip0]
    exact Or.inl ihpt
  · set φ : ℝ≥0 → ℂ := fun s => g (trOf (D n) s) with hφ
    have hcont : ContinuousOn φ (Iic τ) := by
      refine hgc.comp (hα.2.1.mono fun s hs => hsζ s hs) fun s hs => ?_
      exact hαH s (hsζ s hs)
    have hf : ∀ z, {s | s ≤ τ ∧ φ s = z}.Finite := by
      intro z
      refine Finite.of_finite_image ((hfib z).subset ?_) ((hinj n hl).mono fun s hs => hsζ s hs.1)
      rintro _ ⟨s, ⟨hs, hsz⟩, rfl⟩
      exact ⟨hsz, hαH s (hsζ s hs)⟩
    have hH : ∀ s ≤ τ, 0 ≤ (φ s).im := fun s hs =>
      GW1P.mem_Hbar_of_tendsto (hαH s (hsζ s hs)) hcc.2.1 (hgt _ (hαH s (hsζ s hs)))
    obtain ⟨hq, hqi⟩ := isFFPath_reparam (pos_iff_ne_zero.2 hτ0) hcont hf hH
    have hq0 : (fun t : ℝ => φ (t * τ).toNNReal) 0 ∈ A ∪ U := by
      simp only [zero_mul, Real.toNNReal_zero, hφ]
      rw [htip0]
      exact Or.inl ihpt
    have hj := ih.join hq hq0
    have himg : φ '' Iic τ = g '' (trOf (D n) '' Icc 0 τ) := by
      rw [← image_comp]
      congr 1
      ext s
      simp only [mem_Iic, mem_Icc, zero_le, true_and]
    rwa [hqi, himg] at hj

/-- **The post-head chart's facts**: a domain chart of `ℍ ∖ fill (P_n ∪ head)` whose inverse has a boundary map
continuous on `ℍ̄`, within bounded distance of the identity, with finite fibres. -/
theorem postHead_chart_facts {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hinj : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      InjOn (trOf (D j)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D j).2})
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c₀ : Chart}
    {θ' : ℝ} (hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c₀, θ'))
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < (D n).2) :
    ∃ (X : Set ℂ) (g : ℂ → ℂ) (C : ℝ),
      IsDomainChart (H \ fillH X) ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner
        (headDrv (D n) τ) (headTime (D n) τ)) ∧
      ContinuousOn g Hbar ∧
      EqOn g ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).loewner
        (headDrv (D n) τ) (headTime (D n) τ)).2.1 H ∧
      (∀ q ∈ Hbar, ‖g q - q‖ ≤ C) ∧ ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  have hlne : (ExplState.run κ b jumps w D (n + 1)).2.2.2.1 n ≠ none := by rw [hl']; simp
  obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hlne
  have hℓ : n ≤ w.2.2.length := hlen.le
  have htop : instrTime w n = ⊤ := Lx.instrTime_boundaryWalk_of_launch hl'
  have hwθ : w.2.2[n]? = some (Sum.inl (θ, ⊤)) := by
    rw [hw, GW1Conn.getElem?_boundaryWalkSpec]
    simp [hlen, hev]
  set sc := capSpec w n θ (τ : ℝ≥0∞) with hsc
  -- regularity of the capped program (as in `Sx.cap_chart_facts`)
  have hreg : ∀ k c θ'', (ExplState.run κ b jumps sc D (k + 1)).2.2.2.1 k = some (c, θ'') →
      GW1P.PieceRegular (D k).1 (min (instrTime sc k) (D k).2) := by
    intro k c θ'' hlk
    rcases lt_trichotomy k n with hkn | rfl | hkn
    · rw [run_capSpec_of_le hℓ D (Nat.succ_le_of_lt hkn)] at hlk
      rw [instrTime_capSpec_of_lt hkn hℓ]
      exact hP k c θ'' hlk
    · rw [instrTime_capSpec hℓ]
      have h := hP k c₀ θ' hl'
      rw [htop] at h
      obtain ⟨h0, hc, η, hη, -⟩ := h
      have hle : min (τ : ℝ≥0∞) (D k).2 ≤ min ⊤ (D k).2 := min_le_min_right _ le_top
      refine ⟨h0, hc.mono fun s hs => (show (s : ℝ≥0∞) ≤ _ from hs).trans hle,
        η, BRLeaf.isGeneratingTrace_of_le hη hle, fun htop' => ?_⟩
      exact absurd htop' (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))
    · obtain ⟨hk, -, -⟩ := eq_launch_of_launches sc D hlk
      rw [hsc, capSpec_getElem?_of_gt hkn hℓ] at hk
      cases hk
  have hnot := Mk.stStatus_capSpec_ne_done (κ := κ) (b := b) (jumps := jumps) hℓ hwθ D hlne hτ
  have hchart := chart_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ hwθ D hl' τ
  have hchart' : stChart (ExplState.run κ b jumps sc D (n + 1)) =
      (stChart (ExplState.run κ b jumps w D n)).loewner (headDrv (D n) τ) (headTime (D n) τ) := hchart
  obtain ⟨-, gc, C, hD, -, -, -, hgc, hgi, hgb, -, hC⟩ := S3.Canon.runChart_package sc D hreg (n + 1) hnot
  have hfib := Lk.finite_fibre_of_pinv (pinv_capSucc hP hinj htip hl' hτ) hD hgc hgi hgb
  rw [hchart'] at hD hgi
  exact ⟨_, gc, C, hD, hgc, hgi, hC, hfib⟩

end InteractingSLE.Theorem14.SB.Pq
