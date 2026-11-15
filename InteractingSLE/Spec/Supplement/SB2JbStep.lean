/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JbCanon
import InteractingSLE.Spec.Supplement.SB2JaFin
import InteractingSLE.Spec.Supplement.SB2JdChart

/-!
# SB2(2)'s joint stage induction: one finite lockstep stage at walk level

Packet PROVE-SB2-LIFTSET (round 20).

* **`relChart_facts_of_lt`**: the relative run chart at stage `n` is a normalized conformal domain chart of the
  complement of its prefix's fill, with boundary limits, once the pieces launched before `n` are regular
  (`truncDrv`; `Lw.isDomainChart_runChart`, `WalkIntCanon.isNormalized_runChart`, `runChart_facts_of_lt`);
* **`stageFin_walk`**: at an actual stage `n` that starts at an old point (`R` explored) with a finite positive piece,
  given the upper chart's facts, the tail lift, the density of good times, the relative chart's facts with the fill
  identity, the lifted seed (where the relative chart is continuous from `ℍ` and reads `0`) and EL's generation, the
  run-chart stage curve is driven and `StageRelFinP` holds. Inputs: `canon_old_fin` (F2a with its lift),
  `goodTp_eq_canonGood_old` (the good-set matching), `phys_facts_of_fill` (the physical domain identity); conclusion
  by `stage_fin_of_canon`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The relative run chart's facts at `n` from the regularity of the pieces launched before `n`.** -/
theorem relChart_facts_of_lt {θ : ℝ} {D : ℕ → Drv} {n : ℕ}
    (hreg : ∀ k < n, ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2))
    (hnd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ GW1Conn.stDone) :
    IsDomainChart (H \ fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
        (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      WalkIntCanon.IsNormalized (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      HasBdryLimits (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 ∧
      ContinuousOn (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 H ∧
      (∀ w ∈ H, (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1
        ((stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 w) = w) ∧
      ∀ y ∈ H, (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1 y ∈ H := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have hP : RegLaunches κ b jumps spec (truncDrv D n) := by
    intro k c θ' hl
    by_cases hk : k < n
    · rw [run_truncDrv spec D (show k + 1 ≤ n by omega)] at hl
      have h := hreg k hk c θ' hl
      unfold truncDrv; simp only [hk, ↓reduceIte]; exact h
    · unfold truncDrv; simp only [hk, ↓reduceIte]
      exact LuM.pieceRegular_zeroDrv0 _
  have hrun := run_truncDrv (κ := κ) (b := b) (jumps := jumps) spec D (le_refl n)
  have hpre : SB.prefixPhysSet κ b jumps spec (truncDrv D n) n = SB.prefixPhysSet κ b jumps spec D n := by
    unfold SB.prefixPhysSet; rw [hrun]
  have hnd' : stStatus (ExplState.run κ b jumps spec (truncDrv D n) n) ≠ GW1Conn.stDone := by rw [hrun]; exact hnd
  have hdom := Lw.isDomainChart_runChart spec (truncDrv D n) (fun k c θ' hl => hP k c θ' hl) n hnd'
  rw [hrun, hpre] at hdom
  have hN : WalkIntCanon.IsNormalized (stChart (ExplState.run κ b jumps spec D n)) :=
    WalkIntCanon.isNormalized_runChart spec D n fun j hj c θ' hl => hreg j hj c θ' hl
  obtain ⟨hcc, hfib⟩ := runChart_facts_of_lt spec (D := D) (n := n) hreg
  obtain ⟨f, -, hf, -, -⟩ := hfib
  refine ⟨hdom, hN, fun x hx => ⟨f x, hf x hx⟩, hcc.1.continuousOn, hcc.2.2, hcc.2.1⟩

/-- **One finite lockstep stage at walk level**: driven and `StageRelFinP`. -/
theorem stageFin_walk {θ : ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) (hfin : (D n).2 ≠ ⊤)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hR : (realMax (pA '' Icc 0 1) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {c : Chart} (hc : IsDomainChart (H \ fillH (pA '' Icc 0 1)) c) (hcN : WalkIntCanon.IsNormalized c)
    {ĝ : ℂ → ℂ} (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcH' : ∀ w ∈ H, c.2.1 w ∈ H)
    (hoff : BdryOff c) (hDom : c.2.1 '' H = H \ fillH (pA '' Icc 0 1))
    {m : ℝ} {tL : ℝ≥0} {γ : ℝ≥0 → ℂ} (hγ : IsTailLiftCurve c (realMax (pA '' Icc 0 1)) m β tL γ)
    (hhead : β '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1))
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)))
    {s₂ : ExplState} {e₂ : Drv} {P₂ : Set ℂ}
    (h₁ : IsDomainChart (H \ fillH P₂) (stChart s₂)) (hc₁N : WalkIntCanon.IsNormalized (stChart s₂))
    (hfill : fillH P₂ = fillH (liftImage β tL γ (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)))
    (hB₂ : HasBdryLimits (stChart s₂).2.1) (hcH₂ : ContinuousOn (stChart s₂).2.1 H)
    (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H)
    {w₀ : ℂ}
    (hw₀ : ∀ s, β (tL + s) = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ) →
      γ s = w₀)
    (hcw₀ : ContinuousWithinAt (stChart s₂).1 H w₀) (hz₀ : (stChart s₂).1 w₀ = 0)
    (he₂ : e₂.2 = capLife (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (D n).2 s₂))
    (hgen : ∀ T < capLife (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂),
      IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m
        (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 s₂)))
    (hreg : IsRegularDriver e₂) :
    IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂) ∧
      StageRelFinP c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 s₂ e₂ := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set q := pcPt s (D n) with hqdef
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
  -- the good-set matching and F2a with its lift
  have hgood := goodTp_eq_canonGood_old hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR hDom
  have hgdp : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆ closure (goodTp c q (D n).2) := hgd
  have hden : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (D n).2 → t ∈ closure {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 ∧
      q t' ∈ H \ fillH A} := fun t ht => by
    have h := hgdp ht
    have he : goodTp c q (D n).2 = {t' : ℝ≥0 | (t' : ℝ≥0∞) ≤ (D n).2 ∧ q t' ∈ H \ fillH A} := by
      ext t'; simp only [goodTp, hDom, mem_ofPred_eq]
    rwa [he] at h
  obtain ⟨e, ζ, hζc, hζH, hF, hcv⟩ := canon_old_fin hP hW hlm hlh hl hpos hfin hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR
    hden
  -- the cut, the hull of `A ∪ prefix` and the physical domain identity
  obtain ⟨σ, hσ, hPσ, hTσ, hle⟩ := old_cut hP hW hlm hlh hl hpos hpinv hAc hβ hβ0 hβr hR
  obtain ⟨-, -, -, hA, -⟩ := cut_package hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle
  have hPσ' : Pn = β '' Icc 0 σ := hPσ
  have hX : IsHPHull (fillH (A ∪ Pn)) := by rw [hPσ']; exact hA
  have hB : IsCompact Pn := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  have hBr : Pn ⊆ range β := by
    rw [hβr]; exact statePhysicalSet_subset_physSet (κ := κ) (b := b) (jumps := jumps) (D := D) hlen.le
  obtain ⟨x₁, hΦ, hΦd⟩ := phys_facts_of_fill hc hcN h₁ hc₁N hAc hĝ hC hγ hβ hfill hB hBr hhead hX
  -- the piece on the tail after `t_L`
  have htLσ : tL ≤ σ := by
    have hRP : (realMax A : ℂ) ∈ β '' Icc 0 σ := by rw [← hPσ']; exact hR
    obtain ⟨τ, hτ, hτe⟩ := hRP
    have : τ = tL := hβ.2.1 (hτe.trans hγ.1.symm)
    rw [← this]; exact hτ.2
  -- the finite lifetime
  set L₁ := (D n).2.toNNReal with hL₁def
  have hLe : ((L₁ : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfin
  have hL₁ : 0 < L₁ := by
    have := pos_iff_ne_zero.2 hpos
    rw [← hLe] at this; exact_mod_cast this
  have hpcc := continuousOn_pcPt_launch hP hl
  have htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (L₁ : ℝ≥0∞)}, q t ∈ β '' Ici tL := fun t ht => by
    obtain ⟨τ, hτ, hτe⟩ := hTσ t (by rw [← hLe]; exact ht)
    exact ⟨τ, le_trans htLσ hτ, hτe⟩
  have hq0 : q 0 = ((stPt s : ℝ) : ℂ) := pcPt_zero_launch hP hW hl hpos
  have hw₀' : ∀ s', β (tL + s') = q 0 → γ s' = w₀ := fun s' h => hw₀ s' (h.trans hq0)
  rw [← hLe] at hgood hF hcv hgdp he₂ hgen hpcc ⊢
  exact stage_fin_of_canon hL₁ hγ hβ hcH hc1 hcH' hoff hpcc htl hgood hF hΦ hΦd hw₀' hcw₀ hz₀ hζc hζH hcv hgdp
    he₂ hgen hreg hB₂ hcH₂ hc1₂ hc₂

end InteractingSLE.Theorem14.SB.Lk
