/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeDense

/-!
# SB2(2)'s joint stage induction (v6): the generation-free core of a lockstep stage

Packet PROVE-SB2-LIFTSET (round 21). Under GEOM2's v6 rule the relative driver of a stage generates its stage curve
only on the mask, which asks for dense readings at that stage; and the admissibility clause asks for drivenness on the
mask for families known only before the stage. **`stageCore_walk`**: at an old actual stage (a launched, positive
piece with `R` explored) with the lockstep facts of the relative state (domain chart, normalization, fill identity,
the chart reading `0` and continuous at the lifted seed), **without any fact of the relative driver of the stage**:

* the run-chart stage curve is driven (CORNER's F2a carried by `isDrivenCurve_stCurvep_of_canon`, the good-set
  matching `goodTp_eq_canonGood_old`, the physical domain identity `phys_facts_of_fill`, the start value
  `tendsto_relValp_of_tail`);
* the lifted good points lie in the relative chart's domain (`stage_dom_of_phys`);
* the readings in the relative chart's domain are dense (`denseReads_of`).
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

/-- **The generation-free core of an old lockstep stage**: drivenness, the domain clause and dense readings. -/
theorem stageCore_walk {θ : ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hR : (realMax (pA '' Icc 0 1) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H)
    {c : Chart} (hc : IsDomainChart (H \ fillH (pA '' Icc 0 1)) c) (hcN : WalkIntCanon.IsNormalized c)
    {ĝ : ℂ → ℂ} (hĝ : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (ĝ p))) {C : ℝ} (hC : ∀ p ∈ Hbar, ‖ĝ p - p‖ ≤ C)
    (hcH : ContinuousOn c.2.1 H) (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hcH' : ∀ w ∈ H, c.2.1 w ∈ H)
    (hoff : BdryOff c) (hDom : c.2.1 '' H = H \ fillH (pA '' Icc 0 1))
    {m : ℝ} {tL : ℝ≥0} {γ : ℝ≥0 → ℂ} (hγ : IsTailLiftCurve c (realMax (pA '' Icc 0 1)) m β tL γ)
    (hhead : β '' Icc 0 tL ⊆ hullK (pA '' Icc 0 1))
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)))
    {s₂ : ExplState} {P₂ : Set ℂ}
    (h₁ : IsDomainChart (H \ fillH P₂) (stChart s₂)) (hc₁N : WalkIntCanon.IsNormalized (stChart s₂))
    (hfill : fillH P₂ = fillH (liftImage β tL γ (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)))
    {w₀ : ℂ}
    (hw₀ : ∀ s, β (tL + s) = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ) →
      γ s = w₀)
    (hcw₀ : ContinuousWithinAt (stChart s₂).1 H w₀) (hz₀ : (stChart s₂).1 w₀ = 0) :
    IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂) ∧
      (∀ t ∈ goodTp c (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2,
        liftPt c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t) ∈
          (stChart s₂).2.1 '' H) ∧
      Nv.DenseReads c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 s₂ := by
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
  -- F2a, the good-set matching and the physical domain identity
  obtain ⟨x₀, hF⟩ := Dv.isDrivenCurve_walkStage_old hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR
    hS3
  have hgood := goodTp_eq_canonGood_old hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR hDom
  obtain ⟨σ, hσ, hPσ, hTσ, hle⟩ := old_cut hP hW hlm hlh hl hpos hpinv hAc hβ hβ0 hβr hR
  obtain ⟨-, -, -, hA, -⟩ := cut_package hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle
  have hPσ' : Pn = β '' Icc 0 σ := hPσ
  have hX : IsHPHull (fillH (A ∪ Pn)) := by rw [hPσ']; exact hA
  have hB : IsCompact Pn := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  have hBr : Pn ⊆ range β := by
    rw [hβr]; exact statePhysicalSet_subset_physSet (κ := κ) (b := b) (jumps := jumps) (D := D) hlen.le
  obtain ⟨x₁, hΦ, hΦd⟩ := phys_facts_of_fill hc hcN h₁ hc₁N hAc hĝ hC hγ hβ hfill hB hBr hhead hX
  -- the domain clause
  have hoffX : ∀ t ∈ goodTp c q (D n).2, q t ∉ fillH (A ∪ Pn) := fun t ht => by
    rw [hgood] at ht; exact ht.2.2
  have hdom := stage_dom_of_phys hΦd hc1 hcH' h₁.1.2.1 hoffX
  -- the start value and the drivenness
  have htLσ : tL ≤ σ := by
    have hRP : (realMax A : ℂ) ∈ β '' Icc 0 σ := by rw [← hPσ']; exact hR
    obtain ⟨τ, hτ, hτe⟩ := hRP
    have : τ = tL := hβ.2.1 (hτe.trans hγ.1.symm)
    rw [← this]; exact hτ.2
  have hpcc := continuousOn_pcPt_launch hP hl
  have htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2}, q t ∈ β '' Ici tL := fun t ht => by
    obtain ⟨τ, hτ, hτe⟩ := hTσ t ht
    exact ⟨τ, le_trans htLσ hτ, hτe⟩
  obtain ⟨σt, hσc, hσt⟩ := exists_tailTime hβ hpcc htl
  have hq0 : q 0 = ((stPt s : ℝ) : ℂ) := pcPt_zero_launch hP hW hl hpos
  have h0mem : ((0 : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := by simp
  have hgdp : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆ closure (goodTp c q (D n).2) := hgd
  have h0 : Tendsto (relValp c m q s₂) (𝓝[goodTp c q (D n).2 ∩ {t | (t : ℝ≥0∞) < (D n).2}] 0) (𝓝 0) := by
    have h := tendsto_relValp_of_tail (G := goodTp c q (D n).2 ∩ {t | (t : ℝ≥0∞) < (D n).2}) (t₀ := 0)
      hγ hcH hc1 hoff hσc hσt inter_subset_left h0mem
      (hw₀ (σt 0) ((hσt 0 h0mem).trans hq0)) hcw₀
    rwa [hz₀] at h
  have hne := neBot_good_zero hpos hgdp
  obtain ⟨hdr, -⟩ := isDrivenCurve_stCurvep_of_canon hΦ hgood hF h0 hne
  -- the dense readings
  have hO : IsOpen (c.2.1 '' H) := hc.1.isOpen_image
  have hdom' : ∀ t ∈ goodTp c q (D n).2, liftPt c m (q t) ∈ (stChart s₂).dom := fun t ht => by
    show liftPt c m (q t) ∈ ((stChart s₂).dom : Set ℂ)
    rw [h₁.1.coe_dom]; exact hdom t ht
  have hpc' : ContinuousOn q {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} :=
    hpcc.mono fun t (ht : (t : ℝ≥0∞) < (D n).2) => (le_of_lt ht : (t : ℝ≥0∞) ≤ (D n).2)
  have hdense := denseReads_of hpos hpc' hO hgdp hdom'
  exact ⟨hdr, hdom, hdense⟩

end InteractingSLE.Theorem14.SB.Lk
