/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JbInf

/-!
# SB2(2)'s joint stage induction: F2a at the infinite last stage, with the lift and the capacity

Packet PROVE-SB2-LIFTSET (round 20). **`canon_old_top`** (walk level): at an old stage with an infinite piece, F2a's
canonical curve (`Dv.isDrivenCurve_walkStage_old`) is the lift `γ ∘ φ₀` of CORNER's time change of the piece along the
tail of `β` after the cut (the offsets agree: both curves start at `0`, `canonVal_eq_of_lift_shift`); the lift is
transient; and the canonical curve is the run-chart stage curve for the hull chart of `A ∪ β([0, σ])` with the
identity relative chart (`stValp_init_eq_canonVal`), so `capLife_root_top` gives an infinite capacity lifetime from the
capacity growth of the prefix with the piece (`hcap_prefix_piece`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Sec7.PocketTraversal Sec7.Lemma71C LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

/-- **The stage values for a hull chart with the identity relative chart are the canonical values.** -/
theorem stValp_init_eq_canonVal {X : Set ℂ} (hA : IsHPHull (fillH X)) (e : ℝ) (q : ℝ≥0 → ℂ) (L : ℝ≥0∞) (t : ℝ≥0) :
    stValp (Mo.hullChart (fillH X) 0) (-e) q L (ExplState.init 0) t = Dv.canonVal X e q L t := by
  classical
  have hD := Mo.isDomainChart_hullChart hA 0
  have hG : goodTp (Mo.hullChart (fillH X) 0) q L = Dv.canonGood X q L := by
    ext t'; simp only [goodTp, Dv.canonGood, hD.2.1, mem_ofPred_eq]
  have hf : relValp (Mo.hullChart (fillH X) 0) (-e) q (ExplState.init 0) =
      fun t' => (Mo.hullChart (fillH X) e).1 (q t') := by
    funext t'
    simp only [relValp, liftPt, Mo.hullChart_fwd]
    simp [ExplState.init, stChart, Chart.id, Chart.recenter, sub_eq_add_neg]
  unfold stValp Dv.canonVal
  rw [hG, hf]

/-- The canonical curve of an infinite piece is the run-chart stage curve for the hull chart with the identity relative
chart. -/
theorem canonCurve_top_eq_stCurvep {X : Set ℂ} (hA : IsHPHull (fillH X)) (e : ℝ) (q : ℝ≥0 → ℂ) :
    Dv.canonCurve X e q ⊤ = stCurvep (Mo.hullChart (fillH X) 0) (-e) q ⊤ (ExplState.init 0) := by
  funext u
  rw [stCurvep_of_top rfl, stValp_init_eq_canonVal hA]
  unfold Dv.canonCurve
  simp only [↓reduceIte]

/-- The inverse hull chart's boundary map stays within bounded distance of the identity on `ℍ̄`. -/
theorem hullChart_ext_bounded {X : Set ℂ} (hA : IsHPHull (fillH X)) {g : ℂ → ℂ}
    (hgt : ∀ q ∈ Hbar, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] q) (𝓝 (g q))) :
    ∃ C : ℝ, ∀ q ∈ Hbar, ‖g q - q‖ ≤ C := by
  obtain ⟨M, hM⟩ := Mo.hullChart_inv_bounded hA 0
  refine ⟨M, fun q hq => ?_⟩
  have : (𝓝[H] q).NeBot := GW1P.neBot_nhdsWithin_H hq
  have h1 : Tendsto (fun y => ‖(Mo.hullChart (fillH X) 0).2.1 y - y‖) (𝓝[H] q) (𝓝 ‖g q - q‖) :=
    ((hgt q hq).sub (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  exact le_of_tendsto h1 (eventually_nhdsWithin_of_forall fun y hy => hM y hy)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **F2a at an infinite old stage, with the lift and the capacity** (walk level). -/
theorem canon_old_top {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) (htop : (D n).2 = ⊤)
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
    (hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 |
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t' ∈ H \ fillH (pA '' Icc 0 1)}) :
    ∃ (x₀ : ℝ) (ζ : ℝ≥0 → ℂ),
      IsDrivenCurve (Dv.canonCurve (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        x₀ (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) ⊤) ∧
      (∀ t, ζ t ∈ Hbar) ∧ Tendsto (fun t => ‖ζ t‖) atTop atTop ∧
      (∀ t, Dv.canonVal (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n) x₀
        (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) ⊤ t = ζ t) ∧
      capLife (Dv.canonCurve (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
        x₀ (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) ⊤) = ⊤ := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set A := pA '' Icc 0 1 with hAdef
  set q := pcPt s (D n) with hqdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hpc
  obtain ⟨x₀, hF⟩ := Dv.isDrivenCurve_walkStage_old hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR
    hS3
  rw [htop] at hF
  obtain ⟨σ, hσ, hPσ, hTσ, hle⟩ := old_cut hP hW hlm hlh hl hpos hpinv hAc hβ hβ0 hβr hR
  obtain ⟨e, g, γ, hA, hgt, hgi, hgc, hgfr, hγ⟩ := cut_package hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle
  set X := A ∪ β '' Icc 0 σ with hXdef
  have hPσ' : SB.prefixPhysSet κ b jumps w D n = β '' Icc 0 σ := hPσ
  have hXX : A ∪ SB.prefixPhysSet κ b jumps w D n = X := by rw [hPσ']
  rw [hXX] at hF ⊢
  have hXc : IsCompact X := hAc.union (isCompact_Icc.image hβ.1)
  -- the infinite piece: continuous, injective, onto the tail after the cut
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) w D hl
  have hpcc := continuousOn_pcPt_launch hP hl
  have hqc : Continuous q := by
    rw [← continuousOn_univ]
    exact hpcc.mono fun t _ => (show (t : ℝ≥0∞) ≤ (D n).2 by rw [htop]; exact le_top)
  have hinj := pcPt_injOn_launch hP hW hl
  have hqi : Function.Injective q := fun a b' hab =>
    hinj (show (a : ℝ≥0∞) < (D n).2 by rw [htop]; exact ENNReal.coe_lt_top)
      (show (b' : ℝ≥0∞) < (D n).2 by rw [htop]; exact ENNReal.coe_lt_top) hab
  have hq0 : q 0 = β σ := by rw [hσ]; exact pcPt_zero_launch hP hW hl hpos
  have hdone : stStatus (ExplState.run κ b jumps w D (n + 1)) = GW1Conn.stDone := by
    by_contra hnd'
    exact fin_of_not_done hnd' hl htop
  have hphys := physSet_walk_eq_of_done (κ := κ) (θ := θ) (b := b) (J := jumps) (D := D) (n := n + 1)
    (Nat.succ_le_of_lt hlen) hdone
  have hsucc := prefixPhysSet_succ_of_launch hl'
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hqβ : range q = β '' Ici σ := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨t, rfl⟩
      exact hTσ t (by rw [htop]; exact le_top)
    · rintro _ ⟨τ, hτ, rfl⟩
      have hmem : β τ ∈ SB.prefixPhysSet κ b jumps w D (n + 1) := by
        have := mem_range_self (f := β) τ
        rw [hβr, hphys] at this
        exact this
      rw [hsucc] at hmem
      rcases hmem with hP' | hT'
      · have hP'' : β τ ∈ SB.prefixPhysSet κ b jumps w D n := hP'
        rw [hPσ'] at hP''
        obtain ⟨τ', hτ', he⟩ := hP''
        have := hβ.2.1 he
        have hτσ : τ = σ := le_antisymm (this ▸ hτ'.2) hτ
        rw [hτσ, ← hq0]; exact mem_range_self 0
      · rw [htip] at hT'
        obtain ⟨t, -, ht⟩ := hT'
        exact ⟨t, ht⟩
  obtain ⟨φ₀, hφc, hφ0, hφm, hφs, hqφ⟩ := Dv.exists_timeChange_top hβ hqc hqi hq0 hqβ
  set q' : ℝ≥0 → ℂ := fun t => β (σ + φ₀ t) with hq'def
  have hqq' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ⊤ → q t = q' t := fun t _ => hqφ t
  have hgood : {t' : ℝ≥0 | q t' ∈ H \ fillH A} ⊆ Dv.canonGood X q' ⊤ := by
    rintro t' ht'
    have ht'0 : 0 < t' := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      have ht0 : q 0 ∈ H \ fillH A := h ▸ ht'
      rw [hq0, hσ] at ht0
      have him : (0 : ℝ) < (((stPt s : ℝ) : ℂ)).im := ht0.1
      simp at him
    refine ⟨le_top, ?_⟩
    have ht'' : q t' ∈ H \ fillH A := ht'
    rw [hqφ t'] at ht''
    exact Dv.mem_diff_fill_union hAc hβ hA hγ hgt hgi hgfr (by rw [← hφ0]; exact hφm ht'0) ht''
  have hdq : ∀ t : ℝ≥0, t ∈ closure (Dv.canonGood X q' ⊤) := fun t => closure_mono hgood (hden t)
  have hζl : ∀ t, Tendsto (Mo.hullChart (fillH X) 0).2.1 (𝓝[H] (γ (φ₀ t) - ((-e : ℝ) : ℂ))) (𝓝 (q' t)) :=
    fun t => hγ.2.2.2 (φ₀ t)
  have hζc : Continuous (fun t => γ (φ₀ t)) := hγ.2.1.1.comp hφc
  have hval : ∀ t, Dv.canonVal X x₀ q ⊤ t = γ (φ₀ t) + ((e - x₀ : ℝ) : ℂ) := fun t => by
    rw [canonVal_congr hqq']
    exact canonVal_eq_of_lift_shift hA hζc (fun t => hγ.2.1.2.2.1 _) hζl hgt hgi hgfr (hdq t) x₀
  -- the offsets agree
  have hex : e = x₀ := by
    have h0 := hF.zero
    unfold Dv.canonCurve at h0
    simp only [↓reduceIte, Real.toNNReal_zero] at h0
    rw [hval 0, hφ0, hγ.2.2.1, zero_add] at h0
    have := congrArg Complex.re h0
    simp at this; linarith
  have hcv : ∀ t, Dv.canonVal X x₀ q ⊤ t = γ (φ₀ t) := fun t => by
    rw [hval t, hex, sub_self, Complex.ofReal_zero, add_zero]
  -- transience
  have hφtop : Tendsto φ₀ atTop atTop :=
    tendsto_atTop_atTop_of_monotone hφm.monotone fun y => ⟨(hφs y).choose, (hφs y).choose_spec.ge⟩
  have hζtr : Tendsto (fun t => ‖γ (φ₀ t)‖) atTop atTop := hγ.2.1.2.2.2.comp hφtop
  have hqtr : Tendsto (fun t => ‖q t‖) atTop atTop := by
    have h1 : Tendsto (fun t => σ + φ₀ t) atTop atTop :=
      tendsto_atTop_mono (fun t => le_add_self) hφtop
    exact (hβ.2.2.2.comp h1).congr fun t => by simp only [Function.comp, hqφ t]
  -- the capacity lifetime, through the hull chart with the identity relative chart
  have hD := Mo.isDomainChart_hullChart hA 0
  have hcc := Mo.isConformal_hullChart hA 0
  have hoff : BdryOff (Mo.hullChart (fillH X) 0) := bdryOff_of_ext hcc hgc hgi hgt
  obtain ⟨C, hC⟩ := hullChart_ext_bounded hA hgt
  have hs₂ : ∀ z, (stChart (ExplState.init 0)).1 z = z := fun z => by
    simp [ExplState.init, stChart, Chart.id, Chart.recenter]
  have hgdq : ∀ t, t ∈ closure (goodTp (Mo.hullChart (fillH X) 0) q ⊤) := fun t => by
    have hG : goodTp (Mo.hullChart (fillH X) 0) q ⊤ = Dv.canonGood X q' ⊤ := by
      rw [← Dv.canonGood_congr hqq']
      ext t'; simp only [goodTp, Dv.canonGood, hD.2.1, mem_ofPred_eq]
    rw [hG]; exact hdq t
  have hhead : β '' Icc 0 σ ⊆ hullK X := by
    rintro _ ⟨τ, hτ, rfl⟩
    have hmem : β τ ∈ X := Or.inr ⟨τ, hτ, rfl⟩
    rcases (show (0 : ℝ) ≤ (β τ).im from hβ.2.2.1 τ).lt_or_eq with hpos' | hzero
    · exact Or.inl (mem_fillH_of_mem_closure hpos' (subset_closure hmem))
    · have hre : β τ = (((β τ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hre] at hmem ⊢
      exact Or.inr ⟨(β τ).re, ⟨FinRel.realMin_le_of_mem hXc hmem, Lx.le_realMax_of_mem hXc hmem⟩, rfl⟩
  have hKpc : IsCompact (β '' Icc 0 σ) := isCompact_Icc.image hβ.1
  have hcapK : ∀ T : ℝ≥0, IsHPHull (fillH (β '' Icc 0 σ ∪ q '' Icc 0 T)) ∧
      ConformalImage.hcapSet (fillH (β '' Icc 0 σ ∪ q '' Icc 0 T)) =
        2 * T + ConformalImage.hcapSet (fillH (β '' Icc 0 σ)) := fun T => by
    have h := hcap_prefix_piece hP hW hl htop T
    rw [hPσ'] at h
    exact h
  rw [hex] at hγ
  have hqr : ∀ t, q t ∈ range β := fun t => image_subset_range _ _ (hqβ ▸ mem_range_self t)
  have hcap := capLife_root_top hγ hβ hcc.1.continuousOn hcc.2.2 hoff hs₂ hqc hqi hq0
    (fun t => hqβ ▸ mem_range_self t) hgdq hqtr hA hXc hD hgc hgi hgt hC hhead hKpc (image_subset_range _ _) hqc
    hqr hcapK
  refine ⟨x₀, fun t => γ (φ₀ t), hF, fun t => hγ.2.1.2.2.1 _, hζtr, hcv, ?_⟩
  rw [canonCurve_top_eq_stCurvep hA]
  exact hcap

/-- **One infinite lockstep stage at walk level**: driven and `StageRelInfP`. -/
theorem stageInf_walk {θ : ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) (htop : (D n).2 = ⊤)
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
    {s₂ : ExplState} {e₂ : Drv} {P₂ : Set ℂ}
    (h₁ : IsDomainChart (H \ fillH P₂) (stChart s₂)) (hc₁N : WalkIntCanon.IsNormalized (stChart s₂))
    (hfill : fillH P₂ = fillH (liftImage β tL γ (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)))
    (hB₂ : HasBdryLimits (stChart s₂).2.1) {C₂ : ℝ}
    (hC₂ : ∀ p ∈ Hbar, ‖extendFrom H (stChart s₂).2.1 p - p‖ ≤ C₂) (hcH₂ : ContinuousOn (stChart s₂).2.1 H)
    (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w) (hc₂ : ∀ y ∈ H, (stChart s₂).2.1 y ∈ H)
    {w₀ : ℂ}
    (hw₀ : ∀ s, β (tL + s) = ((stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℝ) : ℂ) →
      γ s = w₀)
    (hcw₀ : ContinuousWithinAt (stChart s₂).1 H w₀) (hz₀ : (stChart s₂).1 w₀ = 0)
    (he₂ : e₂.2 = capLife (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
      (D n).2 s₂))
    (hreg : IsRegularDriver e₂) :
    IsDrivenCurve (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂) ∧
      StageRelInfP c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) (D n).2 s₂ e₂ ∧
      Tendsto (fun u => ‖stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂ u‖) atTop atTop ∧
      capLife (stCurvep c m (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n))
        (D n).2 s₂) = ⊤ := by
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
  have hgood := goodTp_eq_canonGood_old hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR hDom
  have hgdp : {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆ closure (goodTp c q (D n).2) := hgd
  have hden : ∀ t : ℝ≥0, t ∈ closure {t' : ℝ≥0 | q t' ∈ H \ fillH A} := fun t => by
    have h := hgdp (show (t : ℝ≥0∞) < (D n).2 by rw [htop]; exact ENNReal.coe_lt_top)
    refine closure_mono (fun t' ht' => ?_) h
    have ht'' := ht'.2
    rw [hDom] at ht''
    exact ht''
  obtain ⟨x₀, ζ, hF, hζH, hζtr, hcv, hcap⟩ := canon_old_top hP hW hlm hlh hl hpos htop hpinv hpc hp0 hpH hpv hβ hβ0
    hβr hS1 hR hS3 hden
  obtain ⟨σ, hσ, hPσ, hTσ, hle⟩ := old_cut hP hW hlm hlh hl hpos hpinv hAc hβ hβ0 hβr hR
  obtain ⟨-, -, -, hA, -⟩ := cut_package hpc hp0 hpH hpv hβ hβ0 hS1 hσ hle
  have hPσ' : Pn = β '' Icc 0 σ := hPσ
  have hX : IsHPHull (fillH (A ∪ Pn)) := by rw [hPσ']; exact hA
  have hB : IsCompact Pn := Lx.isCompact_prefixPhysSet_run w D hP n hnd
  have hBr : Pn ⊆ range β := by
    rw [hβr]; exact statePhysicalSet_subset_physSet (κ := κ) (b := b) (jumps := jumps) (D := D) hlen.le
  obtain ⟨x₁, hΦ, hΦd⟩ := phys_facts_of_fill hc hcN h₁ hc₁N hAc hĝ hC hγ hβ hfill hB hBr hhead hX
  have htLσ : tL ≤ σ := by
    have hRP : (realMax A : ℂ) ∈ β '' Icc 0 σ := by rw [← hPσ']; exact hR
    obtain ⟨τ, hτ, hτe⟩ := hRP
    have : τ = tL := hβ.2.1 (hτe.trans hγ.1.symm)
    rw [← this]; exact hτ.2
  have hpcc := continuousOn_pcPt_launch hP hl
  have htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2}, q t ∈ β '' Ici tL := fun t ht => by
    obtain ⟨τ, hτ, hτe⟩ := hTσ t ht
    exact ⟨τ, le_trans htLσ hτ, hτe⟩
  have hq0 : q 0 = ((stPt s : ℝ) : ℂ) := pcPt_zero_launch hP hW hl hpos
  have hw₀' : ∀ s', β (tL + s') = q 0 → γ s' = w₀ := fun s' h => hw₀ s' (h.trans hq0)
  rw [htop] at hgood hgdp he₂ hpcc htl ⊢
  exact stage_inf_of_canon hγ hβ hcH hc1 hcH' hoff hpcc htl hgood hF hΦ hΦd hw₀' hcw₀ hz₀ hζH hζtr hcv hcap hgdp
    he₂ hreg hB₂ hC₂ hcH₂ hc1₂ hc₂

end InteractingSLE.Theorem14.SB.Lk
