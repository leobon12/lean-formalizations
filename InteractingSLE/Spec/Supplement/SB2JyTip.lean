/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JiTop
import InteractingSLE.Spec.Supplement.SB2LgChain

/-!
# SB2(2): the actual piece's tip set and tail times, and the lift relation with closed tail times

Packet PROVE-SB2-LIFTSET (round 14). Facts about an actual launched piece, **proved outright** from the regularity of
the walk's launches (`RegLaunches`, almost sure by `GW1W.regLaunches_of_stagedPiecesRegular`):

* **`tipSet_newPc_launch`**: the piece's physical set is the image of its points `pcPt` over `[0, e.2]`, and these
  are the values of a continuous, proper boundary map of the launch chart along the chosen trace;
* **`isClosed_tipSet_launch`** (every launch: a recorded piece is closed, `GW1P.isClosed_pieces_run`),
  **`isCompact_tipSet_launch`** (finite lifetime);
* `isClosed_tail_times`, **`isCompact_tail_times_launch`**.

**Correction of `SB2JiGeom.StageGeomInf`**: its field `IsCompact {s | β₀ (tL + s) ∈ tip}` is false for an infinite
actual piece on the tail (the proper curve `β₀` traverses it on an unbounded time set). The lift relation only needs
the tail times closed (the lift curve is proper, hence a closed map):

* **`liftImage_eq_closure_closed`**, **`liftRel_of_closure_closed`** (closed tail times), `liftRel_of_stage_closed2`;
* **`liftRel_concrete_top2`**: `SB2JiTop.liftRel_concrete_top` with closed tail times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The physical set of a launched piece is the image of its points**: at a regular launch, there is a continuous
boundary map `g` of the launch chart on `ℍ̄` (proper: `‖w‖ ≤ C₁ ‖g w‖ + C₂`) with `pcPt = g ∘ trOf` on `[0, e.2]`, and
the recorded piece's physical set is `pcPt '' [0, e.2]`. -/
theorem tipSet_newPc_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = g (trOf (D n) t)) ∧
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
          (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
          (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 =
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) ''
          {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := by
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ true) hP n
  have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ true) D hP n).1
  obtain ⟨g, hgc, -, hprop, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) t).im := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hval : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = g (trOf (D n) t) :=
    fun t ht => bdVal_eq_of_tendsto (hαH t ht) (hgt _ (hαH t ht))
  refine ⟨g, hgc, hprop, hval, ?_⟩
  rw [tipSet_newPc_eq hα hPR.2.1 hPR.1 (fun t ht => hgt _ (hαH t ht)), image_image]
  exact (image_congr fun t ht => hval t ht).symm

/-- **A launched piece's physical set is closed** (it is recorded by the launch, and recorded pieces of a run with
regular launches are closed). -/
theorem isClosed_tipSet_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    IsClosed ((newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2) := by
  have hcl := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ true) D hP (n + 1)).2
  apply hcl
  rw [GW1W.launch_walk hl, launch_pieces]
  exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **A launched piece of finite lifetime is compact.** -/
theorem isCompact_tipSet_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hfin : (D n).2 ≠ ⊤) :
    IsCompact ((newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2) := by
  obtain ⟨g, hgc, -, hval, htip⟩ := tipSet_newPc_launch hP hl
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hK : IsCompact {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := by
    have e' : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} = Iic (D n).2.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Iic]
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
    rw [e', ← Icc_bot]
    exact isCompact_Icc
  have hcont : ContinuousOn (fun t => g (trOf (D n) t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} :=
    hgc.comp hα.2.1 fun t ht => im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  rw [htip, image_congr (s := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2}) fun t ht => hval t ht]
  exact hK.image_of_continuousOn hcont

/-- The tail times of a closed set are closed. -/
theorem isClosed_tail_times {β₀ : ℝ≥0 → ℂ} (hβ : Continuous β₀) (tL : ℝ≥0) {S : Set ℂ} (hS : IsClosed S) :
    IsClosed {s | β₀ (tL + s) ∈ S} :=
  hS.preimage (hβ.comp (continuous_const.add continuous_id))

/-- **The tail times of a launched piece of finite lifetime are compact** (`β₀` proper). -/
theorem isCompact_tail_times_launch (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hfin : (D n).2 ≠ ⊤) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (tL : ℝ≥0) :
    IsCompact {s | β₀ (tL + s) ∈
      (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2} :=
  isCompact_tail_times hβ (isCompact_tipSet_launch hP hl hfin)

/-! ### The lift relation with closed tail times -/

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The lift image as the closure of the intrinsic lift, closed tail times** (`liftImage_eq_closure` with the tail
times closed rather than compact: the lift curve is proper, hence a closed map). -/
theorem liftImage_eq_closure_closed (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {S : Set ℂ}
    (hTcl : IsClosed {s | β₀ (tL + s) ∈ S})
    (hdense : {s | β₀ (tL + s) ∈ S} ⊆ closure {s | β₀ (tL + s) ∈ S ∩ c.2.1 '' H}) :
    liftImage β₀ tL γ S = closure (liftPt c m '' (S ∩ c.2.1 '' H ∩ β₀ '' Ici tL)) := by
  set T := {s | β₀ (tL + s) ∈ S} with hTdef
  set G := {s | β₀ (tL + s) ∈ S ∩ c.2.1 '' H} with hGdef
  have hγc : Continuous γ := hγ.2.1.1
  have hGT : G ⊆ T := fun s hs => hs.1
  have hGimg : γ '' G = liftPt c m '' (S ∩ c.2.1 '' H ∩ β₀ '' Ici tL) := by
    ext z
    constructor
    · rintro ⟨s, ⟨hsS, hsD⟩, rfl⟩
      have hH := (lift_mem_H_iff hγ hcH hc1 hoff s).1.1 hsD
      refine ⟨β₀ (tL + s), ⟨⟨hsS, hsD⟩, tL + s, mem_Ici.2 (le_add_of_nonneg_right zero_le), rfl⟩, ?_⟩
      exact ((lift_mem_H_iff hγ hcH hc1 hoff s).2 hH).symm
    · rintro ⟨_, ⟨⟨hpS, hpD⟩, t, ht, rfl⟩, rfl⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = tL + s := ⟨t - tL, (add_tsub_cancel_of_le (mem_Ici.1 ht)).symm⟩
      have hH := (lift_mem_H_iff hγ hcH hc1 hoff s).1.1 hpD
      exact ⟨s, ⟨hpS, hpD⟩, (lift_mem_H_iff hγ hcH hc1 hoff s).2 hH⟩
  unfold liftImage
  rw [← hGimg]
  have hTimg : IsClosed (γ '' T) := (isClosedEmbedding_of_isProperCurve hγ.2.1).isClosedMap T hTcl
  refine Subset.antisymm ?_ (hTimg.closure_subset_iff.2 (image_mono hGT))
  calc γ '' T ⊆ γ '' closure G := image_mono hdense
    _ ⊆ closure (γ '' G) := image_closure_subset_closure_image hγc

/-- **The lift relation from the intrinsic lift, closed tail times.** -/
theorem liftRel_of_closure_closed (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {q₁ q₂ : Pc}
    (hTcl : IsClosed {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2})
    (hdense : {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2} ⊆
      closure {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H})
    (hq : q₂.1.tipSet q₂.2.1 q₂.2.2 =
      closure (liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL))) :
    LiftRel β₀ tL γ q₁ q₂ := by
  unfold LiftRel
  rw [hq, liftImage_eq_closure_closed hγ hcH hc1 hoff hTcl hdense]

/-- **The lift relation at one stage, closed tail times and closed relative image.** -/
theorem liftRel_of_stage_closed2 (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {q₁ : Pc}
    (hTcl : IsClosed {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2} ⊆
      closure {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H})
    {s : ExplState} {e : Drv} {α : ℝ≥0 → ℂ} {f : ℂ → ℂ} (hα : IsGeneratingTrace e.1 e.2 α)
    (hW : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ e.2}) (hW0 : e.1 0 = 0)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e.2 → Tendsto (stChart s).2.1 (𝓝[H] (α t)) (𝓝 (f (α t))))
    (hclosed : IsClosed ((fun t => f (α t)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2}))
    (hgc : ContinuousOn (fun t => f (α t)) {t | (t : ℝ≥0∞) ≤ e.2})
    {Gd : Set ℝ≥0} {v : ℝ≥0 → ℂ} (hGd : Gd ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2})
    (hdense₂ : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2} ⊆ closure Gd) (hval : ∀ t ∈ Gd, f (α t) = v t)
    (hv₁ : v '' Gd ⊆ liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL))
    (hv₂ : liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL) ⊆ closure (v '' Gd)) :
    LiftRel β₀ tL γ q₁ (newPc s e) := by
  refine liftRel_of_closure_closed hγ hcH hc1 hoff hTcl hdense₁ ?_
  rw [tipSet_newPc_eq hα hW hW0 hc, image_image, image_eq_closure_of_closed hclosed hgc hGd hdense₂,
    image_congr hval]
  exact Subset.antisymm (closure_mono hv₁) (closure_minimal hv₂ isClosed_closure)

variable {s₁ s₂ : ExplState} {e₁ e₂ : Drv}

/-- **The lift relation at a concrete stage, infinite actual lifetime, closed tail times** (the corrected
`liftRel_concrete_top`). -/
theorem liftRel_concrete_top2 (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c)
    (hTcl : IsClosed {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2})
    (hdense₁ : {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
      closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H})
    (htip₁ : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 =
      pcPt s₁ e₁ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2})
    (htail : (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H ⊆ β₀ '' Ici tL)
    (he₁ : e₁.2 = ⊤) (hρ : IsDrivenCurve (stCurve c m s₁ e₁ s₂))
    (he₂ : e₂.2 = capLife (stCurve c m s₁ e₁ s₂))
    (hgen : ∀ T < capLife (stCurve c m s₁ e₁ s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurve c m s₁ e₁ s₂)))
    (hW : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) ≤ e₂.2}) (hW0 : e₂.1 0 = 0)
    {α : ℝ≥0 → ℂ} (hαeq : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → α τ = capTrace (stCurve c m s₁ e₁ s₂) τ)
    (hα0 : α 0 = 0) (hαc : ContinuousOn α {τ | (τ : ℝ≥0∞) ≤ e₂.2}) {f : ℂ → ℂ}
    (hc : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ e₂.2 → Tendsto (stChart s₂).2.1 (𝓝[H] (α τ)) (𝓝 (f (α τ))))
    (hgc : ContinuousOn (fun τ => f (α τ)) {τ | (τ : ℝ≥0∞) ≤ e₂.2})
    (hclosed : IsClosed ((fun τ => f (α τ)) '' {τ : ℝ≥0 | (τ : ℝ≥0∞) ≤ e₂.2}))
    (hcH₂ : ContinuousOn (stChart s₂).2.1 H) (hc1₂ : ∀ w ∈ H, (stChart s₂).1 ((stChart s₂).2.1 w) = w)
    (hdom : ∀ t ∈ goodT c s₁ e₁, liftPt c m (pcPt s₁ e₁ t) ∈ (stChart s₂).2.1 '' H)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < e₁.2} ⊆ closure (goodT c s₁ e₁)) :
    LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂) := by
  have hα := isGeneratingTrace_ext he₂ hgen hαeq hα0 hαc
  refine liftRel_of_stage_closed2 hγ hcH hc1 hoff hTcl hdense₁ hα hW hW0 hc hclosed hgc
    (fun τ h => le_of_lt h.1) (hdense_top hρ he₂ he₁ hgd)
    (v := fun τ => liftPt c m (pcPt s₁ e₁ (cTmTop c m s₁ e₁ s₂ τ))) ?_ ?_ ?_
  · rintro τ ⟨hτ, hg⟩
    obtain ⟨z, hz, hzw⟩ := hdom _ hg
    have hατ : α τ = z := by
      rw [hαeq τ hτ]
      show stCurve c m s₁ e₁ s₂ (capInv (stCurve c m s₁ e₁ s₂) τ) = z
      rw [stCurve_of_top he₁]
      change stVal c m s₁ e₁ s₂ (cTmTop c m s₁ e₁ s₂ τ) = z
      rw [stVal_of_good hg]
      unfold relVal
      rw [← hzw, hc1₂ z hz]
    have hlim := hc τ (le_of_lt hτ)
    rw [hατ] at hlim
    have : (𝓝[H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hz)
    rw [hατ, tendsto_nhds_unique hlim (hcH₂ z hz), hzw]
  · rintro _ ⟨τ, ⟨-, hg⟩, rfl⟩
    have hmem : pcPt s₁ e₁ (cTmTop c m s₁ e₁ s₂ τ) ∈
        (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 := by
      rw [htip₁]
      exact ⟨_, hg.1, rfl⟩
    exact ⟨_, ⟨⟨hmem, hg.2⟩, htail ⟨hmem, hg.2⟩⟩, rfl⟩
  · rintro _ ⟨p, ⟨⟨hp, hpD⟩, -⟩, rfl⟩
    rw [htip₁] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact hcov_top hρ he₂ ⟨_, ⟨t, ⟨ht, hpD⟩, rfl⟩, rfl⟩

end InteractingSLE.Theorem14.SB.Lk
