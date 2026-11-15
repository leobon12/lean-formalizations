/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwStage0
import InteractingSLE.Spec.Supplement.SBS3LtDensity

/-!
# SB2(2): the shifted start piece's actual-piece fields, assembled (D6 v3, item 1)

Packet PROVE-SB2-LIFTSET (round 17). `Stage0Act` collects the actual-piece fields of `Stage0Facts` (all but the
relative facts `StageRelP`). At the launch of stage `n` holding `R` in its new physical part, with the shifted point map
`p = pcPt (t_R + ·)` and shifted lifetime `L = L₀ − t_R` (`t_R = visitTime`):

* **`stage0Act_old`** (Case I: `R` already in the old physical part): then `t_R = 0`
  (`visitTime_eq_zero_of_old`: the piece meets the old part only in its seed) and the unshifted facts apply;
* **`stage0Act_new`** (Case II: `R` first visited by the piece, at `t_R < L₀`): the points before `t_R` are head
  points (`startPiece_order`), so no good time precedes `t_R`; the good times after `t_R` are dense (`hgd_after`); the
  fields transport along `u ↦ u − t_R`;
* **`stage0Act_of_mem`**: both cases, whenever the shifted lifetime is nonzero.

The shifted lifetime is zero exactly when the piece first visits `R` at its end (Case II with `t_R = L₀`): the corner
case of the handoff §R17.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

/-- **The actual-piece fields of `Stage0Facts`** (all but the relative facts). -/
def Stage0Act (c : Chart) (m : ℝ) (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (s₁ : ExplState) (e₁ : Drv) (p : ℝ≥0 → ℂ)
    (L : ℝ≥0∞) : Prop :=
  (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H = p '' goodTp c p L ∧
  {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L) ∧ L ≠ 0 ∧
  (∀ t ∈ goodTp c p L, (t : ℝ≥0∞) = L → liftPt c m (p t) ∈
    closure ((fun t' => liftPt c m (p t')) '' (goodTp c p L ∩ {t' | (t' : ℝ≥0∞) < L}))) ∧
  {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2} ⊆
    closure {s | β₀ (tL + s) ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2 ∩ c.2.1 '' H}

theorem Stage0Act.facts {c : Chart} {m : ℝ} {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₁ : ExplState} {e₁ : Drv}
    {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {e₂ : Drv} (h : Stage0Act c m β₀ tL s₁ e₁ p L)
    (hr : StageRelP c m p L s₂ e₂) : Stage0Facts c m β₀ tL s₁ e₁ p L s₂ e₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hr⟩

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The visit time is `0` when `R` is in the old physical part** (the piece meets it only in its seed). -/
theorem visitTime_eq_zero_of_old (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {R : ℝ}
    (hR : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) :
    visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R = 0 := by
  have h0' := pcPt_zero_launch hP hW hl hpos
  have hcap := tip_inter_old_eq hW hl
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  unfold visitTime
  by_cases hex : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s₁ (D n) t = (R : ℂ)
  · obtain ⟨t, ht, htR⟩ := hex
    have hmem : pcPt s₁ (D n) t ∈ (newPc s₁ (D n)).1.tipSet (newPc s₁ (D n)).2.1 (newPc s₁ (D n)).2.2 ∩
        statePhysicalSet 0 s₁ := ⟨by rw [htip]; exact ⟨t, ht, rfl⟩, by rw [htR]; exact hR⟩
    rw [hcap] at hmem
    have h0 : pcPt s₁ (D n) 0 = (R : ℂ) := by rw [h0', ← htR]; exact (mem_singleton_iff.1 hmem).symm
    exact le_antisymm (csInf_le (OrderBot.bddBelow _) ⟨by simp, h0⟩) (by simp)
  · rw [show {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s₁ (D n) t = (R : ℂ)} = ∅ from
      eq_empty_iff_forall_notMem.2 fun t ht => hex ⟨t, ht⟩]
    exact NNReal.sInf_empty

/-- **Case I: `R` in the old physical part** (the shift is `0`; the unshifted facts). -/
theorem stage0Act_old (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {c : Chart} (hcc : c.IsConformal) (m : ℝ) {A : Set ℂ} (hA : IsClosed A)
    (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) {R : ℝ} (hβL : β₀ tL = R)
    (hR : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ H) :
    Stage0Act c m β₀ tL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R + t))
      ((D n).2 - visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R) := by
  rw [visitTime_eq_zero_of_old hP hW hl hpos hR]
  simp only [zero_add, ENNReal.coe_zero, tsub_zero]
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hgd := S3.Asm.hgd_of_launch_tailH hP hW hl hA hDom hβ hβ0 hβr hβL hR hright hS3
  refine ⟨?_, hgd, hpos, hend_of_launch hcc m hP hl hpos,
    hdense_tail_of_good hP hl hpos hβ (tail_of_launch hl hβr hK hDom) hgd⟩
  rw [htip]
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hD⟩
    exact ⟨t, ⟨ht, hD⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hD⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, hD⟩

/-- **Case II: `R` first visited by the piece, before its end** (the shifted facts). -/
theorem stage0Act_new (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {c : Chart} (hcc : c.IsConformal) (m : ℝ) {A : Set ℂ} (hA : IsClosed A)
    (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) {R : ℝ} (hβL : β₀ tL = R)
    (hRold : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (R : ℂ))
    (hlt : ((visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R : ℝ≥0) : ℝ≥0∞) <
      (D n).2)
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ H) :
    Stage0Act c m β₀ tL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R + t))
      ((D n).2 - visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R) := by
  obtain ⟨-, hsh, hmin⟩ := visitTime_spec hP hl hvis
  have hpc := continuousOn_pcPt_launch hP hl
  have htail := tail_of_launch hl hβr hK hDom
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  set sh := visitTime s₁ (D n) R with hsh_def
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  obtain ⟨hbefore, hafter⟩ := startPiece_order hP hW hl hpos hβ hβ0 hβr (tL := tL) (by rw [hβL]; exact hRold)
    (sh := sh) (by rw [hsh, hβL]) (fun t ht h => hmin t ht (h.trans hβL)) hlt
  have hgdA := hgd_after hP hW hl hA hDom hβ hβr hafter hright hS3
  -- no good time before the visit
  have hge : ∀ u ∈ goodT c s₁ (D n), sh ≤ u := by
    intro u hu
    by_contra hlt'
    push Not at hlt'
    obtain ⟨t', ht', heq⟩ := htail ⟨by rw [htip]; exact ⟨u, hu.1, rfl⟩, hu.2⟩
    exact absurd (hbefore u hlt' t' heq) (not_lt.2 ht')
  have hshL : (sh : ℝ≥0∞) ≤ (D n).2 := hlt.le
  have hgoodp : ∀ t, t ∈ goodTp c (fun t => pcPt s₁ (D n) (sh + t)) ((D n).2 - sh) ↔
      sh + t ∈ goodT c s₁ (D n) := by
    intro t
    show ((t : ℝ≥0∞) ≤ (D n).2 - sh ∧ _) ↔ (((sh + t : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 ∧ _)
    rw [ENNReal.coe_add, ENNReal.le_sub_iff_add_le_left ENNReal.coe_ne_top hshL]
  have hsub : ∀ u, sh ≤ u → sh + (u - sh) = u := fun u hu => add_tsub_cancel_of_le hu
  have hmaps : MapsTo (fun u : ℝ≥0 => u - sh) (goodT c s₁ (D n))
      (goodTp c (fun t => pcPt s₁ (D n) (sh + t)) ((D n).2 - sh)) := fun u hu =>
    (hgoodp _).2 (by rw [hsub u (hge u hu)]; exact hu)
  refine ⟨?_, ?_, (tsub_pos_iff_lt.2 hlt).ne', ?_, ?_⟩
  · -- the piece's part in `D`
    rw [htip]
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hzD⟩
      have hug : u ∈ goodT c s₁ (D n) := ⟨hu, hzD⟩
      refine ⟨u - sh, hmaps hug, ?_⟩
      show pcPt s₁ (D n) (sh + (u - sh)) = _
      rw [hsub u (hge u hug)]
    · rintro ⟨t, ht, rfl⟩
      have h2 := (hgoodp t).1 ht
      exact ⟨⟨sh + t, h2.1, rfl⟩, h2.2⟩
  · -- the shifted density
    intro t ht
    have ht' : ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 := by
      rw [ENNReal.coe_add]; exact lt_tsub_iff_left.1 ht
    have hc := hgdA ⟨le_self_add, ht'⟩
    have hcont : Continuous fun u : ℝ≥0 => u - sh := continuous_id.sub continuous_const
    have h1 := map_mem_closure hcont hc hmaps
    rwa [add_tsub_cancel_left] at h1
  · -- the lifted endpoint
    intro t ht heq
    have h2 := (hgoodp t).1 ht
    have heq' : ((sh + t : ℝ≥0) : ℝ≥0∞) = (D n).2 := by
      rw [ENNReal.coe_add, heq, add_tsub_cancel_of_le hshL]
    have hE := hend_of_launch hcc m hP hl hpos (sh + t) h2 heq'
    refine closure_mono ?_ hE
    rintro _ ⟨u, ⟨hu, hult⟩, rfl⟩
    refine ⟨u - sh, ⟨hmaps hu, ?_⟩, ?_⟩
    · show ((u - sh : ℝ≥0) : ℝ≥0∞) < (D n).2 - sh
      rw [lt_tsub_iff_left, ← ENNReal.coe_add, hsub u (hge u hu)]
      exact hult
    · show liftPt c m (pcPt s₁ (D n) (sh + (u - sh))) = _
      rw [hsub u (hge u hu)]
  · -- the tail's `D`-times
    refine hdense_tail_of_closure hβ htail fun s hs => ?_
    rw [htip] at hs ⊢
    obtain ⟨u, hu, heq⟩ := hs
    have hshu : sh ≤ u := by
      by_contra h
      push Not at h
      exact absurd (hbefore u h (tL + s) heq.symm) (not_lt.2 le_self_add)
    have huc : u ∈ closure (goodT c s₁ (D n)) := by
      rcases lt_or_eq_of_le (show (u : ℝ≥0∞) ≤ (D n).2 from hu) with hlt' | heq'
      · exact hgdA ⟨hshu, hlt'⟩
      · have hshu' : sh < u := by
          have : (sh : ℝ≥0∞) < u := heq' ▸ hlt
          exact_mod_cast this
        have hIco : Ico sh u ⊆ closure (goodT c s₁ (D n)) := fun x hx =>
          hgdA ⟨hx.1, by rw [← heq']; exact_mod_cast hx.2⟩
        have hu' : u ∈ closure (Ico sh u) := by rw [closure_Ico hshu'.ne]; exact ⟨hshu'.le, le_rfl⟩
        exact closure_minimal hIco isClosed_closure hu'
    have h1 := ((hpc u hu).mono (show goodT c s₁ (D n) ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} from
      fun t' h => h.1)).mem_closure_image huc
    rw [← heq]
    refine closure_mono ?_ h1
    rintro _ ⟨t', ht', rfl⟩
    exact ⟨⟨t', ht'.1, rfl⟩, ht'.2⟩

/-- **The shifted start piece's actual-piece fields** whenever `R` is in the launch's new physical part and the shifted
lifetime is nonzero. -/
theorem stage0Act_of_mem (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {c : Chart} (hcc : c.IsConformal) (m : ℝ) {A : Set ℂ} (hA : IsClosed A)
    (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) {R : ℝ} (hβL : β₀ tL = R)
    (hRmem : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hL : (D n).2 - visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R ≠ 0)
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ H) :
    Stage0Act c m β₀ tL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
      (fun t => pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R + t))
      ((D n).2 - visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R) := by
  by_cases hRo : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
  · exact stage0Act_old hP hW hl hpos hcc m hA hDom hβ hβ0 hβr hK hβL hRo hright hS3
  · have hsplit : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) =
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∪
          (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).1.tipSet
            (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.1
            (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)).2.2 := by
      rw [GW1W.launch_walk hl]
      exact GW1WalkChain.statePhysicalSet_launch 0 _ n (D n) θ ⊤
    rw [hsplit] at hRmem
    have hRt := hRmem.resolve_left hRo
    obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
    rw [htip] at hRt
    obtain ⟨t, ht, htR⟩ := hRt
    exact stage0Act_new hP hW hl hpos hcc m hA hDom hβ hβ0 hβr hK hβL hRo ⟨t, ht, htR⟩
      (tsub_pos_iff_lt.1 (pos_iff_ne_zero.2 hL)) hright hS3

end InteractingSLE.Theorem14.SB.Lk
