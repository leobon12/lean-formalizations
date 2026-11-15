/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwOrder

/-!
# SB2(2): the shifted start piece's actual-piece facts (D6 v3, item 1)

Packet PROVE-SB2-LIFTSET (round 17). At a pure piece entry, with `t_R = visitTime` and the shifted point map
`p = pcPt (t_R + ·)` on `[0, L₀ − t_R]`, the actual-piece fields of `Stage0Facts` are **proved** (deterministic, given
GW1's chain facts, Lemma S2's tail clause, the tail form of S3 in `ℍ` and the upper chart's domain):

* `visitTime_spec` (the first visit is attained);
* **`hgd_after`**: the good times are dense in `[t_R, L₀)` (the piece's points after `t_R` are tail points,
  `startPiece_order`; then `interior_setOf_notMem_domain_eq_empty` and the tail form of S3 on arcs after `t_R`);
* `hdense_tail_of_closure` (the tail's `D`-times are dense once every tail point of the tip is a limit of its points in
  `D`);
* **`stage0Actual`**: `htipD` (no good time before `t_R`), the shifted density, `L ≠ 0` (when `t_R < L₀`), the lifted
  endpoint, and the tail's `D`-time density.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **The first visit of `R` is attained** when the piece visits `R`. -/
theorem visitTime_spec (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) {R : ℝ}
    (hR : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (R : ℂ)) :
    ((visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R : ℝ≥0) : ℝ≥0∞) ≤
        (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)
        (visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R) = (R : ℂ) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (R : ℂ) →
        visitTime (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R ≤ t := by
  have hpc := continuousOn_pcPt_launch hP hl
  have hK : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := isClosed_le ENNReal.continuous_coe continuous_const
  have hcl : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = (R : ℂ)} :=
    hpc.preimage_isClosed_of_isClosed hK isClosed_singleton
  have hmem := hcl.csInf_mem hR (OrderBot.bddBelow _)
  exact ⟨hmem.1, hmem.2, fun t ht htR => csInf_le (OrderBot.bddBelow _) ⟨ht, htR⟩⟩

/-- **The good times are dense after `t_R`** (the piece's points after `t_R` are tail points). -/
theorem hgd_after (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {c : Chart} {A : Set ℂ} (hA : IsClosed A) (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ}
    (hβ : IsProperCurve β₀) (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {tL sh : ℝ≥0}
    (hord : ∀ t : ℝ≥0, sh < t → (t : ℝ≥0∞) < (D n).2 → ∀ t' : ℝ≥0,
      β₀ t' = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t → tL < t')
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ H) :
    {t : ℝ≥0 | sh ≤ t ∧ (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) := by
  set s₁ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs₁
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hpc := continuousOn_pcPt_launch hP hl
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ true) hP n
  have hinj := pcPt_injOn_launch hP hW hl
  have he := isClosedEmbedding_of_isProperCurve hβ
  have htipR : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → pcPt s₁ (D n) t ∈ range β₀ := fun t ht => by
    rw [hβr]
    exact tipSet_subset_physSet_launch hl (by rw [htip]; exact ⟨t, ht, rfl⟩)
  rintro t₀ ⟨hsh₀, ht₀⟩
  by_contra hcl
  obtain ⟨U, hU, hUg⟩ : ∃ U ∈ 𝓝 t₀, U ∩ goodT c s₁ (D n) = ∅ := by
    rw [mem_closure_iff_nhds] at hcl
    push Not at hcl
    obtain ⟨U, hU, hUe⟩ := hcl
    exact ⟨U, hU, hUe⟩
  obtain ⟨u, htu, hIcoU⟩ := exists_Ico_subset_of_mem_nhds hU ⟨t₀ + 1, lt_add_one t₀⟩
  obtain ⟨d', htd', hd'T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
  set d := min u d' with hd
  have htd : t₀ < d := lt_min htu (by exact_mod_cast htd')
  have hdT : (d : ℝ≥0∞) < (D n).2 := lt_of_le_of_lt (by exact_mod_cast min_le_right u d') hd'T
  have hIT : ∀ t ∈ Ioo t₀ d, (t : ℝ≥0∞) < (D n).2 := fun t ht => lt_trans (ENNReal.coe_lt_coe.2 ht.2) hdT
  have hIK : ∀ t ∈ Ioo t₀ d, (t : ℝ≥0∞) ≤ (D n).2 := fun t ht => le_of_lt (hIT t ht)
  have hbad : ∀ t ∈ Ioo t₀ d, pcPt s₁ (D n) t ∉ H \ fillH A := by
    intro t ht hgood
    have htU : t ∈ U := hIcoU ⟨le_of_lt ht.1, lt_of_lt_of_le ht.2 (min_le_left u d')⟩
    have : t ∈ U ∩ goodT c s₁ (D n) := ⟨htU, hIK t ht, by rw [hDom]; exact hgood⟩
    rw [hUg] at this
    exact this
  have hint := interior_setOf_notMem_domain_eq_empty (p := pcPt s₁ (D n)) (α := trOf (D n)) hA isOpen_Ioo
    (hpc.mono fun t ht => hIK t ht)
    (fun t ht => im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 (hIK t ht))
    (fun t ht hH => by
      have he' : pcPt s₁ (D n) t = (stChart s₁).2.1 (trOf (D n) t) := bdVal_eq_of_mem_H hcc.1.continuousOn hH
      rw [he']
      exact hcc.2.1 hH)
    (fun t ht hH hA' => by
      obtain ⟨t', ht'⟩ := htipR t (hIK t ht)
      have hlt := hord t (lt_of_le_of_lt hsh₀ ht.1) (hIT t ht) t' ht'
      rw [← ht'] at hH hA' ⊢
      exact hright t' hlt hH hA')
    (interior_real_times_nn hα (hPR.2.1.mono fun s hs => le_of_lt (show (s : ℝ≥0∞) < (D n).2 from hs)) hPR.1
      hdT)
    (fun a e hae hsub' hsubA => by
      obtain ⟨mid, hm1, hm2⟩ := exists_between hae
      have hmT : (mid : ℝ≥0∞) < (D n).2 := hIT mid (hsub' ⟨hm1, hm2⟩)
      have hsubI : Ioo a mid ⊆ Ioo t₀ d := fun x hx => hsub' ⟨hx.1, lt_trans hx.2 hm2⟩
      -- a time of `(a, mid)` where the trace is in `ℍ`
      obtain ⟨t, htI, htH⟩ : ∃ t ∈ Ioo a mid, trOf (D n) t ∈ H := by
        by_contra hno
        push Not at hno
        have hreal := interior_real_times_nn (a := a) hα (hPR.2.1.mono fun s hs => le_of_lt
          (show (s : ℝ≥0∞) < (D n).2 from hs)) hPR.1 hmT
        have hall : {t : ℝ≥0 | t ∈ Ioo a mid ∧ (trOf (D n) t).im = 0} = Ioo a mid := by
          ext t
          refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
          have h0 := im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 (hIK t (hsubI h))
          by_contra hne
          exact hno t h (lt_of_le_of_ne h0 (Ne.symm hne))
        rw [hall, isOpen_Ioo.interior_eq] at hreal
        obtain ⟨y, hy⟩ := exists_between hm1
        exact (hreal ▸ (hy : y ∈ Ioo a mid) : y ∈ (∅ : Set ℝ≥0))
      have hpH : ∀ t' ∈ Ioo a mid, trOf (D n) t' ∈ H → pcPt s₁ (D n) t' ∈ H := fun t' _ h => by
        rw [show pcPt s₁ (D n) t' = (stChart s₁).2.1 (trOf (D n) t') from bdVal_eq_of_mem_H hcc.1.continuousOn h]
        exact hcc.2.1 h
      have hopen : IsOpen (Ioo a mid ∩ pcPt s₁ (D n) ⁻¹' H) :=
        (hpc.mono fun t' ht' => hIK t' (hsubI ht')).isOpen_inter_preimage isOpen_Ioo QuantumZipper.isOpen_H
      obtain ⟨a₀, c₀, ⟨hat, htc⟩, hJ⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨a, htI.1⟩ ⟨mid, htI.2⟩).1
        (hopen.mem_nhds ⟨htI, hpH t htI htH⟩)
      obtain ⟨a', ha1, ha2⟩ := exists_between hat
      obtain ⟨c'', hc1, hc2⟩ := exists_between htc
      have hJ' : Icc a' c'' ⊆ Ioo a mid ∩ pcPt s₁ (D n) ⁻¹' H := fun x hx =>
        hJ ⟨lt_of_lt_of_le ha1 hx.1, lt_of_le_of_lt hx.2 hc2⟩
      have hIcc : Icc a' c'' ⊆ Ioo t₀ d := fun x hx => hsubI (hJ' hx).1
      have hlt : a' < c'' := lt_trans ha2 hc1
      have hSA : pcPt s₁ (D n) '' Icc a' c'' ⊆ A ∩ H := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨hsubA ⟨x, ⟨(hJ' hx).1.1, lt_trans (hJ' hx).1.2 hm2⟩, rfl⟩, (hJ' hx).2⟩
      have hSr : pcPt s₁ (D n) '' Icc a' c'' ⊆ range β₀ := by
        rintro _ ⟨x, hx, rfl⟩; exact htipR x (hIK x (hIcc hx))
      have hSc : IsPreconnected (pcPt s₁ (D n) '' Icc a' c'') :=
        isPreconnected_Icc.image _ (hpc.mono fun x hx => hIK x (hIcc hx))
      have hne : pcPt s₁ (D n) a' ≠ pcPt s₁ (D n) c'' := fun h =>
        (ne_of_lt hlt) (hinj (hIT a' (hIcc ⟨le_rfl, hlt.le⟩)) (hIT c'' (hIcc ⟨hlt.le, le_rfl⟩)) h)
      obtain ⟨σ, τ, hστ, hστS⟩ := WalkCont.exists_Icc_image_subset_of_isPreconnected he.isEmbedding hSr hSc
        ⟨a', ⟨le_rfl, hlt.le⟩, rfl⟩ ⟨c'', ⟨hlt.le, le_rfl⟩, rfl⟩ hne
      obtain ⟨x, hx, hxσ⟩ := hστS ⟨σ, ⟨le_rfl, hστ.le⟩, rfl⟩
      have hσ := hord x (lt_of_le_of_lt hsh₀ (hIcc hx).1) (hIT x (hIcc hx)) σ hxσ.symm
      exact hS3 σ τ hσ.le hστ fun z hz => hSA (hστS (image_mono Ioo_subset_Icc_self hz)))
  have hfull : {t : ℝ≥0 | t ∈ Ioo t₀ d ∧ pcPt s₁ (D n) t ∉ H \ fillH A} = Ioo t₀ d := by
    ext t
    exact ⟨fun h => h.1, fun h => ⟨h, hbad t h⟩⟩
  rw [hfull, isOpen_Ioo.interior_eq] at hint
  obtain ⟨y, hy⟩ := exists_between htd
  exact (hint ▸ (⟨hy.1, hy.2⟩ : y ∈ Ioo t₀ d) : y ∈ (∅ : Set ℝ≥0))

/-- **The tail's `D`-times are dense** once every tail point of `T` is a limit of points of `T` in `D` and the points
of `T` in `D` are on the tail (`β₀` proper). -/
theorem hdense_tail_of_closure {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) {tL : ℝ≥0} {T Dm : Set ℂ}
    (htail : T ∩ Dm ⊆ β₀ '' Ici tL) (hTD : ∀ s, β₀ (tL + s) ∈ T → β₀ (tL + s) ∈ closure (T ∩ Dm)) :
    {s | β₀ (tL + s) ∈ T} ⊆ closure {s | β₀ (tL + s) ∈ T ∩ Dm} := by
  have he := isClosedEmbedding_of_isProperCurve hβ
  intro s hs
  set G' := {u : ℝ≥0 | tL ≤ u ∧ β₀ u ∈ T ∩ Dm} with hG'
  have himg : β₀ '' G' = T ∩ Dm := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu.2
    · intro hz
      obtain ⟨u, hu, rfl⟩ := htail hz
      exact ⟨u, ⟨hu, hz⟩, rfl⟩
  have hu : tL + s ∈ closure G' := by
    rw [he.isInducing.closure_eq_preimage_closure_image, himg]
    exact hTD s hs
  have hsub : (fun u : ℝ≥0 => u - tL) '' G' ⊆ {s | β₀ (tL + s) ∈ T ∩ Dm} := by
    rintro _ ⟨u, hu, rfl⟩
    show β₀ (tL + (u - tL)) ∈ T ∩ Dm
    rw [add_tsub_cancel_of_le hu.1]
    exact hu.2
  have hcont : Continuous fun u : ℝ≥0 => u - tL := continuous_id.sub continuous_const
  have h2 := hcont.continuousWithinAt.mem_closure_image hu
  rw [show tL + s - tL = s from add_tsub_cancel_left tL s] at h2
  exact closure_mono hsub h2

end InteractingSLE.Theorem14.SB.Lk
