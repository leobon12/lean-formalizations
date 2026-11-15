/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3LtMain
import InteractingSLE.Spec.Supplement.SB2JtTail

/-!
# SB2(2)'s good-time density from Lemma S3's tail form in `ℍ` — PROVED from Theorems 1.2–1.3

Worker PROVE-R6-CORNER (round 7). PROVE-SB2-LIFTSET's `Lk.sb2LowerStageDensityTail` (`SB2JtTail`) takes
`S3.Canon.SB2LowerWalkTailNoCommonArcStatement` as a hypothesis, and uses it only through `Lk.piece_noArc_of_tail`,
which applies it to arcs it has shown to lie in `ℍ`. The same three proofs with the `ℍ`-form of the hypothesis
(`¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ ℍ`, PROVED here as `sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13`):

* `piece_noArc_of_tailH`, `hgd_of_launch_tailH` (deterministic; LIFTSET's proofs, the last line adapted);
* **`sb2LowerStageDensity_of_thm12_thm13`**: LIFTSET's density conclusion with **no S3 hypothesis**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Lk Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **No open time interval of a later piece maps into `A`**, from the tail form of S3 (deterministic). -/
theorem piece_noArc_of_tailH (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {A : Set ℂ} {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0}
    (hhead : β₀ '' Icc 0 tL ⊆ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hS3 : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ H) :
    ∀ s₁ s₂ : ℝ≥0, s₁ < s₂ → (s₂ : ℝ≥0∞) ≤ (D n).2 →
      ¬ pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) '' Ioo s₁ s₂ ⊆ A := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  intro s₁ s₂ h12 h2 hsub
  have hPR := pieceRegular_of_launch hP hl
  have hαT := isGeneratingTrace_trOf hPR
  have hpc := continuousOn_pcPt_launch hP hl
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ true) hP n
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have hinj := pcPt_injOn_launch hP hW hl
  have hsimp := tip_inter_old_real hW hl
  obtain ⟨mid, hm1, hm2⟩ := exists_between h12
  have hmT : (mid : ℝ≥0∞) < (D n).2 := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hm2) h2
  have hIK : ∀ t ∈ Ioo s₁ mid, (t : ℝ≥0∞) ≤ (D n).2 := fun t ht =>
    le_of_lt (lt_trans (ENNReal.coe_lt_coe.2 ht.2) hmT)
  -- a time of `(s₁, mid)` where the trace is in `ℍ`
  obtain ⟨t, htI, htH⟩ : ∃ t ∈ Ioo s₁ mid, trOf (D n) t ∈ H := by
    by_contra hno
    push Not at hno
    have hreal := interior_real_times_nn (a := s₁) hαT (hPR.2.1.mono fun s hs => le_of_lt
      (show (s : ℝ≥0∞) < (D n).2 from hs)) hPR.1 hmT
    have hall : {t : ℝ≥0 | t ∈ Ioo s₁ mid ∧ (trOf (D n) t).im = 0} = Ioo s₁ mid := by
      ext t
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      have h0 := im_nonneg_of_isGeneratingTrace_le hαT hPR.2.1 hPR.1 (hIK t h)
      by_contra hne
      exact hno t h (lt_of_le_of_ne h0 (Ne.symm hne))
    rw [hall, isOpen_Ioo.interior_eq] at hreal
    obtain ⟨y, hy⟩ := exists_between hm1
    exact (hreal ▸ (hy : y ∈ Ioo s₁ mid) : y ∈ (∅ : Set ℝ≥0))
  have hpH : ∀ t' ∈ Ioo s₁ mid, trOf (D n) t' ∈ H → pcPt s (D n) t' ∈ H := fun t' _ h => by
    rw [show pcPt s (D n) t' = (stChart s).2.1 (trOf (D n) t') from bdVal_eq_of_mem_H hcc.1.continuousOn h]
    exact hcc.2.1 h
  -- an open interval around `t` where the piece is in `ℍ`
  have hopen : IsOpen (Ioo s₁ mid ∩ pcPt s (D n) ⁻¹' H) :=
    (hpc.mono fun t' ht' => hIK t' ht').isOpen_inter_preimage isOpen_Ioo QuantumZipper.isOpen_H
  obtain ⟨a, c', ⟨hat, htc⟩, hJ⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨s₁, htI.1⟩ ⟨mid, htI.2⟩).1
    (hopen.mem_nhds ⟨htI, hpH t htI htH⟩)
  obtain ⟨a', ha1, ha2⟩ := exists_between hat
  obtain ⟨c'', hc1, hc2⟩ := exists_between htc
  have hIcc : Icc a' c'' ⊆ Ioo a c' := fun x hx => ⟨lt_of_lt_of_le ha1 hx.1, lt_of_le_of_lt hx.2 hc2⟩
  set S := pcPt s (D n) '' Icc a' c'' with hS
  have hSsub : ∀ z ∈ S, z ∈ H ∧ z ∈ A ∧
      z ∈ (newPc s (D n)).1.tipSet (newPc s (D n)).2.1 (newPc s (D n)).2.2 := by
    rintro _ ⟨x, hx, rfl⟩
    have hxJ := hJ (hIcc hx)
    refine ⟨hxJ.2, hsub ⟨x, ⟨hxJ.1.1, lt_trans hxJ.1.2 hm2⟩, rfl⟩, ?_⟩
    rw [htip]; exact ⟨x, hIK x hxJ.1, rfl⟩
  have hSrange : S ⊆ range β₀ := fun z hz => by
    rw [hβr]; exact tipSet_subset_physSet_launch hl (hSsub z hz).2.2
  have hSconn : IsPreconnected S :=
    (isPreconnected_Icc.image _ ((hpc.mono fun x hx => hIK x (hJ (hIcc hx)).1)))
  have hlt : a' < c'' := lt_trans ha2 hc1
  have hltT : ∀ x ∈ Ioo s₁ mid, (x : ℝ≥0∞) < (D n).2 := fun x hx => lt_trans (ENNReal.coe_lt_coe.2 hx.2) hmT
  have hne : pcPt s (D n) a' ≠ pcPt s (D n) c'' := fun he =>
    (ne_of_lt hlt) (hinj (hltT a' (hJ (hIcc ⟨le_rfl, hlt.le⟩)).1) (hltT c'' (hJ (hIcc ⟨hlt.le, le_rfl⟩)).1) he)
  have he := isClosedEmbedding_of_isProperCurve hβ
  obtain ⟨σ, τ, hστ, hστS⟩ := WalkCont.exists_Icc_image_subset_of_isPreconnected he.isEmbedding hSrange hSconn
    ⟨a', ⟨le_rfl, hlt.le⟩, rfl⟩ ⟨c'', ⟨hlt.le, le_rfl⟩, rfl⟩ hne
  have hσ : tL ≤ σ := by
    by_contra hlt
    push Not at hlt
    have hz := hστS ⟨σ, ⟨le_rfl, hστ.le⟩, rfl⟩
    have hold := hhead ⟨σ, ⟨zero_le, hlt.le⟩, rfl⟩
    have hre := hsimp ⟨(hSsub _ hz).2.2, hold⟩
    have hpos : (0 : ℝ) < (β₀ σ).im := (hSsub _ hz).1
    rw [show (β₀ σ).im = 0 from hre] at hpos
    exact lt_irrefl _ hpos
  exact hS3 σ τ hσ hστ fun z hz =>
    ⟨(hSsub z (hστS (image_mono Ioo_subset_Icc_self hz))).2.1, (hSsub z (hστS (image_mono Ioo_subset_Icc_self hz))).1⟩

/-- **The good-time density at a launch whose state holds `R`, from the tail form of S3.** -/
theorem hgd_of_launch_tailH (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {c : Chart} {A : Set ℂ} (hA : IsClosed A) (hDom : c.2.1 '' H = H \ fillH A) {β₀ : ℝ≥0 → ℂ}
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {R : ℝ}
    (hβL : β₀ tL = R)
    (hR : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hright : ∀ t : ℝ≥0, tL < t → β₀ t ∈ H → β₀ t ∉ A → β₀ t ∈ H \ fillH A)
    (hS3 : ∀ s₁ s₂ : ℝ≥0, tL ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ A ∩ H) :
    {t : ℝ≥0 | (t : ℝ≥0∞) < (D n).2} ⊆
      closure (goodT c (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n)) := by
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D hl
  have hsub : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ⊆ range β₀ := by
    rw [hβr]; exact statePhysicalSet_subset_physSet hlen.le
  have hhead := head_subset_of_preconnected hβ hsub (prefix_facts hW.1 hW.2 n).1
    (by rw [hβ0]; exact Or.inl (Or.inl rfl)) (by rw [hβL]; exact hR)
  exact hgd_of_launch hP hW hl hA hDom hβr hhead hright (piece_noArc_of_tailH hP hW hl hβ hβr hhead hS3)

/-- **The good-time density at every relative stage `i ≥ 2`, almost surely, PROVED from Theorems 1.2–1.3**
(GW1's chain facts; Lemma S3's tail form in `ℍ`, `sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13`). -/
theorem sb2LowerStageDensity_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ tL : ℝ≥0, β₀ tL = lR κ b jumps E u l k ω₀ →
            ∀ i, 2 ≤ i →
              (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) + 1)).2.2.2.1
                  (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ≠ none →
              {t : ℝ≥0 | (t : ℝ≥0∞) < (lD₁ b jumps E ω
                  (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2} ⊆
                closure (goodT c (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                  (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
                  (lD₁ b jumps E ω
                    (i + relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))) := by
  have hW := sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hS3 := sb2LowerWalkTailNoCommonArcHStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRu := hER _ hsp
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hS3 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailRight κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hRLQ, hRu] with ω₀ hW₀ hS₀ hC₀ hT₀ hR₀ hRu₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨-, -, hDom⟩ := hC₀ c θ hlaunch b' J' h' hb' hT' hG'
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hRu₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  have hA : IsClosed (upperPrefix κ b jumps E u l k ω₀) :=
    (isCompact_upperPrefix hreg₀ (mem_upperLaunchSet hlaunch)).isClosed
  filter_upwards [hW₀ c θ hlaunch b' J' h' hb' hT' hG', hS₀ c θ hlaunch b' J' h' hb' hT' hG',
    hT₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hWω hSω hTω hRω
  intro β₀ hβ hβ0 hβr tL hβL i hi hl
  have hRmem : ((lR κ b jumps E u l k ω₀ : ℝ) : ℂ) ∈ ExplState.physSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lD₁ b jumps E ω) := by
    rw [← hβL]; exact (hβr ▸ mem_range_self tL : β₀ tL ∈ lowerWalkSet κ b jumps E ω)
  exact hgd_of_launch_tailH hRω hWω hl hA hDom hβ hβ0 hβr hβL (mem_statePhysicalSet_of_stage hRmem hi)
    (hTω β₀ hβ hβ0 hβr tL hβL) (hSω β₀ hβ hβ0 hβr tL hβL)

end InteractingSLE.Theorem14.SB.S3.Asm
