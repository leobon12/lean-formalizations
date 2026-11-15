/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvRoot
import InteractingSLE.Spec.Supplement.SB2JvV5

/-!
# SB2(2): the relative root stage, almost surely (drivenness and relative facts at stage `0`)

Packet PROVE-SB2-LIFTSET (round 18). The shifted start piece `rootPt` (the piece launched at `relOff`, read from its
visit time of `R`) on `[0, rootLife]`:

* `tendsto_norm_trOf`: an infinite regular piece's chosen trace is transient;
* **`rootInputs`** (deterministic): from the actual walk's facts (regular launches, GW1's chain facts, the head hull,
  the upper chart's domain, the seed at an old `R`, the density of good times), the shifted start piece is continuous,
  injective before its end, starts at `β₀ t_L`, lies on `β₀`'s tail, and is transient when infinite;
* **`sb2LowerRoot`**: almost surely under the retained kernel, off a zero root and at a positive shifted lifetime,
  the relative root's stage curve is **driven** and has its **relative facts** (`StageRelFinP` at a finite piece;
  `StageRelInfP` at an infinite one given an infinite capacity lifetime), for every root state with the identity
  chart and every regular relative driver generating it (Theorems 1.2–1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

/-- The shifted start piece: the piece launched from `s` read from its visit time of `R`. -/
def rootPt (s : ExplState) (e : Drv) (R : ℝ) : ℝ≥0 → ℂ := fun t => pcPt s e (visitTime s e R + t)

/-- The shifted start piece's lifetime. -/
def rootLife (s : ExplState) (e : Drv) (R : ℝ) : ℝ≥0∞ := e.2 - visitTime s e R

/-- **An infinite regular piece's chosen trace is transient.** -/
theorem tendsto_norm_trOf {e : Drv} (h : GW1P.PieceRegular e.1 e.2) (htop : e.2 = ⊤) :
    Tendsto (fun t => ‖trOf e t‖) atTop atTop := by
  obtain ⟨-, -, α, hα, htr⟩ := h
  have hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace e.1 e.2 η ∧ (e.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) :=
    ⟨α, hα, htr⟩
  unfold trOf
  split_ifs
  exact hex.choose_spec.2 htop

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}

/-- **An infinite launched piece is transient** (read from any shift). -/
theorem tendsto_norm_pcPt_shift (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (htop : (D n).2 = ⊤) (sh : ℝ≥0) :
    Tendsto (fun t => ‖pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) (sh + t)‖)
      atTop atTop := by
  obtain ⟨g, -, ⟨C₁, C₂, hC₁, hCg⟩, hval, -⟩ := tipSet_newPc_launch hP hl
  have hPR := pieceRegular_of_launch hP hl
  have htr : Tendsto (fun t => ‖trOf (D n) t‖) atTop atTop := tendsto_norm_trOf hPR htop
  have hα := isGeneratingTrace_trOf hPR
  have hH : ∀ r : ℝ≥0, 0 ≤ (trOf (D n) r).im := fun r =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 (by rw [htop]; exact le_top)
  have hshift : Tendsto (fun t : ℝ≥0 => sh + t) atTop atTop :=
    tendsto_atTop_mono (fun t => le_add_self) tendsto_id
  have htr' : Tendsto (fun t => ‖trOf (D n) (sh + t)‖) atTop atTop := htr.comp hshift
  rcases eq_or_lt_of_le hC₁ with h0 | hpos'
  · exfalso
    obtain ⟨r, hr⟩ := (htr.eventually_gt_atTop C₂).exists
    have h1 := hCg _ (hH r)
    rw [← h0, zero_mul, zero_add] at h1
    linarith
  · refine tendsto_atTop_mono (fun t => ?_) ((tendsto_atTop_add_const_right _ (-C₂) htr').atTop_div_const hpos')
    have h1 := hCg _ (hH (sh + t))
    rw [hval (sh + t) (by rw [htop]; exact le_top), div_le_iff₀ hpos']
    linarith

/-- **The shifted start piece's actual facts** (deterministic). -/
theorem rootInputs (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpos : (D n).2 ≠ 0) {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {tL : ℝ≥0} {A : Set ℂ}
    {c : Chart} (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A) {R : ℝ} (hβL : β₀ tL = R)
    (hRmem : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hseed : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) →
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = R)
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < rootLife (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R}
      ⊆ closure (goodTp c (rootPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R)
        (rootLife (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R)))
    (hL0 : rootLife (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R ≠ 0) :
    ContinuousOn (rootPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R)
        {t : ℝ≥0 | (t : ℝ≥0∞) ≤ rootLife (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R} ∧
      InjOn (rootPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R)
        {t : ℝ≥0 | (t : ℝ≥0∞) < rootLife (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R} ∧
      rootPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R 0 = β₀ tL ∧
      (∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤
          rootLife (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R},
        rootPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R t ∈ β₀ '' Ici tL) ∧
      ((D n).2 = ⊤ → Tendsto (fun t =>
        ‖rootPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) R t‖) atTop atTop) := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set sh := visitTime s (D n) R with hsh
  set p := rootPt s (D n) R with hp
  set L := rootLife s (D n) R with hL
  -- the visit time is before the lifetime and the piece is at `R` there
  have hvis : (sh : ℝ≥0∞) ≤ (D n).2 ∧ pcPt s (D n) sh = (R : ℂ) := by
    by_cases hRo : (R : ℂ) ∈ statePhysicalSet 0 s
    · have h0 : sh = 0 := visitTime_eq_zero_of_old hP hW hl hpos hRo
      refine ⟨by rw [h0, ENNReal.coe_zero]; exact bot_le, ?_⟩
      rw [h0, pcPt_zero_launch hP hW hl hpos, hseed hRo]
    · have hsplit : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) =
          statePhysicalSet 0 s ∪ (newPc s (D n)).1.tipSet (newPc s (D n)).2.1 (newPc s (D n)).2.2 := by
        rw [GW1W.launch_walk hl]
        exact GW1WalkChain.statePhysicalSet_launch 0 _ n (D n) θ ⊤
      rw [hsplit] at hRmem
      have hRt := hRmem.resolve_left hRo
      obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
      rw [htip] at hRt
      obtain ⟨t₀, ht₀, ht₀R⟩ := hRt
      obtain ⟨h1, h2, -⟩ := visitTime_spec hP hl ⟨t₀, ht₀, ht₀R⟩
      exact ⟨h1, h2⟩
  have hshL : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ L → ((sh + t : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := fun t ht => by
    rw [ENNReal.coe_add]
    calc (sh : ℝ≥0∞) + t ≤ sh + L := by gcongr
      _ = (D n).2 := add_tsub_cancel_of_le hvis.1
  have hshL' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < L → ((sh + t : ℝ≥0) : ℝ≥0∞) < (D n).2 := fun t ht => by
    rw [ENNReal.coe_add]
    exact lt_tsub_iff_left.1 ht
  have hpc := continuousOn_pcPt_launch hP hl
  have hPc : ContinuousOn p {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} :=
    hpc.comp (continuous_const.add continuous_id).continuousOn fun t ht => hshL t ht
  have hinj : InjOn p {t : ℝ≥0 | (t : ℝ≥0∞) < L} := fun a ha a' ha' e => by
    have := pcPt_injOn_launch hP hW hl (hshL' a ha) (hshL' a' ha') e
    exact add_left_cancel this
  have hp0 : p 0 = β₀ tL := by
    show pcPt s (D n) (sh + 0) = β₀ tL
    rw [add_zero, hvis.2, hβL]
  -- every point is on the tail: good points by `tail_of_launch`, the rest by density and closedness
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP hl
  have htail := tail_of_launch hl hβr hK hDom
  have hcl : IsClosed (β₀ '' Ici tL) := (isClosedEmbedding_of_isProperCurve hβ).isClosedMap _ isClosed_Ici
  have hgood : ∀ t ∈ goodTp c p L, p t ∈ β₀ '' Ici tL := fun t ht => by
    refine htail ⟨?_, ht.2⟩
    rw [htip]
    exact ⟨sh + t, hshL t ht.1, rfl⟩
  have hclos : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} ⊆ closure (goodTp c p L) := by
    intro t ht
    rcases (show (t : ℝ≥0∞) ≤ L from ht).lt_or_eq with hlt | heq
    · exact hgd hlt
    · have ht0 : 0 < t := by
        rcases eq_or_ne t 0 with h0 | h0
        · exact absurd (by rw [← heq, h0, ENNReal.coe_zero]) hL0
        · exact pos_iff_ne_zero.2 h0
      have hsub : Iio t ⊆ {t' : ℝ≥0 | (t' : ℝ≥0∞) < L} := fun t' h => by
        rw [mem_ofPred_eq, ← heq]; exact ENNReal.coe_lt_coe.2 h
      have hmem : t ∈ closure (Iio t) := by
        rw [closure_Iio' (show (Iio t).Nonempty from ⟨0, ht0⟩)]; exact mem_Iic.2 le_rfl
      have := closure_mono (hsub.trans hgd) hmem
      rwa [closure_closure] at this
  have htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}, p t ∈ β₀ '' Ici tL := fun t ht => by
    have hcw : ContinuousWithinAt p (goodTp c p L) t := (hPc t ht).mono fun t' h => h.1
    refine hcl.closure_subset_iff.2 ?_ (hcw.mem_closure_image (hclos ht))
    rintro _ ⟨t', ht', rfl⟩
    exact hgood t' ht'
  refine ⟨hPc, hinj, hp0, htl, fun htop => ?_⟩
  exact tendsto_norm_pcPt_shift hP hl htop sh

/-- **The relative root, almost surely** (Theorems 1.2–1.3): off a zero root and at a positive shifted lifetime, the
stage curve of the shifted start piece read at any root state with the identity chart is driven and has its relative
facts for every regular relative driver generating it (at an infinite piece, given an infinite capacity lifetime). -/
theorem sb2LowerRoot (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
        rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
            (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lR κ b jumps E u l k ω₀) ≠ 0 →
        ∀ s₂ : ExplState, stChart s₂ = Chart.id.recenter 0 →
          let p := rootPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lR κ b jumps E u l k ω₀)
          let L := rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lR κ b jumps E u l k ω₀)
          {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L) ∧
          (L = ⊤ → Tendsto (fun u => ‖stCurvep c m p L s₂ u‖) atTop atTop) ∧
          IsDrivenCurve (stCurvep c m p L s₂) ∧
          ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = capLife (stCurvep c m p L s₂) →
            (∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂))) →
            (L ≠ ⊤ → StageRelFinP c m p L s₂ e₂) ∧
            (L = ⊤ → capLife (stCurvep c m p L s₂) = ⊤ → StageRelInfP c m p L s₂ e₂) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [hβex,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRunExit h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerStage0Act h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hβ₀ hT₀ hU₀ hK₀ hA₀ hX₀ hD₀ hI₀ hS₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm
  obtain ⟨-, ⟨hcH, hc1, hoff⟩, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  filter_upwards [hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hK₀ c θ hlaunch b' J' h' hb' hT' hG',
    hA₀ c θ hlaunch b' J' h' hb' hT' hG', hX₀ c θ hlaunch b' J' h' hb' hT' hG',
    hD₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hS₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hβω hTω hKω hAω hXω hDω hIω hSω
  intro hZ hL0 s₂ hs₂
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  set R := lR κ b jumps E u l k ω₀ with hRdef
  set D₁ := lD₁ b jumps E ω with hD₁
  set o := relOff κ (-(Real.pi / 2)) b jumps R D₁ with ho
  set s₁ := wRun κ (-(Real.pi / 2)) b jumps D₁ o with hs₁
  have hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D₁ := by
    rw [← hγ.1, ← hβr]; exact mem_range_self tL
  obtain ⟨hl, hseed⟩ := launch_seed_of_not_zeroRoot hb hXω hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hAω hDω
    hR hZ
  have hpos : (D₁ o).2 ≠ 0 := fun h0 => hL0 (by simp only [rootLife, h0, zero_tsub])
  have hsh : (D₁ o).2 - shiftD κ (-(Real.pi / 2)) b jumps R D₁ 0 ≠ 0 := by rw [shiftD_zero]; exact hL0
  have hact := hSω β₀ hβ hβ0 hβr tL hγ.1 m hZ hl hpos hsh
  rw [shiftD_zero] at hact
  have hact' : Stage0Act c m β₀ tL s₁ (D₁ o) (rootPt s₁ (D₁ o) R) (rootLife s₁ (D₁ o) R) := hact
  have hK := hKω β₀ hβ hβ0 hβr tL hγ.1
  obtain ⟨hPc, hinj, hp0, htl, htrp⟩ := rootInputs hP₁ hW₁ hl hpos hβ hβr hK hDom hγ.1
    (mem_succ_of_not_zeroRoot hR hZ) hseed hact'.2.1 hL0
  obtain ⟨hs₁', -, -, -, -⟩ := root_chart_facts hs₂
  intro p L
  have hPc2 : ContinuousOn p {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} := hPc
  have hinj2 : InjOn p {t : ℝ≥0 | (t : ℝ≥0∞) < L} := hinj
  have hp02 : p 0 = β₀ tL := hp0
  have htl2 : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L}, p t ∈ β₀ '' Ici tL := htl
  have hgd2 : {t : ℝ≥0 | (t : ℝ≥0∞) < L} ⊆ closure (goodTp c p L) := hact'.2.1
  have htrp2 : (D₁ o).2 = ⊤ → Tendsto (fun t => ‖p t‖) atTop atTop := htrp
  have hL02 : L ≠ 0 := hL0
  have hLe : (D₁ o).2 ≠ ⊤ → L ≠ ⊤ := fun hne => ENNReal.sub_ne_top hne
  clear_value p L
  clear hPc hinj hp0 htl htrp hact' hact
  by_cases hLtop : L = ⊤
  · have he₁ : (D₁ o).2 = ⊤ := by
      by_contra hne
      exact hLe hne hLtop
    subst hLtop
    have hS : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun t => le_top (a := (t : ℝ≥0∞))
    have hS' : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top (r := t)
    have hgd' : ∀ t : ℝ≥0, t ∈ closure (goodTp c p ⊤) := fun t => hgd2 (ENNReal.coe_lt_top (r := t))
    have hPc' : Continuous p := by rw [← continuousOn_univ, ← hS]; exact hPc2
    have hinj' : Function.Injective p := by rw [← injOn_univ, ← hS']; exact hinj2
    have htl' : ∀ t, p t ∈ β₀ '' Ici tL := fun t => htl2 t (le_top (a := (t : ℝ≥0∞)))
    have hr := root_inf hγ hβ hcH hc1 hoff hs₁' hPc' hinj' hp02 htl' hgd' (htrp2 he₁)
    refine ⟨hgd2, fun _ => hr.2.1, hr.1, fun e₂ hreg he₂ _ => ⟨fun h => absurd rfl h, fun _ htop => ?_⟩⟩
    exact root_stageRelInfP hγ hβ hcH hc1 hoff hs₂ hPc' hinj' hp02 htl' hgd' (htrp2 he₁) he₂ hreg htop
  · obtain ⟨L₁, rfl⟩ : ∃ L₁ : ℝ≥0, (L₁ : ℝ≥0∞) = L := ⟨L.toNNReal, ENNReal.coe_toNNReal hLtop⟩
    have hL₁0 : 0 < L₁ := by
      rw [pos_iff_ne_zero]
      intro h
      exact hL02 (by rw [h, ENNReal.coe_zero])
    have hr := root_fin hγ hβ hcH hc1 hoff hL₁0 hs₁' hPc2 hinj2 hp02 htl2 hgd2
    refine ⟨hgd2, fun h => absurd h ENNReal.coe_ne_top, hr.1, fun e₂ hreg he₂ hgen =>
      ⟨fun _ => ?_, fun h => absurd h ENNReal.coe_ne_top⟩⟩
    exact root_stageRelFinP hγ hβ hcH hc1 hoff hL₁0 hs₂ hPc2 hinj2 hp02 htl2 hgd2 he₂ hgen hreg

end InteractingSLE.Theorem14.SB.Lk
