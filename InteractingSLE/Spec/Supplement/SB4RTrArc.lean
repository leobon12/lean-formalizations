/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrArcFam
import InteractingSLE.Spec.Supplement.SB4RTop
import InteractingSLE.Spec.Supplement.SB2LwLift
import InteractingSLE.Spec.Supplement.SB4RSymLeft

/-!
# SB2(2) at the initial-arc seed, from SB2(2) by translation and restart

Packet PROVE-T14-SB4LEAF (rulings R104, R104a). Supplement p. 635: "For a connector seed `v`, retain the lower prefix
through `v`. The remaining lower walk, in its current domain, starts with the remaining low interval up to the next
available mark. [...] Apply the just-proved common-seed assertion in this retained field".
**`sb2ArcLaunchLiftStatement_of_lower`**:
`Lf.SB2ArcLaunchLiftStatement` from SB2(2)'s combined target `Lh.SB2LowerLaunchLiftStatement` (applied at `u = 0` in the
field read from `v`, `exists_arcFam`, with its complete counterflow `exists_complete_counterflow_tr`), the free real
point of the completed lower walk `Lh.LowerWalkLeftFreeStatement` (PROVE-T14-SB2LIFT), and Theorems 1.2–1.3.

R48: Theorems 1.2–1.3 appear only as hypotheses of this Theorem 1.4 result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Supp9B Lx Lu Ly Leaf Exist.Staged Exist.StagedLaw FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

theorem upperSpec_eq (u : ℝ) (l : List (ℝ × ℝ≥0)) : (⟨u, true, scheduleProgram 0 l⟩ : ExplSpec) = upperSpec u l := rfl

/-- **SB2(2) at the initial-arc seed with the lift on its own output** (rulings R104, R104a). -/
theorem sb2ArcLaunchLiftStatement_of_lower (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hC : Lh.SB2LowerLaunchLiftStatement.{u}) (hfree : Lh.LowerWalkLeftFreeStatement.{u}) :
    SB2ArcLaunchLiftStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER v l k hv hlow0 hlow hl hθ hleft
  set B := affData 1 (-v) b with hB
  set JB := affJumps 1 (-v) jumps with hJB
  have hbB : IsPiecewiseConstantBoundaryData B JB := isPiecewiseConstantBoundaryData_affData one_pos hb
  have hhT : IsGFFWithBoundaryData P (fun ω => affField (-v) one_pos (h ω)) B JB :=
    IsGFFWithBoundaryData.affine_finset (m := -v) one_pos hh
  obtain ⟨Wv, ζv, hcfv, hζv⟩ := exists_complete_counterflow_tr h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hv hlow0 hlow
  have hθ' : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := fun p hp => Ioc_subset_Icc_self (hθ p hp)
  obtain ⟨ET, hETs, hETr, hETsch, hrun, hphys⟩ :=
    exists_arcFam h12 h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hv hlow0 hlow hθ'
  have hprog : IsBoundaryContinuedProgram (sspec v l).2.2 := GW2Sched.isBoundaryContinuedProgram_scheduleProgram hθ' 0
  obtain ⟨hPR, -⟩ := Wire.walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hpropT := hPR κ hκ hκ4 B JB hbB P _ hhT Wv ζv hcfv hζv ET hETs hETr
  -- the prefix read from `v`
  have hpre : ∀ ω, (∀ k', ExplState.run κ B JB (upperSpec 0 l) (fun j => ET (upperSpec 0 l) j ω) k' =
      trState v (ExplState.run κ b jumps (sspec v l) (fun j => E (sspec v l) j ω) k')) →
      upperPrefix κ B JB ET 0 l k ω = (fun z => z - (v : ℂ)) '' prefixPhysSet κ b jumps (sspec v l)
        (fun j => E (sspec v l) j ω) k := fun ω hr => by
    unfold upperPrefix
    rw [upperSpec_eq, ← trSpec_sspec v l,
      prefixPhysSet_trSpec v (sspec v l) _ _ k (by rw [trSpec_sspec, hr k]) (by rw [trSpec_sspec, hr k])]
    have h0 : ((↑) : ℝ → ℂ) '' Icc 0 0 ⊆ (fun z => z - (v : ℂ)) '' prefixPhysSet κ b jumps (sspec v l)
        (fun j => E (sspec v l) j ω) k := by
      rintro _ ⟨x, hx, rfl⟩
      have hx0 : x = 0 := le_antisymm hx.2 hx.1
      subst hx0
      exact ⟨(v : ℂ), Or.inl (Or.inl rfl), by simp⟩
    exact Set.union_eq_left.2 h0
  -- SB2(2)'s avoidance read from `v`
  have hleftT : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ B JB ET 0 l k →
      upperPrefix κ B JB ET 0 l k ω ∩ rightSideOf (lowerWalkSet κ B JB ET ω) = ∅ := by
    filter_upwards [hleft, hrun, hphys] with ω hω hr hp hL
    have hLω : ω ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k := by
      have h1 : (ExplState.run κ B JB (upperSpec 0 l) (fun j => ET (upperSpec 0 l) j ω) (k + 1)).2.2.2.1 k ≠ none :=
        hL
      rw [hr (k + 1), trState_launches] at h1
      intro h0
      exact h1 (by show trLaunch v _ = none; rw [h0]; rfl)
    have hav := hω hLω
    rw [hpre ω hr]
    have hsub := rightSideOf_subset_of_restart hv.le hp
    refine Set.eq_empty_of_subset_empty fun z ⟨hz1, hz2⟩ => ?_
    obtain ⟨w, hw, rfl⟩ := hsub hz2
    obtain ⟨w', hw', hww'⟩ := hz1
    have : w' = w := by simpa using hww'
    subst this
    have hmem : w' ∈ arcPrefix κ b jumps E v l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) := ⟨Or.inl hw', hw⟩
    rw [hav] at hmem
    exact hmem
  have hbase := hC κ hκ hκ4 B JB hbB P _ hhT Wv ζv hcfv hζv ET hETs hETr 0 l k le_rfl hl hθ
    (fun x hx => absurd hx.2 (not_lt.2 hx.1.le)) hleftT
  -- the conditional laws of the two retained pasts
  have hregS : ∀ j ω, IsRegularDriver (ET (upperSpec 0 l) j ω) := fun j ω => by
    rw [hETsch]; exact StagedReg.isRegularDriver_regHist j ω
  have hK : ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ B JB (upperSpec 0 l) (ET (upperSpec 0 l)) k) ω₀ =
      condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀ := by
    have hpm' : Measurable (pastMap κ B JB (upperSpec 0 l) (ET (upperSpec 0 l)) k) :=
      measurable_pastMap runMeasStatement hbB (upperSpec 0 l) (fun j _ => (hETs (upperSpec 0 l) hprog).1 j)
        (fun j _ ω => hregS j ω) k le_rfl
    have hpm : Measurable (pastMap κ b jumps (sspec v l) (E (sspec v l)) k) :=
      Measurable.of_comap_le ((hE _ hprog).2.1 k)
    have hae : pastMap κ B JB (upperSpec 0 l) (ET (upperSpec 0 l)) k =ᵐ[P]
        pastMap κ b jumps (sspec v l) (E (sspec v l)) k := by
      filter_upwards [hrun] with ω hr
      funext i
      simp only [pastMap]
      rw [hr k, trState_retained]
    filter_upwards [StagedReg.ae_condExpKernel_eq_of_ae_eq hpm' hpm hae] with ω₀ h
    rw [pastSigma_eq_comap, h, ← pastSigma_eq_comap]
  -- almost sure facts under the retained kernel
  have h𝒢 := (hE _ hprog).2.1 k
  have hfreeQ := KernelTower.ae_ae_condExpKernel_of_ae h𝒢
    (ae_all_iff.2 fun q : ℚ => hfree κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER (q : ℝ))
  have hphysQ := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hphys
  have hpropQ := KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hpropT
  filter_upwards [hbase, hK, hrun, hfreeQ, hphysQ, hpropQ, (hER _ hprog).ae_pieceRegular]
    with ω₀ hb₀ hK₀ hr₀ hfr₀ hph₀ hpr₀ hreg₀
  intro c θ hcθ b' J' h' hb' hT' hG'
  have hcθT : (ExplState.run κ B JB (upperSpec 0 l) (fun j => ET (upperSpec 0 l) j ω₀) (k + 1)).2.2.2.1 k =
      some (trChart v c, θ) := by
    rw [hr₀ (k + 1), trState_launches]
    show trLaunch v _ = _
    rw [hcθ]
    rfl
  have hG'T : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ B JB (upperSpec 0 l) (ET (upperSpec 0 l)) k) ω₀)
      h' b' J' := by rw [hK₀]; exact hG'
  obtain ⟨m, EL, ⟨hm, hlm, hent, hword, hst, hregL, -, -⟩, hlift⟩ := hb₀ (trChart v c) θ hcθT b' J' h' hb'
    (fun ω => isChartTransport_trChart (hT' ω) v) hG'T
  rw [hK₀] at hregL hlift
  replace hst := isStagedHistory_congr_measure hK₀ hst
  -- the largest real point of the history
  have hnot := stStatus_ne_done_of_launches _ _ hcθ
  have hPc : IsCompact (prefixPhysSet κ b jumps (sspec v l) (fun j => E (sspec v l) j ω₀) k) :=
    isCompact_prefixPhysSet_run _ _ hreg₀ k hnot
  set Pk := prefixPhysSet κ b jumps (sspec v l) (fun j => E (sspec v l) j ω₀) k with hPk
  have hvP : (v : ℂ) ∈ Pk := Or.inl (Or.inl rfl)
  have hbdd : BddAbove {x : ℝ | (x : ℂ) ∈ Pk} := by
    obtain ⟨R, hR⟩ := hPc.isBounded.exists_norm_le
    exact ⟨R, fun x hx => (Real.le_norm_self x).trans (by simpa using hR _ hx)⟩
  have hRmax : realMax (upperPrefix κ B JB ET 0 l k ω₀) = realMax (arcPrefix κ b jumps E v l k ω₀) - v := by
    rw [hpre ω₀ hr₀, ← hPk]
    have htr := realMax_translate (A := Pk) v ⟨v, hvP⟩ hbdd
    refine htr.trans ?_
    unfold arcPrefix
    rw [← hPk, realMax_union_Icc hvP hbdd]
  refine ⟨m, EL, ⟨hm, hlm, ?_, fun x hx hxJ => ?_, hst, hregL⟩, ?_⟩
  · rw [hRmax] at hent
    exact isRightEntryValue_of_trChart hent
  · rcases hword x hx hxJ with h1 | h1 | ⟨y, ⟨hy, -⟩, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exact (lt_asymm hy.1 hy.2).elim
  · filter_upwards [hfr₀, hph₀, hpr₀, hlift] with ω hfr hph hpr hω
    obtain ⟨⟨y₀, hy₀, hy₀W, hfreeT⟩, hlt⟩ := hω
    have harc : ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ lowerWalkSet κ b jumps E ω := by
      rintro _ ⟨x, hx, rfl⟩
      have : ((x - v : ℝ) : ℂ) ∈ (fun z => z - (v : ℂ)) '' lowerWalkSet κ b jumps E ω := by
        rw [hph]; exact Or.inl ⟨x - v, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
      obtain ⟨w, hw, hwe⟩ := this
      have hwe' : w - (v : ℂ) = ((x - v : ℝ) : ℂ) := hwe
      have : w = (x : ℂ) := by
        calc w = (w - v) + v := by ring
          _ = _ := by rw [hwe']; push_cast; ring
      rwa [this] at hw
    refine ⟨harc, ?_, fun β₀ hβ₀ hβ₀0 hβ₀r => ?_⟩
    · -- a free real point left of the history
      have hA0 : realMin (arcPrefix κ b jumps E v l k ω₀) ≤ 0 := by
        have hbddA : BddBelow {x : ℝ | (x : ℂ) ∈ arcPrefix κ b jumps E v l k ω₀} := by
          have hAc : IsCompact (arcPrefix κ b jumps E v l k ω₀) :=
            hPc.union (isCompact_Icc.image Complex.continuous_ofReal)
          obtain ⟨R, hR⟩ := hAc.isBounded.exists_norm_le
          exact ⟨-R, fun x hx => by
            have := hR _ hx
            rw [Complex.norm_real, Real.norm_eq_abs] at this
            linarith [neg_abs_le x]⟩
        exact csInf_le hbddA (Or.inr ⟨0, ⟨le_rfl, hv.le⟩, rfl⟩)
      obtain ⟨q, hq⟩ := exists_rat_lt (realMin (arcPrefix κ b jumps E v l k ω₀))
      obtain ⟨y, hy, hyW⟩ := hfr q
      exact ⟨y, by linarith, by linarith, hyW⟩
    · -- the tail after the arc is the restarted walk
      obtain ⟨β', hβ', hβ'0, hβ'r⟩ := hpr
      have hW : range β₀ = ((↑) : ℝ → ℂ) '' Icc 0 v ∪ (fun z => z + (v : ℂ)) '' range β' := by
        rw [hβ₀r, hβ'r]
        have := congrArg (fun S => (fun z => z + (v : ℂ)) '' S) hph
        simp only [Set.image_union, Set.image_image, sub_add_cancel, Set.image_id'] at this
        rw [this]
        congr 1
        ext z
        simp only [Set.mem_image]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x + v, ⟨by linarith [hx.1], by linarith [hx.2]⟩, by push_cast; ring⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x - v, ⟨by linarith [hx.1], by linarith [hx.2]⟩, by push_cast; ring⟩
      obtain ⟨tv, htv, htail⟩ := tail_range_of_arc hβ₀ hβ₀0 hβ' hβ'0 hv hW
      have hβt : IsProperCurve (fun s => β₀ (tv + s) - v) := by
        refine ⟨(hβ₀.1.comp (continuous_const.add continuous_id)).sub continuous_const, fun s t hst => ?_,
          fun s => ?_, ?_⟩
        · have := hβ₀.2.1 (sub_left_injective hst)
          exact add_left_cancel this
        · show 0 ≤ (β₀ (tv + s) - v).im
          rw [Complex.sub_im, Complex.ofReal_im, sub_zero]; exact hβ₀.2.2.1 _
        · have h0 : Tendsto (fun s : ℝ≥0 => tv + s) atTop atTop :=
            tendsto_atTop_atTop.2 fun c => ⟨c, fun a ha => le_add_left ha⟩
          have h1 := hβ₀.2.2.2.comp h0
          refine tendsto_atTop_mono (fun s => ?_) (tendsto_atTop_add_const_right atTop (-|v|) h1)
          have := norm_sub_norm_le (β₀ (tv + s)) (v : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs] at this
          simp only [Function.comp_apply] at this ⊢
          linarith
      obtain ⟨tL, γ, hγL, hγ, hγ0, hγr, hγl⟩ := hlt _ hβt (by simp [htv]) (by rw [htail, hβ'r]; rfl)
      refine ⟨tv + tL, γ, ?_, hγ, hγ0, hγr, fun s => ?_⟩
      · have : β₀ (tv + tL) - v = ((realMax (upperPrefix κ B JB ET 0 l k ω₀) : ℝ) : ℂ) := hγL
        rw [hRmax] at this
        rw [← sub_add_cancel (β₀ (tv + tL)) (v : ℂ), this]
        push_cast; ring
      · have h1 := hγl s
        have h2 : Tendsto (fun w => (trChart v c).2.1 w + (v : ℂ)) (𝓝[H] (γ s - m))
            (𝓝 (β₀ (tv + (tL + s)) - v + v)) := h1.add_const _
        simp only [trChart, sub_add_cancel] at h2
        rw [add_assoc]
        exact h2

end InteractingSLE.Theorem14.SB.Lf
