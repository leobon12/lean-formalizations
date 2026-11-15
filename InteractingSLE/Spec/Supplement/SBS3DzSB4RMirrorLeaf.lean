/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RMirrorLeaf
import InteractingSLE.Spec.Supplement.SBS3DyInst
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen
import InteractingSLE.Spec.Supplement.SBS3DySBLyLeaf

/-!
# Successor of `SB4RMirrorLeaf` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB4RMirrorLeaf` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `scheduleRelativeTailR_left_liftLe`;
* `scheduleRelativeTailR_leftLe`.
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

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule
open Sec7.FlowReflect (reflData reflJumps reflField)

/-- **SB4's distinct-seed leaf, left-walk half, with R95's premise.** -/
theorem scheduleRelativeTailR_left_liftLe (hC : SB2LeftLaunchLiftStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2))
    (h41 : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) {v : ℝ} (hv : 0 ≤ v)
    (hθ : ∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2))
    (hR : ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ))
    (hH : ∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) :
    ScheduleRelativeTailRLe κ b jumps P E v l (fun ω => leftSideOf (leftWalkSet κ b jumps E ω)) := by
  intro k hk hprev
  have hprog : IsBoundaryContinuedProgram (sspec v l).2.2 :=
    GW2Sched.isBoundaryContinuedProgram_scheduleProgram (fun p hp => Ico_subset_Icc_self (hθ p hp)) 0
  have hEu := hE _ hprog
  have hRu := hreg _ hprog
  have hprogL : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (Real.pi / 2) false).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨by linarith [Real.pi_pos], le_rfl⟩ false
  obtain ⟨a, ham, hareg⟩ := Readout.exists_schedule_launch_param_of_side_version hb hEu.1 hRu hk
    (S := fun ω => leftSideOf (leftWalkSet κ b jumps E ω))
    (fun _ hz => (lt_irrefl (0 : ℝ)) (show (0 : ℝ) < 0 from hz.1.1))
    ((Readout.ae_isOpen_physSet_sides (hreg _ hprogL)).mono fun _ hω => hω.2)
    (Side.exists_measurable_physSet_side_versions hb _ (hE _ hprogL).1 (hreg _ hprogL)).2
  have hF := measurableSet_launchEvent_schedule (κ := κ) (b := b) (jumps := jumps) (x := v) (E (sspec v l)) hk
  refine ⟨⟨pastSigma κ b jumps (sspec v l) (E (sspec v l)) k, hEu.2.1 k⟩, a,
    (hEu.2.1 k _ hF).nullMeasurableSet, ham, hareg, ?_⟩
  have hleftP : ∀ᵐ ω ∂P, ω ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k →
      arcPrefix κ b jumps E v l k ω ∩ leftSideOf (leftWalkSet κ b jumps E ω) = ∅ :=
    hprev.mono fun ω hω _ => inter_leftSideOf_union_real hω
  have hout := hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg v l k hv hl hθ hR hleftP
  have hβQ := KernelTower.ae_ae_condExpKernel_of_ae (hEu.2.1 k)
    (hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg)
  have havQ := ae_ae_prefix_avoid hEu hRu hprev
  filter_upwards [hout, hβQ, havQ, Retain.ae_launch_word_cases hκ hb hEu hRu k,
    Retain.ae_launch_chosenTrace_readout h13 hκ hEu hRu hk, hRu.ae_pieceRegular,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (hEu.2.1 k) hF.compl]
    with ω₀ hout₀ hβ₀ hav₀ hwc hread hreg₀ hnotF
  by_cases hω₀ : ω₀ ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k
  swap
  · exact Or.inl ((hnotF hω₀).mono fun ω hω hωF => absurd hωF hω)
  obtain ⟨⟨c, θ⟩, hlaunch⟩ := Option.ne_none_iff_exists'.1 hω₀
  obtain ⟨hcc, bc, jc, hl₀, hbc, hct, hG, hfl₀, hcases⟩ := hwc c θ hlaunch
  obtain ⟨f, -, hf, hfc, -, hreadW⟩ := hread c θ hlaunch
  obtain ⟨m, EL, hout', hliftω⟩ := hout₀ c θ hlaunch bc jc hl₀ hbc hct hG
  obtain ⟨hm, hlm, hent, hword, hst, hregL⟩ := hout'
  -- the retained history at `ω₀` and its reflection
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    exists_path_arcPrefix (κ := κ) (b := b) (jumps := jumps) hv l (fun j => E (sspec v l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = arcPrefix κ b jumps E v l k ω₀ := hpA
  have hc := (eq_launch_of_launches (sspec v l) (fun j => E (sspec v l) j ω₀) hlaunch).2.2
  have hnot := stStatus_ne_done_of_launches _ _ hlaunch
  have hAc : IsCompact (arcPrefix κ b jumps E v l k ω₀) :=
    (isCompact_prefixPhysSet_run _ _ hreg₀ k hnot).union (isCompact_Icc.image Complex.continuous_ofReal)
  set A := arcPrefix κ b jumps E v l k ω₀ with hAdef
  -- the reflected chart is a right entry chart of the reflected history
  have hrc : IsRightEntryChart (Supp9B.refl '' A) (realMax (Supp9B.refl '' A)) ((reflChart c).recenter (-m)) := by
    rw [realMax_refl_image, reflChart_recenter]
    apply isRightEntryChart_reflChart
    rw [hc]
    refine isLeftEntryChart_runChart _ _ hreg₀ k hnot hAc (Lw.fillH_union_real _ _) ?_
    have hsc : stChart (ExplState.run κ b jumps (sspec v l) (fun i => E (sspec v l) i ω₀) k) = c := hc.symm
    rw [hsc]; exact hent
  -- the reflected readout
  have hf' : ∀ z ∈ Hbar, Tendsto (reflChart c).2.1 (𝓝[H] z) (𝓝 (Supp9B.refl (f (Supp9B.refl z)))) := by
    intro z hz
    have hz' : Supp9B.refl z ∈ Hbar := by
      show 0 ≤ (Supp9B.refl z).im; rw [refl_im]; exact hz
    exact (continuous_refl.tendsto _).comp ((hf _ hz').comp (tendsto_refl_nhdsWithin_H z))
  have hfc' : ContinuousOn (fun z => Supp9B.refl (f (Supp9B.refl z))) Hbar :=
    continuous_refl.comp_continuousOn (hfc.comp continuous_refl.continuousOn fun z hz => by
      show 0 ≤ (Supp9B.refl z).im; rw [refl_im]; exact hz)
  have hflR := Sec7.StripWall.isFlowLineDriver_reflect hbc hfl₀
  have hread' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      Supp9B.refl '' schedulePiece κ b jumps v l (fun j => E (sspec v l) j ω) k ⊆
        (fun z => Supp9B.refl (f (Supp9B.refl z))) ''
          (GW2aSingle.chosenTrace (-fun t ω => (E (sspec v l) k ω).1 t) (fun ω => (E (sspec v l) k ω).2) ω ''
            {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (schedDelta 0 l k) (E (sspec v l) k ω).2}) := by
    filter_upwards [hreadW bc jc hl₀ hfl₀, ae_chosenTrace_neg_eq h13 hκ hbc hfl₀] with ω hω hneg
    rw [hω.2.1]
    rintro _ ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, rfl⟩
    refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
    simp only []
    rw [hneg t (ht.trans (min_le_right _ _)), refl_refl]
  -- the reflected lower walk, lift and closed left side
  have hβ' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      ∃ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ ∧ β₀ 0 = 0 ∧ range β₀ = Supp9B.refl '' leftWalkSet κ b jumps E ω :=
    hβ₀.mono fun ω ⟨βL, hβL, hβL0, hβLr⟩ => ⟨reflectCurve βL, isProperCurve_reflectCurve hβL,
      by simp [reflectCurve, hβL0, Supp9B.refl], by
        rw [show leftWalkSet κ b jumps E ω = range βL from hβLr.symm]; exact range_comp _ _⟩
  have hlift' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      (∃ y : ℝ, y < 0 ∧ y < realMin (Supp9B.refl '' A) ∧ (y : ℂ) ∉ Supp9B.refl '' leftWalkSet κ b jumps E ω) ∧
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = Supp9B.refl '' leftWalkSet κ b jumps E ω →
          IsTailLiftOf (reflChart c) (realMax (Supp9B.refl '' A)) m β₀
            (relWalkSet κ (affData 1 m (reflData bc)) (affJumps 1 m (reflJumps jc)) EL ω) := by
    filter_upwards [hliftω] with ω ⟨⟨y, hy0, hyA, hyB⟩, hlt⟩
    refine ⟨⟨-y, by linarith, by rw [realMin_refl_image]; linarith, ?_⟩, fun β₀ hβ hβ0 hβr => ?_⟩
    · rintro ⟨z, hz, hzy⟩
      have : z = (y : ℂ) := by
        have := congrArg Supp9B.refl hzy
        rwa [refl_refl, refl_ofReal, neg_neg] at this
      exact hyB (this ▸ hz)
    · have hr : range (reflectCurve β₀) = leftWalkSet κ b jumps E ω := by
        rw [show reflectCurve β₀ = Supp9B.refl ∘ β₀ from rfl, range_comp, hβr, refl_image_refl_image]
      have h1 := hlt (reflectCurve β₀) (isProperCurve_reflectCurve hβ)
        (by simp [reflectCurve, hβ0, Supp9B.refl]) hr
      rw [reflectCurve_reflectCurve] at h1
      rw [realMax_refl_image]
      exact h1
  have hAL' : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = Supp9B.refl '' leftWalkSet κ b jumps E ω →
        Supp9B.refl '' A ⊆ closedLeftSide β₀ := by
    filter_upwards [hav₀] with ω havω β₀ hβ hβ0 hβr
    have hA' : Supp9B.refl '' A = Supp9B.refl '' prefixPhysSet κ b jumps (sspec v l)
        (fun j => E (sspec v l) j ω₀) k ∪ ((↑) : ℝ → ℂ) '' Icc (-v) 0 := by
      rw [hAdef, arcPrefix, image_union, refl_image_ofReal_Icc]
    rw [hA']
    refine subset_closedLeftSide_of_avoid' hβ hβ0 ?_ (negReal_subset_closedLeftSide hβ hβ0 v) ?_
    · rintro _ ⟨z, hz, rfl⟩
      rcases hcl hz with h1 | h1
      · refine Or.inl ?_
        have h2 := mem_closure_image continuous_refl.continuousAt h1
        refine closure_mono ?_ h2
        rintro _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
        exact ⟨⟨w, hw1, rfl⟩, refl_mem_H hw2⟩
      · exact Or.inr (by rw [← refl_image_ofReal_Icc]; exact ⟨z, h1, rfl⟩)
    · rw [hβr, rightSideOf_refl_image, ← image_inter refl_injective, havω, image_empty]
  -- the geometry in the reflected plane, then reflected back
  have hgeoR := ae_relTailGeometry_of_path h13 hκ (pA := fun s => Supp9B.refl (pA s))
    (continuous_refl.comp_continuousOn hp) (by simp [hp0, Supp9B.refl])
    (fun s hs => by simpa using hpH s hs) (by rw [← hpA', image_image]) (isConformal_reflChart hcc) hm hrc
    hf' hfc' hflR (Apiece := fun ω => Supp9B.refl '' schedulePiece κ b jumps v l (fun j => E (sspec v l) j ω) k)
    (S := fun ω => rightSideOf (Supp9B.refl '' leftWalkSet κ b jumps E ω))
    (B := fun ω => Supp9B.refl '' leftWalkSet κ b jumps E ω)
    (Wrel := fun ω => relWalkSet κ (affData 1 m (reflData bc)) (affJumps 1 m (reflJumps jc)) EL ω)
    (T := schedDelta 0 l k) hread' hβ' hlift' hAL' (Eventually.of_forall fun _ => subset_rfl)
  have hgeo : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (sspec v l) (E (sspec v l)) k) ω₀),
      HasRelTailGeometry (schedulePiece κ b jumps v l (fun j => E (sspec v l) j ω) k)
        (leftSideOf (leftWalkSet κ b jumps E ω))
        (relWalkSet κ (affData 1 m (reflData bc)) (affJumps 1 m (reflJumps jc)) EL ω) m
        (fun t => aff 1 m (GW2aSingle.chosenTrace (-fun t ω => (E (sspec v l) k ω).1 t)
          (fun ω => (E (sspec v l) k ω).2) ω t)) (E (sspec v l) k ω).2 := by
    filter_upwards [hgeoR] with ω hω
    have := hω.refl_image
    rwa [refl_image_refl_image, rightSideOf_refl_image, refl_image_refl_image] at this
  rcases hcases with hzero | hpos
  · refine Or.inl ?_
    filter_upwards [hgeo, hzero] with ω hg hz _
    rw [hz.1] at hg
    exact hg.hasActualTailSewing_zero
  · -- the reflected relative pair is an instance of the amended SB3
    have hangles' : ∀ p ∈ reflAngles l, -(Real.pi / 2) < p.1 := fun p hp => by
      have := (hθ _ (mem_reflAngles.1 hp)).2
      linarith
    have hgaps' : ∀ p ∈ reflAngles l, ∀ q ∈ reflAngles l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ :=
      fun p hp q hq => by
        have := h41 _ (mem_reflAngles.1 hp) _ (mem_reflAngles.1 hq)
        rwa [show -p.1 - -q.1 = -(p.1 - q.1) by ring, abs_neg] at this
    obtain ⟨q, hq, hθq⟩ := exists_mem_of_scheduleProgram_getElem? 0 l k
      (eq_launch_of_launches (sspec v l) (fun j => E (sspec v l) j ω₀) hlaunch).1
    obtain ⟨hpc, hGF, hFL⟩ := relFlowLine_of_isFlowLineDriver h13 hκ
      (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hbc) hflR m
    have hI := isRelSB3Instance_of_word hκ hκ4 hangles' hgaps' (bridge_reflect hR hH)
      ⟨hpc, hGF, fun _ => ⟨hst, hregL⟩, hm, ⟨(-q.1, q.2), mem_reflAngles.2 (by simpa using hq), by rw [hθq]⟩,
        hword, hFL, hpos⟩
    exact Or.inr ⟨fun ω => affField m one_pos (reflField (hl₀ ω)), affData 1 m (reflData bc),
      affJumps 1 m (reflJumps jc), EL, m, -θ, _, _,
      ⟨⟨hI, Lz.lowerLeftAdmissible_of_activeHighWord hκ hκ4 hangles' (bridgeLeft_reflect hR) hlm hword⟩,
        show -θ ≤ Real.pi / 2 by rw [hθq]; linarith [(hθ _ hq).1]⟩,
      hgeo.mono fun _ hω _ => hω⟩

/-- **The left-walk half in the round-1 form** (the pair of mirror inputs). -/
theorem scheduleRelativeTailR_leftLe (hSB2L : SB2LeftLaunchStatement.{u}) (hLiftL : SB2LeftTailLiftStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {l : List (ℝ × ℝ≥0)} (hl : l.Pairwise (fun p q => p.2 < q.2))
    (h41 : ∀ p ∈ l, ∀ q ∈ l, |p.1 - q.1| < 2 * sleLambda κ / chiC κ) {v : ℝ} (hv : 0 ≤ v)
    (hθ : ∀ p ∈ l, p.1 ∈ Ico (-(Real.pi / 2)) (Real.pi / 2))
    (hR : ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightRight κ (b x + Real.pi / 2 * chiC κ))
    (hH : ∀ p ∈ l, ∀ x ∈ Ioo 0 v, x ∉ jumps → -2 < cumWeightLeft κ (b x + p.1 * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightRight κ (b x + Real.pi / 2 * chiC κ)) :
    ScheduleRelativeTailRLe κ b jumps P E v l (fun ω => leftSideOf (leftWalkSet κ b jumps E ω)) :=
  scheduleRelativeTailR_left_liftLe (sb2LeftLaunchLiftStatement_of_pair hSB2L hLiftL) hPL h13 hκ hκ4 hb hh hcf hζ' hE
    hreg hl h41 hv hθ hR hH

end InteractingSLE.Theorem14.SB.Lf
