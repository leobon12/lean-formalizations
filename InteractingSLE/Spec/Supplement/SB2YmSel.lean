/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcLive
import InteractingSLE.Spec.Supplement.SB2FsGlue

/-!
# The base event is a selector of the stage data

Packet PROVE-T14-SB2LIFT (round 37, decision D86, CANON's handoff R8.2 option (A)). CANON's base branch
(`Cz.base_branch`) gives the stage data at a flow stage `ℓ` on the base event
`Q ℓ = {upper launch, ℓ ≤ relOff ∨ (relOff + 2 = ℓ ∧ ZeroRoot)}`. To glue it with the other pieces
(`Fs.stageLawOn_glue`), the selector must be an event of the stage-`ℓ` line σ-algebra and of the completed retained
past at `ℓ`.

* `exists_measurableSet_ent_rand`: the entry events `R ∈ walk after n + 1 instructions` at a measurable random `R`, as
  measurable events on the event of regular pieces (the entry part of NOJUMP's
  `Nc.exists_measurableSet_relOffEvent_rand`).
* `even_of_flow`: B's flow instructions sit at even stages.
* **`exists_baseSelector`**: an event `Q'` of the retained past `stageMarks ℓ` with `Q' = Q ℓ` almost surely. The
  proof follows NOJUMP's `Nc.exists_liveEvent`. On the walk facts (`Nc.relOffEvent_of_walkGood`, `relOff_even`)
  the base event reads B's runs only through `ℓ`:
  `(∀ o, o + 2 ≤ ℓ → ¬ relOffEvent o) ∨ (∃ o, o + 2 = ℓ ∧ relOffEvent o ∧ ¬ Ent o)`. Its regularized reading is
  measurable, and it is frozen under the conditional laws given `stageMarks ℓ`, so it lies in the completion
  (`WalkLaw.mem_aeSigma_of_frozen`).
* **`baseSelector_usable`**: `Q'` is an event of the line σ-algebra `lineFiltC P 𝓖 0` of every line family `𝓖` of
  stage `ℓ` and of `aeSigma (stageMarks ℓ) P`: exactly the two selector conditions of `Fs.stageLawOn_glue`.
* `stageLawOn_congr_ae`: the stage data move to an almost surely smaller event, so the base piece on `Q ℓ` gives the
  base piece on `Q'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Sz

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf WalkSide Mz GW1Bookkeep GW1Conn Lk LuM LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The entry events at a random point, measurably** on the event of regular pieces. -/
theorem exists_measurableSet_ent_rand (hb : IsPiecewiseConstantBoundaryData b jumps) (θ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : ∀ j, Measurable (D j))
    (hDreg : ∀ j ω, IsRegularDriver (D j ω)) {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun i => D i ω) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (D j ω).1 (min (instrTime (boundaryWalkSpec b jumps θ true) j) (D j ω).2))
    {Rf : Ω → ℝ} (hRf : Measurable Rf) :
    ∃ T : ℕ → Set Ω, (∀ n, MeasurableSet (T n)) ∧
      ∀ ω ∈ M, ∀ n, (Ent κ θ b jumps (Rf ω) (fun i => D i ω) n ↔ ω ∈ T n) := by
  classical
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have hs1 : spec.1 = 0 := rfl
  obtain ⟨F, hFm, hF⟩ := Side.exists_measurable_piece_dense_code hb spec hDm hDreg hM hMreg
  obtain ⟨A, hAm, hA⟩ := Side.exists_measurable_arc_dense_code hb spec hDm hDreg
  set Ent' : ℕ → Set Ω := fun n => ⋃ k ∈ Finset.range (n + 1),
    ({ω | ((Rf ω : ℝ) : ℂ) ∈ closure (range (F k ω))} ∪
      {ω | ((Rf ω : ℝ) : ℂ) ∈ closure (range (A k ω))})
    with hEnt'
  refine ⟨Ent', fun n => Finset.measurableSet_biUnion _ fun k _ =>
    (Nc.measurableSet_mem_closure_range_rand (fun i => hFm k i) hRf).union
      (Nc.measurableSet_mem_closure_range_rand (fun i => hAm k i) hRf), fun ω hω n => ?_⟩
  unfold Ent
  rw [statePhysicalSet_run_eq]
  have hF' := hF ω hω
  have hA' := hA ω
  constructor
  · rintro ((h0 | h1) | h2)
    · refine mem_iUnion₂.2 ⟨0, Finset.mem_range.2 (by omega), Or.inl ?_⟩
      show ((Rf ω : ℝ) : ℂ) ∈ closure (range (F 0 ω))
      rw [hF' 0]
      exact Or.inl h0
    · obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h1
      refine mem_iUnion₂.2 ⟨k, hk, Or.inl ?_⟩
      show ((Rf ω : ℝ) : ℂ) ∈ closure (range (F k ω))
      rw [hF' k]
      exact Or.inr hkR
    · obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h2
      refine mem_iUnion₂.2 ⟨k, hk, Or.inr ?_⟩
      show ((Rf ω : ℝ) : ℂ) ∈ closure (range (A k ω))
      rw [hA' k]
      exact Or.inr hkR
  · intro h
    obtain ⟨k, hk, hkR⟩ := mem_iUnion₂.1 h
    rcases hkR with hkR | hkR
    · have hkR' : ((Rf ω : ℝ) : ℂ) ∈ closure (range (F k ω)) := hkR
      rw [hF' k] at hkR'
      rcases hkR' with h0 | h1
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨k, hk, h1⟩))
    · have hkR' : ((Rf ω : ℝ) : ℂ) ∈ closure (range (A k ω)) := hkR
      rw [hA' k] at hkR'
      rcases hkR' with h0 | h1
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (mem_iUnion₂.2 ⟨k, hk, h1⟩)

/-- B's flow instructions sit at even stages. -/
theorem even_of_flow {θ : ℝ} {ℓ : ℕ}
    (hw : (boundaryWalkSpec b jumps θ true).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) : ℓ % 2 = 0 := by
  rw [GW1Conn.getElem?_boundaryWalkSpec] at hw
  split_ifs at hw with h1 h2
  · exact h2
  · simp at hw

/-- **The entry stage at an offset event with no entry at the offset itself**: a zero root. -/
theorem zeroRoot_of_relOffEvent {θ : ℝ} {R : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ}
    (hr : relOffEvent κ θ b jumps R D o) (hne : ¬ Ent κ θ b jumps R D o) :
    ZeroRoot κ θ b jumps R D := by
  classical
  obtain ⟨hrel, e, he, hent⟩ := hr
  have hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) :=
    ⟨e, hent⟩
  obtain ⟨hin, hmin⟩ := entryStage_spec κ θ b jumps hex
  have hle : entryStage κ θ b jumps R D ≤ o + 1 := by
    by_contra hlt
    exact hmin e (by omega) hent
  have hgt : o < entryStage κ θ b jumps R D := by
    by_contra hle'
    exact hne (statePhysicalSet_mono (κ := κ) (θ := θ) (b := b) (jumps := jumps) (D := D)
      (by omega : entryStage κ θ b jumps R D + 1 ≤ o + 1) hin)
  have hev := relOff_even κ θ b jumps R D
  have hE : entryStage κ θ b jumps R D = o + 1 := by omega
  have hArc : ArcEntry κ θ b jumps R D := by unfold ArcEntry; omega
  refine ⟨hArc, fun hM => ?_⟩
  have ho := relOff_of_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hM
  have hs : startOff κ θ b jumps R D = o := by unfold startOff; omega
  omega

/-- **No entry at the offset at a zero root.** -/
theorem not_ent_of_zeroRoot {θ : ℝ} {R : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)))
    (hZ : ZeroRoot κ θ b jumps R D) : ¬ Ent κ θ b jumps R D (relOff κ θ b jumps R D) := by
  have ho := relOff_of_not_mark (κ := κ) (θ := θ) (b₁ := b) (J₁ := jumps) hZ.2
  have he := (startOff_eq κ θ b jumps R D).1 hZ.1
  obtain ⟨-, hmin⟩ := entryStage_spec κ θ b jumps hex
  exact hmin _ (by omega)

section

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The base event, as an event of the retained past at `ℓ`** (up to a null set). See the module docstring. -/
theorem exists_baseSelector (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hgood : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → Nc.WalkGood κ b jumps E u l k ω) :
    ∃ Q' : Set Ω, MeasurableSet[stageMarks κ b jumps E u l k ℓ] Q' ∧
      ∀ᵐ ω ∂P, (ω ∈ Q' ↔ (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
        (ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∨
          relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2 = ℓ ∧
            ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)))) := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  set su := Lu.upperSpec u l with hsudef
  set w := boundaryWalkSpec b jumps θ true with hwdef
  have hsu : IsBoundaryContinuedProgram su.2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  set Eu := StagedReg.regFam E su with hEudef
  set Ew := StagedReg.regFam E w with hEwdef
  have hEum : ∀ j, Measurable (Eu j) := (hE' su hsu).1
  have hEwm : ∀ j, Measurable (Ew j) := (hE' w hw).1
  have hℓev : ℓ % 2 = 0 := even_of_flow hwℓ
  -- the σ-algebra
  have h𝒢 : stageMarks κ b jumps E u l k ℓ ≤ mΩ := sup_le ((hE' su hsu).2.1 k) ((hE' w hw).2.1 ℓ)
  have hu𝒢 : pastSigma κ b jumps su Eu k ≤ stageMarks κ b jumps E u l k ℓ := le_sup_left
  have hw𝒢 : pastSigma κ b jumps w Ew ℓ ≤ stageMarks κ b jumps E u l k ℓ := le_sup_right
  -- the measurable pieces
  set LU : Set Ω := {ω | (ExplState.run κ b jumps su (fun j => Eu j ω) (k + 1)).2.2.2.1 k ≠ none} with hLUdef
  have hLU : MeasurableSet[pastSigma κ b jumps su Eu k] LU :=
    Lv.measurableSet_launch_pastSigma (spec := su) hb hEum (hreg' su) k
  obtain ⟨Rt, hRtm, hRt⟩ := Nc.exists_measurable_realMax_upper (κ := κ) hb (E := E) (u := u) (l := l)
    (hE su hsu).1 (hER su hsu) hu k
  have hRw' := WalkLaw.stagedPiecesRegular_regHist (hER w hw)
  obtain ⟨Mw, hMwae, hMwm, hMwp⟩ := hRw'.ae_pieceRegular.exists_measurable_mem
  choose S hSm hS using fun o => Nc.exists_measurableSet_relOffEvent_rand hb θ (D := Ew) hEwm (hreg' w) hMwm hMwp
    hRtm o
  obtain ⟨T, hTm, hT⟩ := exists_measurableSet_ent_rand (κ := κ) hb θ (D := Ew) hEwm (hreg' w) hMwm hMwp hRtm
  set SS : Set Ω := LU ∩ ((⋂ o, ({_ω | o + 2 ≤ ℓ}ᶜ ∪ (S o)ᶜ)) ∪ ⋃ o, ({_ω | o + 2 = ℓ} ∩ S o ∩ (T o)ᶜ))
    with hSSdef
  have hSS : MeasurableSet SS :=
    (h𝒢 _ (hu𝒢 _ hLU)).inter ((MeasurableSet.iInter fun o => (MeasurableSet.const _).compl.union (hSm o).compl).union
      (MeasurableSet.iUnion fun o => ((MeasurableSet.const _).inter (hSm o)).inter (hTm o).compl))
  -- the frozen event and its regularized reading
  set I : Set Ω := {ω | ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
    ((∀ o, o + 2 ≤ ℓ → ¬ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) o) ∨
      ∃ o, o + 2 = ℓ ∧ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) o ∧
        ¬ Ent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) o)} with hIdef
  set J : Ω → Prop := fun ω => ω ∈ LU ∧
    ((∀ o, o + 2 ≤ ℓ → ¬ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω))
        (fun i => Ew i ω) o) ∨
      ∃ o, o + 2 = ℓ ∧ relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω))
        (fun i => Ew i ω) o ∧
        ¬ Ent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω)) (fun i => Ew i ω) o)
    with hJdef
  set M : Set Ω := {ω | (∀ n, ExplState.run κ b jumps su (fun j => Eu j ω) n =
      ExplState.run κ b jumps su (fun j => E su j ω) n) ∧
    (∀ n, ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => E w j ω) n) ∧
    ω ∈ Mw ∧ (IsCompact (upperPrefix κ b jumps E u l k ω) → Rt ω = realMax (upperPrefix κ b jumps E u l k ω)) ∧
    (ω ∈ Lu.upperLaunchSet κ b jumps E u l k → IsCompact (upperPrefix κ b jumps E u l k ω))} with hMdef
  have hMP : ∀ᵐ ω ∂P, ω ∈ M := by
    filter_upwards [hrun' su hsu, hrun' w hw, hMwae, hRt, hgood] with ω h1 h2 h3 h4 h5
    refine ⟨h1, h2, h3, h4, fun hl => ?_⟩
    obtain ⟨pA, hp, -, -, -, hpA⟩ := (h5 hl).upath
    exact hpA ▸ isCompact_Icc.image_of_continuousOn hp
  have hpre : ∀ ω ∈ M, upperPrefix κ b jumps (StagedReg.regFam E) u l k ω = upperPrefix κ b jumps E u l k ω := by
    intro ω hω
    unfold upperPrefix SB.prefixPhysSet
    show _ ∪ _ = _
    rw [show ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
      (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
      ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω) k
      from hω.1 k]
  have hent_congr : ∀ (R : ℝ) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (o : ℕ),
      (∀ n ≤ o + 1, ExplState.run κ b jumps w D n = ExplState.run κ b jumps w D' n) →
      (Ent κ θ b jumps R D o ↔ Ent κ θ b jumps R D' o) := by
    intro R D D' o hDD
    unfold Ent
    rw [hDD (o + 1) le_rfl]
  have hIJ : ∀ ω ∈ M, (ω ∈ I ↔ J ω) := by
    intro ω hω
    have hlu : ω ∈ Lu.upperLaunchSet κ b jumps E u l k ↔ ω ∈ LU := by
      show _ ≠ none ↔ _ ≠ none
      rw [hω.1 (k + 1)]
    have hro : ∀ o, (relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) o ↔
        relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω))
          (fun i => Ew i ω) o) := fun o => by
      rw [hpre ω hω]
      exact relOffEvent_congr _ _ _ _ _ o fun n _ => (hω.2.1 n).symm
    have hen : ∀ o, (Ent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω) o ↔
        Ent κ θ b jumps (realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω)) (fun i => Ew i ω) o) :=
      fun o => by
        rw [hpre ω hω]
        exact hent_congr _ o fun n _ => (hω.2.1 n).symm
    show (_ ∧ _) ↔ (_ ∧ _)
    rw [hlu]
    refine and_congr_right fun _ => or_congr (forall_congr' fun o => imp_congr_right fun _ => not_congr (hro o))
      (exists_congr fun o => and_congr_right fun _ => and_congr (hro o) (not_congr (hen o)))
  have hEM : ∀ ω ∈ M, (ω ∈ I ↔ ω ∈ SS) := by
    intro ω hω
    rw [hIJ ω hω]
    have hR : ω ∈ LU → realMax (upperPrefix κ b jumps (StagedReg.regFam E) u l k ω) = Rt ω := fun h4 => by
      have hlu : ω ∈ Lu.upperLaunchSet κ b jumps E u l k := by
        show _ ≠ none
        rw [← hω.1 (k + 1)]; exact h4
      rw [hpre ω hω, hω.2.2.2.1 (hω.2.2.2.2 hlu)]
    constructor
    · rintro ⟨h4, h5⟩
      rw [hR h4] at h5
      refine ⟨h4, ?_⟩
      rcases h5 with h5 | ⟨o, ho, h6, h7⟩
      · refine Or.inl (mem_iInter.2 fun o => ?_)
        by_cases ho : o + 2 ≤ ℓ
        · exact Or.inr fun hSo => h5 o ho ((hS o ω hω.2.2.1).2 hSo)
        · exact Or.inl ho
      · exact Or.inr (mem_iUnion.2 ⟨o, ⟨ho, (hS o ω hω.2.2.1).1 h6⟩, fun hTo => h7 ((hT ω hω.2.2.1 o).2 hTo)⟩)
    · rintro ⟨h4, h5⟩
      refine ⟨h4, ?_⟩
      rw [hR h4]
      rcases h5 with h5 | h5
      · refine Or.inl fun o ho hro => ?_
        rcases mem_iInter.1 h5 o with h6 | h6
        · exact h6 ho
        · exact h6 ((hS o ω hω.2.2.1).1 hro)
      · obtain ⟨o, ⟨ho, h6⟩, h7⟩ := mem_iUnion.1 h5
        exact Or.inr ⟨o, ho, (hS o ω hω.2.2.1).2 h6, fun he => h7 ((hT ω hω.2.2.1 o).1 he)⟩
  -- frozen under the conditional laws
  have hfrU := Retain.ae_ae_run_eq su (WalkLaw.stagedPiecesRegular_regHist (hER su hsu)) h𝒢 hu𝒢
  have hfrW : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (stageMarks κ b jumps E u l k ℓ) ω₀), ∀ n, n ≤ ℓ →
      ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => Ew j ω₀) n := by
    have hn : ∀ n, ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (stageMarks κ b jumps E u l k ℓ) ω₀), n ≤ ℓ →
        ExplState.run κ b jumps w (fun j => Ew j ω) n = ExplState.run κ b jumps w (fun j => Ew j ω₀) n := by
      intro n
      by_cases hnℓ : n ≤ ℓ
      · filter_upwards [Retain.ae_ae_run_eq w hRw' h𝒢 ((pastSigma_mono _ _ hnℓ).trans hw𝒢)] with ω₀ hx
        filter_upwards [hx] with ω hω _
        exact hω
      · exact Eventually.of_forall fun _ => Eventually.of_forall fun _ h => absurd h hnℓ
    filter_upwards [ae_all_iff.2 hn] with ω₀ hx
    exact ae_all_iff.2 fun n => hx n
  have hfr : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (stageMarks κ b jumps E u l k ℓ) ω₀), (ω ∈ I ↔ ω₀ ∈ I) := by
    filter_upwards [Nc.ae_ae_mem_iff (P := P) h𝒢 (hu𝒢 _ hLU), hfrU, hfrW,
      Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hMP, hMP] with ω₀ h1 h3 h4 h5 hM₀
    filter_upwards [h1, h3, h4, h5] with ω g1 g3 g4 g5
    rw [hIJ ω g5, hIJ ω₀ hM₀]
    have hup : upperPrefix κ b jumps (StagedReg.regFam E) u l k ω =
        upperPrefix κ b jumps (StagedReg.regFam E) u l k ω₀ := by
      unfold upperPrefix SB.prefixPhysSet
      show _ ∪ _ = _ ∪ _
      rw [show ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
        (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
        ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
          (fun j => StagedReg.regFam E ⟨u, true, scheduleProgram 0 l⟩ j ω₀) k from g3]
    show (ω ∈ LU ∧ _) ↔ (ω₀ ∈ LU ∧ _)
    rw [g1, hup]
    refine and_congr_right fun _ => or_congr (forall_congr' fun o => imp_congr_right fun ho => not_congr
      (relOffEvent_congr _ _ _ _ _ o fun n hn => g4 n (by omega)))
      (exists_congr fun o => and_congr_right fun ho => and_congr
        (relOffEvent_congr _ _ _ _ _ o fun n hn => g4 n (by omega))
        (not_congr (hent_congr _ o fun n hn => g4 n (by omega))))
  have hmem := WalkLaw.mem_aeSigma_of_frozen (P := P) h𝒢 (E := I) hSS hMP hEM hfr
  obtain ⟨G', hG'm, hG'e⟩ := hmem
  refine ⟨G', hG'm, ?_⟩
  -- the intrinsic characterization
  filter_upwards [hG'e.mem_iff, hgood] with ω hG hg
  rw [← hG]
  show (_ ∧ _) ↔ (_ ∧ _)
  refine and_congr_right fun hup => ?_
  have hgω := hg hup
  have hre := relOff_even κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω)
  have hrr : relOffEvent κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω)
      (relOff κ θ b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E w i ω)) :=
    Nc.relOffEvent_of_walkGood hgω
  have hex : ∃ n, ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) ∈
      statePhysicalSet 0 (ExplState.run κ b jumps w (fun i => E w i ω) (n + 1)) := by
    obtain ⟨-, e, -, he⟩ := hrr
    exact ⟨e, he⟩
  constructor
  · rintro (h5 | ⟨o, ho, h6, h7⟩)
    · refine Or.inl ?_
      by_contra hlt
      exact h5 _ (by omega) hrr
    · refine Or.inr ⟨by rw [h6.1]; exact ho, zeroRoot_of_relOffEvent h6 h7⟩
  · rintro (hle | ⟨ho, hZ⟩)
    · exact Or.inl fun o ho hro => by rw [hro.1] at hle; omega
    · exact Or.inr ⟨_, ho, hrr, not_ent_of_zeroRoot hex hZ⟩

/-- **The base selector is usable**: an event of the line σ-algebra of every line family of stage `ℓ` and of the
completed retained past at `ℓ` (the two selector conditions of `Fs.stageLawOn_glue`), equal almost surely to the
base event. -/
theorem baseSelector_usable (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (hgood : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k → Nc.WalkGood κ b jumps E u l k ω)
    {𝓖 : Filtration ℝ≥0 mΩ}
    (h𝓖 : 𝓖 0 = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) :
    ∃ Q' : Set Ω, MeasurableSet[lineFiltC P 𝓖 0] Q' ∧
      MeasurableSet[aeSigma (stageMarks κ b jumps E u l k ℓ) P] Q' ∧
      ∀ᵐ ω ∂P, (ω ∈ Q' ↔ (ω ∈ Lu.upperLaunchSet κ b jumps E u l k ∧
        (ℓ ≤ relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ∨
          relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 2 = ℓ ∧
            ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)))) := by
  obtain ⟨Q', hQm, hQe⟩ := exists_baseSelector hb hE hER hu hlθ k ℓ hwℓ hgood
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hwℓ).1
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  obtain ⟨hE', -, -⟩ := StagedReg.regFam_spec hb hE hER
  have hSM : stageMarks κ b jumps E u l k ℓ ≤ 𝓖 0 := by
    rw [h𝓖]
    refine sup_le_sup le_rfl ?_
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := -(Real.pi / 2)) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ ℓ)
  have hmΩ : stageMarks κ b jumps E u l k ℓ ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 ℓ)
  exact ⟨Q', ⟨hmΩ _ hQm, Q', hSM _ hQm, EventuallyEq.rfl⟩, ⟨Q', hQm, EventuallyEq.rfl⟩, hQe⟩

end

section Stage

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)}
  {k ℓ : ℕ}

/-- **The stage data on an almost surely smaller event.** -/
theorem stageLawOn_congr_ae {𝓖 : Filtration ℝ≥0 mΩ} {A₁ : ℝ≥0 → Ω → Set ℂ} {C C' : Set Ω} {β : Ω → BoundaryWord}
    {S : Set Lv.WordProfile} (hC : ∀ᵐ ω ∂P, ω ∈ C' → ω ∈ C)
    (hS : Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C β S) :
    Fs.StageLawOn κ b jumps P h E u l k ℓ 𝓖 A₁ C' β S := by
  obtain ⟨⟨K, G, Y, M, hlaw, hcov⟩, hβm, ht, htc, hL⟩ := hS
  refine ⟨⟨K, G, Y, M, hlaw, ?_⟩, hβm, ht, ?_, ?_⟩
  · filter_upwards [hcov, hC] with ω h1 h2 h3 using h1 (h2 h3)
  · filter_upwards [htc, hC] with ω h1 h2 h3 using h1 (h2 h3)
  · filter_upwards [hL, hC] with ω h1 h2 h3 using h1 (h2 h3)

end Stage

end InteractingSLE.Theorem14.SB.Sz
