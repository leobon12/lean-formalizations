/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RPath
import InteractingSLE.Spec.Supplement.SB4RZero
import InteractingSLE.Spec.Supplement.SBLzAdm
import InteractingSLE.Spec.Supplement.SB4SewSides
import InteractingSLE.Spec.Theorem15D5Borel

/-!
# SB2(2)'s lifted lower tail and the conditional sewing geometry at one launch

Packet PROVE-T14-SB4LEAF. SB2(2) (ruling R99, `Lz.SB2LowerLaunchEntryAdmStatement`) links the actual lower walk `B`
and SB2(2)'s relative lower walk `EL` only as sets (`B ∩ D_A ⊆ relPhysSet ⊆ B`). The sewing frame needs the source's
pointwise statement (supplement p. 631: "Erase `B` through its unique visit to `R` and lift the remaining tail into
`D_A`. The result is again a finite simple proper lower walk of the retained conditional field"; p. 632: "the actual
completed lower tail has an injective, proper lift"). This file:

* `IsTailLiftOf c R m β₀ Wrel`: the tail of the proper parametrization `β₀` of `B` after its visit to `R` is the chart
  boundary image of a proper curve from `0` with range `Wrel` (read in the recentred chart `c − (−m)`);
* `IsLowerLaunchOutput`: SB2(2)'s per-witness output (R99 form), and `exists_isLowerLaunchOutput_of_adm`;
* **`SB2LowerTailLiftStatement`** (named input): from SB2(2)'s output, almost surely under the retained kernel, the
  lower tail lifts pointwise to the relative walk, and `B` misses some real point left of `A ∪ {0}` (the free collar
  of the reflected frame);
* `subset_closedLeftSide_of_avoid`: a history adherent to its interior points (and the bridge) that avoids the right
  side of `B` is on the closed left of `B`;
* **`ae_relTailGeometry_of_lift`**: at a retained launch, the S1-free relative sewing geometry
  (`Leaf.HasRelTailGeometry`) holds conditionally almost surely for every witness of the conditional flow law.
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

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule

/-! ### The lift -/

/-- **The tail of `β₀` after its visit to `R` lifts to `Wrel`**: `β₀` visits `R` at `t_L`, and a proper curve `γ`
from `0` with range `Wrel` has chart boundary values `β₀ (t_L + s)` at `γ s − m` (the relative walk is read in the
chart `c` recentred at its entry value `−m`). -/
def IsTailLiftOf (c : Chart) (R m : ℝ) (β₀ : ℝ≥0 → ℂ) (Wrel : Set ℂ) : Prop :=
  ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), β₀ tL = (R : ℂ) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ range γ = Wrel ∧
    ∀ s : ℝ≥0, Tendsto c.2.1 (𝓝[H] (γ s - m)) (𝓝 (β₀ (tL + s)))

section Output

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
  (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)

/-- **SB2(2)'s output for one witness** (the conclusion of `Lz.SB2LowerLaunchEntryAdmStatement`, ruling R99, at the
retained realization `ω₀` with launch chart `c` and conditional data `b'` off `J'`, field `h'`). -/
def IsLowerLaunchOutput : Prop :=
  m ≤ 0 ∧
    (∀ y, y ≤ m → y ∉ affJumps 1 m J' →
      -2 < cumWeightLeft κ (affData 1 m b' y + -(Real.pi / 2) * chiC κ)) ∧
    IsRightEntryValue c (realMax (upperPrefix κ b jumps E u l k ω₀)) (-m) ∧
    IsActiveHighWord κ b jumps u l b' J' m ∧
    IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL ∧
    StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (relLowerSpec b' J' m) EL ∧
    (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      WalkRightAdds κ (affData 1 m b') (affJumps 1 m J') (fun _ => EL) ω) ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      lowerWalkSet κ b jumps E ω ∩ (H \ fillH (upperPrefix κ b jumps E u l k ω)) ⊆
          relPhysSet κ (affData 1 m b') (affJumps 1 m J') (c.recenter (-m))
            (relLowerSpec b' J' m) (fun j => EL j ω) ∧
        relPhysSet κ (affData 1 m b') (affJumps 1 m J') (c.recenter (-m))
            (relLowerSpec b' J' m) (fun j => EL j ω) ⊆ lowerWalkSet κ b jumps E ω

end Output

/-- **The setting of SB2(2)** (the hypotheses of `Lz.SB2LowerLaunchEntryAdmStatement`, ruling R99/R96) for a
proposition `C` about each retained launch and each witness of its conditional launch law. -/
def SB2LowerSetting (C : ℝ → (ℝ → ℝ) → Finset ℝ → ∀ {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
    (ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) → ℝ → List (ℝ × ℝ≥0) → ℕ → Ω → Chart →
    (ℝ → ℝ) → Finset ℝ → (Ω → DistOn upperHalfPlaneOpens) → Prop) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' J' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
            h' b' J' →
          C κ b jumps P E u l k ω₀ c b' J' h'

/-- SB2(2) in R99's form gives its output for every witness. -/
theorem sb2LowerSetting_output_of_adm (hSB2 : Lz.SB2LowerLaunchEntryAdmStatement.{u}) :
    SB2LowerSetting.{u} (fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
      ∃ (m : ℝ) (EL : ℕ → _ → (ℝ≥0 → ℝ) × ℝ≥0∞), IsLowerLaunchOutput κ b jumps P E u l k ω₀ c b' J' h' m EL) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [hSB2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨m, EL, hm, hlm, hent, hword, hst, hreg, hadd, hlink⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG'
  exact ⟨m, EL, hm, hlm, hent, hword, hst, hreg, hadd, hlink⟩

/-- **Named input: SB2(2)'s lower tail lifts pointwise** (supplement p. 631: "Erase `B` through its unique visit to
`R` and lift the remaining tail into `D_A`. The result is again a finite simple proper lower walk of the retained
conditional field"; p. 632: "the actual completed lower tail has an injective, proper lift"). In SB2(2)'s setting,
for every witness and every output `(m, EL)` of SB2(2) (R99 form, whose link is only set-level), almost surely under
the retained kernel: the lower walk misses a real point left of `0` and of the retained history (the free collar of
the reflected frame), and the tail of every proper parametrization of the lower walk from `0` after its visit to
`R = max (A ∩ ℝ)` is the chart boundary image of the relative walk (`IsTailLiftOf`). -/
def SB2LowerTailLiftStatement : Prop :=
  SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    ∀ (m : ℝ) (EL : ℕ → _ → (ℝ≥0 → ℝ) × ℝ≥0∞), IsLowerLaunchOutput κ b jumps P E u l k ω₀ c b' J' h' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (∃ y : ℝ, y < 0 ∧ y < realMin (upperPrefix κ b jumps E u l k ω₀) ∧
            (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
          ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
            IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
              (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-! ### The closed left side -/

/-- **A history adherent to its interior points that avoids the right side of a proper curve is on its closed
left** (with any real segment `[u, 0]`, which is always on the closed left: negative real points off the curve are on
its left side). -/
theorem subset_closedLeftSide_of_avoid {β₀ : ℝ≥0 → ℂ} (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    {X : Set ℂ} {u : ℝ} (hcl : X ⊆ closure (X ∩ H) ∪ ((↑) : ℝ → ℂ) '' Icc u 0)
    (havoid : X ∩ rightSideOf (range β₀) = ∅) :
    X ∪ ((↑) : ℝ → ℂ) '' Icc u 0 ⊆ closedLeftSide β₀ := by
  have h0 : (β₀ 0).im = 0 := by rw [hβ0]; rfl
  have hXH : X ∩ H ⊆ closedLeftSide β₀ := fun z hz =>
    mem_closedLeftSide_of_notMem_rightSideOf hβ hβ0 hz.2 fun hR =>
      (Set.eq_empty_iff_forall_notMem.1 havoid) z ⟨hz.1, hR⟩
  have hcl' : closure (X ∩ H) ⊆ closedLeftSide β₀ :=
    closure_minimal hXH (Theorem15D5.isClosed_closedLeftSide (isClosed_seedRayClosure hβ))
  have hbr : ((↑) : ℝ → ℂ) '' Icc u 0 ⊆ closedLeftSide β₀ := by
    rintro _ ⟨y, ⟨-, hy0⟩, rfl⟩
    by_cases hyS : (y : ℂ) ∈ seedRayClosure β₀
    · exact Or.inr hyS
    rcases hy0.lt_or_eq with hy | rfl
    · refine Or.inl (ofReal_mem_leftSide hβ.2.2.1 h0 ?_ hyS)
      rw [hβ0]; simpa using hy
    · exact absurd (Or.inl ⟨0, by rw [hβ0]; simp⟩) hyS
  rintro z (hz | hz)
  · rcases hcl hz with h | h
    · exact hcl' h
    · exact hbr h
  · exact hbr hz

/-! ### The conditional sewing geometry at one launch -/

/-- **The S1-free relative sewing geometry at a retained launch, from the lifted lower tail.** At a retained
realization `ω₀` where instruction `k` of the upper schedule launches in the conformal chart `c` with regular launched
pieces, with the launch readout `f` and a witness of the conditional flow law: if SB2(2) supplies the translation
`m ≤ 0` with right entry value `−m` at `R`, and almost surely under the retained kernel `Q` the lower walk has a
proper parametrization from `0`, its tail lifts to the relative walk `EL` with a free collar, and the retained history
avoids its right side, then `Leaf.HasRelTailGeometry` holds `Q`-almost surely on the launch event, for the
translated chosen trace and the original lifetime. -/
theorem ae_relTailGeometry_of_lift (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} (hu : u ≤ 0) {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {θ : ℝ}
    (hreg₀ : ∀ j c' θ', (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      GW1P.PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2))
    (hlaunch : (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) (k + 1)).2.2.2.1 k =
      some (c, θ))
    (hcc : c.IsConformal) {f : ℂ → ℂ} (hf : ∀ z ∈ Hbar, Tendsto c.2.1 (𝓝[H] z) (𝓝 (f z)))
    (hfc : ContinuousOn f Hbar) {b' : ℝ → ℝ} {J' : Finset ℝ} {hl : Ω → DistOn upperHalfPlaneOpens}
    (hfl : IsFlowLineDriver κ b' J' θ
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) hl
      (fun t ω => (E (upperSpec u l) k ω).1 t) (fun ω => (E (upperSpec u l) k ω).2))
    (hread : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      schedulePiece κ b jumps u l (fun j => E (upperSpec u l) j ω) k =
        f '' (GW2aSingle.chosenTrace (fun t ω => (E (upperSpec u l) k ω).1 t)
          (fun ω => (E (upperSpec u l) k ω).2) ω ''
            {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (schedDelta 0 l k) (E (upperSpec u l) k ω).2}))
    {m : ℝ} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hm : m ≤ 0)
    (hent : IsRightEntryValue c (realMax (upperPrefix κ b jumps E u l k ω₀)) (-m))
    (hβ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∃ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ ∧ β₀ 0 = 0 ∧ range β₀ = lowerWalkSet κ b jumps E ω)
    (hlift : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      (∃ y : ℝ, y < 0 ∧ y < realMin (upperPrefix κ b jumps E u l k ω₀) ∧
          (y : ℂ) ∉ lowerWalkSet κ b jumps E ω) ∧
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
            (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω))
    (havoid : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∩
        rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      HasRelTailGeometry (schedulePiece κ b jumps u l (fun j => E (upperSpec u l) j ω) k)
        (rightSideOf (lowerWalkSet κ b jumps E ω))
        (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω) m
        (fun t => aff 1 m (GW2aSingle.chosenTrace (fun t ω => (E (upperSpec u l) k ω).1 t)
          (fun ω => (E (upperSpec u l) k ω).2) ω t)) (E (upperSpec u l) k ω).2 := by
  -- the retained history at `ω₀` as a path from `0`
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω₀ := hpA
  -- the recentred launch chart is a right entry chart
  have hc := (eq_launch_of_launches (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) hlaunch).2.2
  have hF : ω₀ ∈ upperLaunchSet κ b jumps E u l k := mem_upperLaunchSet hlaunch
  have hrc : IsRightEntryChart (upperPrefix κ b jumps E u l k ω₀)
      (realMax (upperPrefix κ b jumps E u l k ω₀)) (c.recenter (-m)) := by
    rw [hc]
    refine isRightEntryChart_runChart _ _ hreg₀ k (stStatus_ne_done_of_launches _ _ hlaunch)
      (isCompact_upperPrefix hreg₀ hF) (Lw.fillH_union_real _ _) ?_
    have hsc : stChart (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) k) = c :=
      hc.symm
    rw [hsc]; exact hent
  -- the frame, conditionally almost surely
  have hframe : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      Retain.RetainedTailFrame f (rightSideOf (lowerWalkSet κ b jumps E ω))
        (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω) m := by
    filter_upwards [hβ, hlift, havoid] with ω hβω hliftω havω
    obtain ⟨β₀, hβ₀, hβ₀0, hβ₀r⟩ := hβω
    obtain ⟨hcol, hlt⟩ := hliftω
    obtain ⟨tL, γ, htL, hγ, hγ0, hγW, hγl⟩ := hlt β₀ hβ₀ hβ₀0 hβ₀r
    have hAL : upperPrefix κ b jumps E u l k ω₀ ⊆ closedLeftSide β₀ :=
      subset_closedLeftSide_of_avoid hβ₀ hβ₀0 hcl (by rw [hβ₀r]; exact havω)
    refine retainedTailFrame_of_lift hp hp0 hpH hpA' hcc hrc hf hfc hm hβ₀ hβ₀0 hAL htL ?_ hγ hγ0 hγW hγl
      (by rw [hβ₀r])
    obtain ⟨y, hy0, hyA, hyB⟩ := hcol
    exact ⟨y, hy0, hyA, by rw [hβ₀r]; exact hyB⟩
  exact Retain.ae_relTailGeometry_of_frame_readout h13 hκ hfl (T := schedDelta 0 l k)
    (hread.mono fun _ h => h.subset) hframe

end InteractingSLE.Theorem14.SB.Lf
