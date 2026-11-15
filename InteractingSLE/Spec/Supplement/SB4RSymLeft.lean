/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymStaged
import InteractingSLE.Spec.Supplement.SB2LwLift
import InteractingSLE.Spec.Sec7.R7OuterReflect
import InteractingSLE.Spec.Sec7.FlowReflectFlow
import InteractingSLE.Spec.Exist.StagedLaw4
import InteractingSLE.Spec.Supplement.S9BOrder

/-!
# The mirror of SB2(2) from SB2(2), by reflection

Packet PROVE-T14-SB4LEAF (rulings R104, R104a). Supplement p. 631: "Use S2, reflected for the second assertion";
p. 634: "Reflecting gives the upper-walk barrier". **`sb2LeftLaunchLiftStatement_of_lower`**: the mirror of SB2(2)
with the lift on its own output (`Lf.SB2LeftLaunchLiftStatement`) follows from SB2(2)'s combined target
`Lh.SB2LowerLaunchLiftStatement` and Theorems 1.2–1.3.

The reflected configuration: the field `−h ∘ ρ` with data `y ↦ −b(−y)` (`IsGFFWithBoundaryData.reflect`), the
counterflow `−W'` (`R7Outer.isCenteredCounterflowDriver_reflect`), the seed `−v ≤ 0` with angles `−ψ_j`, and the staged
family `reflFam`: the negated regularized schedule on the reflected schedule, the negated regularized left walk on
the reflected left walk (which is the lower walk of the reflected data), and a staged family of the reflected field
from Theorems 1.2–1.3 elsewhere (`reflFam_spec`, via `isStagedHistory_refl`). The reflected runs carry the reflected
components (`runsRefl_schedule` everywhere, `ae_runsRefl_leftWalk` almost surely), so the reflected history, launch
and lower walk are the reflections of the history, launch and left walk, and the two retained σ-algebras have almost
surely the same conditional laws (`ae_condExpKernel_refl`). SB2(2)'s output for the reflected configuration then reads
back as the mirror output (`isLeftEntryValue_of_reflChart` for the entry value).

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

open Supp9B Lx Lu Ly Leaf FlowDilate Sec4 Exist.Staged Exist.StagedLaw GW2Schedule
open Sec7.StripWall (negDrv measurable_negDrv isRegularDriver_negDrv)
open Sec7.FlowReflect (reflData reflJumps reflField)

/-! ### Reflected programs and sets -/

theorem reflData_invol (g : ℝ → ℝ) : reflData (reflData g) = g := by
  funext y
  simp only [reflData, neg_neg]

theorem reflJumps_invol (J : Finset ℝ) : reflJumps (reflJumps J) = J := by
  ext y
  rw [Sec7.FlowReflect.mem_reflJumps, Sec7.FlowReflect.mem_reflJumps, neg_neg]

theorem reflSpec_sspec (v : ℝ) (l : List (ℝ × ℝ≥0)) : reflSpec (sspec v l) = upperSpec (-v) (reflAngles l) :=
  reflSpec_schedule v l

/-- The reflected left walk is the lower walk of the reflected data. -/
theorem reflSpec_leftWalk {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) :
    reflSpec (boundaryWalkSpec b J (Real.pi / 2) false) =
      boundaryWalkSpec (reflData b) (reflJumps J) (-(Real.pi / 2)) true := by
  have := reflSpec_boundaryWalkSpec (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb)
    (Real.pi / 2) false
  rwa [reflData_invol, reflJumps_invol] at this

theorem physSet_reflSpec {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {spec : ExplSpec} {D' D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hr : RunsRefl κ b J spec D' D) :
    ExplState.physSet κ (reflData b) (reflJumps J) (reflSpec spec) D' =
      Supp9B.refl '' ExplState.physSet κ b J spec D := by
  rw [← prefixPhysSet_length, ← prefixPhysSet_length]
  have hlen : (reflSpec spec).2.2.length = spec.2.2.length := List.length_map _
  rw [hlen]
  exact prefixPhysSet_reflSpec spec D' D _ (hr _).1 (hr _).2.1

section Sets

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} {ER E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {v : ℝ} {l : List (ℝ × ℝ≥0)} {ω : Ω}

/-- The reflected upper history is the reflected arc history. -/
theorem upperPrefix_refl
    (hr : RunsRefl κ b J (sspec v l) (fun j => ER (reflSpec (sspec v l)) j ω) (fun j => E (sspec v l) j ω))
    (k : ℕ) :
    upperPrefix κ (reflData b) (reflJumps J) ER (-v) (reflAngles l) k ω =
      Supp9B.refl '' arcPrefix κ b J E v l k ω := by
  unfold upperPrefix arcPrefix
  have hsp : ((-v, true, scheduleProgram 0 (reflAngles l)) : ExplSpec) = reflSpec (sspec v l) :=
    (reflSpec_sspec v l).symm
  rw [hsp, prefixPhysSet_reflSpec _ _ _ k (hr k).1 (hr k).2.1, image_union, refl_image_ofReal_Icc]

/-- The lower walk of the reflected data is the reflected left walk. -/
theorem lowerWalkSet_refl (hb : IsPiecewiseConstantBoundaryData b J)
    (hr : RunsRefl κ b J (boundaryWalkSpec b J (Real.pi / 2) false)
      (fun j => ER (reflSpec (boundaryWalkSpec b J (Real.pi / 2) false)) j ω)
      (fun j => E (boundaryWalkSpec b J (Real.pi / 2) false) j ω)) :
    lowerWalkSet κ (reflData b) (reflJumps J) ER ω = Supp9B.refl '' leftWalkSet κ b J E ω := by
  unfold lowerWalkSet leftWalkSet
  rw [← reflSpec_leftWalk hb]
  exact physSet_reflSpec hr

/-- The reflected launch record. -/
theorem upperLaunch_refl
    (hr : RunsRefl κ b J (sspec v l) (fun j => ER (reflSpec (sspec v l)) j ω) (fun j => E (sspec v l) j ω))
    (k : ℕ) :
    (ExplState.run κ (reflData b) (reflJumps J) (upperSpec (-v) (reflAngles l))
        (fun j => ER (upperSpec (-v) (reflAngles l)) j ω) (k + 1)).2.2.2.1 k =
      reflLaunch ((ExplState.run κ b J (sspec v l) (fun j => E (sspec v l) j ω) (k + 1)).2.2.2.1 k) := by
  rw [← reflSpec_sspec, (hr (k + 1)).2.2.2, reflState_launches]

end Sets

/-- **The left entry value from the reflected chart's right entry value.** -/
theorem isLeftEntryValue_of_reflChart {c : Chart} {L m : ℝ} (h : IsRightEntryValue (reflChart c) (-L) (-m)) :
    IsLeftEntryValue c L m := by
  obtain ⟨f, hf, hfm⟩ := h
  refine ⟨fun x => -f (-x), fun x hx => ?_, ?_⟩
  · have h1 := hf (-x) (by linarith)
    have h2 := tendsto_refl_nhdsWithin_H (x : ℂ)
    rw [refl_ofReal] at h2
    have h3 := (continuous_refl.tendsto _).comp (h1.comp h2)
    rw [refl_ofReal] at h3
    have e : (Supp9B.refl ∘ (reflChart c).1 ∘ Supp9B.refl) = c.1 := by
      funext z
      simp only [Function.comp_apply, reflChart_fwd, refl_refl]
    rwa [e] at h3
  · have := (hfm.comp tendsto_neg_nhdsLT).neg
    rw [neg_neg] at this
    exact this

/-- `IsStagedHistory` only sees the measure (not its finiteness instance). -/
theorem isStagedHistory_congr_measure {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {Q Q' : Measure Ω} [IsFiniteMeasure Q] [IsFiniteMeasure Q'] (hQ : Q = Q')
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hD : IsStagedHistory κ b J Q h spec D) : IsStagedHistory κ b J Q' h spec D := by
  subst hQ
  exact hD

/-! ### The reflected family -/

open Classical in
/-- **The reflected staged family**: the negated regularized schedule `sched` and left walk `lw` on their
reflections, `E₀` elsewhere. -/
def reflFam {Ω : Type*} (E₀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (sched lw : ExplSpec) :
    ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  fun spec => if spec = reflSpec sched then fun k ω => negDrv (StagedReg.regFam E sched k ω)
    else if spec = reflSpec lw then fun k ω => negDrv (StagedReg.regFam E lw k ω) else E₀ spec

section Fam

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ [StandardBorelSpace Ω] in
theorem reflFam_sched (E₀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (sched lw : ExplSpec) :
    reflFam E₀ E sched lw (reflSpec sched) = fun k ω => negDrv (StagedReg.regFam E sched k ω) := by
  simp only [reflFam, ↓reduceIte]

omit mΩ [StandardBorelSpace Ω] in
theorem reflFam_lw (E₀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {sched lw : ExplSpec}
    (hne : reflSpec lw ≠ reflSpec sched) :
    reflFam E₀ E sched lw (reflSpec lw) = fun k ω => negDrv (StagedReg.regFam E lw k ω) := by
  simp only [reflFam, hne, ↓reduceIte]

omit mΩ [StandardBorelSpace Ω] in
theorem reflFam_other (E₀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {sched lw spec : ExplSpec}
    (h1 : spec ≠ reflSpec sched) (h2 : spec ≠ reflSpec lw) : reflFam E₀ E sched lw spec = E₀ spec := by
  simp only [reflFam, h1, h2, ↓reduceIte]

/-- **The reflected family is a staged family of the reflected field** with regular pieces, whose schedule and lower
walk reflect the schedule and the left walk almost surely, with the same retained conditional laws. -/
theorem reflFam_spec (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (E spec))
    {E₀ : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE₀ : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ (reflData b) (reflJumps J) P (fun ω => reflField (h ω)) spec (E₀ spec) ∧
        StagedPiecesRegular κ (reflData b) (reflJumps J) P spec (E₀ spec))
    (v : ℝ) (l : List (ℝ × ℝ≥0)) (hθ : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ (reflData b) (reflJumps J) P (fun ω => reflField (h ω)) spec
        (reflFam E₀ E (sspec v l) (boundaryWalkSpec b J (Real.pi / 2) false) spec)) ∧
    (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ (reflData b) (reflJumps J) P spec
        (reflFam E₀ E (sspec v l) (boundaryWalkSpec b J (Real.pi / 2) false) spec)) ∧
    (∀ᵐ ω ∂P, RunsRefl κ b J (sspec v l)
      (fun j => reflFam E₀ E (sspec v l) (boundaryWalkSpec b J (Real.pi / 2) false) (reflSpec (sspec v l)) j ω)
      (fun j => E (sspec v l) j ω)) ∧
    (∀ᵐ ω ∂P, RunsRefl κ b J (boundaryWalkSpec b J (Real.pi / 2) false)
      (fun j => reflFam E₀ E (sspec v l) (boundaryWalkSpec b J (Real.pi / 2) false)
        (reflSpec (boundaryWalkSpec b J (Real.pi / 2) false)) j ω)
      (fun j => E (boundaryWalkSpec b J (Real.pi / 2) false) j ω)) ∧
    ∀ k, ∀ᵐ ω₀ ∂P, condExpKernel P (pastSigma κ (reflData b) (reflJumps J) (reflSpec (sspec v l))
        (reflFam E₀ E (sspec v l) (boundaryWalkSpec b J (Real.pi / 2) false) (reflSpec (sspec v l))) k) ω₀ =
      condExpKernel P (pastSigma κ b J (sspec v l) (E (sspec v l)) k) ω₀ := by
  set sched := sspec v l with hsched
  set lw := boundaryWalkSpec b J (Real.pi / 2) false with hlw
  have hs : IsBoundaryContinuedProgram sched.2.2 := GW2Sched.isBoundaryContinuedProgram_scheduleProgram hθ 0
  have hl : IsBoundaryContinuedProgram lw.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b J ⟨by linarith [Real.pi_pos], le_rfl⟩ false
  have hne : reflSpec lw ≠ reflSpec sched := fun he => by
    have := congrArg (fun s : ExplSpec => s.2.1) he
    simp [reflSpec, hlw, hsched, sspec, boundaryWalkSpec] at this
  -- the regularized schedule and left walk
  set Ds := StagedReg.regFam E sched with hDs
  set Dl := StagedReg.regFam E lw with hDl
  have hDsS : IsStagedHistory κ b J P h sched Ds := StagedReg.isStagedHistory_regHist hb (hE _ hs) (hER _ hs)
  have hDlS : IsStagedHistory κ b J P h lw Dl := StagedReg.isStagedHistory_regHist hb (hE _ hl) (hER _ hl)
  have hDsR : StagedPiecesRegular κ b J P sched Ds := WalkLaw.stagedPiecesRegular_regHist (hER _ hs)
  have hDlR : StagedPiecesRegular κ b J P lw Dl := WalkLaw.stagedPiecesRegular_regHist (hER _ hl)
  have hregs : ∀ k ω, IsRegularDriver (Ds k ω) := fun k ω => StagedReg.isRegularDriver_regHist k ω
  have hregl : ∀ k ω, IsRegularDriver (Dl k ω) := fun k ω => StagedReg.isRegularDriver_regHist k ω
  have hrs : ∀ ω, RunsRefl κ b J sched (fun j => negDrv (Ds j ω)) (fun j => Ds j ω) := fun ω =>
    runsRefl_schedule hb v l (fun j => Ds j ω)
  have hrl : ∀ᵐ ω ∂P, RunsRefl κ b J lw (fun j => negDrv (Dl j ω)) (fun j => Dl j ω) :=
    (ae_runsRefl_leftWalk h13₀ hκ hκ4 hb hh hcf hζ' hDlS hregl).mono fun ω hω k => by
      rw [hω k]
      exact compRefl_reflState _
  have hSs := isStagedHistory_refl hb hDsS hregs (Eventually.of_forall hrs)
  have hSl := isStagedHistory_refl hb hDlS hregl hrl
  have hRs := stagedPiecesRegular_refl hDsR (Eventually.of_forall hrs)
  have hRl := stagedPiecesRegular_refl hDlR hrl
  -- the runs with the original drivers
  have hrs' : ∀ᵐ ω ∂P, RunsRefl κ b J sched (fun j => negDrv (Ds j ω)) (fun j => E sched j ω) :=
    (StagedReg.ae_run_regHist (hER _ hs)).mono fun ω hω => (hrs ω).congr_right hω
  have hrl' : ∀ᵐ ω ∂P, RunsRefl κ b J lw (fun j => negDrv (Dl j ω)) (fun j => E lw j ω) := by
    filter_upwards [hrl, StagedReg.ae_run_regHist (hER _ hl)] with ω h1 h2
    exact h1.congr_right h2
  refine ⟨fun spec hspec => ?_, fun spec hspec => ?_, ?_, ?_, fun k => ?_⟩
  · by_cases h1 : spec = reflSpec sched
    · subst h1
      rw [reflFam_sched]
      exact hSs
    · by_cases h2 : spec = reflSpec lw
      · subst h2
        rw [reflFam_lw _ _ hne]
        exact hSl
      · rw [reflFam_other _ _ h1 h2]
        exact (hE₀ spec hspec).1
  · by_cases h1 : spec = reflSpec sched
    · subst h1
      rw [reflFam_sched]
      exact hRs
    · by_cases h2 : spec = reflSpec lw
      · subst h2
        rw [reflFam_lw _ _ hne]
        exact hRl
      · rw [reflFam_other _ _ h1 h2]
        exact (hE₀ spec hspec).2
  · rw [reflFam_sched]
    exact hrs'
  · rw [reflFam_lw _ _ hne]
    exact hrl'
  · rw [reflFam_sched]
    exact ae_condExpKernel_refl hb (fun k => measurable_negDrv.comp (hDsS.1 k))
      (fun k ω => isRegularDriver_negDrv (hregs k ω)) (hE _ hs).2.1 hrs' k

end Fam

/-! ### The mirror of SB2(2) -/

/-- **The mirror of SB2(2) with the lift on its own output, from SB2(2)'s combined target** (rulings R104, R104a;
supplement p. 631, "Use S2, reflected for the second assertion"), and Theorems 1.2–1.3. -/
theorem sb2LeftLaunchLiftStatement_of_lower (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hC : Lh.SB2LowerLaunchLiftStatement.{u}) : SB2LeftLaunchLiftStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER v l k hv hl hθ hR hleft
  have hbR := Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb
  have hhR : IsGFFWithBoundaryData P (fun ω => reflField (h ω)) (reflData b) (reflJumps jumps) :=
    Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh
  have hcfR := Sec7.R7Outer.isCenteredCounterflowDriver_reflect hκ hcf
  obtain ⟨E₀, hE₀⟩ := exists_isStagedHistory_regular_of_thm12_thm13 h12 h13 hκ hκ4 hbR hhR
  set ER := reflFam E₀ E (sspec v l) (boundaryWalkSpec b jumps (Real.pi / 2) false) with hERdef
  obtain ⟨hERs, hERr, hrs, hrl, hK⟩ := reflFam_spec h13₀ hκ hκ4 hb hh hcf hζ' hE hER hE₀ v l
    (fun p hp => Ico_subset_Icc_self (hθ p hp))
  -- the reflected hypotheses of SB2(2)
  have hlR : (reflAngles l).Pairwise (fun p q => p.2 < q.2) := List.pairwise_map.2 hl
  have hθR : ∀ p ∈ reflAngles l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2) := fun p hp => by
    have := hθ _ (mem_reflAngles.1 hp)
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  have hleftR : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ (reflData b) (reflJumps jumps) ER (-v) (reflAngles l) k →
      upperPrefix κ (reflData b) (reflJumps jumps) ER (-v) (reflAngles l) k ω ∩
        rightSideOf (lowerWalkSet κ (reflData b) (reflJumps jumps) ER ω) = ∅ := by
    filter_upwards [hleft, hrs, hrl] with ω hω hs hl' hlaunch
    have hL : ω ∈ launchEvent κ b jumps (sspec v l) (E (sspec v l)) k := by
      have h1 : (ExplState.run κ (reflData b) (reflJumps jumps) (upperSpec (-v) (reflAngles l))
          (fun j => ER (upperSpec (-v) (reflAngles l)) j ω) (k + 1)).2.2.2.1 k ≠ none := hlaunch
      rw [upperLaunch_refl hs k] at h1
      intro h0
      exact h1 (by rw [h0]; rfl)
    rw [upperPrefix_refl hs k, lowerWalkSet_refl hb hl', rightSideOf_refl_image,
      ← image_inter refl_injective, hω hL, image_empty]
  have hbase := hC κ hκ hκ4 (reflData b) (reflJumps jumps) hbR P (fun ω => reflField (h ω)) hhR (-W') ζ' hcfR hζ'
    ER hERs hERr (-v) (reflAngles l) k (by linarith) hlR hθR (bridgeLeft_reflect hR) hleftR
  have hprog : IsBoundaryContinuedProgram (sspec v l).2.2 :=
    GW2Sched.isBoundaryContinuedProgram_scheduleProgram (fun p hp => Ico_subset_Icc_self (hθ p hp)) 0
  have hwalkQ := KernelTower.ae_ae_condExpKernel_of_ae ((hE _ hprog).2.1 k)
    (hrl.mono fun ω hω => lowerWalkSet_refl (ER := ER) hb hω)
  filter_upwards [hbase, hK k, hrs, hwalkQ] with ω₀ hb₀ hK₀ hs₀ hw₀
  rw [← reflSpec_sspec] at hb₀
  intro c θ hcθ b' J' h' hb' hT' hG'
  have hcθR : (ExplState.run κ (reflData b) (reflJumps jumps) (reflSpec (sspec v l))
      (fun j => ER (reflSpec (sspec v l)) j ω₀) (k + 1)).2.2.2.1 k = some (reflChart c, -θ) := by
    rw [(hs₀ (k + 1)).2.2.2, reflState_launches]
    show reflLaunch _ = _
    rw [hcθ]
    rfl
  have hT'R : ∀ ω, IsChartTransport (reflChart c) 1 0 (chiC κ) (reflField (h ω)) (reflField (h' ω)) := fun ω => by
    have := Sec5.CfDown.IsChartTransport.reflect_of (c' := reflChart c) (fun z => rfl) (fun w _ => rfl)
      (fun z => rfl) (hT' ω)
    rwa [neg_zero] at this
  have hG'R : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ (reflData b) (reflJumps jumps)
      (reflSpec (sspec v l)) (ER (reflSpec (sspec v l))) k) ω₀) (fun ω => reflField (h' ω)) (reflData b')
      (reflJumps J') := by
    rw [hK₀]
    exact Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hG'
  obtain ⟨m, EL, ⟨hm, hlm, hent, hword, hst, hregL, -, -⟩, hlift⟩ := hb₀ (reflChart c) (-θ) hcθR (reflData b')
    (reflJumps J') (fun ω => reflField (h' ω)) (Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb')
    hT'R hG'R
  rw [reflSpec_sspec] at hK₀
  replace hst := isStagedHistory_congr_measure hK₀ hst
  rw [hK₀] at hregL hlift
  have hpre := upperPrefix_refl hs₀ k
  refine ⟨m, EL, ⟨hm, hlm, ?_, hword, hst, hregL⟩, ?_⟩
  · rw [hpre, realMax_refl_image] at hent
    exact isLeftEntryValue_of_reflChart hent
  · filter_upwards [hlift, hw₀] with ω hω hwω
    obtain ⟨⟨y, hy0, hyA, hyW⟩, hβ⟩ := hω
    rw [hpre] at hyA hβ
    rw [hwω] at hyW hβ
    rw [realMin_refl_image] at hyA
    refine ⟨⟨-y, by linarith, by linarith, fun hy => hyW ⟨_, hy, by rw [refl_ofReal, neg_neg]⟩⟩,
      fun βL hβL hβL0 hβLr => ?_⟩
    have h1 := hβ (reflectCurve βL) (isProperCurve_reflectCurve hβL) (by simp [reflectCurve, hβL0, Supp9B.refl])
      (by rw [show reflectCurve βL = Supp9B.refl ∘ βL from rfl, range_comp, hβLr])
    rwa [realMax_refl_image] at h1

end InteractingSLE.Theorem14.SB.Lf
