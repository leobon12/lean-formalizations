/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JeInd
import InteractingSLE.Spec.Supplement.SB2JwRayAS

/-!
# SB2(2): the start data at `relOff`, uniformly in the relative family (D40)

Packet PROVE-SB2-LIFTSET (round 21). Decision D40: SB2LIFT exports the start data of the corrected bundle (`ArcStart`
or `PieceStartV` at the offset `relOff`) from the stage-`0` facts only, as its almost-sure statement
`Lk.SB2LowerStartDataStatement` (in-flight file `SB2YdStart`, not yet landed). **`SB2LowerStartDataFamStatement`** is
that statement verbatim under a distinct name (no clash): for every everywhere regular family `EL` and every event `G`
on which `EL 0` generates the stage-`0` curve off the stage-`0` zero event and is `zeroDrv` on it, almost surely on `G`
the start disjunction holds. After `SB2YdStart` lands, SB2LIFT's `sb2LowerStartDataStatement_of_thms` is a proof of it
(the bodies are identical).

GEOM2's admissibility clause asks for drivenness at a stage for **every** family known before it, pointwise on the
mask of one event chosen before the family, so the family must be quantified inside the almost-sure event:
**`SB2LowerStartDataUStatement`**. **`sb2LowerStartDataU_of_fam`** derives it from the per-family statement (neither
the family nor the event there need be measurable): apply it to the event of the samples carrying a counterexample
family and to a family choosing one at each such sample; almost surely that event is not entered.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

/-- The ray map of the upper chart at the launch (`sb2LowerRayCorr`). -/
abbrev lι (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) : ℝ → ℝ :=
  rayMap (Lx.bdryValue c) (realMax (upperPrefix κ b jumps E u l k ω₀)) (upperEntry κ b jumps E u l k ω₀)

/-- **SB2LIFT's start data at `relOff`** (D40), verbatim (`Lk.SB2LowerStartDataStatement` of `SB2YdStart`). -/
def SB2LowerStartDataFamStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv, (∀ j ω, IsRegularDriver (EL j ω)) →
    ∀ G : Set _, (∀ ω ∈ G, ω ∉ lZ4 κ b jumps E u l k ω₀ 0 EL →
        (EL 0 ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω),
          IsGeneratingTrace (EL 0 ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω))) →
      (∀ ω ∈ G, ω ∈ lZ4 κ b jumps E u l k ω₀ 0 EL → EL 0 ω = zeroDrv) →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀), ω ∈ G →
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        ∀ ι : ℝ → ℝ, RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι →
          RayChartLim c (lR κ b jumps E u l k ω₀) m ι →
          (∀ s, ∀ x : ℝ, lR κ b jumps E u l k ω₀ < x → β₀ (tL + s) = x → γ s = ι x) →
          (ArcStart κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) (fun j => EL j ω) β₀ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∨
            (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
                (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠
                ⊤)) ∨
          (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
              (lD₁ b jumps E ω) (fun j => EL j ω) β₀ γ tL
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = ⊤)

/-- The stage-`0` facts of a family at one sample: regular drivers, generation of the stage-`0` curve off the
stage-`0` zero event, `zeroDrv` on it. -/
def Root0At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → Drv) (ω : Ω) : Prop :=
  (∀ j, IsRegularDriver (EL j ω)) ∧
  (ω ∉ lZ4 κ b jumps E u l k ω₀ 0 EL →
    (EL 0 ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω) ∧
    ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω),
      IsGeneratingTrace (EL 0 ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m 0 EL ω))) ∧
  (ω ∈ lZ4 κ b jumps E u l k ω₀ 0 EL → EL 0 ω = zeroDrv)

/-- The start disjunction at one sample, for a relative family `D₂`. -/
def StartConcl (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (ω : Ω)
    (D₂ : ℕ → Drv) : Prop :=
  ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
  ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
  ∀ ι : ℝ → ℝ, RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι →
    RayChartLim c (lR κ b jumps E u l k ω₀) m ι →
    (∀ s, ∀ x : ℝ, lR κ b jumps E u l k ω₀ < x → β₀ (tL + s) = x → γ s = ι x) →
    (ArcStart κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) D₂ β₀ tL
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∨
      (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
          (lD₁ b jumps E ω) D₂ β₀ γ tL
          (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 ≠ ⊤)) ∨
    (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) ι
        (lD₁ b jumps E ω) D₂ β₀ γ tL
        (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)) ∧
      (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = ⊤)

/-- **The start data at `relOff`, uniformly in the relative family**: almost surely, every family with the stage-`0`
facts at the sample has the start disjunction there. -/
def SB2LowerStartDataUStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ EL : ℕ → _ → Drv, Root0At κ b jumps E u l k ω₀ c b' J' m EL ω →
        StartConcl κ b jumps E u l k ω₀ c b' J' m ω (fun j => EL j ω)

/-- The launch-level stage curves at a sample read the family only at that sample. -/
theorem lρ3_congr_at {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ} {j : ℕ}
    {EL EL' : ℕ → Ω → Drv} {ω : Ω} (h : ∀ i, EL i ω = EL' i ω) :
    lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω = lρ3 κ b jumps E u l k ω₀ c b' J' m j EL' ω := by
  have hf : (fun i => EL i ω) = fun i => EL' i ω := funext h
  show cΦ3 _ _ _ _ _ _ _ _ _ _ (ExplState.run _ _ _ _ (fun i => EL i ω) j) =
    cΦ3 _ _ _ _ _ _ _ _ _ _ (ExplState.run _ _ _ _ (fun i => EL' i ω) j)
  rw [hf]

theorem root0At_congr {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ}
    {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    {EL EL' : ℕ → Ω → Drv} {ω : Ω} (h : ∀ i, EL i ω = EL' i ω)
    (hR : Root0At κ b jumps E u l k ω₀ c b' J' m EL ω) : Root0At κ b jumps E u l k ω₀ c b' J' m EL' ω := by
  have hρ := lρ3_congr_at (κ := κ) (b := b) (jumps := jumps) (E := E) (u := u) (l := l) (k := k) (ω₀ := ω₀)
    (c := c) (b' := b') (J' := J') (m := m) (j := 0) h
  have hZ : lZ4 κ b jumps E u l k ω₀ 0 EL = lZ4 κ b jumps E u l k ω₀ 0 EL' := rfl
  obtain ⟨h1, h2, h3⟩ := hR
  refine ⟨fun j => h j ▸ h1 j, fun hz => ?_, fun hz => ?_⟩
  · rw [← hZ] at hz
    rw [← hρ, ← h 0]
    exact h2 hz
  · rw [← hZ] at hz
    rw [← h 0]
    exact h3 hz

/-- **The start data, uniformly in the family, from SB2LIFT's per-family statement** (D40). -/
theorem sb2LowerStartDataU_of_fam (hF : SB2LowerStartDataFamStatement.{u}) : SB2LowerStartDataUStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm
  classical
  let Bad : Ω → Prop := fun ω => ∃ EL : ℕ → Ω → Drv, Root0At κ b jumps E u l k ω₀ c b' J' m EL ω ∧
    ¬ StartConcl κ b jumps E u l k ω₀ c b' J' m ω (fun j => EL j ω)
  let EL₀ : ℕ → Ω → Drv := fun j ω => if hω : Bad ω then hω.choose j ω else zeroDrv
  have hEL : ∀ ω (hω : Bad ω), ∀ i, hω.choose i ω = EL₀ i ω := fun ω hω i => by
    simp only [EL₀, hω, ↓reduceDIte]
  have hreg : ∀ j ω, IsRegularDriver (EL₀ j ω) := by
    intro j ω
    by_cases hω : Bad ω
    · rw [← hEL ω hω]; exact hω.choose_spec.1.1 j
    · simp only [EL₀, hω, ↓reduceDIte]; exact isRegularDriver_zeroDrv
  have hA := h₀ c θ hlaunch b' J' h' hb' hT' hG' m hm EL₀ hreg {ω | Bad ω}
    (fun ω hω => (root0At_congr (hEL ω hω) hω.choose_spec.1).2.1)
    (fun ω hω => (root0At_congr (hEL ω hω) hω.choose_spec.1).2.2)
  filter_upwards [hA] with ω hω EL hR
  by_contra hneg
  have hB : Bad ω := ⟨EL, hR, hneg⟩
  have h2 : StartConcl κ b jumps E u l k ω₀ c b' J' m ω (fun j => EL₀ j ω) := hω hB
  have hf : (fun j => EL₀ j ω) = fun j => hB.choose j ω := funext fun i => (hEL ω hB i).symm
  rw [hf] at h2
  exact hB.choose_spec.2 h2

end InteractingSLE.Theorem14.SB.Lk
