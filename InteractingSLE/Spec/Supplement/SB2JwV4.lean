/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtConc
import InteractingSLE.Spec.Supplement.SBS3LtDensity

/-!
# SB2(2): the v4 rule — v3 with the shifted-lifetime zero event (round 17 finding)

Packet PROVE-SB2-LIFTSET (round 17). The v3 rule (D6 option A) asks, at stage `0` off a zero root, for `Stage0Facts`
whenever the start piece's lifetime `L₀` is nonzero; one of its fields is `L₀ − t_R ≠ 0`. At a pure piece entry whose
start piece first visits `R` at its end (`t_R = L₀ < ∞`; `SB2JwCorner`) this fails, so `StagesGeom3` is false at such
a sample. The v4 rule changes only the zero events: a stage is zero when its **shifted** lifetime is `0`
(`(D₁ (j + o)).2 − stageShift j = 0`; for `j ≠ 0` the shift is `0`, so this is v3's zero event there). The curves
(`cρ3`) and the driven events (`cG`) are v3's.

* `cZ4`, `hdep_concrete4`, **`exists_EL_concrete4`**;
* `StagesGeom4` (stage `0` split on the shifted lifetime), **`piecesLift2_of_geom4`**;
* `lZ4`, `GeomAt4`, **`ConcreteSplitV4At`**, **`SB2LowerConcreteSplitV4Statement`** (named input, the v4 rule);
* **`sb2LowerRelDriverStatementT_of_splitV4`**, `sb2LowerLaunchLiftStatement_of_splitV4`: D7's corrected target and the
  combined target from it, as from v3 but with **no S3 input** (the good-time density is
  `S3.Asm.sb2LowerStageDensity_of_thm12_thm13`, D21).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C
open LuM GW1W GW1Bookkeep GW1P
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

section Rule

variable {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart)
  (m : ℝ) (D₁ : Ω → ℕ → Drv)

/-- **The v4 zero events**: odd stages, stage `0` of a zero root, and stages whose shifted actual lifetime is `0`. -/
def cZ4 (j : ℕ) (_F : ℕ → Ω → Drv) : Set Ω :=
  {ω | j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R (D₁ ω)) ∨
    (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 - stageShift κ θ b₁ J₁ R D₁ j ω = 0}

/-- **The v4 rule depends only on the earlier drivers.** -/
theorem hdep_concrete4 (ΦG : ℕ → Ω → ExplState → Prop) :
    ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) →
      cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F = cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F' ∧
        cG κ θ b₂ J₂ ΦG j F = cG κ θ b₂ J₂ ΦG j F' ∧
        cZ4 κ θ b₁ J₁ R D₁ j F = cZ4 κ θ b₁ J₁ R D₁ j F' := by
  intro j F F' h
  obtain ⟨h1, h2, -⟩ := hdep_concrete3 κ θ b₁ J₁ b₂ J₂ R c m D₁ ΦG j F F' h
  exact ⟨h1, h2, rfl⟩

/-- **`exists_EL_rec'` applied to the v4 rule.** -/
theorem exists_EL_concrete4 [MeasurableSpace Ω] (ΦG : ℕ → Ω → ExplState → Prop)
    (hok : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ cZ4 κ θ b₁ J₁ R D₁ i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG i F, ω ∉ cZ4 κ θ b₁ J₁ R D₁ i F →
        (F i ω).2 = capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω) ∧
        ∀ T < capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω))) →
      StageOK (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F) (cG κ θ b₂ J₂ ΦG j F) (cZ4 κ θ b₁ J₁ R D₁ j F)) :
    ∃ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ cZ4 κ θ b₁ J₁ R D₁ j EL, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG j EL, ω ∉ cZ4 κ θ b₁ J₁ R D₁ j EL →
        (EL j ω).2 = capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω) ∧
        ∀ T < capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω)) :=
  exists_EL_rec' _ _ _ (hdep_concrete4 κ θ b₁ J₁ b₂ J₂ R c m D₁ ΦG) hok

end Rule

/-- **The per-stage facts left, v4** (one sample): stage `0` split on the shifted lifetime. -/
def StagesGeom4 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) (Gi : ℕ → Prop) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop :=
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ →
    (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R D₁) ≠ none →
    ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 → Gi 0 ∧
      Stage0Facts c m β₀ tL (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
        (fun t => pcPt (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
          (shiftD κ θ b₁ J₁ R D₁ 0 + t))
        ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0) (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0)) ∧
    ((D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0 → LiftRel β₀ tL γ
      (newPc (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁)))
      (newPc (ExplState.init 0) (D₂ 0)))) ∧
  ∀ i, 2 ≤ i → i % 2 = 0 →
    (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
    stStatus (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) = GW1W.stArcM true →
    ExplState.IsAdmissibleSeed κ (leftLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁))))
      (rightLim b₁ (stPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)))) θ →
    Gi i ∧ StageRelP c m (pcPt (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₁ (i + relOff κ θ b₁ J₁ R D₁)))
      (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2 (wRun κ θ b₂ J₂ D₂ i) (D₂ i)

/-- **The piece lifts from the v4 per-stage facts** (deterministic, one sample). -/
theorem piecesLift2_of_geom4 {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R R' : ℝ}
    {c : Chart} {m : ℝ} {A : Set ℂ} {D₁ D₂ : ℕ → Drv} {Gi : ℕ → Prop} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
    (hγ : IsTailLiftCurve c R' m β₀ tL γ) (hcc : c.IsConformal) (hU : UpperChartOK c)
    (hDom : c.2.1 '' H = H \ fillH A) (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hβ : IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hpos : ∀ n, 0 < n → (wRun κ θ b₁ J₁ D₁ (n + 1)).2.2.2.1 n ≠ none → (D₁ n).2 ≠ 0)
    (hgd : ∀ i, 2 ≤ i →
      (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1 (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
      {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2} ⊆
        closure (goodT c (wRun κ θ b₁ J₁ D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₁ (i + relOff κ θ b₁ J₁ R D₁))))
    (hG : StagesGeom4 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ Gi β₀ γ tL) (hreg : ∀ j, IsRegularDriver (D₂ j))
    (hgen : ∀ j, Gi j → ¬ (j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁) ∨
        (D₁ (j + relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ j = 0) →
      (D₂ j).2 = capLife (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j) ∧
      ∀ T < capLife (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j),
        IsGeneratingTrace (D₂ j).1 T (capTrace (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j)))
    (hdrv : ∀ j, Gi j → IsDrivenCurve (stCurve3 κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ j)) :
    PiecesLift2 κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL := by
  obtain ⟨h0, hi⟩ := hG
  refine ⟨?_, fun hZ hl => ?_⟩
  · intro i hi2 hl hflow hstat hseed
    have hev : i % 2 = 0 := of_decide_eq_true hflow
    have hne : i ≠ 0 := by omega
    obtain ⟨hGi, hF⟩ := hi i hi2 hev hl hstat hseed
    have hp := hpos _ (by omega) hl
    have hnZ : ¬ (i % 2 = 1 ∨ (i = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁) ∨
        (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ i = 0) := by
      rintro (h | ⟨h, -⟩ | h)
      · omega
      · omega
      · unfold shiftD at h
        simp only [hne, ↓reduceIte, ENNReal.coe_zero, tsub_zero] at h
        exact hp h
    obtain ⟨he₂, hg⟩ := hgen i hGi hnZ
    have hd := hdrv i hGi
    rw [stCurve3_of_ne hne] at he₂ hg hd
    exact liftRel_of_stage3 hγ hcc hU hDom hK hβ hβr hP hl hp (hgd i hi2 hl) hF hd he₂ hg (hreg i).2.1
  · by_cases hd0 : (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
    · exact (h0 hZ hl).2 hd0
    · obtain ⟨hG0, hF⟩ := (h0 hZ hl).1 hd0
      have hnZ : ¬ (0 % 2 = 1 ∨ (0 = 0 ∧ ZeroRoot κ θ b₁ J₁ R D₁) ∨
          (D₁ (0 + relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0) := by
        rintro (h | ⟨-, h⟩ | h)
        · omega
        · exact hZ h
        · rw [zero_add] at h; exact hd0 h
      obtain ⟨he₂, hg⟩ := hgen 0 hG0 hnZ
      have hd := hdrv 0 hG0
      unfold stCurve3 at he₂ hg hd
      simp only [zero_add] at he₂ hg hd
      exact liftRel_of_stage0 hγ hU hDom hK hβ hβr hP hl
        (fun hL h => hL (by rw [h]; exact ENNReal.top_sub_coe)) hF hd he₂ hg (hreg 0).2.1

/-- The v4 launch-level zero events. -/
abbrev lZ4 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) : ℕ → (ℕ → Ω → Drv) → Set Ω :=
  cZ4 κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E)

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- The per-stage facts left, almost surely (v4). -/
def GeomAt4 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (ΦG : ℕ → Ω → ExplState → Prop) (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (lR κ b jumps E u l k ω₀) m β₀ tL γ →
        StagesGeom4 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
          (lD₁ b jumps E ω) (fun j => EL j ω) (fun j => ω ∈ lG κ b' J' m ΦG j EL) β₀ γ tL

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The concrete rule in v4 form.** -/
def ConcreteSplitV4At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ ΦG : ℕ → Ω → ExplState → Prop,
    (∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ lZ4 κ b jumps E u l k ω₀ i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ lG κ b' J' m ΦG i F, ω ∉ lZ4 κ b jumps E u l k ω₀ i F →
        (F i ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω))) →
      StageOK (lρ3 κ b jumps E u l k ω₀ c b' J' m j F) (lG κ b' J' m ΦG j F) (lZ4 κ b jumps E u l k ω₀ j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ4 κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ4 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m ΦG EL ∧
      (PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → ClauseT κ b jumps P E u l k ω₀ c b' J' m EL)

/-- **Named input: SB2(2)'s concrete stage rule in v4 form.** -/
def SB2LowerConcreteSplitV4Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ConcreteSplitV4At κ b jumps P E u l k ω₀ c b' J'

/-- **D7's corrected target from the v4 concrete rule** (Theorems 1.2–1.3; no S3 input, D21). -/
theorem sb2LowerRelDriverStatementT_of_splitV4 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0})
    (hS : SB2LowerConcreteSplitV4Statement.{u}) : SB2LowerRelDriverStatementT.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft,
    hRLQ] with ω₀ h₀ hC₀ hH₀ hI₀ hD₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨hcc, hU, hDom⟩ := hC₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨ΦG, hok, hcl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_concrete4 κ (-(Real.pi / 2)) b jumps (affData 1 m b')
    (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) ΦG hok
  refine ⟨EL, hmeas, hreg, ?_⟩
  obtain ⟨hgeom, hrest⟩ := hcl EL hmeas hreg hZ hgen
  refine hrest ?_
  filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
  intro β₀ hβ hβ0 hβr tL γ hγ
  exact piecesLift2_of_geom4 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
    (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
    (fun j => hreg j ω) (fun j hG hnZ => hgen j ω hG hnZ)
    (fun j hG => (hok j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hG)

/-- **SB2(2)'s combined target (R104a) from the v4 concrete rule and the conditional half.** -/
theorem sb2LowerLaunchLiftStatement_of_splitV4 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0})
    (hS : SB2LowerConcreteSplitV4Statement.{u}) (hcond : SB2LowerRelStageCondStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_relDriverT h12 h13 h12₀ h13₀
    (sb2LowerRelDriverStatementT_of_splitV4 h12 h13 h12₀ h13₀ hS) hcond

end InteractingSLE.Theorem14.SB.Lk
