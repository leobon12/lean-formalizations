/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwTR
import InteractingSLE.Spec.Supplement.SB2JvHead
import InteractingSLE.Spec.Supplement.SB2JvEnd
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# SB2(2): the v5 rule — the v4 rule masked by a measurable good event (StageOK measurability)

Packet PROVE-SB2-LIFTSET (round 18). `StageOK` asks that `ω ↦ ρ ω t` be measurable at **every** sample. The v4 stage
curve `lρ3` is the relative run chart applied to the lift of B's piece, with limits along good times elsewhere
(`stValp`, `limUnder`); off an almost-sure event nothing makes it measurable, so the v4 admissibility clause of
`SB2LowerGeomFactsV4Statement` cannot be proved as stated. The v5 rule masks the v4 rule by a measurable event `Gd`
(conull in the proof): the stage curve is `lρ3` on `Gd` and the vertical ray off it (`mρ`), the driven events are `Gd`,
and the zero events are the v4 zero events on `Gd` and everything off it (`mZ`). On `Gd` it is the v4 rule, so a
family admissible for it carries exactly the hypotheses of SB2LIFT's item 4 (`SB2LowerClauseOfLiftsV4Statement`,
unchanged):

* `mρ`, `mZ`, `hdep_mask` (the masked rule depends only on the earlier drivers);
* **`SB2LowerGeomFactsV5Statement`** (LIFTSET, items 1–3, replacing the v4 form);
* the root facts of D25 (exported with `Mn.StageFactsAS`): `RootFactsAt`/**`RootFactsAS`** — the relative root `EL 0`
  is `zeroDrv` at a zero root and at the corner, of positive lifetime with the v4 stage facts of the shifted start
  piece otherwise, and its record is good (`LocalExt.IsDrvGood`, the input of `hitL₂`) when its lifetime is finite;
  **`rootFactsAt_of`** (deterministic) and their almost-sure derivation inside the reduction;
* `SB2LowerClauseOfLiftsV5Statement` (SB2LIFT's item 4 with the root facts as an extra input;
  `sb2LowerClauseOfLiftsV5_of_v4`);
* **`sb2LowerRelDriverStatementTR_of_v5`**: with SB2LIFT's item 4, D23's strengthened target (Theorems 1.2–1.3).
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

open Sec7.PocketTraversal Sec7.Lemma71C

section Mask

variable {Ω : Type*}

/-- The vertical ray, the stage curve off the good event. -/
abbrev vertCurve : ℝ → ℂ := fun t => (t : ℂ) * Complex.I

open Classical in
/-- **The masked stage curves**: the rule's curve on the good event `Gd`, the vertical ray off it. -/
def mρ (Gd : Set Ω) (ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ) (j : ℕ) (F : ℕ → Ω → Drv) (ω : Ω) : ℝ → ℂ :=
  if ω ∈ Gd then ρ j F ω else vertCurve

/-- **The masked zero events**: the rule's zero events on `Gd`, everything off it. -/
def mZ (Gd : Set Ω) (Z : ℕ → (ℕ → Ω → Drv) → Set Ω) (j : ℕ) (F : ℕ → Ω → Drv) : Set Ω :=
  (Z j F ∩ Gd) ∪ Gdᶜ

theorem mρ_of_mem {Gd : Set Ω} {ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∈ Gd) : mρ Gd ρ j F ω = ρ j F ω := by
  classical
  unfold mρ; simp only [h, ↓reduceIte]

theorem subset_mZ {Gd : Set Ω} {Z : ℕ → (ℕ → Ω → Drv) → Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} :
    Z j F ⊆ mZ Gd Z j F := fun ω hω => by
  by_cases h : ω ∈ Gd
  · exact Or.inl ⟨hω, h⟩
  · exact Or.inr h

theorem not_mem_mZ {Gd : Set Ω} {Z : ℕ → (ℕ → Ω → Drv) → Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∈ Gd) (hZ : ω ∉ Z j F) : ω ∉ mZ Gd Z j F := by
  rintro (⟨h1, -⟩ | h2)
  · exact hZ h1
  · exact h2 h

/-- **The masked rule depends only on the earlier drivers.** -/
theorem hdep_mask (Gd : Set Ω) {ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ} {Z : ℕ → (ℕ → Ω → Drv) → Set Ω}
    (hdep : ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) → ρ j F = ρ j F' ∧ Z j F = Z j F') :
    ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) →
      mρ Gd ρ j F = mρ Gd ρ j F' ∧ (fun _ _ => Gd) j F = (fun (_ : ℕ) (_ : ℕ → Ω → Drv) => Gd) j F' ∧
        mZ Gd Z j F = mZ Gd Z j F' := by
  intro j F F' h
  obtain ⟨h1, h2⟩ := hdep j F F' h
  refine ⟨?_, rfl, ?_⟩
  · unfold mρ; rw [h1]
  · unfold mZ; rw [h2]

end Mask

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P

/-- **LIFTSET's half in v5 form**: a measurable good event `Gd` making the masked v4 rule admissible, such that every
measurable, everywhere regular family that is `zeroDrv` on the masked zero events and generates the v4 curves on
`Gd` off the v4 zero events has the per-stage facts `GeomAt4` (driven events `Gd`) and `Mn.StageFactsAS`. -/
def GeomFactsV5At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ Gd : Set Ω, MeasurableSet Gd ∧
    (∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd (lZ4 κ b jumps E u l k ω₀) i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ Gd, ω ∉ lZ4 κ b jumps E u l k ω₀ i F →
        (F i ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω))) →
      StageOK (mρ Gd (lρ3 κ b jumps E u l k ω₀ c b' J' m) j F) Gd (mZ Gd (lZ4 κ b jumps E u l k ω₀) j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ mZ Gd (lZ4 κ b jumps E u l k ω₀) j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ Gd, ω ∉ lZ4 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m (fun _ ω _ => ω ∈ Gd) EL ∧
        Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input (LIFTSET, items 1–3), v5 form** (replaces `SB2LowerGeomFactsV4Statement`). -/
def SB2LowerGeomFactsV5Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → GeomFactsV5At κ b jumps P E u l k ω₀ c b' J'

/-! ### The root facts (D25) -/

/-- Membership in the v4 zero event at stage `0`. -/
theorem mem_cZ4_zero_iff {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (D₁ : Ω → ℕ → Drv)
    (F : ℕ → Ω → Drv) (ω : Ω) :
    ω ∈ cZ4 κ θ b₁ J₁ R D₁ 0 F ↔ ZeroRoot κ θ b₁ J₁ R (D₁ ω) ∨
      (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))).2 - shiftD κ θ b₁ J₁ R (D₁ ω) 0 = 0 := by
  have hs : stageShift κ θ b₁ J₁ R D₁ 0 ω = shiftD κ θ b₁ J₁ R (D₁ ω) 0 := rfl
  simp only [cZ4, mem_ofPred_eq, zero_add, hs, Nat.zero_mod, zero_ne_one, true_and, false_or]


/-- The zero driver's record is good. -/
theorem isDrvGood_zeroDrv : LocalExt.IsDrvGood (recHist (recOf ⊤ zeroDrv)) :=
  isDrvGood_of_continuousOn_le isRegularDriver_zeroDrv (by simp [zeroDrv])
    (continuousOn_const.congr fun _ _ => rfl)

/-- **The facts of the relative root at one sample** (D25): `D₂ 0 = zeroDrv` at a zero root and at the corner (the
shifted start piece has lifetime `0`); otherwise a positive lifetime and the stage facts of the shifted start piece;
a good record when the lifetime is finite. -/
def RootFactsAt (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart) (m : ℝ)
    (D₁ D₂ : ℕ → Drv) : Prop :=
  ((ZeroRoot κ θ b₁ J₁ R D₁ ∨ (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0) → D₂ 0 = zeroDrv) ∧
  (¬ ZeroRoot κ θ b₁ J₁ R D₁ → (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
    (D₂ 0).2 ≠ 0 ∧ Mn.StageFacts c m (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
      (shiftD κ θ b₁ J₁ R D₁ 0) (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0)) ∧
  ((D₂ 0).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D₂ 0))))

/-- **The root facts from the zero pattern, the positivity and the stage facts** (deterministic). -/
theorem rootFactsAt_of {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ} {R : ℝ} {c : Chart}
    {m : ℝ} {A : Set ℂ} {D₁ D₂ : ℕ → Drv}
    (hZ0 : (ZeroRoot κ θ b₁ J₁ R D₁ ∨ (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0) →
      D₂ 0 = zeroDrv)
    (hpos : ¬ ZeroRoot κ θ b₁ J₁ R D₁ → (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      (D₂ 0).2 ≠ 0)
    (hSF : Mn.StageFactsAll κ θ b₁ J₁ b₂ J₂ R c m A D₁ D₂) (hreg : IsRegularDriver (D₂ 0)) :
    RootFactsAt κ θ b₁ J₁ b₂ J₂ R c m D₁ D₂ := by
  have hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (0 + 1)).2.2.2.1 0 ≠ none := by
    rw [GW1.launches_run_one_boundaryWalkSpec]; exact Option.some_ne_none _
  have hst : ¬ ZeroRoot κ θ b₁ J₁ R D₁ → (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 ≠ 0 →
      (D₂ 0).2 ≠ 0 ∧ Mn.StageFacts c m (wRun κ θ b₁ J₁ D₁ (relOff κ θ b₁ J₁ R D₁)) (D₁ (relOff κ θ b₁ J₁ R D₁))
        (shiftD κ θ b₁ J₁ R D₁ 0) (wRun κ θ b₂ J₂ D₂ 0) (D₂ 0) := by
    intro hZ hs
    have hp := hpos hZ hs
    have h := (hSF 0 hl₂ hp).1
    simp only [zero_add] at h
    exact ⟨hp, h⟩
  refine ⟨hZ0, hst, fun hfin => ?_⟩
  by_cases h : ZeroRoot κ θ b₁ J₁ R D₁ ∨ (D₁ (relOff κ θ b₁ J₁ R D₁)).2 - shiftD κ θ b₁ J₁ R D₁ 0 = 0
  · rw [hZ0 h]; exact isDrvGood_zeroDrv
  · push Not at h
    obtain ⟨-, hF⟩ := hst h.1 h.2
    exact isDrvGood_of_continuousOn_le hreg (GW1W.min_top_ne_top hfin)
      (by rw [min_eq_right (le_top : (D₂ 0).2 ≤ ⊤)]; exact hF.2.2.2.2.2.2.2.1)

/-- **The root facts, almost surely** under the retained kernel (D25), for a relative family `EL`. -/
def RootFactsAS (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → Drv) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    RootFactsAt κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
      (lD₁ b jumps E ω) (fun j => EL j ω)

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **SB2LIFT's item 4 with the root facts** (D25): as `SB2LowerClauseOfLiftsV4Statement`, with `RootFactsAS` as an
extra input. -/
def SB2LowerClauseOfLiftsV5Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ (ΦG : ℕ → _ → ExplState → Prop) (EL : ℕ → _ → Drv),
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ4 κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ4 κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m ΦG EL → Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
      PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL → Mn.ClauseTR κ b jumps P E u l k ω₀ c b' J' m EL

/-- The v4 form of item 4 gives the v5 form. -/
theorem sb2LowerClauseOfLiftsV5_of_v4 (h : SB2LowerClauseOfLiftsV4Statement.{u}) :
    SB2LowerClauseOfLiftsV5Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ hf hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P hf hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm ΦG EL hm1 hm2 hZ hg hgeom hSF _ hPL
  exact h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm ΦG EL hm1 hm2 hZ hg hgeom hSF hPL

/-- **The strengthened target from the v5 half and SB2LIFT's item 4** (Theorems 1.2–1.3; no S3 input). -/
theorem sb2LowerRelDriverStatementTR_of_v5 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV5Statement.{u})
    (hC : SB2LowerClauseOfLiftsV5Statement.{u}) : SB2LowerRelDriverStatementTR.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  have hRLQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (GW1W.regLaunches_of_stagedPiecesRegular (hER _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)))
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerWalkInputs h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    S3.Asm.sb2LowerStageDensity_of_thm12_thm13 h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u
      l k hu hlp hlθ hL hleft,
    hRLQ, hβex,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerLaunchRelOff h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft] with ω₀ hG₀ hC₀ hU₀ hH₀ hI₀ hD₀ hR₀ hβ₀ hT₀ hL₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨hcc, hU, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨Gd, -, hok, hfacts⟩ := hG₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  set ρ := lρ3 κ b jumps E u l k ω₀ c b' J' m with hρ
  set Z := lZ4 κ b jumps E u l k ω₀ with hZdef
  have hdep : ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) → ρ j F = ρ j F' ∧ Z j F = Z j F' := by
    intro j F F' hFF
    obtain ⟨h1, -, h3⟩ := hdep_concrete4 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
      (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E) (fun _ _ _ => True) j F F' hFF
    exact ⟨h1, h3⟩
  -- the masked rule is admissible: the generation hypotheses agree on `Gd`
  have hok' : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd Z i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ (fun _ _ => Gd) i F, ω ∉ mZ Gd Z i F → (F i ω).2 = capLife (mρ Gd ρ i F ω) ∧
        ∀ T < capLife (mρ Gd ρ i F ω), IsGeneratingTrace (F i ω).1 T (capTrace (mρ Gd ρ i F ω))) →
      StageOK (mρ Gd ρ j F) ((fun _ _ => Gd) j F) (mZ Gd Z j F) := by
    intro j F hm1 hm2 hz hg
    refine hok j F hm1 hm2 hz fun i hi ω hω hnZ => ?_
    have h := hg i hi ω hω (not_mem_mZ hω hnZ)
    rwa [mρ_of_mem hω] at h
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_rec' (mρ Gd ρ) (fun _ _ => Gd) (mZ Gd Z)
    (hdep_mask Gd hdep) hok'
  have hgen' : ∀ j, ∀ ω ∈ Gd, ω ∉ Z j EL → (EL j ω).2 = capLife (ρ j EL ω) ∧
      ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω)) := by
    intro j ω hω hnZ
    have h := hgen j ω hω (not_mem_mZ hω hnZ)
    rwa [mρ_of_mem hω] at h
  have hZ' : ∀ j, ∀ ω ∈ Z j EL, EL j ω = zeroDrv := fun j ω hω => hZ j ω (subset_mZ hω)
  obtain ⟨hgeom, hSF⟩ := hfacts EL hmeas hreg hZ hgen'
  have hdrv : ∀ j, ∀ ω ∈ Gd, IsDrivenCurve (ρ j EL ω) := by
    intro j ω hω
    have h := (hok' j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hω
    rwa [mρ_of_mem hω] at h
  have hPL : PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
      hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
    intro β₀ hβ hβ0 hβr tL γ hγ
    exact piecesLift2_of_geom4 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
      (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
      (fun j => hreg j ω) (fun j hGj hnZ => hgen' j ω hGj hnZ) (fun j hGj => hdrv j ω hGj)
  -- the root facts (D25)
  have hRoot : RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hSF, hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm,
      hL₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hSFω hβω hTω hLω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
    have hst := (hω β₀ hβ hβ0 hβr tL γ hγ).1
    refine rootFactsAt_of (fun hz => hZ' 0 ω ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 hz)) (fun hnZ hs => ?_) hSFω
      (hreg 0 ω)
    have hGd : ω ∈ Gd := ((hst hnZ (hLω hnZ)).1 hs).1
    have hnZ' : ω ∉ Z 0 EL := fun hz => ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).1 hz).elim hnZ hs
    rw [(hgen' 0 ω hGd hnZ').1]
    exact (capLife_pos_of_driven (hdrv 0 ω hGd)).ne'
  exact ⟨EL, hmeas, hreg, hC₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm (fun _ ω _ => ω ∈ Gd) EL hmeas hreg hZ'
    (fun j ω hω hnZ => hgen' j ω hω hnZ) hgeom hSF hRoot hPL, hSF⟩

end InteractingSLE.Theorem14.SB.Lk
