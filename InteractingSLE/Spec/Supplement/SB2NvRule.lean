/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvCore

/-!
# SB2(2): the v6 rule — the v4 rule masked to the nontrivial launched stages with a good relative state

Packet PROVE-GW2-GEOM2, round 10 (D28). The v5 admissibility clause asks for a driven stage curve on all of `Gd`,
including the zero stages, where it fails (`SB2NvCore`). Measurability of the stage curve at every sample also needs
facts that hold only almost surely per family (the earlier relative records are good, so the run chart is the
measurable version chart; the readings in the relative chart's domain are dense). The v6 rule masks the curve by the
event `maskEv Gd j F`:
* `Gd`;
* not a v4 zero event;
* the actual instruction `j + relOff` launches (`launchEv`);
* the earlier launched relative records with finite stop are good (`recGoodEv`);
* the readings in the relative chart's domain are dense (`denseEv`).

Off the mask the curve is the vertical ray. The same event is the driven event of the recursion (`StageOK`'s `G`) and
the driven-event predicate passed to `GeomAt4` and to SB2LIFT's item 4.

* `stTime`, `GoodRead`, `DenseReads`: the stage-level readings;
* `launchEv`, `recGoodEv`, `denseEv`, `maskEv`, `mρ6`, `hdep6` (the masked rule depends only on the earlier drivers);
* **`GeomFactsV6At`**, **`SB2LowerGeomFactsV6Statement`** (the corrected form of LIFTSET's v5 input);
* **`sb2LowerRelDriverStatementTR_of_v6`**: with SB2LIFT's item 4 (`SB2LowerClauseOfLiftsV5Statement`), D23's
  strengthened target (Theorems 1.2–1.3), by LIFTSET's v5 argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C FlowDilate

/-! ### Readings of a stage curve -/

section Stage

/-- The stage time read at curve time `u` (the reparametrization inside `stCurvep`). -/
def stTime (L : ℝ≥0∞) (u : ℝ) : ℝ≥0 := (if L = ⊤ then u else clockOf L.toReal u).toNNReal

theorem stCurvep_eq (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (u : ℝ) :
    stCurvep c m p L s₂ u = stValp c m p L s₂ (stTime L u) := rfl

/-- **A good reading** at the `i`-th rational curve time: the stage time is good and the lifted point lies in the
relative chart's domain. -/
def GoodRead (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) (i : ℕ) : Prop :=
  stTime L (ratPt i) ∈ goodTp c p L ∧ liftPt c m (p (stTime L (ratPt i))) ∈ (stChart s₂).dom

/-- **Dense readings**: good readings near every rational curve time. -/
def DenseReads (c : Chart) (m : ℝ) (p : ℝ≥0 → ℂ) (L : ℝ≥0∞) (s₂ : ExplState) : Prop :=
  ∀ k n : ℕ, ∃ i, GoodRead c m p L s₂ i ∧ dist (ratPt i) (ratPt k) < 1 / ((n : ℝ) + 1)

/-- At a good reading the stage curve is the relative chart at the lifted point. -/
theorem stCurvep_ratPt_of_goodRead {c : Chart} {m : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞} {s₂ : ExplState} {i : ℕ}
    (h : GoodRead c m p L s₂ i) :
    stCurvep c m p L s₂ (ratPt i) = (stChart s₂).1 (liftPt c m (p (stTime L (ratPt i)))) := by
  rw [stCurvep_eq, stValp_of_good h.1]
  rfl

end Stage

/-! ### The v6 mask -/

section Rule

variable {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart)
  (m : ℝ) (D₁ : Ω → ℕ → Drv)

/-- The actual instruction of stage `j` launches. -/
def launchEv (j : ℕ) : Set Ω :=
  {ω | (wRun κ θ b₁ J₁ (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (j + relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none}

/-- The earlier launched relative records with finite stop are good (`WalkInf.verChart_eq_run`'s condition). -/
def recGoodEv (j : ℕ) (F : ℕ → Ω → Drv) : Set Ω :=
  {ω | ∀ i < j, (wRun κ θ b₂ J₂ (fun i => F i ω) (i + 1)).2.2.2.1 i ≠ none →
    min (instrTime (boundaryWalkSpec b₂ J₂ θ true) i) (F i ω).2 ≠ ⊤ →
    LocalExt.IsDrvGood (recHist (recOf (instrTime (boundaryWalkSpec b₂ J₂ θ true) i) (F i ω)))}

/-- The actual piece of stage `j`, read from the stage shift. -/
abbrev stP (j : ℕ) (ω : Ω) : ℝ≥0 → ℂ :=
  fun t => pcPt (wRun κ θ b₁ J₁ (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω))) (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω)))
    (stageShift κ θ b₁ J₁ R D₁ j ω + t)

/-- The shifted lifetime of the actual piece of stage `j`. -/
abbrev stL (j : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 - stageShift κ θ b₁ J₁ R D₁ j ω

/-- The readings of stage `j` in the relative chart are dense. -/
def denseEv (j : ℕ) (F : ℕ → Ω → Drv) : Set Ω :=
  {ω | DenseReads c m (stP κ θ b₁ J₁ R D₁ j ω) (stL κ θ b₁ J₁ R D₁ j ω) (wRun κ θ b₂ J₂ (fun i => F i ω) j)}

/-- **The v6 mask**: `Gd`, not a v4 zero event, a launched actual instruction, a good relative state. -/
def maskEv (Gd : Set Ω) (j : ℕ) (F : ℕ → Ω → Drv) : Set Ω :=
  Gd ∩ ((cZ4 κ θ b₁ J₁ R D₁ j F)ᶜ ∩ (launchEv κ θ b₁ J₁ R D₁ j ∩
    (recGoodEv κ θ b₂ J₂ j F ∩ denseEv κ θ b₁ J₁ b₂ J₂ R c m D₁ j F)))

open Classical in
/-- **The v6 stage curves**: the v4 curve on the mask, the vertical ray off it. -/
def mρ6 (Gd : Set Ω) (j : ℕ) (F : ℕ → Ω → Drv) (ω : Ω) : ℝ → ℂ :=
  if ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F then cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ω else vertCurve

variable {κ θ b₁ J₁ b₂ J₂ R c m D₁}

theorem maskEv_sub {Gd : Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) : ω ∈ Gd := h.1

theorem not_mem_cZ4_of_maskEv {Gd : Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) : ω ∉ cZ4 κ θ b₁ J₁ R D₁ j F := h.2.1

theorem not_mem_mZ_of_maskEv {Gd : Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) : ω ∉ mZ Gd (cZ4 κ θ b₁ J₁ R D₁) j F :=
  not_mem_mZ h.1 h.2.1

theorem mρ6_of_mem {Gd : Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) :
    mρ6 κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F ω = cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ω := by
  classical
  unfold mρ6; simp only [h, ↓reduceIte]

theorem mρ6_of_not_mem {Gd : Set Ω} {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω}
    (h : ω ∉ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) : mρ6 κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F ω = vertCurve := by
  classical
  unfold mρ6; simp only [h, ↓reduceIte]

/-- **The v6 rule depends only on the earlier drivers.** -/
theorem hdep6 (Gd : Set Ω) :
    ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) →
      mρ6 κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F = mρ6 κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F' ∧
        maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F = maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F' ∧
        mZ Gd (cZ4 κ θ b₁ J₁ R D₁) j F = mZ Gd (cZ4 κ θ b₁ J₁ R D₁) j F' := by
  intro j F F' h
  have hrun : ∀ ω, ∀ n ≤ j, wRun κ θ b₂ J₂ (fun i => F i ω) n = wRun κ θ b₂ J₂ (fun i => F' i ω) n :=
    fun ω n hn => Exist.Staged.run_congr _ fun i hi => by rw [h i (lt_of_lt_of_le hi hn)]
  have hR : recGoodEv κ θ b₂ J₂ j F = recGoodEv κ θ b₂ J₂ j F' := by
    ext ω
    simp only [recGoodEv, mem_ofPred_eq]
    refine forall₂_congr fun i hi => ?_
    rw [hrun ω (i + 1) hi, h i hi]
  have hD : denseEv κ θ b₁ J₁ b₂ J₂ R c m D₁ j F = denseEv κ θ b₁ J₁ b₂ J₂ R c m D₁ j F' := by
    ext ω
    simp only [denseEv, mem_ofPred_eq]
    rw [hrun ω j le_rfl]
  have hM : maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F = maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F' := by
    unfold maskEv
    rw [hR, hD]
    rfl
  obtain ⟨h1, -, -⟩ := hdep_concrete3 κ θ b₁ J₁ b₂ J₂ R c m D₁ (fun _ _ _ => True) j F F' h
  refine ⟨?_, hM, rfl⟩
  funext ω
  unfold mρ6
  rw [hM, h1]

end Rule

/-! ### The launch-level v6 statement -/

/-- The v6 mask at the launch. -/
abbrev lMask (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (Gd : Set Ω) :
    ℕ → (ℕ → Ω → Drv) → Set Ω :=
  maskEv κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
    (lD₁ b jumps E) Gd

/-- The v6 curves at the launch. -/
abbrev lρ6 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (Gd : Set Ω) :
    ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ :=
  mρ6 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m
    (lD₁ b jumps E) Gd

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep GW1P in
/-- **The corrected item-3 half at one launch (v6)**: a measurable `Gd` such that the v6 rule (curve `lρ6`, driven
events the mask, zero events `mZ Gd lZ4`) is admissible for every family admissible for it, and every measurable,
everywhere regular family that is `zeroDrv` on the masked zero events and generates the v4 curves on the mask has the
per-stage facts `GeomAt4` (driven events the mask) and `Mn.StageFactsAS`. -/
def GeomFactsV6At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ Gd : Set Ω, MeasurableSet Gd ∧
    (∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd (lZ4 κ b jumps E u l k ω₀) i F, F i ω = Lk.zeroDrv) →
      (∀ i < j, ∀ ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd i F,
        (F i ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m i F ω))) →
      StageOK (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j F) (lMask κ b jumps E u l k ω₀ c b' J' m Gd j F)
        (mZ Gd (lZ4 κ b jumps E u l k ω₀) j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ mZ Gd (lZ4 κ b jumps E u l k ω₀) j EL, EL j ω = Lk.zeroDrv) →
      (∀ j, ∀ ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd j EL,
        (EL j ω).2 = capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ3 κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      GeomAt4 κ b jumps P E u l k ω₀ c b' J' m (fun j ω _ => ω ∈ lMask κ b jumps E u l k ω₀ c b' J' m Gd j EL) EL ∧
        Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL

/-- **The corrected item-3 input (v6)** (replaces `Lk.SB2LowerGeomFactsV5Statement`, false by `SB2NvCore`). -/
def SB2LowerGeomFactsV6Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → GeomFactsV6At κ b jumps P E u l k ω₀ c b' J'

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep GW1P in
/-- **The strengthened target from the v6 half and SB2LIFT's item 4** (Theorems 1.2–1.3; no S3 input; LIFTSET's
`sb2LowerRelDriverStatementTR_of_v5` with the v6 mask). -/
theorem sb2LowerRelDriverStatementTR_of_v6 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hG : SB2LowerGeomFactsV6Statement.{u})
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
  set M := lMask κ b jumps E u l k ω₀ c b' J' m Gd with hMdef
  -- the v6 rule is admissible: the generation hypotheses agree on the mask
  have hok' : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ mZ Gd Z i F, F i ω = Lk.zeroDrv) →
      (∀ i < j, ∀ ω ∈ M i F, ω ∉ mZ Gd Z i F →
        (F i ω).2 = capLife (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω) ∧
        ∀ T < capLife (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω))) →
      StageOK (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j F) (M j F) (mZ Gd Z j F) := by
    intro j F hm1 hm2 hz hg
    refine hok j F hm1 hm2 hz fun i hi ω hω => ?_
    have h := hg i hi ω hω (not_mem_mZ_of_maskEv hω)
    have e : lρ6 κ b jumps E u l k ω₀ c b' J' m Gd i F ω = ρ i F ω := mρ6_of_mem hω
    rwa [e] at h
  obtain ⟨EL, hmeas, hreg, hZ, hgen⟩ := exists_EL_rec' (lρ6 κ b jumps E u l k ω₀ c b' J' m Gd) M (mZ Gd Z)
    (hdep6 Gd) hok'
  have hgen' : ∀ j, ∀ ω ∈ M j EL, (EL j ω).2 = capLife (ρ j EL ω) ∧
      ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω)) := by
    intro j ω hω
    have h := hgen j ω hω (not_mem_mZ_of_maskEv hω)
    have e : lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j EL ω = ρ j EL ω := mρ6_of_mem hω
    rwa [e] at h
  have hZ' : ∀ j, ∀ ω ∈ Z j EL, EL j ω = Lk.zeroDrv := fun j ω hω => hZ j ω (subset_mZ hω)
  obtain ⟨hgeom, hSF⟩ := hfacts EL hmeas hreg hZ hgen'
  have hdrv : ∀ j, ∀ ω ∈ M j EL, IsDrivenCurve (ρ j EL ω) := by
    intro j ω hω
    have h := (hok' j EL (fun i _ => hmeas i) (fun i _ ω => hreg i ω) (fun i _ => hZ i)
      (fun i _ => hgen i)).2.2.2 ω hω
    have e : lρ6 κ b jumps E u l k ω₀ c b' J' m Gd j EL ω = ρ j EL ω := mρ6_of_mem hω
    rwa [e] at h
  have hPL : PiecesLift2AS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
      hD₀ c θ hlaunch b' J' h' hb' hT' hG', hR₀] with ω hω hHω hIω hDω hRω
    intro β₀ hβ hβ0 hβr tL γ hγ
    exact piecesLift2_of_geom4 hγ hcc hU hDom (hHω β₀ hβ hβ0 hβr tL hγ.1) hβ hβr hRω
      (fun n hn hl => (hIω n).2.2 hn hl) (hDω β₀ hβ hβ0 hβr tL hγ.1) (hω β₀ hβ hβ0 hβr tL γ hγ)
      (fun j => hreg j ω) (fun j hGj _ => hgen' j ω hGj) (fun j hGj => hdrv j ω hGj)
  -- the root facts (D25)
  have hRoot : RootFactsAS κ b jumps P E u l k ω₀ c b' J' m EL := by
    filter_upwards [hgeom, hSF, hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm,
      hL₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hSFω hβω hTω hLω
    obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
    obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
    have hst := (hω β₀ hβ hβ0 hβr tL γ hγ).1
    refine rootFactsAt_of (fun hz => hZ' 0 ω ((mem_cZ4_zero_iff _ _ _ _ _ _ _ _).2 hz)) (fun hnZ hs => ?_) hSFω
      (hreg 0 ω)
    have hM : ω ∈ M 0 EL := ((hst hnZ (hLω hnZ)).1 hs).1
    rw [(hgen' 0 ω hM).1]
    exact (capLife_pos_of_driven (hdrv 0 ω hM)).ne'
  exact ⟨EL, hmeas, hreg, hC₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
    (fun j ω _ => ω ∈ M j EL) EL hmeas hreg hZ' (fun j ω hω _ => hgen' j ω hω) hgeom hSF hRoot hPL, hSF⟩

end InteractingSLE.Theorem14.SB.Nv
