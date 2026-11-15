/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NvProxy
import InteractingSLE.Spec.Supplement.GW2TpRoot
import InteractingSLE.Spec.Supplement.GW2BtContact

/-!
# The death clause of D38's export (D46) and the measurable death event

Packet PROVE-GW2-NOTHR (round 4). Decision D46: STAGEMEAN's export gets a DEATH clause, the window clause of
`GW2Nu.StageKernelExportL` applied at the candidate's death. NOTHR proves BUF's `P`-level `DeathThrXStatement` from it.

* **`IsCanonXN`**, **`StageThresholdN`**, **`DeathThrXStatementN`**: verbatim copies of BUF's `GW2Bh.IsCanonX`,
  `GW2Bh.StageThreshold`, `GW2Bh.DeathThrXStatement` (BUF's file is not landed; the bodies are identical, so the
  statements are definitionally equal).
* **`StageDeathExportX`** (STAGEMEAN, D46), for one instance and its version family. For `P`-almost every `ω₀`, at a
  launch, under the launch kernel `ν` there is SAFE's configuration (as in `StageKernelExportL`). Then `ν`-almost
  surely, on the good set and the history's success, with the stage start below the cap and the death clock finite:
  * the counterflow's tip at `t₀` is interior, `λ > 0`, and the stage-start data identity off a finite set;
  * the candidate's launch lifetime `ζα` is its lifetime `candLife`;
  * for a positive lifetime: the death is before the launch-frame contact, `λ² (d − S)` is the relative clock of
    the death, and a driver `Wd` exists that is continuous from `0` and agrees with every version below its cap,
    whose dilated stage path generates the relative hulls up to the death.
* **`deathFin`**: the measurable event `{deathClockX < ⊤}` on the good set (through ROOTX's `locEvX`).
* **`deathEvent`**: the measurable form of BUF's conclusion for one instance. Its threshold is read through the
  versions' limits (`stageProxyW/R/L`) at the supremum of the caps, or at the seed for a zero-lifetime candidate.
  **`measurableSet_deathEvent`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Nv

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd GW2Rv
  GW2Sde GW2Sdh Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop MartChar.RealFlow GW2Nu Sec5.CrossCond.StagedRepLater

/-! ### BUF's statements (verbatim copies) -/

/-- BUF's `GW2Bh.IsCanonX` (verbatim). -/
def IsCanonXN {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ξ : Ω)
    (Wc : ℝ≥0 → ℝ) : Prop :=
  Continuous Wc ∧ Wc 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < V n ξ → R n q ξ = Wc q) ∧
    (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
      ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
        (schedTr c r l a ξ) (c.α ξ)) ≤ ζc) ∧
    ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M

/-- BUF's `GW2Bh.StageThreshold` (verbatim). -/
def StageThresholdN (κ : ℝ) (β : BoundaryWord) (D : ℝ≥0 → ℝ) (u : ℝ≥0) : Prop :=
  ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
    (fun i => -MartChar.RealFlow.rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) u)
    (fun j => MartChar.RealFlow.rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) u)

/-- BUF's `GW2Bh.DeathThrXStatement` (verbatim). -/
def DeathThrXStatementN (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (h : GoodRoot c r), GW2Sdx.HistOrdered c r l →
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a → RootJ31.oldSuccess c r l ξ →
      ∀ Wc : ℝ≥0 → ℝ, IsCanonXN c r l a (ver Ω c r l a).R (ver Ω c r l a).V ξ Wc →
      deathClockX c r l a ξ < ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
        (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ)) →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver ch Ω c r l a j h.1).srecX c r l (rootPt r.1) ξ))
            (stgDrv Wc (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u

/-! ### The death clause (D46) -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **D46's death clause of STAGEMEAN's export** (one instance `I` with its version family `(Rf, Vf)`, root `x₀`):
the launch-kernel configuration of `StageKernelExportL` and, `ν`-almost surely on the good set and the history's
success with the stage start below the cap and a finite death clock: an interior counterflow tip at `t₀`, `λ > 0`,
the stage-start data identity off a finite set, the launch lifetime equal to the candidate's lifetime, and for a
positive lifetime the death before the launch-frame contact, `λ² (d − S)` = the relative clock of the death, and a
driver `Wd` (continuous from `0`, equal to every version below its cap) whose dilated stage path generates the
relative hulls up to the death. -/
def StageDeathExportX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (I : StageInst Ω) (Rf : ℕ → ℝ≥0 → Ω → ℝ) (Vf : ℕ → Ω → ℝ≥0∞) (x₀ : ℝ) : Prop :=
  ∀ᵐ ω₀ ∂c.P, ∀ (cL : Chart) (θ : ℝ), GW2Olm.curLaunch c r l a ω₀ = some (cL, θ) →
    ∃ (b : ℝ → ℝ) (J : Finset ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
      (α : Ω → ℝ≥0 → ℂ) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (cw : BoundaryWord)
      (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ) (t₀ : Ω → ℝ≥0) (lam : Ω → ℝ) (F : Ω → Set ℝ),
      IsPiecewiseConstantBoundaryData b J ∧ IsPiecewiseConstantBoundaryData b' J' ∧
      (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC c.κ)) (chiC (16 / c.κ)) (h ω) (h' ω)) ∧
      IsFlowLineDriver c.κ b J θ (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h Wα ζα ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) ∧
      IsFlowLineDriver (16 / c.κ) b' J' 0 (condExpKernel c.P (GW2Olm.pastG c r l a) ω₀) h' W ζ ∧
      (∀ᵐ ω ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ζ ω = ⊤ ∧
        IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) ∧
      cw.jumps = J' ∧ (∀ y ∉ J', cw.fn y = b' y) ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (GW2Olm.pastG c r l a) ω₀), ξ ∈ I.GT → oldSuccess c r l ξ →
        ((stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ≥0) : ℝ≥0∞) < I.V ξ → deathClockX c r l a ξ < ⊤ →
        γ ξ (t₀ ξ) ∈ H ∧ 0 < lam ξ ∧ (F ξ).Finite ∧
        (∀ y, y ∉ F ξ → (I.β (I.srecX c r l x₀ ξ)).fn y =
          (gw2Word c.κ θ cw (gb6Rec (t₀ ξ) W ζ ξ)).fn (lam ξ * y)) ∧
        ζα ξ = candLife c r l a ξ ∧
        (0 < candLife c r l a ξ →
          (((candLife c r l a ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < gb6Tc (t₀ ξ) (extTr (t₀ ξ) Wα ζα α) γ ξ ∧
          (lam ξ) ^ 2 * ((deathClockX c r l a ξ).toReal - (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ξ : ℝ)) =
            gb6Clock (t₀ ξ) (regW (t₀ ξ) Wα ζα) W ξ (candLife c r l a ξ).toNNReal ∧
          ∃ Wd : ℝ≥0 → ℝ, Continuous Wd ∧ Wd 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < Vf n ξ → Rf n q ξ = Wd q) ∧
            ∀ t : ℝ≥0, t ≤ (candLife c r l a ξ).toNNReal →
              fwdHull (scD (lam ξ) (fun q : ℝ => stgDrv Wd (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ξ)
                  q.toNNReal)) (gb6Clock (t₀ ξ) (regW (t₀ ξ) Wα ζα) W ξ t) =
                relMap (fun r : ℝ => W r.toNNReal ξ) (t₀ ξ) ''
                  fwdHull (fun r : ℝ => regW (t₀ ξ) Wα ζα r.toNNReal ξ) t)

/-- **D46's death clause at every root-`x` instance of a version family and a choice family.** -/
def DeathExportFamily (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a j : ℕ,
      StageDeathExportX c r l a (instX h13 ver ch Ω c r l a j h.1) (ver Ω c r l a).R (ver Ω c r l a).V (rootPt r.1)

/-! ### The measurable death event -/

/-- The seed threshold of a word (its threshold at time `0`). -/
def SeedThr (κ : ℝ) (β : BoundaryWord) : Prop :=
  ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) 0
    (flowLineXL β.fn β.jumps 0) (flowLineXR β.fn β.jumps 0)

/-- The threshold of a word at the death read through the versions' limits. -/
def ProxThr (κ : ℝ) (β : BoundaryWord) (R : ℕ → ℝ≥0 → ℝ) (S u : ℝ≥0) : Prop :=
  ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0)
    (stageProxyW R S u) (fun i => stageProxyL R S u (flowLineXL β.fn β.jumps 0 i))
    (fun j => stageProxyR R S u (flowLineXR β.fn β.jumps 0 j))

/-- **The finite death clock on the good set**, through ROOTX's local events. -/
def deathFin (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (I : StageInst Ω) (x₀ : ℝ) : Set Ω :=
  {ω | candLife c r l a ω ≤ (candidateCap c r a : ℝ≥0∞)} ∩
    ⋃ q : ℚ, {ω | ((I.T + (candLife c r l a ω).toNNReal : ℝ≥0) : ℝ≥0∞) < (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)} ∩
      locEvX x₀ c.s c.W c.ζ I.W I.GT (q : ℝ).toNNReal

/-- **The measurable death event of one instance.** -/
def deathEvent (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (I : StageInst Ω) (Rf : ℕ → ℝ≥0 → Ω → ℝ) (Vf : ℕ → Ω → ℝ≥0∞) (x₀ : ℝ) : Set Ω :=
  {ω | ω ∈ I.GT → oldSuccess c r l ω → ((stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω : ℝ≥0) : ℝ≥0∞) < I.V ω →
    ω ∈ deathFin c r l a I x₀ →
      (I.srecX c r l x₀ ω ∈ launchBadRec c r l a → SeedThr c.κ (I.β (I.srecX c r l x₀ ω))) ∧
      (I.srecX c r l x₀ ω ∉ launchBadRec c r l a →
        ProxThr c.κ (I.β (I.srecX c r l x₀ ω)) (fun n q => Rf n q ω) (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω)
          ((⨆ n, Vf n ω).toNNReal - stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω))}

/-- **Re-indexing a typed word** in a threshold condition with any state read off the marks. -/
theorem thresholdCondition_reindex {κ : ℝ} {c : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (htype : FCDet.IsFlowType κ 0 c xL xR ρL ρR) (w₀ : ℝ) (fL fR : ℝ → ℝ) :
    ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 0) (flowLineRhoR κ c.fn c.jumps 0 0) w₀
        (fun i => fL (flowLineXL c.fn c.jumps 0 i)) (fun j => fR (flowLineXR c.fn c.jumps 0 j)) ↔
      ForceWord.ThresholdCondition ρL ρR w₀ (fun i => fL (xL i)) (fun j => fR (xR j)) := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := htype
  subst nL nR
  change xL = flowLineXL c.fn c.jumps 0 at hxL
  change xR = flowLineXR c.fn c.jumps 0 at hxR
  change ρL = flowLineRhoL κ c.fn c.jumps 0 0 at hρL
  change ρR = flowLineRhoR κ c.fn c.jumps 0 0 at hρR
  rw [hxL, hxR, hρL, hρR]

omit [StandardBorelSpace Ω] in
/-- **A threshold condition of a measurable word with measurable mark readings is a measurable event** (countably
many word types). -/
theorem measurableSet_wordThr {κ : ℝ} {β : Ω → BoundaryWord} (hβ : Measurable β)
    (hcount : (range fun ω => wordType κ (β ω)).Countable) {w₀ : Ω → ℝ} (hw₀ : Measurable w₀)
    {fL fR : Ω → ℝ → ℝ} (hfL : ∀ {x : Ω → ℝ}, Measurable x → Measurable fun ω => fL ω (x ω))
    (hfR : ∀ {x : Ω → ℝ}, Measurable x → Measurable fun ω => fR ω (x ω)) :
    MeasurableSet {ω | ForceWord.ThresholdCondition (flowLineRhoL κ (β ω).fn (β ω).jumps 0 0)
      (flowLineRhoR κ (β ω).fn (β ω).jumps 0 0) (w₀ ω) (fun i => fL ω (flowLineXL (β ω).fn (β ω).jumps 0 i))
      (fun j => fR ω (flowLineXR (β ω).fn (β ω).jumps 0 j))} := by
  have heq : {ω | ForceWord.ThresholdCondition (flowLineRhoL κ (β ω).fn (β ω).jumps 0 0)
      (flowLineRhoR κ (β ω).fn (β ω).jumps 0 0) (w₀ ω) (fun i => fL ω (flowLineXL (β ω).fn (β ω).jumps 0 i))
      (fun j => fR ω (flowLineXR (β ω).fn (β ω).jumps 0 j))} =
      ⋃ w ∈ range fun ω => wordType κ (β ω), {ω | wordType κ (β ω) = w} ∩
        {ω | ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) (w₀ ω)
          (fun i => fL ω (typedXL κ w (β ω) i)) (fun j => fR ω (typedXR κ w (β ω) j))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop, Set.mem_range]
    constructor
    · intro h
      exact ⟨_, ⟨ω, rfl⟩, rfl, (thresholdCondition_reindex (isFlowType_typed rfl) _ (fL ω) (fR ω)).1 h⟩
    · rintro ⟨w, -, hw, h⟩
      exact (thresholdCondition_reindex (isFlowType_typed hw) _ (fL ω) (fR ω)).2 h
  rw [heq]
  refine MeasurableSet.biUnion hcount fun w _ => ?_
  refine ((measurable_wordType κ).comp hβ (measurableSet_singleton w)).inter ?_
  exact measurableSet_thresholdCondition _ _ hw₀
    (fun i => hfL ((measurable_pi_apply i).comp ((measurable_typedXL κ w).comp hβ)))
    (fun j => hfR ((measurable_pi_apply j).comp ((measurable_typedXR κ w).comp hβ)))

section Meas

omit [StandardBorelSpace Ω]

/-- An implication of measurable events is measurable. -/
theorem measurableSet_imp {p q : Ω → Prop} (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω}) :
    MeasurableSet {ω | p ω → q ω} := by
  have e : {ω | p ω → q ω} = {ω | p ω}ᶜ ∪ {ω | q ω} := by
    ext ω; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
  rw [e]; exact hp.compl.union hq

variable {Rf : ℕ → ℝ≥0 → Ω → ℝ} (hRm : ∀ n t, Measurable (Rf n t)) (hRc : ∀ n ω, Continuous fun t => Rf n t ω)
  {S u : Ω → ℝ≥0} (hS : Measurable S) (hu : Measurable u)

include hRm hRc hS in
/-- The versions' stage paths are measurable at every time. -/
theorem measurable_stgDrv_versions (n : ℕ) (t : ℝ≥0) :
    Measurable fun ω => stgDrv (fun q => Rf n q ω) (S ω) t :=
  (measurable_path_at (hRm n) (hRc n) (hS.add_const t)).sub (measurable_path_at (hRm n) (hRc n) hS)

include hu in
/-- The approximating times are measurable. -/
theorem measurable_tk_at (k : ℕ) : Measurable fun ω => tk (u ω) k :=
  (hu.coe_nnreal_real.sub_const _).real_toNNReal

include hRm hRc hS hu in
/-- The value proxy is measurable. -/
theorem measurable_stageProxyW : Measurable fun ω => stageProxyW (fun n q => Rf n q ω) (S ω) (u ω) :=
  Measurable.limsup fun n =>
    (measurable_path_at (hRm n) (hRc n) (hS.add hu)).sub (measurable_path_at (hRm n) (hRc n) hS)

include hRm hRc hS hu in
/-- The right image proxy of a measurable mark is measurable. -/
theorem measurable_stageProxyR {x : Ω → ℝ} (hx : Measurable x) :
    Measurable fun ω => stageProxyR (fun n q => Rf n q ω) (S ω) (u ω) (x ω) :=
  Measurable.limsup fun k => Measurable.limsup fun n =>
    measurable_rightImg_at (W := fun t ω => stgDrv (fun q => Rf n q ω) (S ω) t)
      (measurable_stgDrv_versions hRm hRc hS n) (fun ω => continuous_stgDrv (hRc n ω) (S ω)) hx
      (measurable_tk_at hu k)

include hRm hRc hS hu in
/-- The left image proxy of a measurable mark is measurable. -/
theorem measurable_stageProxyL {x : Ω → ℝ} (hx : Measurable x) :
    Measurable fun ω => stageProxyL (fun n q => Rf n q ω) (S ω) (u ω) (x ω) :=
  (Measurable.limsup fun k => Measurable.limsup fun n =>
    measurable_rightImg_at (W := fun t ω => -stgDrv (fun q => Rf n q ω) (S ω) t)
      (fun t => (measurable_stgDrv_versions hRm hRc hS n t).neg)
      (fun ω => (continuous_stgDrv (hRc n ω) (S ω)).neg) hx.neg (measurable_tk_at hu k)).neg

end Meas

omit [StandardBorelSpace Ω] in
/-- **The death event of one instance is measurable.** -/
theorem measurableSet_deathEvent (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (I : StageInst Ω) {Rf : ℕ → ℝ≥0 → Ω → ℝ} {Vf : ℕ → Ω → ℝ≥0∞} (x₀ : ℝ)
    (hGTm : MeasurableSet I.GT) (hS : Measurable (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T))
    (hVm : Measurable I.V) (hfin : MeasurableSet (deathFin c r l a I x₀)) (hrec : Measurable (I.srecX c r l x₀))
    (hβ : Measurable I.β) (hcount : (range fun y => wordType c.κ (I.β y)).Countable)
    (hRm : ∀ n t, Measurable (Rf n t)) (hRc : ∀ n ω, Continuous fun t => Rf n t ω) (hVfm : ∀ n, Measurable (Vf n)) :
    MeasurableSet (deathEvent c r l a I Rf Vf x₀) := by
  have hβr : Measurable fun ω => I.β (I.srecX c r l x₀ ω) := hβ.comp hrec
  have hcount' : (range fun ω => wordType c.κ (I.β (I.srecX c r l x₀ ω))).Countable :=
    hcount.mono (by rintro _ ⟨ω, rfl⟩; exact ⟨I.srecX c r l x₀ ω, rfl⟩)
  have hu : Measurable fun ω => (⨆ n, Vf n ω).toNNReal - stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω :=
    (ENNReal.measurable_toNNReal.comp (Measurable.iSup hVfm)).sub hS
  have hbad : MeasurableSet {ω | I.srecX c r l x₀ ω ∈ launchBadRec c r l a} := hrec (measurableSet_launchBadRec c r l a)
  have hseed : MeasurableSet {ω | SeedThr c.κ (I.β (I.srecX c r l x₀ ω))} :=
    measurableSet_wordThr (fL := fun _ x => x) (fR := fun _ x => x) hβr hcount' measurable_const
      (fun hx => hx) (fun hx => hx)
  have hprox : MeasurableSet {ω | ProxThr c.κ (I.β (I.srecX c r l x₀ ω)) (fun n q => Rf n q ω)
      (stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω)
      ((⨆ n, Vf n ω).toNNReal - stgStartX x₀ c.s c.W c.ζ I.W I.GT I.V I.T ω)} :=
    measurableSet_wordThr hβr hcount' (measurable_stageProxyW hRm hRc hS hu)
      (fun hx => measurable_stageProxyL hRm hRc hS hu hx) (fun hx => measurable_stageProxyR hRm hRc hS hu hx)
  refine measurableSet_imp hGTm (measurableSet_imp (measurableSet_oldSuccess c r l)
    (measurableSet_imp (measurableSet_lt hS.coe_nnreal_ennreal hVm)
    (measurableSet_imp hfin ((measurableSet_imp hbad hseed).inter (measurableSet_imp hbad.compl hprox)))))

end InteractingSLE.Theorem14.GW2Nv
