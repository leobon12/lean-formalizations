/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdiVar

/-!
# The SDE half with the time-order guard (ruling R119, decision D1)

Packet PROVE-GW2-SDE (round 10). Decision D1: every per-history statement of the stage layer that is not already
guarded by an alive event gets the deterministic guard `TimeOrdered 0 (RootJ31.historyProgram c r l)`
(`HistOrdered c r l`). Histories that are not time-ordered are never alive (`RootJ32.alive_spec`), so the SDE half is
re-proved with the extra hypothesis `AliveOrdered D` ("alive histories of `D` are time-ordered") and a case split on
the guard (vacuous in the unordered case).

* `HistOrdered`, `AliveOrdered`, **`aliveOrdered_rootJ32`**;
* the two halves of JOINTDET's `RetainedStoppedSDEStatement` as statements: `RetainedStoppedNearSDE`, and the slow
  half EVENTUALLY in a version index `n` (decision D3), `RetainedStoppedSlowSDEN`; `FrameNNearWord`,
  `FrameNSlowWordN` (the slow word eventually in `n`);
* **`retainedStoppedNearSDE_of_safeT`**, **`retainedStoppedSlowSDEN_of_safeT`**: the halves from guarded safe laws;
* `FrameNSafeStatementT` (`FrameNSafeStatement` with guarded `nearSafe`/`slowSafe`),
  **`retainedStoppedSDEStatement_of_frameNSafeT`**;
* `VPkgSafeT` (`VPkgSafe` with guarded `nearSafe`/`slowSafe`), **`retainedStoppedSDEStatement_vpkgT`**;
* **`retainedStoppedSDEStatement_rootFrameNT`** (round 5's per-stage targets, guarded).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdx

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2Sdh GW2Sdi GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6
  GW2TipSystem.RootN4 Exist.StagedLaw Restart

/-- **The time-order guard of decision D1** (deterministic in the history). -/
abbrev HistOrdered {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : Prop :=
  Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l)

/-- **Alive histories of `D` are time-ordered** (almost surely). -/
def AliveOrdered (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → HistOrdered c r l

/-- **J32's alive histories are time-ordered** (`RootJ32.alive_spec`, third component). -/
theorem aliveOrdered_rootJ32 : AliveOrdered RootJ32.constructionFamily.{u} :=
  fun _ _ _ c r l => Eventually.of_forall fun ω h => (RootJ32.alive_spec c r l ω h).2.2

/-- The unordered case of a guarded statement is vacuous on alive histories. -/
theorem ae_alive_of_not_ordered {D : ConstructionFamily.{u}} (hord : AliveOrdered D) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)}
    (h : ¬ HistOrdered c r l) (p : Ω → Prop) :
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → p ω := by
  filter_upwards [hord Ω c r l] with ω hω halive using absurd (hω halive) h

/-! ### The two halves of the stopped SDE -/

/-- The near half of JOINTDET's `RetainedStoppedSDEStatement` (its `near` field). -/
def RetainedStoppedNearSDE (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop,
        let z := (C Ω c r).near l ω
        (z.dynamics n m).IsStopped (condExpKernel c.P (c.sigma r l) ω) c.κ
          z.family.xL (z.family.ρLs m) z.family.xR (z.family.ρRs m)

/-- **The slow half of the stopped SDE, eventually in the version index `n`** (decision D3). -/
def RetainedStoppedSlowSDEN (D : ConstructionFamily.{u}) (S : ℕ → ComparisonFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ᶠ n in atTop,
      let z := (S n Ω c r).slow l a ω
      z.dynamics.IsStopped (condExpKernel c.P (c.sigma r l) ω) c.κ
        z.xL (angleWordL c.κ z.φ z.mL z.ρL₀) z.xR (angleWordR c.κ z.φ z.mR z.ρR₀)

/-- **The successor of `RetainedStoppedSDEStatement`** (decision D3): the near half for `C`, the slow half eventually
in `n` for `S n`. -/
structure RetainedStoppedSDEStatementN (D : ConstructionFamily.{u}) (C : ComparisonFamily.{u})
    (S : ℕ → ComparisonFamily.{u}) : Prop where
  near : RetainedStoppedNearSDE D C
  slow : RetainedStoppedSlowSDEN D S

/-- The exact slow half is the eventual one for the constant family. -/
theorem RetainedStoppedSDEStatement.toN {D : ConstructionFamily.{u}} {C : ComparisonFamily.{u}}
    (h : RetainedStoppedSDEStatement D C) : RetainedStoppedSDEStatementN D C fun _ => C :=
  ⟨h.near, fun Ω _ _ c r k l hl a => (h.slow Ω c r k l hl a).mono fun _ hω halive =>
    Eventually.of_forall fun _ => hω halive⟩

/-- The eventual slow half for a constant family is the exact one. -/
theorem RetainedStoppedSDEStatementN.of_const {D : ConstructionFamily.{u}} {C : ComparisonFamily.{u}}
    (h : RetainedStoppedSDEStatementN D C fun _ => C) : RetainedStoppedSDEStatement D C :=
  ⟨h.near, fun Ω _ _ c r k l hl a => (h.slow Ω c r k l hl a).mono fun _ hω halive =>
    (hω halive).exists.choose_spec⟩

/-- The near words of a frame (`FrameNWordStatement.nearWord`). -/
def FrameNNearWord (D : ConstructionFamily.{u}) (F : FrameNFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).record ω ∈
        ((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).E ∧
      PresentsO c.κ
        (((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).β
          (((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).record ω))
        ((F Ω c r).nearScale l ω) ((F Ω c r).base.flip l)
        ((F Ω c r).base.nearFamily l ω).xL (((F Ω c r).base.nearFamily l ω).ρLs m)
        ((F Ω c r).base.nearFamily l ω).xR (((F Ω c r).base.nearFamily l ω).ρRs m)

/-- **The slow words eventually in the version index `n`** (decision D3) for frames `F n`. -/
def FrameNSlowWordN (D : ConstructionFamily.{u}) (F : ℕ → FrameNFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (k : ℕ)
    (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ᶠ n in atTop,
      ((F n Ω c r).base.slowVar l a).record ω ∈ ((F n Ω c r).base.slowVar l a).E ∧
      PresentsO c.κ (((F n Ω c r).base.slowVar l a).β (((F n Ω c r).base.slowVar l a).record ω))
        (F n Ω c r).base.scale ((F n Ω c r).base.flip l) ((F n Ω c r).base.slowShell l a ω).xL
        (angleWordL c.κ ((F n Ω c r).base.slowShell l a ω).φ ((F n Ω c r).base.slowShell l a ω).mL
          ((F n Ω c r).base.slowShell l a ω).ρL₀)
        ((F n Ω c r).base.slowShell l a ω).xR
        (angleWordR c.κ ((F n Ω c r).base.slowShell l a ω).φ ((F n Ω c r).base.slowShell l a ω).mR
          ((F n Ω c r).base.slowShell l a ω).ρR₀)

/-- The exact slow words give the eventual ones for the constant family. -/
theorem frameNSlowWordN_const {D : ConstructionFamily.{u}} {F : FrameNFamily.{u}} (h : FrameNWordStatement D F) :
    FrameNSlowWordN D fun _ => F :=
  fun Ω _ _ c r k l hl a => (h.slowWord Ω c r k l hl a).mono fun _ hω halive => Eventually.of_forall fun _ => hω halive

/-! ### The halves from guarded safe laws -/

/-- **The near half from guarded near safe laws** (Theorems 1.2–1.3, R48). -/
theorem retainedStoppedNearSDE_of_safeT (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (F : FrameNFamily.{u}) (hord : AliveOrdered D)
    (hscale : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), (F Ω c r).nearScale l ω ≠ 0)
    (hsafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
        ∀ a : ℕ, ((F Ω c r).base.nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
          ((F Ω c r).base.nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).base.nearVar l n m a).record)
    (hword : FrameNNearWord D F) :
    RetainedStoppedNearSDE D (comparisonFamilyN F) := by
  intro Ω _ _ c r l
  by_cases hTO : HistOrdered c r l
  swap
  · exact ae_alive_of_not_ordered hord hTO _
  obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
  have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hall : ∀ᵐ ω ∂c.P, ∀ n m a : ℕ,
      (((F Ω c r).base.nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).base.nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).base.nearVar l n m a).record) →
      ((F Ω c r).base.nearVar l n m a).record ω ∈ ((F Ω c r).base.nearVar l n m a).E →
      ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
        FCDet.IsFlowType c.κ 0
          (((F Ω c r).base.nearVar l n m a).β (((F Ω c r).base.nearVar l n m a).record ω)) xL xR ρL ρR →
        ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = ((F Ω c r).base.nearVar l n m a).R ∧
          d.stop = ((F Ω c r).base.nearVar l n m a).stop ∧
          d.IsStopped (condExpKernel c.P (c.sigma r l) ω) c.κ xL ρL xR ρR := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun a => ?_
    by_cases hs : ((F Ω c r).base.nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).base.nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).base.nearVar l n m a).record
    · filter_upwards [StageVar.ae_exists_isStopped_of_generates c.h12p h13 c.hκ hFd h𝒢 hs.1 hs.2]
        with ω hω _ hE nL nR xL ρL xR ρR hw
      exact hω hE hw
    · exact Eventually.of_forall fun ω h => absurd h hs
  filter_upwards [hall, hword Ω c r l] with ω hω hw halive n
  filter_upwards [hsafe Ω c r l hTO n, hw halive n] with m hs hm
  exact isStopped_chooseDyn (exists_isStopped_orient (hscale Ω c r l ω) _
    (fun hft => hω n m _ (hs _) hm.1 hft) hm.2)

/-- **The slow half, eventually in the version index, from guarded slow safe laws for every version** (Theorems
1.2–1.3, R48). -/
theorem retainedStoppedSlowSDEN_of_safeT (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (F : ℕ → FrameNFamily.{u}) (hord : AliveOrdered D)
    (hscale : ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), (F n Ω c r).base.scale ≠ 0)
    (hsafe : ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
        HistOrdered c r l → ∀ a : ℕ, ((F n Ω c r).base.slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
          ((F n Ω c r).base.slowVar l a).IsSafe c.κ c.P ((F n Ω c r).base.slowVar l a).record)
    (hword : FrameNSlowWordN D F) :
    RetainedStoppedSlowSDEN D fun n => comparisonFamilyN (F n) := by
  intro Ω _ _ c r k l hl a
  by_cases hTO : HistOrdered c r l
  swap
  · exact ae_alive_of_not_ordered hord hTO _
  obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
  have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hall := ae_all_iff.2 fun n => StageVar.ae_exists_isStopped_of_generates c.h12p h13 c.hκ hFd h𝒢
    (hsafe n Ω c r k l hl hTO a).1 (hsafe n Ω c r k l hl hTO a).2
  filter_upwards [hall, hword Ω c r k l hl a] with ω hω hw halive
  filter_upwards [hw halive] with n hn
  exact isStopped_chooseDyn (exists_isStopped_orient (hscale n Ω c r) _ (fun hft => hω n hn.1 hft) hn.2)

/-! ### `FrameNSafeStatement` with the guard -/

/-- **`FrameNSafeStatement` with guarded safe laws** (decision D1). -/
structure FrameNSafeStatementT (D : ConstructionFamily.{u}) (F : FrameNFamily.{u}) : Prop where
  scale_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), (F Ω c r).base.scale ≠ 0
  nearScale_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), (F Ω c r).nearScale l ω ≠ 0
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ∀ a : ℕ, ((F Ω c r).base.nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).base.nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).base.nearVar l n m a).record
  slowSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
      HistOrdered c r l → ∀ a : ℕ, ((F Ω c r).base.slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).base.slowVar l a).IsSafe c.κ c.P ((F Ω c r).base.slowVar l a).record
  words : FrameNWordStatement D F

/-- The unguarded statement implies the guarded one. -/
theorem FrameNSafeStatement.toT {D : ConstructionFamily.{u}} {F : FrameNFamily.{u}} (h : FrameNSafeStatement D F) :
    FrameNSafeStatementT D F :=
  ⟨h.scale_ne, h.nearScale_ne, fun Ω _ _ c r l _ => h.nearSafe Ω c r l,
    fun Ω _ _ c r k l hl _ => h.slowSafe Ω c r k l hl, h.words⟩

/-- **JOINTDET's `RetainedStoppedSDEStatement` from guarded safe laws** (decision D1; Theorems 1.2–1.3, R48): the
successor of `GW2Sdh.retainedStoppedSDEStatement_of_frameNSafe` with the extra hypothesis `AliveOrdered D`. -/
theorem retainedStoppedSDEStatement_of_frameNSafeT (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (F : FrameNFamily.{u}) (hord : AliveOrdered D) (hF : FrameNSafeStatementT D F) :
    RetainedStoppedSDEStatement D (comparisonFamilyN F) :=
  RetainedStoppedSDEStatementN.of_const
    ⟨retainedStoppedNearSDE_of_safeT h12p₀ h13₀ h13 D F hord hF.nearScale_ne hF.nearSafe hF.words.nearWord,
      retainedStoppedSlowSDEN_of_safeT h12p₀ h13₀ h13 D (fun _ => F) hord (fun _ => hF.scale_ne)
        (fun _ => hF.slowSafe) (frameNSlowWordN_const hF.words)⟩

/-! ### `VPkgSafe` with the guard -/

/-- **`VPkgSafe` with guarded safe laws** (decision D1). -/
structure VPkgSafeT (V : VPkgFamily.{u}) : Prop where
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ∀ a : ℕ, ((V Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((V Ω c r).nearVar l n m a).IsSafe c.κ c.P ((V Ω c r).nearVar l n m a).record
  slowSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
      HistOrdered c r l → ∀ a : ℕ, ((V Ω c r).slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((V Ω c r).slowVar l a).IsSafe c.κ c.P ((V Ω c r).slowVar l a).record

theorem VPkgSafe.toT {V : VPkgFamily.{u}} (h : VPkgSafe V) : VPkgSafeT V :=
  ⟨fun Ω _ _ c r l _ => h.nearSafe Ω c r l, fun Ω _ _ c r k l hl _ => h.slowSafe Ω c r k l hl⟩

/-- **The SDE half for a stage-variable package with guarded safe laws** (decision D1; Theorems 1.2–1.3, R48). -/
theorem retainedStoppedSDEStatement_vpkgT (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    (V : VPkgFamily.{u}) (lam : NearDil.{u})
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hord : AliveOrdered D) (hV : VPkgSafeT V) (hwords : FrameNWordStatement D (V.frameN lam)) :
    RetainedStoppedSDEStatement D (comparisonFamilyN (V.frameN lam)) :=
  retainedStoppedSDEStatement_of_frameNSafeT h12p₀ h13₀ h13 D (V.frameN lam) hord
    { scale_ne := fun _ _ _ _ r => rootScale_ne_zero r.2
      nearScale_ne := fun Ω _ _ c r l ω => nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
      nearSafe := hV.nearSafe
      slowSafe := hV.slowSafe
      words := hwords }

/-- **The SDE property for ROOT2's frame with near dilations from guarded per-stage targets** (decision D1; the
instance, its near stops and its slow stops are `Good` only on time-ordered histories). -/
theorem retainedStoppedSDEStatement_rootFrameNT (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    {K : PkgFamily.{u}} {lam : NearDil.{u}}
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hord : AliveOrdered D)
    (hinst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ a : ℕ,
        ((K Ω c r).inst l a).Good c r l)
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
        ∀ a : ℕ, ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l)
    (hslow : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
        HistOrdered c r l → ∀ a : ℕ, ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l)
    (hwords : FrameNWordStatement D (K.rootFrameN lam)) :
    RetainedStoppedSDEStatement D (comparisonFamilyN (K.rootFrameN lam)) :=
  retainedStoppedSDEStatement_of_frameNSafeT h12p₀ h13₀ h13 D (K.rootFrameN lam) hord
    { scale_ne := fun _ _ _ _ r => rootScale_ne_zero r.2
      nearScale_ne := fun Ω _ _ c r l ω => nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
      nearSafe := fun Ω _ _ c r l hTO n => (hnear Ω c r l hTO n).mono fun _ hm a =>
        ⟨(hinst Ω c r l hTO a).generates _, (hinst Ω c r l hTO a).isSafe (hm a)⟩
      slowSafe := fun Ω _ _ c r k l hl hTO a =>
        ⟨(hinst Ω c r l hTO a).generates _, (hinst Ω c r l hTO a).isSafe (hslow Ω c r k l hl hTO a)⟩
      words := hwords }

end InteractingSLE.Theorem14.GW2Sdx
