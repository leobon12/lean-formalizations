/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdiBuf

/-!
# GW2's comparisons from stage variables alone (ruling R113: root-agnostic interface)

Packet PROVE-GW2-SDE (round 6). Ruling R113: the stage identity is proved at root `0` and transported to a root `x` by
a translation lemma for the GB6 version layer (record, engine, safe law), in ROOT2's re-centred coordinates
(`relMap − relMap(x)`). PROVE-GW2-SDE states the instance in the translated coordinates.

The SDE half consumes the stage law ONLY through stage variables: a stage record, a relative driver, a cap, a word
map, a record event, a field and a stop, with `StageVar.Generates ∧ StageVar.IsSafe`
(`GW2Sdh.FrameNSafeStatement`). The root-`0` `StageInst` (GB6's explored curve from `0`, the relative chart without
re-centring) is ONE way to produce such variables (`StageInst.var`); at a root `x` the transported version layer
produces them directly. So the root-`x` instance is stated here at the level of stage variables, with every
identification input phrased through the variable's own driver `v.R` and stop `v.stop`:

* `VPkg c r` (near families, candidates, near and slow stage variables, shells), `VPkgFamily`;
  **`VPkgFamily.frameN V lam`** (ROOT2's frame, R112's dilations); **`PkgFamily.toV`** with `toV_frameN`
  (`rfl`: round 5's packages are the special case of instance-built variables);
* `VPkgSafe V` (the transported safe laws: `Generates ∧ IsSafe` per variable), `vpkgSafe_toV` (from round 2's
  `StageInst.Good`/`StageStop.Good`), **`retainedStoppedSDEStatement_vpkg`**;
* explicit drivers and stops: `vpkg_near_W/near_stop/slow_W/slow_stop`, `vpkg_slow_drv/slow_stop'`;
* the J32 buffer half in terms of the variables: `VNearImgL` (lossy near facts), `VDriverId` (S1 with `v.R`),
  `VStopCovers` (S3 with `v.stop`), `VShellChoice` (S4, start `GW2Bf.histStart`);
  **`ae_slowBufferFact_vpkg`** (PROVE-GW2-BUF's slow proof, start discharged); **`VPairInputs`**,
  **`retainedComparisonsLossy_vpkg`** (both C24 binders for J32, lossy near binder).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdi

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2Sdg GW2Sdh GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6
  GW2TipSystem.RootN4

/-- **A comparison package from stage variables**: near families and candidates, near and slow stage variables, and
the slow shells (an oriented frame without its frame change). -/
structure VPkg {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  nearFamily : List (EntryIdx c.Θ c.Q) → Ω → NearCrossingFamily.{u} c.κ
  nearCandidate : List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ
  nearVar : List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ → StageVar Ω
  slowShell : List (EntryIdx c.Θ c.Q) → ℕ → Ω → SlowShell
  slowVar : List (EntryIdx c.Θ c.Q) → ℕ → StageVar Ω

/-- Stage-variable packages for every source setup and root. -/
abbrev VPkgFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q), VPkg c r

/-- **ROOT2's frame for a stage-variable package**, with R112's near dilations. -/
def VPkgFamily.frameN (V : VPkgFamily.{u}) (lam : NearDil.{u}) : FrameNFamily.{u} :=
  fun Ω _ _ c r =>
    ⟨{ scale := rootScale r.2
       flip := fun l => flipOf l.length
       nearFamily := (V Ω c r).nearFamily
       nearCandidate := (V Ω c r).nearCandidate
       nearVar := (V Ω c r).nearVar
       slowShell := (V Ω c r).slowShell
       slowVar := (V Ω c r).slowVar }, fun l ω => nearRootScale r.2 (lam Ω c r l ω)⟩

/-- The stage-variable package of a per-stage package (instance-built variables). -/
def _root_.InteractingSLE.Theorem14.GW2Sde.PkgFamily.toV (K : PkgFamily.{u}) : VPkgFamily.{u} :=
  fun Ω _ _ c r =>
    { nearFamily := (K Ω c r).nearFamily
      nearCandidate := (K Ω c r).nearCandidate
      nearVar := fun l n m a => ((K Ω c r).inst l a).var c r l ((K Ω c r).nearStop l n m a)
      slowShell := (K Ω c r).slowShell
      slowVar := fun l a => ((K Ω c r).inst l a).var c r l ((K Ω c r).slowStop l a) }

/-- Round 5's frames are those of the instance-built variables. -/
theorem toV_frameN (K : PkgFamily.{u}) (lam : NearDil.{u}) : K.toV.frameN lam = K.rootFrameN lam := rfl

/-- **The safe laws of a stage-variable package** (at a root `x`: the transported GB6 version layer). -/
structure VPkgSafe (V : VPkgFamily.{u}) : Prop where
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((V Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((V Ω c r).nearVar l n m a).IsSafe c.κ c.P ((V Ω c r).nearVar l n m a).record
  slowSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((V Ω c r).slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((V Ω c r).slowVar l a).IsSafe c.κ c.P ((V Ω c r).slowVar l a).record

/-- Instance-built variables are safe under round 2's per-stage targets. -/
theorem vpkgSafe_toV {K : PkgFamily.{u}}
    (hinst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).inst l a).Good c r l)
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
        ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l)
    (hslow : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l) :
    VPkgSafe K.toV where
  nearSafe Ω _ _ c r l n := (hnear Ω c r l n).mono fun _ hm a =>
    ⟨(hinst Ω c r l a).generates _, (hinst Ω c r l a).isSafe (hm a)⟩
  slowSafe Ω _ _ c r k l hl a :=
    ⟨(hinst Ω c r l a).generates _, (hinst Ω c r l a).isSafe (hslow Ω c r k l hl a)⟩

/-- **The SDE half for a stage-variable package** (Theorems 1.2–1.3, R48). -/
theorem retainedStoppedSDEStatement_vpkg (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    (V : VPkgFamily.{u}) (lam : NearDil.{u})
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hV : VPkgSafe V) (hwords : FrameNWordStatement D (V.frameN lam)) :
    RetainedStoppedSDEStatement D (comparisonFamilyN (V.frameN lam)) :=
  retainedStoppedSDEStatement_of_frameNSafe h12p₀ h13₀ h13 D (V.frameN lam)
    { scale_ne := fun _ _ _ _ r => rootScale_ne_zero r.2
      nearScale_ne := fun Ω _ _ c r l ω => nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
      nearSafe := hV.nearSafe
      slowSafe := hV.slowSafe
      words := hwords }

/-! ### Explicit drivers and stops -/

section Formulas

variable (V : VPkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

theorem vpkg_near_W (ω : Ω) (n m : ℕ) (q : ℝ≥0) (ξ : Ω) :
    (((comparisonFamilyN (V.frameN lam) Ω c r).near l ω).dynamics n m).W q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * lam Ω c r l ω *
        ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
          (q / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ) := by
  simp only [comparisonFamilyN, FrameN.nearData, chooseDyn_W, FrameN.nearDrv]
  exact (orientProc_flipOf _ _ q ξ).trans (congrArg _ (scaleProc_nearRootScale r.2 _ _ q ξ))

theorem vpkg_near_stop (ω : Ω) (n m : ℕ) (ξ : Ω) (hlam : lam Ω c r l ω ≠ 0) :
    (((comparisonFamilyN (V.frameN lam) Ω c r).near l ω).dynamics n m).stop ξ =
      (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
        ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ := by
  simp only [comparisonFamilyN, FrameN.nearData, chooseDyn_stop, FrameN.nearStop]
  exact div_nearRootScale _ r.2 hlam

theorem vpkg_slow_drv (a : ℕ) (q : ℝ≥0) (ξ : Ω) :
    (V.frameN lam Ω c r).base.drv l ((V.frameN lam Ω c r).base.slowVar l a) q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((V Ω c r).slowVar l a).R (q / (4 : ℝ≥0) ^ r.2) ξ) :=
  (orientProc_flipOf _ _ q ξ).trans (congrArg _ (scaleProc_rootScale r.2 _ q ξ))

theorem vpkg_slow_stop' (a : ℕ) (ξ : Ω) :
    (V.frameN lam Ω c r).base.stop ((V.frameN lam Ω c r).base.slowVar l a) ξ =
      (4 : ℝ≥0∞) ^ r.2 * ((V Ω c r).slowVar l a).stop ξ :=
  div_rootScale _ r.2

theorem vpkg_slow_W (a : ℕ) (ω : Ω) (q : ℝ≥0) (ξ : Ω) :
    ((comparisonFamilyN (V.frameN lam) Ω c r).slow l a ω).dynamics.W q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((V Ω c r).slowVar l a).R (q / (4 : ℝ≥0) ^ r.2) ξ) := by
  rw [← vpkg_slow_drv V lam Ω c r l a q ξ]
  exact congrFun (congrFun (slowData_W _ l a ω) q) ξ

theorem vpkg_slow_stop (a : ℕ) (ω ξ : Ω) :
    ((comparisonFamilyN (V.frameN lam) Ω c r).slow l a ω).dynamics.stop ξ =
      (4 : ℝ≥0∞) ^ r.2 * ((V Ω c r).slowVar l a).stop ξ := by
  rw [← vpkg_slow_stop' V lam Ω c r l a ξ]
  exact congrFun (slowData_stop _ l a ω) ξ

end Formulas

/-! ### The J32 buffer half in terms of the stage variables -/

section Inputs

variable (V : VPkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

/-- **The lossy near facts for J32 in terms of the near stage variables** (`RootNearImg32L` with `v.R`, `v.stop`). -/
def VNearImgL (ε : ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
    ∀ n : ℕ, ∀ᶠ m in atTop, ∃ N : Set Ω, condExpKernel c.P (c.sigma r l) ω N ≤ ε ∧
      ∀ᵐ ξ ∂(condExpKernel c.P (c.sigma r l) ω), ξ ∉ N →
      0 < (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
        ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
          ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ →
        v < (n : ℝ≥0) →
        imgState ((V Ω c r).nearFamily l ω).xL ((V Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * lam Ω c r l ω * ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
            (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ))
          v ∉ nearBuffer ((V Ω c r).nearFamily l ω) n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) →
        (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
          ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).stop ξ →
        imgState ((V Ω c r).nearFamily l ω).xL ((V Ω c r).nearFamily l ω).xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * lam Ω c r l ω * ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
            (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ))
          t ∈ nearTarget ((V Ω c r).nearFamily l ω) →
        RootJ32.sourceSample c r l ((V Ω c r).nearCandidate l ω n m) ξ ∈ RootD25.reachSet

variable (a : ℕ)

/-- **S1 in terms of the slow stage variable**: on the retained gate, before the buffer, J32's centred reads are the
variable's relative driver. -/
def VDriverId : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ u : ℝ≥0, u < rootGain c r l a ξ →
    GW2Bf.j32Read c r l a (rootHistCap c r l a ξ + u) ξ - GW2Bf.j32Read c r l a (rootHistCap c r l a ξ) ξ =
      ((V Ω c r).slowVar l a).R u ξ

/-- **S3 in terms of the slow stage variable**: on the retained gate, its stop dominates the gain up to the buffer. -/
def VStopCovers : Prop :=
  ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → (rootGain c r l a ξ : ℝ≥0∞) ≤ ((V Ω c r).slowVar l a).stop ξ

/-- **S4 for a stage-variable package**: shell clauses and the start `GW2Bf.histStart` on alive histories. -/
def VShellChoice : Prop :=
  ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
    ShellFact c.κ (RootJ31.sourceDriftBound c r) ((V Ω c r).slowShell l a ω) ∧
      ((V Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω

end Inputs

theorem nearImgPathLossy_vpkg (V : VPkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    {ε : ℝ≥0∞} (hlam : ∀ ω, lam Ω c r l ω ≠ 0) (h : VNearImgL V lam Ω c r l ε) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      ∀ n, ∀ᶠ m in atTop, NearImgPathLossy ((comparisonFamilyN (V.frameN lam) Ω c r).near l ω)
        (condExpKernel c.P (c.sigma r l) ω) (((RootJ32.constructionFamily Ω c).experiment r).data.sample l)
        (((RootJ32.constructionFamily Ω c).experiment r).data.reach l) n m ε := by
  filter_upwards [h] with ω hω halive n
  filter_upwards [hω halive n] with m hm
  obtain ⟨N, hN, hae⟩ := hm
  refine ⟨N, hN, ?_⟩
  filter_upwards [hae] with ξ hξ hξN
  obtain ⟨h0, hex, htg⟩ := hξ hξN
  have hW : (fun s => (((comparisonFamilyN (V.frameN lam) Ω c r).near l ω).dynamics n m).W s ξ) =
      fun s => (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * lam Ω c r l ω *
        ((V Ω c r).nearVar l n m ((V Ω c r).nearCandidate l ω n m)).R
          (s / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ) :=
    funext fun s => vpkg_near_W V lam Ω c r l ω n m s ξ
  have hS := vpkg_near_stop V lam Ω c r l ω n m ξ (hlam ω)
  refine ⟨hS ▸ h0, fun v hv hvn => ?_, fun t htn ht htar => ?_⟩
  · rw [hW]
    exact hex v (hv.trans hS) hvn
  · rw [hW] at htar
    exact htg t htn (ht.trans_eq hS) htar

/-- **The slow buffer fact for J32 for a stage-variable package** at P-a.e. alive history (PROVE-GW2-BUF's proof of
`GW2Bf.ae_slowBufferFact_rootJ32` with the variable's driver and stop; the start is `GW2Bf.histStart`). -/
theorem ae_slowBufferFact_vpkg (h13 : Exist.Theorem13Statement.{u}) (V : VPkgFamily.{u}) (lam : NearDil.{u})
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hdrv : VDriverId V Ω c r l a) (hstop : VStopCovers V Ω c r l a)
    (hshell : VShellChoice V Ω c r l a) :
    ∀ᵐ ω ∂c.P, ω ∈ ((RootJ32.constructionFamily Ω c).experiment r).data.alive ((RootJ32.constructionFamily Ω c).G r) l →
      SlowBufferFact ((comparisonFamilyN (V.frameN lam) Ω c r).slow l a ω) (condExpKernel c.P (c.sigma r l) ω)
        (RootJ31.sourceDriftBound c r) (RootJ32.sourceSample c r l a) := by
  by_cases hord : Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l)
  · have hv₀ := GW2Bf.v0_le_historyTime c r l hord
    have hG : MeasurableSet[c.sigma r l] (rootGate c r l) := RootK32.measurableSet_sourceBuffer_gate c r l
    have hread : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l → ∀ q : ℚ≥0,
        ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 →
        (RootJ32.sourceSample c r l a ξ).2 q = GW2Bf.histStart c r l ξ +
          (V.frameN lam Ω c r).base.drv l ((V.frameN lam Ω c r).base.slowVar l a) q ξ := by
      filter_upwards [GW2Bf.ae_j32Start_eq_histStart h13 c r l hv₀, hdrv] with ξ hst hd hξG q hq
      have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
        lt_of_le_of_lt zero_le (hq.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
      have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < rootGain c r l a ξ :=
        div_four_pow_lt r.2 (by rw [← GW2Bf.j32Sample_fst]; exact hq)
      rw [GW2Bf.j32Sample_snd c r l a ξ hq, hst a hlive, hd hξG _ hu, vpkg_slow_drv]
    have hlife : ∀ᵐ ξ ∂c.P, ξ ∈ rootGate c r l →
        (RootJ32.sourceSample c r l a ξ).1 ≤
          (V.frameN lam Ω c r).base.stop ((V.frameN lam Ω c r).base.slowVar l a) ξ := by
      filter_upwards [hstop] with ξ hs hξG
      rw [GW2Bf.j32Sample_fst, vpkg_slow_stop']
      gcongr
      exact hs hξG
    filter_upwards [slowBufferFact_of_read (V.frameN lam Ω c r).base l a (RootJ31.sourceDriftBound c r)
      (RootJ32.sourceSample c r l a) hG (GW2Bf.measurable_histStart c r l) hread hlife, hshell]
      with ω h1 h2 halive
    obtain ⟨hcov, hold, -⟩ := RootJ32.alive_spec c r l ω halive
    exact h1 ⟨hcov, hold⟩ (h2 halive).1 (h2 halive).2
  · exact Eventually.of_forall fun ω halive => absurd (RootJ32.alive_spec c r l ω halive).2.2 hord

/-- **The named inputs of the lossy R11 pair for J32 from stage-variable packages** `V k` (near candidates with loss
`(k + 1)⁻¹`; slow inputs for `V 0`). -/
structure VPairInputs (V : ℕ → VPkgFamily.{u}) (lam : NearDil.{u}) : Prop where
  lam_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0
  safe : ∀ k : ℕ, VPkgSafe (V k)
  words : ∀ k : ℕ, FrameNWordStatement RootJ32.constructionFamily ((V k).frameN lam)
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), VNearImgL (V k) lam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VDriverId (V 0) Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VStopCovers (V 0) Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      VShellChoice (V 0) Ω c r l a

/-- **Both C24 binders for J32 from stage-variable packages, with the lossy near binder** (R113, R114; Theorems
1.2–1.3, R48). -/
theorem retainedComparisonsLossy_vpkg (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (V : ℕ → VPkgFamily.{u})
    (lam : NearDil.{u}) (hV : VPairInputs V lam) :
    RetainedNearModelsLossyStatement RootJ32.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ32.constructionFamily.{u} := by
  have hsde : ∀ k, RetainedStoppedSDEStatement RootJ32.constructionFamily (comparisonFamilyN ((V k).frameN lam)) :=
    fun k => retainedStoppedSDEStatement_vpkg h12p₀ h13₀ h13 (V k) lam hV.lam_ne (hV.safe k) (hV.words k)
  refine retainedComparisonsLossy_of_stoppedSDE_buffer RootJ32.constructionFamily
    (fun k => comparisonFamilyN ((V k).frameN lam)) hsde ?_ ?_
  · intro Ω _ _ c r l k
    filter_upwards [(hsde k).near Ω c r l,
      nearImgPathLossy_vpkg (V k) lam Ω c r l (hV.lam_ne Ω c r l) (hV.nearImg k Ω c r l)]
      with ω hs hi halive n
    filter_upwards [hs halive n, hi halive n] with m h1 h2
    exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2
  · intro Ω _ _ c r k l hl a
    exact ae_slowBufferFact_vpkg h13 (V 0) lam Ω c r l a (hV.driverId Ω c r k l hl a) (hV.stopCovers Ω c r k l hl a)
      (hV.shell Ω c r k l hl a)

end InteractingSLE.Theorem14.GW2Sdi
