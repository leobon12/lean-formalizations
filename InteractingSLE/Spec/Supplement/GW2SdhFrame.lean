/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdfPkg

/-!
# GW2's comparison frame with per-history near dilations (ruling R112)

Packet PROVE-GW2-SDE (round 5). Ruling R112: each NEAR comparison is dilated per history by a scale `λ` with
`λ (17/8 − S) ≤ 17/8`, `S` the stage start (PROVE-GW2-BUF's `mem_reachSet_of_scaled_target`). The slow comparisons
keep round 3's frame. This file adds a near time scale per history and retained sample to the oriented frame, and
proves the SDE half for the new comparison family:

* `FrameN c r`: an oriented frame `base : FrameO c r` with a near time scale `nearScale l ω` (the near space factor is
  `(√nearScale)⁻¹`); `FrameN.nearDrv`, `FrameN.nearStop`, `FrameN.nearData`; **`comparisonFamilyN F`** (near data
  dilated at `nearScale l ω`, slow data = round 3's);
* `FrameNWordStatement` (near words presented at `nearScale l ω`), **`FrameNSafeStatement`**,
  **`retainedStoppedSDEStatement_of_frameNSafe`**;
* ROOT2's frame with near dilations `lam` (`NearDil`): `nearRootScale k λ = (4^k λ²)⁻¹`,
  **`PkgFamily.rootFrameN K lam`**, `scaleProc_nearRootScale` (`2^k λ · X(t/(4^k λ²))`),
  **`retainedStoppedSDEStatement_rootFrameN`**, and the explicit near/slow drivers and stops
  (`rootFrameN_near_W`: `(−1)^{|l|} 2^{r.2} λ R(q/(4^{r.2} λ²))`, `rootFrameN_near_stop`: `4^{r.2} λ² τ`;
  `rootFrameN_slow_W/stop` as round 3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdh

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6
  GW2TipSystem.RootN4 Exist.StagedLaw Restart

/-- **An oriented frame with near time scales per history and retained sample.** -/
structure FrameN {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  base : FrameO c r
  nearScale : List (EntryIdx c.Θ c.Q) → Ω → ℝ≥0

/-- A frame with near time scales for every source setup and root. -/
abbrev FrameNFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    FrameN c r

section Frame

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}

/-- The near driver of a stage variable at the retained sample `ω`. -/
abbrev FrameN.nearDrv (F : FrameN c r) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (v : StageVar Ω) : ℝ≥0 → Ω → ℝ :=
  orientProc (F.base.flip l) (scaleProc (F.nearScale l ω) v.R)

/-- The near stop of a stage variable at the retained sample `ω`. -/
abbrev FrameN.nearStop (F : FrameN c r) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (v : StageVar Ω) : Ω → ℝ≥0∞ :=
  fun ξ => v.stop ξ / F.nearScale l ω

/-- **The near comparison data**, dilated at the near scale of the history and the retained sample. -/
def FrameN.nearData [StandardBorelSpace Ω] (F : FrameN c r) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    GW2JDetR11.NearData Ω c.κ where
  family := F.base.nearFamily l ω
  candidate := F.base.nearCandidate l ω
  dynamics := fun n m => chooseDyn (condExpKernel c.P (c.sigma r l) ω) c.κ (F.base.nearFamily l ω).xL
    ((F.base.nearFamily l ω).ρLs m) (F.base.nearFamily l ω).xR ((F.base.nearFamily l ω).ρRs m)
    (F.nearDrv l ω (F.base.nearVar l n m (F.base.nearCandidate l ω n m)))
    (F.nearStop l ω (F.base.nearVar l n m (F.base.nearCandidate l ω n m)))

end Frame

/-- **The comparison family with dilated near comparisons.** -/
def comparisonFamilyN (F : FrameNFamily.{u}) : GW2JDetR11.ComparisonFamily.{u} :=
  fun Ω _ _ c r => ⟨(F Ω c r).nearData, (F Ω c r).base.slowData⟩

/-- **The frame words with dilated near comparisons** (near words presented at the near scale). -/
structure FrameNWordStatement (D : ConstructionFamily.{u}) (F : FrameNFamily.{u}) : Prop where
  nearWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).record ω ∈
        ((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).E ∧
      PresentsO c.κ
        (((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).β
          (((F Ω c r).base.nearVar l n m ((F Ω c r).base.nearCandidate l ω n m)).record ω))
        ((F Ω c r).nearScale l ω) ((F Ω c r).base.flip l)
        ((F Ω c r).base.nearFamily l ω).xL (((F Ω c r).base.nearFamily l ω).ρLs m)
        ((F Ω c r).base.nearFamily l ω).xR (((F Ω c r).base.nearFamily l ω).ρRs m)
  slowWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ((F Ω c r).base.slowVar l a).record ω ∈ ((F Ω c r).base.slowVar l a).E ∧
      PresentsO c.κ (((F Ω c r).base.slowVar l a).β (((F Ω c r).base.slowVar l a).record ω))
        (F Ω c r).base.scale ((F Ω c r).base.flip l) ((F Ω c r).base.slowShell l a ω).xL
        (angleWordL c.κ ((F Ω c r).base.slowShell l a ω).φ ((F Ω c r).base.slowShell l a ω).mL
          ((F Ω c r).base.slowShell l a ω).ρL₀)
        ((F Ω c r).base.slowShell l a ω).xR
        (angleWordR c.κ ((F Ω c r).base.slowShell l a ω).φ ((F Ω c r).base.slowShell l a ω).mR
          ((F Ω c r).base.slowShell l a ω).ρR₀)

/-- **The per-stage safe laws consumed by the SDE half with dilated near comparisons.** -/
structure FrameNSafeStatement (D : ConstructionFamily.{u}) (F : FrameNFamily.{u}) : Prop where
  scale_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), (F Ω c r).base.scale ≠ 0
  nearScale_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), (F Ω c r).nearScale l ω ≠ 0
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((F Ω c r).base.nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).base.nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).base.nearVar l n m a).record
  slowSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((F Ω c r).base.slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).base.slowVar l a).IsSafe c.κ c.P ((F Ω c r).base.slowVar l a).record
  words : FrameNWordStatement D F

/-- **JOINTDET's `RetainedStoppedSDEStatement` for the comparisons with dilated near comparisons**
(Theorems 1.2–1.3, R48). -/
theorem retainedStoppedSDEStatement_of_frameNSafe (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (F : FrameNFamily.{u}) (hF : FrameNSafeStatement D F) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamilyN F) := by
  refine ⟨fun Ω _ _ c r l => ?_, fun Ω _ _ c r k l hl a => ?_⟩
  · obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
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
    filter_upwards [hall, hF.words.nearWord Ω c r l] with ω hω hw halive n
    filter_upwards [hF.nearSafe Ω c r l n, hw halive n] with m hs hm
    exact isStopped_chooseDyn (exists_isStopped_orient (hF.nearScale_ne Ω c r l ω) _
      (fun hft => hω n m _ (hs _) hm.1 hft) hm.2)
  · obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
    have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
    have hs := hF.slowSafe Ω c r k l hl a
    filter_upwards [StageVar.ae_exists_isStopped_of_generates c.h12p h13 c.hκ hFd h𝒢 hs.1 hs.2,
      hF.words.slowWord Ω c r k l hl a] with ω hω hw halive
    obtain ⟨hE, hpr⟩ := hw halive
    exact isStopped_chooseDyn (exists_isStopped_orient (hF.scale_ne Ω c r) _ (fun hft => hω hE hft) hpr)

/-! ### ROOT2's frame with near dilations -/

/-- **Per-history near dilations** (space factors `λ`) for every source setup and root. -/
abbrev NearDil :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_ : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → Ω → ℝ≥0

/-- The near time scale at root scale `k` and dilation `λ`: `(4^k λ²)⁻¹`. -/
def nearRootScale (k : ℕ) (lam : ℝ≥0) : ℝ≥0 := ((4 : ℝ≥0) ^ k * lam ^ 2)⁻¹

theorem nearRootScale_ne_zero (k : ℕ) {lam : ℝ≥0} (hlam : lam ≠ 0) : nearRootScale k lam ≠ 0 :=
  inv_ne_zero (mul_ne_zero (pow_ne_zero k (by norm_num)) (pow_ne_zero 2 hlam))

theorem sqrt_nearRootScale_inv (k : ℕ) (lam : ℝ≥0) :
    (Real.sqrt (nearRootScale k lam))⁻¹ = (2 : ℝ) ^ k * lam := by
  have h : ((nearRootScale k lam : ℝ≥0) : ℝ) = ((2 : ℝ) ^ k * lam)⁻¹ ^ 2 := by
    simp only [nearRootScale, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_pow]
    rw [inv_pow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [h, Real.sqrt_sq (by positivity), inv_inv]

/-- **The near dilation**: `scaleProc (nearRootScale k λ) X t = 2^k λ · X(t / (4^k λ²))`. -/
theorem scaleProc_nearRootScale {Ω : Type*} (k : ℕ) (lam : ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    scaleProc (nearRootScale k lam) X t ω = (2 : ℝ) ^ k * lam * X (t / ((4 : ℝ≥0) ^ k * lam ^ 2)) ω := by
  simp only [scaleProc]
  rw [sqrt_nearRootScale_inv]
  simp only [nearRootScale, div_eq_inv_mul]

theorem div_nearRootScale (x : ℝ≥0∞) (k : ℕ) {lam : ℝ≥0} (hlam : lam ≠ 0) :
    x / (nearRootScale k lam : ℝ≥0∞) = (4 : ℝ≥0∞) ^ k * (lam : ℝ≥0∞) ^ 2 * x := by
  have h4 : ((4 : ℝ≥0) ^ k * lam ^ 2 : ℝ≥0) ≠ 0 := mul_ne_zero (pow_ne_zero k (by norm_num)) (pow_ne_zero 2 hlam)
  rw [nearRootScale, ENNReal.coe_inv h4, div_eq_mul_inv, inv_inv, mul_comm]
  push_cast
  rfl

/-- **ROOT2's frame with near dilations**: slow comparisons as round 3 (`rootScale r.2`, orientation `(−1)^{|l|}`),
near comparisons at the time scale `(4^{r.2} λ²)⁻¹`, `λ = lam Ω c r l ω`. -/
def _root_.InteractingSLE.Theorem14.GW2Sde.PkgFamily.rootFrameN (K : PkgFamily.{u}) (lam : NearDil.{u}) :
    FrameNFamily.{u} :=
  fun Ω _ _ c r => ⟨(K.rootFrame Ω c r).frame, fun l ω => nearRootScale r.2 (lam Ω c r l ω)⟩

/-- **The SDE property for ROOT2's frame with near dilations** (Theorems 1.2–1.3, R48): from round 2's per-stage
targets and the frame words (near words presented at the dilated scale). -/
theorem retainedStoppedSDEStatement_rootFrameN (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    {K : PkgFamily.{u}} {lam : NearDil.{u}}
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hinst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).inst l a).Good c r l)
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
        ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l)
    (hslow : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l)
    (hwords : FrameNWordStatement D (K.rootFrameN lam)) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamilyN (K.rootFrameN lam)) :=
  retainedStoppedSDEStatement_of_frameNSafe h12p₀ h13₀ h13 D (K.rootFrameN lam)
    { scale_ne := fun _ _ _ _ r => rootScale_ne_zero r.2
      nearScale_ne := fun Ω _ _ c r l ω => nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
      nearSafe := fun Ω _ _ c r l n => (hnear Ω c r l n).mono fun _ hm a =>
        ⟨(hinst Ω c r l a).generates _, (hinst Ω c r l a).isSafe (hm a)⟩
      slowSafe := fun Ω _ _ c r k l hl a =>
        ⟨(hinst Ω c r l a).generates _, (hinst Ω c r l a).isSafe (hslow Ω c r k l hl a)⟩
      words := hwords }

/-! ### The comparison dynamics in ROOT2's frame with near dilations, explicitly -/

/-- **The near comparison driver**: `(−1)^{|l|} · 2^{r.2} λ · R(q / (4^{r.2} λ²))`. -/
theorem rootFrameN_near_W (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (n m : ℕ) (q : ℝ≥0) (ξ : Ω) :
    (((comparisonFamilyN (K.rootFrameN lam) Ω c r).near l ω).dynamics n m).W q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * lam Ω c r l ω *
        ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c
          (q / ((4 : ℝ≥0) ^ r.2 * lam Ω c r l ω ^ 2)) ξ) := by
  simp only [comparisonFamilyN, FrameN.nearData, chooseDyn_W, FrameN.nearDrv]
  exact (orientProc_flipOf _ _ q ξ).trans (congrArg _ (scaleProc_nearRootScale r.2 _ _ q ξ))

/-- **The near comparison stop**: `4^{r.2} λ²` times the near stage stop. -/
theorem rootFrameN_near_stop (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (n m : ℕ) (ξ : Ω) (hlam : lam Ω c r l ω ≠ 0) :
    (((comparisonFamilyN (K.rootFrameN lam) Ω c r).near l ω).dynamics n m).stop ξ =
      (4 : ℝ≥0∞) ^ r.2 * (lam Ω c r l ω : ℝ≥0∞) ^ 2 *
        ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ := by
  simp only [comparisonFamilyN, FrameN.nearData, chooseDyn_stop, FrameN.nearStop]
  exact div_nearRootScale _ r.2 hlam

/-- The slow comparisons with near dilations are round 3's. -/
theorem rootFrameN_slow (K : PkgFamily.{u}) (lam : NearDil.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    (comparisonFamilyN (K.rootFrameN lam) Ω c r).slow = (comparisonFamilyO K.rootFrame.frame Ω c r).slow :=
  rfl

end InteractingSLE.Theorem14.GW2Sdh
