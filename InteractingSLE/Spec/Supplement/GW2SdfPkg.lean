/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdfFrame
import InteractingSLE.Spec.Supplement.GW2SdeNeeds

/-!
# GW2's retained stopped SDE: the per-stage targets in the samples' frame

Packet PROVE-GW2-SDE (round 3). Round 2's package (`GW2Sde.Pkg`: an instance for every history and candidate, the
physical stops and the frame shells) together with a frame change (`scale`, `flip`), and its reduction:

* `PkgO`, `PkgO.frame`, `PkgOFamily`, `PkgOFamily.frame`; **`PkgFamily.rootFrame`**: ROOT2's frame, time scale
  `rootScale r.2 = (4^{r.2})⁻¹` (space factor `2^{r.2}`) and orientation `flipOf |l|` (`ε = (−1)^{|l|}`);
* `FrameOWordStatement` (the frame words, presented through the frame change);
* **`PkgOGoodStatement D K`**: round 2's per-stage targets (`StageInst.Good`, `StageStop.Good`) with the frame words
  in the samples' frame;
* **`frameOSafeStatement_of_pkgOGood`**, **`retainedStoppedSDEStatement_of_pkgOGood`**,
  **`retainedStoppedSDEStatement_rootFrame`** (the comparison family whose dynamics match ROOT2's samples).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdf

open GW2JDetR11 GW2Sde GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 Restart

/-- **A per-stage package with a frame change.** -/
structure PkgO {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  pkg : Pkg c r
  scale : ℝ≥0
  flip : List (EntryIdx c.Θ c.Q) → Bool

/-- The oriented frame of a package with a frame change. -/
def PkgO.frame {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} (K : PkgO c r) :
    FrameO c r where
  scale := K.scale
  flip := K.flip
  nearFamily := K.pkg.nearFamily
  nearCandidate := K.pkg.nearCandidate
  nearVar l n m a := (K.pkg.inst l a).var c r l (K.pkg.nearStop l n m a)
  slowShell := K.pkg.slowShell
  slowVar l a := (K.pkg.inst l a).var c r l (K.pkg.slowStop l a)

/-- A package with a frame change for every source setup and root. -/
abbrev PkgOFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q), PkgO c r

/-- The oriented frame family of a package family with frame changes. -/
def PkgOFamily.frame (K : PkgOFamily.{u}) : FrameOFamily.{u} := fun Ω _ _ c r => (K Ω c r).frame

/-- **ROOT2's frame**: time scale `(4^{r.2})⁻¹` (space factor `2^{r.2}`) and orientation `(−1)^{|l|}`. -/
def _root_.InteractingSLE.Theorem14.GW2Sde.PkgFamily.rootFrame (K : PkgFamily.{u}) : PkgOFamily.{u} :=
  fun Ω _ _ c r => ⟨K Ω c r, rootScale r.2, fun l => flipOf l.length⟩

/-- **The frame words in the samples' frame** (target for ROOT2 / the near-comparison work). -/
structure FrameOWordStatement (D : ConstructionFamily.{u}) (F : FrameOFamily.{u}) : Prop where
  nearWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).record ω ∈
        ((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).E ∧
      PresentsO c.κ
        (((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).β
          (((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).record ω))
        (F Ω c r).scale ((F Ω c r).flip l)
        ((F Ω c r).nearFamily l ω).xL (((F Ω c r).nearFamily l ω).ρLs m) ((F Ω c r).nearFamily l ω).xR
        (((F Ω c r).nearFamily l ω).ρRs m)
  slowWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ((F Ω c r).slowVar l a).record ω ∈ ((F Ω c r).slowVar l a).E ∧
      PresentsO c.κ (((F Ω c r).slowVar l a).β (((F Ω c r).slowVar l a).record ω)) (F Ω c r).scale
        ((F Ω c r).flip l) ((F Ω c r).slowShell l a ω).xL
        (angleWordL c.κ ((F Ω c r).slowShell l a ω).φ ((F Ω c r).slowShell l a ω).mL
          ((F Ω c r).slowShell l a ω).ρL₀)
        ((F Ω c r).slowShell l a ω).xR
        (angleWordR c.κ ((F Ω c r).slowShell l a ω).φ ((F Ω c r).slowShell l a ω).mR
          ((F Ω c r).slowShell l a ω).ρR₀)

/-- **The per-stage targets in the samples' frame** (named input; round 2's targets with the frame words presented
through the frame change). -/
structure PkgOGoodStatement (D : ConstructionFamily.{u}) (K : PkgOFamily.{u}) : Prop where
  scale_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), (K Ω c r).scale ≠ 0
  inst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).pkg.inst l a).Good c r l
  nearStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((K Ω c r).pkg.nearStop l n m a).Good ((K Ω c r).pkg.inst l a) c r l
  slowStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((K Ω c r).pkg.slowStop l a).Good ((K Ω c r).pkg.inst l a) c r l
  words : FrameOWordStatement D K.frame

/-- **`FrameOSafeStatement` from the per-stage targets.** -/
theorem frameOSafeStatement_of_pkgOGood {D : ConstructionFamily.{u}} {K : PkgOFamily.{u}}
    (hK : PkgOGoodStatement D K) : FrameOSafeStatement D K.frame where
  scale_ne := hK.scale_ne
  nearSafe Ω _ _ c r l n := (hK.nearStop Ω c r l n).mono fun _ hm a =>
    ⟨(hK.inst Ω c r l a).generates _, (hK.inst Ω c r l a).isSafe (hm a)⟩
  nearWord := hK.words.nearWord
  slowSafe Ω _ _ c r k l hl a :=
    ⟨(hK.inst Ω c r l a).generates _, (hK.inst Ω c r l a).isSafe (hK.slowStop Ω c r k l hl a)⟩
  slowWord := hK.words.slowWord

/-- **JOINTDET's `RetainedStoppedSDEStatement` for the dilated and oriented comparisons, from the per-stage
targets** (Theorems 1.2–1.3, R48). -/
theorem retainedStoppedSDEStatement_of_pkgOGood (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    {K : PkgOFamily.{u}} (hK : PkgOGoodStatement D K) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamilyO K.frame) :=
  retainedStoppedSDEStatement_of_frameOSafe h12p₀ h13₀ h13 D K.frame (frameOSafeStatement_of_pkgOGood hK)

/-- ROOT2's frame has a nonzero time scale. -/
theorem rootFrame_scale_ne (K : PkgFamily.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
      (K.rootFrame Ω c r).scale ≠ 0 :=
  fun _ _ _ _ r => rootScale_ne_zero r.2

/-- **The SDE property for ROOT2's frame** (dynamics `(−1)^{|l|} 2^{r.2} R(· / 4^{r.2})`, stops `4^{r.2} τ`): from
round 2's per-stage targets and the frame words in ROOT2's frame. -/
theorem retainedStoppedSDEStatement_rootFrame (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) {D : ConstructionFamily.{u}}
    {K : PkgFamily.{u}}
    (hinst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).inst l a).Good c r l)
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
        ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l)
    (hslow : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l)
    (hwords : FrameOWordStatement D K.rootFrame.frame) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamilyO K.rootFrame.frame) :=
  retainedStoppedSDEStatement_of_pkgOGood h12p₀ h13₀ h13
    ⟨rootFrame_scale_ne K, hinst, hnear, hslow, hwords⟩

/-! ### The comparison dynamics in ROOT2's frame, explicitly (for the buffer half) -/

/-- **The slow comparison driver in ROOT2's frame**: `(−1)^{|l|} · 2^{r.2} · R(q / 4^{r.2})` with `R` the stage relative
driver of the candidate's instance. -/
theorem rootFrame_slow_W (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (q : ℝ≥0)
    (ξ : Ω) :
    ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω).dynamics.W q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 * ((K Ω c r).inst l a).drv c (q / (4 : ℝ≥0) ^ r.2) ξ) := by
  simp only [comparisonFamilyO, FrameO.slowData, chooseDyn_W, FrameO.drv]
  exact (orientProc_flipOf _ _ q ξ).trans (congrArg _ (scaleProc_rootScale r.2 _ q ξ))

/-- **The near comparison driver in ROOT2's frame.** -/
theorem rootFrame_near_W (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (n m : ℕ) (q : ℝ≥0)
    (ξ : Ω) :
    (((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω).dynamics n m).W q ξ =
      (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
        ((K Ω c r).inst l ((K Ω c r).nearCandidate l ω n m)).drv c (q / (4 : ℝ≥0) ^ r.2) ξ) := by
  simp only [comparisonFamilyO, FrameO.nearData, chooseDyn_W, FrameO.drv]
  exact (orientProc_flipOf _ _ q ξ).trans (congrArg _ (scaleProc_rootScale r.2 _ q ξ))

theorem div_rootScale (x : ℝ≥0∞) (k : ℕ) : x / (rootScale k : ℝ≥0∞) = (4 : ℝ≥0∞) ^ k * x := by
  have h4 : ((4 : ℝ≥0) ^ k : ℝ≥0) ≠ 0 := pow_ne_zero k (by norm_num)
  rw [rootScale, ENNReal.coe_inv h4, div_eq_mul_inv, inv_inv, mul_comm]
  push_cast
  rfl

/-- **The slow comparison stop in ROOT2's frame**: `4^{r.2}` times the stage stop. -/
theorem rootFrame_slow_stop (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω ξ : Ω) :
    ((comparisonFamilyO K.rootFrame.frame Ω c r).slow l a ω).dynamics.stop ξ =
      (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).slowStop l a).stop ξ := by
  simp only [comparisonFamilyO, FrameO.slowData, chooseDyn_stop, FrameO.stop]
  exact div_rootScale _ r.2

/-- **The near comparison stop in ROOT2's frame.** -/
theorem rootFrame_near_stop (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (n m : ℕ) (ξ : Ω) :
    (((comparisonFamilyO K.rootFrame.frame Ω c r).near l ω).dynamics n m).stop ξ =
      (4 : ℝ≥0∞) ^ r.2 * ((K Ω c r).nearStop l n m ((K Ω c r).nearCandidate l ω n m)).stop ξ := by
  simp only [comparisonFamilyO, FrameO.nearData, chooseDyn_stop, FrameO.stop]
  exact div_rootScale _ r.2

end InteractingSLE.Theorem14.GW2Sdf
