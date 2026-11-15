/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdfScale
import InteractingSLE.Spec.Supplement.GW2SdeWire

/-!
# GW2's retained stopped SDE in the samples' frame (dilated and oriented comparisons)

Packet PROVE-GW2-SDE (round 3). ROOT2's samples read the future driver as `ε · a · (relative driver)(· / a²)` with
`a = 2^{r.2}` (`RootJ31.sourceSample`) and `ε = (−1)^{|l|}`. So the comparison dynamics that the buffer half can
match against the samples are the stage dynamics DILATED and ORIENTED. This file defines that comparison family and
proves the SDE half for it:

* `orientProc flip X`: `X`, or `−X` when `flip`;
* `FrameO c r`: the round-2 `Frame` data together with a time scale `scale` (the samples' space factor is
  `(√scale)⁻¹`) and an orientation `flip l` per history; `comparisonFamilyO F`: the dynamics are `chooseDyn` with the
  PRESCRIBED driver `orientProc (flip l) (scaleProc scale v.R)` and stop `v.stop / scale`;
* `PresentsO κ β scale flip xL ρL xR ρR`: the frame word, mapped back through the frame change, presents the
  angle-`0` flow-line word of `β` (`FCDet.IsFlowType`);
* **`exists_isStopped_orient`**: stopped dynamics in the samples' frame from stopped dynamics in the stage frame
  (`GW2Sdf.exists_isStopped_scale`, `GW2Sdf.exists_isStopped_reflect`);
* **`FrameOSafeStatement D F`**, **`retainedStoppedSDEStatement_of_frameOSafe`**;
* ROOT2's actual frame: `rootScale r = (4^{r.2})⁻¹`, `flipOf l = decide (Odd l.length)`, with
  `scaleProc_rootScale` (`(√scale)⁻¹ = 2^{r.2}`) and `orientProc_flipOf` (`orientProc (flipOf l) X = (−1)^{|l|} X`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdf

open ZhanGT4.UpMark GW2JDetR11 GW2Sde GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4
  Exist.StagedLaw Restart

/-- The orientation of a process: the process itself, or its reflection when `flip`. -/
def orientProc {Ω : Type*} (flip : Bool) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  if flip then fun t ω => -X t ω else X

/-- **The frame word, mapped back through the frame change, presents the flow-line word of `β`.** -/
def PresentsO (κ : ℝ) (β : BoundaryWord) (scale : ℝ≥0) (flip : Bool) {nL nR : ℕ} (xL ρL : Fin nL → ℝ)
    (xR ρR : Fin nR → ℝ) : Prop :=
  match flip with
  | false => FCDet.IsFlowType κ 0 β (fun i => Real.sqrt scale * xL i) (fun j => Real.sqrt scale * xR j) ρL ρR
  | true => FCDet.IsFlowType κ 0 β (fun j => -(Real.sqrt scale * xR j)) (fun i => -(Real.sqrt scale * xL i)) ρR ρL

/-- **Stopped dynamics in the samples' frame** from stopped dynamics for every presentation in the stage frame. -/
theorem exists_isStopped_orient {Ω : Type u} [MeasurableSpace Ω] {ν : Measure Ω} {κ : ℝ} {β : BoundaryWord}
    {R : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞} {scale : ℝ≥0} (hc : scale ≠ 0) (flip : Bool)
    (hv : ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}, FCDet.IsFlowType κ 0 β xL xR ρL ρR →
      ∃ d : LocalDynamics Ω nL nR, d.W = R ∧ d.stop = τ ∧ d.IsStopped ν κ xL ρL xR ρR)
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} (hp : PresentsO κ β scale flip xL ρL xR ρR) :
    ∃ d : LocalDynamics Ω nL nR, d.W = orientProc flip (scaleProc scale R) ∧
      d.stop = (fun ω => τ ω / scale) ∧ d.IsStopped ν κ xL ρL xR ρR := by
  have hs : Real.sqrt scale ≠ 0 := (Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc))).ne'
  have hback : ∀ {n : ℕ} (x : Fin n → ℝ), (fun i => (Real.sqrt scale)⁻¹ * (Real.sqrt scale * x i)) = x :=
    fun x => funext fun i => by rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  cases flip with
  | false =>
    have hp' : FCDet.IsFlowType κ 0 β (fun i => Real.sqrt scale * xL i) (fun j => Real.sqrt scale * xR j) ρL ρR :=
      hp
    obtain ⟨d, hW, hst, hd⟩ := exists_isStopped_scale hc (hv hp')
    rw [hback, hback] at hd
    exact ⟨d, hW, hst, hd⟩
  | true =>
    have hp' : FCDet.IsFlowType κ 0 β (fun j => -(Real.sqrt scale * xR j)) (fun i => -(Real.sqrt scale * xL i))
        ρR ρL := hp
    obtain ⟨d, hW, hst, hd⟩ := exists_isStopped_reflect (exists_isStopped_scale hc (hv hp'))
    have e : ∀ {n : ℕ} (x : Fin n → ℝ),
        -(fun i => (Real.sqrt scale)⁻¹ * -(Real.sqrt scale * x i)) = x := fun x => funext fun i => by
      simp only [Pi.neg_apply, mul_neg, neg_neg]
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    rw [e, e] at hd
    exact ⟨d, hW, hst, hd⟩

/-! ### The oriented frame -/

/-- **The comparison frames in the samples' frame**: the round-2 frame data with a time scale and an orientation. -/
structure FrameO {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  scale : ℝ≥0
  flip : List (EntryIdx c.Θ c.Q) → Bool
  nearFamily : List (EntryIdx c.Θ c.Q) → Ω → NearCrossingFamily.{u} c.κ
  nearCandidate : List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ
  nearVar : List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ → StageVar Ω
  slowShell : List (EntryIdx c.Θ c.Q) → ℕ → Ω → SlowShell
  slowVar : List (EntryIdx c.Θ c.Q) → ℕ → StageVar Ω

/-- An oriented frame for every source setup and root. -/
abbrev FrameOFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    FrameO c r

/-- The prescribed driver of a stage variable in the samples' frame. -/
abbrev FrameO.drv {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} (F : FrameO c r)
    (l : List (EntryIdx c.Θ c.Q)) (v : StageVar Ω) : ℝ≥0 → Ω → ℝ :=
  orientProc (F.flip l) (scaleProc F.scale v.R)

/-- The prescribed stop of a stage variable in the samples' frame. -/
abbrev FrameO.stop {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} (F : FrameO c r)
    (v : StageVar Ω) : Ω → ℝ≥0∞ :=
  fun ω => v.stop ω / F.scale

/-- The near comparison data of an oriented frame. -/
def FrameO.nearData {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} (F : FrameO c r) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    GW2JDetR11.NearData Ω c.κ where
  family := F.nearFamily l ω
  candidate := F.nearCandidate l ω
  dynamics := fun n m => chooseDyn (condExpKernel c.P (c.sigma r l) ω) c.κ (F.nearFamily l ω).xL
    ((F.nearFamily l ω).ρLs m) (F.nearFamily l ω).xR ((F.nearFamily l ω).ρRs m)
    (F.drv l (F.nearVar l n m (F.nearCandidate l ω n m))) (F.stop (F.nearVar l n m (F.nearCandidate l ω n m)))

/-- The slow comparison data of an oriented frame. -/
def FrameO.slowData {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} (F : FrameO c r) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    GW2JDetR11.SlowData Ω c.κ where
  nL₀ := (F.slowShell l a ω).nL₀
  nR₀ := (F.slowShell l a ω).nR₀
  ρL₀ := (F.slowShell l a ω).ρL₀
  ρR₀ := (F.slowShell l a ω).ρR₀
  mL := (F.slowShell l a ω).mL
  mR := (F.slowShell l a ω).mR
  φ := (F.slowShell l a ω).φ
  xL := (F.slowShell l a ω).xL
  xR := (F.slowShell l a ω).xR
  start := (F.slowShell l a ω).start
  dynamics := chooseDyn (condExpKernel c.P (c.sigma r l) ω) c.κ (F.slowShell l a ω).xL
    (angleWordL c.κ (F.slowShell l a ω).φ (F.slowShell l a ω).mL (F.slowShell l a ω).ρL₀)
    (F.slowShell l a ω).xR
    (angleWordR c.κ (F.slowShell l a ω).φ (F.slowShell l a ω).mR (F.slowShell l a ω).ρR₀)
    (F.drv l (F.slowVar l a)) (F.stop (F.slowVar l a))

/-- **The comparison family of an oriented frame family.** -/
def comparisonFamilyO (F : FrameOFamily.{u}) : GW2JDetR11.ComparisonFamily.{u} :=
  fun Ω _ _ c r => ⟨(F Ω c r).nearData, (F Ω c r).slowData⟩

/-- **The per-stage safe laws consumed by the SDE half in the samples' frame** (`FrameSafeStatement` with the frame
words presented through the frame change, `PresentsO`). -/
structure FrameOSafeStatement (D : ConstructionFamily.{u}) (F : FrameOFamily.{u}) : Prop where
  scale_ne : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q), (F Ω c r).scale ≠ 0
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((F Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).nearVar l n m a).record
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
  slowSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((F Ω c r).slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).slowVar l a).IsSafe c.κ c.P ((F Ω c r).slowVar l a).record
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

/-- **JOINTDET's `RetainedStoppedSDEStatement` for the dilated and oriented comparisons** of an oriented frame family
(Theorems 1.2–1.3, R48). -/
theorem retainedStoppedSDEStatement_of_frameOSafe (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (F : FrameOFamily.{u}) (hF : FrameOSafeStatement D F) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamilyO F) := by
  refine ⟨fun Ω _ _ c r l => ?_, fun Ω _ _ c r k l hl a => ?_⟩
  · obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
    have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
    have hall : ∀ᵐ ω ∂c.P, ∀ n m a : ℕ,
        (((F Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
          ((F Ω c r).nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).nearVar l n m a).record) →
        ((F Ω c r).nearVar l n m a).record ω ∈ ((F Ω c r).nearVar l n m a).E →
        ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
          FCDet.IsFlowType c.κ 0 (((F Ω c r).nearVar l n m a).β (((F Ω c r).nearVar l n m a).record ω))
            xL xR ρL ρR →
          ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = ((F Ω c r).nearVar l n m a).R ∧
            d.stop = ((F Ω c r).nearVar l n m a).stop ∧
            d.IsStopped (condExpKernel c.P (c.sigma r l) ω) c.κ xL ρL xR ρR := by
      refine ae_all_iff.2 fun n => ae_all_iff.2 fun m => ae_all_iff.2 fun a => ?_
      by_cases hs : ((F Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
          ((F Ω c r).nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).nearVar l n m a).record
      · filter_upwards [StageVar.ae_exists_isStopped_of_generates c.h12p h13 c.hκ hFd h𝒢 hs.1 hs.2]
          with ω hω _ hE nL nR xL ρL xR ρR hw
        exact hω hE hw
      · exact Eventually.of_forall fun ω h => absurd h hs
    filter_upwards [hall, hF.nearWord Ω c r l] with ω hω hw halive n
    filter_upwards [hF.nearSafe Ω c r l n, hw halive n] with m hs hm
    exact isStopped_chooseDyn (exists_isStopped_orient (hF.scale_ne Ω c r) _
      (fun hft => hω n m _ (hs _) hm.1 hft) hm.2)
  · obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
    have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
    have hs := hF.slowSafe Ω c r k l hl a
    filter_upwards [StageVar.ae_exists_isStopped_of_generates c.h12p h13 c.hκ hFd h𝒢 hs.1 hs.2,
      hF.slowWord Ω c r k l hl a] with ω hω hw halive
    obtain ⟨hE, hpr⟩ := hw halive
    exact isStopped_chooseDyn (exists_isStopped_orient (hF.scale_ne Ω c r) _ (fun hft => hω hE hft) hpr)

/-! ### ROOT2's actual frame -/

/-- The time scale of ROOT2's samples at a scaled root: `(4^{r.2})⁻¹` (space factor `2^{r.2}`). -/
def rootScale (k : ℕ) : ℝ≥0 := ((4 : ℝ≥0) ^ k)⁻¹

/-- The orientation of ROOT2's samples after a history: reflected for odd histories. -/
def flipOf (n : ℕ) : Bool := decide (Odd n)

theorem rootScale_ne_zero (k : ℕ) : rootScale k ≠ 0 :=
  inv_ne_zero (pow_ne_zero k (by norm_num))

theorem sqrt_rootScale_inv (k : ℕ) : (Real.sqrt (rootScale k))⁻¹ = (2 : ℝ) ^ k := by
  have h : ((rootScale k : ℝ≥0) : ℝ) = ((2 : ℝ) ^ k)⁻¹ ^ 2 := by
    simp only [rootScale, NNReal.coe_inv, NNReal.coe_pow]
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h, Real.sqrt_sq (by positivity), inv_inv]

/-- **ROOT2's dilation**: `scaleProc (rootScale k) X t = 2^k · X(t / 4^k)`. -/
theorem scaleProc_rootScale {Ω : Type*} (k : ℕ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    scaleProc (rootScale k) X t ω = (2 : ℝ) ^ k * X (t / (4 : ℝ≥0) ^ k) ω := by
  simp only [scaleProc]
  rw [sqrt_rootScale_inv]
  simp only [rootScale, div_eq_inv_mul]

/-- **ROOT2's orientation**: `orientProc (flipOf n) X = (−1)^n X`. -/
theorem orientProc_flipOf {Ω : Type*} (n : ℕ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    orientProc (flipOf n) X t ω = (-1 : ℝ) ^ n * X t ω := by
  rcases Nat.even_or_odd n with h | h
  · have hf : flipOf n = false := by
      simp only [flipOf, decide_eq_false_iff_not, Nat.not_odd_iff_even]
      exact h
    simp only [orientProc, hf, Bool.false_eq_true, ↓reduceIte, h.neg_one_pow, one_mul]
  · have hf : flipOf n = true := by
      simp only [flipOf, decide_eq_true_eq]
      exact h
    simp only [orientProc, hf, ↓reduceIte, h.neg_one_pow, neg_one_mul]

end InteractingSLE.Theorem14.GW2Sdf
