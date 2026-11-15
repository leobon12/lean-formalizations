/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeStage
import InteractingSLE.Spec.Supplement.GW2JDetR11Facts
import InteractingSLE.Spec.Supplement.GW2RdStgEnc
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Supplement.GW2SkRec

/-!
# GW2's retained stopped SDE for a construction, from the per-stage safe laws

Packet PROVE-GW2-SDE. JOINTDET's R11 pair (`GW2JDetR11.RetainedStoppedSDEStatement D C` and
`GW2JDetR11.RetainedBufferStatement D C`) must be proved for ONE shared comparison family `C`. This file fixes how `C`
is built, so that the two halves can be proved separately:

* `Frame c r` (shared data): the near families and candidates, the slow data shells (`SlowShell`: `SlowData` without
  its dynamics), and the stage variables (`StageVar`, each with its own stage record) of the physical future pieces
  they read — the stage variable of the near comparison `(n, m)` reading candidate `a` after history `l` is
  `nearVar l n m a`, that of the slow comparison of candidate `a` is `slowVar l a`;
* `comparisonFamily F`: the comparison data whose dynamics are `chooseDyn` with the stage variable's PHYSICAL driver
  `R` and PHYSICAL stop (`chooseDyn_W`, `chooseDyn_stop`); so the buffer half is a statement about `R`, `stop` and the
  frame only, and needs nothing from the SDE half;
* `StageVar.Generates P 𝒢`: the stage record generates `𝒢` up to null sets (for ROOT2's encoded record
  `GW2Rd.stageEncRec c r l` exactly: `stageEncRec_record_le`, `stageEncRec_sigma_le`; for RELDET's augmented record
  `augRec x y`: `generates_augRec`); `StageVar.ae_exists_isStopped_of_generates`: the stopped SDE then holds under
  the kernel of `𝒢` itself;
* **`FrameSafeStatement D F`** (the named per-stage input of the SDE half): every stage variable's record generates
  the retained σ-algebra `c.sigma r l` up to null sets and the variable is safe for its record (`StageVar.IsSafe`:
  K2's safe law and the engine's conditions) — eventually in `m` for the near comparisons — and, almost surely on the
  alive history, the record lies in the stage's good event and the frame's word is a presentation of the angle-`0`
  flow-line word of the stage word (`FCDet.IsFlowType`);
* **`retainedStoppedSDEStatement_of_frameSafe`**: `RetainedStoppedSDEStatement D (comparisonFamily F)`, for every
  construction `D` (in particular `RootJ31.constructionFamily`), from `FrameSafeStatement D F` and Theorems 1.2–1.3.

The kernel identification: σ-algebras equal up to null sets have almost surely equal regular conditional kernels
(`KernelTower.ae_condExpKernel_eq_of_le_aeSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6 GW2TipSystem.RootN4 Exist.StagedLaw Restart

/-- The data shell of a slow comparison: `GW2JDetR11.SlowData` without its dynamics. -/
structure SlowShell where
  nL₀ : ℕ
  nR₀ : ℕ
  ρL₀ : Fin nL₀ → ℝ
  ρR₀ : Fin nR₀ → ℝ
  mL : ℕ
  mR : ℕ
  φ : ℕ → ℝ
  xL : Fin (mL + nL₀) → ℝ
  xR : Fin (mR + nR₀ + 1) → ℝ
  start : ℝ

/-- **The comparison frames of one source and root**, shared by the SDE half and the buffer half of R11's pair. -/
structure Frame {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) where
  nearFamily : List (EntryIdx c.Θ c.Q) → Ω → NearCrossingFamily.{u} c.κ
  nearCandidate : List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ
  nearVar : List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ → StageVar Ω
  slowShell : List (EntryIdx c.Θ c.Q) → ℕ → Ω → SlowShell
  slowVar : List (EntryIdx c.Θ c.Q) → ℕ → StageVar Ω

/-- A frame for every source setup and root. -/
abbrev FrameFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    Frame c r

/-- The near comparison data of a frame at a history and a sample. -/
def Frame.nearData {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} (F : Frame c r) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    GW2JDetR11.NearData Ω c.κ where
  family := F.nearFamily l ω
  candidate := F.nearCandidate l ω
  dynamics := fun n m => chooseDyn (condExpKernel c.P (c.sigma r l) ω) c.κ (F.nearFamily l ω).xL
    ((F.nearFamily l ω).ρLs m) (F.nearFamily l ω).xR ((F.nearFamily l ω).ρRs m)
    (F.nearVar l n m (F.nearCandidate l ω n m)).R (F.nearVar l n m (F.nearCandidate l ω n m)).stop

/-- The slow comparison data of a frame at a history, a candidate and a sample. -/
def Frame.slowData {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} (F : Frame c r) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
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
    (F.slowVar l a).R (F.slowVar l a).stop

/-- **The comparison family of a frame family**: the dynamics carry the physical drivers and stops. -/
def comparisonFamily (F : FrameFamily.{u}) : GW2JDetR11.ComparisonFamily.{u} :=
  fun Ω _ _ c r => ⟨(F Ω c r).nearData, (F Ω c r).slowData⟩

/-- **The record of a stage variable generates `𝒢` up to `P`-null sets.** -/
def StageVar.Generates {Ω : Type u} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Ω] (v : StageVar Ω) (P : Measure Ω) :
    Prop :=
  Measurable v.record ∧ MeasurableSpace.comap v.record inferInstance ≤ LocalSets.aeSigma 𝒢 P ∧
    𝒢 ≤ LocalSets.aeSigma (MeasurableSpace.comap v.record inferInstance) P

/-- **The stopped SDE of a safe stage variable under the kernel of a σ-algebra its record generates** (up to null
sets): kernels of null-equivalent σ-algebras agree almost surely. -/
theorem StageVar.ae_exists_isStopped_of_generates (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {Fd : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode κ 0 Fd) {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {v : StageVar Ω}
    (hg : v.Generates (𝒢 := 𝒢) P) (hv : v.IsSafe κ P v.record) :
    ∀ᵐ ω₀ ∂P, v.record ω₀ ∈ v.E → ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
      FCDet.IsFlowType κ 0 (v.β (v.record ω₀)) xL xR ρL ρR →
      ∃ d : GW2JDetR11.LocalDynamics Ω nL nR, d.W = v.R ∧ d.stop = v.stop ∧
        d.IsStopped (condExpKernel P 𝒢 ω₀) κ xL ρL xR ρR := by
  have hker := KernelTower.ae_condExpKernel_eq_of_le_aeSigma (P := P) hg.1.comap_le h𝒢 hg.2.1 hg.2.2
  filter_upwards [hv.ae_exists_isStopped h12p h13 hκ hFd hg.1, hker] with ω hω hk hE nL nR xL ρL xR ρR hw
  rw [← hk]
  exact hω hE hw

/-- **The per-stage safe laws consumed by the SDE half** (named input; supplied by the stage chain): every stage
variable's record generates `c.sigma r l` up to null sets and the variable is safe for its record (eventually in `m`
for the near comparisons), and almost surely on the alive history the record is in the stage's good event and the
frame's word presents the stage's flow-line word. -/
structure FrameSafeStatement (D : ConstructionFamily.{u}) (F : FrameFamily.{u}) : Prop where
  nearSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((F Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).nearVar l n m a).record
  nearWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop,
      ((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).record ω ∈
        ((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).E ∧
      FCDet.IsFlowType c.κ 0
        (((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).β
          (((F Ω c r).nearVar l n m ((F Ω c r).nearCandidate l ω n m)).record ω))
        ((F Ω c r).nearFamily l ω).xL ((F Ω c r).nearFamily l ω).xR (((F Ω c r).nearFamily l ω).ρLs m)
        (((F Ω c r).nearFamily l ω).ρRs m)
  slowSafe : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((F Ω c r).slowVar l a).Generates (𝒢 := c.sigma r l) c.P ∧
        ((F Ω c r).slowVar l a).IsSafe c.κ c.P ((F Ω c r).slowVar l a).record
  slowWord : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
    ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
      ((F Ω c r).slowVar l a).record ω ∈ ((F Ω c r).slowVar l a).E ∧
      FCDet.IsFlowType c.κ 0 (((F Ω c r).slowVar l a).β (((F Ω c r).slowVar l a).record ω))
        ((F Ω c r).slowShell l a ω).xL ((F Ω c r).slowShell l a ω).xR
        (angleWordL c.κ ((F Ω c r).slowShell l a ω).φ ((F Ω c r).slowShell l a ω).mL
          ((F Ω c r).slowShell l a ω).ρL₀)
        (angleWordR c.κ ((F Ω c r).slowShell l a ω).φ ((F Ω c r).slowShell l a ω).mR
          ((F Ω c r).slowShell l a ω).ρR₀)

/-- ROOT2's encoded stage record is measurable. -/
theorem measurable_stageEncRec {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Measurable (GW2Rd.stageEncRec c r l) :=
  (GW2Rd.measurable_stageEncRec_sigma c r l).mono (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _) le_rfl

/-- ROOT2's encoded stage record generates `c.sigma r l` (first inclusion up to null sets). -/
theorem stageEncRec_record_le {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSpace.comap (GW2Rd.stageEncRec c r l) inferInstance ≤ LocalSets.aeSigma (c.sigma r l) c.P :=
  (GW2Rd.comap_stageEncRec_sigma c r l).le.trans (LocalSets.le_aeSigma _ _)

/-- ROOT2's encoded stage record generates `c.sigma r l` (second inclusion up to null sets). -/
theorem stageEncRec_sigma_le {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    c.sigma r l ≤ LocalSets.aeSigma (MeasurableSpace.comap (GW2Rd.stageEncRec c r l) inferInstance) c.P :=
  (GW2Rd.comap_stageEncRec_sigma c r l).ge.trans (LocalSets.le_aeSigma _ _)

/-- The augmented record generates the join of its two parts. -/
theorem comap_augRec {Ω : Type*} (x y : Ω → RecData) :
    MeasurableSpace.comap (GW2Rd.augRec x y) inferInstance =
      MeasurableSpace.comap x inferInstance ⊔ MeasurableSpace.comap y inferInstance := by
  change MeasurableSpace.comap (GW2Rd.pairEnc ∘ fun ω => (x ω, y ω)) inferInstance = _
  rw [← MeasurableSpace.comap_comp, GW2Rd.pairEnc.measurableEmbedding.comap_eq]
  exact MeasurableSpace.comap_prodMk x y

/-- **An augmented stage record generates `𝒢`** when its first part generates `𝒢` exactly (e.g. ROOT2's encoded
record and `c.sigma r l`) and its second part is `𝒢`-measurable up to null sets. -/
theorem generates_augRec {Ω : Type u} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω} {v : StageVar Ω}
    {x y : Ω → RecData} (hv : v.record = GW2Rd.augRec x y) (hx : Measurable x) (hy : Measurable y)
    (hx𝒢 : MeasurableSpace.comap x inferInstance = 𝒢)
    (hy𝒢 : MeasurableSpace.comap y inferInstance ≤ LocalSets.aeSigma 𝒢 P) : v.Generates (𝒢 := 𝒢) P := by
  rw [StageVar.Generates, hv, comap_augRec]
  have h1 : 𝒢 ≤ MeasurableSpace.comap x inferInstance ⊔ MeasurableSpace.comap y inferInstance :=
    (le_of_eq hx𝒢.symm).trans le_sup_left
  exact ⟨GW2Rd.measurable_augRec hx hy, sup_le (hx𝒢.le.trans (LocalSets.le_aeSigma _ _)) hy𝒢,
    h1.trans (LocalSets.le_aeSigma _ _)⟩

/-- **JOINTDET's `RetainedStoppedSDEStatement` for any construction, from the per-stage safe laws** of a frame family
(Theorems 1.2–1.3 at universes `0` and `u` are used, R48: Theorem 1.4 work). -/
theorem retainedStoppedSDEStatement_of_frameSafe (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (F : FrameFamily.{u}) (hF : FrameSafeStatement D F) :
    GW2JDetR11.RetainedStoppedSDEStatement D (comparisonFamily F) := by
  refine ⟨fun Ω _ _ c r l => ?_, fun Ω _ _ c r k l hl a => ?_⟩
  · obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
    have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
    have hall : ∀ᵐ ω ∂c.P, ∀ n m a : ℕ,
        (((F Ω c r).nearVar l n m a).Generates (𝒢 := c.sigma r l) c.P ∧
          ((F Ω c r).nearVar l n m a).IsSafe c.κ c.P ((F Ω c r).nearVar l n m a).record) →
        ((F Ω c r).nearVar l n m a).record ω ∈ ((F Ω c r).nearVar l n m a).E →
        ∀ {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ},
          FCDet.IsFlowType c.κ 0 (((F Ω c r).nearVar l n m a).β (((F Ω c r).nearVar l n m a).record ω)) xL xR ρL ρR →
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
    exact isStopped_chooseDyn (hω n m _ (hs _) hm.1 hm.2)
  · obtain ⟨Fd, hFd⟩ := canonicalDriverCodeStatement_of_param h12p₀ h13₀ c.κ 0 c.hκ
    have h𝒢 : c.sigma r l ≤ _ := stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
    have hs := hF.slowSafe Ω c r k l hl a
    filter_upwards [StageVar.ae_exists_isStopped_of_generates c.h12p h13 c.hκ hFd h𝒢 hs.1 hs.2,
      hF.slowWord Ω c r k l hl a] with ω hω hw halive
    obtain ⟨hE, hft⟩ := hw halive
    exact isStopped_chooseDyn (hω hE hft)

end InteractingSLE.Theorem14.GW2Sde
