/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdgNear
import InteractingSLE.Spec.Supplement.GW2JDetR11Assembly

/-!
# GW2's R11 pair for ROOT2's construction: the complete list of named inputs

Packet PROVE-GW2-SDE (round 4). JOINTDET's `retainedComparisons_of_stoppedSDE_buffer` turns the R11 pair
(`RetainedStoppedSDEStatement D C`, `RetainedBufferStatement D C`, for the SAME comparison family `C`) into both C24
binders. This file applies it to ROOT2's construction `RootJ31.constructionFamily` and the comparison family
`comparisonFamilyO K.rootFrame.frame` of rounds 3–4. Everything still needed is collected in ONE structure:

* **`RootPairInputs K`**: round 2's per-stage targets (`StageInst.Good`, `StageStop.Good` for the near and slow
  stops), the frame words in ROOT2's frame (`FrameOWordStatement`), the near facts for the actual stage driver
  (`RootNearImg`), and the slow inputs on the retained gate (`RootDriverId`, `RootStartFrozen`, `RootStopCovers`,
  `RootShellChoice`);
* **`retainedPair_rootJ31`** (both R11 properties) and **`retainedComparisons_rootJ31`** (both C24 binders,
  `RetainedNearModelsStatement` and `RetainedSlowComparisonsStatement`, for ROOT2's construction).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdg

open GW2JDetR11 GW2Sde GW2Sdf GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootL6

/-- **The named inputs of the R11 pair for ROOT2's construction** with the per-stage package `K`. -/
structure RootPairInputs (K : PkgFamily.{u}) : Prop where
  inst : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), ((K Ω c r).inst l a).Good c r l
  nearStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n : ℕ), ∀ᶠ m in atTop, ∀ a : ℕ,
      ((K Ω c r).nearStop l n m a).Good ((K Ω c r).inst l a) c r l
  slowStop : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ((K Ω c r).slowStop l a).Good ((K Ω c r).inst l a) c r l
  words : FrameOWordStatement RootJ31.constructionFamily K.rootFrame.frame
  nearImg : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), RootNearImg K Ω c r l
  driverId : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootDriverId K Ω c r l a
  startFrozen : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStartFrozen Ω c r l a
  stopCovers : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootStopCovers K Ω c r l a
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      RootShellChoice K Ω c r l a

/-- **Both R11 properties for ROOT2's construction**, for the same comparison family (Theorems 1.2–1.3, R48). -/
theorem retainedPair_rootJ31 (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u})
    (hK : RootPairInputs K) :
    RetainedStoppedSDEStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame) ∧
      RetainedBufferStatement RootJ31.constructionFamily (comparisonFamilyO K.rootFrame.frame) := by
  have hsde := retainedStoppedSDEStatement_rootFrame h12p₀ h13₀ h13 hK.inst hK.nearStop hK.slowStop hK.words
  exact ⟨hsde, retainedBufferStatement_rootFrame_of_img K hsde hK.nearImg hK.driverId hK.startFrozen
    hK.stopCovers hK.shell⟩

/-- **Both C24 binders for ROOT2's construction** from the named inputs (Theorems 1.2–1.3, R48). -/
theorem retainedComparisons_rootJ31 (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (K : PkgFamily.{u})
    (hK : RootPairInputs K) :
    RetainedNearModelsStatement RootJ31.constructionFamily.{u} ∧
      RetainedSlowComparisonsStatement RootJ31.constructionFamily.{u} :=
  have h := retainedPair_rootJ31 h12p₀ h13₀ h13 K hK
  retainedComparisons_of_stoppedSDE_buffer _ _ h.1 h.2

end InteractingSLE.Theorem14.GW2Sdg
