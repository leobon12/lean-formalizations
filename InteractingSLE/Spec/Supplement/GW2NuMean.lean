/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NtWire

/-!
# GW2's `noThreshold` in the form of the `hmean` binder of `Wire.theorem14Statement_assembled7` (decision D36)

Packet PROVE-GW2-NOTHR (round 3). `Wire.theorem14Statement_assembled7` takes STAGEMEAN's part of the open lines as the
binder `hmean : ∀ …, GW2Rd.OpenLinesMeanX (GW2Rv.instX h13 ver (GW2Rd.schedChoiceLinesX h12 h13 base) …)`. Its field
`noThreshold` is the threshold clause. Route (M) gives it from D38's export (`GW2Nt.ExportFamily`):

* **`hmean_noThreshold_of_export`**: the clause `noThreshold` of `hmean`, for every root-`x` instance of the top;
* **`hmean_of_export`**: `hmean` from its two other fields (`mean`, `condGFF`) and the export.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nu

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sdh GW2Nt

/-- **The clause `noThreshold` of the `hmean` binder of `Wire.theorem14Statement_assembled7`** (every good root,
time-ordered history, candidate and version) from D38's export. -/
theorem hmean_noThreshold_of_export {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hexp : ExportFamily ver base) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a n : ℕ,
        NoThresholdX (instX Wire.T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base)
          Ω c r l a n h.1) c r l (rootPt r.1) :=
  hno_of_export hword hE₀ hexp

/-- **The `hmean` binder of `Wire.theorem14Statement_assembled7` from its fields `mean` and `condGFF` and D38's
export** (the field `noThreshold`). -/
theorem hmean_of_export {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hexp : ExportFamily ver base)
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l →
      (h : GoodRoot c r) → ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0)
        (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instX Wire.T14Asm7.h13 ver
          (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).B t)
          (WholeField.centredField c.h (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          stageMeanAtX (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1) c r l (rootPt r.1)
            w t ψ ω (g ω))
    (hcond : ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l →
      (h : GoodRoot c r) → ∀ a n : ℕ,
        ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : ℝ),
          Measurable[𝒢.1] ((instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
              (rootPt r.1)) ∧ 0 ≤ M ∧
          (∀ y ∈ (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).E,
            ∀ x ∉ ((instX Wire.T14Asm7.h13 ver
              (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).β y).jumps,
              |((instX Wire.T14Asm7.h13 ver
                (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).β y).fn x| ≤ M) ∧
          ∀ᵐ ω₀ ∂c.P, (instX Wire.T14Asm7.h13 ver
            (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
              (rootPt r.1) ω₀ ∈ (instX Wire.T14Asm7.h13 ver
                (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).E →
            IsGFFWithBoundaryData (condExpKernel c.P 𝒢.1 ω₀) (instX Wire.T14Asm7.h13 ver
              (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).Hr
              ((instX Wire.T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base)
                Ω c r l a n h.1).β ((instX Wire.T14Asm7.h13 ver
                  (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
                    (rootPt r.1) ω₀)).fn
              ((instX Wire.T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base)
                Ω c r l a n h.1).β ((instX Wire.T14Asm7.h13 ver
                  (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1).srecX c r l
                    (rootPt r.1) ω₀)).jumps) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a n : ℕ,
        GW2Rd.OpenLinesMeanX (instX Wire.T14Asm7.h13 ver
          (GW2Rd.schedChoiceLinesX Wire.T14Asm7.h12 Wire.T14Asm7.h13 base) Ω c r l a n h.1) c r l (rootPt r.1) :=
  fun Ω _ _ c r l hTO h a n =>
    ⟨hmeanF Ω c r l hTO h a n, hmean_noThreshold_of_export hword hE₀ hexp Ω c r l hTO h a n,
      hcond Ω c r l hTO h a n⟩

end InteractingSLE.Theorem14.GW2Nu
