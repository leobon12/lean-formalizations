/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T14Asm7
import InteractingSLE.Spec.Supplement.GW2SdoShape
import InteractingSLE.Spec.Supplement.GW2TqInst
import InteractingSLE.Spec.Supplement.GW2TmZero
import InteractingSLE.Spec.Supplement.GW2TlDeath

/-!
# Theorem 1.4's current top: any gap family, RELDET's instance inputs, the pinned near selection

Packet PROVE-T14-ASSEMBLE7 (round 2, decision D36: ASSEMBLE7 keeps the top current). Successors of
`Wire.theorem14Statement_assembled7` (round 1, landed):

* the gap family is a parameter with its measurability `hgap` and positivity `hpos` (round 1 fixed round 16's
  `GW2Sdq.gapFam`; SDE's round 17 replaces it);
* the instance inputs come from RELDET's `GW2Rd.instInputsX_of_linesX_mean` (715ea21e6): `condGFF` is RELDET's, and
  round 1's `hmean : OpenLinesMeanX` is replaced by STAGEMEAN's `mean` field `hmeanF`, the threshold field `hno`
  (PROVE-GW2-NOTHR) and the base family's height bound `hbd`;
* the package `V` keeps round 1's same-slots form (`hs`; SDE's selection changes under D37); for SDE's current
  `withNearS` selection `T14Cur.pkgS` the slots agree by `rfl` (`sameSlots_withNearS`);
* **`T14Cur.baseWm cw`**: the base family of GEOM2's root-`x` word map (`GW2Wm.wmChoiceX` at the history program, the
  candidate's angle, record event off RELDET's `launchBadRec`, decision D26 (A′)) for a counterflow word `cw`; for it
  `hword`, `hE₀`, `hbd` are PROVED (`hword_baseWm`, `hE₀_baseWm`, `hbd_baseWm`);
* **`Wire.theorem14Statement_assembled7G`** (any base family) and **`Wire.theorem14Statement_assembled7Wm`** (the base
  family `baseWm cw`).

All results are conditional helpers; no frozen declaration changes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14Cur

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24

/-- **The near base-word reader** of SDE's pinned selection (`GW2Sdx.VPkgXFamily.withNearS`). -/
abbrev NearBase : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → Ω → Restart.BoundaryWord

/-- **The candidate selector** of SDE's pinned selection. -/
abbrev NearSel : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
    List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ

/-- **The choice family with RELDET's `u₀` and marks** put into a base family (`GW2Rd.schedChoiceLinesX`). -/
abbrev chL (base : GW2Sdh.SchedChoiceFamily.{u}) : GW2Sdh.SchedChoiceFamily.{u} :=
  GW2Rd.schedChoiceLinesX T14Asm7.h12 T14Asm7.h13 base

/-- **The package at buffer index `k` with SDE's pinned near selection.** -/
abbrev pkgS (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u}) (Kb : ℕ → GW2Sde.PkgFamily.{u})
    (nb : NearBase.{u}) (kSel : NearSel.{u}) (k : ℕ) : GW2Sdx.VPkgXFamily.{u} :=
  GW2Sdx.VPkgXFamily.withNearS (GW2Rv.pkgX T14Asm7.h13 ver (chL base) (Kb k)) GW2Sdh.nearLam nb kSel

/-- **J32's alive event on the scaled cover with gap family `gap`** at a history. -/
abbrev aliveS (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : Set Ω :=
  ((GW2Sdz.J32S.{u} gap Ω c).experiment r).data.alive ((GW2Sdz.J32S.{u} gap Ω c).G r) l

/-- **SDE's pinned near selection keeps the package's slots.** -/
theorem sameSlots_withNearS (V : GW2Sdx.VPkgXFamily.{u}) (lam : GW2Sdh.NearDil.{u}) (nb : NearBase.{u})
    (kSel : NearSel.{u}) : GW2Rv.SameSlots V (GW2Sdx.VPkgXFamily.withNearS V lam nb kSel) :=
  fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-! ### The base family of GEOM2's word map -/

/-- **A counterflow word for every source setup and root** (the word `c'` of GEOM2's `GW2Wm.rootWordX`). -/
abbrev CfWord : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω), ScaledRootIdx c.Θ c.Q →
    Restart.BoundaryWord

/-- **The base family of GEOM2's root-`x` word map**: at a history `l` and candidate `a`, `GW2Wm.wmChoiceX` with the
history program, the candidate's angle and the record event off RELDET's zero-lifetime records (D26 (A′)); `u₀` and
the marks are placeholders that `chL` replaces on time-ordered histories. -/
def baseWm (cw : CfWord.{u}) : GW2Sdh.SchedChoiceFamily.{u} := fun Ω _ _ c r l a =>
  GW2Wm.wmChoiceX c.κ (cw Ω c r) (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
    (GW2Rd.length_historyProgram c r l) (GW2Rd.candAngle c r l a) (GW2Rd.launchBadRec c r l a)ᶜ (fun _ => 0)
    (fun _ => ⊥)

/-- **`hword` for `baseWm`** (GEOM2's `wmChoiceX_targets`). -/
theorem hword_baseWm (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (_ : GW2Sdx.HistOrdered c r l)
    (_ : GW2Rv.GoodRoot c r) (a : ℕ) :
    Measurable (baseWm cw Ω c r l a).β ∧
      (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((baseWm cw Ω c r l a).β y)).Countable ∧
      ∀ y, ((baseWm cw Ω c r l a).β y).IsSorted :=
  GW2Wm.wmChoiceX_targets _ _ _ _ _ _ _ _ _ _ _

/-- **`hE₀` for `baseWm`** (RELDET's `measurableSet_launchBadRec`). -/
theorem hE₀_baseWm (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (_ : GW2Sdx.HistOrdered c r l)
    (_ : GW2Rv.GoodRoot c r) (a : ℕ) : MeasurableSet (baseWm cw Ω c r l a).E₀ :=
  (GW2Rd.measurableSet_launchBadRec c r l a).compl

/-- **`hbd` for `baseWm`** (RELDET's `exists_bound_wmChoiceX`). -/
theorem hbd_baseWm (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (_ : GW2Sdx.HistOrdered c r l)
    (_ : GW2Rv.GoodRoot c r) (a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Exist.StagedLaw.RecData) (z : ℝ), |((baseWm cw Ω c r l a).β y).fn z| ≤ M :=
  GW2Rd.exists_bound_wmChoiceX _ _ _ _ _ _ _ _ _ _ _

/-! ### GW2's root tests from the owners' fields -/

/-- **GW2's root tests for J32 with a drift family, any gap family, from ROOTX's instance inputs and the owners'
near and slow fields** (any package `V` with the slots of ROOTX's package, e.g. `pkgS`). -/
theorem gw2RootTestStatement_inst (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    {ver : GW2Rv.SchedVerXFamily.{u}} {base : GW2Sdh.SchedChoiceFamily.{u}}
    (hI : GW2Rv.InstInputsX T14Asm7.h13 ver (chL base))
    {Kb : ℕ → GW2Sde.PkgFamily.{u}} {V : ℕ → GW2Sdx.VPkgXFamily.{u}}
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL base) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL base) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS gap Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    GW2RootTestStatement.{u} :=
  have hV := T14Asm7.vPairInputsXCSD_of_sameSlots (gap := gap) (C := C) hs hI hnear hwords hnearImg hshell
  have h := GW2Rt.retainedComparisonsLossyXCSD_vpkg
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ T14Asm7.h13 _
    GW2Sdh.nearLam gap C hV
  GW2Sdy.gw2RootTestStatement_of_scaledCover_A_lossyS T14Asm7.h13 T14Asm7.h13₀
    (GW2Rt.withDrift RootJ32.constructionFamily C) gap hgap hpos
    (GW2Rt.rootGeometryAStatement_withDrift (RootJ32.rootGeometryAStatement_withScaledCover T14Asm7.h13 gap) C)
    h.1 h.2

/-- **The root-`x` instance of version `n`** with the choice family `chL base`. -/
abbrev instC (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u}) (Ω : Type u) [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ)
    (h : GW2Rv.GoodRoot c r) :=
  GW2Rv.instX T14Asm7.h13 ver (chL base) Ω c r l a n h.1

/-- **GW2's root tests from the owners' fields** (RELDET's `GW2Rd.instInputsX_of_linesX_mean`: the base family's word
map, record event and height bound, STAGEMEAN's `mean`, the threshold field; then `gw2RootTestStatement_inst`). -/
theorem gw2RootTestStatement_fields (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hbd : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Exist.StagedLaw.RecData) (z : ℝ), |((base Ω c r l a).β y).fn z| ≤ M)
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver base Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver base Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver base Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver base Ω c r l a n h) c r l (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL base) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL base) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS gap Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_inst gap hgap hpos (GW2Rd.instInputsX_of_linesX_mean hword hE₀ hbd hmeanF hno) hs hnear
    hwords hnearImg C hshell

end InteractingSLE.Wire.T14Cur

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur

/-- **Theorem 1.4, current top for any gap family and any base choice family** (round 1's
`theorem14Statement_assembled7` with the gap family a parameter, RELDET's instance inputs from the mean and the
threshold). -/
theorem theorem14Statement_assembled7G (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hbd : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Exist.StagedLaw.RecData) (z : ℝ), |((base Ω c r l a).β y).fn z| ≤ M)
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver base Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver base Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver base Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver base Ω c r l a n h) c r l (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL base) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL base) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS gap Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  T14Asm7.theorem14Statement_of_rootTests
    (gw2RootTestStatement_fields gap hgap hpos ver base hword hE₀ hbd hmeanF hno Kb V hs hnear hwords hnearImg C
      hshell)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_liftEx T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hTL)

/-- **Theorem 1.4, current top with GEOM2's word-map base family `T14Cur.baseWm cw`**: the base family's word map,
record event and height bound are PROVED (`hword_baseWm`, `hE₀_baseWm`, `hbd_baseWm`); the counterflow word `cw` is
data. -/
theorem theorem14Statement_assembled7Wm (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm cw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm cw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS gap Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_assembled7G gap hgap hpos ver (baseWm cw) (hword_baseWm cw) (hE₀_baseWm cw) (hbd_baseWm cw)
    hmeanF hno Kb V hs hnear hwords hnearImg C hshell hTL

end InteractingSLE.Wire
