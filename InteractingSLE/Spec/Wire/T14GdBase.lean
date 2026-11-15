/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T14NxTop
import InteractingSLE.Spec.Supplement.GW2KtTop
import InteractingSLE.Spec.Supplement.GW2RnFam

/-!
# The guarded base family: the top's instance inputs from the guarded forms alone (D54, D67, D68)

Packet PROVE-T14-ASSEMBLE7 (round 2b). D54/D67 rule that the top consumes the owners' guarded forms of `hmeanF` and
`hno`: strictly ordered histories and roots `0 ∨ lowerArcRoots` (GEOM2's `GW2Kt.HmeanFGuarded`, ROOTX's
`GW2Rn.hno_stopX`). D68 makes the top's version family NOTHR's stop family, re-indexed with BUF's `ψx`
(`GW2Kt.stopPkgVer ψx`).

**The obstruction.** The top reaches GW2's frozen interface through `GW2Rv.InstInputsX` (ROOTX's `vpkgXSafe_pkgX`
for SDE's `safe` field). `InstInputsX` asks for the instance inputs at every weakly ordered history
(`GW2Sdx.HistOrdered`, D1's guard) and every good root. At a history with a tie (two consecutive entries at the same
time) the retained gate `rootGate = coverEvent ∩ oldSuccess` can have positive probability, and the instance's
record event `E₀ ∩ succRec ∩ aliveRecX` is not null. So the guarded forms do not give `InstInputsX` for the top's
base `T14Cur.baseWm cw`.

**The bridge.** `guardBase base` is `base` on guarded histories (`Guard`) and `base` with the empty record event
elsewhere. RELDET's `schedChoiceLinesX` at `(l, a)` reads only `base Ω c r l a`, so on guarded histories the top's
instances for `guardBase base` *are* those for `base` (`instC_guardBase_of_guard`). Elsewhere the instance's record
event is empty (`instC_guardBase_E_of_not`), and `stageMeanAtX` and `NoThresholdX` hold vacuously. Main results:

* **`hmeanF_guardBase`**, **`hno_guardBase`**: the top's (weakly guarded) binders for `guardBase base` from the
  guarded forms for `base`;
* **`instInputsX_guardBase`**: `InstInputsX` for `chL (guardBase (baseWm cw))` from the guarded forms;
* **`instInputsX_stopG`**: `InstInputsX` for D68's family `GW2Kt.stopPkgVer ψx` and `chL (guardBase (baseWm cwSrc))`,
  with **no hypotheses** (GEOM2's `hmeanFGuarded_stopPkgVer`, ROOTX's `hno_stopX` with GEOM2's root-`x` base).

Whoever builds the package's fields on `guardBase` must replace the identity `E₀ = (launchBadRec)ᶜ` used at every
history (ROOTX's `hE₀eq_baseWm`, BUF's `pkgCh`) by `guardBase_E₀_of_guard` on guarded histories. The top reads
only guarded histories: `GW2Kt.guard_of_aliveS`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14Gd

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24
  Theorem14.GW2TipSystem.RootJ31 T14Cur

/-- **The guard of D54/D67**: a strictly ordered history at a root `0` or in `lowerArcRoots`. -/
def Guard {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : Prop :=
  (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) ∧
    (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps)

open Classical in
/-- **The guarded base family**: `base` on guarded histories, `base` with the empty record event elsewhere. -/
def guardBase (base : GW2Sdh.SchedChoiceFamily.{u}) : GW2Sdh.SchedChoiceFamily.{u} := fun Ω _ _ c r l a =>
  if Guard c r l then base Ω c r l a else { base Ω c r l a with E₀ := ∅ }

variable (base : GW2Sdh.SchedChoiceFamily.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} (a : ℕ)

theorem guardBase_of_guard (hg : Guard c r l) : guardBase base Ω c r l a = base Ω c r l a := by
  unfold guardBase
  simp only [hg, ↓reduceIte]

theorem guardBase_β : (guardBase base Ω c r l a).β = (base Ω c r l a).β := by
  unfold guardBase
  split_ifs <;> rfl

theorem guardBase_E₀_of_not (hg : ¬ Guard c r l) : (guardBase base Ω c r l a).E₀ = ∅ := by
  unfold guardBase
  simp only [hg, ↓reduceIte]

/-- On guarded histories the guarded base keeps the record event. -/
theorem guardBase_E₀_of_guard (hg : Guard c r l) : (guardBase base Ω c r l a).E₀ = (base Ω c r l a).E₀ := by
  rw [guardBase_of_guard base a hg]

theorem measurableSet_guardBase_E₀ (hE : MeasurableSet (base Ω c r l a).E₀) :
    MeasurableSet (guardBase base Ω c r l a).E₀ := by
  by_cases hg : Guard c r l
  · rw [guardBase_E₀_of_guard base a hg]
    exact hE
  · rw [guardBase_E₀_of_not base a hg]
    exact MeasurableSet.empty

/-- RELDET's lines choice at `(l, a)` reads only the base at `(l, a)`. -/
theorem chL_guardBase_of_guard (hg : Guard c r l) : chL (guardBase base) Ω c r l a = chL base Ω c r l a := by
  show GW2Rd.schedChoiceLinesX T14Asm7.h12 T14Asm7.h13 (guardBase base) Ω c r l a =
    GW2Rd.schedChoiceLinesX T14Asm7.h12 T14Asm7.h13 base Ω c r l a
  unfold GW2Rd.schedChoiceLinesX
  rw [guardBase_of_guard base a hg]

/-- **On guarded histories the top's instances for the guarded base are those for the base.** -/
theorem instC_guardBase_of_guard (ver : GW2Rv.SchedVerXFamily.{u}) (n : ℕ) (h : GW2Rv.GoodRoot c r)
    (hg : Guard c r l) : instC ver (guardBase base) Ω c r l a n h = instC ver base Ω c r l a n h := by
  show GW2Rv.schedInstSX c r l a (GW2Rz.schedGTX T14Asm7.h13 c r l a) ((ver Ω c r l a).isA h.1 n)
      (chL (guardBase base) Ω c r l a) =
    GW2Rv.schedInstSX c r l a (GW2Rz.schedGTX T14Asm7.h13 c r l a) ((ver Ω c r l a).isA h.1 n)
      (chL base Ω c r l a)
  rw [chL_guardBase_of_guard base a hg]

/-- **Off the guard the instances' record event is empty.** -/
theorem instC_guardBase_E_of_not (ver : GW2Rv.SchedVerXFamily.{u}) (n : ℕ) (h : GW2Rv.GoodRoot c r)
    (hg : ¬ Guard c r l) : (instC ver (guardBase base) Ω c r l a n h).E = ∅ := by
  have hE₀ : (chL (guardBase base) Ω c r l a).E₀ = ∅ := by
    rw [GW2Rd.schedChoiceLinesX_E₀ T14Asm7.h12 T14Asm7.h13 (guardBase base) c r l a]
    exact guardBase_E₀_of_not base a hg
  show (chL (guardBase base) Ω c r l a).E₀ ∩ GW2Sdi.succRec c r l ∩ _ = ∅
  rw [hE₀, Set.empty_inter, Set.empty_inter]

/-! ### The top's binders for the guarded base -/

variable {base} in
/-- **The top's `hmeanF` binder for the guarded base** (every weakly ordered history) from the guarded form for the
base (GEOM2's `GW2Kt.HmeanFGuarded`): on guarded histories the instances agree; elsewhere the live event is empty. -/
theorem hmeanF_guardBase {ver : GW2Rv.SchedVerXFamily.{u}} (hG : GW2Kt.HmeanFGuarded ver base) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (guardBase base) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (guardBase base) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (guardBase base) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω) := by
  intro Ω _ _ c r l _ h a n w t g hg ψ
  by_cases hgd : Guard c r l
  · rw [instC_guardBase_of_guard base a ver n h hgd] at hg ⊢
    exact hG Ω c r l hgd.1 h hgd.2 a n w t g hg ψ
  · refine Eventually.of_forall fun ω hω => ?_
    have hE := instC_guardBase_E_of_not base a ver n h hgd
    simp only [GW2Rd.liveEvRec, hE, Set.empty_inter, Set.preimage_empty, Set.mem_empty_iff_false] at hω

variable {base} in
/-- **The top's `hno` binder for the guarded base** from the guarded form for the base (ROOTX's `GW2Rn.hno_stopX`
form): off the guard the record event is empty. -/
theorem hno_guardBase {ver : GW2Rv.SchedVerXFamily.{u}}
    (hG : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver base Ω c r l a n h) c r l (rootPt r.1)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver (guardBase base) Ω c r l a n h) c r l (rootPt r.1) := by
  intro Ω _ _ c r l _ h a n
  by_cases hgd : Guard c r l
  · rw [instC_guardBase_of_guard base a ver n h hgd]
    exact hG Ω c r l hgd.1 h hgd.2 a n
  · refine Eventually.of_forall fun ω hω => ?_
    rw [instC_guardBase_E_of_not base a ver n h hgd] at hω
    exact absurd hω (Set.notMem_empty _)

/-- **`hword` for the guarded word-map base.** -/
theorem hword_guardBase (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hTO : GW2Sdx.HistOrdered c r l)
    (h : GW2Rv.GoodRoot c r) (a : ℕ) :
    Measurable (guardBase (baseWm cw) Ω c r l a).β ∧
      (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((guardBase (baseWm cw) Ω c r l a).β y)).Countable ∧
      ∀ y, ((guardBase (baseWm cw) Ω c r l a).β y).IsSorted := by
  rw [guardBase_β]
  exact hword_baseWm cw Ω c r l hTO h a

/-- **`hE₀` for the guarded word-map base.** -/
theorem hE₀_guardBase (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hTO : GW2Sdx.HistOrdered c r l)
    (h : GW2Rv.GoodRoot c r) (a : ℕ) : MeasurableSet (guardBase (baseWm cw) Ω c r l a).E₀ :=
  measurableSet_guardBase_E₀ (baseWm cw) a (hE₀_baseWm cw Ω c r l hTO h a)

/-- **`hbd` for the guarded word-map base.** -/
theorem hbd_guardBase (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hTO : GW2Sdx.HistOrdered c r l)
    (h : GW2Rv.GoodRoot c r) (a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (y : Exist.StagedLaw.RecData) (z : ℝ), |((guardBase (baseWm cw) Ω c r l a).β y).fn z| ≤ M := by
  rw [guardBase_β]
  exact hbd_baseWm cw Ω c r l hTO h a

/-- **The top's instance inputs for the guarded word-map base from the guarded forms** (RELDET's
`instInputsX_of_linesX_mean` with `hmeanF_guardBase`, `hno_guardBase`). -/
theorem instInputsX_guardBase {ver : GW2Rv.SchedVerXFamily.{u}} (cw : CfWord.{u})
    (hmean : GW2Kt.HmeanFGuarded ver (baseWm cw))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1)) :
    GW2Rv.InstInputsX T14Asm7.h13 ver (chL (guardBase (baseWm cw))) :=
  GW2Rd.instInputsX_of_linesX_mean (hword_guardBase cw) (hE₀_guardBase cw) (hbd_guardBase cw)
    (hmeanF_guardBase hmean) (hno_guardBase hno)

/-! ### D68's family: the stop family re-indexed with BUF's `ψx`, at BUF's word -/

/-- **The guarded `hno` for D68's family** (ROOTX's `GW2Rn.hno_stopX` at BUF's word with GEOM2's root-`x` base,
re-indexed: the re-indexed instance is the stop instance at the re-indexed version, by `rfl`). -/
theorem hno_stopPkgVer (ψx : GW2Bh.PsiFam.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
      (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC (GW2Kt.stopPkgVer ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
        (rootPt r.1) := by
  intro Ω _ _ c r l hord h hroot a n
  exact GW2Rn.hno_stopX GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc
    (fun Ω _ _ c r hg hx => GW2Kx.claimAllX_nil_rootX T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ c r
      (Or.inr hx) hg.2 (GW2Kt.isCfWordOf_cwSrc Ω c r)) Ω c r l hord h hroot a _

/-- **The top's instance inputs for D68's family on the guarded base, with no hypotheses.** -/
theorem instInputsX_stopG (ψx : GW2Bh.PsiFam.{u}) :
    GW2Rv.InstInputsX T14Asm7.h13 (GW2Kt.stopPkgVer ψx) (chL (guardBase (baseWm GW2Bh.cwSrc))) :=
  instInputsX_guardBase GW2Bh.cwSrc (GW2Kt.hmeanFGuarded_stopPkgVer ψx) (hno_stopPkgVer ψx)

end InteractingSLE.Wire.T14Gd
