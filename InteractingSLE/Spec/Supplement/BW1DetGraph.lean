/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1DetWitness

/-!
# BW1's terminal relation is a Borel relation (`TermRelGraphStatement`)

Packet PROVE-BW1-DET. The projection of the Borel witness set (`BW1DetCode.witnessSet`) that forgets the clock code
and the regularity proofs is injective (`clock_eq_of_mem_witnessSet`), so its range is Borel (Lusin–Souslin).
Reading drivers through their rational codes gives a Borel set `G` of (relative driver, counterflow, record) such
that, for regular drivers and the record of a regular piece with finite lifetime, membership in `G` is exactly
`BW1Term.IsTermRelOf` (`termRelGraphStatement`).

## Main results

* `projection_injective`, `measurableSet_graphCodes`;
* **`TermRelGraphStatement`** (named, deterministic) and its proof **`termRelGraphStatement`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.BW1Det

open Exist Exist.StagedLaw GW1Borel BW1Term

/-- Forget the regularity proofs and the clock code. -/
def projection (x : witnessSet) : (Code × Code) × RecData := ((x.1.1.1.1.1, x.1.1.1.2.1), x.1.1.2)

theorem measurable_projection : Measurable projection := by
  have h : Measurable fun x : Wsp => ((x.1.1.1.1, x.1.1.2.1), x.1.2) :=
    ((measurable_subtype_coe.comp measurable_wU).prodMk (measurable_subtype_coe.comp measurable_wV)).prodMk
      measurable_wR
  exact h.comp measurable_subtype_coe

theorem projection_injective : Function.Injective projection := by
  intro x y hxy
  have hu : x.1.1.1.1 = y.1.1.1.1 := Subtype.ext (congrArg (fun p : (Code × Code) × RecData => p.1.1) hxy)
  have hv : x.1.1.1.2 = y.1.1.1.2 := Subtype.ext (congrArg (fun p : (Code × Code) × RecData => p.1.2) hxy)
  have hr : x.1.1.2 = y.1.1.2 := congrArg (fun p : (Code × Code) × RecData => p.2) hxy
  have h1 : x.1.1 = y.1.1 := Prod.ext (Prod.ext hu hv) hr
  exact Subtype.ext (Prod.ext h1 (clock_eq_of_mem_witnessSet x.2 y.2 h1))

/-- The codes of the witnessed relation. -/
def graphCodes : Set ((Code × Code) × RecData) := range projection

theorem measurableSet_graphCodes : MeasurableSet graphCodes := by
  let : StandardBorelSpace witnessSet := measurableSet_witnessSet.standardBorel
  have : MeasurableSpace.CountablyGenerated ((Code × Code) × RecData) := inferInstance
  have : MeasurableSpace.SeparatesPoints ((Code × Code) × RecData) := inferInstance
  have : MeasurableSpace.CountablySeparated ((Code × Code) × RecData) :=
    MeasurableSpace.countablySeparated_of_separatesPoints
  exact (measurable_projection.measurableEmbedding projection_injective).measurableSet_range

/-- The rational code of a path. -/
def pathCode (W : ℝ≥0 → ℝ) : Code := fun q : ℚ≥0 => W q

theorem measurable_pathCode : Measurable pathCode :=
  measurable_pi_iff.2 fun q => measurable_pi_apply (q : ℝ≥0)

theorem driver_pathCode {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) : driver (pathCode W) = W :=
  GW1Det.regQ_restrict hW hW0

/-- **The relation graph on paths.** -/
def relGraph : Set (((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × RecData) :=
  {p | ((pathCode p.1.1, pathCode p.1.2), p.2) ∈ graphCodes}

theorem measurableSet_relGraph : MeasurableSet relGraph :=
  measurableSet_graphCodes.preimage
    (((measurable_pathCode.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_pathCode.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)

theorem mem_relGraph_iff {U V : ℝ≥0 → ℝ} (hU : GW1Path.IsRegCf U) (hV : GW1Path.IsRegCf V)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : GW1P.PieceRegular D.1 (min ⊤ D.2)) (hfin : D.2 ≠ ⊤) :
    ((U, V), recOf ⊤ D) ∈ relGraph ↔ IsTermRelOf U V D := by
  have eU := driver_pathCode hU.1 hU.2.1
  have eV := driver_pathCode hV.1 hV.2.1
  have hUc : pathCode U ∈ regularCodes := by
    show GW1Path.IsRegCf (driver (pathCode U))
    rw [eU]
    exact hU
  have hVc : pathCode V ∈ regularCodes := by
    show GW1Path.IsRegCf (driver (pathCode V))
    rw [eV]
    exact hV
  constructor
  · rintro ⟨⟨⟨⟨⟨u, v⟩, r⟩, c⟩, hx⟩, he⟩
    simp only [projection, Prod.mk.injEq] at he
    obtain ⟨⟨hu, hv⟩, hr⟩ := he
    have hu' : u = ⟨pathCode U, hUc⟩ := Subtype.ext hu
    have hv' : v = ⟨pathCode V, hVc⟩ := Subtype.ext hv
    subst hu' hv' hr
    obtain ⟨-, hpre⟩ := (mem_witnessSet_iff _ _ hD hfin c).1 hx
    rw [eU, eV] at hpre
    exact ⟨clock c, hpre⟩
  · rintro ⟨ℓ, hℓ⟩
    have h0 := GW1Det.clock_zero_of_range hℓ.2.1 hℓ.2.2.1
    have hcl : clock (fun q : ℚ≥0 => (ℓ q : ℝ)) = ℓ := clock_restrict hℓ.1 h0
    have hpre : GW1LaunchClock.IsPrefixClock (termChart D) (driver (⟨pathCode V, hVc⟩ : RegularCode).1)
        (driver (⟨pathCode U, hUc⟩ : RegularCode).1) (termSet D) (clock (fun q : ℚ≥0 => (ℓ q : ℝ))) := by
      rw [hcl]
      change GW1LaunchClock.IsPrefixClock (termChart D) (driver (pathCode V)) (driver (pathCode U)) (termSet D) ℓ
      rw [eU, eV]
      exact hℓ
    have hx := (mem_witnessSet_iff ⟨pathCode U, hUc⟩ ⟨pathCode V, hVc⟩ hD hfin _).2
      ⟨fun q => by rw [hcl], hpre⟩
    exact ⟨⟨_, hx⟩, rfl⟩

/-- **Named deterministic statement: BW1's terminal relation is Borel.** There is a measurable set `G` of
(relative driver, counterflow driver, record of the piece) such that, for regular drivers `U`, `V`
(`GW1Path.IsRegCf`) and a regular piece `D` with finite lifetime, `((U, V), recOf ⊤ D) ∈ G` iff `U` is the relative
counterflow of `V` after the piece (`BW1Term.IsTermRelOf`). -/
def TermRelGraphStatement : Prop :=
  ∃ G : Set (((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)) × RecData), MeasurableSet G ∧
    ∀ (U V : ℝ≥0 → ℝ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞), GW1Path.IsRegCf U → GW1Path.IsRegCf V →
      GW1P.PieceRegular D.1 (min ⊤ D.2) → D.2 ≠ ⊤ → (((U, V), recOf ⊤ D) ∈ G ↔ IsTermRelOf U V D)

theorem termRelGraphStatement : TermRelGraphStatement :=
  ⟨relGraph, measurableSet_relGraph, fun _ _ _ hU hV hD hfin => mem_relGraph_iff hU hV hD hfin⟩

end InteractingSLE.Theorem14.BW1Det
