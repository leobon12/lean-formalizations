/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Nil
import InteractingSLE.Spec.Supplement.GW2TwMean
import InteractingSLE.Spec.Supplement.GW2NxMean
import InteractingSLE.Spec.Supplement.GW2NyKer
import InteractingSLE.Spec.Supplement.GW2RmPkg

/-!
# The top's `hmeanF` binder for the re-indexed stop family (D68 item 2)

Packet PROVE-GW2-GEOM2, round 15 (D68). The top (`Wire.theorem14Statement_assembled7Wm_one(F)`, ROOTX's `GW2RmTop`)
reads `hmeanF` at `T14Cur.instC ver (T14Cur.baseWm GW2Bh.cwSrc)`. D68 rules that the top's single version family is
NOTHR's stop family `GW2Nx.schedVerXStopFamily`, re-indexed with BUF's `ψx`. This file proves the top's binder for
that family:

* **the bridge** `isCfWordOf_cwSrc`: BUF's word `GW2Bh.cwSrc` (the source counterflow's data word `cfWordSrc`) is a
  word of the counterflow's data, like NOTHR's `cfWordCanon`. The `hmeanF` proofs are generic in such words, so no
  identification of the two words is needed;
* **the re-indexing**: a re-indexed family's instance at version `n` is the original instance at version `φ n`
  (BUF's `instX_reindex`, by `rfl`). The binder for `verReindex (schedVerXStopFamily h13) φ hφ` is therefore the
  stop family's binder at `φ n`, for every strictly monotone `φ`;
* **the guard** (D54/D67): strictly ordered histories and roots `0 ∨ lowerArcRoots`. `HmeanFGuarded ver base` is the
  guarded binder form that ASSEMBLE7 must re-wire into the top. `guard_of_aliveS` shows that every history the top
  reads (an alive history of the scaled family) satisfies the guard.

Main results: **`hmeanFGuarded_stopReindex`** (any strictly monotone re-indexing) and **`hmeanFGuarded_stopPkgVer`**
(BUF's re-indexing `reindexPlus (pkgPsi h13 ψx)`, the stop analogue of `GW2Bh.pkgVer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Kt

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd
  Sec5.Prop513Schedule Supp8 Supp8.Q3Stop

/-- **The bridge**: BUF's counterflow word `cwSrc` is a word of the source counterflow's data. -/
theorem isCfWordOf_cwSrc (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) : GW2Kb.IsCfWordOf c.κ c.P c.h c.W c.ζ (GW2Bh.cwSrc Ω c r) := by
  obtain ⟨h', htr, hfl⟩ := GW2Cone.isFlowLineDriver_counterflowData c.hκ c.hb c.hh c.hcf
  exact ⟨_, _, h', Sec7.StripSysField.isPiecewiseConstant_counterflowData c.κ c.hb, htr, hfl,
    GW2Sds.cfWordSrc_jumps c, GW2Sds.cfWordSrc_fn c⟩

/-- **The guarded `hmeanF` binder** (D54/D67): the top's `hmeanF` binder at the top's instances
`T14Cur.instC ver base`, on strictly ordered histories and at roots `0 ∨ lowerArcRoots`. This is the form ASSEMBLE7
must re-wire into the top; `guard_of_aliveS` supplies the guard at every history the top reads. -/
def HmeanFGuarded (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) →
    (h : GW2Rv.GoodRoot c r) → (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) →
    ∀ (a n : ℕ) (w : WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      LocalSets.IsLocalSetMean ((Wire.T14Cur.instC ver base Ω c r l a n h).B t)
        (WholeField.centredField c.h (Wire.T14Cur.instC ver base Ω c r l a n h).u₀) c.P g →
      ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
        stageMeanAtX (Wire.T14Cur.instC ver base Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω)

/-- **The guard holds at every history the top reads**: an alive history of the scaled family is strictly ordered
and its root is `0` or in `lowerArcRoots` (NOTHR's `aliveS_pairwise_lt`, `aliveS_root_cases`). -/
theorem guard_of_aliveS (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) {ω : Ω}
    (hω : ω ∈ Wire.T14Cur.aliveS gap Ω c r l) :
    (historyProgram c r l).Pairwise (fun p q => p.2 < q.2) ∧
      (rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) :=
  ⟨GW2Nx.aliveS_pairwise_lt gap Ω c r l hω, GW2Ny.aliveS_root_cases gap Ω c r l hω⟩

/-- **The guarded binder for the stop family at BUF's word** (roots `0 ∨ lowerArcRoots`): RELDET's
`hmeanF_rootX_of_nil` with GEOM2's base `claimAllX_nil_rootX` and NOTHR's `hVd_stop`. -/
theorem hmeanFGuarded_stop :
    HmeanFGuarded (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) (Wire.T14Cur.baseWm GW2Bh.cwSrc) := by
  intro Ω _ _ c r l hord h hroot a n w t g hg ψ
  exact hmeanF_rootX_of_nil (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) GW2Bh.cwSrc isCfWordOf_cwSrc
    (fun Ω _ _ c r hg hx => GW2Kx.claimAllX_nil_rootX Wire.T14Asm7.h12 Wire.T14Asm7.h13 Wire.T14Asm7.h12₀
      Wire.T14Asm7.h13₀ c r (Or.inr hx) hg.2 (isCfWordOf_cwSrc Ω c r))
    (GW2Nx.hVd_stop GW2Bh.cwSrc) Ω c r l hord h hroot a n w t g hg ψ

/-- **The guarded binder for the stop family re-indexed by any strictly monotone `φ`**: the re-indexed instance at
version `n` is the stop instance at version `φ n` (`GW2Bh.instX_reindex`, by `rfl`). -/
theorem hmeanFGuarded_stopReindex
    (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a)) :
    HmeanFGuarded (GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13) φ hφ)
      (Wire.T14Cur.baseWm GW2Bh.cwSrc) := by
  intro Ω _ _ c r l hord h hroot a n w t g hg ψ
  exact hmeanFGuarded_stop Ω c r l hord h hroot a (φ Ω c r l a n) w t g hg ψ

/-- **The stop family re-indexed with BUF's re-indexing** `reindexPlus (pkgPsi h13 ψx)` (the stop analogue of
`GW2Bh.pkgVer`, D68). -/
def stopPkgVer (ψx : GW2Bh.PsiFam.{u}) : GW2Rv.SchedVerXFamily.{u} :=
  GW2Bh.verReindex (GW2Nx.schedVerXStopFamily Wire.T14Asm7.h13)
    (fun Ω _ _ c r l a => GW2Bh.reindexPlus (GW2Bh.pkgPsi Wire.T14Asm7.h13 ψx Ω c r l a))
    (fun Ω _ _ c r l a => GW2Bh.strictMono_reindexPlus (GW2Bh.monotone_pkgPsi Wire.T14Asm7.h13 ψx Ω c r l a))

/-- **The top's guarded `hmeanF` binder for the stop family re-indexed with BUF's `ψx`, at BUF's word `cwSrc`.** -/
theorem hmeanFGuarded_stopPkgVer (ψx : GW2Bh.PsiFam.{u}) :
    HmeanFGuarded (stopPkgVer ψx) (Wire.T14Cur.baseWm GW2Bh.cwSrc) :=
  hmeanFGuarded_stopReindex _ _

end InteractingSLE.Theorem14.GW2Kt
