/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RpClosed
import InteractingSLE.Spec.Supplement.GW2RlBot
import InteractingSLE.Spec.Supplement.GW2RmTop
import InteractingSLE.Spec.Supplement.GW2NxCov

/-!
# The single package on NOTHR's stop family (D68 (3))

PROVE-GW2-ROOTX round 14. D68: the top's version family is NOTHR's stop family `GW2Nx.schedVerXStopFamily`,
re-indexed with BUF's `ψx`. BUF reports (its handoff, round 20, "D68 answer") that nearImg's version-loss clause fails
as stated on the stop family. So both packages are kept: round 12's `T14Rm.pkgOne` (death family, BUF's nearImg)
and this one.

**The re-indexing.** The near words need EVERY candidate's slot to pass the history clock, eventually in `m`
(uniformly). BUF's `pkgPsi` gets this from `psiCov`, which is built on the DEATH family's cover events. The stop
family is an independent choice (not the death family capped at the stop), so `psiCov` says nothing about it, and
for GEOM2's `GW2Kt.stopPkgVer ψx` (which re-uses `pkgPsi`) no uniform cover is available. The stop analogue of
`pkgVer` uses the stop family's own cover events: ROOTX's `GW2Rl.verU`,

  `oneVerS ψx = verU (schedVerXStopFamily h13) ψx`, re-indexed by `m ↦ max (psiU_stop a m, monoHull ψx a m) + m`,

with `VerCovers` from NOTHR's `hcov_stop`. GEOM2's `hmeanFGuarded_stopReindex` and ROOTX's `hno_stopReindex` hold
for every strictly monotone re-indexing, so `hmeanF` and `hno` (guarded) hold for `oneVerS ψx` too.

**The package** `pkgOneS ψx Ex K₀ kSel k`:
`withNearSB (withShell (pkgXk (oneVerS ψx) cwSrc (oneKbS ψx Ex K₀) k) (rjShells …)) nearLam (oneNbS ψx) (kSel k)`,
with BUF's near stops `nearStopPkgX` for the exits `Ex` and ROOTX's reference near base `GW2Rl.refNb`. Proved:
`sameSlots_pkgOneS` (`hs`), `slowShell_pkgOneS` (`hsh`), **`hshell_pkgOneS`**, **`nearStopsX_pkgOneS`** (`hnear`),
**`vwordsX_pkgOneS`** (`hwords`), **`hmeanFGuarded_oneVerS`**, **`hnoGuarded_oneVerS`**, and the top
**`Wire.theorem14Statement_assembled7Wm_oneS`** (as round 12's `_one`; `hnearImg` for `pkgOneS` left to BUF's corrected
stop route).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Wire.T14Rp

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk

/-- NOTHR's stop family covers the history clock (`GW2Nx.hcov_stop`). -/
theorem verCovers_stop : VerCovers (GW2Nx.schedVerXStopFamily T14Asm7.h13) :=
  GW2Nx.hcov_stop T14Asm7.h13

/-- **The top's version family on the stop family** (D68): the stop family re-indexed uniformly on its own cover
events and by BUF's `ψx`. -/
abbrev oneVerS (ψx : GW2Bh.PsiFam.{u}) : GW2Rv.SchedVerXFamily.{u} :=
  GW2Rl.verU (GW2Nx.schedVerXStopFamily T14Asm7.h13) ψx

/-- The base packages: BUF's near stops for the exits `Ex` on `K₀` (every buffer index). -/
abbrev oneKbS (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u}) :
    ℕ → GW2Sde.PkgFamily.{u} :=
  fun _ => GW2Bh.nearStopPkgX T14Asm7.h13 (oneVerS ψx) (chL (baseWm GW2Bh.cwSrc)) Ex K₀

/-- The near base: the base word of the first version beyond the clock (ROOTX's `GW2Rl.refNb`). -/
abbrev oneNbS (ψx : GW2Bh.PsiFam.{u}) : NearBase.{u} := GW2Rl.refNb T14Asm7.h13 (oneVerS ψx) GW2Bh.cwSrc

/-- **The single package on the stop family** at buffer index `k`. -/
abbrev pkgOneS (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u})
    (kSel : GW2Bh.NearSelB.{u}) (k : ℕ) : GW2Sdx.VPkgXFamily.{u} :=
  GW2Bh.withNearSB (withShell (pkgXk (oneVerS ψx) GW2Bh.cwSrc (oneKbS ψx Ex K₀) k)
    (rjShells (oneVerS ψx) GW2Bh.cwSrc)) GW2Sdh.nearLam (oneNbS ψx) (kSel k)

variable (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u}) (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})

/-- The re-indexed stop family covers the history clock. -/
theorem verCovers_oneVerS : VerCovers (oneVerS ψx) := GW2Rl.verCovers_verU verCovers_stop ψx

/-- **The package has the slots of ROOTX's package** (the top's `hs`). -/
theorem sameSlots_pkgOneS (k : ℕ) :
    GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 (oneVerS ψx) (chL (baseWm GW2Bh.cwSrc)) (oneKbS ψx Ex K₀ k))
      (pkgOneS ψx Ex K₀ kSel k) :=
  fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-- **The package's slow shells are D33's** (`hsh`). -/
theorem slowShell_pkgOneS (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (pkgOneS ψx Ex K₀ kSel k Ω c r).slowShell l a ω =
      GW2Rj.rjShell T14Asm7.h13 (oneVerS ψx) (GW2Bh.cwSrc Ω c r) c r l a ω :=
  rfl

/-- **The near stops are good** (`hnear`), for exits that are measurable path rules. -/
theorem nearStopsX_pkgOneS (hI : GW2Rv.InstInputsX T14Asm7.h13 (oneVerS ψx) (chL (baseWm GW2Bh.cwSrc)))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a)) (k : ℕ) :
    GW2Rv.NearStopsX T14Asm7.h13 (oneVerS ψx) (chL (baseWm GW2Bh.cwSrc)) (oneKbS ψx Ex K₀ k) :=
  GW2Bh.nearStopsX_nearStopPkgX hI hE K₀

/-- **`hshell` for the stop package**: D33's shell field at buffer index `0`, any gap family. -/
theorem hshell_pkgOneS (hI : GW2Rv.InstInputsX T14Asm7.h13 (oneVerS ψx) (chL (baseWm GW2Bh.cwSrc)))
    (gap : RootCv.GapFamily.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (rjDrift GW2Bh.cwSrc Ω c r) ((pkgOneS ψx Ex K₀ kSel 0 Ω c r).slowShell l a ω) ∧
            ((pkgOneS ψx Ex K₀ kSel 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω := by
  intro Ω _ _ c r k l hl a
  exact GW2Rj.rjShell_fact_scaled (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI GW2Bh.cwSrc
    (hβ_baseWm GW2Bh.cwSrc) (hE₀eq_baseWm GW2Bh.cwSrc) gap Ω c r k l hl a

/-- The near base's identity for the stop package (`GW2Rl.heq_refNb`). -/
theorem heq_oneNbS :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l → ∃ a n : ℕ,
        ENNReal.ofReal (GW2Rz.clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
          (oneVerS ψx Ω c r l a).V n ω ∧
        oneNbS ψx Ω c r l ω = GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s
          (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (GW2Rd.augRec (GW2Rd.stageEncRec c r l) (GW2Rz.stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
            (GW2Rz.schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((oneVerS ψx Ω c r l a).V n)
            (RootJ31.historyTime c r l) ((oneVerS ψx Ω c r l a).R n)) ω) :=
  fun Ω _ _ c r l hg => GW2Rl.heq_refNb T14Asm7.h13 (oneVerS ψx) GW2Sdq.gapFam GW2Bh.cwSrc
    (verCovers_oneVerS ψx) Ω c r l hg

/-- **`hwords` for the stop package** (rightward form): ROOTX's near words for a uniformly covering family
(`GW2Rl.ae_nearSlotWords`, `unifCover_verU`), the rightward structure (`GW2Rl.hstructBot_junction`) and ROOTX's slow
words for `rjShell`. -/
theorem vwordsX_pkgOneS (hI : GW2Rv.InstInputsX T14Asm7.h13 (oneVerS ψx) (chL (baseWm GW2Bh.cwSrc))) (k : ℕ) :
    GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (pkgOneS ψx Ex K₀ kSel k) GW2Sdh.nearLam := by
  have hslow := GW2Rk.frameNSlowWordN_rjShell
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI
    GW2Sdq.gapFam GW2Sdh.nearLam GW2Bh.cwSrc (hβ_baseWm GW2Bh.cwSrc) (hE₀eq_baseWm GW2Bh.cwSrc)
    (verCovers_oneVerS ψx)
    (withShell (pkgXk (oneVerS ψx) GW2Bh.cwSrc (oneKbS ψx Ex K₀) k) (rjShells (oneVerS ψx) GW2Bh.cwSrc))
    (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl)
  refine GW2Bh.vwordsX_withNearSB _ GW2Sdh.nearLam (oneNbS ψx) (kSel k) GW2Sdh.nearLam_ne (fun Ω _ _ c r l => ?_)
    (GW2Rl.hstructBot_junction (oneVerS ψx) (oneNbS ψx) (heq_oneNbS ψx)) hslow
  filter_upwards [GW2Rl.ae_nearSlotWords (h13 := T14Asm7.h13) (oneVerS ψx) GW2Bh.cwSrc (hβ_baseWm GW2Bh.cwSrc)
    (hE₀eq_baseWm GW2Bh.cwSrc) (GW2Rl.unifCover_verU T14Asm7.h13 verCovers_stop ψx) (oneKbS ψx Ex K₀ k)
    GW2Sdq.gapFam Ω c r l] with ω hω halive n
  filter_upwards [hω halive n] with m hm i j
  obtain ⟨h1, h2⟩ := hm (Nat.pair i j)
  refine ⟨h1, h2.trans ?_⟩
  rw [GW2Sdy.candidateAngle_pair]

/-- **The top's guarded `hmeanF` for the stop package's family** (GEOM2's `hmeanFGuarded_stopReindex`). -/
theorem hmeanFGuarded_oneVerS : GW2Kt.HmeanFGuarded (oneVerS ψx) (baseWm GW2Bh.cwSrc) :=
  GW2Kt.hmeanFGuarded_stopReindex _ _

/-- **The top's guarded `hno` for the stop package's family** (`GW2Rp.hno_stopReindex`). -/
theorem hnoGuarded_oneVerS : GW2Rp.HnoGuarded (oneVerS ψx) (baseWm GW2Bh.cwSrc) :=
  GW2Rp.hno_stopReindex GW2Bh.cwSrc GW2Kt.isCfWordOf_cwSrc _ _

end InteractingSLE.Wire.T14Rp

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk
  T14Rp

/-- **Theorem 1.4 on the stop package** (D68): `hgap`, `hpos`, `hs`, `C`, `hshell`, `hnear` and `hwords` discharged
(round 12's `_one` with `pkgOneS`). The guarded forms of `hmeanF`, `hno` are `T14Rp.hmeanFGuarded_oneVerS`,
`hnoGuarded_oneVerS`; `hnearImg` for `pkgOneS` is BUF's corrected stop route. -/
theorem theorem14Statement_assembled7Wm_oneS (ψx : GW2Bh.PsiFam.{u}) (Ex : GW2Bh.ExitFam.{u})
    (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC (oneVerS ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC (oneVerS ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC (oneVerS ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω
            (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC (oneVerS ψx) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l (rootPt r.1))
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ),
      Supp8.GB6.HullId.IsPathRule (Ex Ω c r l n a) ∧ Measurable (Ex Ω c r l n a))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgOneS ψx Ex K₀ kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} := by
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm GW2Bh.cwSrc) (hE₀_baseWm GW2Bh.cwSrc)
    (hbd_baseWm GW2Bh.cwSrc) hmeanF hno
  exact theorem14Statement_assembled7Wm_shell GW2Sdq.gapFam GW2Sdq.measurable_gapFam
    (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x) (oneVerS ψx) GW2Bh.cwSrc hmeanF hno (oneKbS ψx Ex K₀)
    (pkgOneS ψx Ex K₀ kSel) (sameSlots_pkgOneS ψx Ex K₀ kSel) (slowShell_pkgOneS ψx Ex K₀ kSel 0)
    (nearStopsX_pkgOneS ψx Ex K₀ hI hE) (vwordsX_pkgOneS ψx Ex K₀ kSel hI) hnearImg hTL

end InteractingSLE.Wire
