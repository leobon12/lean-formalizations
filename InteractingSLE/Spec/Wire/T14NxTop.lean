/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T14CurMain
import InteractingSLE.Spec.Supplement.GW2NtWire
import InteractingSLE.Spec.Supplement.SB2JeAS
import InteractingSLE.Spec.Supplement.GW2SdsGap
import InteractingSLE.Spec.Supplement.SB2YdStart
import InteractingSLE.Spec.Supplement.GW2RjTop
import InteractingSLE.Spec.Supplement.GW2RkTop
import InteractingSLE.Spec.Supplement.GW2RlTop
import InteractingSLE.Spec.Supplement.GW2RmTop

/-!
# Theorem 1.4's current top, round 2b: the two-sided gap (D43) and the threshold field from NOTHR's export

Packet PROVE-T14-ASSEMBLE7 (round 2, after the mid-session landing 43ab20d51 of the `T14Cur*` files).
**`Wire.theorem14Statement_assembled10`**: `Wire.theorem14Statement_assembled7C` at SDE's two-sided gap family
`GW2Sdq.gapFam` (decision D43: under the span gap `GW2Sdr.gapFam2` RELDET's D37 is false), with the binder `hno`
replaced by `hexp : GW2Nt.ExportFamily ver (baseWm cw)` (D38's export, PROVE-GW2-STAGEMEAN's stage-start identity at
the launch kernel) through PROVE-GW2-NOTHR's `GW2Nt.hno_baseWm_of_export` (c429f214a). LIFTSET's v6 input comes
from SB2LIFT's start data `hSD : Lk.SB2LowerStartDataFamStatement` through LIFTSET's `Lk.sb2LowerGeomRestV6`
(1a3e07fea). `T14CurMain`'s `assembled8` (span gap) is superseded by D43.
**`Wire.theorem14Statement_assembled11`**: `assembled10` with the gap's positivity PROVED (`GW2Sds.ae_gapFam_pos`).
**`Wire.theorem14Statement_assembled12`**: `assembled11` with SB2LIFT's start data PROVED
(`Lk.sb2LowerStartDataStatement_of_thms`), hence LIFTSET's v6 input proved.
**`Wire.theorem14Statement_assembled13`**: `assembled12` with ROOTX's package `T14Rj.pkgRj` and drift family
`T14Rj.rjDrift`, its shell field PROVED (`T14Rj.hshell_pkgRj`).
**`Wire.theorem14Statement_assembled14`**: `assembled13` with the source counterflow word and `hwords` from ROOTX's
`T14Rk.vwordsX_pkgRj_junction` (`hcov`, `hword`, `heq`).
**`Wire.theorem14Statement_assembled15`**: ROOTX's closed word package (`theorem14Statement_assembled7Wm_rlc`) with
SB2(2) as in `assembled12`–`14` and the threshold field `hno` itself (D38's export is in question, 08e0c9a2d).
**`Wire.theorem14Statement_assembled16`**: ROOTX's single rightward package (D61,
`theorem14Statement_assembled7Wm_oneF`) with SB2(2) as before; `hnearImg` replaced by BUF's `hlaw`, `hdeath`, `hsrc`.

All results are conditional helpers; no frozen declaration changes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: `theorem14Statement_assembled7C` at SDE's two-sided gap
family `GW2Sdq.gapFam` (decision D43; its measurability `GW2Sdq.measurable_gapFam` is proved, its positivity `hpos` is
SDE's), with the threshold field from D38's export (`hexp`, through `GW2Nt.hno_baseWm_of_export`) and LIFTSET's v6
input from SB2LIFT's start data (`hSD`, through LIFTSET's `Lk.sb2LowerGeomRestV6`, 1a3e07fea). -/
theorem theorem14Statement_assembled10
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω)
    (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm cw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm cw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hexp : GW2Nt.ExportFamily ver (baseWm cw))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hSD : SB.Lk.SB2LowerStartDataFamStatement.{u})
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled7C GW2Sdq.gapFam GW2Sdq.measurable_gapFam hpos ver cw hmeanF
    (GW2Nt.hno_baseWm_of_export cw hexp) Kb V hs hnear hwords hnearImg C hshell
    (SB.Lk.sb2LowerGeomRestV6 T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hSD) hcan hdet

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: `theorem14Statement_assembled10` with the gap's positivity
PROVED (SDE's `GW2Sds.ae_gapFam_pos`). -/
theorem theorem14Statement_assembled11
    (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm cw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm cw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hexp : GW2Nt.ExportFamily ver (baseWm cw))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hSD : SB.Lk.SB2LowerStartDataFamStatement.{u})
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled10 (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x) ver cw hmeanF hexp Kb V hs hnear hwords
    hnearImg C hshell hSD hcan hdet

/-- **SB2LIFT's start data (D40) is LIFTSET's verbatim copy** `Lk.SB2LowerStartDataFamStatement`, PROVED
(`Lk.sb2LowerStartDataStatement_of_thms`, 60b3d4230; the two definitions have the same body). -/
theorem sb2LowerStartDataFamStatement : SB.Lk.SB2LowerStartDataFamStatement.{u} :=
  SB.Lk.sb2LowerStartDataStatement_of_thms T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: `theorem14Statement_assembled11` with SB2LIFT's start data
PROVED (`sb2LowerStartDataFamStatement`), so LIFTSET's v6 input `Nv.SB2LowerGeomRestV6Statement` is proved
(`Lk.sb2LowerGeomRestV6`). -/
theorem theorem14Statement_assembled12
    (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm cw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm cw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hexp : GW2Nt.ExportFamily ver (baseWm cw))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled11 ver cw hmeanF hexp Kb V hs hnear hwords hnearImg C hshell sb2LowerStartDataFamStatement
    hcan hdet

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: `theorem14Statement_assembled12` with ROOTX's package
`T14Rj.pkgRj` (SDE's pinned package with D33's optimal slow shells) and drift family `T14Rj.rjDrift cw`, whose slots
and shell field are PROVED (`T14Rj.hshell_pkgRj`, 44019b0c9, from the top's `hmeanF` and the threshold field). -/
theorem theorem14Statement_assembled13
    (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm cw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm cw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hexp : GW2Nt.ExportFamily ver (baseWm cw))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (kSel : NearSel.{u})
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (T14Rj.pkgRj ver cw Kb nb kSel k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((T14Rj.pkgRj ver cw Kb nb kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled12 ver cw hmeanF hexp Kb (T14Rj.pkgRj ver cw Kb nb kSel)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) hnear hwords hnearImg (T14Rj.rjDrift cw)
    (T14Rj.hshell_pkgRj GW2Sdq.gapFam ver cw hmeanF (GW2Nt.hno_baseWm_of_export cw hexp) Kb nb kSel) hcan hdet

/-- **The source counterflow word** (`GW2Sds.cfWordSrc`) as a counterflow-word family. -/
abbrev T14Nx.cwSrc : CfWord.{u} := fun _ _ _ c _ => GW2Sds.cfWordSrc c

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: `theorem14Statement_assembled13` with the counterflow word
the source's (`GW2Sds.cfWordSrc`, SDE's choice) and `hwords` from ROOTX's `T14Rk.vwordsX_pkgRj_junction`
(4023146ac, D53): the version family's coverage `hcov` (SDE: `GW2Sdt.hcov_canon`, `GW2Sdt.hcov_death`, transported by
`GW2Sdt.eventually_lt_reindex`), BUF's near slots `hword`, the near base's identity `heq`; the slow words (D33's
shells) and the near base's structure (SDE's `GW2Sds.hstruct_junction`) are proved. -/
theorem theorem14Statement_assembled14

    (ver : GW2Rv.SchedVerXFamily.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm T14Nx.cwSrc) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm T14Nx.cwSrc) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm T14Nx.cwSrc) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω (g ω))
    (hexp : GW2Nt.ExportFamily ver (baseWm T14Nx.cwSrc))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (kSel : NearSel.{u})
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm T14Nx.cwSrc)) (Kb k))
    (hcov : T14Rk.VerCovers ver)
    (hword : ∀ k : ℕ, T14Rk.NearSlotWords GW2Sdq.gapFam ver T14Nx.cwSrc Kb nb k)
    (heq : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l → ∃ a n : ℕ,
        ENNReal.ofReal (GW2Rz.clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l a).V n ω ∧
        nb Ω c r l ω = GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (GW2Rd.augRec (GW2Rd.stageEncRec c r l) (GW2Rz.stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
            (GW2Rz.schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
            (RootJ31.historyTime c r l) ((ver Ω c r l a).R n)) ω))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((T14Rj.pkgRj ver T14Nx.cwSrc Kb nb kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS GW2Sdq.gapFam Ω c r l))
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled13 ver T14Nx.cwSrc hmeanF hexp Kb nb kSel hnear
    (T14Rk.vwordsX_pkgRj_junction ver hmeanF (GW2Nt.hno_baseWm_of_export _ hexp) Kb nb kSel hcov hword heq) hnearImg
    hcan hdet

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: ROOTX's word package closed
(`theorem14Statement_assembled7Wm_rlc`, fabb481b0: the re-indexed death family `T14Rl.rlVer ψx`, the source
counterflow word, the reference near base; `hcov`, `hword`, `heq` proved) with SB2(2) from LIFTSET's proved v6 input
(`assembled12`'s route) and CONDFIN's root reduction.
The threshold field is the binder `hno` itself (STAGEMEAN, 08e0c9a2d: D38's export is not provable as stated). -/
theorem theorem14Statement_assembled15 (ψx : GW2Rl.PsiFamR.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC (T14Rl.rlVer ψx) (baseWm T14Rl.rlCw) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC (T14Rl.rlVer ψx) (baseWm T14Rl.rlCw) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC (T14Rl.rlVer ψx) (baseWm T14Rl.rlCw) Ω c r l a n h) c r l (rootPt r.1) w t ψ ω
            (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC (T14Rl.rlVer ψx) (baseWm T14Rl.rlCw) Ω c r l a n h) c r l (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (kSel : NearSel.{u})
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 (T14Rl.rlVer ψx) (chL (baseWm T14Rl.rlCw)) (Kb k))
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((T14Rj.pkgRj (T14Rl.rlVer ψx) T14Rl.rlCw Kb (T14Rl.rlNb ψx) kSel k).at 0) GW2Sdh.nearLam
        Ω c r l
        ((k : ℝ≥0∞) + 1)⁻¹ (aliveS GW2Sdq.gapFam Ω c r l))
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled7Wm_rlc ψx hmeanF hno Kb kSel hnear hnearImg
    (SB.Cg.sb2LowerTailLiftExStatement_of_rest T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
      (SB.Lk.sb2LowerGeomRestV6 T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ sb2LowerStartDataFamStatement) hcan
      (SB.Ch.sb2LowerRelPosWRootStatement_of_det T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hdet))

/-- **Theorem 1.4, current top (PROVE-T14-ASSEMBLE7)**: ROOTX's single rightward package (D61,
`theorem14Statement_assembled7Wm_oneF`, 68b6a53bd: BUF's `withNearSB` selection on the re-indexed death family with
`psiGoodFam`, exit rules `exitB`; `hwords`, `hshell`, `hs`, `hnear` PROVED; `hnearImg` from BUF's
`vNearImgOn_of_nearData`) with SB2(2) as in `assembled15`. Open: the top's instance fields `hmeanF`, `hno`, BUF's
`hlaw`, `hdeath`, `hsrc`, and SB2(2)'s `hcan`, `hdet`. -/
theorem theorem14Statement_assembled16 (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean
          ((instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h).B t)
          (WholeField.centredField c.h
            (instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h).u₀)
          c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX
            (instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
            (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX
        (instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
        (rootPt r.1))
    (hlaw : GW2Bh.StageLawXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13))
    (hdeath : GW2Bh.DeathThrXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13)
      (GW2Bh.pkgCh T14Asm7.h13 T14Asm7.h12 GW2Bh.cwSrc))
    (hsrc : GW2Bh.SrcBoundStatement.{u} T14Asm7.h13 T14Asm7.h12 K₀ kSel)
    (hcan : SB.Mz.SB2LowerStageCanonStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13))
    (hdet : SB.Ch.SB2LowerRootDetWStatement.{u}
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled7Wm_oneF K₀ kSel hmeanF hno hlaw hdeath hsrc
    (SB.Cg.sb2LowerTailLiftExStatement_of_rest T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀
      (SB.Lk.sb2LowerGeomRestV6 T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ sb2LowerStartDataFamStatement) hcan
      (SB.Ch.sb2LowerRelPosWRootStatement_of_det T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hdet))

/-- **GW2's root tests on ROOTX's single rightward package with BUF's final choices** (the GW2 half of
`theorem14Statement_assembled7Wm_oneF`, for the light-cone provider): from the top's instance fields and BUF's
`hlaw`, `hdeath`, `hsrc`. -/
theorem T14Nx.gw2RootTestStatement_oneF (K₀ : GW2Sde.PkgFamily.{u}) (kSel : GW2Bh.NearSelB.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean
          ((instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h).B t)
          (WholeField.centredField c.h
            (instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12))
              (baseWm GW2Bh.cwSrc) Ω c r l a n h).u₀) c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX
            (instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
            (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX
        (instC (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12)) (baseWm GW2Bh.cwSrc) Ω c r l a n h) c r l
        (rootPt r.1))
    (hlaw : GW2Bh.StageLawXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13))
    (hdeath : GW2Bh.DeathThrXStatement.{u} T14Asm7.h13 (GW2Rd.schedVerXDeathFamily T14Asm7.h13)
      (GW2Bh.pkgCh T14Asm7.h13 T14Asm7.h12 GW2Bh.cwSrc))
    (hsrc : GW2Bh.SrcBoundStatement.{u} T14Asm7.h13 T14Asm7.h12 K₀ kSel) :
    GW2RootTestStatement.{u} :=
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm GW2Bh.cwSrc) (hE₀_baseWm GW2Bh.cwSrc)
    (hbd_baseWm GW2Bh.cwSrc) hmeanF hno
  T14Cur.gw2RootTestStatement_fields GW2Sdq.gapFam GW2Sdq.measurable_gapFam
    (fun _ _ _ c x => GW2Sds.ae_gapFam_pos c x) (T14Rm.oneVer (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12))
    (baseWm GW2Bh.cwSrc)
    (hword_baseWm GW2Bh.cwSrc) (hE₀_baseWm GW2Bh.cwSrc) (hbd_baseWm GW2Bh.cwSrc) hmeanF hno
    (T14Rm.oneKb (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀)
    (T14Rm.pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel)
    (T14Rm.sameSlots_pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel)
    (T14Rm.nearStopsX_pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ hI
      (fun Ω _ _ c r l n a => GW2Bh.exitB_spec Ω c r l n a))
    (T14Rm.vwordsX_pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel hI)
    (fun k Ω _ _ c r l => T14Rm.vNearImgOn_pkgOne K₀ kSel hI hlaw hdeath hsrc k Ω c r l) (T14Rj.rjDrift GW2Bh.cwSrc)
    (T14Rm.hshell_pkgOne (GW2Bh.psiGoodFam T14Asm7.h13 T14Asm7.h12) GW2Bh.exitB K₀ kSel hI GW2Sdq.gapFam)

end InteractingSLE.Wire
