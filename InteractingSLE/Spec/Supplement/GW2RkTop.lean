/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RkSlow
import InteractingSLE.Spec.Supplement.GW2RjTop
import InteractingSLE.Spec.Supplement.GW2SdsWords

/-!
# `hwords` for `pkgRj` (decision D53)

PROVE-GW2-ROOTX round 10. The top `Wire.theorem14Statement_assembled7Wm_rj` (round 9) has the binder `hwords` for the
package `pkgRj` (SDE's `pkgS` with D33's shells). `VWordsX` is the near words and the slow words; SDE's
`GW2Sdo.vwordsX_withNearS` assembles it from the near slots' words (`hword`), the near base's structure (`hstruct`)
and the slow words (`hslow`). Here `hslow` is PROVED for D33's shells (`GW2Rk.frameNSlowWordN_rjShell`):

* `pkgRj_eq`: `pkgRj = withNearS (withShell (pkgX …) rjShells) …` (definitional);
* **`vwordsX_pkgRj`**: `hwords` for `pkgRj` from the version family's coverage (`hcov`, SDE's form), `hword` (BUF's
  re-indexed near slots, D45 (1)) and `hstruct`;
* **`vwordsX_pkgRj_junction`**: the same with SDE's `hstruct_junction` (gap `GW2Sdq.gapFam`, counterflow word
  `cfWordSrc`), so only `hcov`, `hword` and the near base's identity `heq` remain;
* **`Wire.theorem14Statement_assembled7Wm_rjw`**: round 9's top with `hwords` replaced by `hcov`, `hword`,
  `hstruct`;
* **`Wire.theorem14Statement_assembled7Wm_shell`**: the current top with the shell field discharged for ANY package
  whose slow shells at buffer index `0` are D33's (e.g. BUF's `withNearSB` package with `rjShells`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Wire.T14Rk

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj

/-- ROOTX's package of the top at buffer index `k`. -/
abbrev pkgXk (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u}) (Kb : ℕ → GW2Sde.PkgFamily.{u}) (k : ℕ) :
    GW2Sdx.VPkgXFamily.{u} :=
  GW2Rv.pkgX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k)

theorem pkgRj_eq (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u}) (Kb : ℕ → GW2Sde.PkgFamily.{u})
    (nb : NearBase.{u}) (kSel : NearSel.{u}) (k : ℕ) :
    pkgRj ver cw Kb nb kSel k =
      GW2Sdx.VPkgXFamily.withNearS (withShell (pkgXk ver cw Kb k) (rjShells ver cw)) GW2Sdh.nearLam nb kSel :=
  rfl

/-- **The near slots' words** of ROOTX's package at buffer index `k` with near base `nb` (SDE's `hword`). -/
abbrev NearSlotWords (gap : RootCv.GapFamily.{u}) (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (k : ℕ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i j : ℕ,
      ((pkgXk ver cw Kb k Ω c r).nearVar l n m (Nat.pair i j)).record ω ∈
          ((pkgXk ver cw Kb k Ω c r).nearVar l n m (Nat.pair i j)).E ∧
        ((pkgXk ver cw Kb k Ω c r).nearVar l n m (Nat.pair i j)).β
            (((pkgXk ver cw Kb k Ω c r).nearVar l n m (Nat.pair i j)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (nb Ω c r l ω)

/-- **The near base's structure** (SDE's `hstruct`). -/
abbrev NearBaseStruct (gap : RootCv.GapFamily.{u}) (nb : NearBase.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)),
    ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
      GW2Sdy.NearStruct c.κ (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
        (nb Ω c r l ω)

/-- **The version family covers the history clock** on the alive events (SDE's `hcov`; discharged by SDE's
`GW2Sdt.hcov_death`, `GW2Sdt.hcov_canon`, and `GW2Sdt.eventually_lt_reindex` for BUF's re-indexings). -/
abbrev VerCovers (ver : GW2Rv.SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r →
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ GW2Rz.goodX (rootPt r.1) c.s →
      (RootJ31.historyTime c r l : ℝ≥0∞) < GW2Rz.contactX (rootPt r.1) c.s (GW2Rd.schedTr c r l a) c.α ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (GW2Rz.clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
        (RootJ31.historyTime c r l) ω) < (ver Ω c r l a).V n ω

/-- **`hwords` for `pkgRj`**: the slow words are D33's (`GW2Rk.frameNSlowWordN_rjShell`); the near words are SDE's
assembly from `hword` and `hstruct`. -/
theorem vwordsX_pkgRj (gap : RootCv.GapFamily.{u}) (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
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
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (kSel : NearSel.{u}) (hcov : VerCovers ver)
    (hword : ∀ k : ℕ, NearSlotWords gap ver cw Kb nb k) (hstruct : NearBaseStruct gap nb) :
    ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (pkgRj ver cw Kb nb kSel k) GW2Sdh.nearLam := by
  intro k
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm cw) (hE₀_baseWm cw) (hbd_baseWm cw) hmeanF hno
  have hslow := GW2Rk.frameNSlowWordN_rjShell
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI gap
    GW2Sdh.nearLam cw (hβ_baseWm cw) (hE₀eq_baseWm cw) hcov (withShell (pkgXk ver cw Kb k) (rjShells ver cw))
    (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl)
  rw [pkgRj_eq]
  exact GW2Sdo.vwordsX_withNearS (withShell (pkgXk ver cw Kb k) (rjShells ver cw)) GW2Sdh.nearLam nb kSel
    GW2Sdh.nearLam_ne (hword k) hstruct hslow

/-- **`hwords` for `pkgRj` on SDE's junction-gap cover with the source counterflow word**: `hstruct` is SDE's
`GW2Sds.hstruct_junction`; what remains is the coverage `hcov`, BUF's near slots `hword`, and the near base's
identity `heq` (the near base is GEOM2's base word of a version beyond the history clock). -/
theorem vwordsX_pkgRj_junction (ver : GW2Rv.SchedVerXFamily.{u})
    (hmeanF : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, ∀ (w : Supp8.Q3Stop.WordType) (t : ℝ≥0) (g : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        LocalSets.IsLocalSetMean ((instC ver (baseWm fun _ _ _ c _ => GW2Sds.cfWordSrc c) Ω c r l a n h).B t)
          (WholeField.centredField c.h (instC ver (baseWm fun _ _ _ c _ => GW2Sds.cfWordSrc c) Ω c r l a n h).u₀)
          c.P g →
        ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P,
          GW2Rz.stageMeanAtX (instC ver (baseWm fun _ _ _ c _ => GW2Sds.cfWordSrc c) Ω c r l a n h) c r l
            (rootPt r.1) w t ψ ω (g ω))
    (hno : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GW2Rv.GoodRoot c r) →
      ∀ a n : ℕ, GW2Rz.NoThresholdX (instC ver (baseWm fun _ _ _ c _ => GW2Sds.cfWordSrc c) Ω c r l a n h) c r l
        (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (kSel : NearSel.{u}) (hcov : VerCovers ver)
    (hword : ∀ k : ℕ, NearSlotWords GW2Sdq.gapFam ver (fun _ _ _ c _ => GW2Sds.cfWordSrc c) Kb nb k)
    (heq : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Rv.GoodRoot c r →
      ∀ᵐ ω ∂c.P, ω ∈ aliveS GW2Sdq.gapFam Ω c r l → ∃ a n : ℕ,
        ENNReal.ofReal (GW2Rz.clockX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a) (RootJ31.historyTime c r l) ω) <
          (ver Ω c r l a).V n ω ∧
        nb Ω c r l ω = GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (GW2Rd.augRec (GW2Rd.stageEncRec c r l) (GW2Rz.stgPreRecX (rootPt r.1) c.s c.W c.ζ (GW2Rd.schedW c r l a)
            (GW2Rz.schedGTX Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} c r l a) ((ver Ω c r l a).V n)
            (RootJ31.historyTime c r l) ((ver Ω c r l a).R n)) ω)) :
    ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam)
      (pkgRj ver (fun _ _ _ c _ => GW2Sds.cfWordSrc c) Kb nb kSel k) GW2Sdh.nearLam :=
  vwordsX_pkgRj GW2Sdq.gapFam ver (fun _ _ _ c _ => GW2Sds.cfWordSrc c) hmeanF hno Kb nb kSel hcov hword
    (GW2Sds.hstruct_junction ver nb heq)

end InteractingSLE.Wire.T14Rk

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj T14Rk

/-- **Theorem 1.4, round 9's top with `hwords` assembled** (D53): the package `pkgRj`, with `hwords` from the
coverage of the version family, BUF's near slots and the near base's structure (the slow words are D33's). -/
theorem theorem14Statement_assembled7Wm_rjw (gap : RootCv.GapFamily.{u})
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
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (kSel : NearSel.{u})
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hcov : VerCovers ver) (hword : ∀ k : ℕ, NearSlotWords gap ver cw Kb nb k) (hstruct : NearBaseStruct gap nb)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgRj ver cw Kb nb kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS gap Ω c r l))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_assembled7Wm_rj gap hgap hpos ver cw hmeanF hno Kb nb kSel hnear
    (vwordsX_pkgRj gap ver cw hmeanF hno Kb nb kSel hcov hword hstruct) hnearImg hTL

/-- **Theorem 1.4, the current top with the shell field discharged for ANY package with D33's slow shells** at
buffer index `0` (e.g. BUF's `withNearSB` package with `rjShells`): `C := Cstar`. -/
theorem theorem14Statement_assembled7Wm_shell (gap : RootCv.GapFamily.{u})
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
    (hsh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω),
      (V 0 Ω c r).slowShell l a ω = GW2Rj.rjShell T14Asm7.h13 ver (cw Ω c r) c r l a ω)
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX T14Asm7.h13 ver (chL (baseWm cw)) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹ (aliveS gap Ω c r l))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} := by
  refine theorem14Statement_assembled7Wm gap hgap hpos ver cw hmeanF hno Kb V hs hnear hwords hnearImg (rjDrift cw)
    ?_ hTL
  intro Ω _ _ c r k l hl a
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm cw) (hE₀_baseWm cw) (hbd_baseWm cw) hmeanF hno
  filter_upwards [GW2Rj.rjShell_fact_scaled
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI cw
    (hβ_baseWm cw) (hE₀eq_baseWm cw) gap Ω c r k l hl a] with ω hω halive
  rw [hsh]
  exact hω halive

end InteractingSLE.Wire
