/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ZtWire
import InteractingSLE.Spec.Supplement.SB2WfFin
import InteractingSLE.Spec.Supplement.GW2SdyTop
import InteractingSLE.Spec.Supplement.GW2GmQJ32
import InteractingSLE.Spec.Supplement.GW2SdqGap
import InteractingSLE.Spec.Sec5.Aux61CptThm
import InteractingSLE.Spec.Supplement.GW2RvPkg
import InteractingSLE.Spec.Supplement.SB2LkEx
import InteractingSLE.Spec.Supplement.GW2RtDrift
import InteractingSLE.Spec.Supplement.GW2TpSets

/-!
# Theorem 1.4 re-assembled from the landed successors: the open list

Packet PROVE-T14-ASSEMBLE7. `Wire.theorem14Statement_assembled7` concludes the unchanged `Wire.Theorem14Statement`
from exactly the still-open named statements, each in its newest landed form; every closed input is discharged by its
landed proof:

* **Theorems 1.2–1.3** and the two Aux. 61 fibre covers: `Sec5.Aux61Cpt.theorem12Statement_of_cptCover`,
  `theorem13Statement_of_cptCover`, `cptFibreCover`, `cptFibreCover₀` (R48 allows them for Theorem 1.4);
* **SB2(1)** (`ψ ≤ π/2`, decision D22): `Lv.sb2UpperLaunchEntryLAmbLeStatement_of_remainderLife` with E7 from
  PROVE-T14-SB2WORD's `Wf.sb2RemainderLifeStatement` (`Zt.sb2RemainderLifeLeStatement_of_vh`);
* **SB3** by `LuM.sb3InductionGenRStatement_of_sb2Le`; the free real point by
  `Lk.lowerWalkLeftFreeStatement_of_thm12_thm13`; **GW4** by `GW4Fix.gw4ComponentRepAStatement`; **SB4** from SB2(2)'s
  combined target by `theorem14Statement_of_sb2Lift_freeLe`;
* **GW2**: COVER's scaled cover with SDE's gap family `GW2Sdq.gapFam` (its measurability
  `GW2Sdq.measurable_gapFam`), J32 as the construction (`RootJ32.rootGeometryAStatement_withScaledCover`), the root
  tests by `GW2Sdy.gw2RootTestStatement_of_scaledCover_A_lossyS`; the near half of ROOTX's package inputs gives the
  near binder (`retainedNearModelsLossy_rootx`, which does not read the slow fields);
* **SB2(2)'s combined target** from its one-walk erasure identity by `Lk.sb2LowerLaunchLiftStatement_of_liftEx`.

The open inputs of `theorem14Statement_assembled7` (the handoff keeps their owners and status):

* `hpos` — the gap's positivity on the cover event (PROVE-GW2-SDE, (N3));
* `ver`, `ch`, `Kb`, `V`, `hs`, `hI`, `hnear`, `hwords`, `hnearImg` — the near half of `GW2Rv.RootPairInputsX`
  (same-slots form);
* `hSlow` — GW2's lossy slow comparisons for J32 on the scaled cover (`GW2Sdx.RetainedSlowComparisonsLossyStatement`;
  its landed reduction needs the refuted `shell` clause, decision D30);
* `hTL` — SB2(2)'s erasure identity for one relative walk (`SB.Lk.SB2LowerTailLiftExStatement`).

`theorem14Statement_assembled7_of_family` is the coarse form for any construction family with the D2 geometry on the
scaled cover (for successors of J32, decision D30).

All results are conditional helpers; no frozen declaration changes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14Asm7

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24

/-! ### The closed inputs -/

/-- **Theorem 1.2** (universe `u`), proved. -/
theorem h12 : Exist.Theorem12Statement.{u} := Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u}

/-- **Theorem 1.3** (universe `u`), proved. -/
theorem h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}

/-- **Theorem 1.2** (universe `0`), proved. -/
theorem h12₀ : Exist.Theorem12Statement.{0} := Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0}

/-- **Theorem 1.3** (universe `0`), proved. -/
theorem h13₀ : Exist.Theorem13Statement.{0} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}

/-- **E7 for `ψ ≤ π/2`**, proved (PROVE-T14-SB2WORD's `Wf.sb2RemainderLifeStatement`). -/
theorem hE7 : SB.Vh.SB2RemainderLifeLeStatement.{u} :=
  SB.Zt.sb2RemainderLifeLeStatement_of_vh SB.Wf.sb2RemainderLifeStatement

/-- **SB2(1) in GW1's ambient setting, `ψ ≤ π/2`**, proved. -/
theorem hSB2 : SB.Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  SB.Lv.sb2UpperLaunchEntryLAmbLeStatement_of_remainderLife h12 h13 h12₀ h13₀ hE7

/-- **SB3's induction statement (bounded angles)**, proved. -/
theorem hSB3 : SB.Ly.SB3InductionGenRLeStatement.{u} :=
  SB.LuM.sb3InductionGenRStatement_of_sb2Le hSB2 h12 h13 h12₀ h13₀ Sec5.Aux61Cpt.cptFibreCover.{u}
    Sec5.Aux61Cpt.cptFibreCover₀

/-! ### GW2's near binder from the root-`x` package inputs (no shell) -/

open GW2Sde GW2Sdh GW2Sdi GW2Sdx GW2Sdz GW2Rv in
/-- **GW2's lossy near models for J32 on the scaled cover from the root-`x` package inputs**: the near half of
`GW2Rv.retainedComparisonsLossy_rootx` (SDE's `GW2Sdz.retainedComparisonsLossyXCS_vpkg`), which reads only the
instance inputs `hI`, the near stops `hnear`, the words `hwords` and the lossy near facts `hnearImg` (of any package `V`
with the package's slots, as in `GW2Rv.vPairInputsXCS_of_sameSlots`) — not the slow fields (`driverId`,
`stopExhausts`, `shell`). -/
theorem retainedNearModelsLossy_rootx {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}
    {Kb : ℕ → PkgFamily.{u}} {gap : RootCv.GapFamily.{u}} {V : ℕ → VPkgXFamily.{u}}
    (hs : ∀ k : ℕ, SameSlots (pkgX h13 ver ch (Kb k)) (V k)) (hI : InstInputsX h13 ver ch)
    (hnear : ∀ k : ℕ, NearStopsX h13 ver ch (Kb k)) (hwords : ∀ k : ℕ, VWordsX (J32S gap) (V k) nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      VNearImgOn ((V k).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l)) :
    RetainedNearModelsLossyStatement (J32S gap) := by
  have hsde : ∀ k, RetainedStoppedSDEStatementN (J32S gap) (comparisonFamilyN (((V k).at 0).frameN nearLam))
      fun n => comparisonFamilyN (((V k).at n).frameN nearLam) :=
    fun k => retainedStoppedSDEStatementN_vpkgX
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ h13 (V k) nearLam
      nearLam_ne (aliveOrdered_scaled gap) (vpkgXSafe_of_sameSlots (vpkgXSafe_pkgX hI (hnear k)) (hs k))
      (hwords k)
  refine retainedNearModelsLossy_of_nearSDE (J32S gap)
    (fun k => comparisonFamilyN (((V k).at 0).frameN nearLam)) (fun k => (hsde k).near) ?_
  intro Ω _ _ c r l k
  filter_upwards [(hsde k).near Ω c r l,
    nearImgPathLossy_on ((V k).at 0) nearLam Ω c r l (nearLam_ne Ω c r l) (hnearImg k Ω c r l)]
    with ω hs hi halive n
  filter_upwards [hs halive n, hi halive n] with m h1 h2
  exact nearBufferFactLossy_of_imgPath h1 (RootJ32.experiment_reach_measurable c r l _) h2

/-! ### ROOTX's drift successor fed by the root-`x` package (same-slots form) -/

open GW2Sde GW2Sdh GW2Sdi GW2Sdx GW2Sdy GW2Sdz GW2Rv GW2Rt in
/-- **`GW2Rt.VPairInputsXCSD` for any package with the slots of the package at every root** (the drift-family
successor of `GW2Rv.vPairInputsXCS_of_sameSlots`): `lam_ne`, `safe`, `driverId`, `stopExhausts` are discharged;
`words`, `nearImg` and `shell` (against the drift family `C`) are the owners' fields. -/
theorem vPairInputsXCSD_of_sameSlots {ver : SchedVerXFamily.{u}} {ch : SchedChoiceFamily.{u}}
    {Kb : ℕ → PkgFamily.{u}} {gap : RootCv.GapFamily.{u}} {V : ℕ → VPkgXFamily.{u}} {C : DriftFamily.{u}}
    (hs : ∀ k : ℕ, SameSlots (pkgX h13 ver ch (Kb k)) (V k)) (hI : InstInputsX h13 ver ch)
    (hnear : ∀ k : ℕ, NearStopsX h13 ver ch (Kb k)) (hwords : ∀ k : ℕ, VWordsX (J32S gap) (V k) nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      VNearImgOn ((V k).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l))
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ ((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l →
          ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    VPairInputsXCSD V nearLam gap C where
  lam_ne := nearLam_ne
  safe k := vpkgXSafe_of_sameSlots (vpkgXSafe_pkgX hI (hnear k)) (hs k)
  words := hwords
  nearImg := hnearImg
  driverId _ _ _ c r _ l _ a n := vDriverIdN_of_sameSlots (vDriverIdN_pkgX (Kb 0) c r l a n) (hs 0)
  stopExhausts _ _ _ c r _ l _ a := vStopExhaustsN_of_sameSlots (vStopExhaustsN_pkgX (Kb 0) c r l a) (hs 0)
  shell := hshell

/-! ### The tops -/

/-- **Theorem 1.4 from GW2's root tests and SB2(2)'s combined target** (everything else proved). -/
theorem theorem14Statement_of_rootTests (hTests : GW2RootTestStatement.{u})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift_freeLe h12 h13 h12₀ h13₀ hTests hSB3 hC
    (SB.Lk.lowerWalkLeftFreeStatement_of_thm12_thm13 h12 h13 h12₀ h13₀) (GW4Fix.gw4ComponentRepAStatement h12 h13)

/-- **GW2's root tests on COVER's scaled cover with SDE's gap family**, for any construction family with the D2
geometry (`GW2Sdy.gw2RootTestStatement_of_scaledCover_A_lossyS` with `gap := GW2Sdq.gapFam`). -/
theorem gw2RootTestStatement_of_family (D : ConstructionFamily.{u})
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover D GW2Sdq.gapFam))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D GW2Sdq.gapFam))
    (hSlow : GW2Sdx.RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover D GW2Sdq.gapFam)) :
    GW2RootTestStatement.{u} :=
  GW2Sdy.gw2RootTestStatement_of_scaledCover_A_lossyS h13 h13₀ D GW2Sdq.gapFam GW2Sdq.measurable_gapFam hpos
    hGeometry hNear hSlow

/-- **Theorem 1.4 for any construction family with the D2 geometry on the scaled cover** (open: the gap's
positivity, the family's two lossy comparison binders, SB2(2)'s erasure identity for one relative walk). -/
theorem theorem14Statement_assembled7_of_family (D : ConstructionFamily.{u})
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover D GW2Sdq.gapFam))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D GW2Sdq.gapFam))
    (hSlow : GW2Sdx.RetainedSlowComparisonsLossyStatement (RootCv.withScaledCover D GW2Sdq.gapFam))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_of_rootTests (gw2RootTestStatement_of_family D hpos hGeometry hNear hSlow)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_liftEx h12 h13 h12₀ h13₀ hTL)

/-- **GW2's root tests for J32 with a drift family on the scaled cover** (decision D30: `GW2Rt.withDrift`), from
ROOTX's successor pair inputs `GW2Rt.VPairInputsXCSD`. -/
theorem gw2RootTestStatement_drift
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω)
    (C : GW2Rt.DriftFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hV : GW2Rt.VPairInputsXCSD V GW2Sdh.nearLam GW2Sdq.gapFam C) : GW2RootTestStatement.{u} :=
  have h := GW2Rt.retainedComparisonsLossyXCSD_vpkg
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ h13 V GW2Sdh.nearLam GW2Sdq.gapFam C hV
  gw2RootTestStatement_of_family (GW2Rt.withDrift RootJ32.constructionFamily C) hpos
    (GW2Rt.rootGeometryAStatement_withDrift (RootJ32.rootGeometryAStatement_withScaledCover h13 GW2Sdq.gapFam) C)
    h.1 h.2

/-- **GW2's root tests for J32 with a drift family, from the owners' fields** (RELDET's instance inputs
`GW2Rd.instInputsX_of_linesX` on the choice family `GW2Rd.schedChoiceLinesX` of a base family; BUF's near stops; SDE's
words; BUF's lossy near facts; the shells against `C`). -/
theorem gw2RootTestStatement_fields
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω)
    {ver : GW2Rv.SchedVerXFamily.{u}} {base : GW2Sdh.SchedChoiceFamily.{u}}
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hmean : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l →
      (h : GW2Rv.GoodRoot c r) → ∀ a n : ℕ,
        GW2Rd.OpenLinesMeanX (GW2Rv.instX h13 ver (GW2Rd.schedChoiceLinesX h12 h13 base) Ω c r l a n h.1) c r l
          (rootPt r.1))
    {Kb : ℕ → GW2Sde.PkgFamily.{u}} {V : ℕ → GW2Sdx.VPkgXFamily.{u}}
    (hs : ∀ k : ℕ, GW2Rv.SameSlots (GW2Rv.pkgX h13 ver (GW2Rd.schedChoiceLinesX h12 h13 base) (Kb k)) (V k))
    (hnear : ∀ k : ℕ, GW2Rv.NearStopsX h13 ver (GW2Rd.schedChoiceLinesX h12 h13 base) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).G r) l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).experiment r).data.alive
            ((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).G r) l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_drift hpos C V
    (vPairInputsXCSD_of_sameSlots hs (GW2Rd.instInputsX_of_linesX hword hE₀ hmean) hnear hwords hnearImg hshell)

end InteractingSLE.Wire.T14Asm7

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24

/-- **Theorem 1.4, re-assembled (PROVE-T14-ASSEMBLE7)**: J32 with a drift family (decision D30) on COVER's scaled
cover with SDE's gap family `GW2Sdq.gapFam`. The hypotheses are exactly the still-open named statements in their
newest landed forms (data: the version family `ver`, the base choice family `base`, the package families `Kb`, `V`,
the drift family `C`):

* `hpos` — the gap's positivity on the cover event (SDE, (N3));
* `hword`, `hE₀` — the base choice family's word map and record event; `hmean` — STAGEMEAN's part of the open
  lines inputs (`GW2Rd.OpenLinesMeanX`) on every root-`x` instance (RELDET's `GW2Rd.instInputsX_of_linesX` does
  the rest);
* `hs` — `V` has the package's slots (by `rfl` for the package itself or SDE's `withNearS` selection);
* `hnear` — BUF's near stops (`GW2Bh.nearStopsX_nearStopPkgX` for BUF's package);
* `hwords` — SDE's near and slow words; `hnearImg` — BUF's lossy near facts;
* `hshell` — the slow shells against the drift family `C` (decision D30/D33; ROOTX);
* `hTL` — SB2(2)'s erasure identity for one relative walk (`SB.Lk.SB2LowerTailLiftExStatement`).

Theorems 1.2–1.3, the fibre covers, SB2(1) (with E7), SB3, the free real point, SB4, GW4, GW2's cover, the gap's
measurability, J32's geometry (with any drift family), RELDET's `u₀` and marks, the version drivers and stop
exhaustion are discharged by their landed proofs. -/
theorem theorem14Statement_assembled7
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < GW2Sdq.gapFam Ω c x ω)
    (ver : GW2Rv.SchedVerXFamily.{u}) (base : GW2Sdh.SchedChoiceFamily.{u})
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, Measurable (base Ω c r l a).β ∧
        (Set.range fun y => Supp8.Q3Stop.wordType c.κ ((base Ω c r l a).β y)).Countable ∧
        ∀ y, ((base Ω c r l a).β y).IsSorted)
    (hE₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → GW2Rv.GoodRoot c r →
      ∀ a : ℕ, MeasurableSet (base Ω c r l a).E₀)
    (hmean : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l →
      (h : GW2Rv.GoodRoot c r) → ∀ a n : ℕ,
        GW2Rd.OpenLinesMeanX
          (GW2Rv.instX T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX T14Asm7.h12 T14Asm7.h13 base) Ω c r l a n h.1) c r l
          (rootPt r.1))
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (V : ℕ → GW2Sdx.VPkgXFamily.{u})
    (hs : ∀ k : ℕ,
      GW2Rv.SameSlots (GW2Rv.pkgX T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX T14Asm7.h12 T14Asm7.h13 base) (Kb k))
        (V k))
    (hnear : ∀ k : ℕ,
      GW2Rv.NearStopsX T14Asm7.h13 ver (GW2Rd.schedChoiceLinesX T14Asm7.h12 T14Asm7.h13 base) (Kb k))
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (V k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((V k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).experiment r).data.alive
          ((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).G r) l))
    (C : GW2Rt.DriftFamily.{u})
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).experiment r).data.alive
            ((GW2Sdz.J32S.{u} GW2Sdq.gapFam Ω c).G r) l →
          GW2Sdy.ShellFactLe c.κ (C Ω c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω)
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  T14Asm7.theorem14Statement_of_rootTests
    (T14Asm7.gw2RootTestStatement_fields hpos hword hE₀ hmean hs hnear hwords hnearImg C hshell)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_liftEx T14Asm7.h12 T14Asm7.h13 T14Asm7.h12₀ T14Asm7.h13₀ hTL)

end InteractingSLE.Wire
