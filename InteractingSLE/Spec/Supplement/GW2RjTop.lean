/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RjFact
import InteractingSLE.Spec.Wire.T14CurTop

/-!
# The current top with D33's slow shell: `hshell` discharged (decision D33)

PROVE-GW2-ROOTX round 9. The top `Wire.theorem14Statement_assembled7Wm` takes any package `V` with the slots of
ROOTX's package, a drift family `C` and the shell field `hshell` for `V 0`. Here:

* `withShell V sh`: the package `V` with the slow shells `sh` (same slots, `sameSlots_withShell`);
* **`pkgRj ver cw Kb nb kSel k`**: SDE's pinned package `T14Cur.pkgS ver (baseWm cw) Kb nb kSel k` with D33's shells
  `GW2Rj.rjShell` (the optimal shell of the slow record's raised stage word);
* **`hshell_pkgRj`**: the shell field for `pkgRj` against the drift family `Cstar κ (cw Ω c r) x s` (from
  `GW2Rj.rjShell_fact_scaled`, the instance inputs `GW2Rd.instInputsX_of_linesX_mean` of the top's own fields);
* **`Wire.theorem14Statement_assembled7Wm_rj`**: the top with `V := pkgRj …`, `hs`, `C`, `hshell` discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire.T14Rj

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur

/-- **A package with replaced slow shells** (same slots). -/
def withShell (V : GW2Sdx.VPkgXFamily.{u})
    (sh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
      List (EntryIdx c.Θ c.Q) → ℕ → Ω → GW2Sde.SlowShell) : GW2Sdx.VPkgXFamily.{u} :=
  fun Ω _ _ c r => { V Ω c r with slowShell := sh Ω c r }

theorem sameSlots_withShell (V : GW2Sdx.VPkgXFamily.{u})
    (sh : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
      List (EntryIdx c.Θ c.Q) → ℕ → Ω → GW2Sde.SlowShell) : GW2Rv.SameSlots V (withShell V sh) :=
  fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-- **D33's slow shells** for the top's version family and counterflow word. -/
abbrev rjShells (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (_r : ScaledRootIdx c.Θ c.Q),
      List (EntryIdx c.Θ c.Q) → ℕ → Ω → GW2Sde.SlowShell :=
  fun _ _ _ c r => GW2Rj.rjShell T14Asm7.h13 ver (cw _ c r) c r

/-- **SDE's pinned package with D33's slow shells.** -/
abbrev pkgRj (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u}) (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u})
    (kSel : NearSel.{u}) (k : ℕ) : GW2Sdx.VPkgXFamily.{u} :=
  withShell (pkgS ver (baseWm cw) Kb nb kSel k) (rjShells ver cw)

/-- **D33's drift family**: the constant `C*` of the root word's shape. -/
abbrev rjDrift (cw : CfWord.{u}) : GW2Rt.DriftFamily.{u} :=
  fun _ _ _ c r => GW2Rq.Cstar c.κ (cw _ c r) (rootPt r.1) c.s

theorem hβ_baseWm (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (chL (baseWm cw) Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r) (rootPt r.1) c.s
      (RootJ31.historyProgram c r l) ((entryList l).length + 1) (GW2Rd.length_historyProgram c r l)
      (GW2Rd.candAngle c r l a) := by
  rw [GW2Rd.schedChoiceLinesX_β]
  rfl

theorem hE₀eq_baseWm (cw : CfWord.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    (chL (baseWm cw) Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ := by
  rw [GW2Rd.schedChoiceLinesX_E₀]
  rfl

/-- **The shell field of `pkgRj`** against D33's drift family (from the top's own instance fields). -/
theorem hshell_pkgRj (gap : RootCv.GapFamily.{u}) (ver : GW2Rv.SchedVerXFamily.{u}) (cw : CfWord.{u})
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
    (Kb : ℕ → GW2Sde.PkgFamily.{u}) (nb : NearBase.{u}) (kSel : NearSel.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ aliveS gap Ω c r l →
          GW2Sdy.ShellFactLe c.κ (rjDrift cw Ω c r) ((pkgRj ver cw Kb nb kSel 0 Ω c r).slowShell l a ω) ∧
            ((pkgRj ver cw Kb nb kSel 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω := by
  intro Ω _ _ c r k l hl a
  have hI := GW2Rd.instInputsX_of_linesX_mean (hword_baseWm cw) (hE₀_baseWm cw) (hbd_baseWm cw) hmeanF hno
  exact GW2Rj.rjShell_fact_scaled (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12 T14Asm7.h13)
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 T14Asm7.h12₀ T14Asm7.h13₀) T14Asm7.h13₀ hI cw
    (hβ_baseWm cw) (hE₀eq_baseWm cw) gap Ω c r k l hl a

end InteractingSLE.Wire.T14Rj

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur T14Rj

/-- **Theorem 1.4, current top with D33's slow shell**: `Wire.theorem14Statement_assembled7Wm` with the package
`pkgRj` (SDE's pinned package with the optimal shells of the slow records), the drift family `Cstar`, its slots and
its shell field PROVED. -/
theorem theorem14Statement_assembled7Wm_rj (gap : RootCv.GapFamily.{u})
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
    (hwords : ∀ k : ℕ, GW2Sdx.VWordsX (GW2Sdz.J32S.{u} gap) (pkgRj ver cw Kb nb kSel k) GW2Sdh.nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      GW2Sdz.VNearImgOn ((pkgRj ver cw Kb nb kSel k).at 0) GW2Sdh.nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (aliveS gap Ω c r l))
    (hTL : SB.Lk.SB2LowerTailLiftExStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_assembled7Wm gap hgap hpos ver cw hmeanF hno Kb (pkgRj ver cw Kb nb kSel)
    (fun _ _ _ _ _ _ => ⟨rfl, rfl⟩) hnear hwords hnearImg (rjDrift cw)
    (hshell_pkgRj gap ver cw hmeanF hno Kb nb kSel) hTL

end InteractingSLE.Wire
