/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NtTop
import InteractingSLE.Spec.Wire.T14CurTop

/-!
# GW2's `noThreshold`: the `hno` binder of Theorem 1.4's current top from D38's export

Packet PROVE-GW2-NOTHR (round 2, decisions D36 and D38). Theorem 1.4's current top
(`Wire.theorem14Statement_assembled7G`, `…7Wm`; PROVE-T14-ASSEMBLE7) takes the threshold field as the binder `hno`:
`GW2Rz.NoThresholdX` of every root-`x` instance `T14Cur.instC ver base` (the field `noThreshold` of the `hmean`
binder `GW2Rd.OpenLinesMeanX` of `Wire.theorem14Statement_assembled7`). Route (M) proves it from D38's export
(`GW2Nt.StageKernelExportX`, PROVE-GW2-STAGEMEAN's stage-start identity at the launch kernel):

* **`hno_of_export`**: the binder `hno` for any version family and any base choice family with a measurable word map
  of countably many types and a measurable record event (`hword`, `hE₀` of the top);
* **`hno_baseWm_of_export`**: the same for GEOM2's word-map family `T14Cur.baseWm cw` (its `hword`, `hE₀` are proved);
* **`Wire.theorem14Statement_assembled7Wm_export`**: the current top with `hno` replaced by the export.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Nt

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rv GW2Sdh Wire.T14Cur

/-- **D38's export at every root-`x` instance of a version family and a base choice family.** -/
def ExportFamily (ver : SchedVerXFamily.{u}) (base : SchedChoiceFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) → ∀ a n : ℕ,
      StageKernelExportX c r l a (instC ver base Ω c r l a n h) (rootPt r.1)

/-- **The binder `hno` of Theorem 1.4's current top from D38's export** (any version family, any base family with
the top's `hword` and `hE₀`). -/
theorem hno_of_export {ver : SchedVerXFamily.{u}} {base : SchedChoiceFamily.{u}}
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
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) →
      ∀ a n : ℕ, NoThresholdX (instC ver base Ω c r l a n h) c r l (rootPt r.1) := by
  intro Ω _ _ c r l hTO h a n
  have hβ := hword Ω c r l hTO h a
  have hE := hE₀ Ω c r l hTO h a
  rw [← GW2Rd.schedChoiceLinesX_β Wire.T14Asm7.h12 Wire.T14Asm7.h13 base c r l a] at hβ
  rw [← GW2Rd.schedChoiceLinesX_E₀ Wire.T14Asm7.h12 Wire.T14Asm7.h13 base c r l a] at hE
  exact noThresholdX_of_export Wire.T14Asm7.h13 c r l a h.1 h.2 hTO (schedGTX_spec Wire.T14Asm7.h13 c r l a)
    ((ver Ω c r l a).isA h.1 n) ((ver Ω c r l a).fin n) (chL base Ω c r l a) hβ hE (hexp Ω c r l hTO h a n)

/-- **`hno` for GEOM2's word-map family** `T14Cur.baseWm cw` from D38's export. -/
theorem hno_baseWm_of_export {ver : SchedVerXFamily.{u}} (cw : CfWord.{u}) (hexp : ExportFamily ver (baseWm cw)) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
      (l : List (EntryIdx c.Θ c.Q)), GW2Sdx.HistOrdered c r l → (h : GoodRoot c r) →
      ∀ a n : ℕ, NoThresholdX (instC ver (baseWm cw) Ω c r l a n h) c r l (rootPt r.1) :=
  hno_of_export (hword_baseWm cw) (hE₀_baseWm cw) hexp

end InteractingSLE.Theorem14.GW2Nt

namespace InteractingSLE.Wire

open Theorem14 Theorem14.GW2TipSystem Theorem14.GW2TipSystem.Gm Theorem14.GW2TipSystem.RootC24 T14Cur

/-- **Theorem 1.4, current top with GEOM2's word-map base family, the threshold field from D38's export**: the
binder `hno` of `Wire.theorem14Statement_assembled7Wm` is replaced by `GW2Nt.ExportFamily ver (baseWm cw)`
(PROVE-GW2-STAGEMEAN's stage-start identity at the launch kernel), through `GW2Nt.hno_baseWm_of_export`. -/
theorem theorem14Statement_assembled7Wm_export (gap : RootCv.GapFamily.{u})
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
    (hexp : GW2Nt.ExportFamily ver (baseWm cw))
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
  Wire.theorem14Statement_assembled7G gap hgap hpos ver (baseWm cw) (hword_baseWm cw) (hE₀_baseWm cw) (hbd_baseWm cw)
    hmeanF (GW2Nt.hno_baseWm_of_export cw hexp) Kb V hs hnear hwords hnearImg C hshell hTL

end InteractingSLE.Wire
