/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvPkg
import InteractingSLE.Spec.Supplement.GW2BnShape
import InteractingSLE.Spec.Supplement.GW2BnBridge
import InteractingSLE.Spec.Supplement.GW2BqRead
import InteractingSLE.Spec.Supplement.GW2SdsCw

/-!
# The near stop's exit rules

Packet PROVE-GW2-BUF (round 19; the instance layer). The near stop of slot `(l, n, m, a)` exits the near cell of
level `n` (round 14's `cellStop (cellOf n …)`, with the cap `(n + 1)/A` of D35). It is read off the stage record `y`
through GEOM2's base word `wordD y` (`GW2Wm.baseWordX` with SDE's counterflow word `cfWordSrc`):

* `lamL l`: the near dilation (`nearLam`, a function of the history only); `scL r l` the near scale and
  `c2L r l = 2^k λ`, with `√scale = c₂⁻¹` (**`sqrt_scL`**);
* `wordD c r l`, `shapeD` (the lower shape `nearShapeBot` of the dilated word), `posLD`, `posRD` (its padded
  flow-line positions): **`measurable_wordD`**, `measurable_shapeD`, `measurable_posLD`, `measurable_posRD`;
* **`exitB`**: the exit rule family (independent of the candidate), **`exitB_spec`** (measurable path rules, the
  `hE` of `nearStopsX_pkgKb`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootH10 GW2Rz GW2Rd GW2Rv GW2Sde
  GW2Sdh GW2Sdx GW2Sdy

/-- The near dilation of a history (`nearLam`, which reads only the history's length). -/
def lamL {Θ : Set ℝ} {Q : Set ℝ≥0} (l : List (EntryIdx Θ Q)) : ℝ≥0 := if l.length = 0 then 1 else 17 / 35

theorem nearLam_eq_lamL (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) : nearLam Ω c r l ω = lamL l := rfl

theorem lamL_pos {Θ : Set ℝ} {Q : Set ℝ≥0} (l : List (EntryIdx Θ Q)) : 0 < lamL l := by
  unfold lamL
  split_ifs <;> norm_num

/-- The near scale of a history. -/
def scL {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) : ℝ≥0 :=
  nearRootScale r.2 (lamL l)

/-- The near frame's factor `2^k λ`. -/
def c2L {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) : ℝ≥0 := 2 ^ r.2 * lamL l

theorem c2L_pos {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) : 0 < c2L r l :=
  mul_pos (pow_pos (by norm_num) _) (lamL_pos l)

theorem sqrt_scL {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) :
    Real.sqrt (scL r l) = ((c2L r l : ℝ))⁻¹ := by
  have h4 : ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2 : ℝ≥0) = (c2L r l) ^ 2 := by
    unfold c2L
    rw [mul_pow, ← pow_mul, mul_comm r.2 2, pow_mul]
    norm_num
  unfold scL nearRootScale
  rw [h4, NNReal.coe_inv, NNReal.coe_pow, Real.sqrt_inv]
  congr 1
  exact Real.sqrt_sq (c2L r l).2

section Dec

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- **GEOM2's base word of a stage record** (with SDE's counterflow word). -/
def wordD (y : RecData) : BoundaryWord :=
  GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
    ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l) y

/-- The lower shape of the dilated base word of a record. -/
def shapeD (y : RecData) : NearShape := nearShapeBot (scL r l) (GW2Sdf.flipOf l.length) (wordD c r l y)

/-- The padded left positions of the dilated base word of a record. -/
def posLD (y : RecData) : ℕ → ℝ := padXL (nearDilWord (scL r l) (GW2Sdf.flipOf l.length) (wordD c r l y))

/-- The padded right positions of the dilated base word of a record. -/
def posRD (y : RecData) : ℕ → ℝ := padXR (nearDilWord (scL r l) (GW2Sdf.flipOf l.length) (wordD c r l y))

theorem measurable_wordD : Measurable (wordD c r l) :=
  (GW2JDetR5.measurable_stageWord (GW2Wm.measurable_rootWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s)
    (GW2Wm.progAngle (RootJ31.historyProgram c r l)) ((entryList l).length + 1)).comp
    (GW2Wm.measurable_stageDec (rootPt r.1) c.s (RootJ31.historyProgram c r l) ((entryList l).length + 1)
      (GW2Ru.length_historyProgram c r l))

theorem measurable_nearShapeBot (s : ℝ≥0) (flip : Bool) : Measurable (nearShapeBot s flip) := by
  have hd := measurable_nearDilWord_at s flip
  have hNL : Measurable fun c : BoundaryWord =>
      flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 :=
    FCDet.measurable_flowLineNL_zero.comp hd
  have hNR : Measurable fun c : BoundaryWord =>
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 :=
    FCDet.measurable_flowLineNR_zero.comp hd
  have hsub : Measurable fun c : BoundaryWord =>
      flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1 :=
    (measurable_from_nat (f := fun n : ℕ => n - 1)).comp hNL
  have hcut : Measurable fun c : BoundaryWord => GW2Sdo.cutR (nearDilWord s flip c) := by
    have : (fun c : BoundaryWord => GW2Sdo.cutR (nearDilWord s flip c)) =
        fun c => cutCountR (nearDilWord s flip c) := funext fun c => cutR_eq_cutCountR _
    rw [this]
    exact measurable_cutCountR.comp hd
  exact hNL.prodMk (hNR.prodMk (hsub.prodMk (hcut.prodMk measurable_const)))

theorem measurable_shapeD : Measurable (shapeD c r l) :=
  (measurable_nearShapeBot _ _).comp (measurable_wordD c r l)

theorem measurable_posLD : Measurable (posLD c r l) := (measurable_nearPos_comp (measurable_wordD c r l) _ _).1

theorem measurable_posRD : Measurable (posRD c r l) := (measurable_nearPos_comp (measurable_wordD c r l) _ _).2

end Dec

/-- **The exit rule family of the near stops**: at history `l` and level `n`, the exit of the near cell read off the
record, in the near frame `A = c₂²`, `B = ± c₂`, with the cap `(n + 1)/A`. -/
def exitB : ExitFam.{u} := fun _ _ _ c r l n _ =>
  cellStop (cellOf n (shapeD c r l) (posLD c r l) (posRD c r l)) (posLD c r l) (posRD c r l) (c2L r l ^ 2)
    (nearSign (GW2Sdf.flipOf l.length) * c2L r l) (((n : ℝ≥0) + 1) / c2L r l ^ 2)

/-- **The exit rules are measurable path rules.** -/
theorem exitB_spec (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n a : ℕ) :
    Supp8.GB6.HullId.IsPathRule (exitB.{u} Ω c r l n a) ∧ Measurable (exitB.{u} Ω c r l n a) :=
  ⟨isPathRule_cellStop _ _ _ (pow_pos (c2L_pos r l) 2) _ _,
    measurable_cellStop (measurable_cellOf n (measurable_shapeD c r l) (measurable_posLD c r l)
      (measurable_posRD c r l)) (measurable_posLD c r l) (measurable_posRD c r l) _ _ _⟩

end InteractingSLE.Theorem14.GW2Bh
