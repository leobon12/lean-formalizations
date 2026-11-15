import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.couplingMean
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import InteractingSLE.Frozen.Spec.usualAugmentation
import InteractingSLE.Frozen.Spec.IsRightForceImage
import InteractingSLE.Frozen.Spec.IsLeftForceImage
import InteractingSLE.Frozen.Spec.continuationThreshold
import InteractingSLE.Frozen.Spec.IsContLocalMartingaleBefore
import InteractingSLE.Frozen.Spec.IsConformalRadius
import InteractingSLE.Spec.Sec2.MartingaleFinalImage
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Spec.Sec2.MartingaleExtract
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Complex.RiemannMap
import InteractingSLE.Spec.Restart.ConverseBefore

/-!
# Certification of the frozen Theorem 2.4 / 2.6 definitions

Characterization lemmas for the five definition anchors of Theorems 2.4 and 2.6 (Specification §2.3, pp. 34–40;
ruling R109): `IsRightForceImage`, `IsLeftForceImage`, `continuationThreshold`, `IsContLocalMartingaleBefore` and
`IsConformalRadius` (`InteractingSLE/Frozen/Spec/`). The frozen docstrings cite this module. These are the
certification lemmas of the audited candidate `T2426-v2` (audits `planning/audits/AUD-T2426A-v2.md`,
`planning/audits/AUD-T2426C.md`), landed with the frozen definitions imported instead of copied (packet
PROVE-FREEZE-T2426). Sections:

* **A, force-point images**: reality, positivity (intermediate value theorem), uniqueness and the sign at time
  `0` of real solutions of (1.7); the adapters `isRightForceImage_iff` / `isLeftForceImage_iff` to the landed
  `MartChar.RealFlow.rightImg` (with nonemptiness and the lower bound before translating the infimum); existence and
  uniqueness on the source carrier; the source characterizations: time `0`, the unswallowed value `g_t(x)`, and the
  extreme-endpoint value (right/left limit of `g_t` at the end of the swallowed real set).
* **B, local martingales before `ζ`**: invariance under changes at and after `ζ` (exact,
  `isContLocalMartingaleBefore_congr`) and under almost-sure changes before `ζ` when `𝓕 0` contains the null sets
  (`isContLocalMartingaleBefore_congr_ae`, every usual augmentation); continuous martingales are included; the bridge to
  the landed `MartChar.IsLocalMartingaleBefore`.
* **C, conformal radius**: the relation is functional (Schwarz lemma), positive, `crad(ℍ, z) = 2 Im z`,
  existence on `ℍ ∖ K_t` through the Loewner map with value `2 Im f_t(z)/|f_t'(z)|`, the component containing `z` is
  `ℍ ∖ K_t`, the bracket hypothesis of Theorem 2.6 is equivalent to its explicit Loewner form, and a bracket process
  exists (`exists_log_conformalRadius_process`).
* **D**: the force-point binders of the theorems are satisfiable (measurable versions exist).
* **Plumbing**: Theorem 2.4's converse from the landed `Restart.ConverseBefore.isRandomWordEvolution_prod` under
  named bridges (a conditional lemma with a distinct name; it is not a proof of the frozen theorem).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-! ## Certification A: the force-point images (audit AUD-T2426B F2) -/

namespace Certify2426

open MartChar.RealFlow

section RealSol

variable {W : ℝ → ℝ}

/-- A solution of the centred flow from a real point is real. -/
lemma eq_ofReal_re_of_isForwardSol (hW : Continuous W) {y T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W (y : ℂ) T u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    u s = ((u s).re : ℂ) :=
  Complex.ext (by simp) (by simp [im_eq_zero_of_isForwardSol_real hW hu hs])

lemma integral_two_div_eq (hW : Continuous W) {y T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W (y : ℂ) T u) {s : ℝ} (hs : s ∈ Icc 0 T) :
    (∫ r in (0 : ℝ)..s, 2 / u r) = ((∫ r in (0 : ℝ)..s, 2 / (u r).re : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  have h := eq_ofReal_re_of_isForwardSol hW hu ⟨hr.1, hr.2.trans hs.2⟩
  show 2 / u r = ((2 / (u r).re : ℝ) : ℂ)
  conv_lhs => rw [h]
  push_cast
  rfl

/-- **Positivity, reality and the intermediate value step**: a solution of the centred flow (1.7) from a real point
`y` to the right of `W 0` is real and positive, i.e. a positive solution of the real Loewner equation. -/
lemma isPosSol_re_of_isForwardSol (hW : Continuous W) {y T : ℝ} (hy : W 0 < y) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W (y : ℂ) T u) : IsPosSol W y T (fun s => (u s).re) := by
  have hX : ContinuousOn (fun s => (u s).re) (Icc 0 T) := Complex.continuous_re.comp_continuousOn hu.1
  have heq : ∀ s ∈ Icc 0 T, (u s).re = y - W s + ∫ r in (0 : ℝ)..s, 2 / (u r).re := by
    intro s hs
    have h := congrArg Complex.re (hu.2 s hs).2
    rw [integral_two_div_eq hW hu hs] at h
    simpa using h
  have hne : ∀ s ∈ Icc 0 T, (u s).re ≠ 0 := fun s hs h0 =>
    (hu.2 s hs).1 (by rw [eq_ofReal_re_of_isForwardSol hW hu hs, h0, Complex.ofReal_zero])
  refine ⟨hX, fun s hs => ⟨?_, heq s hs⟩⟩
  by_contra hlt
  have hle := not_lt.1 hlt
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hs.1.trans hs.2⟩
  have h0 : 0 < (u 0).re := by
    rw [heq 0 hT, intervalIntegral.integral_same, add_zero]
    linarith
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hs.1 (hX.mono (Icc_subset_Icc le_rfl hs.2))
    ⟨hle, h0.le⟩
  exact hne r ⟨hr.1, hr.2.trans hs.2⟩ hr0

/-- A positive solution of the real Loewner equation is a solution of the centred flow (1.7). -/
lemma isForwardSol_ofReal_of_isPosSol {y T : ℝ} {X : ℝ → ℝ} (hX : IsPosSol W y T X) :
    QuantumZipper.IsForwardSol W (y : ℂ) T (fun s => (X s : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp_continuousOn hX.1, fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.ofReal_ne_zero.2 (hX.2 s hs).1.ne'
  · have h := (hX.2 s hs).2
    have hint : (∫ r in (0 : ℝ)..s, 2 / (X r : ℂ)) = ((∫ r in (0 : ℝ)..s, 2 / X r : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r _ => ?_
      push_cast
      rfl
    rw [hint]
    dsimp only
    conv_lhs => rw [h]
    push_cast
    ring

/-- **Alive points**: for `y > W 0`, the centred flow from `y` exists on `[0, T]` iff `y` is not swallowed by `T` in the
landed real-flow sense (`MartChar.RealFlow.Alive`). -/
lemma exists_isForwardSol_iff_alive (hW : Continuous W) {y T : ℝ} (hy : W 0 < y) :
    (∃ u, QuantumZipper.IsForwardSol W (y : ℂ) T u) ↔ Alive W y T :=
  ⟨fun ⟨_, hu⟩ => ⟨_, isPosSol_re_of_isForwardSol hW hy hu⟩,
    fun ⟨_, hX⟩ => ⟨_, isForwardSol_ofReal_of_isPosSol hX⟩⟩

/-- **Uniqueness**: the (chosen) centred map at an alive real point is the real flow. -/
lemma re_fwdMap_eq_cflow (hW : Continuous W) {y T : ℝ} (hy : W 0 < y) (hT : 0 ≤ T)
    (h : ∃ u, QuantumZipper.IsForwardSol W (y : ℂ) T u) :
    (QuantumZipper.fwdMap W T y).re = cflow W y T := by
  classical
  rw [QuantumZipper.fwdMap, dite_eq_left_of_eq_true (eq_true h)]
  exact (cflow_eq_of_isPosSol hW (isPosSol_re_of_isForwardSol hW hy h.choose_spec)
    ⟨hT, le_rfl⟩).symm

/-- The mirror of a solution of the centred flow solves it for the mirrored driver. -/
lemma isForwardSol_neg {p : ℂ} {T : ℝ} {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W p T u) :
    QuantumZipper.IsForwardSol (fun s => -W s) (-p) T (fun s => -u s) := by
  refine ⟨hu.1.neg, fun s hs => ⟨neg_ne_zero.2 (hu.2 s hs).1, ?_⟩⟩
  have h := (hu.2 s hs).2
  have hint : (∫ r in (0 : ℝ)..s, 2 / -u r) = -∫ r in (0 : ℝ)..s, 2 / u r := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [div_neg]
  rw [hint]
  dsimp only
  conv_lhs => rw [h]
  push_cast
  ring

lemma exists_isForwardSol_neg_iff {y T : ℝ} :
    (∃ u, QuantumZipper.IsForwardSol W (y : ℂ) T u) ↔
      ∃ u, QuantumZipper.IsForwardSol (fun s => -W s) ((-y : ℝ) : ℂ) T u := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨_, by simpa using isForwardSol_neg hu⟩
  · rintro ⟨u, hu⟩
    have h := isForwardSol_neg hu
    simp only [neg_neg, Complex.ofReal_neg] at h
    exact ⟨_, h⟩

/-- The (chosen) centred map at an alive real point left of the driver, through the mirrored real flow. -/
lemma re_fwdMap_eq_neg_cflow (hW : Continuous W) {y T : ℝ} (hy : y < W 0) (hT : 0 ≤ T)
    (h : ∃ u, QuantumZipper.IsForwardSol W (y : ℂ) T u) :
    (QuantumZipper.fwdMap W T y).re = -cflow (fun s => -W s) (-y) T := by
  classical
  have hW' : Continuous fun s => -W s := hW.neg
  have hsol : QuantumZipper.IsForwardSol (fun s => -W s) ((-y : ℝ) : ℂ) T
      (fun s => -h.choose s) := by simpa using isForwardSol_neg h.choose_spec
  have hpos := isPosSol_re_of_isForwardSol hW' (show -W 0 < -y by linarith) hsol
  have hc := cflow_eq_of_isPosSol hW' hpos ⟨hT, le_rfl⟩
  rw [QuantumZipper.fwdMap, dite_eq_left_of_eq_true (eq_true h)]
  rw [hc]
  simp

end RealSol

/-- Translation of an infimum. -/
lemma add_csInf_eq_csInf_image {S : Set ℝ} (hne : S.Nonempty) (hb : BddBelow S) (c : ℝ) :
    c + sInf S = sInf ((fun s => c + s) '' S) := by
  have hb' : BddBelow ((fun s => c + s) '' S) := by
    obtain ⟨m, hm⟩ := hb
    exact ⟨c + m, by rintro _ ⟨s, hs, rfl⟩; have := hm hs; simp only; linarith⟩
  refine le_antisymm (le_csInf (hne.image _) ?_) ?_
  · rintro _ ⟨s, hs, rfl⟩
    have := csInf_le hb hs
    simp only
    linarith
  · have : sInf ((fun s => c + s) '' S) - c ≤ sInf S :=
      le_csInf hne fun s hs => by
        have := csInf_le hb' ⟨s, hs, rfl⟩
        simp only at this
        linarith
    linarith

section Images

variable {w : ℝ≥0 → ℝ}

lemma continuous_path (hw : Continuous w) : Continuous (fun s : ℝ => w s.toNNReal) :=
  hw.comp continuous_real_toNNReal

/-- **Adapter, right**: on the source carrier the formula of `IsRightForceImage` is the landed geometric image
`MartChar.RealFlow.rightImg` (nonemptiness and the lower bound `0` justify moving `w t` through the infimum). -/
theorem add_sInf_rightSet_eq_rightImg (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : 0 ≤ x)
    (t : ℝ≥0) :
    w t + sInf {c : ℝ | ∃ y : ℝ, x < y ∧
      (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u) ∧
      c = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) (t : ℝ) (y : ℂ)).re} =
      rightImg (fun s : ℝ => w s.toNNReal) x t := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := continuous_path hw
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hWt : W t = w t := by simp [hWdef]
  set S := {c : ℝ | ∃ y : ℝ, x < y ∧ (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol W (y : ℂ) (t : ℝ) u) ∧
    c = (QuantumZipper.fwdMap W (t : ℝ) (y : ℂ)).re} with hSdef
  have hset : imgSet W x t = (fun c => w t + c) '' S := by
    ext g
    constructor
    · rintro ⟨y, hxy, hy, rfl⟩
      have hy0 : W 0 < y := by rw [hW0]; linarith
      have hex := (exists_isForwardSol_iff_alive hW hy0).2 hy
      refine ⟨cflow W y t, ⟨y, hxy, hex, (re_fwdMap_eq_cflow hW hy0 t.coe_nonneg hex).symm⟩, ?_⟩
      simp only [gImg, hWt]
    · rintro ⟨c, ⟨y, hxy, hex, rfl⟩, rfl⟩
      have hy0 : W 0 < y := by rw [hW0]; linarith
      refine ⟨y, hxy, (exists_isForwardSol_iff_alive hW hy0).1 hex, ?_⟩
      rw [gImg, re_fwdMap_eq_cflow hW hy0 t.coe_nonneg hex, hWt]
  have hne : S.Nonempty := by
    obtain ⟨g, hg⟩ := imgSet_nonempty hW x t.coe_nonneg
    rw [hset] at hg
    obtain ⟨c, hc, -⟩ := hg
    exact ⟨c, hc⟩
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro c ⟨y, hxy, hex, rfl⟩
    have hy0 : W 0 < y := by rw [hW0]; linarith
    rw [re_fwdMap_eq_cflow hW hy0 t.coe_nonneg hex]
    exact (((exists_isForwardSol_iff_alive hW hy0).1 hex).cflow_pos hW ⟨t.coe_nonneg, le_rfl⟩).le
  rw [rightImg, hset, add_csInf_eq_csInf_image hne hbdd]

/-- **Adapter, left** (reflection `y ↦ −y`, `W ↦ −W`): on the source carrier the formula of `IsLeftForceImage` is
`−rightImg (−W) (−x)`, the landed left image (`PocketTraversal.geomLW`, `MartChar.geomL`). -/
theorem add_sSup_leftSet_eq_neg_rightImg (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : x ≤ 0)
    (t : ℝ≥0) :
    w t + sSup {c : ℝ | ∃ y : ℝ, y < x ∧
      (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u) ∧
      c = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) (t : ℝ) (y : ℂ)).re} =
      -rightImg (fun s : ℝ => -w s.toNNReal) (-x) t := by
  have hW : Continuous (fun s : ℝ => w s.toNNReal) := continuous_path hw
  have hW' : Continuous (fun s : ℝ => -w s.toNNReal) := hW.neg
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  have hR := add_sInf_rightSet_eq_rightImg (w := -w) hw.neg (by simp [hw0]) (neg_nonneg.2 hx) t
  simp only [Pi.neg_apply] at hR
  have hset : {c : ℝ | ∃ y : ℝ, y < x ∧
      (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u) ∧
      c = (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) (t : ℝ) (y : ℂ)).re} =
      -{c : ℝ | ∃ y : ℝ, -x < y ∧
      (∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => -w s.toNNReal) (y : ℂ) (t : ℝ) u) ∧
      c = (QuantumZipper.fwdMap (fun s : ℝ => -w s.toNNReal) (t : ℝ) (y : ℂ)).re} := by
    ext c
    simp only [Set.mem_neg, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, hyx, hex, rfl⟩
      have hy0 : y < (fun s : ℝ => w s.toNNReal) 0 := by rw [hW0]; linarith
      have hex' := (exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal)).1 hex
      refine ⟨-y, by linarith, hex', ?_⟩
      rw [re_fwdMap_eq_neg_cflow hW hy0 t.coe_nonneg hex,
        re_fwdMap_eq_cflow hW' (by simp [hw0]; linarith) t.coe_nonneg hex', neg_neg]
    · rintro ⟨y', hy', hex', hc⟩
      have hy0 : -y' < (fun s : ℝ => w s.toNNReal) 0 := by rw [hW0]; linarith
      have hex : ∃ u : ℝ → ℂ, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) ((-y' : ℝ) : ℂ)
          (t : ℝ) u :=
        (exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal) (y := -y')).2 (by simpa using hex')
      refine ⟨-y', by linarith, hex, ?_⟩
      rw [re_fwdMap_eq_neg_cflow hW hy0 t.coe_nonneg hex, neg_neg]
      rw [re_fwdMap_eq_cflow hW' (by simp [hw0]; linarith) t.coe_nonneg hex'] at hc
      linarith
  rw [hset, Real.sSup_neg, ← hR]
  ring

/-- **`IsRightForceImage` is the landed geometric right image on the source carrier.** -/
theorem isRightForceImage_iff {x : ℝ} {v : ℝ≥0 → ℝ} :
    IsRightForceImage w x v ↔ Continuous w ∧ w 0 = 0 ∧ 0 ≤ x ∧
      ∀ t : ℝ≥0, v t = rightImg (fun s : ℝ => w s.toNNReal) x t := by
  constructor
  · rintro ⟨hw, hw0, hx, hv⟩
    exact ⟨hw, hw0, hx, fun t => (hv t).trans (add_sInf_rightSet_eq_rightImg hw hw0 hx t)⟩
  · rintro ⟨hw, hw0, hx, hv⟩
    exact ⟨hw, hw0, hx, fun t => (hv t).trans (add_sInf_rightSet_eq_rightImg hw hw0 hx t).symm⟩

/-- **`IsLeftForceImage` is the landed geometric left image on the source carrier.** -/
theorem isLeftForceImage_iff {x : ℝ} {v : ℝ≥0 → ℝ} :
    IsLeftForceImage w x v ↔ Continuous w ∧ w 0 = 0 ∧ x ≤ 0 ∧
      ∀ t : ℝ≥0, v t = -rightImg (fun s : ℝ => -w s.toNNReal) (-x) t := by
  constructor
  · rintro ⟨hw, hw0, hx, hv⟩
    exact ⟨hw, hw0, hx, fun t => (hv t).trans (add_sSup_leftSet_eq_neg_rightImg hw hw0 hx t)⟩
  · rintro ⟨hw, hw0, hx, hv⟩
    exact ⟨hw, hw0, hx, fun t => (hv t).trans (add_sSup_leftSet_eq_neg_rightImg hw hw0 hx t).symm⟩

/-- On the source carrier the right image process exists and is unique. -/
theorem existsUnique_isRightForceImage (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    ∃! v : ℝ≥0 → ℝ, IsRightForceImage w x v :=
  ⟨_, ⟨hw, hw0, hx, fun _ => rfl⟩, fun _ hv => funext hv.2.2.2⟩

/-- On the source carrier the left image process exists and is unique. -/
theorem existsUnique_isLeftForceImage (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : x ≤ 0) :
    ∃! v : ℝ≥0 → ℝ, IsLeftForceImage w x v :=
  ⟨_, ⟨hw, hw0, hx, fun _ => rfl⟩, fun _ hv => funext hv.2.2.2⟩

/-- **Time zero**: the right image starts at the force point. -/
theorem IsRightForceImage.apply_zero {x : ℝ} {v : ℝ≥0 → ℝ} (h : IsRightForceImage w x v) : v 0 = x := by
  obtain ⟨hw, hw0, hx, hv⟩ := isRightForceImage_iff.1 h
  rw [hv 0, NNReal.coe_zero]
  exact rightImg_zero (continuous_path hw) (by simp [hw0]) hx

/-- **Time zero**: the left image starts at the force point. -/
theorem IsLeftForceImage.apply_zero {x : ℝ} {v : ℝ≥0 → ℝ} (h : IsLeftForceImage w x v) : v 0 = x := by
  obtain ⟨hw, hw0, hx, hv⟩ := isLeftForceImage_iff.1 h
  have hW' : Continuous (fun s : ℝ => -w s.toNNReal) := (continuous_path hw).neg
  rw [hv 0, NNReal.coe_zero, rightImg_zero hW' (by simp [hw0]) (neg_nonneg.2 hx), neg_neg]

/-- A point from which the centred flow exists is not the driver's starting point. -/
lemma ne_zero_of_isForwardSol (hw0 : w 0 = 0) {x : ℝ} {t : ℝ≥0} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) (t : ℝ) u) : x ≠ 0 := by
  have h0 := hu.2 0 ⟨le_rfl, t.coe_nonneg⟩
  rw [intervalIntegral.integral_same, add_zero] at h0
  intro hx
  apply h0.1
  rw [h0.2, hx]
  simp [hw0]

/-- **Unswallowed value, right**: while `x` is not swallowed, the image is `g_t(x) = w_t + f_t(x)`. -/
theorem IsRightForceImage.apply_of_isForwardSol {x : ℝ} {v : ℝ≥0 → ℝ} (h : IsRightForceImage w x v)
    {t : ℝ≥0} (hx : ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) (t : ℝ) u) :
    v t = w t + (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t x).re := by
  obtain ⟨hw, hw0, hx0, hv⟩ := isRightForceImage_iff.1 h
  have hW := continuous_path hw
  have hpos : (fun s : ℝ => w s.toNNReal) 0 < x := by
    obtain ⟨u, hu⟩ := hx
    simpa [hw0] using lt_of_le_of_ne hx0 (ne_zero_of_isForwardSol hw0 hu).symm
  have hA := (exists_isForwardSol_iff_alive hW hpos).1 hx
  rw [hv t, rightImg_eq_gImg hW t.coe_nonneg hA, gImg, re_fwdMap_eq_cflow hW hpos t.coe_nonneg hx]
  simp

/-- **Unswallowed value, left**: while `x` is not swallowed, the image is `g_t(x) = w_t + f_t(x)`. -/
theorem IsLeftForceImage.apply_of_isForwardSol {x : ℝ} {v : ℝ≥0 → ℝ} (h : IsLeftForceImage w x v)
    {t : ℝ≥0} (hx : ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) (t : ℝ) u) :
    v t = w t + (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t x).re := by
  obtain ⟨hw, hw0, hx0, hv⟩ := isLeftForceImage_iff.1 h
  have hW := continuous_path hw
  have hneg : x < (fun s : ℝ => w s.toNNReal) 0 := by
    obtain ⟨u, hu⟩ := hx
    simpa [hw0] using lt_of_le_of_ne hx0 (ne_zero_of_isForwardSol hw0 hu)
  have hex' := (exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal)).1 hx
  have hpos' : (fun s : ℝ => -w s.toNNReal) 0 < -x := by simp only at hneg ⊢; linarith
  have hW' : Continuous (fun s : ℝ => -w s.toNNReal) := hW.neg
  have hA := (exists_isForwardSol_iff_alive hW' hpos').1 hex'
  rw [hv t, rightImg_eq_gImg hW' t.coe_nonneg hA, gImg,
    re_fwdMap_eq_neg_cflow hW hneg t.coe_nonneg hx]
  simp only [Real.toNNReal_coe]
  ring

/-- **Extreme endpoint, right**: if `x` is swallowed at time `t`, the image is the right limit of `g_t` at the right
end `r_t = sup {y ≥ 0 : y swallowed by time t}` of the swallowed real set: "the `g_t` image of the right endpoint of
`ℝ ∩ K_t`". -/
theorem IsRightForceImage.tendsto_of_not_isForwardSol {x : ℝ} {v : ℝ≥0 → ℝ}
    (h : IsRightForceImage w x v) {t : ℝ≥0}
    (hx : ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) (t : ℝ) u) :
    Tendsto (fun y : ℝ => w t + (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t y).re)
      (𝓝[>] sSup {y : ℝ | 0 ≤ y ∧
        ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u})
      (𝓝 (v t)) := by
  obtain ⟨hw, hw0, hx0, hv⟩ := isRightForceImage_iff.1 h
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := continuous_path hw
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hWt : W t = w t := by simp [hWdef]
  have ht := t.coe_nonneg
  set Sw := {y : ℝ | 0 ≤ y ∧ ¬ ∃ u, QuantumZipper.IsForwardSol W (y : ℂ) (t : ℝ) u} with hSw
  have halive : ∀ y, x < y → (Alive W y t ↔ ∃ u, QuantumZipper.IsForwardSol W (y : ℂ) (t : ℝ) u) :=
    fun y hy => (exists_isForwardSol_iff_alive hW (by rw [hW0]; linarith)).symm
  have hxS : x ∈ Sw := ⟨hx0, hx⟩
  obtain ⟨g₁, y₁, hxy₁, hy₁, -⟩ := imgSet_nonempty hW x ht
  have hbdd : BddAbove Sw := ⟨y₁, fun y hy => by
    by_contra hlt
    exact hy.2 ((halive y (hxy₁.trans (not_le.1 hlt))).1 (hy₁.of_le hW (not_le.1 hlt).le ht))⟩
  set r := sSup Sw with hr
  have hxr : x ≤ r := le_csSup hbdd hxS
  have hgt : ∀ y, r < y → Alive W y t := fun y hy => by
    by_contra hna
    have hmem : y ∈ Sw := ⟨by linarith, fun hex => hna ((halive y (by linarith)).2 hex)⟩
    exact absurd (le_csSup hbdd hmem) (not_le.2 hy)
  have hge : ∀ y', x < y' → Alive W y' t → r ≤ y' := fun y' hxy' hy' => by
    by_contra hlt
    obtain ⟨y'', hy''S, hlt''⟩ := exists_lt_of_lt_csSup ⟨x, hxS⟩ (not_le.1 hlt)
    exact hy''S.2 ((halive y'' (hxy'.trans hlt'')).1 (hy'.of_le hW hlt''.le ht))
  rw [hv t]
  refine Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ⟨ε, hε, fun y hy hdist => ?_⟩
  have hry : r < y := hy
  have hxy : x < y := hxr.trans_lt hry
  have hyA := hgt y hry
  have hg : w t + (QuantumZipper.fwdMap W t y).re = gImg W y t := by
    rw [gImg, re_fwdMap_eq_cflow hW (by rw [hW0]; linarith) ht ((halive y hxy).1 hyA), hWt]
  have h1 := rightImg_le_gImg hW ht hxy hyA
  have h2 := gImg_sub_rightImg_le hW ht hxy hyA hge
  rw [Real.dist_eq] at hdist ⊢
  rw [hg, abs_of_nonneg (by linarith)]
  rw [abs_of_pos (by linarith)] at hdist
  linarith

/-- **Extreme endpoint, left**: if `x` is swallowed at time `t`, the image is the left limit of `g_t` at the left
end `l_t = inf {y ≤ 0 : y swallowed by time t}` of the swallowed real set ("the `g_t` image of the left endpoint of
`ℝ ∩ K_t`"); proved from the right case by the reflection `y ↦ −y`, `w ↦ −w`. -/
theorem IsLeftForceImage.tendsto_of_not_isForwardSol {x : ℝ} {v : ℝ≥0 → ℝ}
    (h : IsLeftForceImage w x v) {t : ℝ≥0}
    (hx : ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (x : ℂ) (t : ℝ) u) :
    Tendsto (fun y : ℝ => w t + (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t y).re)
      (𝓝[<] sInf {y : ℝ | y ≤ 0 ∧
        ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u})
      (𝓝 (v t)) := by
  obtain ⟨hw, hw0, hx0, hv⟩ := isLeftForceImage_iff.1 h
  have hW : Continuous (fun s : ℝ => w s.toNNReal) := continuous_path hw
  have hW' : Continuous (fun s : ℝ => -w s.toNNReal) := hW.neg
  have ht := t.coe_nonneg
  have hR : IsRightForceImage (-w) (-x) (fun t => rightImg (fun s : ℝ => -w s.toNNReal) (-x) t) :=
    isRightForceImage_iff.2 ⟨hw.neg, by simp [hw0], neg_nonneg.2 hx0, fun _ => rfl⟩
  have hx' : ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => (-w) s.toNNReal) ((-x : ℝ) : ℂ) (t : ℝ) u :=
    fun hex => hx ((exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal)).2 hex)
  have hT := IsRightForceImage.tendsto_of_not_isForwardSol hR hx'
  simp only [Pi.neg_apply] at hT
  set A := {y : ℝ | y ≤ 0 ∧
    ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u} with hA
  have hA' : {y : ℝ | 0 ≤ y ∧
      ¬ ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => -w s.toNNReal) (y : ℂ) (t : ℝ) u} = -A := by
    ext y
    simp only [Set.mem_neg, Set.mem_ofPred_eq, hA, neg_nonpos]
    refine and_congr Iff.rfl (not_congr ?_)
    rw [exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal) (y := -y), neg_neg]
  rw [hA', Real.sSup_neg] at hT
  set l := sInf A with hl
  have hxA : x ∈ A := ⟨hx0, hx⟩
  obtain ⟨g₁, y₁, hxy₁, hy₁, -⟩ := imgSet_nonempty hW' (-x) ht
  have hbddA : BddBelow A := ⟨-y₁, fun y hy => by
    by_contra hlt
    have hlt' : y₁ < -y := by linarith [not_le.1 hlt]
    have hA1 : Alive (fun s : ℝ => -w s.toNNReal) (-y) t := hy₁.of_le hW' hlt'.le ht
    have hex' := (exists_isForwardSol_iff_alive hW' (by simp [hw0]; linarith)).2 hA1
    exact hy.2 ((exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal) (y := y)).2
      (by simpa using hex'))⟩
  have hl0 : l ≤ 0 := (csInf_le hbddA hxA).trans hx0
  have hneg : Tendsto (fun y : ℝ => -y) (𝓝[<] l) (𝓝[>] (-l)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (continuous_neg.tendsto l).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y (hy : y < l)
      exact neg_lt_neg hy
  have hcomp := (hT.comp hneg).neg
  rw [hv t]
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y (hy : y < l)
  have hy0 : y ≤ 0 := hy.le.trans hl0
  have hnotA : y ∉ A := fun hyA => absurd (csInf_le hbddA hyA) (not_le.2 hy)
  have hex : ∃ u, QuantumZipper.IsForwardSol (fun s : ℝ => w s.toNNReal) (y : ℂ) (t : ℝ) u := by
    by_contra hne
    exact hnotA ⟨hy0, hne⟩
  have hyneg : y < (fun s : ℝ => w s.toNNReal) 0 := by
    have hy0' : y ≠ 0 := by
      obtain ⟨u, hu⟩ := hex
      exact ne_zero_of_isForwardSol hw0 hu
    simp only [Real.toNNReal_zero, hw0]
    exact lt_of_le_of_ne hy0 hy0'
  have hex' := (exists_isForwardSol_neg_iff (W := fun s : ℝ => w s.toNNReal)).1 hex
  show -((-w t) + (QuantumZipper.fwdMap (fun s : ℝ => -w s.toNNReal) (t : ℝ) ((-y : ℝ) : ℂ)).re) =
    w t + (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) (t : ℝ) (y : ℂ)).re
  rw [re_fwdMap_eq_neg_cflow hW hyneg ht hex,
    re_fwdMap_eq_cflow hW' (by simp only at hyneg ⊢; linarith) ht hex']
  ring

end Images

/-! ## Certification B: the local-martingale predicate (audit AUD-T2426B F3) -/

section LocalMart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {ζ : Ω → WithTop ℝ≥0}

lemma coe_untopA_of_ne_top {x : WithTop ℝ≥0} (h : x ≠ ⊤) : ((x.untopA : ℝ≥0) : WithTop ℝ≥0) = x := by
  rw [WithTop.untopA_eq_untop h, WithTop.coe_untop]

/-- A localizing time that is `0` or strictly below `ζ` reads `X` only strictly before `ζ`: the localized processes of
two processes that agree before `ζ` coincide (at the sample `ω`). -/
lemma stoppedIndicator_apply_congr {X Y : ℝ≥0 → Ω → ℝ} {σ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hσ : σ ω = 0 ∨ σ ω < ζ ω) (hXY : ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω)
    (t : ℝ≥0) :
    stoppedProcess (fun t => {ω | 0 < σ ω}.indicator (X t)) σ t ω =
      stoppedProcess (fun t => {ω | 0 < σ ω}.indicator (Y t)) σ t ω := by
  simp only [stoppedProcess, Set.indicator, Set.mem_ofPred_eq]
  split_ifs with hpos
  · rcases hσ with h0 | hlt
    · rw [h0] at hpos
      exact absurd hpos (lt_irrefl _)
    · have hne : min (t : WithTop ℝ≥0) (σ ω) ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
      refine hXY _ ?_
      rw [coe_untopA_of_ne_top hne]
      exact (min_le_right _ _).trans_lt hlt
  · rfl

/-- **The predicate depends only on the values strictly before `ζ`** (exact form: changes of `X` at and after `ζ`, at
every sample, do not matter). -/
theorem isContLocalMartingaleBefore_congr {X Y : ℝ≥0 → Ω → ℝ}
    (hXY : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω) :
    IsContLocalMartingaleBefore 𝓕 P ζ X ↔ IsContLocalMartingaleBefore 𝓕 P ζ Y := by
  have key : ∀ {X Y : ℝ≥0 → Ω → ℝ}, (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω) →
      IsContLocalMartingaleBefore 𝓕 P ζ X → IsContLocalMartingaleBefore 𝓕 P ζ Y := by
    intro X Y hXY ⟨hc, σ, hst, hσ, hex, hm⟩
    refine ⟨hc.mono fun ω hω => hω.congr fun t ht => (hXY ω t ht).symm, σ, hst, hσ, hex, fun n => ?_⟩
    have heq : stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (Y t)) (σ n) =
        stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n) := by
      funext t ω
      exact (stoppedIndicator_apply_congr (hσ n ω) (hXY ω) t).symm
    rw [heq]
    exact hm n
  exact ⟨key hXY, key fun ω t ht => (hXY ω t ht).symm⟩

/-- A martingale multiplied by the indicator of an `𝓕 0`-measurable set is a martingale. -/
lemma martingale_indicator_of_measurableSet_zero {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓕 P)
    {A : Set Ω} (hA : MeasurableSet[𝓕 0] A) : Martingale (fun t => A.indicator (M t)) 𝓕 P := by
  refine ⟨fun t => (hM.1 t).indicator (𝓕.mono zero_le _ hA), fun i j hij => ?_⟩
  have hAi : MeasurableSet[𝓕 i] A := 𝓕.mono zero_le _ hA
  exact (condExp_indicator (hM.integrable j) hAi).trans
    ((hM.2 i j hij).mono fun ω hω => by simp only [Set.indicator]; split_ifs <;> simp [hω])

/-- **The predicate depends only on the almost-sure class of the process before `ζ`**, in a filtration whose time-`0`
σ-algebra contains the null sets (e.g. every usual augmentation, `isContLocalMartingaleBefore_congr_ae_usualAugmentation`).
The localizing times are set to `0` on a measurable null set carrying the disagreement. -/
theorem isContLocalMartingaleBefore_congr_ae
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) {X Y : ℝ≥0 → Ω → ℝ}
    (hXY : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω) :
    IsContLocalMartingaleBefore 𝓕 P ζ X ↔ IsContLocalMartingaleBefore 𝓕 P ζ Y := by
  classical
  have key : ∀ {X Y : ℝ≥0 → Ω → ℝ}, (∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω) →
      IsContLocalMartingaleBefore 𝓕 P ζ X → IsContLocalMartingaleBefore 𝓕 P ζ Y := by
    intro X Y hXY ⟨hc, σ, hst, hσ, hex, hm⟩
    obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hXY)
    have hN0' : MeasurableSet[𝓕 0] N := hnull N hNm hN0
    have hgood : ∀ ω, ω ∉ N → ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ζ ω → X t ω = Y t ω :=
      fun ω hω => by
        by_contra hbad
        exact hω (hNsub hbad)
    have haeN : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    set σ' : ℕ → Ω → WithTop ℝ≥0 := fun n ω => if ω ∈ N then 0 else σ n ω with hσ'
    refine ⟨?_, σ', fun n => ?_, fun n ω => ?_, ?_, fun n => ?_⟩
    · filter_upwards [hc, haeN] with ω hω hωN
      exact hω.congr fun t ht => (hgood ω hωN t ht).symm
    · intro t
      have hset : {ω | σ' n ω ≤ t} = N ∪ ({ω | σ n ω ≤ t} ∩ Nᶜ) := by
        ext ω
        by_cases hω : ω ∈ N
        · simp only [hσ', hω, ite_true, Set.mem_ofPred_eq, Set.mem_union, true_or, iff_true]
          exact zero_le
        · simp [hσ', hω]
      rw [hset]
      exact (𝓕.mono zero_le _ hN0').union ((hst n t).inter (𝓕.mono zero_le _ hN0'.compl))
    · by_cases hω : ω ∈ N
      · exact Or.inl (by simp [hσ', hω])
      · simpa [hσ', hω] using hσ n ω
    · filter_upwards [hex, haeN] with ω hω hωN r hr
      simpa [hσ', hωN] using hω r hr
    · have heq : stoppedProcess (fun t => {ω | 0 < σ' n ω}.indicator (Y t)) (σ' n) =
          fun t => Nᶜ.indicator (stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n) t) := by
        funext t ω
        by_cases hω : ω ∈ N
        · simp [stoppedProcess, Set.indicator, hσ', hω]
        · have h1 : stoppedProcess (fun t => {ω | 0 < σ' n ω}.indicator (Y t)) (σ' n) t ω =
              stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (Y t)) (σ n) t ω := by
            simp [stoppedProcess, Set.indicator, hσ', hω]
          rw [h1, (stoppedIndicator_apply_congr (hσ n ω) (hgood ω hω) t).symm]
          simp [Set.indicator, hω]
      rw [heq]
      exact martingale_indicator_of_measurableSet_zero (hm n) hN0'.compl
  exact ⟨key hXY, key (hXY.mono fun ω h t ht => (h t ht).symm)⟩

/-- The usual augmentation contains the null sets at time `0`. -/
theorem isContLocalMartingaleBefore_congr_ae_usualAugmentation [MeasurableSpace Ω]
    {𝓗 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Q : Measure Ω} {ξ : Ω → WithTop ℝ≥0}
    {X Y : ℝ≥0 → Ω → ℝ} (hXY : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < ξ ω → X t ω = Y t ω) :
    IsContLocalMartingaleBefore (usualAugmentation 𝓗 Q) Q ξ X ↔
      IsContLocalMartingaleBefore (usualAugmentation 𝓗 Q) Q ξ Y :=
  isContLocalMartingaleBefore_congr_ae (fun _ hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    hXY

/-- **Sanity: the predicate contains the continuous martingales** (`ζ = ⊤`, localizing times `σ_n = n`; the time-`0`
localizer reads nothing). -/
theorem Martingale.isContLocalMartingaleBefore_top [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hM : Martingale X 𝓕 P) (hc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) :
    IsContLocalMartingaleBefore 𝓕 P (fun _ => ⊤) X := by
  refine ⟨hc.mono fun ω hω => hω.continuousOn, fun n _ => ((n : ℝ≥0) : WithTop ℝ≥0), fun n => ?_,
    fun n ω => Or.inr (WithTop.coe_lt_top _), ae_of_all _ fun ω r _ => ?_, fun n => ?_⟩
  · exact isStoppingTime_const 𝓕 _
  · obtain ⟨m, hm⟩ := exists_nat_gt (r : ℝ)
    filter_upwards [Filter.eventually_ge_atTop m] with k hk
    have : (r : ℝ) < k := hm.trans_le (by exact_mod_cast hk)
    exact WithTop.coe_lt_coe.2 (by exact_mod_cast this)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : stoppedProcess (fun t => {ω | 0 < (((0 : ℕ) : ℝ≥0) : WithTop ℝ≥0)}.indicator (X t))
          (fun _ => (((0 : ℕ) : ℝ≥0) : WithTop ℝ≥0)) = fun _ _ => 0 := by
        funext t ω
        simp [stoppedProcess]
      rw [h0]
      exact martingale_zero _ _ _
    · have hpos : (0 : WithTop ℝ≥0) < ((n : ℝ≥0) : WithTop ℝ≥0) := by
        exact_mod_cast (show (0 : ℝ≥0) < n by exact_mod_cast hn)
      have heq : stoppedProcess (fun t => {ω | 0 < ((n : ℝ≥0) : WithTop ℝ≥0)}.indicator (X t))
          (fun _ => ((n : ℝ≥0) : WithTop ℝ≥0)) = fun t => X (min t n) := by
        funext t ω
        simp only [stoppedProcess, Set.indicator, Set.mem_ofPred_eq, hpos, ite_true]
        rw [← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      rw [heq]
      refine ⟨fun t => (hM.1 (min t n)).mono (𝓕.mono (min_le_left t n)), fun i j hij => ?_⟩
      show P[X (min j (n : ℝ≥0)) | 𝓕 i] =ᵐ[P] X (min i (n : ℝ≥0))
      rcases le_or_gt (n : ℝ≥0) i with hni | hin
      · have h1 : min j (n : ℝ≥0) = n := min_eq_right (hni.trans hij)
        have h2 : min i (n : ℝ≥0) = n := min_eq_right hni
        rw [h1, h2]
        exact (condExp_of_stronglyMeasurable (𝓕.le i) ((hM.1 n).mono (𝓕.mono hni))
          (hM.integrable n)).eventuallyEq
      · have h2 : min i (n : ℝ≥0) = i := min_eq_left hin.le
        rw [h2]
        exact hM.2 i (min j n) (le_min hij hin.le)

/-- **Bridge to the landed predicate** (`MartChar.IsLocalMartingaleBefore`, the hypothesis form of the landed proofs
of Theorem 2.4's converse): given an `𝓕 0`-measurable integrable initial value. -/
theorem IsContLocalMartingaleBefore.isLocalMartingaleBefore [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (h : IsContLocalMartingaleBefore 𝓕 P ζ X) (h0m : StronglyMeasurable[𝓕 0] (X 0))
    (h0i : Integrable (X 0) P) : MartChar.IsLocalMartingaleBefore 𝓕 P ζ X := by
  classical
  obtain ⟨-, σ, hst, hσ, hex, hm⟩ := h
  refine ⟨σ, hst, fun n ω => ?_, hex, fun n => ?_⟩
  · rcases hσ n ω with h0 | hlt
    · rw [h0]; exact bot_le
    · exact hlt.le
  · have hA : MeasurableSet[𝓕 0] {ω | σ n ω = 0} := by
      have := hst n 0
      simpa [nonpos_iff_eq_zero] using this
    have hconst : Martingale (fun _ : ℝ≥0 => {ω | σ n ω = 0}.indicator (X 0)) 𝓕 P := by
      have hsm : StronglyMeasurable[𝓕 ⊥] ({ω | σ n ω = 0}.indicator (X 0)) := by
        rw [bot_eq_zero]
        exact h0m.indicator hA
      exact martingale_const_fun 𝓕 P hsm (h0i.indicator (𝓕.le 0 _ hA))
    have heq : stoppedProcess X (σ n) = fun t =>
        stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n) t +
          {ω | σ n ω = 0}.indicator (X 0) := by
      funext t ω
      simp only [stoppedProcess, Pi.add_apply, Set.indicator, Set.mem_ofPred_eq]
      by_cases h0 : σ n ω = 0
      · have hmin : (min (t : WithTop ℝ≥0) 0).untopA = 0 := by
          rw [min_eq_right zero_le, WithTop.untopA_eq_untop WithTop.zero_ne_top, WithTop.untop_zero]
        simp only [h0, lt_irrefl, ite_false, ite_true, hmin, zero_add]
      · have hpos : 0 < σ n ω := pos_iff_ne_zero.2 h0
        simp [hpos, h0]
    rw [heq]
    exact (hm n).add hconst

end LocalMart

/-! ## Certification C: the conformal radius (audit AUD-T2426B F4) -/

section ConfRadius

open Metric
open SupercriticalConformalCovariance (IsConformalBijection)

/-- **Choice independence (Schwarz lemma)**: all conformal maps of the disc onto `D` sending `0` to `z` have the same
`|φ'(0)|`, so `IsConformalRadius D z` is a functional relation on every `(D, z)`. -/
theorem isConformalRadius_unique {D : Set ℂ} {z : ℂ} {r r' : ℝ} (h : IsConformalRadius D z r)
    (h' : IsConformalRadius D z r') : r = r' := by
  obtain ⟨φ, hφd, hφb, hφ0, rfl⟩ := h
  obtain ⟨ψ, hψd, hψb, hψ0, rfl⟩ := h'
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  set e := QuantumZipper.CA.univalentOPH isOpen_ball hφd hφb.injOn with he
  have himg : φ '' ball 0 1 = D := hφb.image_eq
  have hed : DifferentiableOn ℂ e.symm D := by
    have := QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball hφd hφb.injOn
    rwa [himg] at this
  have hleft : ∀ w ∈ ball (0 : ℂ) 1, e.symm (φ w) = w := fun w hw =>
    QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball hφd hφb.injOn hw
  have hright : ∀ q ∈ D, φ (e.symm q) = q := fun q hq =>
    QuantumZipper.CA.univalentOPH_apply_symm_apply isOpen_ball hφd hφb.injOn (himg ▸ hq)
  have hebij : BijOn e.symm D (ball 0 1) := by
    refine ⟨fun q hq => ?_, fun q₁ h₁ q₂ h₂ h => ?_, fun w hw => ⟨φ w, hφb.mapsTo hw, hleft w hw⟩⟩
    · have hq' : q ∈ e.target := by
        rw [he, QuantumZipper.CA.univalentOPH_target, himg]
        exact hq
      have := e.map_target hq'
      rwa [he, QuantumZipper.CA.univalentOPH_source] at this
    · rw [← hright q₁ h₁, ← hright q₂ h₂, h]
  have hg : IsConformalBijection (e.symm ∘ ψ) (ball 0 1) (ball 0 1) :=
    isConformalBijection_comp ⟨hed, hebij⟩ ⟨hψd, hψb⟩
  have hg0 : (e.symm ∘ ψ) 0 = 0 := by
    simp only [Function.comp_apply, hψ0, ← hφ0, hleft 0 h0]
  obtain ⟨u, hu, hrot⟩ := QuantumZipper.CA.exists_rotation_of_bijOn_ball hg.1 hg.2 hg0
  have hψu : ∀ w ∈ ball (0 : ℂ) 1, ψ w = φ (u * w) := fun w hw => by
    have := hrot hw
    simp only [Function.comp_apply] at this
    rw [← this, hright _ (hψb.mapsTo hw)]
  have hev : ψ =ᶠ[𝓝 0] fun w => φ (u * w) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds h0) hψu
  have hφdiff : DifferentiableAt ℂ φ 0 := hφd.differentiableAt (isOpen_ball.mem_nhds h0)
  have hder : deriv ψ 0 = deriv φ 0 * u := by
    rw [hev.deriv_eq]
    have h1 : HasDerivAt (fun w => u * w) u 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul u
    have h2 : HasDerivAt φ (deriv φ 0) (u * 0) := by
      rw [mul_zero]
      exact hφdiff.hasDerivAt
    exact (h2.comp 0 h1).deriv
  rw [hder, norm_mul, hu, mul_one]

/-- A conformal radius is positive (an injective holomorphic map has nonzero derivative). -/
theorem IsConformalRadius.pos {D : Set ℂ} {z : ℂ} {r : ℝ} (h : IsConformalRadius D z r) : 0 < r := by
  obtain ⟨φ, hφd, hφb, -, rfl⟩ := h
  exact norm_pos_iff.2 (QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hφd hφb.injOn
    (mem_ball_self one_pos))

/-- **`crad(ℍ, z) = 2 Im z`** (the disc chart `ζ ↦ Cayley⁻¹` centred at `z`). -/
theorem isConformalRadius_upperHalfPlane {z : ℂ} (hz : z ∈ QuantumZipper.H) :
    IsConformalRadius QuantumZipper.H z (2 * z.im) := by
  obtain ⟨hd, hb⟩ := isConformalBijection_diskChartH hz
  refine ⟨diskChartH z, hd, hb, diskChartH_zero z, ?_⟩
  have hz' : 0 < z.im := hz
  rw [(hasDerivAt_diskChartH z).deriv]
  simp [abs_of_pos hz']

/-- **The Loewner domain has a conformal radius at every unswallowed point**, through the Loewner map
(`exists_isConformalBijection_ball_fwdHull`): `crad(ℍ ∖ K_t, z) = 2 Im f_t(z) / |f_t'(z)|`. -/
theorem isConformalRadius_fwdHull {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ QuantumZipper.H \ QuantumZipper.fwdHull W t) :
    IsConformalRadius (QuantumZipper.H \ QuantumZipper.fwdHull W t) z
      (2 * (QuantumZipper.fwdMap W t z).im / ‖deriv (QuantumZipper.fwdMap W t) z‖) := by
  obtain ⟨φ, hφ, hφ0, hφd⟩ := exists_isConformalBijection_ball_fwdHull hW hW0 ht hz
  exact ⟨φ, hφ.1, hφ.2, hφ0, hφd⟩

/-- The complement of the Loewner hull is connected: the component containing an unswallowed point is all of it
("the unbounded component containing `z`"). -/
theorem connectedComponentIn_fwdHull_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ QuantumZipper.H \ QuantumZipper.fwdHull W t) :
    connectedComponentIn (QuantumZipper.H \ QuantumZipper.fwdHull W t) z =
      QuantumZipper.H \ QuantumZipper.fwdHull W t := by
  obtain ⟨φ, hφ, -, -⟩ := exists_isConformalBijection_ball_fwdHull hW hW0 ht hz
  refine IsPreconnected.connectedComponentIn ?_ hz
  rw [← hφ.2.image_eq]
  exact (convex_ball (0 : ℂ) 1).isPreconnected.image φ hφ.1.continuousOn

/-- A point is outside `K_t` before its swallowing time. -/
lemma mem_diff_fwdHull_of_lt_swallowTime {W : ℝ → ℝ} {z : ℂ} (hz : z ∈ QuantumZipper.H) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime W z) :
    z ∈ QuantumZipper.H \ QuantumZipper.fwdHull W t := by
  refine ⟨hz, fun hK => ?_⟩
  have h := hK.2
  rw [ENNReal.ofReal_coe_nnreal] at h
  exact absurd h (not_le.2 ht)

/-- **The radii of Theorem 2.6 exist, are positive and explicit, before `z` is swallowed** (continuous driver from
`0`): `crad(ℍ, z) = 2 Im z` and `crad(component of ℍ ∖ K_t containing z, z) = 2 Im f_t(z) / |f_t'(z)|`. -/
theorem exists_isConformalRadius_pair {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {z : ℂ}
    (hz : z ∈ QuantumZipper.H) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => w s.toNNReal) z) :
    IsConformalRadius QuantumZipper.H z (2 * z.im) ∧
      IsConformalRadius (connectedComponentIn (QuantumZipper.H \
        QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t) z) z
        (2 * (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t z).im /
          ‖deriv (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t) z‖) := by
  have hW := continuous_path hw
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  have hz' := mem_diff_fwdHull_of_lt_swallowTime hz ht
  refine ⟨isConformalRadius_upperHalfPlane hz, ?_⟩
  rw [connectedComponentIn_fwdHull_eq hW hW0 t.coe_nonneg hz']
  exact isConformalRadius_fwdHull hW hW0 t.coe_nonneg hz'

/-- **The bracket process of Theorem 2.6 is pinned**: any `A_t` satisfying the radius relation at `(t, ω)` is the
explicit Loewner quantity `log (2 Im z / (2 Im f_t(z) / |f_t'(z)|))`. -/
theorem eq_log_of_isConformalRadius {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {z : ℂ}
    (hz : z ∈ QuantumZipper.H) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < QuantumZipper.swallowTime (fun s : ℝ => w s.toNNReal) z) {a : ℝ}
    (ha : ∃ r₀ r : ℝ, IsConformalRadius QuantumZipper.H z r₀ ∧
      IsConformalRadius (connectedComponentIn (QuantumZipper.H \
        QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) t) z) z r ∧ a = Real.log (r₀ / r)) :
    a = Real.log (2 * z.im / (2 * (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t z).im /
      ‖deriv (QuantumZipper.fwdMap (fun s : ℝ => w s.toNNReal) t) z‖)) := by
  obtain ⟨r₀, r, h₀, h, rfl⟩ := ha
  obtain ⟨h₀', h'⟩ := exists_isConformalRadius_pair hw hw0 hz ht
  rw [isConformalRadius_unique h₀ h₀', isConformalRadius_unique h h']

/-- **The bracket hypothesis of Theorem 2.6 in explicit Loewner form**: for every process `A` satisfying the radius
relation almost surely before a stop `ξ ≤ τ_z`, `𝔥² − A` is a continuous local martingale before `ξ` (in a usual
augmentation) iff `𝔥² − log (2 Im z / (2 Im f_t(z)/|f_t'(z)|))` is. Such an `A` exists:
`exists_log_conformalRadius_process`. -/
theorem isContLocalMartingaleBefore_sq_sub_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓗 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ} {z : ℂ} (hz : z ∈ QuantumZipper.H)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0) {ξ : Ω → ℝ≥0∞}
    (hξ : ∀ ω, ξ ω ≤ QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z) {X A : ℝ≥0 → Ω → ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ξ ω → ∃ r₀ r : ℝ, IsConformalRadius QuantumZipper.H z r₀ ∧
      IsConformalRadius (connectedComponentIn (QuantumZipper.H \
        QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t) z) z r ∧ A t ω = Real.log (r₀ / r)) :
    IsContLocalMartingaleBefore (usualAugmentation 𝓗 P) P (fun ω => (ξ ω : WithTop ℝ≥0))
        (fun t ω => X t ω ^ 2 - A t ω) ↔
      IsContLocalMartingaleBefore (usualAugmentation 𝓗 P) P (fun ω => (ξ ω : WithTop ℝ≥0))
        (fun t ω => X t ω ^ 2 - Real.log (2 * z.im /
          (2 * (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) t z).im /
            ‖deriv (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) t) z‖))) := by
  refine isContLocalMartingaleBefore_congr_ae_usualAugmentation ?_
  filter_upwards [hW, hA] with ω hWω hAω t ht
  have ht' : (t : ℝ≥0∞) < ξ ω := ht
  rw [eq_log_of_isConformalRadius hWω.1 hWω.2 hz ((ht'.trans_le (hξ ω))) (hAω t ht')]

/-- **Non-vacuity of the bracket hypothesis of Theorem 2.6** (audit AUD-T2426A-v2, note V3): for a driver that is
almost surely continuous from `0` and any stop `T`, the explicit Loewner process
`A_t = log (2 Im z / (2 Im f_t(z) / |f_t'(z)|))` satisfies the radius relation almost surely before `min (τ_z, T)`. -/
theorem exists_log_conformalRadius_process {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {W : ℝ≥0 → Ω → ℝ} {z : ℂ} (hz : z ∈ QuantumZipper.H)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0) (T : Ω → ℝ≥0∞) :
    ∃ A : ℝ≥0 → Ω → ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z) (T ω) →
      ∃ r₀ r : ℝ, IsConformalRadius QuantumZipper.H z r₀ ∧
        IsConformalRadius (connectedComponentIn (QuantumZipper.H \
          QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) t) z) z r ∧
        A t ω = Real.log (r₀ / r) := by
  refine ⟨fun t ω => Real.log (2 * z.im / (2 * (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) t z).im /
      ‖deriv (QuantumZipper.fwdMap (fun s : ℝ => W s.toNNReal ω) t) z‖)), ?_⟩
  filter_upwards [hW] with ω hω t ht
  obtain ⟨h1, h2⟩ := exists_isConformalRadius_pair hω.1 hω.2 hz (ht.trans_le (min_le_left _ _))
  exact ⟨_, _, h1, h2, rfl⟩

end ConfRadius

/-! ## Certification D: the force-point binders are satisfiable (non-vacuity of `hV`) -/

section Version

/-- **Measurable force-point processes with the source meaning exist** for every measurable driver that is almost
surely continuous from `0`: modify the driver on a measurable null set and take the landed geometric images. So the
binders `VL`, `VR` with `hVL`, `hVR`, `hV` of Theorems 2.4–2.6 never make the theorems vacuous. -/
theorem exists_forceImage_processes {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ t, Measurable (W t)) (hWae : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0) :
    ∃ (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ),
      (∀ i t, Measurable (VL i t)) ∧ (∀ j t, Measurable (VR j t)) ∧
      ∀ᵐ ω ∂P, (∀ i, IsLeftForceImage (fun t => W t ω) (xL i) (fun t => VL i t ω)) ∧
        ∀ j, IsRightForceImage (fun t => W t ω) (xR j) (fun t => VR j t ω) := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hWae)
  have hgood : ∀ ω, ω ∉ N → Continuous (fun t => W t ω) ∧ W 0 ω = 0 := fun ω hω => by
    by_contra hbad
    exact hω (hNsub hbad)
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ N then 0 else W t ω with hW'def
  have hW'm : ∀ t, Measurable (W' t) := fun t => Measurable.ite hNm measurable_const (hW t)
  have hW'c : ∀ ω, Continuous fun t => W' t ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp only [hW'def, hω, ite_true]; exact continuous_const
    · simp only [hW'def, hω, ite_false]; exact (hgood ω hω).1
  have hW'n : ∀ ω, Continuous fun t => -W' t ω := fun ω => (hW'c ω).neg
  let 𝓒 : Filtration ℝ≥0 mΩ := Filtration.const ℝ≥0 mΩ le_rfl
  refine ⟨fun i t ω => -MartChar.RealFlow.rightImg (Bessel.realPath (fun t ω => -W' t ω) ω) (-xL i) t,
    fun j t ω => MartChar.RealFlow.rightImg (Bessel.realPath W' ω) (xR j) t, fun i t => ?_, fun j t => ?_, ?_⟩
  · exact (MartChar.measurable_rightImg_realPath (𝓕 := 𝓒) (fun t => (hW'm t).neg) hW'n (-xL i) t).neg
  · exact MartChar.measurable_rightImg_realPath (𝓕 := 𝓒) hW'm hW'c (xR j) t
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    have hWW : ∀ t, W' t ω = W t ω := fun t => by simp [hW'def, hω]
    obtain ⟨hc, h0⟩ := hgood ω hω
    refine ⟨fun i => isLeftForceImage_iff.2 ⟨hc, h0, hF.2.1 i, fun t => ?_⟩,
      fun j => isRightForceImage_iff.2 ⟨hc, h0, hF.2.2.2 j, fun t => ?_⟩⟩
    · congr 2
      funext s
      simp [Bessel.realPath, hWW]
    · congr 1
      funext s
      simp [Bessel.realPath, hWW]

end Version

/-! ## Plumbing (conditional evidence): Theorem 2.4's converse from the landed `isRandomWordEvolution_prod` -/

section Plumbing

/-- `continuationThreshold` is the landed `MartChar.thresholdTime` (literal infimum vs. `if`-form). -/
theorem continuationThreshold_eq_thresholdTime {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) :
    continuationThreshold ρL ρR w vL vR = MartChar.thresholdTime ρL ρR w vL vR := by
  classical
  unfold continuationThreshold MartChar.thresholdTime
  split_ifs with h
  · rw [ENNReal.coe_sInf h]
    rfl
  · rw [Set.not_nonempty_iff_eq_empty] at h
    refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
    have : t ∈ MartChar.thresholdSet ρL ρR w vL vR := ht
    rw [h] at this
    exact absurd this (Set.notMem_empty t)

lemma fwdMap_time_zero (W : ℝ → ℝ) {z : ℂ} (hz : z ≠ W 0) :
    QuantumZipper.fwdMap W 0 z = z - W 0 := by
  have hex : ∃ u, QuantumZipper.IsForwardSol W z 0 u :=
    ⟨fun _ => z - W 0, continuousOn_const, fun s hs => by
      obtain rfl : s = 0 := le_antisymm hs.2 hs.1
      simp [sub_ne_zero.2 hz]⟩
  rw [QuantumZipper.fwdMap, dite_eq_left_of_eq_true (eq_true hex)]
  have := (hex.choose_spec.2 0 ⟨le_rfl, le_rfl⟩).2
  simpa using this

open Sec7.PocketTraversal in
/-- **Theorem 2.4 (v2), converse direction, from the landed `Restart.ConverseBefore.isRandomWordEvolution_prod`**,
under the bridge hypotheses `hWc`, `hW0` (everywhere versions, obtained from the almost-sure hypotheses by the
modification of `exists_forceImage_processes` and `isContLocalMartingaleBefore_congr_ae_usualAugmentation`), `hWa`
(the driver is adapted to the augmented curve filtration) and `hVL`, `hVR` (the processes are the landed images; by
`isLeftForceImage_iff`/`isRightForceImage_iff` this is the a.s. hypothesis `hV` on the modified driver). -/
theorem converse24v2_of_bridges {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {η : ℝ≥0 → Ω → ℂ} (hη : ∀ t, StronglyMeasurable (η t))
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hWa : StronglyAdapted (usualAugmentation (Filtration.natural η hη) P) W)
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hVL : VL = geomLW W (fun _ => xL)) (hVR : VR = geomRW W (fun _ => xR))
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
        (∀ ω t, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω))
          (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (u ω t)) →
        ∀ z ∈ QuantumZipper.H,
          IsContLocalMartingaleBefore (usualAugmentation (Filtration.natural η hη) P) P
            (fun ω => ((min (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z)
              (continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
                (fun j s => VR j s ω)) : ℝ≥0∞) : WithTop ℝ≥0))
            (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω),
        MeasurePreserving π P' P ∧
        ∃ (𝓕' : Filtration ℝ≥0 mΩ') (B : ℝ≥0 → Ω' → ℝ),
          IsIntegratedSLEEvolution κ xL xR ρL ρR P' 𝓕' (fun t ω' => W t (π ω'))
            (fun i t ω' => VL i t (π ω')) (fun j t ω' => VR j t (π ω')) B
            (fun ω' => continuationThreshold ρL ρR (fun s => W s (π ω')) (fun i s => VL i s (π ω'))
              (fun j s => VR j s (π ω'))) := by
  subst hVL hVR
  set 𝓖 := usualAugmentation (Filtration.natural η hη) P with h𝓖
  set VL := geomLW W (fun _ : Ω => xL) with hVLd
  set VR := geomRW W (fun _ : Ω => xR) with hVRd
  have hT : ∀ ω, continuationThreshold ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun j s => VR j s ω) =
      MartChar.thresholdTime ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun j s => VR j s ω) :=
    fun ω => continuationThreshold_eq_thresholdTime _ _ _ _ _
  have hVLa : ∀ i, StronglyAdapted 𝓖 (VL i) := fun i => stronglyAdapted_geomLW hWa hWc measurable_const i
  have hVRa : ∀ j, StronglyAdapted 𝓖 (VR j) := fun j => stronglyAdapted_geomRW hWa hWc measurable_const j
  have hTst : IsStoppingTime 𝓖 (fun ω => (MartChar.thresholdTime ρL ρR (fun s => W s ω)
      (fun i s => VL i s ω) (fun j s => VR j s ω) : WithTop ℝ≥0)) := fun t =>
    MartChar.measurableSet_thresholdTime_le hWc (fun i ω => (isForcePath_geomLW hWc _ ω i).1)
      (fun j ω => (isForcePath_geomRW hWc _ ω j).1) hWa hVLa hVRa
      (fun ω i j s t hst h => geomLW_merge hWc _ ω i j s t hst h)
      (fun ω i j s t hst h => geomRW_merge hWc _ ω i j s t hst h) t
  have hmart' : ∀ z ∈ QuantumZipper.H, MartChar.IsLocalMartingaleBefore 𝓖 P
      (fun ω => min (QuantumZipper.swallowTime (MartChar.wpath W ω) z : WithTop ℝ≥0)
        (MartChar.thresholdTime ρL ρR (fun s => W s ω) (fun i s => VL i s ω) (fun j s => VR j s ω)))
      (MartChar.coupProc κ ρL ρR W VL VR z) := by
    intro z hz
    have h := hmart (fun ω t => MartChar.meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω))
      (fun ω t => MartChar.isBoundedHarmonicExtension_meanExt _ _ _ _ _ _) z hz
    simp only [hT] at h
    have hz0 : ∀ ω, z ≠ ((fun s : ℝ => W s.toNNReal ω) 0 : ℂ) := fun ω hzW => by
      have : (0 : ℝ) < z.im := hz
      rw [hzW] at this
      simp at this
    have hX0 : ∀ ω, MartChar.coupProc κ ρL ρR W VL VR z 0 ω =
        MartChar.meanExt κ ρL ρR 0 xL xR z := fun ω => by
      have hVL0 : (fun i => VL i 0 ω) = xL := funext fun i => geomLW_zero hWc hW0 (hF.2.1 i)
      have hVR0 : (fun j => VR j 0 ω) = xR := funext fun j => geomRW_zero hWc hW0 (hF.2.2.2 j)
      simp only [MartChar.coupProc, couplingMean, NNReal.coe_zero, QuantumZipper.logDerivFwd,
        intervalIntegral.integral_same, neg_zero, Complex.zero_im, mul_zero, sub_zero, hVL0, hVR0, hW0 ω]
      rw [show MartChar.wpath W ω = (fun s : ℝ => W s.toNNReal ω) from rfl,
        fwdMap_time_zero (fun s : ℝ => W s.toNNReal ω) (hz0 ω)]
      simp [hW0 ω]
    have hX0' : MartChar.coupProc κ ρL ρR W VL VR z 0 = fun _ => MartChar.meanExt κ ρL ρR 0 xL xR z :=
      funext hX0
    refine IsContLocalMartingaleBefore.isLocalMartingaleBefore h ?_ ?_
    · rw [hX0']
      exact stronglyMeasurable_const
    · rw [hX0']
      exact integrable_const _
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := Restart.ConverseBefore.isRandomWordEvolution_prod
    (𝒢 := ⊥) (F := Set.univ) hκ bot_le MeasurableSet.univ measurable_const measurable_const
    (fun _ => hF.2.1) (fun _ => hF.2.2.2) (fun _ => hF.1) (fun _ => hF.2.2.1) hW0 hWc hWa hTst hmart'
    (ae_of_all _ fun _ _ => le_rfl)
  obtain ⟨-, -, -, -, hB, hWb, hVLb, hVRb, hpath⟩ := hE
  refine ⟨Ω × (ℕ → ℝ), inferInstance, P.prod P₀, Prod.fst, measurePreserving_fst,
    WholeField.prodFiltration 𝓖 𝓦, B, ?_⟩
  simp only [continuationThreshold_eq_thresholdTime]
  exact ⟨hB, hWb, hVLb, hVRb, hpath.mono fun p hp => hp (Set.mem_preimage.2 (Set.mem_univ _))⟩

end Plumbing

end Certify2426

end InteractingSLE
