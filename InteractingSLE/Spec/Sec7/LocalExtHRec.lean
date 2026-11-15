/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.HistBorel
import InteractingSLE.Spec.Sec7.LocalExtFStmt
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit

/-!
# Aux. lemma 54: the record of a stopped coupling (history and field off the hull)

Packet PROVE-LOCEXT-H. Aux. lemma 54 (specification p. 246) samples the future of a stopped coupling from one fixed
reference coupling, conditionally on a **record** of the stopped coupling: "Record the entire stopped driving history,
including `S`, … and map its active field to `ℍ` … The pair has exactly the same joint law in the stopped coupling and
in the fixed full reference coupling". Instead of the conformally mapped active field we record the field itself on
every test function whose support avoids the hull `K_S` (the same information: the active field is the field off the
hull, and conversely), which needs no conformal transport:

* `tsHist`: a two-seed history read at the dyadic times, as a history of `Sec4` (`HistorySpace 1 1`); `tsHull y`, the
  hull at the recorded stop along the regularized driver (`Sec4.regHull`), with measurable avoidance events
  (`measurableSet_disjoint_tsHull`);
* `fieldRec x y : TestOn → ℝ`: `ψ ↦ x(ψ)` if `supp ψ` avoids `tsHull y`, `0` otherwise; the record
  `recOf x y = (y, fieldRec x y)` on `RecSp = TwoSeedHist × (TestOn → ℝ)` (product σ-algebra), jointly measurable
  (`measurable_recOf`);
* `tsOf S X`: the history of a two-seed state `X` stopped at a finite time `S`; for `X` continuous on `[0, S]` the
  history read from it is continuous (`isContHist_tsHist_tsOf`), its driver is `X₁(· ∧ S)` (`histPath_tsHist_tsOf`), its
  force coordinates are those of `X S` (`histVL_tsHist_tsOf`, `histVR_tsHist_tsOf`), and its hull is the hull of any
  driver `w` that agrees with `X₁` on `[0, S]` and is continuous a little beyond `S` (`tsHull_tsOf_eq`);
* `twoSeedProj_stoppedHistory_eq_tsOf`, `seedProj_stoppedHistory_eq_tsOf`: the two-seed stopped histories of the stopped
  coupling and of the reference are of this form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec4 LawUnique LQGMetric

/-! ### Two-seed histories as histories of `Sec4` -/

/-- The dyadic rational `k / 2ⁿ` of `p = (n, k)`. -/
def dyadicQ (p : ℕ × ℕ) : ℚ≥0 := (p.2 : ℚ≥0) / 2 ^ p.1

theorem coe_dyadicQ (p : ℕ × ℕ) : ((dyadicQ p : ℚ≥0) : ℝ≥0) = dyadicTime p := by
  simp only [dyadicQ, dyadicTime, NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat]

/-- **A two-seed history read at the dyadic times**, as a history of `Sec4` (the recorded stop, `0` if infinite, and
the recorded states). -/
def tsHist (y : TwoSeedHist) : HistorySpace 1 1 :=
  (((y.1.untopD 0 : ℝ≥0) : ℝ≥0∞), fun p => y.2 (dyadicQ p))

theorem measurable_tsHist : Measurable tsHist :=
  (measurable_coe_nnreal_ennreal.comp ((WithTop.measurable_untopD 0).comp measurable_fst)).prodMk
    (Measurable.of_eval fun p => (measurable_pi_apply (dyadicQ p)).comp measurable_snd)

/-- **The hull read from a two-seed history** (at its recorded stop, along the regularized driver, closed in `ℍ`). -/
def tsHull (y : TwoSeedHist) : Set ℂ := regHull (tsHist y)

theorem measurableSet_disjoint_tsHull {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {y : TwoSeedHist | Disjoint K (tsHull y)} :=
  measurable_tsHist (measurableSet_disjoint_regHull hK)

/-! ### The record -/

open Classical in
/-- **The field off the hull**: the pairing `x(ψ)` of every test function whose support avoids `tsHull y`, and `0` on
the others. -/
def fieldRec (x : DistOn upperHalfPlaneOpens) (y : TwoSeedHist) : TestOn upperHalfPlaneOpens → ℝ :=
  fun ψ => if Disjoint (tsupport ψ) (tsHull y) then x ψ else 0

/-- The record space: a two-seed history and the field off its hull (product σ-algebra). -/
abbrev RecSp : Type := TwoSeedHist × (TestOn upperHalfPlaneOpens → ℝ)

/-- **The record** of a field and a two-seed history. -/
def recOf (x : DistOn upperHalfPlaneOpens) (y : TwoSeedHist) : RecSp := (y, fieldRec x y)

theorem measurable_fieldRec_apply (ψ : TestOn upperHalfPlaneOpens) :
    Measurable fun p : DistOn upperHalfPlaneOpens × TwoSeedHist => fieldRec p.1 p.2 ψ := by
  classical
  have hs : MeasurableSet {p : DistOn upperHalfPlaneOpens × TwoSeedHist | Disjoint (tsupport ψ) (tsHull p.2)} :=
    measurable_snd (measurableSet_disjoint_tsHull ψ.hasCompactSupport.isCompact)
  exact Measurable.ite hs ((measurable_distOn_apply ψ).comp measurable_fst) measurable_const

theorem measurable_recOf : Measurable fun p : DistOn upperHalfPlaneOpens × TwoSeedHist => recOf p.1 p.2 :=
  measurable_snd.prodMk (Measurable.of_eval fun ψ => measurable_fieldRec_apply ψ)

theorem fieldRec_of_disjoint {x : DistOn upperHalfPlaneOpens} {y : TwoSeedHist} {ψ : TestOn upperHalfPlaneOpens}
    (h : Disjoint (tsupport ψ) (tsHull y)) : fieldRec x y ψ = x ψ := by
  classical
  simp only [fieldRec, h, ↓reduceIte]

/-! ### Histories of a stopped two-seed state -/

/-- **The two-seed history of a state `X` stopped at the finite time `S`**. -/
def tsOf (S : ℝ≥0) (X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)) : TwoSeedHist :=
  ((S : WithTop ℝ≥0), fun q => X (min (q : ℝ≥0) S))

variable {S : ℝ≥0} {X : ℝ≥0 → ℝ × (Fin 1 → ℝ) × (Fin 1 → ℝ)}

theorem tsHist_tsOf_fst : (tsHist (tsOf S X)).1 = (S : ℝ≥0∞) := by
  simp only [tsHist, tsOf, WithTop.untopD_coe]

theorem histStop_tsHist_tsOf : histStop (tsHist (tsOf S X)) = S := by
  simp only [histStop, tsHist_tsOf_fst, ENNReal.toNNReal_coe]

theorem tsHist_tsOf_snd (p : ℕ × ℕ) : (tsHist (tsOf S X)).2 p = X (min (dyadicTime p) S) := by
  simp only [tsHist, tsOf, coe_dyadicQ]

/-- A state continuous on `[0, S]`, stopped at `S`, is continuous. -/
theorem continuous_stop_of_continuousOn (hX : ContinuousOn X (Iic S)) : Continuous fun t => X (min t S) :=
  hX.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t S

/-- **The history of a continuous stopped state is continuous.** -/
theorem isContHist_tsHist_tsOf (hX : ContinuousOn X (Iic S)) : IsContHist (tsHist (tsOf S X)) := by
  refine ⟨by rw [tsHist_tsOf_fst]; exact ENNReal.coe_ne_top, fun t => X (min t S),
    continuous_stop_of_continuousOn hX, fun p _ => tsHist_tsOf_snd p⟩

/-- The value at the lower dyadic approximations of `r ≤ S` converges to `X r`. -/
theorem tendsto_lowerDyadic_tsOf (hX : ContinuousOn X (Iic S)) {r : ℝ≥0} (hr : r ≤ S) :
    Tendsto (fun n => (tsHist (tsOf S X)).2 (lowerDyadic r n)) atTop (𝓝 (X r)) := by
  have heq : (fun n => (tsHist (tsOf S X)).2 (lowerDyadic r n)) = fun n => X (dyadicTime (lowerDyadic r n)) := by
    funext n
    rw [tsHist_tsOf_snd, min_eq_left ((dyadicTime_lowerDyadic_le r n).trans hr)]
  rw [heq]
  exact (hX r hr).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicTime_lowerDyadic r,
    Eventually.of_forall fun n => (dyadicTime_lowerDyadic_le r n).trans hr⟩)

/-- **The driver read from the history** is `X₁(t ∧ S)`. -/
theorem histPath_tsHist_tsOf (hX : ContinuousOn X (Iic S)) (t : ℝ≥0) :
    histPath (tsHist (tsOf S X)) t = (X (min t S)).1 := by
  unfold histPath
  rw [show (tsHist (tsOf S X)).1.toNNReal = S from histStop_tsHist_tsOf]
  exact ((continuous_fst.tendsto _).comp (tendsto_lowerDyadic_tsOf hX (min_le_right t S))).limUnder_eq

theorem histVL_tsHist_tsOf (hX : ContinuousOn X (Iic S)) (i : Fin 1) :
    histVL (tsHist (tsOf S X)) i = (X S).2.1 i := by
  unfold histVL
  rw [show (tsHist (tsOf S X)).1.toNNReal = S from histStop_tsHist_tsOf]
  exact (((continuous_apply i).comp (continuous_fst.comp continuous_snd)).tendsto _ |>.comp
    (tendsto_lowerDyadic_tsOf hX le_rfl)).limUnder_eq

theorem histVR_tsHist_tsOf (hX : ContinuousOn X (Iic S)) (i : Fin 1) :
    histVR (tsHist (tsOf S X)) i = (X S).2.2 i := by
  unfold histVR
  rw [show (tsHist (tsOf S X)).1.toNNReal = S from histStop_tsHist_tsOf]
  exact (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).tendsto _ |>.comp
    (tendsto_lowerDyadic_tsOf hX le_rfl)).limUnder_eq

/-- The driver of the history as a real path. -/
theorem histDrive_tsHist_tsOf (hX : ContinuousOn X (Iic S)) :
    histDrive (tsHist (tsOf S X)) = fun r : ℝ => (X (min r.toNNReal S)).1 := by
  funext r
  exact histPath_tsHist_tsOf hX r.toNNReal

/-- The hull read from the history of a continuous stopped state is the closure in `ℍ` of the hull of its (continuous)
driver at `S`. -/
theorem tsHull_tsOf (hX : ContinuousOn X (Iic S)) :
    tsHull (tsOf S X) = closure (fwdHull (histDrive (tsHist (tsOf S X))) S) ∩ (upperHalfPlaneOpens : Set ℂ) := by
  rw [tsHull, (isContHist_tsHist_tsOf hX).regHull_eq, histHull,
    show (tsHist (tsOf S X)).1.toNNReal = S from histStop_tsHist_tsOf]

theorem continuous_histDrive_tsOf (hX : ContinuousOn X (Iic S)) : Continuous (histDrive (tsHist (tsOf S X))) := by
  rw [histDrive_tsHist_tsOf hX]
  exact continuous_fst.comp ((continuous_stop_of_continuousOn hX).comp continuous_real_toNNReal)

/-- The hull of the history's driver at `S` is the hull at `S` of every driver `w` that agrees with `X₁` on `[0, S]` and
is continuous before some `a > S`. -/
theorem fwdHull_histDrive_tsOf (hX : ContinuousOn X (Iic S)) {w : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hSa : (S : ℝ≥0∞) < a)
    (hw : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < a}) (hwX : ∀ t ≤ S, (X t).1 = w t) :
    fwdHull (fun r : ℝ => w r.toNNReal) S = fwdHull (histDrive (tsHist (tsOf S X))) S := by
  obtain ⟨t₂, hSt₂, ht₂a⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hSa
  have hSt₂' : S < t₂ := by exact_mod_cast hSt₂
  set V : ℝ → ℝ := fun r => w (min r.toNNReal t₂) with hVdef
  have hVc : Continuous V :=
    (hw.comp_continuous (continuous_id.min continuous_const) fun t =>
      lt_of_le_of_lt (by exact_mod_cast min_le_right t t₂) ht₂a).comp continuous_real_toNNReal
  have h1 : fwdHull (fun r : ℝ => w r.toNNReal) S = fwdHull V S := by
    refine fwdHull_eq_of_eqOn S.coe_nonneg (by exact_mod_cast hSt₂') fun r hr => ?_
    simp only [hVdef]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  rw [h1]
  refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc hVc (continuous_histDrive_tsOf hX) S.coe_nonneg fun r hr => ?_
  rw [histDrive_tsHist_tsOf hX]
  simp only [hVdef]
  have hrS : r.toNNReal ≤ S := Real.toNNReal_le_iff_le_coe.2 hr.2
  rw [min_eq_left (hrS.trans hSt₂'.le), min_eq_left hrS, hwX _ hrS]

/-- **The hull read from the history of a continuous stopped state** is the closure in `ℍ` of the hull at `S` of every
driver `w` that agrees with `X₁` on `[0, S]` and is continuous before some `a > S`. -/
theorem tsHull_tsOf_eq (hX : ContinuousOn X (Iic S)) {w : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hSa : (S : ℝ≥0∞) < a)
    (hw : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < a}) (hwX : ∀ t ≤ S, (X t).1 = w t) :
    tsHull (tsOf S X) = closure (fwdHull (fun r : ℝ => w r.toNNReal) S) ∩ (upperHalfPlaneOpens : Set ℂ) := by
  rw [tsHull_tsOf hX, fwdHull_histDrive_tsOf hX hSa hw hwX]

/-- **A set of `ℍ` that misses the hull of the driver at `S` misses the hull read from the history.** -/
theorem disjoint_tsHull_tsOf (hX : ContinuousOn X (Iic S)) {w : ℝ≥0 → ℝ} {a : ℝ≥0∞} (hSa : (S : ℝ≥0∞) < a)
    (hw : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < a}) (hwX : ∀ t ≤ S, (X t).1 = w t) {K : Set ℂ} (hKH : K ⊆ H)
    (hK : Disjoint K (fwdHull (fun r : ℝ => w r.toNNReal) S)) : Disjoint K (tsHull (tsOf S X)) := by
  rw [tsHull_tsOf hX]
  rw [fwdHull_histDrive_tsOf hX hSa hw hwX] at hK
  refine Set.disjoint_left.2 fun z hzK hzA => ?_
  have hzc : z ∈ H \ fwdHull (histDrive (tsHist (tsOf S X))) S :=
    ⟨hKH hzK, fun h => Set.disjoint_left.1 hK hzK h⟩
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzA.1 _
    (FwdHolo.isOpen_compl_fwdHull (continuous_histDrive_tsOf hX) S.coe_nonneg) hzc
  exact hy1.2 hy2

end LocalExt

end InteractingSLE
