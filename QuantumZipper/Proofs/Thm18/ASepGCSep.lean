import QuantumZipper.Proofs.Thm18.ASepGCEx
import Mathlib.MeasureTheory.Measure.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 7: the Borel separation sandwich `GCSepStmt`, and `GoodCMeasStmt`

With `R = revMap (backDrv W τ 0 a)` (a conformal injection of `ℍ` onto `G = R ℍ`, whose code
version is `psiF`), the hull is `A = ℍ \ G`. Let `T` be the (closed) support of the circle
measure `σ_i`. For `r = 1/(2(n+1))`:

* `SepD (1/(n+1))` (no point of `A` within `1/(n+1)` of a point of `T`, since `σ_i` charges
  every neighbourhood of a support point) implies that every compact piece
  `C_{n,m} = {w : dist(w, T) ≤ r, Im w ≥ 1/(m+1), |w| ≤ m+1}` lies in `G`;
* a compact `C ⊆ G` lies in `R(K_j)` for some compact `K_j ⊆ ℍ` (open mapping theorem, mathlib
  `AnalyticOnNhd.is_constant_or_isOpen`, directed cover), and `C ⊆ R(K_j)` is a countable
  condition in the code (`Cov`: countable dense subsets of `C` and `K_j`, `R(K_j)` closed);
* conversely `∀ m, ∃ j, Cov` gives `{w ∈ ℍ : dist(w, T) ≤ r} ⊆ G`, hence `SepD r`
  (`σ_i` does not charge the complement of its support, mathlib `Measure.measure_compl_support`).

So `S = {(c, τ, a, i, n) | ∀ m, ∃ j, Cov}` is a Borel sandwich: **`gcSepStmt_holds`**, and with
`GC.goodCMeasStmt_of_sep`: **`goodCMeasStmt_holds : GoodCMeasStmt`**.

Own elementary argument (descriptive-set bookkeeping the paper leaves implicit).
-/

noncomputable section

open MeasureTheory Set Function Filter Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

/-! ## Exhaustion of `ℍ` by compacts -/

/-- Open pieces of `ℍ`. -/
def Oj (j : ℕ) : Set ℂ := {ζ | ‖ζ‖ < (j : ℝ) + 1 ∧ 1 / ((j : ℝ) + 1) < ζ.im}

/-- Compact pieces of `ℍ`. -/
def Kj (j : ℕ) : Set ℂ := {ζ | ‖ζ‖ ≤ (j : ℝ) + 1 ∧ 1 / ((j : ℝ) + 1) ≤ ζ.im}

theorem Oj_subset_Kj (j : ℕ) : Oj j ⊆ Kj j := fun _ h => ⟨h.1.le, h.2.le⟩

theorem Kj_subset_H (j : ℕ) : Kj j ⊆ H := fun _ h =>
  lt_of_lt_of_le (by positivity) h.2

theorem isOpen_Oj (j : ℕ) : IsOpen (Oj j) :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem isCompact_Kj (j : ℕ) : IsCompact (Kj j) := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (j : ℝ) + 1)).subset fun z hz => ?_
  simpa [Metric.mem_closedBall, dist_zero_right] using hz.1

theorem monotone_Oj : Monotone Oj := by
  intro j j' h z hz
  have h' : (j : ℝ) ≤ j' := by exact_mod_cast h
  refine ⟨lt_of_lt_of_le hz.1 (by linarith), lt_of_le_of_lt ?_ hz.2⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem H_subset_iUnion_Oj : H ⊆ ⋃ j, Oj j := by
  intro z hz
  have hz' : 0 < z.im := hz
  obtain ⟨j1, hj1⟩ := exists_nat_gt ‖z‖
  obtain ⟨j2, hj2⟩ := exists_nat_one_div_lt hz'
  refine mem_iUnion.2 ⟨max j1 j2, ?_, ?_⟩
  · have : (j1 : ℝ) ≤ (max j1 j2 : ℕ) := by exact_mod_cast le_max_left j1 j2
    linarith
  · refine lt_of_le_of_lt ?_ hj2
    have : (j2 : ℝ) ≤ (max j1 j2 : ℕ) := by exact_mod_cast le_max_right j1 j2
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-! ## The compact pieces near the circle -/

theorem fcI_ne_zero (i : ℕ) : fcI i ≠ 0 := by
  haveI : IsProbabilityMeasure (fcI i) := by
    unfold fcI foldedCircle
    exact (Measure.isProbabilityMeasure_map_iff measurable_foldH.aemeasurable).2 inferInstance
  exact IsProbabilityMeasure.ne_zero _

/-- The compact pieces of `{w ∈ ℍ : dist(w, supp σ_i) ≤ 1/(2(n+1))}`. -/
def Cset (i n m : ℕ) : Set ℂ :=
  {w | infDist w (fcI i).support ≤ 1 / (2 * ((n : ℝ) + 1)) ∧ 1 / ((m : ℝ) + 1) ≤ w.im ∧
    ‖w‖ ≤ (m : ℝ) + 1}

theorem Cset_subset_H (i n m : ℕ) : Cset i n m ⊆ H := fun _ h =>
  lt_of_lt_of_le (by positivity) h.2.1

theorem isCompact_Cset (i n m : ℕ) : IsCompact (Cset i n m) := by
  refine Metric.isCompact_of_isClosed_isBounded
    ((isClosed_le (continuous_infDist_pt _) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le continuous_norm continuous_const))) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (m : ℝ) + 1)).subset fun z hz => ?_
  simpa [Metric.mem_closedBall, dist_zero_right] using hz.2.2

/-- Countable dense subsets. -/
def DC (i n m : ℕ) : Set ℂ := (TopologicalSpace.exists_countable_dense_subset (Cset i n m)).choose

def DK (j : ℕ) : Set ℂ := (TopologicalSpace.exists_countable_dense_subset (Kj j)).choose

theorem DC_spec (i n m : ℕ) :
    (DC i n m).Countable ∧ DC i n m ⊆ Cset i n m ∧ Cset i n m ⊆ closure (DC i n m) :=
  (TopologicalSpace.exists_countable_dense_subset (Cset i n m)).choose_spec

theorem DK_spec (j : ℕ) : (DK j).Countable ∧ DK j ⊆ Kj j ∧ Kj j ⊆ closure (DK j) :=
  (TopologicalSpace.exists_countable_dense_subset (Kj j)).choose_spec

/-- The countable covering condition `C_{n,m} ⊆ R(K_j)`. -/
def Cov (p : (ℕ → ℝ) × ℝ × ℝ) (i n m j : ℕ) : Prop :=
  ∀ w ∈ DC i n m, ∀ e : ℕ, ∃ ζ ∈ DK j, dist (psiF p ζ) w < 1 / ((e : ℝ) + 1)

theorem measurableSet_Cov (i n m j : ℕ) : MeasurableSet {p | Cov p i n m j} := by
  have e : {p | Cov p i n m j} = ⋂ w ∈ DC i n m, ⋂ e : ℕ, ⋃ ζ ∈ DK j,
      {p : (ℕ → ℝ) × ℝ × ℝ | dist (psiF p ζ) w < 1 / ((e : ℝ) + 1)} := by
    ext p; simp only [Cov, mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
  rw [e]
  refine MeasurableSet.biInter (DC_spec i n m).1 fun w _ => MeasurableSet.iInter fun e =>
    MeasurableSet.biUnion (DK_spec j).1 fun ζ _ => measurableSet_lt ?_ measurable_const
  have hζ : Measurable fun p : (ℕ → ℝ) × ℝ × ℝ => psiF p ζ :=
    Measurable.comp (g := fun s : ((ℕ → ℝ) × ℝ × ℝ) × ℂ => psiF s.1 s.2)
      (f := fun p : (ℕ → ℝ) × ℝ × ℝ => (p, ζ)) measurable_psiF
      (measurable_id.prodMk measurable_const)
  exact hζ.dist measurable_const

/-! ## The code reverse flow on `ℍ` -/

section Valid

variable {k : ℕ → ℝ} {τ a : ℝ}

theorem continuousOn_psiF (hτ : 0 ≤ τ) (ha : 0 < a) : ContinuousOn (psiF (k, τ, a)) H := by
  have hV : Continuous (revDrv (wg k) τ a).2 := by
    simp only [revDrv]; have := continuous_wg k; fun_prop
  have hT : 0 ≤ (revDrv (wg k) τ a).1 := by
    simp only [revDrv]; exact div_nonneg hτ (sq_nonneg a)
  exact ((differentiableOn_revMap _ hV hT).continuousOn).congr fun y hy =>
    psiF_eq_revMap hτ ha hy

theorem isOpen_image_psiF (hτ : 0 ≤ τ) (ha : 0 < a) {s : Set ℂ} (hs : s ⊆ H) (ho : IsOpen s) :
    IsOpen (psiF (k, τ, a) '' s) := by
  have hV : Continuous (revDrv (wg k) τ a).2 := by
    simp only [revDrv]; have := continuous_wg k; fun_prop
  have hT : 0 ≤ (revDrv (wg k) τ a).1 := by
    simp only [revDrv]; exact div_nonneg hτ (sq_nonneg a)
  set R := revMap (revDrv (wg k) τ a).2 (revDrv (wg k) τ a).1 with hR
  have himg : psiF (k, τ, a) '' s = R '' s :=
    Set.EqOn.image_eq fun y hy => psiF_eq_revMap hτ ha (hs hy)
  rw [himg]
  have hA : AnalyticOnNhd ℂ R H := (differentiableOn_revMap _ hV hT).analyticOnNhd isOpen_H'
  have hP : IsPreconnected H := (convex_halfSpace_im_gt 0).isPreconnected
  rcases hA.is_constant_or_isOpen hP with ⟨w, hw⟩ | h
  · exfalso
    have hI : Complex.I ∈ H := by show 0 < Complex.I.im; simp
    have h2I : (2 * Complex.I) ∈ H := by show 0 < (2 * Complex.I).im; simp
    have := injOn_revMap _ hV hT hI h2I ((hw _ hI).trans (hw _ h2I).symm)
    have h' := congrArg Complex.im this
    simp at h'
  · exact h s hs ho

theorem cov_of_subset (hτ : 0 ≤ τ) (ha : 0 < a) {i n m : ℕ}
    (hC : Cset i n m ⊆ psiF (k, τ, a) '' H) : ∃ j, Cov (k, τ, a) i n m j := by
  have hcov : Cset i n m ⊆ ⋃ j, psiF (k, τ, a) '' Oj j := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hC hw
    obtain ⟨j, hj⟩ := mem_iUnion.1 (H_subset_iUnion_Oj hz)
    exact mem_iUnion.2 ⟨j, z, hj, rfl⟩
  obtain ⟨j, hj⟩ := (isCompact_Cset i n m).elim_directed_cover _
    (fun j => isOpen_image_psiF hτ ha ((Oj_subset_Kj j).trans (Kj_subset_H j)) (isOpen_Oj j))
    hcov (Monotone.directed_le fun j j' h => image_mono (monotone_Oj h))
  refine ⟨j, fun w hw e => ?_⟩
  obtain ⟨ζ0, hζ0, hζw⟩ := hj ((DC_spec i n m).2.1 hw)
  have hζK : ζ0 ∈ Kj j := Oj_subset_Kj j hζ0
  have hcont := (continuousOn_psiF (k := k) hτ ha) ζ0 (Kj_subset_H j hζK)
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.1 hcont (1 / ((e : ℝ) + 1))
    (by positivity)
  obtain ⟨ζ, hζD, hζd⟩ := Metric.mem_closure_iff.1 ((DK_spec j).2.2 hζK) δ hδ
  refine ⟨ζ, hζD, ?_⟩
  rw [← hζw]
  exact hδf (Kj_subset_H j ((DK_spec j).2.1 hζD)) (by rw [dist_comm]; exact hζd)

theorem subset_of_cov (hτ : 0 ≤ τ) (ha : 0 < a) {i n m j : ℕ} (h : Cov (k, τ, a) i n m j) :
    Cset i n m ⊆ psiF (k, τ, a) '' Kj j := by
  have hcl : IsClosed (psiF (k, τ, a) '' Kj j) :=
    ((isCompact_Kj j).image_of_continuousOn
      ((continuousOn_psiF hτ ha).mono (Kj_subset_H j))).isClosed
  refine (DC_spec i n m).2.2.trans (closure_minimal (fun w hw => ?_) hcl)
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨ζ, hζD, hζ⟩ := h w hw e
  exact ⟨psiF (k, τ, a) ζ, ⟨ζ, (DK_spec j).2.1 hζD, rfl⟩, by rw [dist_comm]; linarith⟩

end Valid

/-! ## The sandwich -/

theorem revHull_backDrv_eq (κ : ℝ) {x : ℝ≥0 → ℝ} (hx : Continuous x) {τ a : ℝ} (hτ : 0 ≤ τ)
    (ha : 0 < a) :
    revHull (backDrv (pathDrive κ x) τ 0 a).2 (backDrv (pathDrive κ x) τ 0 a).1 =
      H \ psiF (kcode κ (codeP x), τ, a) '' H := by
  rw [backDrv_zero, ← revDrv_sub_const (pathDrive κ x) (pathDrive κ x 0), ← wg_kcode hx,
    revHull]
  congr 1
  exact (Set.EqOn.image_eq fun y hy => psiF_eq_revMap hτ ha hy).symm

/-- **The Borel separation sandwich holds.** -/
theorem gcSepStmt_holds : GCSepStmt := by
  intro γ _ _
  set κ := γ ^ 2
  refine ⟨{s | ∀ m : ℕ, ∃ j : ℕ, Cov (kcode κ s.1, s.2.1, s.2.2.1) s.2.2.2.1 s.2.2.2.2 m j},
    ?_, ?_⟩
  · refine measurableSet_setOfPred.2 (Measurable.forall fun m => Measurable.exists fun j =>
      measurableSet_setOfPred.1 ?_)
    have e : {s : (ℕ → ℝ) × (ℝ × ℝ × ℕ × ℕ) |
        Cov (kcode κ s.1, s.2.1, s.2.2.1) s.2.2.2.1 s.2.2.2.2 m j} =
        ⋃ i : ℕ, ⋃ n : ℕ, {s : (ℕ → ℝ) × (ℝ × ℝ × ℕ × ℕ) | s.2.2.2.1 = i ∧ s.2.2.2.2 = n} ∩
          (fun s : (ℕ → ℝ) × (ℝ × ℝ × ℕ × ℕ) => (kcode κ s.1, s.2.1, s.2.2.1)) ⁻¹'
            {p | Cov p i n m j} := by
      ext s
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
      exact ⟨fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩, fun ⟨i, n, ⟨hi, hn⟩, h⟩ => hi ▸ hn ▸ h⟩
    rw [e]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
    · exact (measurableSet_eq_fun measurable_snd.snd.snd.fst measurable_const).inter
        (measurableSet_eq_fun measurable_snd.snd.snd.snd measurable_const)
    · exact (measurableSet_Cov i n m j).preimage (((measurable_kcode κ).comp measurable_fst).prodMk
        (measurable_snd.fst.prodMk measurable_snd.snd.fst))
  intro x hx τ a hτ ha i n
  have hA := revHull_backDrv_eq κ hx hτ.le ha
  set p : (ℕ → ℝ) × ℝ × ℝ := (kcode κ (codeP x), τ, a) with hp
  have hsupp : (fcI i).support.Nonempty := Measure.nonempty_support (fcI_ne_zero i)
  have hr : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have hrn : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
    apply one_div_lt_one_div_of_lt (by positivity); linarith
  constructor
  · intro hsep m
    refine cov_of_subset hτ.le ha fun w hw => ?_
    by_contra hwG
    have hwA : w ∈ revHull (backDrv (pathDrive κ x) τ 0 a).2
        (backDrv (pathDrive κ x) τ 0 a).1 := by
      rw [hA]; exact ⟨Cset_subset_H i n m hw, hwG⟩
    obtain ⟨s, hs, hsw⟩ := (infDist_lt_iff hsupp).1 (lt_of_le_of_lt hw.1 hrn)
    have hsT : s ∈ thickening (1 / ((n : ℝ) + 1))
        (revHull (backDrv (pathDrive κ x) τ 0 a).2 (backDrv (pathDrive κ x) τ 0 a).1) :=
      mem_thickening_iff.2 ⟨w, hwA, by rw [dist_comm]; exact hsw⟩
    have hpos := (Measure.mem_support_iff_forall s).1 hs _
      (isOpen_thickening.mem_nhds hsT)
    exact absurd hsep (ne_of_gt hpos)
  · intro hS
    refine ⟨1 / (2 * ((n : ℝ) + 1)), hr, ?_⟩
    refine measure_mono_null (fun s hs => ?_) (Measure.measure_compl_support (μ := fcI i))
    intro hsT
    obtain ⟨z, hzA, hzs⟩ := mem_thickening_iff.1 hs
    rw [hA] at hzA
    obtain ⟨hzH, hzG⟩ := hzA
    have hz' : 0 < z.im := hzH
    obtain ⟨m1, hm1⟩ := exists_nat_gt ‖z‖
    obtain ⟨m2, hm2⟩ := exists_nat_one_div_lt hz'
    set m := max m1 m2
    have hm1' : (m1 : ℝ) ≤ m := by exact_mod_cast le_max_left m1 m2
    have hm2' : (m2 : ℝ) ≤ m := by exact_mod_cast le_max_right m1 m2
    have hzC : z ∈ Cset i n m := by
      refine ⟨?_, ?_, by linarith⟩
      · exact (infDist_le_dist_of_mem hsT).trans (by rw [dist_comm]; exact hzs.le)
      · refine le_trans ?_ hm2.le
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
    obtain ⟨j, hj⟩ := hS m
    obtain ⟨ζ, hζ, hζz⟩ := subset_of_cov hτ.le ha hj hzC
    exact hzG ⟨ζ, Kj_subset_H j hζ, hζz⟩

/-- **`GoodCMeasStmt` holds.** -/
theorem goodCMeasStmt_holds : GoodCMeasStmt :=
  goodCMeasStmt_of_sep gcSepStmt_holds

end GC
end ASep
end QuantumZipper
