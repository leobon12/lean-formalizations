/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedMean

/-!
# The staged prefix's own mean, II: the chart after `k + 1` pieces is a Loewner chart of the concatenation

Packet PROVE-CROSSCOND-STAGED2. A staged prefix `α₁ ∪ ⋯ ∪ α_{k+1}` with pieces stopped at own times `T₀, …, T_k` is
read in the chart obtained from the root chart by the centred Loewner maps of the stopped pieces, one after the other
(`Chart.loewner`, the run's chart of a flow program, `Theorem14.GW2Schedule.succChart`). This file proves that this
iterated chart **is** the Loewner chart of the concatenated driver at the cumulative time (inverse maps on `ℍ`, forward
maps and lifts on the domain), by induction from the two-stage identities of `Sec7.StripSideHeightProb`
(`twoChart_inv_eq`, `twoChart_fwd_lift_eq`), and deduces the measurability of the iterated chart in any σ-algebra in
which the piece drivers are measurable (`Chart.loewnerChartAtTime`, `Lemma72D`):

* `cumT`, `catN`: the cumulative own times and the concatenated driver of the pieces `0, …, k`;
* `iterChart x₀ w T k`: the chart after the pieces `0, …, k` (root `x₀`); `catChartN x₀ w T k`: the recentred
  Loewner chart of `catN w T k` at `cumT T k`;
* **`iterChart_agree`**: the two agree (inverse on `ℍ`, forward map and lift on the domain);
* **`measurableSet_mem_dom_catChartN`**, **`measurable_indicator_fwd_catChartN`**,
  **`measurable_indicator_lift_catChartN`**, **`measurableSet_closedBall_subset_dom_catChartN`**: the measurability
  hypotheses of `ae_condExp_cexp_of_chartLaw` for `catChartN`.

Deterministic and measurability facts only; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Staged

open Sec7.StripSideHeightProb

/-! ### The concatenated driver and the iterated chart -/

section Det

/-- The cumulative own time of the pieces `0, …, k`. -/
def cumT (T : ℕ → ℝ≥0) (k : ℕ) : ℝ≥0 := ∑ j ∈ Finset.range (k + 1), T j

theorem cumT_zero (T : ℕ → ℝ≥0) : cumT T 0 = T 0 := by simp [cumT]

theorem cumT_succ (T : ℕ → ℝ≥0) (k : ℕ) : cumT T (k + 1) = cumT T k + T (k + 1) := by
  simp only [cumT]
  rw [Finset.sum_range_succ]

/-- The concatenated driver of the pieces `0, …, k`. -/
def catN (w : ℕ → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) : ℕ → ℝ≥0 → ℝ
  | 0 => w 0
  | k + 1 => catPath (catN w T k) (cumT T k) (w (k + 1))

/-- The chart after the pieces `0, …, k`: the recentring at the root `x₀`, then the centred Loewner maps of the
pieces (the recursion of `Chart.loewner`). -/
def iterChart (x₀ : ℝ) (w : ℕ → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) : ℕ → Chart
  | 0 => (Chart.id.recenter x₀).loewner (Ito.rpath (w 0)) (T 0)
  | k + 1 => (iterChart x₀ w T k).loewner (Ito.rpath (w (k + 1))) (T (k + 1))

/-- The recentred Loewner chart of the concatenated driver at the cumulative time. -/
def catChartN (x₀ : ℝ) (w : ℕ → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) (k : ℕ) : Chart :=
  (Chart.id.recenter x₀).loewner (Ito.rpath (catN w T k)) (cumT T k)

variable {w : ℕ → ℝ≥0 → ℝ} {T : ℕ → ℝ≥0}

theorem continuous_catN (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) :
    ∀ k, Continuous (catN w T k)
  | 0 => hc 0
  | k + 1 => continuous_catPath (continuous_catN hc h0 k) (hc (k + 1)) (h0 (k + 1))

theorem catN_zero (h0 : ∀ j, w j 0 = 0) : ∀ k, catN w T k 0 = 0
  | 0 => h0 0
  | k + 1 => catPath_zero (catN_zero h0 k)

theorem rpath_zero_of_zero {v : ℝ≥0 → ℝ} (h0 : v 0 = 0) : Ito.rpath v 0 = 0 := by simp [Ito.rpath, h0]

theorem continuous_rpath_of {v : ℝ≥0 → ℝ} (hc : Continuous v) : Continuous (Ito.rpath v) :=
  hc.comp continuous_real_toNNReal

/-- The recentred Loewner chart is the Loewner chart translated by the root: forward maps. -/
theorem recenter_loewner_fst (x₀ : ℝ) (W : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    ((Chart.id.recenter x₀).loewner W t).1 z = (Chart.id.loewner W t).1 (z - x₀) := rfl

theorem recenter_loewner_inv (x₀ : ℝ) (W : ℝ → ℝ) (t : ℝ) (y : ℂ) :
    ((Chart.id.recenter x₀).loewner W t).2.1 y = (Chart.id.loewner W t).2.1 y + x₀ := rfl

theorem recenter_loewner_lift (x₀ : ℝ) (W : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    ((Chart.id.recenter x₀).loewner W t).2.2 z = (Chart.id.loewner W t).2.2 (z - x₀) := rfl

theorem isConformal_recenter_loewner (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : ((Chart.id.recenter x₀).loewner W t).IsConformal :=
  (Chart.isConformal_id.recenter x₀).loewner hW hW0 ht

/-- **The domain of the recentred Loewner chart is the translate of the Loewner domain.** -/
theorem mem_dom_recenter_loewner_iff (x₀ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} :
    z ∈ ((Chart.id.recenter x₀).loewner W t).dom ↔ z - x₀ ∈ (Chart.id.loewner W t).dom := by
  rw [← SetLike.mem_coe, (isConformal_recenter_loewner x₀ hW hW0 ht).coe_dom, ← SetLike.mem_coe,
    (Chart.isConformal_id.loewner hW hW0 ht).coe_dom]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    rw [recenter_loewner_inv, add_sub_cancel_right]
  · rintro ⟨y, hy, hyz⟩
    refine ⟨y, hy, ?_⟩
    rw [recenter_loewner_inv, hyz, sub_add_cancel]

theorem isConformal_catChartN (x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) (k : ℕ) :
    (catChartN x₀ w T k).IsConformal :=
  isConformal_recenter_loewner x₀ (continuous_rpath_of (continuous_catN hc h0 k))
    (rpath_zero_of_zero (catN_zero h0 k)) (cumT T k).coe_nonneg

theorem isConformal_iterChart (x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) :
    ∀ k, (iterChart x₀ w T k).IsConformal
  | 0 => isConformal_recenter_loewner x₀ (continuous_rpath_of (hc 0)) (rpath_zero_of_zero (h0 0)) (T 0).coe_nonneg
  | k + 1 => (isConformal_iterChart x₀ hc h0 k).loewner (continuous_rpath_of (hc (k + 1)))
      (rpath_zero_of_zero (h0 (k + 1))) (T (k + 1)).coe_nonneg

theorem iterChart_zero_eq (x₀ : ℝ) : iterChart x₀ w T 0 = catChartN x₀ w T 0 := by
  simp only [iterChart, catChartN, catN, cumT_zero]

/-- **The iterated chart is the Loewner chart of the concatenation**: the inverse maps agree on `ℍ`, and the forward
maps and the lifts agree on the domain `inv '' ℍ`. -/
theorem iterChart_agree (x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) :
    ∀ k, (∀ y ∈ H, (iterChart x₀ w T k).2.1 y = (catChartN x₀ w T k).2.1 y) ∧
      ∀ z ∈ (catChartN x₀ w T k).2.1 '' H,
        (iterChart x₀ w T k).1 z = (catChartN x₀ w T k).1 z ∧
          (iterChart x₀ w T k).2.2 z = (catChartN x₀ w T k).2.2 z
  | 0 => by
    rw [iterChart_zero_eq]
    exact ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := iterChart_agree x₀ hc h0 k
    have hW := continuous_catN (T := T) hc h0 k
    have hW0 := catN_zero (T := T) h0 k
    have hw' := hc (k + 1)
    have hw'0 := h0 (k + 1)
    have hr' : Continuous (Ito.rpath (w (k + 1))) := continuous_rpath_of hw'
    have hr'0 : Ito.rpath (w (k + 1)) 0 = 0 := rpath_zero_of_zero hw'0
    -- the chart of the concatenation at `k + 1`, through `catChart`
    have hcat : ∀ y, (catChartN x₀ w T (k + 1)).2.1 y =
        (catChart (catN w T k) (cumT T k) (w (k + 1)) (T (k + 1))).2.1 y + x₀ := by
      intro y
      rw [catChartN, recenter_loewner_inv, cumT_succ]
      rfl
    have hcatf : ∀ z, (catChartN x₀ w T (k + 1)).1 z =
        (catChart (catN w T k) (cumT T k) (w (k + 1)) (T (k + 1))).1 (z - x₀) := by
      intro z
      rw [catChartN, recenter_loewner_fst, cumT_succ]
      rfl
    have hcatl : ∀ z, (catChartN x₀ w T (k + 1)).2.2 z =
        (catChart (catN w T k) (cumT T k) (w (k + 1)) (T (k + 1))).2.2 (z - x₀) := by
      intro z
      rw [catChartN, recenter_loewner_lift, cumT_succ]
      rfl
    have hinv : ∀ y ∈ H, (iterChart x₀ w T (k + 1)).2.1 y = (catChartN x₀ w T (k + 1)).2.1 y := by
      intro y hy
      have hv : fwdMapInv (Ito.rpath (w (k + 1))) (T (k + 1)) y ∈ H :=
        QuantumZipper.RS.fwdMapInv_mem_H hr' hr'0 (T (k + 1)).coe_nonneg hy
      change (iterChart x₀ w T k).2.1 (fwdMapInv (Ito.rpath (w (k + 1))) (T (k + 1)) y) = _
      rw [ih1 _ hv, hcat, ← twoChart_inv_eq hW hW0 hw' hw'0 hy]
      rfl
    refine ⟨hinv, fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hz
    set z' : ℂ := (catChart (catN w T k) (cumT T k) (w (k + 1)) (T (k + 1))).2.1 y with hz'
    have hzz : (catChartN x₀ w T (k + 1)).2.1 y - x₀ = z' := by rw [hcat, add_sub_cancel_right]
    have hcc : (catChart (catN w T k) (cumT T k) (w (k + 1)) (T (k + 1))).IsConformal :=
      Chart.isConformal_id.loewner (continuous_rpath_catPath hW hw' hw'0) (rpath_catPath_zero hW0)
        (cumT T k + T (k + 1)).coe_nonneg
    have hz'd : z' ∈ (catChart (catN w T k) (cumT T k) (w (k + 1)) (T (k + 1))).dom := by
      rw [← SetLike.mem_coe, hcc.coe_dom]
      exact mem_image_of_mem _ hy
    obtain ⟨hf, hl⟩ := twoChart_fwd_lift_eq hW hW0 hw' hw'0 hz'd
    -- the point is in the image of the chart at `k`
    have hv : fwdMapInv (Ito.rpath (w (k + 1))) (T (k + 1)) y ∈ H :=
      QuantumZipper.RS.fwdMapInv_mem_H hr' hr'0 (T (k + 1)).coe_nonneg hy
    have hzk : (catChartN x₀ w T (k + 1)).2.1 y =
        (catChartN x₀ w T k).2.1 (fwdMapInv (Ito.rpath (w (k + 1))) (T (k + 1)) y) := by
      rw [← ih1 _ hv, ← hinv y hy]
      rfl
    have hmem : (catChartN x₀ w T (k + 1)).2.1 y ∈ (catChartN x₀ w T k).2.1 '' H := by
      rw [hzk]
      exact mem_image_of_mem _ hv
    obtain ⟨e1, e2⟩ := ih2 _ hmem
    have hk1 : (catChartN x₀ w T k).1 ((catChartN x₀ w T (k + 1)).2.1 y) =
        (Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).1 z' := by
      change (Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).1 ((catChartN x₀ w T (k + 1)).2.1 y - x₀) = _
      rw [hzz]
    have hk2 : (catChartN x₀ w T k).2.2 ((catChartN x₀ w T (k + 1)).2.1 y) =
        (Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).2.2 z' := by
      change (Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).2.2
        ((catChartN x₀ w T (k + 1)).2.1 y - x₀) = _
      rw [hzz]
    refine ⟨?_, ?_⟩
    · change fwdMap (Ito.rpath (w (k + 1))) (T (k + 1)) ((iterChart x₀ w T k).1 _) = _
      rw [e1, hk1, hcatf, hzz, ← hf]
      rfl
    · change (logDerivFwd (Ito.rpath (w (k + 1))) (T (k + 1)) ((iterChart x₀ w T k).1 _)).im +
        (iterChart x₀ w T k).2.2 _ = _
      rw [e1, e2, hk1, hk2, hcatl, hzz, ← hl]
      change _ = (logDerivFwd (Ito.rpath (w (k + 1))) (T (k + 1))
          ((Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).1 z')).im + 0 +
        (Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).2.2 z'
      ring

/-- The domains of the iterated chart and of the chart of the concatenation coincide. -/
theorem iterChart_dom_eq (x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) (k : ℕ) :
    (iterChart x₀ w T k).dom = (catChartN x₀ w T k).dom := by
  have e : (iterChart x₀ w T k).2.1 '' H = (catChartN x₀ w T k).2.1 '' H :=
    image_congr fun y hy => (iterChart_agree x₀ hc h0 k).1 y hy
  ext z
  change z ∈ interior ((iterChart x₀ w T k).2.1 '' H) ↔ z ∈ interior ((catChartN x₀ w T k).2.1 '' H)
  rw [e]

/-- **A field read in the iterated chart is read in the chart of the concatenation.** -/
theorem isChartTransport_catChartN_of_iterChart (x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0)
    (k : ℕ) {σ a χ : ℝ} {h h' : LQGMetric.DistOn upperHalfPlaneOpens}
    (ht : IsChartTransport (iterChart x₀ w T k) σ a χ h h') :
    IsChartTransport (catChartN x₀ w T k) σ a χ h h' := by
  have hi := isConformal_iterChart (T := T) x₀ hc h0 k
  have himg : (iterChart x₀ w T k).2.1 '' H = (catChartN x₀ w T k).2.1 '' H :=
    image_congr fun y hy => (iterChart_agree x₀ hc h0 k).1 y hy
  refine isChartTransport_congr_dom hi.isOpen_image (iterChart_agree x₀ hc h0 k).1 (fun z hz => ?_)
    (fun z hz => ?_) ht
  · rw [himg] at hz
    exact ((iterChart_agree x₀ hc h0 k).2 z hz).1
  · rw [himg] at hz
    exact ((iterChart_agree x₀ hc h0 k).2 z hz).2

theorem continuousOn_lift_catChartN (x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) (k : ℕ) :
    ContinuousOn (catChartN x₀ w T k).2.2 (catChartN x₀ w T k).dom := by
  have hW := continuous_rpath_of (continuous_catN (T := T) hc h0 k)
  have hW0 := rpath_zero_of_zero (catN_zero (T := T) h0 k)
  have hl := Chart.continuousOn_lift_loewner hW hW0 (cumT T k).coe_nonneg
  have hcont : ContinuousOn (fun z : ℂ => (Chart.id.loewner (Ito.rpath (catN w T k)) (cumT T k)).2.2 (z - x₀))
      (catChartN x₀ w T k).dom :=
    hl.comp (continuous_id.sub continuous_const).continuousOn fun z hz =>
      (mem_dom_recenter_loewner_iff x₀ hW hW0 (cumT T k).coe_nonneg).1 hz
  exact hcont.congr fun z _ => recenter_loewner_lift x₀ _ _ z

end Det

/-! ### Measurability of the chart of the concatenation -/

section Meas

variable {Ω : Type*} (𝓗 : MeasurableSpace Ω) {W : ℕ → Ω → ℝ≥0 → ℝ} (T : ℕ → ℝ≥0)

/-- The domain of a centred Loewner chart is `ℍ` minus the hull. -/
theorem mem_dom_loewner_iff_mem_diff_hull {v : ℝ → ℝ} (hv : Continuous v) (hv0 : v 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} : z ∈ (Chart.id.loewner v t).dom ↔ z ∈ H \ fwdHull v t := by
  refine ⟨mem_H_diff_fwdHull_of_mem_dom hv hv0 ht, fun hz => ?_⟩
  rw [Chart.mem_dom_loewner_iff hv hv0 ht]
  exact ⟨hz.1, Ito.exists_isForwardSol_of_mem ht hz⟩

omit 𝓗 in
/-- **Closed-disc events of a centred Loewner domain at a deterministic time.** -/
theorem measurableSet_closedBall_subset_dom_loewner {V : ℝ≥0 → Ω → ℝ} (hVc : ∀ ω, Continuous fun s => V s ω)
    (hV0 : ∀ ω, V 0 ω = 0) {m : MeasurableSpace Ω} (hVm : ∀ s, Measurable[m] (V s)) (t : ℝ≥0) (z : ℂ) (ε : ℝ) :
    MeasurableSet[m] {ω | Metric.closedBall z ε ⊆ (Chart.id.loewner (Ito.rpath (V · ω)) t).dom} := by
  have hdr : ∀ ω, QuantumZipper.drive 1 V ω = Ito.rpath (V · ω) := fun ω => by
    funext s
    simp [QuantumZipper.drive, Ito.rpath]
  have hc : ∀ ω, Continuous (Ito.rpath (V · ω)) := fun ω => (hVc ω).comp continuous_real_toNNReal
  have hc0 : ∀ ω, Ito.rpath (V · ω) 0 = 0 := fun ω => by simp [Ito.rpath, hV0 ω]
  have e : {ω | Metric.closedBall z ε ⊆ (Chart.id.loewner (Ito.rpath (V · ω)) t).dom} =
      {ω | Metric.closedBall z ε ⊆ H ∧ Disjoint (Metric.closedBall z ε) (fwdHull (QuantumZipper.drive 1 V ω) t)} := by
    ext ω
    simp only [mem_ofPred_eq, hdr]
    constructor
    · intro hB
      exact ⟨fun y hy => ((mem_dom_loewner_iff_mem_diff_hull (hc ω) (hc0 ω) t.coe_nonneg).1 (hB hy)).1,
        Set.disjoint_left.2 fun y hy hK =>
          ((mem_dom_loewner_iff_mem_diff_hull (hc ω) (hc0 ω) t.coe_nonneg).1 (hB hy)).2 hK⟩
    · rintro ⟨hBH, hd⟩ y hy
      exact (mem_dom_loewner_iff_mem_diff_hull (hc ω) (hc0 ω) t.coe_nonneg).2 ⟨hBH hy, Set.disjoint_left.1 hd hy⟩
  rw [e]
  rcases lt_or_ge ε 0 with hε | hε
  · have : Metric.closedBall z ε = ∅ := Metric.closedBall_eq_empty.2 hε
    convert MeasurableSet.univ using 1
    ext ω
    simp only [this, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨empty_subset _, disjoint_bot_left⟩
  rcases hε.eq_or_lt with rfl | hε
  · have hdom := Chart.measurableSet_mem_dom_loewnerChartAtTime (mΩ := m) (𝓗 := m) (W := V)
      (τ := fun _ => t) le_rfl hVc hV0 measurable_const (fun s => hVm _) z
    convert hdom using 1
    ext ω
    simp only [Metric.closedBall_zero, singleton_subset_iff, disjoint_singleton_left, mem_ofPred_eq]
    rw [hdr, ← not_iff_not]
    simp only [not_and, not_not]
    change _ ↔ z ∉ (Chart.id.loewner (Ito.rpath (V · ω)) t).dom
    rw [mem_dom_loewner_iff_mem_diff_hull (hc ω) (hc0 ω) t.coe_nonneg]
    simp only [Set.mem_sdiff, not_and, not_not]
  rcases lt_or_ge ε z.im with hz | hz
  · refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.const _
    · exact Sec7.Lemma72D.measurableSet_disjoint_closedBall_fwdHull_real hVc t.coe_nonneg (fun s _ => hVm s) hε hz
  · have hB : ¬ Metric.closedBall z ε ⊆ H := by
      intro hB
      have hmem : z - (ε : ℂ) * Complex.I ∈ Metric.closedBall z ε := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      have := hB hmem
      simp only [H, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] at this
      linarith
    convert MeasurableSet.empty using 1
    ext ω
    simp only [hB, false_and, mem_ofPred_eq, mem_empty_iff_false]

variable {𝓗} (x₀ : ℝ) (hWc : ∀ j ω, Continuous (W j ω)) (hW0 : ∀ j ω, W j ω 0 = 0)
  (hWm : ∀ j s, Measurable[𝓗] fun ω => W j ω s)

/-- The concatenated driver family. -/
abbrev catV (W : ℕ → Ω → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) (k : ℕ) : ℝ≥0 → Ω → ℝ :=
  fun s ω => catN (fun j => W j ω) T k s

include hWm in
theorem measurable_catV_apply : ∀ (k : ℕ) (s : ℝ≥0), Measurable[𝓗] (catV W T k s)
  | 0, s => hWm 0 s
  | k + 1, s => by
    by_cases hs : s ≤ cumT T k
    · have e : catV W T (k + 1) s = catV W T k s := funext fun ω => catPath_of_le hs
      rw [e]
      exact measurable_catV_apply k s
    · have e : catV W T (k + 1) s = fun ω => catV W T k (cumT T k) ω + W (k + 1) ω (s - cumT T k) :=
        funext fun ω => by simp only [catV, catN, catPath, hs, ↓reduceIte]
      rw [e]
      exact (measurable_catV_apply k _).add (hWm _ _)

include hWc hW0 in
theorem continuous_catV (k : ℕ) (ω : Ω) : Continuous fun s => catV W T k s ω :=
  continuous_catN (fun j => hWc j ω) (fun j => hW0 j ω) k

include hW0 in
theorem catV_zero (k : ℕ) (ω : Ω) : catV W T k 0 ω = 0 := catN_zero (fun j => hW0 j ω) k

include hWc hW0 in
theorem mem_dom_catChartN_iff (k : ℕ) (ω : Ω) (z : ℂ) :
    z ∈ (catChartN x₀ (fun j => W j ω) T k).dom ↔
      z - x₀ ∈ (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom :=
  mem_dom_recenter_loewner_iff x₀ (continuous_rpath_of (continuous_catV T hWc hW0 k ω))
    (rpath_zero_of_zero (catV_zero T hW0 k ω)) (cumT T k).coe_nonneg

include hWc hW0 hWm

/-- **The domain events of the chart of the concatenation.** -/
theorem measurableSet_mem_dom_catChartN (k : ℕ) (z : ℂ) :
    MeasurableSet[𝓗] {ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom} := by
  have e : {ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom} =
      {ω | z - x₀ ∈ (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom} := by
    ext ω
    exact mem_dom_catChartN_iff T x₀ hWc hW0 k ω z
  rw [e]
  exact Chart.measurableSet_mem_dom_loewnerChartAtTime (mΩ := 𝓗) (W := catV W T k) (τ := fun _ => cumT T k)
    le_rfl (continuous_catV T hWc hW0 k) (catV_zero T hW0 k) measurable_const
    (fun _ => measurable_catV_apply T hWm k _) (z - x₀)

/-- **The masked forward maps of the chart of the concatenation.** -/
theorem measurable_indicator_fwd_catChartN (k : ℕ) (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom}.indicator
      fun ω => (catChartN x₀ (fun j => W j ω) T k).1 z) := by
  have e : ({ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom}.indicator
      fun ω => (catChartN x₀ (fun j => W j ω) T k).1 z) =
      {ω | z - x₀ ∈ (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom}.indicator
        fun ω => (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).1 (z - x₀) := by
    funext ω
    by_cases hz : z ∈ (catChartN x₀ (fun j => W j ω) T k).dom
    · rw [indicator_of_mem (show ω ∈ {ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom} from hz),
        indicator_of_mem (show ω ∈ {ω | z - x₀ ∈ (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom}
          from (mem_dom_catChartN_iff T x₀ hWc hW0 k ω z).1 hz)]
      rfl
    · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom} from hz),
        indicator_of_notMem (show ω ∉ {ω | z - x₀ ∈
          (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom} from
          fun h => hz ((mem_dom_catChartN_iff T x₀ hWc hW0 k ω z).2 h))]
  rw [e]
  exact Chart.measurable_indicator_fwd_loewnerChartAtTime (mΩ := 𝓗) (W := catV W T k) (τ := fun _ => cumT T k)
    le_rfl (continuous_catV T hWc hW0 k) (catV_zero T hW0 k) measurable_const
    (fun _ => measurable_catV_apply T hWm k _) (z - x₀)

/-- **The masked lifts of the chart of the concatenation.** -/
theorem measurable_indicator_lift_catChartN (k : ℕ) (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom}.indicator
      fun ω => (catChartN x₀ (fun j => W j ω) T k).2.2 z) := by
  have e : ({ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom}.indicator
      fun ω => (catChartN x₀ (fun j => W j ω) T k).2.2 z) =
      {ω | z - x₀ ∈ (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom}.indicator
        fun ω => (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).2.2 (z - x₀) := by
    funext ω
    by_cases hz : z ∈ (catChartN x₀ (fun j => W j ω) T k).dom
    · rw [indicator_of_mem (show ω ∈ {ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom} from hz),
        indicator_of_mem (show ω ∈ {ω | z - x₀ ∈ (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom}
          from (mem_dom_catChartN_iff T x₀ hWc hW0 k ω z).1 hz)]
      rfl
    · rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (catChartN x₀ (fun j => W j ω) T k).dom} from hz),
        indicator_of_notMem (show ω ∉ {ω | z - x₀ ∈
          (Chart.loewnerChartAtTime (catV W T k) (fun _ => cumT T k) ω).dom} from
          fun h => hz ((mem_dom_catChartN_iff T x₀ hWc hW0 k ω z).2 h))]
  rw [e]
  exact Chart.measurable_indicator_lift_loewnerChartAtTime (mΩ := 𝓗) (W := catV W T k) (τ := fun _ => cumT T k)
    le_rfl (continuous_catV T hWc hW0 k) (catV_zero T hW0 k) measurable_const
    (fun _ => measurable_catV_apply T hWm k _) (z - x₀)

/-- **Closed-disc events of the chart of the concatenation.** -/
theorem measurableSet_closedBall_subset_dom_catChartN (k : ℕ) (z : ℂ) (ε : ℝ) :
    MeasurableSet[𝓗] {ω | Metric.closedBall z ε ⊆ (catChartN x₀ (fun j => W j ω) T k).dom} := by
  have e : {ω | Metric.closedBall z ε ⊆ (catChartN x₀ (fun j => W j ω) T k).dom} =
      {ω | Metric.closedBall (z - x₀) ε ⊆ (Chart.id.loewner (Ito.rpath (catV W T k · ω)) (cumT T k)).dom} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · intro hB y hy
      have hy' : y + x₀ ∈ Metric.closedBall z ε := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
        rwa [show y + (x₀ : ℂ) - z = y - (z - x₀) by ring]
      have h := (mem_dom_catChartN_iff T x₀ hWc hW0 k ω (y + x₀)).1 (hB hy')
      rwa [add_sub_cancel_right] at h
    · intro hB y hy
      have hy' : y - x₀ ∈ Metric.closedBall (z - x₀) ε := by
        rw [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
        rwa [show y - (x₀ : ℂ) - (z - x₀) = y - z by ring]
      exact (mem_dom_catChartN_iff T x₀ hWc hW0 k ω y).2 (hB hy')
  rw [e]
  exact measurableSet_closedBall_subset_dom_loewner (continuous_catV T hWc hW0 k) (catV_zero T hW0 k)
    (measurable_catV_apply T hWm k) (cumT T k) (z - x₀) ε

end Meas

end InteractingSLE.Sec5.CrossCond.Staged
