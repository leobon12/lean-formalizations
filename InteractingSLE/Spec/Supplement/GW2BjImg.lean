/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BjRead
import InteractingSLE.Spec.Supplement.GW2SdgNear

/-!
# The image state is a measurable functional of the path (near facts, piece 1; decision D12 item 4)

Packet PROVE-GW2-BUF (round 7). `GW2Sdg.imgState xL xR w t` is built from the real Loewner images `rightImg`, whose
values are chosen positive solutions. Through the measurable regularized-flow readout `regFlowRead` (Bernstein drivers),
this file gives measurable path readouts that agree with the real objects on paths continuous on `[0, T]`:

* `aliveRead T y w` (`Alive` through rational times and levels `1/(n+1)`), **`measurableSet_aliveRead`**,
  **`aliveRead_iff`**;
* `gImgRead T y w` (the image `g_T(y)` through the eventually constant regularized flows), **`measurable_gImgRead`**,
  **`gImgRead_eq`**;
* `rightImgRead T x w` (the infimum over rational alive points, in `EReal`), **`measurable_rightImgRead`**,
  **`rightImgRead_eq`**;
* **`imgStateRead`**, **`measurable_imgStateRead`**, **`imgStateRead_eq`** (the image state at `T` of a path continuous
  on `[0, T]`), and causality **`imgStateRead_congr`**.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow

/-! ### The readout at the horizon `0` -/

theorem bdrv_zero (n : ℕ) (w : ℝ≥0 → ℝ) : bdrv 0 n w = frozenDrive w (0 : ℝ≥0) := by
  funext s
  have hg : ∀ k : Fin (n + 1), gridTime 0 k = 0 := fun k => by
    unfold gridTime
    exact zero_mul _
  have h0 : (min s ((0 : ℝ≥0) : ℝ)).toNNReal = 0 := by
    rw [NNReal.coe_zero]
    exact Real.toNNReal_of_nonpos (min_le_right _ _)
  have hl : bdrv 0 n w s = ∑ k : Fin (n + 1), bernstein n k (unitTime 0 s) * w 0 := by
    unfold bdrv bsum gridVals
    exact Finset.sum_congr rfl fun k _ => by rw [hg k]
  rw [hl, ← Finset.sum_mul, bernstein.probability, one_mul]
  unfold frozenDrive
  rw [h0]

theorem lipRead_zero (Φ : (ℝ → ℝ) → ℝ) (w : ℝ≥0 → ℝ) : lipRead 0 Φ w = Φ (frozenDrive w (0 : ℝ≥0)) := by
  unfold lipRead
  simp only [bdrv_zero]
  exact limsup_const _

/-- **The readout on a path continuous on `[0, T]`**, every horizon. -/
theorem lipRead_eq' {T : ℝ≥0} {Φ : (ℝ → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C) (hΦ : UnifLip T Φ C)
    {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) : lipRead T Φ w = Φ (frozenDrive w T) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h0 | hT
  · subst h0
    exact lipRead_zero Φ w
  · exact lipRead_eq hT hC hΦ hw

theorem regFlowRead_eq' {T : ℝ≥0} {ε : ℝ} (hε : 0 < ε) (y : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T)
    {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) :
    regFlowRead T ε y s w = regFlow (frozenDrive w T) ε y s :=
  lipRead_eq' (by positivity) (unifLip_regFlow hε y hs) hw

theorem continuous_frozenDrive' {T : ℝ≥0} {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) :
    Continuous (frozenDrive w T) :=
  continuous_frozenDrive (by rwa [Real.toNNReal_coe])

/-! ### Alive points -/

/-- A lower bound at rational times and at `T` is a lower bound on `[0, T]`, for a continuous function. -/
theorem forall_Icc_of_rat {f : ℝ → ℝ} {T c : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hq : ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T → c ≤ f q) (hT : c ≤ f T) : ∀ s ∈ Icc (0 : ℝ) T, c ≤ f s := by
  intro s hs
  rcases hs.2.eq_or_lt with h | hlt
  · rw [h]; exact hT
  by_contra hn'
  have hn : f s < c := not_le.1 hn'
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 (hf s hs) (c - f s) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < min (s + δ) T from lt_min (by linarith) hlt)
  have hqI : (q : ℝ) ∈ Icc (0 : ℝ) T := ⟨hs.1.trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
  have hd : dist (q : ℝ) s < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    linarith [min_le_left (s + δ) T]
  have h1 := hball hqI hd
  rw [Real.dist_eq] at h1
  have h2 := hq q hqI
  linarith [(abs_lt.1 h1).2]

/-- **`Alive` read from the path**: a level `1/(n+1)` below the regularized flow at rational times and at `T`. -/
def aliveRead (T : ℝ≥0) (y : ℝ) (w : ℝ≥0 → ℝ) : Prop :=
  ∃ n : ℕ, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T → 1 / ((n : ℝ) + 1) ≤ regFlowRead T (1 / ((n : ℝ) + 1)) y q w) ∧
    1 / ((n : ℝ) + 1) ≤ regFlowRead T (1 / ((n : ℝ) + 1)) y T w

theorem measurableSet_aliveRead (T : ℝ≥0) (y : ℝ) : MeasurableSet {w : ℝ≥0 → ℝ | aliveRead T y w} := by
  classical
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have he : {w : ℝ≥0 → ℝ | aliveRead T y w} = ⋃ n : ℕ,
      ((⋂ q : ℚ, if (q : ℝ) ∈ Icc (0 : ℝ) T then
          {w | 1 / ((n : ℝ) + 1) ≤ regFlowRead T (1 / ((n : ℝ) + 1)) y q w} else univ) ∩
        {w | 1 / ((n : ℝ) + 1) ≤ regFlowRead T (1 / ((n : ℝ) + 1)) y T w}) := by
    ext w
    simp only [aliveRead, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
    refine exists_congr fun n => and_congr_left' (forall_congr' fun q => ?_)
    by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
    · simp only [hq, ↓reduceIte, mem_ofPred_eq, true_imp_iff]
    · simp only [hq, ↓reduceIte, mem_univ, false_imp_iff]
  rw [he]
  refine MeasurableSet.iUnion fun n => (MeasurableSet.iInter fun q => ?_).inter ?_
  · by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
    · simp only [hq, ↓reduceIte]
      exact measurableSet_le measurable_const (measurable_regFlowRead T (hε n) y hq)
    · simp only [hq, ↓reduceIte]
      exact MeasurableSet.univ
  · exact measurableSet_le measurable_const (measurable_regFlowRead T (hε n) y ⟨T.coe_nonneg, le_rfl⟩)

/-- **`aliveRead` is `Alive` of the frozen driver** on paths continuous on `[0, T]`. -/
theorem aliveRead_iff {T : ℝ≥0} (y : ℝ) {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) :
    aliveRead T y w ↔ Alive (frozenDrive w T) y T := by
  have hu := continuous_frozenDrive' hw
  rw [alive_iff_regFlow hu T.coe_nonneg]
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  constructor
  · rintro ⟨n, hq, hT⟩
    refine ⟨n, forall_Icc_of_rat ((continuousOn_regFlow hu (hε n) y).mono fun s hs => hs.1)
      (fun q hq' => ?_) ?_⟩
    · rw [← regFlowRead_eq' (hε n) y hq' hw]
      exact hq q hq'
    · rw [← regFlowRead_eq' (hε n) y ⟨T.coe_nonneg, le_rfl⟩ hw]
      exact hT
  · rintro ⟨n, h⟩
    refine ⟨n, fun q hq => ?_, ?_⟩
    · rw [regFlowRead_eq' (hε n) y hq hw]
      exact h q hq
    · rw [regFlowRead_eq' (hε n) y ⟨T.coe_nonneg, le_rfl⟩ hw]
      exact h T ⟨T.coe_nonneg, le_rfl⟩

/-! ### Images of alive points -/

/-- **The image `g_T(y)` read from the path.** -/
def gImgRead (T : ℝ≥0) (y : ℝ) (w : ℝ≥0 → ℝ) : ℝ :=
  w T + limsup (fun n : ℕ => regFlowRead T (1 / ((n : ℝ) + 1)) y T w) atTop

theorem measurable_gImgRead (T : ℝ≥0) (y : ℝ) : Measurable (gImgRead T y) := by
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  exact (measurable_pi_apply T).add
    (Measurable.limsup fun n => measurable_regFlowRead T (hε n) y ⟨T.coe_nonneg, le_rfl⟩)

/-- **`gImgRead` is the image of an alive point** on paths continuous on `[0, T]`. -/
theorem gImgRead_eq {T : ℝ≥0} {y : ℝ} {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T))
    (ha : Alive (frozenDrive w T) y T) : gImgRead T y w = gImg (frozenDrive w T) y T := by
  have hu := continuous_frozenDrive' hw
  have hε : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  obtain ⟨n₀, hn₀⟩ := (alive_iff_regFlow hu T.coe_nonneg).1 ha
  have hX := isPosSol_regFlow hu (hε n₀) hn₀
  have hcf : cflow (frozenDrive w T) y T = regFlow (frozenDrive w T) (1 / ((n₀ : ℝ) + 1)) y T :=
    cflow_eq_regFlow hu (hε n₀) hn₀ ⟨T.coe_nonneg, le_rfl⟩
  have hev : ∀ᶠ n : ℕ in atTop, regFlowRead T (1 / ((n : ℝ) + 1)) y T w = cflow (frozenDrive w T) y T := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
    have heq := hX.eqOn_regFlow hu (hε n) T.coe_nonneg fun s hs => hle.trans (hn₀ s hs)
    rw [regFlowRead_eq' (hε n) y ⟨T.coe_nonneg, le_rfl⟩ hw, heq ⟨T.coe_nonneg, le_rfl⟩, hcf]
  have hlim : Tendsto (fun n : ℕ => regFlowRead T (1 / ((n : ℝ) + 1)) y T w) atTop
      (𝓝 (cflow (frozenDrive w T) y T)) := tendsto_nhds_of_eventually_eq hev
  unfold gImgRead gImg
  rw [hlim.limsup_eq, frozenDrive_eq ⟨T.coe_nonneg, le_rfl⟩, Real.toNNReal_coe]

/-! ### Images of marks -/

open Classical in
/-- **The image of a right mark read from the path**: the infimum over rational alive points beyond it. -/
def rightImgRead (T : ℝ≥0) (x : ℝ) (w : ℝ≥0 → ℝ) : ℝ :=
  (⨅ q : ℚ, if x < (q : ℝ) ∧ aliveRead T q w then ((gImgRead T q w : ℝ) : EReal) else ⊤).toReal

theorem measurable_rightImgRead (T : ℝ≥0) (x : ℝ) : Measurable (rightImgRead T x) := by
  classical
  refine measurable_ereal_toReal.comp (Measurable.iInf fun q => ?_)
  refine Measurable.ite ?_ (measurable_coe_real_ereal.comp (measurable_gImgRead T q)) measurable_const
  by_cases hx : x < (q : ℝ)
  · simp only [hx, true_and]
    exact measurableSet_aliveRead T q
  · simp only [hx, false_and, ofPred_false]
    exact MeasurableSet.empty

/-- **`rightImgRead` is the real image of the mark** on paths continuous on `[0, T]`. -/
theorem rightImgRead_eq {T : ℝ≥0} (x : ℝ) {w : ℝ≥0 → ℝ} (hw : ContinuousOn w (Iic T)) :
    rightImgRead T x w = rightImg (frozenDrive w T) x T := by
  classical
  set u := frozenDrive w T with hudef
  have hu : Continuous u := continuous_frozenDrive' hw
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  set S := imgSet u x T with hS
  have hne : S.Nonempty := imgSet_nonempty hu x hT0
  have hbdd : BddBelow S := imgSet_bddBelow hu x hT0
  set F : ℚ → EReal := fun q => if x < (q : ℝ) ∧ aliveRead T q w then ((gImgRead T q w : ℝ) : EReal) else ⊤
    with hF
  -- the value of `F` at rational alive points
  have hFq : ∀ q : ℚ, x < (q : ℝ) → Alive u q T → F q = ((gImg u q T : ℝ) : EReal) := by
    intro q hq ha
    have hr : aliveRead T q w := (aliveRead_iff q hw).2 ha
    simp only [hF, hq, hr, and_self, ↓reduceIte, gImgRead_eq hw ha]
    rfl
  have hlow : ((sInf S : ℝ) : EReal) ≤ ⨅ q, F q := by
    refine le_iInf fun q => ?_
    by_cases hc : x < (q : ℝ) ∧ aliveRead T q w
    · have ha : Alive u q T := (aliveRead_iff q hw).1 hc.2
      rw [hFq q hc.1 ha]
      exact EReal.coe_le_coe_iff.2 (csInf_le hbdd ⟨q, hc.1, ha, rfl⟩)
    · simp only [hF, hc, ↓reduceIte, le_top]
  have hup : ⨅ q, F q ≤ ((sInf S : ℝ) : EReal) := by
    by_contra hn'
    have hn : ((sInf S : ℝ) : EReal) < ⨅ q, F q := not_le.1 hn'
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hn
    have hr1' : sInf S < r := EReal.coe_lt_coe_iff.1 hr1
    obtain ⟨g, ⟨y, hxy, hay, hgy⟩, hg⟩ := exists_lt_of_csInf_lt hne hr1'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + (r - g) by linarith)
    have haq : Alive u q T := hay.of_le hu hq1.le hT0
    have hbound := (cflow_lt_and_sub_le hu hay hq1 hT0 (s := T) ⟨hT0, le_rfl⟩).2
    have hgq : gImg u q T < r := by
      unfold gImg at hgy ⊢
      linarith
    have h1 : ⨅ q, F q ≤ F q := iInf_le F q
    rw [hFq q (hxy.trans hq1) haq] at h1
    have h2 : ((gImg u q T : ℝ) : EReal) < (r : EReal) := EReal.coe_lt_coe_iff.2 hgq
    exact (lt_irrefl _) ((h1.trans_lt h2).trans hr2)
  unfold rightImgRead rightImg
  rw [show (⨅ q : ℚ, if x < (q : ℝ) ∧ aliveRead T q w then ((gImgRead T q w : ℝ) : EReal) else ⊤) = ⨅ q, F q
    from rfl, le_antisymm hup hlow, EReal.toReal_coe]

/-! ### The image state -/

/-- **The image state read from the path** at the horizon `T`. -/
def imgStateRead {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (T : ℝ≥0) (w : ℝ≥0 → ℝ) :
    ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (w T, fun i => -rightImgRead T (-xL i) (fun u => -w u), fun j => rightImgRead T (xR j) w)

theorem measurable_imgStateRead {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (T : ℝ≥0) :
    Measurable (imgStateRead xL xR T) := by
  have hneg : Measurable fun w : ℝ≥0 → ℝ => fun u => -w u :=
    measurable_pi_iff.2 fun u => (measurable_pi_apply u).neg
  refine (measurable_pi_apply T).prodMk ((measurable_pi_iff.2 fun i => ?_).prodMk (measurable_pi_iff.2 fun j => ?_))
  · exact ((measurable_rightImgRead T (-xL i)).comp hneg).neg
  · exact measurable_rightImgRead T (xR j)

/-- **The image state of a path continuous on `[0, T]`.** -/
theorem imgStateRead_eq {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {T : ℝ≥0} {w : ℝ≥0 → ℝ}
    (hw : ContinuousOn w (Iic T)) : imgStateRead xL xR T w = GW2Sdg.imgState xL xR w T := by
  have hw' : ContinuousOn (fun u => -w u) (Iic T) := hw.neg
  unfold imgStateRead GW2Sdg.imgState
  congr 1
  refine Prod.ext ?_ ?_
  · funext i
    simp only
    rw [rightImgRead_eq (-xL i) hw']
    rfl
  · funext j
    simp only
    rw [rightImgRead_eq (xR j) hw]

/-- **The image state read at `T` depends on the path on `[0, T]` only.** -/
theorem imgStateRead_congr {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (T : ℝ≥0) {w w' : ℝ≥0 → ℝ}
    (h : ∀ u ≤ T, w u = w' u) : imgStateRead xL xR T w = imgStateRead xL xR T w' := by
  have hrf : ∀ (v v' : ℝ≥0 → ℝ), (∀ u ≤ T, v u = v' u) → ∀ ε y s, regFlowRead T ε y s v = regFlowRead T ε y s v' :=
    fun v v' hv ε y s => lipRead_congr T _ hv
  have hal : ∀ (v v' : ℝ≥0 → ℝ), (∀ u ≤ T, v u = v' u) → ∀ y, aliveRead T y v ↔ aliveRead T y v' := by
    intro v v' hv y
    unfold aliveRead
    simp only [hrf v v' hv]
  have hg : ∀ (v v' : ℝ≥0 → ℝ), (∀ u ≤ T, v u = v' u) → ∀ y, gImgRead T y v = gImgRead T y v' := by
    intro v v' hv y
    unfold gImgRead
    simp only [hrf v v' hv, hv T le_rfl]
  have hr : ∀ (v v' : ℝ≥0 → ℝ), (∀ u ≤ T, v u = v' u) → ∀ x, rightImgRead T x v = rightImgRead T x v' := by
    intro v v' hv x
    unfold rightImgRead
    congr 1
    refine iInf_congr fun q => ?_
    rw [hg v v' hv]
    by_cases h1 : x < (q : ℝ) ∧ aliveRead T q v
    · have h2 : x < (q : ℝ) ∧ aliveRead T q v' := ⟨h1.1, (hal v v' hv q).1 h1.2⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
    · have h2 : ¬ (x < (q : ℝ) ∧ aliveRead T q v') := fun h => h1 ⟨h.1, (hal v v' hv q).2 h.2⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
  have hn : ∀ u ≤ T, (fun u => -w u) u = (fun u => -w' u) u := fun u hu => by simp only [h u hu]
  unfold imgStateRead
  simp only [h T le_rfl, hr w w' h, hr _ _ hn]

end InteractingSLE.Theorem14.GW2Bh
