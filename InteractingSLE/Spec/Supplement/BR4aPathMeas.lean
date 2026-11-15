/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aPathSample
import InteractingSLE.Spec.Sec7.Lemma72DHull
import InteractingSLE.Spec.Coupling.WholeField2Cap

/-!
# Corollary BR4a, pathwise: measurability of the inverse clock

Packet PROVE-BR4A. Corollary BR4a's clock `ℓ` must be measurable at each time. `BR4aPathSample.invClk` reads it on
rational times from the relative clock `a(q) = hcap(mob v (K_q))/2` and the condition `ok(q)`: the pole `−1/v` avoids
the closed original hull at `q`. For a driver process `B` continuous in time and measurable at each time:

* `measurableSet_inter_nonempty_fwdHull`: `{ω : K_q(ω) ∩ U ≠ ∅}` is measurable for open `U ⊆ ℍ` (rational closed
  discs in `U` and `Sec7.Lemma72D.measurableSet_disjoint_closedBall_fwdHull_real`);
* `measurable_image_fwdHull`: `ω ↦ mob v (K_q(ω))` is measurable for the hitting σ-algebra;
* `measurableSet_poleOk`: `{ω : −1/v ∉ cl K_q(ω)}` is measurable;
* `clock_eq_hcapHit`, `measurable_hcapHitClock`: on `ok(q)` the relative clock is the measurable capacity
  `hcapHit(mob v (K_q))/2` (`WholeField.hcapHit`);
* **`measurable_invClk_clock`**: `ω ↦ invClk a ok u` is measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.BR4aPath

variable {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}

/-- The point with rational coordinates `(y₁, y₂)`. -/
def ratPt' (y : ℚ × ℚ) : ℂ := ⟨(y.1 : ℝ), (y.2 : ℝ)⟩

/-- **Open subsets of `ℍ` are unions of rational closed discs inside them.** -/
theorem exists_ratDisc {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ y : ℚ × ℚ × ℚ, 0 < (y.2.2 : ℝ) ∧ closedBall (ratPt' (y.1, y.2.1)) (y.2.2 : ℝ) ⊆ U ∧
      z ∈ closedBall (ratPt' (y.1, y.2.1)) (y.2.2 : ℝ) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - r / 8 < z.re by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - r / 8 < z.im by linarith)
  obtain ⟨e, he1, he2⟩ := exists_rat_btwn (show r / 4 < r / 2 by linarith)
  have hcz : dist z (ratPt' (a, b)) < r / 4 := by
    rw [Complex.dist_eq]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [ratPt', Complex.sub_re, Complex.sub_im]
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  refine ⟨(a, b, e), by simp only; linarith, fun w hw => hball ?_, ?_⟩
  · rw [mem_closedBall] at hw
    rw [mem_ball]
    calc dist w z ≤ dist w (ratPt' (a, b)) + dist (ratPt' (a, b)) z := dist_triangle _ _ _
      _ < (e : ℝ) + r / 4 := by
          refine add_lt_add_of_le_of_lt hw ?_
          rw [dist_comm]; exact hcz
      _ ≤ r := by linarith
  · rw [mem_closedBall]
    exact le_of_lt (lt_trans hcz he1)

omit [MeasurableSpace Ω] in
theorem drive_one_eq (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    QuantumZipper.drive 1 B ω = fun s : ℝ => B s.toNNReal ω := by
  funext s
  simp [QuantumZipper.drive]

/-- **Hitting an open subset of `ℍ` by the hull at a fixed time is measurable.** -/
theorem measurableSet_inter_nonempty_fwdHull (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ r, Measurable (B r))
    {q : ℝ} (hq : 0 ≤ q) {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet {ω | (fwdHull (fun s : ℝ => B s.toNNReal ω) q ∩ U).Nonempty} := by
  have e : {ω | (fwdHull (fun s : ℝ => B s.toNNReal ω) q ∩ U).Nonempty} =
      ⋃ y : ℚ × ℚ × ℚ, ⋃ (_ : 0 < (y.2.2 : ℝ) ∧ closedBall (ratPt' (y.1, y.2.1)) (y.2.2 : ℝ) ⊆ U),
        {ω | Disjoint (closedBall (ratPt' (y.1, y.2.1)) (y.2.2 : ℝ))
          (fwdHull (QuantumZipper.drive 1 B ω) q)}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, drive_one_eq, exists_prop]
    constructor
    · rintro ⟨z, hzK, hzU⟩
      obtain ⟨y, hy0, hyU, hzy⟩ := exists_ratDisc hU hzU
      exact ⟨y, ⟨hy0, hyU⟩, fun hd => Set.disjoint_left.1 hd hzy hzK⟩
    · rintro ⟨y, ⟨-, hyU⟩, hy⟩
      obtain ⟨z, hz1, hz2⟩ := Set.not_disjoint_iff.1 hy
      exact ⟨z, hz2, hyU hz1⟩
  rw [e]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  refine MeasurableSet.compl ?_
  have hc : (y.2.2 : ℝ) < (ratPt' (y.1, y.2.1)).im := by
    have hlow : ratPt' (y.1, y.2.1) - (y.2.2 : ℝ) * Complex.I ∈ U := hy.2 (by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy.1])
    have := hUH hlow
    change (0 : ℝ) < (ratPt' (y.1, y.2.1) - (y.2.2 : ℝ) * Complex.I).im at this
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, mul_one] at this
    linarith
  exact Sec7.Lemma72D.measurableSet_disjoint_closedBall_fwdHull_real hBc hq (fun r _ => hBm r) hy.1 hc

/-- **The image hull `mob v (K_q)` is measurable for the hitting σ-algebra.** -/
theorem measurable_image_fwdHull (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ r, Measurable (B r)) {v : ℝ}
    (hv : v ≠ 0) {q : ℝ} (hq : 0 ≤ q) :
    Measurable[_, hittingSigma] fun ω => mob v '' fwdHull (fun s : ℝ => B s.toNNReal ω) q := by
  refine @measurable_generateFrom _ _ _ _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have hcont : ContinuousOn (mob v) H := fun z hz =>
    (Sec5.CrossRestart.continuousAt_realMobius (a' := 1) (b' := 0) (c' := v) (d' := 1)
      (by simpa using mul_add_one_ne_zero hv hz)).continuousWithinAt
  have hV : IsOpen (H ∩ mob v ⁻¹' U) := hcont.isOpen_inter_preimage QuantumZipper.isOpen_H hU
  have e : (fun ω => mob v '' fwdHull (fun s : ℝ => B s.toNNReal ω) q) ⁻¹' {A : Set ℂ | (A ∩ U).Nonempty} =
      {ω | (fwdHull (fun s : ℝ => B s.toNNReal ω) q ∩ (H ∩ mob v ⁻¹' U)).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
      exact ⟨z, hz, QuantumZipper.fwdHull_mono.2 q hz, hzU⟩
    · rintro ⟨z, hz, -, hzU⟩
      exact ⟨mob v z, mem_image_of_mem _ hz, hzU⟩
  rw [e]
  exact measurableSet_inter_nonempty_fwdHull hBc hBm hq hV inter_subset_left

/-- **The pole condition `−1/v ∉ cl K_q` is a measurable event.** -/
theorem measurableSet_poleOk (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ r, Measurable (B r)) (v : ℝ)
    {q : ℝ} (hq : 0 ≤ q) :
    MeasurableSet {ω | ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => B s.toNNReal ω) q)} := by
  have e : {ω | ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => B s.toNNReal ω) q)} =
      ⋃ n : ℕ, {ω | (fwdHull (fun s : ℝ => B s.toNNReal ω) q ∩
        (ball ((pole v : ℝ) : ℂ) (1 / ((n : ℝ) + 1)) ∩ H)).Nonempty}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_compl_iff, Set.not_nonempty_iff_eq_empty]
    constructor
    · intro hp
      obtain ⟨r, hr, hd⟩ := exists_disjoint_ball_of_notMem_closure hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
      refine ⟨n, Set.eq_empty_iff_forall_notMem.2 fun z hz => ?_⟩
      exact Set.disjoint_left.1 hd (ball_subset_ball hn.le hz.2.1) hz.1
    · rintro ⟨n, hn⟩ hp
      rw [Metric.mem_closure_iff] at hp
      obtain ⟨z, hzK, hz⟩ := hp (1 / ((n : ℝ) + 1)) (by positivity)
      have : z ∈ fwdHull (fun s : ℝ => B s.toNNReal ω) q ∩ (ball ((pole v : ℝ) : ℂ) (1 / ((n : ℝ) + 1)) ∩ H) :=
        ⟨hzK, by rw [mem_ball, dist_comm]; exact hz, QuantumZipper.fwdHull_mono.2 q hzK⟩
      rw [hn] at this
      exact this
  rw [e]
  exact MeasurableSet.iUnion fun n => (measurableSet_inter_nonempty_fwdHull hBc hBm hq
    (isOpen_ball.inter QuantumZipper.isOpen_H) inter_subset_right).compl

/-- **On the pole condition the relative clock is the measurable capacity.** -/
theorem clock_eq_hcapHit {v : ℝ} (hv : v ≠ 0) {w : ℝ → ℝ} (hw : Continuous w) {q : ℝ} (hq : 0 ≤ q)
    (hp : ((pole v : ℝ) : ℂ) ∉ closure (fwdHull w q)) :
    clock v w q = (WholeField.hcapHit (mob v '' fwdHull w q)).toReal / 2 := by
  obtain ⟨r, hr, hd⟩ := exists_disjoint_ball_of_notMem_closure hp
  have hd' : Disjoint (ball (Sec5.CrossRestart.mobPole v 1 : ℂ) r) (fwdHull w q) := by
    rw [mobPole_eq]
    exact hd
  have hK := Sec5.CrossRestart.isHPHull_image (a := 1) (b := 0) (c := v) (d := 1) (by norm_num) hv
    (isHPHull_fwdHull hw hq) hr hd'
  have hK' : IsHPHull (mob v '' fwdHull w q) := hK
  rw [clock, WholeField.IsHPHull.hcapHit_eq hK', ConformalImage.hcapSet_eq hK']
  congr 1
  exact (ENNReal.toReal_ofReal (HPHull.hcap_nonneg _)).symm

theorem measurable_hcapHitClock (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ r, Measurable (B r)) {v : ℝ}
    (hv : v ≠ 0) {q : ℝ} (hq : 0 ≤ q) :
    Measurable fun ω => (WholeField.hcapHit (mob v '' fwdHull (fun s : ℝ => B s.toNNReal ω) q)).toReal / 2 :=
  ((WholeField.measurable_hcapHit.comp (measurable_image_fwdHull hBc hBm hv hq)).ennreal_toReal).div_const 2

/-- **The inverse clock is measurable at each time.** -/
theorem measurable_invClk_clock (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ r, Measurable (B r)) {v : ℝ}
    (hv : v ≠ 0) (u : ℝ≥0) :
    Measurable fun ω => invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => B s.toNNReal ω) t)
      (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => B s.toNNReal ω) t)) u := by
  classical
  refine Measurable.iSup fun q : ℚ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  set t : ℝ≥0 := (q : ℝ).toNNReal
  have e : {ω | 0 ≤ q ∧ ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => B s.toNNReal ω) t) ∧
      clock v (fun s : ℝ => B s.toNNReal ω) t < u} =
      {_ω : Ω | 0 ≤ q} ∩ ({ω | ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => B s.toNNReal ω) t)} ∩
        {ω | (WholeField.hcapHit (mob v '' fwdHull (fun s : ℝ => B s.toNNReal ω) t)).toReal / 2 < u}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rwa [← clock_eq_hcapHit hv (continuous_rpath (hBc ω)) t.coe_nonneg h2]
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rwa [clock_eq_hcapHit hv (continuous_rpath (hBc ω)) t.coe_nonneg h2]
  rw [e]
  exact (MeasurableSet.const _).inter ((measurableSet_poleOk hBc hBm v t.coe_nonneg).inter
    (measurableSet_lt (measurable_hcapHitClock hBc hBm hv t.coe_nonneg) measurable_const))

end InteractingSLE.Theorem14.BR4aPath
