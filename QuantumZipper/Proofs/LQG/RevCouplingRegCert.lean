import QuantumZipper.Proofs.LQG.InfiniteMass
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

/-!
# RCBMR, deterministic part: a measurable certificate for a regular boundary measure

Task RCBMR (`Blueprint.RevCouplingBoundaryMeasureRegular`). The regularity of the boundary
measure (vague limit exists; no atoms; positive on intervals; finite on compact intervals) must be
transferred through a law identity of circle coordinates, so we express it by a **measurable**
event `Cert γ` of field samples which depends only on `avgReg` (hence only on `coordsFull`):

* `Cert γ x`: the approximations `bdryApprox γ x k` are finite on `[-N, N]`; the integrals of the
  countable test family `testFam N m`, `bump N` (`BoundaryVague`) are Cauchy; `Psi γ (a,b) x > 0`
  for rational `a < b`; and on `[-(n+1), n+1]`, small dyadic balls have `Psi` mass
  `≤ (e+1)⁻¹` (`InfMass.Psi` is the measurable functional equal to `ν(U)` for open `U`).
* `measurable_cert`, `cert_congr` (only `avgReg` matters), `certSet` (the event in `coordsFull`
  coordinates, via the measurable reconstruction `recF`), `mem_certSet_iff`.
* `good_of_cert`: a certificate gives a vague limit `ν` (Riesz–Markov, `BdryVague`) with no atoms,
  positive on every nondegenerate open interval and finite on compact intervals.
* `cert_of_vague`: conversely, a vague limit with these properties (and locally finite
  approximations) gives a certificate; the atom clause uses the Lebesgue number lemma.

Own elementary bookkeeping (no published source needed: countable characterization of vague
convergence and of atomlessness on compacts).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace RevCouplingReg

open BdryVague InfMass LQGMeas

/-! ## 1. The certificate and its measurability -/

/-- Cauchy condition for the approximating integrals of `g`. -/
def CauchyI (γ : ℝ) (g : ℝ → ℝ) (x : FieldSample) : Prop :=
  ∀ e : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ k' : ℕ, K ≤ k' →
    |∫ t, g t ∂bdryApprox γ x k - ∫ t, g t ∂bdryApprox γ x k'| ≤ 1 / ((e : ℝ) + 1)

/-- The countable certificate of a regular boundary measure. -/
def Cert (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ k N : ℕ, bdryApprox γ x k (Icc (-(N : ℝ)) N) < ∞) ∧
  (∀ N m : ℕ, CauchyI γ (testFam N m) x) ∧ (∀ N : ℕ, CauchyI γ (bump N) x) ∧
  (∀ a b : ℚ, (a : ℝ) < b → 0 < Psi γ (Ioo (a : ℝ) b) x) ∧
  (∀ n e : ℕ, ∃ j : ℕ, ∀ i : ℤ, |(i : ℝ)| ≤ ((n : ℝ) + 1) * 2 ^ j →
    Psi γ (ball ((i : ℝ) / 2 ^ j) (2 / 2 ^ j)) x ≤ ((e : ℝ≥0∞) + 1)⁻¹)

theorem measurable_cauchyI (γ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (CauchyI γ g) := by
  unfold CauchyI
  refine Measurable.forall fun e => Measurable.exists fun K => Measurable.forall fun k =>
    measurable_const.imp (Measurable.forall fun k' => measurable_const.imp ?_)
  exact GoodMeas.mprop_abs_le (meas_integral_bdryApprox γ k hg)
    (meas_integral_bdryApprox γ k' hg) _

theorem measurable_cert (γ : ℝ) : Measurable (Cert γ) := by
  unfold Cert
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
  · refine Measurable.forall fun k => Measurable.forall fun N => ?_
    exact measurableSet_setOfPred.1 (measurableSet_lt
      ((Measure.measurable_coe measurableSet_Icc).comp (measurable_bdryApprox γ k))
      measurable_const)
  · exact Measurable.forall fun N => Measurable.forall fun m =>
      measurable_cauchyI γ (continuous_testFam N m).measurable
  · exact Measurable.forall fun N => measurable_cauchyI γ (continuous_bump N).measurable
  · refine Measurable.forall fun a => Measurable.forall fun b => measurable_const.imp ?_
    exact measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_Psi γ _))
  · refine Measurable.forall fun n => Measurable.forall fun e => Measurable.exists fun j =>
      Measurable.forall fun i => measurable_const.imp ?_
    exact measurableSet_setOfPred.1 (measurableSet_le (measurable_Psi γ _) measurable_const)

/-- The certificate only depends on `avgReg`. -/
theorem cert_congr {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    Cert γ x ↔ Cert γ x' := by
  have hb := Factorization.bdryApprox_congr h γ
  have hP : ∀ U, Psi γ U x = Psi γ U x' := fun U => Psi_congr h
  unfold Cert CauchyI
  simp only [hb, hP]

/-! ## 2. Reconstruction from `coordsFull` and the coordinate event -/

open Classical in
/-- Measurable reconstruction of a field sample from its full circle coordinates. -/
def recF (c : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = μ
  then c (Nat.find h) else 0

theorem measurable_recF : Measurable recF := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold recF
  by_cases h : ∃ i, foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 = μ
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

theorem coordsFull_recF (y : FieldSample) :
    CoordsFull.coordsFull (recF (CoordsFull.coordsFull y)) = CoordsFull.coordsFull y := by
  classical
  funext i
  have h : ∃ j, foldedCircle (CoordsFull.fullIndex j).1 (CoordsFull.fullIndex j).2 =
      foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 := ⟨i, rfl⟩
  simp only [CoordsFull.coordsFull, recF, h, ↓reduceDIte]
  exact congrArg y (Nat.find_spec h)

/-- The certificate as an event of the full circle coordinates. -/
def certSet (γ : ℝ) : Set (ℕ → ℝ) := {c | Cert γ (recF c)}

theorem measurableSet_certSet (γ : ℝ) : MeasurableSet (certSet γ) :=
  measurableSet_setOfPred.2 ((measurable_cert γ).comp measurable_recF)

theorem mem_certSet_iff (γ : ℝ) (y : FieldSample) :
    CoordsFull.coordsFull y ∈ certSet γ ↔ Cert γ y :=
  cert_congr (CoordsFull.avgReg_congr_full (coordsFull_recF y))

/-! ## 3. Certificate ⇒ regular boundary measure -/

theorem exists_tendsto_of_cauchyI {γ : ℝ} {g : ℝ → ℝ} {x : FieldSample} (h : CauchyI γ g x) :
    ∃ l, Tendsto (fun k => ∫ t, g t ∂bdryApprox γ x k) atTop (𝓝 l) := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε => ?_)
  obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
  obtain ⟨K, hK⟩ := h e
  exact ⟨K, fun n hn => lt_of_le_of_lt (by rw [Real.dist_eq]; exact hK n hn K le_rfl) he⟩

theorem cauchyI_of_tendsto {γ : ℝ} {g : ℝ → ℝ} {x : FieldSample} {l : ℝ}
    (h : Tendsto (fun k => ∫ t, g t ∂bdryApprox γ x k) atTop (𝓝 l)) : CauchyI γ g x := by
  intro e
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.1 h.cauchySeq (1 / ((e : ℝ) + 1)) (by positivity)
  exact ⟨K, fun k hk k' hk' => by
    have := hK k hk k' hk'
    rw [Real.dist_eq] at this
    exact this.le⟩

theorem tendsto_inv_succ_zero :
    Tendsto (fun e : ℕ => ((e : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
  have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  refine this.congr fun e => ?_
  simp [Function.comp]

/-- **Certificate ⇒ regular vague limit.** -/
theorem good_of_cert {γ : ℝ} {x : FieldSample} (h : Cert γ x) :
    ∃ ν, IsVagueLimitR (bdryApprox γ x) ν ∧ (∀ t : ℝ, ν {t} = 0) ∧
      (∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) ∧ (∀ u v : ℝ, ν (Icc u v) < ∞) := by
  obtain ⟨hF, hT, hBm, hP, hA⟩ := h
  have hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ x k) := fun k =>
    isFiniteMeasureOnCompacts_of_Icc (hF k)
  obtain ⟨ν, hν⟩ := exists_isVagueLimitR_of_testFam hfin
    (fun N m => exists_tendsto_of_cauchyI (hT N m)) (fun N => exists_tendsto_of_cauchyI (hBm N))
  have := hν.1
  refine ⟨ν, hν, fun t => ?_, fun u v huv => ?_, fun u v => isCompact_Icc.measure_lt_top⟩
  · have hle : ∀ e : ℕ, ν {t} ≤ ((e : ℝ≥0∞) + 1)⁻¹ := by
      intro e
      obtain ⟨j, hj⟩ := hA ⌈|t|⌉₊ e
      set i : ℤ := ⌊t * 2 ^ j⌋
      have hp : (0 : ℝ) < 2 ^ j := by positivity
      have hp1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have h1 : (i : ℝ) ≤ t * 2 ^ j := Int.floor_le _
      have h2 : t * 2 ^ j - 1 < i := Int.sub_one_lt_floor _
      have hn : |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
      have ha1 : t * 2 ^ j ≤ |t| * 2 ^ j := mul_le_mul_of_nonneg_right (le_abs_self t) hp.le
      have ha2 : -|t| * 2 ^ j ≤ t * 2 ^ j := mul_le_mul_of_nonneg_right (neg_abs_le t) hp.le
      have ha3 : |t| * 2 ^ j ≤ (⌈|t|⌉₊ : ℝ) * 2 ^ j := mul_le_mul_of_nonneg_right hn hp.le
      have hi : |(i : ℝ)| ≤ ((⌈|t|⌉₊ : ℝ) + 1) * 2 ^ j := by
        rw [abs_le]; constructor <;> nlinarith
      have hmem : t ∈ ball ((i : ℝ) / 2 ^ j) (2 / 2 ^ j) := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        have e1 : (i : ℝ) / 2 ^ j ≤ t := by rw [div_le_iff₀ hp]; exact h1
        have e2 : t < (i : ℝ) / 2 ^ j + 2 / 2 ^ j := by
          rw [← add_div, lt_div_iff₀ hp]; linarith
        have e3 : (0 : ℝ) < 2 / 2 ^ j := by positivity
        constructor <;> linarith
      calc ν {t} ≤ ν (ball ((i : ℝ) / 2 ^ j) (2 / 2 ^ j)) :=
            measure_mono (singleton_subset_iff.2 hmem)
        _ = Psi γ (ball ((i : ℝ) / 2 ^ j) (2 / 2 ^ j)) x := (Psi_eq isOpen_ball hν).symm
        _ ≤ _ := hj i hi
    exact nonpos_iff_eq_zero.1 (ge_of_tendsto' tendsto_inv_succ_zero hle)
  · obtain ⟨a, hua, hav⟩ := exists_rat_btwn huv
    obtain ⟨b, hab, hbv⟩ := exists_rat_btwn hav
    calc 0 < Psi γ (Ioo (a : ℝ) b) x := hP a b hab
      _ = ν (Ioo (a : ℝ) b) := Psi_eq isOpen_Ioo hν
      _ ≤ ν (Ioo u v) := measure_mono (Ioo_subset_Ioo hua.le hbv.le)

/-! ## 4. Regular vague limit ⇒ certificate -/

/-- Uniformly small balls on a compact set, for a locally finite atomless measure. -/
theorem exists_small_balls {ν : Measure ℝ} [IsLocallyFiniteMeasure ν] (hat : ∀ t, ν {t} = 0)
    {s : Set ℝ} (hs : IsCompact s) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s, ν (ball y δ) < ε := by
  have hr : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ν (ball y r) < ε := by
    intro y
    have ht := tendsto_measure_cthickening_of_isCompact (μ := ν) (isCompact_singleton (x := y))
    rw [hat y] at ht
    obtain ⟨r, hr1, hr0⟩ := (((ht.mono_left nhdsWithin_le_nhds).eventually
      (gt_mem_nhds hε)).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
    refine ⟨r, hr0, lt_of_le_of_lt (measure_mono ?_) hr1⟩
    rw [cthickening_singleton y (le_of_lt hr0)]
    exact ball_subset_closedBall
  choose r hr0 hrε using hr
  obtain ⟨δ, hδ, hL⟩ := lebesgue_number_lemma_of_metric hs (c := fun y => ball y (r y))
    (fun y => isOpen_ball) (fun y _ => mem_iUnion.2 ⟨y, mem_ball_self (hr0 y)⟩)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  obtain ⟨z, hz⟩ := hL y hy
  exact lt_of_le_of_lt (measure_mono hz) (hrε z)

/-- **Regular vague limit ⇒ certificate.** -/
theorem cert_of_vague {γ : ℝ} {x : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ x) ν)
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ x k)) (hat : ∀ t : ℝ, ν {t} = 0)
    (hpos : ∀ u v : ℝ, u < v → 0 < ν (Ioo u v)) : Cert γ x := by
  have := hν.1
  refine ⟨fun k N => ?_, fun N m => ?_, fun N => ?_, fun a b hab => ?_, fun n e => ?_⟩
  · have := hfin k; exact isCompact_Icc.measure_lt_top
  · exact cauchyI_of_tendsto (hν.2 _ (continuous_testFam N m) (hasCompactSupport_testFam N m))
  · exact cauchyI_of_tendsto (hν.2 _ (continuous_bump N) (hasCompactSupport_bump N))
  · rw [Psi_eq isOpen_Ioo hν]; exact hpos _ _ hab
  · have hε : (0 : ℝ≥0∞) < ((e : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.2 (by simp)
    obtain ⟨δ, hδ, hsm⟩ := exists_small_balls hat
      (isCompact_Icc (a := -((n : ℝ) + 1)) (b := (n : ℝ) + 1)) hε
    obtain ⟨j, hj⟩ := exists_nat_gt (2 / δ)
    have hjp : (j : ℝ) < 2 ^ j := by exact_mod_cast j.lt_two_pow_self
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have h2 : 2 / 2 ^ j < δ := by
      rw [div_lt_iff₀ hp]
      have := (div_lt_iff₀ hδ).1 (hj.trans hjp)
      linarith
    refine ⟨j, fun i hi => ?_⟩
    have hy : (i : ℝ) / 2 ^ j ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      have : |(i : ℝ) / 2 ^ j| ≤ (n : ℝ) + 1 := by
        rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]; exact hi
      exact abs_le.1 this
    rw [Psi_eq isOpen_ball hν]
    exact (lt_of_le_of_lt (measure_mono (ball_subset_ball h2.le)) (hsm _ hy)).le

end RevCouplingReg
end QuantumZipper
