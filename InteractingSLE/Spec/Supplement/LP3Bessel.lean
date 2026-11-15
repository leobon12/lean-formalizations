/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP3Flow
import InteractingSLE.Stochastic.BrownianSupport
import QuantumZipper.Proofs.Loewner.Algebra

/-!
# Lemma LP3: the Bessel step and the Markov splitting

Packet PROVE-LP15. Supplement §6.3, proof of Lemma LP3 (`source/spec/p481-528.md` L25–L35, p. 482): "The
ordinary-SLE gap at the inner point is a Bessel process of dimension `1 + 4/k ∈ (1, 2)` until it hits zero. Its
first zero is almost surely finite. Couple all initial gaps `y ∈ [ε/2, 2ε]` with the same Brownian motion.
One-dimensional comparison up to the first zero gives `τ_y ≤ τ_{2ε}`. By Brownian scaling and the almost sure
finiteness of `τ_{2ε}`, for a sufficiently large deterministic `K` the event `τ_{2ε} ≤ Kε²,
sup_{0 ≤ t ≤ τ_{2ε}} |√k B_t| ≤ Kε` has a fixed strictly positive probability independent of `ε`."

* `besselSet κ K M`: a measurable set of paths `y` (stopped at `K`) on which the point `2` is not alive at time `K`
  under the driver `√κ y` and `|√κ y| < M` at rational times `≤ K` (two constants instead of the source's single
  `K`; `besselSet_spec`).
* `exists_bessel_constants`: constants `K, M` with probability `≥ 1/2` for **every** Brownian motion (its path law
  is the same, `Sec2.Assembly2.map_path_eq_map_path`), from the almost sure finiteness of the swallowing time
  (`ae_exists_not_alive`, [RS05] Lemma 6.1) and continuity.
* `scaledBesselEvent`, `measureReal_scaledBesselEvent`, `scaledBesselEvent_spec`: Brownian scaling — with
  probability `≥ 1/2` the point `2e` is not alive at time `K e²` and `|√κ Y| ≤ M e` on `[0, K e²]`; the event is
  measurable for the past of `Y` at `K e²`.
* `measure_inter_eq_mul_of_past`: the Markov splitting at a deterministic time (`IsPreBrownianReal.indepFun_shift`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.LP.LP3

/-! ### Stopped paths -/

/-- The path stopped at time `K`. -/
def stopPath (K : ℝ≥0) (y : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => y (min t K)

theorem measurable_stopPath (K : ℝ≥0) : Measurable (stopPath K) :=
  measurable_pi_iff.2 fun t => measurable_pi_apply (min t K)

theorem continuous_stopPath (K : ℝ≥0) {y : ℝ≥0 → ℝ} (hy : Continuous y) : Continuous (stopPath K y) :=
  hy.comp (continuous_id.min continuous_const)

theorem stopPath_zero (K : ℝ≥0) {y : ℝ≥0 → ℝ} (hy0 : y 0 = 0) : stopPath K y 0 = 0 := by
  simp [stopPath, hy0]

/-- Being alive at `K` only depends on the driver up to `K`. -/
theorem alive_stopPath_iff (s : ℝ) (K : ℝ≥0) (y : ℝ≥0 → ℝ) (x : ℝ) :
    Alive (pathDrive s (stopPath K y)) x K ↔ Alive (pathDrive s y) x K := by
  have h : ∀ r ∈ Icc (0 : ℝ) K, pathDrive s (stopPath K y) r = pathDrive s y r := by
    intro r hr
    have hr' : r.toNNReal ≤ K := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
    simp only [pathDrive, stopPath, min_eq_left hr']
  constructor
  · rintro ⟨u, hu⟩; exact ⟨u, QuantumZipper.isForwardSol_congr_drive h hu⟩
  · rintro ⟨u, hu⟩; exact ⟨u, QuantumZipper.isForwardSol_congr_drive (fun r hr => (h r hr).symm) hu⟩

/-! ### The Bessel set -/

/-- The universal measurable set of paths deciding "alive at `T`" (`exists_aliveSet`). -/
def aliveSet (s x : ℝ) (hx : 0 < x) (T : ℝ≥0) : Set (ℝ≥0 → ℝ) := (exists_aliveSet s hx T).choose

theorem measurableSet_aliveSet (s x : ℝ) (hx : 0 < x) (T : ℝ≥0) : MeasurableSet (aliveSet s x hx T) :=
  (exists_aliveSet s hx T).choose_spec.1

theorem mem_aliveSet_iff {s x : ℝ} {hx : 0 < x} {T : ℝ≥0} {y : ℝ≥0 → ℝ} (hy : Continuous y) (hy0 : y 0 = 0) :
    y ∈ aliveSet s x hx T ↔ Alive (pathDrive s y) x T :=
  (exists_aliveSet s hx T).choose_spec.2 y hy hy0

/-- The Bessel set: the point `2` is dead at `K` under `√κ y`, and `|√κ y| < M` at rational times `≤ K`. -/
def besselSet (κ : ℝ) (K M : ℝ≥0) : Set (ℝ≥0 → ℝ) :=
  (aliveSet (√κ) 2 two_pos K)ᶜ ∩ {y | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ K → |√κ * y q| < M}

theorem measurableSet_besselSet (κ : ℝ) (K M : ℝ≥0) : MeasurableSet (besselSet κ K M) := by
  refine (measurableSet_aliveSet _ _ _ _).compl.inter ?_
  simp only [ofPred_forall]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
    measurableSet_lt (continuous_abs.measurable.comp ((measurable_pi_apply _).const_mul _))
      measurable_const

/-- What the Bessel set says about a continuous path. -/
theorem besselSet_spec {κ : ℝ} {K M : ℝ≥0} {y : ℝ≥0 → ℝ} (hy : Continuous y) (hy0 : y 0 = 0)
    (h : stopPath K y ∈ besselSet κ K M) :
    ¬ Alive (pathDrive (√κ) y) 2 K ∧ ∀ t ≤ K, |√κ * y t| ≤ M := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ha => h1 ?_, fun t ht => ?_⟩
  · rw [mem_aliveSet_iff (continuous_stopPath K hy) (stopPath_zero K hy0), alive_stopPath_iff]
    exact ha
  · have hφ : Continuous fun t => |√κ * stopPath K y t| :=
      (continuous_const.mul (continuous_stopPath K hy)).abs
    have := BrownianSupport.le_of_forall_nnrat_lt hφ (fun q hq => h2 q hq) t ht
    simpa [stopPath, min_eq_left ht] using this

/-- The converse direction, used to bound the probability from below. -/
theorem stopPath_mem_besselSet {κ : ℝ} {K M : ℝ≥0} {y : ℝ≥0 → ℝ} (hy : Continuous y) (hy0 : y 0 = 0)
    (h1 : ¬ Alive (pathDrive (√κ) y) 2 K) (h2 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ K → |√κ * y q| < M) :
    stopPath K y ∈ besselSet κ K M := by
  refine ⟨fun ha => h1 ?_, fun q hq => ?_⟩
  · rwa [mem_aliveSet_iff (continuous_stopPath K hy) (stopPath_zero K hy0), alive_stopPath_iff] at ha
  · simpa [stopPath, min_eq_left hq] using h2 q hq

/-! ### Universal constants -/

universe u v

/-- **The Bessel constants.** For `κ > 4` there are `K, M` such that for every Brownian motion `X` with
measurable coordinates, `P(stopPath K X ∈ besselSet κ K M) ≥ 1/2`. A reference Brownian motion with continuous
paths vanishing at `0` is used to compute the common value. -/
theorem exists_bessel_constants {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBm : ∀ r, Measurable (B r)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 4 < κ) :
    ∃ K M : ℝ≥0, 0 < K ∧ ∀ {Ω' : Type v} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
      {X : ℝ≥0 → Ω' → ℝ}, IsPreBrownianReal X P' → (∀ t, Measurable (X t)) →
        1 / 2 ≤ P'.real {ω | stopPath K (fun t => X t ω) ∈ besselSet κ K M} := by
  have hP : IsProbabilityMeasure P := hB.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hmB : Measurable fun ω (t : ℝ≥0) => B t ω := measurable_pi_iff.2 hBm
  -- (1) the point `2` is dead at a large integer time with probability `≥ 3/4`
  set D : ℕ → Set Ω := fun n => {ω | Alive (sDrive (√κ) B ω) 2 (n : ℝ≥0)} with hD
  have hDm : ∀ n, MeasurableSet (D n) := fun n =>
    (NonSwallow.bmFilt hBm).le _ _ (measurableSet_alive_bmFilt hBm hBc hB0 (√κ) two_pos (n : ℝ≥0))
  have hDanti : Antitone D := by
    intro n m hnm ω hω
    exact Alive.mono hω (Nat.cast_nonneg n) (by exact_mod_cast hnm)
  have hDnull : P (⋂ n, D n) = 0 := by
    have hae := ae_exists_not_alive hB hBm hBc hB0 hκ (x := 2) two_pos
    rw [ae_iff] at hae
    refine measure_mono_null (fun ω hω => ?_) hae
    simp only [mem_iInter] at hω
    simp only [mem_ofPred_eq, not_exists, not_forall, not_not]
    intro n
    have := hω n
    simp only [hD, mem_ofPred_eq, NNReal.coe_natCast] at this
    exact this
  have hlimD := tendsto_measure_iInter_atTop (μ := P) (fun n => (hDm n).nullMeasurableSet) hDanti
    ⟨0, measure_ne_top _ _⟩
  rw [hDnull] at hlimD
  obtain ⟨n, hn⟩ := (hlimD.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4) by
    rw [ENNReal.ofReal_pos]; norm_num))).exists
  set K : ℝ≥0 := (n : ℝ≥0) + 1 with hK
  have hDK : P {ω | Alive (sDrive (√κ) B ω) 2 K} ≤ ENNReal.ofReal (1 / 4) := by
    refine (measure_mono fun ω hω => ?_).trans hn.le
    exact Alive.mono hω (Nat.cast_nonneg n) (by simp [hK])
  -- (2) the driver stays bounded on `[0, K]` with probability `≥ 3/4`
  set G : ℕ → Set Ω := fun m => {ω | ∀ q : ℚ≥0, (q : ℝ≥0) ≤ K → |√κ * B q ω| < m} with hG
  have hGm : ∀ m, MeasurableSet (G m) := fun m => by
    simp only [hG, ofPred_forall]
    exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
      measurableSet_lt (continuous_abs.measurable.comp ((hBm _).const_mul _)) measurable_const
  have hGmono : Monotone G := by
    intro m m' hmm' ω hω q hq
    exact (hω q hq).trans_le (by exact_mod_cast hmm')
  have hGall : P (⋃ m, G m) = 1 := by
    refine le_antisymm prob_le_one ?_
    rw [← measure_univ (μ := P)]
    refine measure_mono fun ω _ => ?_
    have hcont : ContinuousOn (fun t : ℝ≥0 => √κ * B t ω) (Icc 0 K) :=
      (continuous_const.mul (hBc ω)).continuousOn
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := K)).exists_bound_of_continuousOn hcont
    obtain ⟨m, hm⟩ := exists_nat_gt C
    refine mem_iUnion.2 ⟨m, fun q hq => ?_⟩
    have := hC q ⟨zero_le, hq⟩
    rw [Real.norm_eq_abs] at this
    linarith
  have hlimG := tendsto_measure_iUnion_atTop (μ := P) hGmono
  rw [hGall] at hlimG
  obtain ⟨m, hm⟩ := (hlimG.eventually (lt_mem_nhds (show ENNReal.ofReal (3 / 4) < 1 by
    rw [ENNReal.ofReal_lt_one]; norm_num))).exists
  refine ⟨K, (m : ℝ≥0), by simp [hK, add_pos_of_nonneg_of_pos], ?_⟩
  -- (3) the common probability
  set S : Set (ℝ≥0 → ℝ) := stopPath K ⁻¹' besselSet κ K m with hS
  have hSm : MeasurableSet S := measurable_stopPath K (measurableSet_besselSet κ K m)
  set DK : Set Ω := {ω | Alive (sDrive (√κ) B ω) 2 K} with hDKdef
  have hDKm : MeasurableSet DK :=
    (NonSwallow.bmFilt hBm).le _ _ (measurableSet_alive_bmFilt hBm hBc hB0 (√κ) two_pos K)
  have hsub : (DK ∪ (G m)ᶜ)ᶜ ⊆ {ω | (fun t => B t ω) ∈ S} := by
    intro ω hω
    simp only [compl_union, compl_compl, mem_inter_iff, mem_compl_iff] at hω
    exact stopPath_mem_besselSet (hBc ω) (hB0 ω) hω.1 hω.2
  have hDKr : P.real DK ≤ 1 / 4 := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hDK
  have hGr : 3 / 4 ≤ P.real (G m) := by
    rw [measureReal_def]
    have h34 : (3 / 4 : ℝ) = (ENNReal.ofReal (3 / 4)).toReal := by rw [ENNReal.toReal_ofReal (by norm_num)]
    rw [h34]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hm.le
  have hGc : P.real (G m)ᶜ = 1 - P.real (G m) := probReal_compl_eq_one_sub (hGm m)
  have hU := measureReal_union_le DK (G m)ᶜ (μ := P)
  have hcompl : P.real (DK ∪ (G m)ᶜ)ᶜ = 1 - P.real (DK ∪ (G m)ᶜ) :=
    probReal_compl_eq_one_sub (hDKm.union (hGm m).compl)
  have hmono := measureReal_mono hsub (μ := P) (measure_ne_top _ _)
  have hB2 : 1 / 2 ≤ P.real {ω | (fun t => B t ω) ∈ S} := by linarith
  intro Ω' _ P' _ X hX hXm
  have hmX : Measurable fun ω (t : ℝ≥0) => X t ω := measurable_pi_iff.2 hXm
  have hlaw := Sec2.Assembly2.map_path_eq_map_path hX hB.toIsPreBrownianReal hmX hmB
  have hval : P'.real {ω | stopPath K (fun t => X t ω) ∈ besselSet κ K m} =
      P.real {ω | (fun t => B t ω) ∈ S} := by
    have e1 : {ω | stopPath K (fun t => X t ω) ∈ besselSet κ K m} = (fun ω t => X t ω) ⁻¹' S := rfl
    have e2 : {ω | (fun t => B t ω) ∈ S} = (fun ω t => B t ω) ⁻¹' S := rfl
    rw [e1, e2, measureReal_def, measureReal_def, ← Measure.map_apply hmX hSm, hlaw,
      Measure.map_apply hmB hSm]
  rw [hval]
  exact hB2

/-! ### Brownian scaling -/

/-- The scaled path `t ↦ e⁻¹ y(e² t)`. -/
def scaledPath (e : ℝ≥0) (y : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => (e : ℝ)⁻¹ * y (e ^ 2 * t)

theorem continuous_scaledPath (e : ℝ≥0) {y : ℝ≥0 → ℝ} (hy : Continuous y) : Continuous (scaledPath e y) :=
  continuous_const.mul (hy.comp (continuous_const.mul continuous_id))

theorem scaledPath_zero (e : ℝ≥0) {y : ℝ≥0 → ℝ} (hy0 : y 0 = 0) : scaledPath e y 0 = 0 := by
  simp [scaledPath, hy0]

section Scaling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ℝ≥0 → Ω → ℝ}

theorem isPreBrownianReal_scaledPath (hY : IsPreBrownianReal Y P) {e : ℝ≥0} (he : e ≠ 0) :
    IsPreBrownianReal (fun t ω => scaledPath e (fun s => Y s ω) t) P := by
  have hc : e ^ 2 ≠ 0 := pow_ne_zero 2 he
  have h := hY.smul hc
  have hs : √((e ^ 2 : ℝ≥0) : ℝ) = e := by rw [NNReal.coe_pow]; exact Real.sqrt_sq e.2
  simpa only [scaledPath, hs] using h

/-- The scaled Bessel event: the scaled path, stopped at `K`, lies in the Bessel set. -/
def scaledBesselEvent (κ : ℝ) (K M e : ℝ≥0) (Y : ℝ≥0 → Ω → ℝ) : Set Ω :=
  {ω | stopPath K (scaledPath e (fun t => Y t ω)) ∈ besselSet κ K M}

/-- The scaled Bessel event is an event of the past of `Y` at `e² K`. -/
theorem measurableSet_scaledBesselEvent (κ : ℝ) (K M e : ℝ≥0) :
    MeasurableSet[MeasurableSpace.comap (fun ω (r : Iic (e ^ 2 * K)) => Y r ω) MeasurableSpace.pi]
      (scaledBesselEvent κ K M e Y) := by
  let Φ : (Iic (e ^ 2 * K) → ℝ) → (ℝ≥0 → ℝ) := fun x t =>
    (e : ℝ)⁻¹ * x ⟨e ^ 2 * min t K, mem_Iic.2 (mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le)⟩
  have hΦ : Measurable Φ := measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _
  exact ⟨Φ ⁻¹' besselSet κ K M, hΦ (measurableSet_besselSet κ K M), rfl⟩

/-- **The Bessel step at scale `e`.** On the scaled Bessel event, the point `2e` is not alive at time `K e²`
under `√κ Y`, and `|√κ Y| ≤ M e` on `[0, K e²]`. -/
theorem scaledBesselEvent_spec {κ : ℝ} {K M e : ℝ≥0} (he : e ≠ 0) {ω : Ω} (hYc : Continuous fun t => Y t ω)
    (hY0 : Y 0 ω = 0) (h : ω ∈ scaledBesselEvent κ K M e Y) :
    ¬ Alive (pathDrive (√κ) fun t => Y t ω) (2 * e) (e ^ 2 * K) ∧
      ∀ t ≤ e ^ 2 * K, |√κ * Y t ω| ≤ M * e := by
  have hepos : (0 : ℝ) < e := by exact_mod_cast pos_iff_ne_zero.2 he
  obtain ⟨h1, h2⟩ := besselSet_spec (continuous_scaledPath e hYc) (scaledPath_zero e hY0) h
  refine ⟨fun ⟨u, hu⟩ => h1 ?_, fun t ht => ?_⟩
  · have hu' : IsForwardSol (pathDrive (√κ) fun t => Y t ω) ((e : ℝ) * (2 : ℂ)) (e ^ 2 * K) u := by
      have : (((2 * e : ℝ≥0) : ℝ) : ℂ) = ((e : ℝ) : ℂ) * 2 := by push_cast; ring
      rw [← this]; exact_mod_cast hu
    have hs := LoewnerAlgebra.isForwardSol_scale hepos hu'
    have hT : ((e : ℝ) ^ 2 * K) / (e : ℝ) ^ 2 = K := by field_simp
    have hdrv : (fun t => pathDrive (√κ) (fun t => Y t ω) ((e : ℝ) ^ 2 * t) / e) =
        pathDrive (√κ) (scaledPath e fun t => Y t ω) := by
      funext t
      simp only [pathDrive, scaledPath]
      have h2 : (((e : ℝ) ^ 2 * t)).toNNReal = e ^ 2 * t.toNNReal := by
        rw [Real.toNNReal_mul (by positivity)]
        congr 1
        rw [← NNReal.coe_pow, Real.toNNReal_coe]
      rw [h2]
      field_simp
    rw [hT, hdrv] at hs
    have h2c : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
    exact ⟨_, h2c ▸ hs⟩
  · set s : ℝ≥0 := t / e ^ 2 with hsdef
    have he2 : e ^ 2 ≠ 0 := pow_ne_zero 2 he
    have hts : e ^ 2 * s = t := by rw [hsdef, mul_div_cancel₀ _ he2]
    have hsK : s ≤ K := by
      rw [hsdef, div_le_iff₀ (pos_iff_ne_zero.2 he2), mul_comm]; exact ht
    have := h2 s hsK
    simp only [scaledPath, hts] at this
    have e1 : √κ * Y t ω = e * (√κ * ((e : ℝ)⁻¹ * Y t ω)) := by field_simp
    rw [e1, abs_mul, abs_of_pos hepos, mul_comm (M : ℝ)]
    exact mul_le_mul_of_nonneg_left this hepos.le

end Scaling

/-! ### The Markov splitting at a deterministic time -/

/-- An event of the past at `t₀` and an event of the increments after `t₀` are independent. -/
theorem measure_inter_eq_mul_of_past {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (t₀ : ℝ≥0) {A C : Set Ω}
    (hA : MeasurableSet[MeasurableSpace.comap (fun ω (r : Iic t₀) => B r ω) MeasurableSpace.pi] A)
    (hC : MeasurableSet[MeasurableSpace.comap (fun ω r => B (t₀ + r) ω - B t₀ ω) MeasurableSpace.pi] C) :
    P (A ∩ C) = P A * P C := by
  rw [inter_comm, mul_comm]
  exact (hB.indepFun_shift t₀).meas_inter hC hA

end InteractingSLE.LP.LP3
