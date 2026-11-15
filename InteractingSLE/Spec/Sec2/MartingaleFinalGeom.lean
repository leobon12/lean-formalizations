import InteractingSLE.Spec.Sec2.MartingaleFinalNull
import InteractingSLE.Spec.Sec2.MartingaleFinal
import InteractingSLE.Stochastic.Bessel.Estimate
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Theorem 2.4, converse implication, for the geometric force-point images

Packet PROVE-SEC2-MART2. Specification §2.3, Theorem 2.4 (`source/spec/p001-048.md`, anchors `thm-2.4`,
`thm-2.4-proof`, L815–L898). The force-point coordinates are the geometric images of the force points
under the real Loewner flow of the driver: `geomR W xR i t ω = rightImg (W·ω) (xR i) t` and, by the
reflection `x ↦ −x`, `geomL W xL i t ω = −rightImg (−W·ω) (−xL i) t`.

All deterministic properties that `MartChar.isIntegratedSLEEvolution_of_couplingMean` asks of the
coordinates are proved here for the geometric images of every continuous driver (in particular the
null collision sets, `RealFlow.volume_rightImg_eq_zero`, without a generating curve), and their
adaptedness follows from QuantumZipper's `Dynkin.measurable_of_integralEq`.

## Main results

* `stronglyAdapted_geomR`, `stronglyAdapted_geomL`;
* `isForcePath_rightImg`;
* `isIntegratedSLEEvolution_geom_of_couplingMean`: **Theorem 2.4, converse implication.**
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

open RealFlow

/-! ### Adaptedness of the geometric images -/

section Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

lemma measurable_regFlow_realPath (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hWc : ∀ ω, Continuous (W · ω)) {ε : ℝ} (hε : 0 < ε) (y : ℝ) (s : ℝ≥0) :
    Measurable[𝓕 s] fun ω => regFlow (Bessel.realPath W ω) ε y s := by
  refine QuantumZipper.Dynkin.measurable_of_integralEq 𝓕 hWa hWc
    (Bessel.lipschitzWith_regDrift zero_le_two hε)
    (fun z => by rw [Real.norm_eq_abs]; exact Bessel.abs_regDrift_le zero_le_two hε z)
    (u := y) (e := (-1 : ℝ)) (U := fun t ω => regFlow (Bessel.realPath W ω) ε y t)
    (fun ω t => ?_) (fun ω => ?_) s
  · rw [regFlow_eq (Bessel.continuous_realPath hWc ω) hε y t.coe_nonneg]
    have hI : ∫ r in (0 : ℝ)..t, Bessel.regDrift 2 ε (regFlow (Bessel.realPath W ω) ε y r)
        = ∫ r in (0 : ℝ)..t, Bessel.regDrift 2 ε
          (regFlow (Bessel.realPath W ω) ε y (r.toNNReal : ℝ)) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le t.coe_nonneg] at hr
      simp only [Real.coe_toNNReal r hr.1]
    rw [hI]
    simp only [Bessel.realPath, Real.toNNReal_coe, smul_eq_mul]
    ring
  · exact (continuousOn_regFlow (Bessel.continuous_realPath hWc ω) hε y).comp_continuous
      NNReal.continuous_coe fun t => t.coe_nonneg

lemma measurableSet_forall_le_regFlow (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hWc : ∀ ω, Continuous (W · ω)) {ε : ℝ} (hε : 0 < ε) (y : ℝ) (t : ℝ≥0) :
    MeasurableSet[𝓕 t]
      {ω | ∀ s ∈ Icc 0 (t : ℝ), ε ≤ regFlow (Bessel.realPath W ω) ε y s} := by
  have hset : {ω | ∀ s ∈ Icc 0 (t : ℝ), ε ≤ regFlow (Bessel.realPath W ω) ε y s}
      = (⋂ q : ℚ, {ω | (0 : ℝ) ≤ q → (q : ℝ) ≤ t →
          ε ≤ regFlow (Bessel.realPath W ω) ε y q}) ∩
        {ω | ε ≤ regFlow (Bessel.realPath W ω) ε y t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [forall_Icc_iff_rat ((continuousOn_regFlow (Bessel.continuous_realPath hWc ω) hε y).mono
      fun s hs => hs.1)]
    exact ⟨fun h => ⟨h.1, h.2 t.coe_nonneg⟩, fun h => ⟨h.1, fun _ => h.2⟩⟩
  rw [hset]
  refine (MeasurableSet.iInter fun q => ?_).inter
    (measurableSet_le measurable_const (measurable_regFlow_realPath hWa hWc hε y t))
  by_cases hq : (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ t
  · have hs : ((q : ℝ).toNNReal : ℝ) = q := Real.coe_toNNReal _ hq.1
    have hst : (q : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hq.2
    have hm := (measurable_regFlow_realPath hWa hWc hε y (q : ℝ).toNNReal).mono (𝓕.mono hst)
      le_rfl
    rw [hs] at hm
    have : {ω | (0 : ℝ) ≤ q → (q : ℝ) ≤ t → ε ≤ regFlow (Bessel.realPath W ω) ε y q}
        = {ω | ε ≤ regFlow (Bessel.realPath W ω) ε y q} := by
      ext ω; simp [hq.1, hq.2]
    rw [this]
    exact measurableSet_le measurable_const hm
  · have : {ω | (0 : ℝ) ≤ q → (q : ℝ) ≤ t → ε ≤ regFlow (Bessel.realPath W ω) ε y q}
        = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hq
    rw [this]
    exact MeasurableSet.univ

/-- **The geometric image is adapted.** -/
lemma measurable_rightImg_realPath (hWa : ∀ t, Measurable[𝓕 t] (W t))
    (hWc : ∀ ω, Continuous (W · ω)) (x : ℝ) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => rightImg (Bessel.realPath W ω) x t := by
  refine measurable_of_Iio (mδ := 𝓕 t) fun c => ?_
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hε
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hset : (fun ω => rightImg (Bessel.realPath W ω) x t) ⁻¹' Iio c
      = ⋃ q : ℚ, ⋃ n : ℕ, {_ω : Ω | x < q} ∩
        {ω | ∀ s ∈ Icc 0 (t : ℝ), ε n ≤ regFlow (Bessel.realPath W ω) (ε n) q s} ∩
        {ω | Bessel.realPath W ω t + regFlow (Bessel.realPath W ω) (ε n) q t < c} := by
    ext ω
    have hw := Bessel.continuous_realPath hWc ω
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hV
      obtain ⟨y, hxy, hy, hlt⟩ := exists_lt_of_rightImg_lt hw t.coe_nonneg hV
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + (c - gImg (Bessel.realPath W ω) y t)
        by linarith)
      have hq : Alive (Bessel.realPath W ω) q t := hy.of_le hw hq1.le t.coe_nonneg
      have hgq := abs_gImg_sub_le hw t.coe_nonneg hy hq
      obtain ⟨n, hn⟩ := (alive_iff_regFlow hw t.coe_nonneg).1 hq
      refine ⟨q, n, ⟨hxy.trans hq1, hn⟩, ?_⟩
      rw [← cflow_eq_regFlow hw (hε0 n) hn ⟨t.coe_nonneg, le_rfl⟩]
      have := le_abs_self (gImg (Bessel.realPath W ω) (q : ℝ) t - gImg (Bessel.realPath W ω) y t)
      rw [abs_of_pos (sub_pos.2 hq1)] at hgq
      simp only [gImg] at this hgq hlt hq2 ⊢
      linarith
    · rintro ⟨q, n, ⟨hxq, hn⟩, hlt⟩
      have hq : Alive (Bessel.realPath W ω) q t := ⟨_, isPosSol_regFlow hw (hε0 n) hn⟩
      refine (rightImg_le_gImg hw t.coe_nonneg hxq hq).trans_lt ?_
      rw [gImg, cflow_eq_regFlow hw (hε0 n) hn ⟨t.coe_nonneg, le_rfl⟩]
      exact hlt
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun n => ?_
  refine ((@MeasurableSet.const Ω (𝓕 t) _).inter
    (measurableSet_forall_le_regFlow hWa hWc (hε0 n) q t)).inter ?_
  have h1 : Measurable[𝓕 t] fun ω => Bessel.realPath W ω t := by
    simp only [Bessel.realPath, Real.toNNReal_coe]
    exact hWa t
  exact measurableSet_lt (h1.add (measurable_regFlow_realPath hWa hWc (hε0 n) q t))
    measurable_const

end Adapted

/-! ### The geometric images are force paths -/

/-- **The geometric image is a force path**: continuous, non-decreasing, `dV = 2/(V − w) dt` away
from collisions, and a Lebesgue-null collision set. -/
theorem isForcePath_rightImg {w : ℝ → ℝ} (hw : Continuous w) (x : ℝ) :
    IsForcePath (fun t : ℝ≥0 => w t) (fun t : ℝ≥0 => rightImg w x t) := by
  refine ⟨(continuousOn_rightImg hw x).comp_continuous NNReal.continuous_coe
      fun t => t.coe_nonneg, Or.inl fun a b hab => rightImg_mono_time hw x a.coe_nonneg hab,
    fun u hu hne => ?_, ?_⟩
  · have hcu : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal _ hu.le
    simp only [hcu] at hne ⊢
    refine (hasDerivAt_rightImg hw hu hne).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hu] with s hs
    simp only [Real.coe_toNNReal _ (le_of_lt hs)]
  · refine measure_mono_null (fun u hu => ?_) (volume_rightImg_eq_zero hw x)
    obtain ⟨hu0, hu⟩ := hu
    simp only [Real.coe_toNNReal _ hu0] at hu
    exact ⟨hu0, hu⟩

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The geometric right force-point images** `V^{i,R}_t = rightImg (W·ω) (x^{i,R}) t`. -/
def geomR (W : ℝ≥0 → Ω → ℝ) (xR : Fin nR → ℝ) : Fin nR → ℝ≥0 → Ω → ℝ :=
  fun i t ω => rightImg (Bessel.realPath W ω) (xR i) t

/-- **The geometric left force-point images**, by reflection:
`V^{i,L}_t = −rightImg (−W·ω) (−x^{i,L}) t`. -/
def geomL (W : ℝ≥0 → Ω → ℝ) (xL : Fin nL → ℝ) : Fin nL → ℝ≥0 → Ω → ℝ :=
  fun i t ω => -rightImg (Bessel.realPath (fun t ω => -W t ω) ω) (-xL i) t

lemma realPath_coe (W : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : Bessel.realPath W ω t = W t ω := by
  simp [Bessel.realPath]

lemma realPath_neg (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Bessel.realPath (fun t ω => -W t ω) ω = fun s => -Bessel.realPath W ω s := rfl

lemma isForcePath_geomR {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (xR : Fin nR → ℝ)
    (ω : Ω) (i : Fin nR) : IsForcePath (fun t => W t ω) (fun t => geomR W xR i t ω) := by
  have h := isForcePath_rightImg (Bessel.continuous_realPath hWc ω) (xR i)
  simp only [realPath_coe] at h
  exact h

lemma isForcePath_geomL {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (xL : Fin nL → ℝ)
    (ω : Ω) (i : Fin nL) : IsForcePath (fun t => W t ω) (fun t => geomL W xL i t ω) := by
  have hWc' : ∀ ω, Continuous fun t => -W t ω := fun ω => (hWc ω).neg
  have h := (isForcePath_rightImg (Bessel.continuous_realPath hWc' ω) (-xL i)).neg
  simp only [realPath_coe, neg_neg] at h
  exact h

lemma stronglyAdapted_geomR {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓕 W) (hWc : ∀ ω, Continuous (W · ω)) (xR : Fin nR → ℝ) (i : Fin nR) :
    StronglyAdapted 𝓕 (geomR W xR i) := fun t =>
  (measurable_rightImg_realPath (fun t => (hWa t).measurable) hWc (xR i) t).stronglyMeasurable

lemma stronglyAdapted_geomL {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓕 W) (hWc : ∀ ω, Continuous (W · ω)) (xL : Fin nL → ℝ) (i : Fin nL) :
    StronglyAdapted 𝓕 (geomL W xL i) := fun t =>
  (measurable_rightImg_realPath (fun t => (hWa t).measurable.neg) (fun ω => (hWc ω).neg)
    (-xL i) t).neg.stronglyMeasurable

/-- Merging, in either order of the force points. -/
lemma rightImg_eq_of_eq' {w : ℝ → ℝ} (hw : Continuous w) {x x' s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (heq : rightImg w x s = rightImg w x' s) : rightImg w x t = rightImg w x' t := by
  rcases lt_trichotomy x x' with h | rfl | h
  · exact rightImg_eq_of_eq hw hs hst h heq
  · rfl
  · exact (rightImg_eq_of_eq hw hs hst h heq.symm).symm

/-! ### Theorem 2.4, converse implication -/

/-- **Theorem 2.4, converse implication** (Specification §2.3, p. 35). Let `W` be a continuous
adapted driver with `W₀ = 0`, let `(xL; xR)` be an ordered force word (`x^{i,L} ≤ 0 ≤ x^{j,R}`), and let
the force-point coordinates be the geometric images of the force points under the Loewner flow of
`W` (`geomL`, `geomR`). If every coupling mean `𝔥_t(z)`, `z ∈ ℍ` — for every choice of the bounded
harmonic extensions — is a local martingale before `z` is swallowed, then `W` and the `V^{i,q}`,
coupled with the Brownian motion `B = M/√κ`, form an integrated `SLE_κ(ρ)` evolution up to the
continuation threshold (frozen `IsIntegratedSLEEvolution`, lifetime `thresholdTime`).

No generating curve is needed: the only use of the curve in the source's proof (Lemma 2.5, null
collision sets) holds for the geometric images of every continuous driver
(`RealFlow.volume_rightImg_eq_zero`). -/
theorem isIntegratedSLEEvolution_geom_of_couplingMean {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hx : IsOrderedForceWord xL xR)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => geomL W xL i t ω - W t ω)
          (fun i => geomR W xR i t ω - W t ω))
        (forceJumpSet (fun i => geomL W xL i t ω - W t ω) (fun i => geomR W xR i t ω - W t ω))
        (u ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W (geomL W xL) (geomR W xR)
      (fun t ω => martProc (jointρ ρL ρR) W (jointV (geomL W xL) (geomR W xR)) t ω /
        Real.sqrt κ)
      (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomL W xL i t ω)
        (fun j t => geomR W xR j t ω)) := by
  obtain ⟨hxLa, hxL0, hxRm, hxR0⟩ := hx
  have hw : ∀ ω, Continuous (Bessel.realPath W ω) := Bessel.continuous_realPath hWc
  have hw' : ∀ ω, Continuous (Bessel.realPath (fun t ω => -W t ω) ω) :=
    Bessel.continuous_realPath fun ω => (hWc ω).neg
  have hw0 : ∀ ω, Bessel.realPath W ω 0 = 0 := fun ω => by
    simp [Bessel.realPath, hW0 ω]
  have hw0' : ∀ ω, Bessel.realPath (fun t ω => -W t ω) ω 0 = 0 := fun ω => by
    simp [Bessel.realPath, hW0 ω]
  refine isIntegratedSLEEvolution_of_couplingMean hκ hW0 (fun i ω => ?_) (fun i ω => ?_) hWc hWa
    (stronglyAdapted_geomL hWa hWc xL) (stronglyAdapted_geomR hWa hWc xR) (fun ω t i => ?_)
    (fun ω t i => ?_) (isForcePath_geomL hWc xL) (isForcePath_geomR hWc xR) (fun ω i => ?_)
    (fun ω j => ?_) (fun ω t => ?_) (fun ω t => ?_) (fun ω i j s t hst h => ?_)
    (fun ω i j s t hst h => ?_) (fun ω t ht i j hL hR => ?_) hmart
  · -- left images start at the force points
    simp only [geomL, NNReal.coe_zero]
    rw [rightImg_zero (hw' ω) (hw0' ω) (neg_nonneg.2 (hxL0 i)), neg_neg]
  · simp only [geomR, NNReal.coe_zero]
    exact rightImg_zero (hw ω) (hw0 ω) (hxR0 i)
  · -- side ordering
    have h := le_rightImg (hw' ω) (-xL i) t.coe_nonneg
    rw [realPath_coe] at h
    simp only [geomL]
    linarith
  · have h := le_rightImg (hw ω) (xR i) t.coe_nonneg
    rw [realPath_coe] at h
    exact h
  · -- monotonicity in time
    intro a b hab
    simp only [geomL, neg_le_neg_iff]
    exact rightImg_mono_time (hw' ω) _ a.coe_nonneg hab
  · intro a b hab
    exact rightImg_mono_time (hw ω) _ a.coe_nonneg hab
  · -- index ordering
    intro i j hij
    simp only [geomL, neg_le_neg_iff]
    exact rightImg_mono_index (hw' ω) t.coe_nonneg (neg_le_neg (hxLa hij))
  · intro i j hij
    exact rightImg_mono_index (hw ω) t.coe_nonneg (hxRm hij)
  · -- merged points stay merged
    simp only [geomL, neg_inj] at h ⊢
    exact rightImg_eq_of_eq' (hw' ω) s.coe_nonneg hst h
  · exact rightImg_eq_of_eq' (hw ω) s.coe_nonneg hst h
  · -- left and right images never meet the driver together
    have hsum := rightImg_add_rightImg_neg_ge (hw ω) (xR j) (-xL i) t.coe_nonneg
    rw [← realPath_neg] at hsum
    simp only [geomL, geomR] at hL hR
    have hpos : 0 < Real.sqrt t := Real.sqrt_pos.2 (by exact_mod_cast ht)
    linarith

end MartChar

end InteractingSLE
