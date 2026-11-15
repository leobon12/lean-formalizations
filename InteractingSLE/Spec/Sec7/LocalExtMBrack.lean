/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtMMart
import InteractingSLE.Spec.Sec7.LocalExtA3Var

/-!
# The bracket identity of a random word: the density martingale is the Doléans density of the distant drift

Packet PROVE-LOCEXT-M (clause (a) of `RestartDrivingLocalityInput`; Aux. lemma 55, proof, specification p. 248:
"`(M_t − m, v) = ∫₀ᵗ a_s dB_s` … under `ℚ`, `B^ℚ_{t∧S} = B_{t∧S} + ∫₀^{t∧S} a_s ds` is Brownian motion stopped at `S`").
PROVE-LOCEXT-A3 proved it for a deterministic word (`stochIntegral_srcTheta_ae_eq`, `doleansDensity_srcTheta_ae_eq`).
For an evolution from a random admissible word `c` whose seed pattern is fixed on the good event (new weights `ρL'`,
`ρR'`: the seed weights), with a field satisfying the coupling clause for the same processes:

* `srcThetaW`: the Girsanov drift of the change to the seed weights, cut at the local stop `S` and the level `7r`;
  before `S` it is the source drift (`srcThetaW_eq_of_lt`, (HL7));
* `stochIntegral_indicator_ae_eq`: the Itô integral is local in events of time `0`;
* **`stochIntegral_srcThetaW_ae_eq`**: on every initial event `A` where the source is bounded,
  `∫₀ᵗ θ dB = (𝔥_{t∧S}, v_c) − (𝔥₀, v_c)` almost surely (the brackets of `LocalExtMMart`, the variance identity from the
  coupling clause, `stochIntegral_ae_eq_of_brackets`);
* **`doleansDensity_srcThetaW_ae_eq`**: almost surely, the Doléans density of `θ` past the horizon is the density
  martingale `N_S = martW … S` of the random word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open Coupling Ito Sec2 Girsanov

/-! ### The Itô integral is local in initial events -/

section Locality

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
theorem isRiemannRegular_indicator (hθreg : IsRiemannRegular P θ) (A : Set Ω) :
    IsRiemannRegular P (fun s => A.indicator (θ s)) := by
  filter_upwards [hθreg] with ω hω
  filter_upwards [hω] with u hu
  by_cases hωA : ω ∈ A
  · simpa only [indicator_of_mem hωA] using hu
  · simp only [indicator_of_notMem hωA]; exact continuousWithinAt_const

omit [IsProbabilityMeasure P] in
theorem abs_indicator_le_max {θ : ℝ≥0 → Ω → ℝ} {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (A : Set Ω) (t : ℝ≥0) (ω : Ω) :
    |A.indicator (θ t) ω| ≤ max C 0 := by
  by_cases hω : ω ∈ A
  · rw [indicator_of_mem hω]; exact (hθb t ω).trans (le_max_left _ _)
  · rw [indicator_of_notMem hω, abs_zero]; exact le_max_right _ _

theorem riemannSum_indicator {A : Set Ω} (n : ℕ) (t : ℝ≥0) :
    riemannSum B (fun s => A.indicator (θ s)) n t = A.indicator (riemannSum B θ n t) := by
  funext ω
  by_cases hω : ω ∈ A
  · simp only [riemannSum, indicator_of_mem hω]
  · simp only [riemannSum, indicator_of_notMem hω, zero_mul, Finset.sum_const_zero]

/-- **The Itô integral is local in events of time `0`**: `∫ 1_A θ dB = 1_A ∫ θ dB`. -/
theorem stochIntegral_indicator_ae_eq (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {A : Set Ω} (hA : MeasurableSet[𝓕 0] A)
    (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun s => A.indicator (θ s)) t =ᵐ[P] A.indicator (stochIntegral P 𝓕 B θ t) := by
  have hAt : MeasurableSet[𝓕 t] A := 𝓕.mono (zero_le (a := t)) A hA
  have hAs : ∀ s, MeasurableSet[𝓕 s] A := fun s => 𝓕.mono (zero_le (a := s)) A hA
  have hθAm : StronglyAdapted 𝓕 (fun s => A.indicator (θ s)) := fun s => (hθm s).indicator (hAs s)
  have hθAb : ∀ t ω, |A.indicator (θ t) ω| ≤ max C 0 := fun t ω => by
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω]; exact (hθb t ω).trans (le_max_left _ _)
    · rw [indicator_of_notMem hω, abs_zero]; exact le_max_right _ _
  have hθAreg : IsRiemannRegular P (fun s => A.indicator (θ s)) := by
    filter_upwards [hθreg] with ω hω
    filter_upwards [hω] with u hu
    by_cases hωA : ω ∈ A
    · simpa only [indicator_of_mem hωA] using hu
    · simp only [indicator_of_notMem hωA]; exact continuousWithinAt_const
  have hI := isRiemannLimit_stochIntegral hB hθm hθb hθreg t
  refine stochIntegral_ae_eq_of_isRiemannLimit hB hθAm hθAb hθAreg ⟨hI.1.indicator hAt, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hI.2 (fun n => zero_le) fun n => ?_
  refine eLpNorm_mono fun ω => ?_
  rw [riemannSum_indicator, Pi.sub_apply, Pi.sub_apply]
  by_cases hω : ω ∈ A
  · rw [indicator_of_mem hω, indicator_of_mem hω]
  · rw [indicator_of_notMem hω, indicator_of_notMem hω, sub_zero, norm_zero]; exact norm_nonneg _

/-- A time-constant integrable process measurable at time `0` is a martingale. -/
theorem martingale_const_of_zero {𝓖 : Filtration ℝ≥0 mΩ} {f : Ω → ℝ} (hf : StronglyMeasurable[𝓖 0] f)
    (hfi : Integrable f P) : Martingale (fun _ => f) 𝓖 P :=
  ⟨fun t => hf.mono (𝓖.mono (zero_le (a := t))), fun s _ _ =>
    (condExp_of_stronglyMeasurable (𝓖.le s) (hf.mono (𝓖.mono (zero_le (a := s)))) hfi).eventuallyEq⟩

end Locality

/-! ### The Girsanov drift of the seed weights of a random word -/

section Theta

variable {Ω : Type*} {nL nR : ℕ} {κ : ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {r : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)} {ζ : Ω → ℝ≥0∞} {S : Ω → ℝ≥0} {ω : Ω}

/-- **The Girsanov drift of the change to the weights `(ρL'; ρR')`**, cut at the stop `S` and at the level `7r`. -/
def srcThetaW (κ r : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) (S : Ω → ℝ≥0) (ζ : Ω → ℝ≥0∞)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  weightDrift κ (7 * r) ρL ρL' ρR ρR' (fun ω => (S ω : ℝ≥0∞)) ζ W VL VR

/-- The constant bounding `srcThetaW`. -/
def srcThetaBound (κ r : ℝ) (ρL ρL' : Fin nL → ℝ) (ρR ρR' : Fin nR → ℝ) : ℝ :=
  |1 / Real.sqrt κ| * ((∑ j, |weightDiff ρL ρL' ρR ρR' j|) * (7 * r)⁻¹)

/-- **The distant marks of a good path of the word are `7r` away before the stop.** -/
theorem IsWordGood.gap (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω))
    (hpat : seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR') {t : ℝ≥0} (ht : (t : ℝ≥0∞) < S ω) :
    (∀ i, ρL' i ≠ ρL i → 7 * r ≤ |W t ω - VL i t ω|) ∧
      ∀ i, ρR' i ≠ ρR i → 7 * r ≤ |W t ω - VR i t ω| := by
  have hp' := hg.1.1.isSLEPathUpTo le_rfl
  have htζ : (t : ℝ≥0∞) < ζ ω := ht.trans (hg.lt_zeta hx)
  have htS : (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [← hg.2.2.2]; exact WithTop.coe_le_coe.2 (by exact_mod_cast ht.le)
  have hwt : |W t ω| ≤ r / 4 := abs_le_of_le_localStopPath hp'.continuousOn_w hp'.w_zero hx.2.1.le htS htζ
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have hxi : (c ω).1 i ≠ 0 := fun h0 => hi (by rw [← hpat.1]; simp [seedWtL, h0])
    exact (seven_mul_le_sub_vL hp' hx.1 hx.2 hxi htζ hwt).trans (le_abs_self _)
  · have hxi : (c ω).2 i ≠ 0 := fun h0 => hi (by rw [← hpat.2]; simp [seedWtR, h0])
    rw [abs_sub_comm]
    exact (seven_mul_le_vR_sub hp' hx.1 hx.2 hxi htζ hwt).trans (le_abs_self _)

/-- **Before the stop the Girsanov drift is the source drift** (HL7) along a good path of the word. -/
theorem IsWordGood.srcThetaW_eq (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω))
    (hpat : seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR') (hSζ : (S ω : ℝ≥0∞) ≤ ζ ω) {t : ℝ≥0}
    (ht : t < S ω) :
    srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR t ω =
      srcDrift κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) t := by
  have hp' := hg.1.1.isSLEPathUpTo le_rfl
  have hct : (t : ℝ≥0∞) < S ω := by exact_mod_cast ht
  have hδ : (0 : ℝ) < 7 * r := by have := hx.2.1; positivity
  have htS : ((t : ℝ).toNNReal : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [Real.toNNReal_coe, ← hg.2.2.2]
    exact WithTop.coe_le_coe.2 ht.le
  rw [srcThetaW, weightDrift_eq_of_lt hδ hSζ hp'.continuousOn_w hp'.continuousOn_vL
      hp'.continuousOn_vR (fun t' ht' => hg.gap hx hpat ht') hct,
    show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl,
    srcDrift_eq_distDrift_of_isGoodPath hg.1.1 hg.1.2.1 hx.1 hx.2 hg.1.2.2 t.coe_nonneg htS, Real.toNNReal_coe]
  unfold distDrift
  have hL : ∑ i, (ρL' i - ρL i) / (W t ω - VL i t ω) =
      -∑ i ∈ distSetL (c ω).1, ρL i / (W t ω - VL i t ω) := by
    rw [distSetL, Finset.sum_filter, ← Finset.sum_neg_distrib, ← hpat.1]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (c ω).1 i = 0 <;> simp [seedWtL, h, neg_div]
  have hR : ∑ i, (ρR' i - ρR i) / (W t ω - VR i t ω) =
      -∑ i ∈ distSetR (c ω).2, ρR i / (W t ω - VR i t ω) := by
    rw [distSetR, Finset.sum_filter, ← Finset.sum_neg_distrib, ← hpat.2]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : (c ω).2 i = 0 <;> simp [seedWtR, h, neg_div]
  rw [hL, hR]
  ring

/-- After the stop the Girsanov drift vanishes. -/
theorem srcThetaW_eq_zero_of_lt {t : ℝ≥0} (h : S ω < t) : srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR t ω = 0 :=
  cutDrift_eq_zero (τ := fun ω => (S ω : ℝ≥0∞)) (by exact_mod_cast h)

/-- **The drift of `θ` along a good path of the word**: `∫₀ᵗ θ = ∫₀^{t∧S} A`. -/
theorem IsWordGood.drift_srcThetaW_eq {mΩ : MeasurableSpace Ω} {𝓔 : Filtration ℝ≥0 mΩ}
    (hθ : IsStronglyProgressive 𝓔 (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR)) {C : ℝ}
    (hθb : ∀ t ω, |srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR t ω| ≤ C)
    (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω))
    (hpat : seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR') (hSζ : (S ω : ℝ≥0∞) ≤ ζ ω) (t : ℝ≥0) :
    drift (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t ω =
      ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ),
        srcDrift κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) u := by
  refine integral_eq_of_stop (intervalIntegrable_time hθ hθb ω 0 t) (fun u hu0 huS => ?_) (fun u hu => ?_)
  · have hlt : u.toNNReal < S ω := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]; exact huS
    rw [hg.srcThetaW_eq hx hpat hSζ hlt, Real.coe_toNNReal _ hu0.le]
  · refine srcThetaW_eq_zero_of_lt ?_
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hu.le)]
    exact hu

/-- **The quadratic integral of `θ` along a good path of the word**: `∫₀ᵗ θ² = ∫₀^{t∧S} A²`. -/
theorem IsWordGood.quadInt_srcThetaW_eq {mΩ : MeasurableSpace Ω} {𝓔 : Filtration ℝ≥0 mΩ}
    (hθ : IsStronglyProgressive 𝓔 (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR)) {C : ℝ}
    (hθb : ∀ t ω, |srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR t ω| ≤ C)
    (hg : IsWordGood κ ρL ρR r W VL VR B c ζ S ω) (hx : IsAdmWord r (c ω))
    (hpat : seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR') (hSζ : (S ω : ℝ≥0∞) ≤ ζ ω) (t : ℝ≥0) :
    quadInt (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t ω =
      ∫ u in (0 : ℝ)..((min t (S ω) : ℝ≥0) : ℝ),
        srcDrift κ (c ω).1 (c ω).2 ρL ρR r (fun s : ℝ => W s.toNNReal ω) u ^ 2 := by
  have hint : IntervalIntegrable (fun u : ℝ => srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR u.toNNReal ω ^ 2)
      volume 0 t :=
    (intervalIntegrable_const (c := C ^ 2)).mono_fun'
      ((measurable_time_of_progressive hθ ω).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun u => by
        show ‖srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR u.toNNReal ω ^ 2‖ ≤ C ^ 2
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ _) 2)
  refine integral_eq_of_stop hint (fun u hu0 huS => ?_) (fun u hu => ?_)
  · have hlt : u.toNNReal < S ω := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]; exact huS
    rw [hg.srcThetaW_eq hx hpat hSζ hlt, Real.coe_toNNReal _ hu0.le]
  · rw [srcThetaW_eq_zero_of_lt, zero_pow two_ne_zero]
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hu.le)]
    exact hu

/-- **The Girsanov drift is progressive, bounded and Riemann-regular.** -/
theorem srcThetaW_props {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓔 : Filtration ℝ≥0 mΩ}
    (hWa : AdaptedBefore 𝓔 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓔 ζ (VL i)) (hVRa : ∀ j, AdaptedBefore 𝓔 ζ (VR j))
    (hS : ∀ s : ℝ≥0, MeasurableSet[𝓔 s] {ω | (S ω : ℝ≥0∞) ≤ s}) (hSζ : ∀ ω, (S ω : ℝ≥0∞) ≤ ζ ω)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun s => VL i s ω) {s | (s : ℝ≥0∞) < ζ ω}) ∧
      ∀ j, ContinuousOn (fun s => VR j s ω) {s | (s : ℝ≥0∞) < ζ ω}) (hr : 0 < r) :
    IsStronglyProgressive 𝓔 (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) ∧
      (∀ t ω, |srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR t ω| ≤ srcThetaBound κ r ρL ρL' ρR ρR') ∧
      IsRiemannRegular P (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) := by
  have hδ : (0 : ℝ) < 7 * r := by positivity
  have hU := allMarks_adaptedBefore hVLa hVRa
  have hcont' : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hcont] with ω ⟨hW, hL, hR⟩
    refine ⟨hW, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hL i
    | right i => simpa [allMarks] using hR i
  exact ⟨isStronglyProgressive_cutDrift (continuous_shiftIntegrand κ 1 hδ _) hWa hU hS,
    fun t ω => abs_cutDrift_le (abs_shiftIntegrand_le κ 1 hδ _) t ω,
    isRiemannRegular_cutDrift (continuous_shiftIntegrand κ 1 hδ _) hSζ hcont'⟩

end Theta

/-! ### Conditional second moments of a localized conditionally Gaussian variable -/

section CondGauss

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Localizing and recentring a conditionally Gaussian variable**: if `E[e^{ibY} | m] = cfVal(bμ, b²q)`, then for
`k` and `A` measurable for `m`, `E[e^{ib 1_A (Y − k)} | m] = cfVal(b 1_A (μ − k), b² 1_A q)`. -/
theorem condExp_cexp_indicator_sub (hm : m ≤ mΩ) {Y : Ω → ℝ} (hY : Measurable Y) {μ q k : Ω → ℝ}
    (hk : Measurable[m] k) {A : Set Ω} (hA : MeasurableSet[m] A)
    (hc : ∀ b : ℝ, P[fun ω => Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (b * μ ω) (b ^ 2 * q ω)) (b : ℝ) :
    P[fun ω => Complex.exp (Complex.I * ((b * A.indicator (fun ω => Y ω - k ω) ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (b * A.indicator (fun ω => μ ω - k ω) ω) (b ^ 2 * A.indicator q ω) := by
  set g : Ω → ℂ := A.indicator fun ω => Complex.exp (Complex.I * ((-(b * k ω)) : ℝ)) with hgdef
  have hgm : StronglyMeasurable[m] g := by
    refine (Measurable.indicator ?_ hA).stronglyMeasurable
    exact @GFF.measurable_exp_I_mul Ω m _ (hk.const_mul b).neg
  have heY : Measurable fun ω => Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ)) :=
    GFF.measurable_exp_I_mul (hY.const_mul b)
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ A
    · rw [hgdef, indicator_of_mem hω, hnorm]
    · rw [hgdef, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hEi : Integrable (fun ω => Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ))) P :=
    Integrable.of_bound heY.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (hnorm _).le)
  have hFi : Integrable (fun ω => g ω * Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ))) P :=
    hEi.bdd_mul (hgm.mono hm).aestronglyMeasurable (Eventually.of_forall hgb)
  have hAc : StronglyMeasurable[m] (Aᶜ.indicator fun _ => (1 : ℂ)) :=
    (stronglyMeasurable_const.indicator hA.compl)
  have hAci : Integrable (Aᶜ.indicator fun _ => (1 : ℂ)) P :=
    (integrable_const (1 : ℂ)).indicator (hm _ hA.compl)
  have e : (fun ω => Complex.exp (Complex.I * ((b * A.indicator (fun ω => Y ω - k ω) ω : ℝ) : ℂ))) =
      (fun ω => g ω * Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ))) + Aᶜ.indicator fun _ => (1 : ℂ) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [hgdef, indicator_of_mem hω, Pi.add_apply, indicator_of_notMem (show ω ∉ Aᶜ from fun h => h hω),
        add_zero, ← Complex.exp_add]
      congr 1; push_cast; ring
    · simp only [hgdef, indicator_of_notMem hω, mul_zero, Complex.ofReal_zero, Complex.exp_zero, zero_mul,
        Pi.add_apply, indicator_of_mem (show ω ∈ Aᶜ from hω), zero_add]
  rw [e]
  have hpull := condExp_bilin_of_stronglyMeasurable_left (m := m) (μ := P) (ContinuousLinearMap.mul ℝ ℂ) hgm
    (by simpa using hFi) hEi
  filter_upwards [condExp_add hFi hAci m, hpull, hc b,
    (condExp_of_stronglyMeasurable hm hAc hAci).eventuallyEq] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply]
  simp only [ContinuousLinearMap.mul_apply'] at h2
  rw [h2, h3, h4]
  by_cases hω : ω ∈ A
  · simp only [hgdef, indicator_of_mem hω, indicator_of_notMem (show ω ∉ Aᶜ from fun h => h hω), add_zero, cfVal,
      ← Complex.exp_add]
    congr 1; push_cast; ring
  · simp only [hgdef, indicator_of_notMem hω, zero_mul, indicator_of_mem (show ω ∈ Aᶜ from hω), zero_add, cfVal,
      mul_zero, Complex.ofReal_zero, sub_zero, Complex.exp_zero]

/-- **The variance identity for a localized conditionally Gaussian variable** at two nested σ-algebras
`m₀ ≤ m₁`: `E[(1_A (μ₁ − μ₀))²] = E[1_A q₀] − E[1_A q₁]`. -/
theorem integral_sq_indicator_eq_of_condGauss {m₀ m₁ : MeasurableSpace Ω} (hm₀₁ : m₀ ≤ m₁) (hm₁ : m₁ ≤ mΩ)
    {Y μ₀ q₀ μ₁ q₁ : Ω → ℝ} (hY : Measurable[mΩ] Y) (hμ₀ : Measurable[m₀] μ₀) {A : Set Ω}
    (hA : MeasurableSet[m₀] A)
    (hc₀ : ∀ b : ℝ, P[fun ω => Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ)) | m₀] =ᵐ[P]
      fun ω => cfVal (b * μ₀ ω) (b ^ 2 * q₀ ω))
    (hc₁ : ∀ b : ℝ, P[fun ω => Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ)) | m₁] =ᵐ[P]
      fun ω => cfVal (b * μ₁ ω) (b ^ 2 * q₁ ω))
    (hYi : Integrable (fun ω => A.indicator (fun ω => Y ω - μ₀ ω) ω ^ 2) P)
    (hq₁i : Integrable (A.indicator q₁) P)
    (hμi : Integrable (fun ω => A.indicator (fun ω => μ₁ ω - μ₀ ω) ω ^ 2) P) :
    ∫ ω, A.indicator (fun ω => μ₁ ω - μ₀ ω) ω ^ 2 ∂P =
      ∫ ω, A.indicator q₀ ω ∂P - ∫ ω, A.indicator q₁ ω ∂P := by
  have hm₀ : m₀ ≤ mΩ := hm₀₁.trans hm₁
  have hYA : Measurable[mΩ] fun ω => A.indicator (fun ω => Y ω - μ₀ ω) ω :=
    (hY.sub (hμ₀.mono hm₀ le_rfl)).indicator (hm₀ _ hA)
  have hYi' : Integrable (fun ω => (A.indicator (fun ω => Y ω - μ₀ ω) ω - 0) ^ 2) P := by simpa using hYi
  have h1 := ae_condExp_sq_sub_of_condGauss hm₁ hYA
    (condExp_cexp_indicator_sub hm₁ hY (hμ₀.mono hm₀₁ le_rfl) (hm₀₁ _ hA) hc₁) 0 hYi'
  have h0 := ae_condExp_sq_sub_of_condGauss hm₀ hYA
    (condExp_cexp_indicator_sub hm₀ hY hμ₀ hA hc₀) 0 hYi'
  have e1 : ∫ ω, (A.indicator (fun ω => Y ω - μ₀ ω) ω - 0) ^ 2 ∂P =
      ∫ ω, (A.indicator q₁ ω + (A.indicator (fun ω => μ₁ ω - μ₀ ω) ω - 0) ^ 2) ∂P := by
    rw [← integral_condExp hm₁]; exact integral_congr_ae h1
  have e0 : ∫ ω, (A.indicator (fun ω => Y ω - μ₀ ω) ω - 0) ^ 2 ∂P =
      ∫ ω, (A.indicator q₀ ω + (A.indicator (fun ω => μ₀ ω - μ₀ ω) ω - 0) ^ 2) ∂P := by
    rw [← integral_condExp hm₀]; exact integral_congr_ae h0
  have hz : ∀ ω, (A.indicator (fun ω => μ₀ ω - μ₀ ω) ω - 0) ^ 2 = 0 := fun ω => by
    by_cases hω : ω ∈ A <;> simp [hω]
  simp only [hz, add_zero] at e0
  simp only [sub_zero] at e1 e0
  rw [integral_add hq₁i hμi] at e1
  linarith

theorem sq_le_two_mul_exp_add_exp (x : ℝ) : x ^ 2 ≤ 2 * (Real.exp x + Real.exp (-x)) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have h2 : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases abs_choice x with h | h <;> rw [h] <;> linarith [Real.exp_pos x, Real.exp_pos (-x)]
  have h3 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith [abs_nonneg x]

/-- **Square integrability of a localized conditionally Gaussian variable** with bounded conditional variance on the
localization event (exponential moments, `lintegral_mul_exp_of_condGauss`). -/
theorem integrable_sq_indicator_of_condGauss (hm : m ≤ mΩ) {X a q : Ω → ℝ} (hX : Measurable[mΩ] X)
    (hc : ∀ b : ℝ, P[fun ω => Complex.exp (Complex.I * ((b * X ω : ℝ) : ℂ)) | m] =ᵐ[P]
      fun ω => cfVal (b * a ω) (b ^ 2 * q ω))
    (ha : Measurable[m] a) {A : Set Ω} (hA : MeasurableSet[m] A) {M : ℝ} (hqA : ∀ ω ∈ A, q ω ≤ M) :
    Integrable (fun ω => A.indicator (fun ω => X ω - a ω) ω ^ 2) P := by
  have hamΩ : Measurable[mΩ] a := ha.mono hm le_rfl
  have hfm : Measurable[mΩ] fun ω => A.indicator (fun ω => X ω - a ω) ω ^ 2 :=
    ((hX.sub hamΩ).indicator (hm _ hA)).pow_const 2
  have hexp : ∀ lam : ℝ, ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (lam * (X ω - a ω)))) ω ∂P ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * M / 2)) := fun lam => by
    have hW : Measurable[m] (A.indicator fun ω => ENNReal.ofReal (Real.exp (-(lam * a ω)))) :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ha.const_mul lam).neg)).indicator hA
    have key := lintegral_mul_exp_of_condGauss hm hX hc hW lam
    have e1 : ∀ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (-(lam * a ω)))) ω *
        ENNReal.ofReal (Real.exp (lam * X ω)) =
        A.indicator (fun ω => ENNReal.ofReal (Real.exp (lam * (X ω - a ω)))) ω := fun ω => by
      by_cases hω : ω ∈ A
      · simp only [indicator_of_mem hω]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring
      · simp [hω]
    have e2 : ∀ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (-(lam * a ω)))) ω *
        ENNReal.ofReal (Real.exp (lam * a ω + lam ^ 2 * q ω / 2)) =
        A.indicator (fun ω => ENNReal.ofReal (Real.exp (lam ^ 2 * q ω / 2))) ω := fun ω => by
      by_cases hω : ω ∈ A
      · simp only [indicator_of_mem hω]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring
      · simp [hω]
    simp only [e1, e2] at key
    rw [key]
    calc ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (lam ^ 2 * q ω / 2))) ω ∂P
        ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (lam ^ 2 * M / 2)) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ A
          · rw [indicator_of_mem hω]
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have := hqA ω hω
            have : 0 ≤ lam ^ 2 := sq_nonneg lam
            nlinarith
          · rw [indicator_of_notMem hω]; exact zero_le
      _ = ENNReal.ofReal (Real.exp (lam ^ 2 * M / 2)) := by simp
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => sq_nonneg _)]
  have hpt : ∀ ω, ENNReal.ofReal (A.indicator (fun ω => X ω - a ω) ω ^ 2) ≤
      2 * (A.indicator (fun ω => ENNReal.ofReal (Real.exp (1 * (X ω - a ω)))) ω +
        A.indicator (fun ω => ENNReal.ofReal (Real.exp ((-1) * (X ω - a ω)))) ω) := fun ω => by
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, one_mul, neg_one_mul]
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul zero_le_two]
      exact ENNReal.ofReal_le_ofReal (sq_le_two_mul_exp_add_exp _)
    · simp [hω]
  have hm1 : Measurable fun ω => A.indicator (fun ω => ENNReal.ofReal (Real.exp (1 * (X ω - a ω)))) ω :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hX.sub hamΩ).const_mul 1))).indicator (hm _ hA)
  calc ∫⁻ ω, ENNReal.ofReal (A.indicator (fun ω => X ω - a ω) ω ^ 2) ∂P
      ≤ ∫⁻ ω, 2 * (A.indicator (fun ω => ENNReal.ofReal (Real.exp (1 * (X ω - a ω)))) ω +
        A.indicator (fun ω => ENNReal.ofReal (Real.exp ((-1) * (X ω - a ω)))) ω) ∂P := lintegral_mono hpt
    _ = 2 * (∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp (1 * (X ω - a ω)))) ω ∂P +
        ∫⁻ ω, A.indicator (fun ω => ENNReal.ofReal (Real.exp ((-1) * (X ω - a ω)))) ω ∂P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hm1]
    _ < ⊤ := by
          refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
          · exact (hexp 1).trans_lt ENNReal.ofReal_lt_top
          · exact (hexp (-1)).trans_lt ENNReal.ofReal_lt_top

end CondGauss

/-! ### The variance identity of the random word -/

section Variance

variable {κ : ℝ} {nL nR : ℕ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {S : Ω → ℝ≥0} {A : Set Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- On the localization event, the localized tested mean is the tested mean of the word. -/
theorem srcMeanW_eq_srcMeanAt (hadm : ∀ ω, IsAdmWord r (c ω)) {σ : Ω → ℝ≥0} {ω : Ω} (hω : ω ∈ A) (t : ℝ≥0) :
    srcMeanW κ ρL ρR r W VL VR c σ A t ω =
      srcMeanAt κ (c ω).1 (c ω).2 ρL ρR r W VL VR (min t (σ ω)) ω := by
  simp only [srcMeanW, srcMeanInt, hω, ↓reduceIte, vSrcW_of_adm κ ρL ρR r (hadm ω), srcMeanAt, bheProc]

/-- **The variance identity of the random word**, localized on an initial event `A` on which the source data are
bounded: `E[(1_A ((𝔥_{t∧S}, v_c) − (𝔥₀, v_c)))²] = E[1_A ∫₀ᵗ θ²]`. -/
theorem integral_srcMeanW_sub_sq_eq [IsProbabilityMeasure P]
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (hhm : Measurable h)
    (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω)) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsWordGood κ ρL ρR r W VL VR B c ζ S ω)
    (hpat : ∀ ω ∈ G, seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR')
    (hS𝓖 : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0)) (hSζ : ∀ ω, (S ω : ℝ≥0∞) ≤ ζ ω)
    {𝓔 : Filtration ℝ≥0 mΩ} (hθp : IsStronglyProgressive 𝓔 (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR)) {C : ℝ}
    (hθb : ∀ t ω, |srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR t ω| ≤ C)
    (hA0 : MeasurableSet[𝓖 0] A) (hAG : A ⊆ G) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) (hAn : ∀ ω ∈ A, |normW κ ρL ρR r (c ω)| ≤ m)
    (hAc : ∀ ω ∈ A, |centreW κ ρL ρR r (c ω)| ≤ m) (t : ℝ≥0)
    (hmeanm : Measurable (srcMeanW κ ρL ρR r W VL VR c S A t)) :
    ∫ ω, A.indicator (fun ω => srcMeanW κ ρL ρR r W VL VR c S A t ω - centreW κ ρL ρR r (c ω)) ω ^ 2 ∂P =
      ∫ ω, A.indicator (quadInt (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t) ω ∂P := by
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hgood : ∀ᵐ ω ∂P, IsWordPath κ ρL ρR W VL VR B ζ c ω := by
    filter_upwards [hGae] with ω hω using (hG ω hω).1
  have hcm : Measurable c := hc.mono (𝓖.le 0) le_rfl
  -- the stopping times and their σ-algebras
  have hτ : IsStoppingTime 𝓖 fun ω => min (S ω : WithTop ℝ≥0) (t : WithTop ℝ≥0) := hS𝓖.min_const t
  have hτ0 : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const _ _
  have h01 : hτ0.measurableSpace ≤ hτ.measurableSpace :=
    hτ0.measurableSpace_mono hτ fun ω => by simp
  have hm0 : hτ0.measurableSpace = 𝓖 0 := IsStoppingTime.measurableSpace_const 𝓖 0
  have hτS : ∀ᵐ ω ∂P, min (S ω : WithTop ℝ≥0) (t : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    filter_upwards [hGae] with ω hω
    rw [← (hG ω hω).2.2.2]; exact min_le_left _ _
  have hτ0S : ∀ᵐ ω ∂P, ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω :=
    ae_of_all _ fun ω => by simp
  have huntop : ∀ ω, (min (S ω : WithTop ℝ≥0) (t : WithTop ℝ≥0)).untopD 0 = min t (S ω) := fun ω => by
    rw [← WithTop.coe_min, WithTop.untopD_coe, min_comm]
  have hc₁ := condExp_cexp_shift hcf hhm hc hadm hgood hτ hτS
  have hc₀ := condExp_cexp_shift hcf hhm hc hadm hgood hτ0 hτ0S
  set Y := shiftPairW κ ρL ρR r c h with hYdef
  have hY : Measurable Y := measurable_shiftPairW hhm hcm
  -- the time-`0` mean is `normW / 2`
  set μ₀ : Ω → ℝ := fun ω => normW κ ρL ρR r (c ω) / 2 with hμ₀def
  set q₀ : Ω → ℝ := fun ω => normW κ ρL ρR r (c ω) with hq₀def
  have hc₀' : ∀ b : ℝ, P[fun ω => Complex.exp (Complex.I * ((b * Y ω : ℝ) : ℂ)) | hτ0.measurableSpace] =ᵐ[P]
      fun ω => cfVal (b * μ₀ ω) (b ^ 2 * q₀ ω) := fun b => by
    filter_upwards [hc₀ b, hGae] with ω h1 hω
    have hg := hG ω hω
    rw [h1]
    simp only [WithTop.untopD_coe]
    rw [srcMeanAt_zero_of_isGoodPath ⟨hg.1.1, hg.1.2.1⟩ (hadm ω).1 (hadm ω).2, ← centreW_of_adm κ ρL ρR r (hadm ω)]
    have hE := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1.1 hg.1.2.1 (hadm ω).1
      (hadm ω).2 hg.1.2.2 (t := 0) (by simp)
    simp only [srcEnergyAt]
    rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, hE,
      ← normW_of_adm κ ρL ρR r (hadm ω)]
    simp [hμ₀def, hq₀def]
  have hμ₀m : Measurable[hτ0.measurableSpace] μ₀ := by
    rw [hm0]; exact ((measurable_normW κ ρL ρR r).comp hc).div_const 2
  have hAτ0 : MeasurableSet[hτ0.measurableSpace] A := by rw [hm0]; exact hA0
  -- the time-`τ` data
  set μ₁ : Ω → ℝ := fun ω => srcMeanAt κ (c ω).1 (c ω).2 ρL ρR r W VL VR
    ((min (S ω : WithTop ℝ≥0) (t : WithTop ℝ≥0)).untopD 0) ω - centreW κ ρL ρR r (c ω) +
      normW κ ρL ρR r (c ω) / 2 with hμ₁def
  set q₁ : Ω → ℝ := fun ω => srcEnergyAt κ (c ω).1 (c ω).2 ρL ρR r W
    ((min (S ω : WithTop ℝ≥0) (t : WithTop ℝ≥0)).untopD 0) ω with hq₁def
  -- the pathwise identities on `A`
  have hq₁A : ∀ ω ∈ A, q₁ ω = q₀ ω - quadInt (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t ω := fun ω hω => by
    have hg := hG ω (hAG hω)
    have hle : ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
      rw [← hg.2.2.2]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
    have hE := loewnerGreenEnergy_vSrc_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1.1 hg.1.2.1 (hadm ω).1
      (hadm ω).2 hg.1.2.2 hle
    simp only [hq₁def, huntop, srcEnergyAt, hq₀def]
    rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, hE,
      hg.quadInt_srcThetaW_eq hθp hθb (hadm ω) (hpat ω (hAG hω)) (hSζ ω) t, normW_of_adm κ ρL ρR r (hadm ω)]
    rfl
  have hμA : ∀ ω ∈ A, μ₁ ω - μ₀ ω = srcMeanW κ ρL ρR r W VL VR c S A t ω - centreW κ ρL ρR r (c ω) :=
    fun ω hω => by
      simp only [hμ₁def, hμ₀def, huntop, srcMeanW_eq_srcMeanAt hadm hω]
      ring
  -- bounds on `A`
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  set K := meanSrcBound κ ρL ρR r * |m| * volume.real (srcBox r) with hK
  have hmeanb : ∀ ω, |srcMeanW κ ρL ρR r W VL VR c S A t ω| ≤ K := fun ω => by
    have hpt : ∀ z, ‖srcMeanInt κ ρL ρR r W VL VR c S A t z ω‖ ≤
        (srcBox r).indicator (fun _ => meanSrcBound κ ρL ρR r * |m|) z := fun z => by
      rw [Real.norm_eq_abs]
      exact abs_srcMeanInt_le hadm hG hAG hAm (fun _ => le_rfl) subset_rfl t z ω
    have h := norm_integral_le_of_norm_le (integrable_srcBox_indicator r _) (ae_of_all _ hpt)
    rwa [integral_srcBox_indicator, Real.norm_eq_abs] at h
  have hquadb : ∀ ω, |quadInt (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t ω| ≤ C ^ 2 * t := fun ω => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (f := fun u : ℝ => srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR u.toNNReal ω ^ 2) (C := C ^ 2) fun u _ => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hθb _ _) 2
    rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg t.coe_nonneg] at this
  have hQm : Measurable (quadInt (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t) :=
    ((stronglyMeasurable_integral_comp hθp (measurable_id.pow_const 2) t).mono (𝓔.le t)).measurable
  have hcentm : Measurable fun ω => centreW κ ρL ρR r (c ω) := (measurable_centreW κ ρL ρR r).comp hcm
  have hq₀m : Measurable q₀ := (measurable_normW κ ρL ρR r).comp hcm
  have hAm' : MeasurableSet A := 𝓖.le 0 _ hA0
  -- the integrability hypotheses
  have hYi := integrable_sq_indicator_of_condGauss hτ0.measurableSpace_le hY hc₀' hμ₀m hAτ0 (M := m)
    fun ω hω => (le_abs_self _).trans (hAn ω hω)
  have hq₁e : A.indicator q₁ = A.indicator fun ω => q₀ ω - quadInt (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t ω :=
    funext fun ω => by
      by_cases hω : ω ∈ A
      · rw [indicator_of_mem hω, indicator_of_mem hω, hq₁A ω hω]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  have hq₁i : Integrable (A.indicator q₁) P := by
    rw [hq₁e]
    refine Integrable.of_bound ((hq₀m.sub hQm).indicator hAm').aestronglyMeasurable (|m| + C ^ 2 * t)
      (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, Real.norm_eq_abs]
      exact (abs_sub _ _).trans (add_le_add ((hAn ω hω).trans (le_abs_self m)) (hquadb ω))
    · rw [indicator_of_notMem hω, norm_zero]
      positivity
  have hμe : (fun ω => A.indicator (fun ω => μ₁ ω - μ₀ ω) ω ^ 2) =
      fun ω => A.indicator (fun ω => srcMeanW κ ρL ρR r W VL VR c S A t ω - centreW κ ρL ρR r (c ω)) ω ^ 2 :=
    funext fun ω => by
      by_cases hω : ω ∈ A
      · rw [indicator_of_mem hω, indicator_of_mem hω, hμA ω hω]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  have hμi : Integrable (fun ω => A.indicator (fun ω => μ₁ ω - μ₀ ω) ω ^ 2) P := by
    rw [hμe]
    refine Integrable.of_bound ((((hmeanm.sub hcentm).indicator hAm').pow_const 2).aestronglyMeasurable)
      ((K + |m|) ^ 2) (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
        (add_le_add (hmeanb ω) ((hAc ω hω).trans (le_abs_self m)))) 2
    · rw [indicator_of_notMem hω, Real.norm_eq_abs]; simp only [ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, abs_zero]; positivity
  have key := integral_sq_indicator_eq_of_condGauss h01 hτ.measurableSpace_le hY hμ₀m hAτ0 hc₀' hc₁ hYi hq₁i hμi
  rw [hμe] at key
  rw [key, ← integral_sub (by
    refine Integrable.of_bound (hq₀m.indicator hAm').aestronglyMeasurable |m| (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, Real.norm_eq_abs]; exact (hAn ω hω).trans (le_abs_self m)
    · rw [indicator_of_notMem hω, norm_zero]; exact abs_nonneg m) hq₁i]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  rw [hq₁e]
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω]; ring
  · simp only [indicator_of_notMem hω, sub_zero]

end Variance

/-! ### The bracket identity -/

section Bracket

theorem isStronglyProgressive_indicator {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {θ : ℝ≥0 → Ω → ℝ} (hθ : IsStronglyProgressive 𝓕 θ) {A : Set Ω} (hA : MeasurableSet[𝓕 0] A) :
    IsStronglyProgressive 𝓕 (fun s => A.indicator (θ s)) := fun i => by
  have hS : MeasurableSet[Subtype.instMeasurableSpace.prod (𝓕 i)] {p : Set.Iic i × Ω | p.2 ∈ A} :=
    measurable_snd (𝓕.mono (zero_le (a := i)) A hA)
  have e : (fun p : Set.Iic i × Ω => A.indicator (θ p.1) p.2) =
      {p : Set.Iic i × Ω | p.2 ∈ A}.indicator fun p => θ p.1 p.2 := by
    funext p; by_cases hp : p.2 ∈ A <;> simp [hp]
  rw [e]
  exact (hθ i).indicator hS

variable {κ : ℝ} {nL nR : ℕ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 𝓖 : Filtration ℝ≥0 mΩ}
  {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {S : Ω → ℝ≥0} {A : Set Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- On the localization event, the cross process is `srcMeanW · B_{t∧S} − ∫ v (Im f_{t∧S} − Im z)`. -/
theorem srcCrossW_eq (hadm : ∀ ω, IsAdmWord r (c ω)) (hG : ∀ ω ∈ G, IsWordGood κ ρL ρR r W VL VR B c ζ S ω)
    (hAG : A ⊆ G) {ω : Ω} (hω : ω ∈ A) (t : ℝ≥0) :
    srcCrossW κ ρL ρR r W VL VR B c S A t ω =
      srcMeanW κ ρL ρR r W VL VR c S A t ω * B (min t (S ω)) ω -
        ∫ z, vSrcW κ ρL ρR r (c ω) z * ((fwdMap (rpath (W · ω)) (min t (S ω) : ℝ≥0) z).im - z.im) := by
  have hg := hG ω (hAG hω)
  have hx := hadm ω
  have hle : ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
    rw [← hg.2.2.2]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
  have hv : vSrcW κ ρL ρR r (c ω) = vSrc κ (c ω).1 (c ω).2 ρL ρR r := vSrcW_of_adm κ ρL ρR r hx
  have hvm : Measurable (vSrc κ (c ω).1 (c ω).2 ρL ρR r) := measurable_vSrc hx.1 hx.2
  have hi1 := integrable_couplingMean_mul_of_isGoodPath hg.1.1 hg.1.2.1 hx.1 hx.2 hg.1.2.2 hle
    (isBoundedHarmonicExtension_bheProc (W := W) (VL := VL) (VR := VR) κ ρL ρR ω (min t (S ω))) hvm
    (fun z => le_rfl)
  have hi2 := integrable_mul_im_sub_of_isGoodPath hg.1.1 hg.1.2.1 hx.1 hx.2 hg.1.2.2 hle hvm (fun z => le_rfl)
  simp only [srcCrossW, srcMeanW, srcCrossInt, srcMeanInt, hω, ↓reduceIte, hv]
  have e : ∀ z, vSrc κ (c ω).1 (c ω).2 ρL ρR r z * (couplingMean κ (fun s : ℝ => W s.toNNReal ω)
      (min t (S ω) : ℝ≥0) (bheProc κ ρL ρR W VL VR ω (min t (S ω))) z * B (min t (S ω)) ω -
      ((fwdMap (rpath (W · ω)) (min t (S ω) : ℝ≥0) z).im - z.im)) =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (S ω) : ℝ≥0)
        (bheProc κ ρL ρR W VL VR ω (min t (S ω))) z * vSrc κ (c ω).1 (c ω).2 ρL ρR r z * B (min t (S ω)) ω -
      vSrc κ (c ω).1 (c ω).2 ρL ρR r z * ((fwdMap (rpath (W · ω)) (min t (S ω) : ℝ≥0) z).im - z.im) :=
    fun z => by ring
  simp only [e]
  have hi1' : Integrable (fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (S ω) : ℝ≥0)
      (bheProc κ ρL ρR W VL VR ω (min t (S ω))) z * vSrc κ (c ω).1 (c ω).2 ρL ρR r z) := hi1
  rw [integral_sub (hi1'.mul_const _) hi2, integral_mul_const]

/-- **The bracket identity of a random word** (Aux. lemma 55, `(M_t − m, v) = ∫₀ᵗ a_s dB_s`), on every initial event `A`
where the source data are bounded: almost surely on `A`, `∫₀ᵗ θ dB = (𝔥_{t∧S}, v_c) − (𝔥₀, v_c)`. -/
theorem stochIntegral_srcThetaW_ae_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r)
    (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 (fun ω => (c ω).1) (fun ω => (c ω).2) W VL VR B ζ)
    (hBn : IsFilteredBrownianReal (nullAugmented 𝓕 P) B P) (h𝓖 : 𝓖 ≤ 𝓕)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (hhm : Measurable h)
    (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsWordGood κ ρL ρR r W VL VR B c ζ S ω)
    (hpat : ∀ ω ∈ G, seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR')
    (hS𝓖 : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0)) (hSζ : ∀ ω, (S ω : ℝ≥0∞) ≤ ζ ω)
    (hA0 : MeasurableSet[𝓖 0] A) (hAG : A ⊆ G) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) (hAn : ∀ ω ∈ A, |normW κ ρL ρR r (c ω)| ≤ m)
    (hAc : ∀ ω ∈ A, |centreW κ ρL ρR r (c ω)| ≤ m) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ A → stochIntegral P (nullAugmented 𝓕 P) B (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR) t ω =
      srcMeanW κ ρL ρR r W VL VR c S A t ω - centreW κ ρL ρR r (c ω) := by
  set 𝓔 := nullAugmented 𝓕 P with h𝓔
  set θ := srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR with hθdef
  have hle𝓖 : ∀ t, 𝓖 t ≤ 𝓔 t := fun t => (h𝓖 t).trans (le_nullAugmented 𝓕 P t)
  have hS : IsStoppingTime 𝓔 fun ω => (S ω : WithTop ℝ≥0) := fun t => hle𝓖 t _ (hS𝓖 t)
  have hc𝓕 : Measurable[𝓕 0] c := hc.mono (h𝓖 0) le_rfl
  have hA0' : MeasurableSet[𝓔 0] A := hle𝓖 0 _ hA0
  have hGm : MeasurableSet G := 𝓔.le 0 G hG0
  have hAm' : MeasurableSet A := 𝓔.le 0 A hA0'
  have hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓔 t] N :=
    fun t N hN h0 => measurableSet_nullAugmented_of_null hN h0 t
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  -- the drift
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun s => VL i s ω) {s | (s : ℝ≥0∞) < ζ ω}) ∧
      ∀ j, ContinuousOn (fun s => VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hGae] with ω hω
    have hp := (hG ω hω).1.1
    exact ⟨hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  obtain ⟨hθp, hθb, hθreg⟩ := srcThetaW_props (P := P) (𝓔 := 𝓔) (ρL' := ρL') (ρR' := ρR') (κ := κ)
    (adaptedBefore_mono (le_nullAugmented 𝓕 P) hE.2.2.2.1)
    (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hE.2.2.2.2.1 i))
    (fun j => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hE.2.2.2.2.2.1 j)) (fun s => hS s) hSζ hcont hr0
  set C := srcThetaBound κ r ρL ρL' ρR ρR' with hC
  -- the martingales of `LocalExtMMart`
  have hmean := martingale_srcMeanW hE hc𝓕 hadm hG0 hG hS hA0' hAG hκ hr0 hAm
  have hcross := martingale_srcCrossW hE hc𝓕 hadm hG0 hG hS hA0' hAG hκ hr0 hGc hAm
  -- the localized processes
  set θA : ℝ≥0 → Ω → ℝ := fun s => A.indicator (θ s) with hθAdef
  set cA : Ω → ℝ := A.indicator fun ω => centreW κ ρL ρR r (c ω) with hcAdef
  have hcAm : StronglyMeasurable[𝓔 0] cA :=
    ((((measurable_centreW κ ρL ρR r).comp hc).mono (hle𝓖 0) le_rfl).indicator hA0').stronglyMeasurable
  have hcAb : ∀ ω, |cA ω| ≤ |m| := fun ω => by
    by_cases hω : ω ∈ A
    · rw [hcAdef, indicator_of_mem hω]; exact (hAc ω hω).trans (le_abs_self m)
    · rw [hcAdef, indicator_of_notMem hω, abs_zero]; exact abs_nonneg m
  have hcAi : Integrable cA P := Integrable.of_bound (hcAm.mono (𝓔.le 0)).aestronglyMeasurable |m|
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hcAb ω)
  set X : ℝ≥0 → Ω → ℝ := fun t ω => srcMeanW κ ρL ρR r W VL VR c S A t ω - cA ω with hXdef
  have hXA : ∀ t ω, X t ω = A.indicator (fun ω => srcMeanW κ ρL ρR r W VL VR c S A t ω -
      centreW κ ρL ρR r (c ω)) ω := fun t ω => by
    by_cases hω : ω ∈ A
    · simp [hXdef, hcAdef, hω]
    · simp [hXdef, hcAdef, hω, srcMeanW, srcMeanInt]
  have hX : Martingale X 𝓔 P := hmean.sub (martingale_const_of_zero hcAm hcAi)
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; positivity
  set K := meanSrcBound κ ρL ρR r * |m| * volume.real (srcBox r) with hK
  have hmeanb : ∀ t ω, |srcMeanW κ ρL ρR r W VL VR c S A t ω| ≤ K := fun t ω => by
    have hpt : ∀ z, ‖srcMeanInt κ ρL ρR r W VL VR c S A t z ω‖ ≤
        (srcBox r).indicator (fun _ => meanSrcBound κ ρL ρR r * |m|) z := fun z => by
      rw [Real.norm_eq_abs]
      exact abs_srcMeanInt_le hadm hG hAG hAm (fun _ => le_rfl) subset_rfl t z ω
    have h := norm_integral_le_of_norm_le (integrable_srcBox_indicator r _) (ae_of_all _ hpt)
    rwa [integral_srcBox_indicator, Real.norm_eq_abs] at h
  have hXb : ∀ t ω, |X t ω| ≤ K + |m| := fun t ω => (abs_sub _ _).trans (add_le_add (hmeanb t ω) (hcAb ω))
  have hXL2 : ∀ t, MemLp (X t) 2 P := fun t => MemLp.of_bound
    (((hX.1 t).mono (𝓔.le t)).aestronglyMeasurable) (K + |m|) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hXb t ω)
  -- the localized drift
  have hθAp : IsStronglyProgressive 𝓔 θA := isStronglyProgressive_indicator hθp hA0'
  have hθAb : ∀ t ω, |θA t ω| ≤ max C 0 := abs_indicator_le_max hθb A
  have hθAreg : IsRiemannRegular P θA := isRiemannRegular_indicator hθreg A
  have hdriftA : ∀ t ω, drift θA t ω = A.indicator (drift θ t) ω := fun t ω => by
    by_cases hω : ω ∈ A
    · simp only [drift, hθAdef, indicator_of_mem hω]
    · simp only [drift, hθAdef, indicator_of_notMem hω, intervalIntegral.integral_zero]
  have hquadA : ∀ t ω, quadInt θA t ω = A.indicator (quadInt θ t) ω := fun t ω => by
    by_cases hω : ω ∈ A
    · simp only [quadInt, hθAdef, indicator_of_mem hω]
    · simp only [quadInt, hθAdef, indicator_of_notMem hω, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, intervalIntegral.integral_zero]
  -- the cross bracket
  have hBc : ∀ ω ∈ G, Continuous (B · ω) := fun ω hω => (hG ω hω).2.1
  have hXS : ∀ t ω, srcMeanW κ ρL ρR r W VL VR c S A t ω =
      srcMeanW κ ρL ρR r W VL VR c S A (min t (S ω)) ω := fun t ω => by
    simp only [srcMeanW, srcMeanInt, min_eq_left (min_le_right t (S ω))]
  have h3 := martingale_mul_noise_sub_stopped hBn hnull hGm hGc hBc hS hmean.1 (fun t ω => hmeanb t ω) hXS
  have hN := (WholeField.martingale_noiseOn hBn hnull hGm hGc).1
  have hcN := martingale_mul_of_zero hN hcAm hcAb
  have hY := (hcross.add h3).sub hcN
  have hXB : Martingale (fun t ω => X t ω * B t ω - drift θA t ω) 𝓔 P := by
    refine WholeField.martingale_of_ae_eq_of_null hY (fun t => ?_) (fun t => ?_) hnull
    · exact ((((hX.1 t).mono (𝓔.le t)).measurable.mul (hE.1.measurable' t)).sub
        ((stronglyMeasurable_integral_comp hθAp measurable_id t).mono (𝓔.le t)).measurable)
    · filter_upwards [hGae] with ω hω
      have hN1 : ∀ u, WholeField.noiseOn B G u ω = B u ω := fun u => by simp [WholeField.noiseOn, hω]
      simp only [Pi.add_apply, Pi.sub_apply, hN1, hdriftA]
      by_cases hωA : ω ∈ A
      · have hg := hG ω hω
        have hx := hadm ω
        have hle : ((min t (S ω) : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
          rw [← hg.2.2.2]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
        have hint := integral_vSrc_mul_im_sub_eq_of_isGoodPath (κ := κ) (ρL := ρL) (ρR := ρR) hg.1.1 hg.1.2.1
          hx.1 hx.2 hg.1.2.2 hle
        rw [srcCrossW_eq hadm hG hAG hωA t, indicator_of_mem hωA,
          hg.drift_srcThetaW_eq hθp hθb hx (hpat ω hω) (hSζ ω) t, ← vSrcW_of_adm κ ρL ρR r hx] at *
        simp only [hXdef, hcAdef, indicator_of_mem hωA]
        rw [show (fun s : ℝ => W s.toNNReal ω) = Ito.rpath (fun t => W t ω) from rfl, ← hint]
        ring
      · have h0 : srcCrossW κ ρL ρR r W VL VR B c S A t ω = 0 := by
          simp [srcCrossW, srcCrossInt, hωA]
        have h1 : srcMeanW κ ρL ρR r W VL VR c S A t ω = 0 := by
          simp [srcMeanW, srcMeanInt, hωA]
        simp only [h0, h1, hXdef, hcAdef, indicator_of_notMem hωA]
        ring
  -- the variance identity
  have hX2 : ∀ t, ∫ ω, X t ω ^ 2 ∂P = ∫ ω, quadInt θA t ω ∂P := fun t => by
    simp only [hXA, hquadA]
    exact integral_srcMeanW_sub_sq_eq hcf hhm hc hadm hGc hG hpat hS𝓖 hSζ hθp hθb hA0 hAG hAm hAn hAc t
      ((hmean.1 t).mono (𝓔.le t)).measurable
  -- conclusion
  have hBpre := isFilteredPreBrownian_of_isFilteredBrownianReal hBn
  have hbr := stochIntegral_ae_eq_of_brackets hBpre hθAp hθAb hθAreg hX hXL2 hXB hX2 t
  have hloc := stochIntegral_indicator_ae_eq hBpre hθp.stronglyAdapted hθb hθreg hA0' t
  filter_upwards [hbr, hloc] with ω h1 h2 hωA
  rw [indicator_of_mem hωA] at h2
  rw [← h2, h1]
  simp only [hXdef, hcAdef, indicator_of_mem hωA]

/-- **The Doléans density of `θ` past the horizon is the density martingale at the stop**, almost surely on every
initial event where the source data are bounded. -/
theorem doleansDensity_srcThetaW_ae_eq_on [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r)
    (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 (fun ω => (c ω).1) (fun ω => (c ω).2) W VL VR B ζ)
    (hBn : IsFilteredBrownianReal (nullAugmented 𝓕 P) B P) (h𝓖 : 𝓖 ≤ 𝓕)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (hhm : Measurable h)
    (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsWordGood κ ρL ρR r W VL VR B c ζ S ω)
    (hpat : ∀ ω ∈ G, seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR')
    (hS𝓖 : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0)) (hSζ : ∀ ω, (S ω : ℝ≥0∞) ≤ ζ ω)
    (hA0 : MeasurableSet[𝓖 0] A) (hAG : A ⊆ G) {m : ℝ}
    (hAm : ∀ ω ∈ A, ∀ z, |vSrcW κ ρL ρR r (c ω) z| ≤ m) (hAn : ∀ ω ∈ A, |normW κ ρL ρR r (c ω)| ≤ m)
    (hAc : ∀ ω ∈ A, |centreW κ ρL ρR r (c ω)| ≤ m) :
    ∀ᵐ ω ∂P, ω ∈ A → doleansDensity P (nullAugmented 𝓕 P) B (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR)
      (stopHorizon r + 1) ω = martW κ ρL ρR r W VL VR c (S ω) ω := by
  set 𝓔 := nullAugmented 𝓕 P with h𝓔
  have hle𝓖 : ∀ t, 𝓖 t ≤ 𝓔 t := fun t => (h𝓖 t).trans (le_nullAugmented 𝓕 P t)
  have hS : IsStoppingTime 𝓔 fun ω => (S ω : WithTop ℝ≥0) := fun t => hle𝓖 t _ (hS𝓖 t)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun s => VL i s ω) {s | (s : ℝ≥0∞) < ζ ω}) ∧
      ∀ j, ContinuousOn (fun s => VR j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hGae] with ω hω
    have hp := (hG ω hω).1.1
    exact ⟨hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  obtain ⟨hθp, hθb, -⟩ := srcThetaW_props (P := P) (𝓔 := 𝓔) (ρL' := ρL') (ρR' := ρR') (κ := κ)
    (adaptedBefore_mono (le_nullAugmented 𝓕 P) hE.2.2.2.1)
    (fun i => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hE.2.2.2.2.1 i))
    (fun j => adaptedBefore_mono (le_nullAugmented 𝓕 P) (hE.2.2.2.2.2.1 j)) (fun s => hS s) hSζ hcont hr0
  filter_upwards [stochIntegral_srcThetaW_ae_eq hκ hr0 hE hBn h𝓖 hcf hhm hc hadm hG0 hGc hG hpat hS𝓖 hSζ hA0
    hAG hAm hAn hAc (stopHorizon r + 1)] with ω h1 hωA
  have hg := hG ω (hAG hωA)
  have hx := hadm ω
  have hmin : min (stopHorizon r + 1) (S ω) = S ω :=
    min_eq_right (hg.le_horizon.trans (le_add_of_nonneg_right zero_le_one))
  rw [doleansDensity, h1 hωA, hg.quadInt_srcThetaW_eq hθp hθb hx (hpat ω (hAG hωA)) (hSζ ω), hmin,
    srcMeanW_eq_srcMeanAt hadm hωA, hmin, martW, srcMart, centreW_of_adm κ ρL ρR r hx]

end Bracket

/-! ### Bounded-source events and the Doléans density on the whole good event -/

section Cover

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ)

/-- The words whose source data are bounded by `n` (the source tested on a set `D`). -/
def srcBoundSet (D : Set ℂ) (n : ℕ) : Set ((Fin nL → ℝ) × (Fin nR → ℝ)) :=
  {x | (∀ z ∈ D, |vDensW κ ρL ρR r x z| ≤ n) ∧ |normW κ ρL ρR r x| ≤ n ∧ |centreW κ ρL ρR r x| ≤ n}

variable {κ ρL ρR r}

theorem measurableSet_srcBoundSet {D : Set ℂ} (hD : D.Countable) (n : ℕ) :
    MeasurableSet (srcBoundSet κ ρL ρR r D n) := by
  have e : srcBoundSet κ ρL ρR r D n = (⋂ z ∈ D, {x | |vDensW κ ρL ρR r x z| ≤ n}) ∩
      ({x | |normW κ ρL ρR r x| ≤ n} ∩ {x | |centreW κ ρL ρR r x| ≤ n}) := by
    ext x; simp [srcBoundSet]
  rw [e]
  refine (MeasurableSet.biInter hD fun z _ => measurableSet_le
    (continuous_abs.measurable.comp (measurable_vDensW_apply κ ρL ρR r z)) measurable_const).inter
    ((measurableSet_le (continuous_abs.measurable.comp (measurable_normW κ ρL ρR r)) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp (measurable_centreW κ ρL ρR r)) measurable_const))

theorem abs_vSrcW_le_of_mem {D : Set ℂ} (hD : Dense D) {n : ℕ} {x : (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hx : x ∈ srcBoundSet κ ρL ρR r D n) (z : ℂ) : |vSrcW κ ρL ρR r x z| ≤ n := by
  have hcl : IsClosed {z : ℂ | |vDensW κ ρL ρR r x z| ≤ n} :=
    isClosed_le (continuous_abs.comp (continuous_vDensW κ ρL ρR r x)) continuous_const
  have hall : ∀ z, |vDensW κ ρL ρR r x z| ≤ n := fun z => by
    have hsub : D ⊆ {z : ℂ | |vDensW κ ρL ρR r x z| ≤ n} := fun z hz => hx.1 z hz
    have := hcl.closure_subset_iff.2 hsub (hD.closure_eq ▸ mem_univ z)
    exact this
  by_cases hz : z ∈ H
  · simp only [vSrcW, indicator_of_mem hz]; exact hall z
  · simp only [vSrcW, indicator_of_notMem hz, abs_zero]; exact Nat.cast_nonneg n

theorem exists_mem_srcBoundSet (D : Set ℂ) {x : (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsAdmWord r x) :
    ∃ n : ℕ, x ∈ srcBoundSet κ ρL ρR r D n := by
  have hc : Continuous (vDensW κ ρL ρR r x) := continuous_vDensW κ ρL ρR r x
  have hs : HasCompactSupport (vDensW κ ρL ρR r x) := by
    rw [vDensW_eq_of_adm κ ρL ρR r hx]; exact hasCompactSupport_vDens hx.2.1
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨n, hn⟩ := exists_nat_ge (max C (max |normW κ ρL ρR r x| |centreW κ ρL ρR r x|))
  refine ⟨n, fun z _ => ?_, ?_, ?_⟩
  · exact ((Real.norm_eq_abs _).symm.le.trans (hC z)).trans ((le_max_left _ _).trans hn)
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans hn

end Cover

section DoleansCover

variable {κ : ℝ} {nL nR : ℕ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 𝓖 : Filtration ℝ≥0 mΩ}
  {c : Ω → (Fin nL → ℝ) × (Fin nR → ℝ)}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {S : Ω → ℝ≥0} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The Doléans density of the Girsanov drift is the density martingale at the stop** (Aux. lemma 55 for a random
word), almost surely. -/
theorem doleansDensity_srcThetaW_ae_eq [IsProbabilityMeasure P] (hκ : 0 < κ) (hr0 : 0 < r)
    (hE : IsIntegratedSLEEvolutionFrom κ ρL ρR P 𝓕 (fun ω => (c ω).1) (fun ω => (c ω).2) W VL VR B ζ)
    (hBn : IsFilteredBrownianReal (nullAugmented 𝓕 P) B P) (h𝓖 : 𝓖 ≤ 𝓕)
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) (hhm : Measurable h)
    (hc : Measurable[𝓖 0] c) (hadm : ∀ ω, IsAdmWord r (c ω))
    (hG𝓖 : MeasurableSet[𝓖 0] G) (hGc : P Gᶜ = 0)
    (hG : ∀ ω ∈ G, IsWordGood κ ρL ρR r W VL VR B c ζ S ω)
    (hpat : ∀ ω ∈ G, seedWtL (c ω).1 ρL = ρL' ∧ seedWtR (c ω).2 ρR = ρR')
    (hS𝓖 : IsStoppingTime 𝓖 fun ω => (S ω : WithTop ℝ≥0)) (hSζ : ∀ ω, (S ω : ℝ≥0∞) ≤ ζ ω) :
    ∀ᵐ ω ∂P, doleansDensity P (nullAugmented 𝓕 P) B (srcThetaW κ r ρL ρL' ρR ρR' S ζ W VL VR)
      (stopHorizon r + 1) ω = martW κ ρL ρR r W VL VR c (S ω) ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G := (h𝓖 0).trans (le_nullAugmented 𝓕 P 0) _ hG𝓖
  set A : ℕ → Set Ω := fun n => G ∩ c ⁻¹' srcBoundSet κ ρL ρR r D n with hAdef
  have hA0 : ∀ n, MeasurableSet[𝓖 0] (A n) := fun n => hG𝓖.inter (hc (measurableSet_srcBoundSet hDc n))
  have hn := fun n => doleansDensity_srcThetaW_ae_eq_on hκ hr0 hE hBn h𝓖 hcf hhm hc hadm hG0 hGc hG hpat hS𝓖 hSζ
    (hA0 n) inter_subset_left (m := n) (fun ω hω z => abs_vSrcW_le_of_mem hDd hω.2 z) (fun ω hω => hω.2.2.1)
    (fun ω hω => hω.2.2.2) (ρL' := ρL') (ρR' := ρR')
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  filter_upwards [ae_all_iff.2 hn, hGae] with ω h1 hω
  obtain ⟨n, hn'⟩ := exists_mem_srcBoundSet (κ := κ) (ρL := ρL) (ρR := ρR) D (hadm ω)
  exact h1 n ⟨hω, hn'⟩

end DoleansCover

end LocalExt

end InteractingSLE
