import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.LGF.Invariance
import HigherDimLQGMetric.Sphere.Var
import GaussianLQG.Probability.Gaussian

/-!
# Gaussian union estimates for sharp shell bounds

A Chernoff bound with a tunable moment parameter, valid also at zero variance.
This is the probability input for the upper halves of [1] Propositions 4.7 and 4.10.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

universe u

open MeasureTheory ProbabilityTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal NNReal

/-- A tunable two-sided Gaussian Chernoff bound, including zero variance. -/
theorem w2_gaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P)
    (h0 : ∫ ω, X ω ∂P = 0) {V T s : ℝ} (hV : Var[X; P] ≤ V)
    (hs : 0 ≤ s) :
    P {ω | T < |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-s * T + s ^ 2 * V / 2)) := by
  let v : ℝ≥0 := (Var[X; P]).toNNReal
  have hLaw : HasLaw X (gaussianReal 0 v) P :=
    GaussianLQG.hasLaw_of_hasGaussianLaw hX h0
  have hv : (v : ℝ) = Var[X; P] :=
    Real.coe_toNNReal _ (variance_nonneg X P)
  have hpos : P.real {ω | T ≤ X ω} ≤ Real.exp (-s * T + s ^ 2 * V / 2) := by
    have h := measure_ge_le_exp_mul_mgf (X := X) (μ := P) (t := s) T hs
      (GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hLaw s)
    rw [mgf_gaussianReal hLaw, zero_mul, zero_add, ← Real.exp_add] at h
    exact h.trans (Real.exp_le_exp.mpr (by rw [hv]; nlinarith only [hV, sq_nonneg s]))
  have hneg : P.real {ω | X ω ≤ -T} ≤ Real.exp (-s * T + s ^ 2 * V / 2) := by
    have h := measure_le_le_exp_mul_mgf (X := X) (μ := P) (t := -s) (-T)
      (neg_nonpos.mpr hs)
      (GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hLaw (-s))
    rw [mgf_gaussianReal hLaw, zero_mul, zero_add, ← Real.exp_add] at h
    exact h.trans (Real.exp_le_exp.mpr (by rw [hv]; nlinarith only [hV, sq_nonneg s]))
  have hsub : {ω | T < |X ω|} ⊆ {ω | T ≤ X ω} ∪ {ω | X ω ≤ -T} := by
    intro ω hω
    change T < |X ω| at hω
    rcases le_abs'.1 hω.le with h | h
    · exact Or.inr (by simpa only [mem_ofPred_eq] using h)
    · exact Or.inl h
  have hreal : P.real {ω | T < |X ω|} ≤
      2 * Real.exp (-s * T + s ^ 2 * V / 2) := by
    calc
      P.real {ω | T < |X ω|} ≤
          P.real ({ω | T ≤ X ω} ∪ {ω | X ω ≤ -T}) := measureReal_mono hsub
      _ ≤ P.real {ω | T ≤ X ω} + P.real {ω | X ω ≤ -T} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-s * T + s ^ 2 * V / 2) := by linarith only [hpos, hneg]
  calc
    P {ω | T < |X ω|} = ENNReal.ofReal (P.real {ω | T < |X ω|}) :=
      (ofReal_measureReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-s * T + s ^ 2 * V / 2)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Union bound over a finite family of centred Gaussian variables with a common variance bound. -/
theorem w2_gaussian_finset_union {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι : Type*} (F : Finset ι) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ F, HasGaussianLaw (X i) P)
    (h0 : ∀ i ∈ F, ∫ ω, X i ω ∂P = 0)
    {V T s : ℝ} (hV : ∀ i ∈ F, Var[X i; P] ≤ V) (hs : 0 ≤ s) :
    P {ω | ∃ i ∈ F, T < |X i ω|} ≤
      ENNReal.ofReal ((F.card : ℝ) * (2 * Real.exp (-s * T + s ^ 2 * V / 2))) := by
  classical
  let E : ι → Set Ω := fun i => {ω | T < |X i ω|}
  have hsub : {ω | ∃ i ∈ F, T < |X i ω|} ⊆ ⋃ i ∈ F, E i := by
    rintro ω ⟨i, hi, hω⟩
    exact Set.mem_biUnion hi hω
  have hterm : ∀ i ∈ F, P (E i) ≤
      ENNReal.ofReal (2 * Real.exp (-s * T + s ^ 2 * V / 2)) := by
    intro i hi
    exact w2_gaussian_abs_tail (hX i hi) (h0 i hi) (hV i hi) hs
  calc
    P {ω | ∃ i ∈ F, T < |X i ω|} ≤ P (⋃ i ∈ F, E i) := measure_mono hsub
    _ ≤ ∑ i ∈ F, P (E i) := measure_biUnion_finset_le _ _
    _ ≤ (F.card : ℝ≥0∞) * ENNReal.ofReal
        (2 * Real.exp (-s * T + s ^ 2 * V / 2)) := by
          simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul F (fun i => P (E i)) _ hterm
    _ = ENNReal.ofReal ((F.card : ℝ) * (2 * Real.exp (-s * T + s ^ 2 * V / 2))) := by
      rw [ENNReal.ofReal_mul (p := (F.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]

/-- The variance estimate used in [1] Lemma 4.9. -/
theorem w2_variance_grid_le {d : ℕ} (_hd : 2 ≤ d) {K : ℝ}
    (hK : ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r ρ : ℝ}, 0 < r → 0 < ρ → ∀ z w : Rd d,
        (r ≤ ρ → Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] ≤
          Real.log (ρ / r) + 2 * max 0 (Real.log (‖z - w‖ / ρ)) + K) ∧
        (ρ ≤ r → Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] ≤
          Real.log (r / ρ) + 2 * max 0 (Real.log (‖z - w‖ / r)) + K))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    (hh : IsWholeSpaceLGF h P) {𝕣 ε r : ℝ} (h𝕣 : 0 < 𝕣) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hr : 0 < r) (hr𝕣 : r ≤ 𝕣) (hrlo : ε ^ 2 * 𝕣 ≤ r) (w : Rd d)
    (hw : ‖w‖ ≤ 𝕣 / ε) :
    Var[fun ω => sphereAvg (h ω) r w - sphereAvg (h ω) 𝕣 0; P] ≤
      4 * Real.log ε⁻¹ + K := by
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have hL : 0 < Real.log ε⁻¹ := Real.log_pos (one_lt_inv_iff₀.mpr ⟨hε0, hε1⟩)
  have hratio : 𝕣 / r ≤ (ε ^ 2)⁻¹ := by
    apply (div_le_iff₀ hr).2
    have he : 𝕣 ≤ r / (ε ^ 2) :=
      (le_div_iff₀ (sq_pos_of_pos hε0)).2 (by nlinarith only [hrlo])
    simpa only [div_eq_mul_inv, mul_comm] using he
  have hlogr : Real.log (𝕣 / r) ≤ 2 * Real.log ε⁻¹ := by
    have h := Real.log_le_log (div_pos h𝕣 hr) hratio
    rw [Real.log_inv, Real.log_pow] at h
    rw [Real.log_inv]
    linarith only [h]
  have hnorm : ‖w‖ / 𝕣 ≤ ε⁻¹ := by
    apply (div_le_iff₀ h𝕣).2
    simpa only [div_eq_mul_inv, mul_comm] using hw
  have hlogw : max 0 (Real.log (‖w‖ / 𝕣)) ≤ Real.log ε⁻¹ := by
    by_cases hw0 : ‖w‖ = 0
    · simp only [hw0, zero_div, Real.log_zero, max_self]
      exact hL.le
    · have hwpos : 0 < ‖w‖ / 𝕣 := div_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)) h𝕣
      have hh := Real.log_le_log hwpos hnorm
      exact max_le hL.le hh
  have hv := (hK hh hr h𝕣 w 0).1 hr𝕣
  simp only [sub_zero] at hv
  linarith only [hv, hlogr, hlogw]

/-- [1] Lemma 4.9 at a single grid point and dyadic radius. -/
theorem w2_gaussian_grid_point {d : ℕ} (hd : 2 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P)
    {𝕣 ε r M K : ℝ} (h𝕣 : 0 < 𝕣) (hε : ε ∈ Ioo (0 : ℝ) 1)
    (hM : 0 ≤ M) (hr : 0 < r) (w : Rd d)
    (hvar : Var[fun ω => sphereAvg (h ω) r w - sphereAvg (h ω) 𝕣 0; P] ≤
      4 * Real.log ε⁻¹ + K) :
    P {ω | Real.sqrt M * Real.log ε⁻¹ <
      |sphereAvg (h ω) r w - sphereAvg (h ω) 𝕣 0|} ≤
      ENNReal.ofReal (2 * Real.exp (M * K / 32) * ε ^ (M / 8)) := by
  let X : Ω → ℝ := fun ω => sphereAvg (h ω) r w - sphereAvg (h ω) 𝕣 0
  obtain ⟨hX, hX0⟩ := hh.hasGaussianLaw_sphereAvg_sub hd hr h𝕣 w 0
  have hs : 0 ≤ Real.sqrt M / 4 := by positivity
  have htail := w2_gaussian_abs_tail hX hX0 hvar hs
    (T := Real.sqrt M * Real.log ε⁻¹)
  have hsq : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hM
  have he : -(Real.sqrt M / 4) * (Real.sqrt M * Real.log ε⁻¹) +
      (Real.sqrt M / 4) ^ 2 * (4 * Real.log ε⁻¹ + K) / 2 =
      M * K / 32 + -(M / 8) * Real.log ε⁻¹ := by
    calc
      _ = (Real.sqrt M) ^ 2 * K / 32 +
          -((Real.sqrt M) ^ 2 / 8) * Real.log ε⁻¹ := by ring_nf
      _ = _ := by rw [hsq]
  have hε0 : 0 < ε := hε.1
  have hpow : ε ^ (M / 8) = Real.exp (-(M / 8) * Real.log ε⁻¹) := by
    rw [Real.rpow_def_of_pos hε0, Real.log_inv]
    ring_nf
  simpa only [he, Real.exp_add, ← hpow, mul_assoc] using htail

/-- Finite-grid form of [1] Lemma 4.9. The constant depends only on the dimension;
`F` may be any finite family of centres and radii in the prescribed range. -/
theorem w2_lemma49_finite {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ {𝕣 ε M : ℝ}, 0 < 𝕣 → ε ∈ Ioo (0 : ℝ) 1 → 0 ≤ M →
      ∀ F : Finset (Rd d × ℝ),
      (∀ q ∈ F, 0 < q.2 ∧ ε ^ 2 * 𝕣 ≤ q.2 ∧ q.2 ≤ ε * 𝕣 ∧ ‖q.1‖ ≤ 𝕣 / ε) →
      P {ω | ∃ q ∈ F, Real.sqrt M * Real.log ε⁻¹ <
        |sphereAvg (h ω) q.2 q.1 - sphereAvg (h ω) 𝕣 0|} ≤
        ENNReal.ofReal ((F.card : ℝ) *
          (2 * Real.exp (M * K / 32) * ε ^ (M / 8))) := by
  classical
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_sub_le hd
  refine ⟨K, ?_⟩
  intro Ω _ P _ h hh 𝕣 ε M h𝕣 hε hM F hF
  let E : Rd d × ℝ → Set Ω := fun q =>
    {ω | Real.sqrt M * Real.log ε⁻¹ <
      |sphereAvg (h ω) q.2 q.1 - sphereAvg (h ω) 𝕣 0|}
  have hsub : {ω | ∃ q ∈ F, Real.sqrt M * Real.log ε⁻¹ <
      |sphereAvg (h ω) q.2 q.1 - sphereAvg (h ω) 𝕣 0|} ⊆ ⋃ q ∈ F, E q := by
    rintro ω ⟨q, hq, hω⟩
    exact Set.mem_biUnion hq hω
  have hterm : ∀ q ∈ F, P (E q) ≤
      ENNReal.ofReal (2 * Real.exp (M * K / 32) * ε ^ (M / 8)) := by
    intro q hq
    obtain ⟨hr, hrlo, hrhi, hw⟩ := hF q hq
    have hr𝕣 : q.2 ≤ 𝕣 := by
      calc q.2 ≤ ε * 𝕣 := hrhi
        _ ≤ 𝕣 := by nlinarith only [hε.2, h𝕣.le]
    have hv := w2_variance_grid_le hd hK hh h𝕣 hε hr hr𝕣 hrlo q.1 hw
    exact w2_gaussian_grid_point hd hh h𝕣 hε hM hr q.1 hv
  calc
    P {ω | ∃ q ∈ F, Real.sqrt M * Real.log ε⁻¹ <
        |sphereAvg (h ω) q.2 q.1 - sphereAvg (h ω) 𝕣 0|} ≤
        P (⋃ q ∈ F, E q) := measure_mono hsub
    _ ≤ ∑ q ∈ F, P (E q) := measure_biUnion_finset_le _ _
    _ ≤ (F.card : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (M * K / 32) * ε ^ (M / 8)) := by
          simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul F (fun q => P (E q)) _ hterm
    _ = ENNReal.ofReal ((F.card : ℝ) *
          (2 * Real.exp (M * K / 32) * ε ^ (M / 8))) := by
      rw [ENNReal.ofReal_mul (p := (F.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]

/-- Polynomial-cardinality form of Lemma 4.9. The exponent `N` can be chosen to
cover the spatial grid and the dyadic scales (for example `N = 3d + 2`). -/
theorem w2_lemma49_card {d : ℕ} (hd : 2 ≤ d) :
    ∃ K : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ {𝕣 ε M N C : ℝ}, 0 < 𝕣 → ε ∈ Ioo (0 : ℝ) 1 → 0 ≤ M → 0 ≤ C →
      ∀ F : Finset (Rd d × ℝ),
      (∀ q ∈ F, 0 < q.2 ∧ ε ^ 2 * 𝕣 ≤ q.2 ∧ q.2 ≤ ε * 𝕣 ∧ ‖q.1‖ ≤ 𝕣 / ε) →
      ((F.card : ℝ) * ε ^ N ≤ C) →
      P {ω | ∃ q ∈ F, Real.sqrt M * Real.log ε⁻¹ <
        |sphereAvg (h ω) q.2 q.1 - sphereAvg (h ω) 𝕣 0|} ≤
        ENNReal.ofReal ((C * (2 * Real.exp (M * K / 32))) * ε ^ (M / 8 - N)) := by
  obtain ⟨K, hK⟩ := w2_lemma49_finite hd
  refine ⟨K, ?_⟩
  intro Ω _ P _ h hh 𝕣 ε M N C h𝕣 hε hM hC F hF hcard
  have hε0 : 0 < ε := hε.1
  have hpow : ε ^ N * ε ^ (M / 8 - N) = ε ^ (M / 8) := by
    rw [← Real.rpow_add hε0]
    congr 1
    ring
  have hreal : (F.card : ℝ) * (2 * Real.exp (M * K / 32) * ε ^ (M / 8)) ≤
      (C * (2 * Real.exp (M * K / 32))) * ε ^ (M / 8 - N) := by
    calc
      _ = ((F.card : ℝ) * ε ^ N) *
          (2 * Real.exp (M * K / 32) * ε ^ (M / 8 - N)) := by rw [← hpow]; ring
      _ ≤ C * (2 * Real.exp (M * K / 32) * ε ^ (M / 8 - N)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  exact (hK P h hh h𝕣 hε hM F hF).trans (ENNReal.ofReal_le_ofReal hreal)

/-- An admissible dyadic radius has index at most `⌊ε⁻²⌋`. -/
theorem w2_le_floor_of_dyadic {ε : ℝ} (hε : 0 < ε) {k : ℕ}
    (hk : ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹) : k ≤ ⌊(ε ^ 2)⁻¹⌋₊ := by
  refine Nat.le_floor ?_
  have h1 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self
  have h2 : (2 : ℝ) ^ k ≤ (ε ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) (by positivity)]
    exact hk
  linarith only [h1, h2]

/-- [1] Lemma 4.9 on W1's spatial grid. The dyadic-index count is bounded by
`2 ε⁻²`, so the final exponent is `M/8 - 3d - 2`. -/
theorem w2_lemma49_grid {d : ℕ} (hd : 3 ≤ d) :
    ∃ K : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ {𝕣 ε M : ℝ}, 0 < 𝕣 → ε ∈ Ioo (0 : ℝ) 1 → 0 ≤ M →
      P {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
        Metric.ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
        ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (h ω) (𝕣 / 2 ^ k) w - sphereAvg (h ω) 𝕣 0|} ≤
        ENNReal.ofReal ((4 * (25 * d : ℝ) ^ d * Real.exp (M * K / 32)) *
          ε ^ (M / 8 - (3 * d + 2))) := by
  classical
  obtain ⟨K, hK⟩ := w2_lemma49_card (by omega : 2 ≤ d)
  refine ⟨K, ?_⟩
  intro Ω _ P _ h hh 𝕣 ε M h𝕣 hε hM
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  let s : ℝ := ε ^ 2 * 𝕣 / (10 * d)
  let B : ℝ := 𝕣 / ε
  let N : ℕ := ⌈B / s⌉₊ + 1
  let J : ℕ := ⌊(ε ^ 2)⁻¹⌋₊ + 1
  let S : Finset (Rd d) := shellGridBox d N s
  let I0 : Finset (Rd d × ℕ) := S ×ˢ Finset.range J
  let good : Rd d × ℕ → Prop := fun q =>
    ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ q.2 ∧ 𝕣 / 2 ^ q.2 ≤ ε * 𝕣 ∧ ‖q.1‖ ≤ B
  let I : Finset (Rd d × ℕ) := I0.filter good
  let F : Finset (Rd d × ℝ) := I.image (fun q => (q.1, 𝕣 / 2 ^ q.2))
  have hs : 0 < s := by dsimp [s]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgrid : gridPts s ∩ Metric.ball (0 : Rd d) B ⊆ (S : Set (Rd d)) :=
    grid_ball_subset_shellGridBox hs hB
  have hF : ∀ q ∈ F, 0 < q.2 ∧ ε ^ 2 * 𝕣 ≤ q.2 ∧
      q.2 ≤ ε * 𝕣 ∧ ‖q.1‖ ≤ 𝕣 / ε := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨_, hlo, hhi, hw⟩ := Finset.mem_filter.mp hp
    exact ⟨by positivity, hlo, hhi, hw⟩
  have hcardS : (S.card : ℝ) * ε ^ (3 * d) ≤ (25 * d : ℝ) ^ d :=
    card_shellGridBox_scaled hd h𝕣 hε0 hε1
  have hJ : (J : ℝ) * ε ^ 2 ≤ 2 := by
    have hf : (⌊(ε ^ 2)⁻¹⌋₊ : ℝ) ≤ (ε ^ 2)⁻¹ := Nat.floor_le (by positivity)
    have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1.le
    have hcancel : (ε ^ 2)⁻¹ * ε ^ 2 = 1 := inv_mul_cancel₀ (sq_pos_of_pos hε0).ne'
    dsimp [J]
    push_cast
    nlinarith only [hf, hε2, hcancel, sq_nonneg ε]
  have hcardF : (F.card : ℝ) ≤ (S.card : ℝ) * J := by
    have hnat : F.card ≤ S.card * J := by
      calc
        F.card ≤ I.card := Finset.card_image_le
        _ ≤ I0.card := Finset.card_filter_le _ _
        _ = S.card * J := by simp only [I0, Finset.card_product, Finset.card_range]
    exact_mod_cast hnat
  have hcard : (F.card : ℝ) * ε ^ ((3 * d : ℕ) + 2 : ℝ) ≤
      2 * (25 * d : ℝ) ^ d := by
    have he : ε ^ ((3 * d : ℕ) + 2 : ℝ) = ε ^ (3 * d) * ε ^ 2 := by
      rw [Real.rpow_add hε0]
      simp only [Real.rpow_natCast]
      norm_num [Real.rpow_natCast]
    rw [he]
    calc
      (F.card : ℝ) * (ε ^ (3 * d) * ε ^ 2) ≤
          ((S.card : ℝ) * J) * (ε ^ (3 * d) * ε ^ 2) :=
        mul_le_mul_of_nonneg_right hcardF (by positivity)
      _ = ((S.card : ℝ) * ε ^ (3 * d)) * ((J : ℝ) * ε ^ 2) := by ring
      _ ≤ (25 * d : ℝ) ^ d * 2 :=
        mul_le_mul hcardS hJ (by positivity) (by positivity)
      _ = 2 * (25 * d : ℝ) ^ d := by ring
  have hsub : {ω | ∃ w ∈ gridPts s ∩ Metric.ball (0 : Rd d) B,
      ∃ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (h ω) (𝕣 / 2 ^ k) w - sphereAvg (h ω) 𝕣 0|} ⊆
      {ω | ∃ q ∈ F, Real.sqrt M * Real.log ε⁻¹ <
        |sphereAvg (h ω) q.2 q.1 - sphereAvg (h ω) 𝕣 0|} := by
    rintro ω ⟨w, hw, k, hlo, hhi, hbad⟩
    have hk : ε ^ 2 ≤ ((2 : ℝ) ^ k)⁻¹ := by
      have h' : ε ^ 2 * 𝕣 ≤ ((2 : ℝ) ^ k)⁻¹ * 𝕣 := by
        simpa only [div_eq_mul_inv, mul_comm] using hlo
      exact le_of_mul_le_mul_right h' h𝕣
    have hkJ : k < J := Nat.lt_succ_of_le (w2_le_floor_of_dyadic hε0 hk)
    have hp : (w, k) ∈ I := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hgrid hw, Finset.mem_range.mpr hkJ⟩,
        ⟨hlo, hhi, (by simpa only [Metric.mem_ball, dist_zero_right] using hw.2 : ‖w‖ < B).le⟩⟩
    exact ⟨(w, 𝕣 / 2 ^ k), Finset.mem_image.mpr ⟨(w, k), hp, rfl⟩, hbad⟩
  have htail := hK P h hh h𝕣 hε hM (C := 2 * (25 * d : ℝ) ^ d)
    (N := ((3 * d : ℕ) + 2 : ℝ)) (by positivity) F hF hcard
  have hreal : (2 * (25 * d : ℝ) ^ d * (2 * Real.exp (M * K / 32))) *
      ε ^ (M / 8 - ((3 * d : ℕ) + 2 : ℝ)) =
      (4 * (25 * d : ℝ) ^ d * Real.exp (M * K / 32)) *
        ε ^ (M / 8 - (3 * d + 2)) := by
    push_cast
    ring
  change P {ω | ∃ w ∈ gridPts s ∩ Metric.ball (0 : Rd d) B,
      ∃ k : ℕ, ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (h ω) (𝕣 / 2 ^ k) w - sphereAvg (h ω) 𝕣 0|} ≤ _
  exact (measure_mono hsub).trans (by simpa only [hreal] using htail)

/-- Lemma 4.9 after a deterministic translation of the LGF. -/
theorem w2_lemma49_grid_shifted {d : ℕ} (hd : 3 ≤ d) :
    ∃ K : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ {𝕣 ε M : ℝ}, 0 < 𝕣 → ε ∈ Ioo (0 : ℝ) 1 → 0 ≤ M → ∀ z : Rd d,
      P {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
        Metric.ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
        ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (h ω) (𝕣 / 2 ^ k) (z + w) - sphereAvg (h ω) 𝕣 z|} ≤
        ENNReal.ofReal ((4 * (25 * d : ℝ) ^ d * Real.exp (M * K / 32)) *
          ε ^ (M / 8 - (3 * d + 2))) := by
  obtain ⟨K, hK⟩ := w2_lemma49_grid hd
  refine ⟨K, ?_⟩
  intro Ω _ P _ h hh 𝕣 ε M h𝕣 hε hM z
  let g : Ω → DistRd d := fun ω => affineComp 1 z (h ω)
  have hg : IsWholeSpaceLGF g P := hh.affineComp one_pos z
  have hbound := hK P g hg h𝕣 hε hM
  have hevent : {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
        Metric.ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
        ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (h ω) (𝕣 / 2 ^ k) (z + w) - sphereAvg (h ω) 𝕣 z|} =
      {ω | ∃ w ∈ gridPts (ε ^ 2 * 𝕣 / (10 * d)) ∩
        Metric.ball (0 : Rd d) (𝕣 / ε), ∃ k : ℕ,
        ε ^ 2 * 𝕣 ≤ 𝕣 / 2 ^ k ∧ 𝕣 / 2 ^ k ≤ ε * 𝕣 ∧
        Real.sqrt M * Real.log ε⁻¹ <
          |sphereAvg (g ω) (𝕣 / 2 ^ k) w - sphereAvg (g ω) 𝕣 0|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, g, sphereAvg_affineComp_one, zero_add]
    simp_rw [add_comm z]
  rw [hevent]
  exact hbound

end HigherDimLQGMetric
