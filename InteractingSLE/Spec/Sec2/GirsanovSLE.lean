/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovCut
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# Adding and removing separated force points by Girsanov's theorem

Packet PROVE-SEC2-GIR. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`):

* L486: "one can obtain existence of a process with the properties above, defined up until the first time that
  one of the *other* force points collides with `W_t`, using a Girsanov transformation … applied to the standard
  one-force-point `SLE_κ(ρ)` … Girsanov's theorem applies because the remaining force points introduce a smooth
  drift to the Brownian motion, and the new process obtained is absolutely continuous with respect to the
  one-force-point process (as long as one stops at a bounded stopping time that occurs before `W_t` gets within
  some fixed constant distance of one of the other force points)";
* L488: "One can also reverse this procedure (starting with a process defined for multiple force points and
  applying Girsanov's theorem to produce the process corresponding to one force point)";
* the explicit density of Aux. lemma 4 (L694–L698): `Z = exp(κ^{-1/2} ∫ D dB - (2κ)⁻¹ ∫ D²)`, under which
  `B̃ = B - κ^{-1/2} ∫ D ds` is a Brownian motion and the driving equation acquires the drift `D`.

The added drift `D_t = ∑_j σ_j / (W_t - U_j(t))` of separated marks `U_j` is replaced by the bounded continuous
`∑_j σ_j r_δ(W_t - U_j(t))` (`r_δ x = x / max (x²) (δ²)`, equal to `1/x` for `|x| ≥ δ`, the source's `r_δ`
of Aux. lemma 4) and cut at a stopping time `τ ≤ ζ ∧ T` before which every gap is at least `δ`
(`GirsanovCut`). Main results:

* `girsanov_shift_drift`: the general change of drift, with sign `ε`;
* `girsanov_add_forcePoints` (existence direction): from an evolution and separated added marks, under the
  changed measure the driving equation holds with the full force word up to `τ`;
* `girsanov_remove_forcePoints` (reverse direction): from an evolution, removing the separated marks
  `SL`, `SR` gives the driving equation of the remaining force word up to `τ`.

In both, the changed measure `Q = Z · P` is a probability measure equivalent to `P`
(`MathFin.IsEquivProbMeasure`), `Z = doleansDensity …` is the explicit Doléans density, the density process is a
martingale (`martingale_doleansDensity`), and `B̃` is a Brownian motion of the same filtration under `Q`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Girsanov

/-! ### The cut reciprocal -/

/-- The cut reciprocal `r_δ x = x / max (x²) (δ²)`: continuous, bounded by `δ⁻¹`, and `1/x` for `|x| ≥ δ`. -/
def recipCut (δ x : ℝ) : ℝ := x / max (x ^ 2) (δ ^ 2)

theorem recipCut_of_le {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ |x|) : recipCut δ x = x⁻¹ := by
  have hx2 : δ ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ hδ.le hx 2
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx
    linarith
  rw [recipCut, max_eq_left hx2]
  field_simp

theorem continuous_recipCut {δ : ℝ} (hδ : 0 < δ) : Continuous (recipCut δ) := by
  refine continuous_id.div ((continuous_pow 2).max continuous_const) fun x => ?_
  exact (lt_max_of_lt_right (pow_pos hδ 2)).ne'

theorem abs_recipCut_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |recipCut δ x| ≤ δ⁻¹ := by
  have hpos : 0 < max (x ^ 2) (δ ^ 2) := lt_max_of_lt_right (pow_pos hδ 2)
  rw [recipCut, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  rcases le_total δ |x| with h | h
  · have hx2 : δ ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ hδ.le h 2
    rw [max_eq_left hx2, ← sq_abs x]
    have : |x| ≤ |x| ^ 2 * δ⁻¹ := by
      rw [sq, mul_assoc]
      have : 1 ≤ |x| * δ⁻¹ := by rw [← div_eq_mul_inv, le_div_iff₀ hδ]; linarith
      nlinarith [abs_nonneg x]
    linarith
  · calc |x| ≤ δ := h
      _ = δ ^ 2 * δ⁻¹ := by field_simp
      _ ≤ max (x ^ 2) (δ ^ 2) * δ⁻¹ := by
        gcongr
        exact le_max_right _ _
      _ = δ⁻¹ * max (x ^ 2) (δ ^ 2) := mul_comm _ _

/-- The cut added drift `∑_j σ_j r_δ(w - u_j)`. -/
def addedDriftCut {m : ℕ} (σ : Fin m → ℝ) (δ w : ℝ) (u : Fin m → ℝ) : ℝ :=
  ∑ j, σ j * recipCut δ (w - u j)

theorem continuous_addedDriftCut {m : ℕ} (σ : Fin m → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous fun p : ℝ × (Fin m → ℝ) => addedDriftCut σ δ p.1 p.2 :=
  continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_recipCut hδ).comp
    (continuous_fst.sub ((continuous_apply j).comp continuous_snd)))

theorem abs_addedDriftCut_le {m : ℕ} (σ : Fin m → ℝ) {δ : ℝ} (hδ : 0 < δ) (w : ℝ) (u : Fin m → ℝ) :
    |addedDriftCut σ δ w u| ≤ (∑ j, |σ j|) * δ⁻¹ := by
  rw [addedDriftCut, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_recipCut_le hδ _) (abs_nonneg _)

/-! ### The general change of drift -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {m : ℕ}
  {τ ζ : Ω → ℝ≥0∞} {W B : ℝ≥0 → Ω → ℝ} {U : Fin m → ℝ≥0 → Ω → ℝ}

/-- A bounded continuous function of the coordinates is interval integrable on `[0, t]`, `t ≤ τ ≤ ζ`, on the
continuity event (it agrees a.e. with a progressive cut drift). -/
theorem intervalIntegrable_comp_of_le {G : ℝ → (Fin m → ℝ) → ℝ}
    (hG : Continuous fun p : ℝ × (Fin m → ℝ) => G p.1 p.2) {M : ℝ} (hGb : ∀ w u, |G w u| ≤ M)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) {ω : Ω} (hτζ : τ ω ≤ ζ ω)
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ τ ω) :
    IntervalIntegrable (fun s : ℝ => G (W s.toNNReal ω) (fun j => U j s.toNNReal ω)) volume 0 t := by
  have hθ := isStronglyProgressive_cutDrift (τ := τ) hG hW hU hτ
  have hint := intervalIntegrable_time hθ (abs_cutDrift_le (τ := τ) (ζ := ζ) (W := W) (U := U) hGb)
    ω 0 t
  rw [intervalIntegrable_iff] at hint ⊢
  refine hint.congr_fun_ae ?_
  rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
  rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
  have h1 : (s.toNNReal : ℝ≥0∞) < τ ω := by
    refine lt_of_lt_of_le ?_ ht
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
    exact lt_of_le_of_ne hs.2 hst
  exact cutDrift_eq_of_lt hG hτζ hWc hUc h1

/-- The integrand of the cut drift of sign `ε`: `-(ε / √κ) ∑_j σ_j r_δ(w - u_j)`. -/
def shiftIntegrand (κ ε δ : ℝ) (σ : Fin m → ℝ) (w : ℝ) (u : Fin m → ℝ) : ℝ :=
  -(ε / Real.sqrt κ) * addedDriftCut σ δ w u

/-- The progressive drift that adds `ε ∑_j σ_j / (W - U_j)` to the driving equation up to `τ`. -/
def shiftDrift (κ ε δ : ℝ) (σ : Fin m → ℝ) (τ ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  cutDrift τ ζ (shiftIntegrand κ ε δ σ) W U

/-- **The change of drift by Girsanov's theorem.** Let `B` be a Brownian motion of `𝓕`, `W` and the marks `U_j`
adapted before `ζ` and continuous on `[0, ζ)` almost surely, and `τ ≤ ζ ∧ T` a stopping time before which every
gap `|W - U_j|` with `σ_j ≠ 0` is at least `δ > 0`. With `θ = shiftDrift κ ε δ σ τ ζ W U` and
`Q = Z_{T+1} · P` (`Z` the Doléans density of `θ`):

* `Q` is a probability measure equivalent to `P`;
* `B̃ = B + ∫₀^· θ` is a Brownian motion of `𝓕` under `Q`;
* almost surely, for every `t ≤ τ`, each `σ_j / (W - U_j)` is integrable on `[0, t]` and
  `√κ B̃_t = √κ B_t - ε ∑_j ∫₀ᵗ σ_j / (W_s - U_j(s)) ds`. -/
theorem girsanov_shift_drift [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) (ε : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (σ : Fin m → ℝ) (hBF : IsFilteredBrownianReal 𝓕 B P)
    (hW : AdaptedBefore 𝓕 ζ W) (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, σ j ≠ 0 → δ ≤ |W t ω - U j t ω|) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B (shiftDrift κ ε δ σ τ ζ W U) (T + 1)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (shiftDrift κ ε δ σ τ ζ W U))
      (girsanovMeasure P 𝓕 B (shiftDrift κ ε δ σ τ ζ W U) (T + 1)) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      (∀ j, IntervalIntegrable (fun s : ℝ => σ j / (W s.toNNReal ω - U j s.toNNReal ω)) volume 0 t) ∧
      Real.sqrt κ * girsanovProcess B (shiftDrift κ ε δ σ τ ζ W U) t ω
        = Real.sqrt κ * B t ω
          - ε * ∑ j, ∫ s in (0 : ℝ)..(t : ℝ), σ j / (W s.toNNReal ω - U j s.toNNReal ω) := by
  have hF : Continuous fun p : ℝ × (Fin m → ℝ) => shiftIntegrand κ ε δ σ p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ hδ)
  have hFb : ∀ w u, |shiftIntegrand κ ε δ σ w u| ≤ |ε / Real.sqrt κ| * ((∑ j, |σ j|) * δ⁻¹) :=
    fun w u => by
      rw [shiftIntegrand, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le σ hδ w u) (abs_nonneg _)
  obtain ⟨h1, h2, h3⟩ := girsanov_cutDrift (P := P) hBF hF hFb hW hU hτ hτζ hτT hcont
  refine ⟨h1, h2, ?_⟩
  filter_upwards [h3, hcont, hgap] with ω h3ω ⟨hWc, hUc⟩ hgω t ht
  -- each cut term is integrable and equals the uncut term a.e. on `[0, t]`
  have hterm : ∀ j, IntervalIntegrable
      (fun s : ℝ => σ j * recipCut δ (W s.toNNReal ω - U j s.toNNReal ω)) volume 0 t := fun j =>
    intervalIntegrable_comp_of_le (G := fun w u => σ j * recipCut δ (w - u j))
      (M := |σ j| * δ⁻¹)
      (continuous_const.mul ((continuous_recipCut hδ).comp
        (continuous_fst.sub ((continuous_apply j).comp continuous_snd))))
      (fun w u => by
        show |σ j * recipCut δ (w - u j)| ≤ |σ j| * δ⁻¹
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_recipCut_le hδ _) (abs_nonneg _))
      hW hU hτ (hτζ ω) hWc hUc ht
  have hae : ∀ j, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 (t : ℝ) →
      σ j * recipCut δ (W s.toNNReal ω - U j s.toNNReal ω)
        = σ j / (W s.toNNReal ω - U j s.toNNReal ω) := fun j => by
    filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
    rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
    have hlt : (s.toNNReal : ℝ≥0∞) < τ ω := by
      refine lt_of_lt_of_le ?_ ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
      exact lt_of_le_of_ne hs.2 hst
    by_cases hσ : σ j = 0
    · simp [hσ]
    · rw [recipCut_of_le hδ (hgω _ hlt j hσ), div_eq_mul_inv]
  have hint : ∀ j, IntervalIntegrable (fun s : ℝ => σ j / (W s.toNNReal ω - U j s.toNNReal ω))
      volume 0 t := fun j => by
    have := hterm j
    rw [intervalIntegrable_iff] at this ⊢
    refine this.congr_fun_ae ?_
    rw [EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hae j
  refine ⟨hint, ?_⟩
  rw [show shiftDrift κ ε δ σ τ ζ W U = cutDrift τ ζ (shiftIntegrand κ ε δ σ) W U from rfl,
    h3ω t ht]
  have hsum : ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ ε δ σ (W s.toNNReal ω)
      (fun j => U j s.toNNReal ω)
      = -(ε / Real.sqrt κ) * ∑ j, ∫ s in (0 : ℝ)..(t : ℝ), σ j / (W s.toNNReal ω - U j s.toNNReal ω) := by
    simp only [shiftIntegrand, addedDriftCut]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      fun j _ => hterm j]
    congr 1
    refine Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr_ae (hae j)
  rw [hsum]
  have hk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  field_simp
  ring

/-! ### Adding separated force points (existence direction, L486) -/

/-- **Adding separated force points by Girsanov** (specification, proof of Theorem 2.2, L486 and the many-point
extension of the two-seed case, L548). Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution (Definition 2.1) for
the force word `(xL; xR)`, `(ρL; ρR)` with lifetime `ζ`, and let `U_j` be further marks with weights `σ_j`,
adapted before `ζ` and continuous on `[0, ζ)` almost surely. Let `τ ≤ ζ ∧ T` be a stopping time before which
`|W - U_j| ≥ δ > 0` for every `j` ("a bounded stopping time that occurs before `W_t` gets within some fixed
constant distance of one of the other force points"). Then under `Q = Z · P`, `Z` the Doléans density of the
added drift `κ^{-1/2} ∑_j σ_j / (W - U_j)` (cut at `τ`):

* `Q` is a probability measure equivalent to `P` ("absolutely continuous with respect to the one-force-point
  process");
* `B̃ = B - κ^{-1/2} ∫₀^{·∧τ} ∑_j σ_j / (W - U_j)` is a Brownian motion of `𝓕` under `Q`;
* `Q`-almost surely, for every `t ≤ τ` before the lifetime, the added reciprocal gaps are integrable on
  `[0, t]` and the driving equation of the full force word holds with `B̃`:
  `W_t = √κ B̃_t + ∑_i ∫₀ᵗ ρL_i/(W - VL_i) + ∑_i ∫₀ᵗ ρR_i/(W - VR_i) + ∑_j ∫₀ᵗ σ_j/(W - U_j)`.

The force-point equations of `V` (and those of `U`, if they hold) are pathwise and hold `Q`-almost surely as
well, since `Q ≪ P`. -/
theorem girsanov_add_forcePoints [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (σ : Fin m → ℝ)
    (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j))
    (hUc : ∀ᵐ ω ∂P, ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, δ ≤ |W t ω - U j t ω|) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B (shiftDrift κ 1 δ σ τ ζ W U) (T + 1)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (shiftDrift κ 1 δ σ τ ζ W U))
      (girsanovMeasure P 𝓕 B (shiftDrift κ 1 δ σ τ ζ W U) (T + 1)) ∧
    ∀ᵐ ω ∂(girsanovMeasure P 𝓕 B (shiftDrift κ 1 δ σ τ ζ W U) (T + 1)),
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω → (t : ℝ≥0∞) < ζ ω →
        (∀ j, IntervalIntegrable (fun s : ℝ => σ j / (W s.toNNReal ω - U j s.toNNReal ω))
          volume 0 t) ∧
        W t ω = Real.sqrt κ * girsanovProcess B (shiftDrift κ 1 δ σ τ ζ W U) t ω
          + (∑ i, ∫ s in (0 : ℝ)..(t : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
          + (∑ i, ∫ s in (0 : ℝ)..(t : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω))
          + (∑ j, ∫ s in (0 : ℝ)..(t : ℝ), σ j / (W s.toNNReal ω - U j s.toNNReal ω)) := by
  obtain ⟨hBF, hW, -, -, hpath⟩ := hE
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath, hUc] with ω hp hu
    exact ⟨hp.2.2.2.1, hu⟩
  obtain ⟨h1, h2, h3⟩ := girsanov_shift_drift (P := P) hκ 1 hδ σ hBF hW hU hτ hτζ hτT hcont
    (hgap.mono fun ω h t ht j _ => h t ht j)
  refine ⟨h1, h2, h1.ac.ae_le ?_⟩
  filter_upwards [h3, hpath] with ω h3ω hp t ht htζ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -⟩ := hp
  obtain ⟨hint, hB⟩ := h3ω t ht
  refine ⟨hint, ?_⟩
  have hw := hweq t htζ
  beta_reduce at hw
  linarith

/-! ### Removing separated force points (reverse direction, L488) -/

/-- The marks of a force word as one family indexed by `Fin (nL + nR)` (left marks first). -/
def allMarks {nL nR : ℕ} (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) :
    Fin (nL + nR) → ℝ≥0 → Ω → ℝ :=
  Fin.addCases (motive := fun _ => ℝ≥0 → Ω → ℝ) VL VR

/-- The weights of the removed marks `SL`, `SR` (other weights set to `0`), indexed like `allMarks`. -/
def removedWeights {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (SL : Finset (Fin nL))
    (SR : Finset (Fin nR)) : Fin (nL + nR) → ℝ :=
  Fin.addCases (motive := fun _ => ℝ) (fun i => if i ∈ SL then ρL i else 0)
    (fun i => if i ∈ SR then ρR i else 0)

/-- **Reverse Girsanov: removing separated force points** (specification, proof of Theorem 2.2, L488: "starting
with a process defined for multiple force points and applying Girsanov's theorem to produce the process
corresponding to one force point"). Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution with lifetime `ζ`, and
let `SL`, `SR` be sets of left and right marks to remove. Let `τ ≤ ζ ∧ T` be a stopping time before which `W`
stays at distance `≥ δ > 0` from the removed marks. Then under `Q = Z · P`, `Z` the Doléans density of minus the
removed drift (cut at `τ`): `Q` is a probability measure equivalent to `P`, `B̂ = B + κ^{-1/2} ∫₀^{·∧τ} D` is a
Brownian motion of `𝓕` under `Q` (`D` the removed drift), and `Q`-almost surely, for every `t ≤ τ` before the
lifetime, the driving equation of the remaining force word holds with `B̂`:
`W_t = √κ B̂_t + ∑_{i ∉ SL} ∫₀ᵗ ρL_i/(W - VL_i) + ∑_{i ∉ SR} ∫₀ᵗ ρR_i/(W - VR_i)`. -/
theorem girsanov_remove_forcePoints [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (SL : Finset (Fin nL))
    (SR : Finset (Fin nR)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i ∈ SL, δ ≤ |W t ω - VL i t ω|) ∧ ∀ i ∈ SR, δ ≤ |W t ω - VR i t ω|) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B
      (shiftDrift κ (-1) δ (removedWeights ρL ρR SL SR) τ ζ W (allMarks VL VR)) (T + 1)) ∧
    IsFilteredBrownianReal 𝓕
      (girsanovProcess B (shiftDrift κ (-1) δ (removedWeights ρL ρR SL SR) τ ζ W (allMarks VL VR)))
      (girsanovMeasure P 𝓕 B
        (shiftDrift κ (-1) δ (removedWeights ρL ρR SL SR) τ ζ W (allMarks VL VR)) (T + 1)) ∧
    ∀ᵐ ω ∂(girsanovMeasure P 𝓕 B
        (shiftDrift κ (-1) δ (removedWeights ρL ρR SL SR) τ ζ W (allMarks VL VR)) (T + 1)),
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω → (t : ℝ≥0∞) < ζ ω →
        W t ω = Real.sqrt κ * girsanovProcess B
            (shiftDrift κ (-1) δ (removedWeights ρL ρR SL SR) τ ζ W (allMarks VL VR)) t ω
          + (∑ i ∈ SLᶜ, ∫ s in (0 : ℝ)..(t : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
          + (∑ i ∈ SRᶜ, ∫ s in (0 : ℝ)..(t : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (allMarks VL VR k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hVL i
    | right i => simpa [allMarks] using hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [allMarks] using hp.2.2.2.2.2.1 i
  have hgap' : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ k,
      removedWeights ρL ρR SL SR k ≠ 0 → δ ≤ |W t ω - allMarks VL VR k t ω| := by
    filter_upwards [hgap] with ω hg t ht k hk
    cases k using Fin.addCases with
    | left i =>
      simp only [removedWeights, allMarks, Fin.addCases_left] at hk ⊢
      by_cases hi : i ∈ SL
      · exact (hg t ht).1 i hi
      · simp [hi] at hk
    | right i =>
      simp only [removedWeights, allMarks, Fin.addCases_right] at hk ⊢
      by_cases hi : i ∈ SR
      · exact (hg t ht).2 i hi
      · simp [hi] at hk
  obtain ⟨h1, h2, h3⟩ := girsanov_shift_drift (P := P) hκ (-1) hδ (removedWeights ρL ρR SL SR) hBF
    hW hU hτ hτζ hτT hcont hgap'
  refine ⟨h1, h2, h1.ac.ae_le ?_⟩
  filter_upwards [h3, hpath] with ω h3ω hp t ht htζ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -⟩ := hp
  obtain ⟨-, hB⟩ := h3ω t ht
  have hsplit : ∑ k, ∫ s in (0 : ℝ)..(t : ℝ), removedWeights ρL ρR SL SR k
        / (W s.toNNReal ω - allMarks VL VR k s.toNNReal ω)
      = (∑ i ∈ SL, ∫ s in (0 : ℝ)..(t : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
        + (∑ i ∈ SR, ∫ s in (0 : ℝ)..(t : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω)) := by
    rw [Fin.sum_univ_add]
    simp only [removedWeights, allMarks, Fin.addCases_left, Fin.addCases_right]
    congr 1
    · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ SL)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [add_eq_left.2]
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp only [hi, ↓reduceIte]
      · refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_filter] at hi
        simp [hi.2]
    · rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ SR)]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [add_eq_left.2]
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp only [hi, ↓reduceIte]
      · refine Finset.sum_eq_zero fun i hi => ?_
        rw [Finset.mem_filter] at hi
        simp [hi.2]
  rw [hsplit] at hB
  have hw := hweq t htζ
  beta_reduce at hw
  have hL := Finset.sum_add_sum_compl SL
    (fun i => ∫ s in (0 : ℝ)..(t : ℝ), ρL i / (W s.toNNReal ω - VL i s.toNNReal ω))
  have hR := Finset.sum_add_sum_compl SR
    (fun i => ∫ s in (0 : ℝ)..(t : ℝ), ρR i / (W s.toNNReal ω - VR i s.toNNReal ω))
  linarith

/-! ### The explicit form of the density -/

/-- **The explicit quadratic part of the density** (Aux. lemma 4, L694: `Z = exp(κ^{-1/2} ∫ D dB - (2κ)⁻¹ ∫ D²)`).
On the continuity event, for `t ≤ τ`, the quadratic integral of the shift drift is
`(ε² / κ) ∫₀ᵗ (∑_j σ_j / (W - U_j))²`; so the density `doleansDensity P 𝓕 B θ t` is
`exp(-∫₀ᵗ θ dB - (ε² / (2κ)) ∫₀ᵗ D²)`, `θ = -(ε/√κ) D` before `τ`. -/
theorem quadInt_shiftDrift_eq {κ : ℝ} (hκ : 0 < κ) (ε : ℝ) {δ : ℝ} (hδ : 0 < δ) (σ : Fin m → ℝ)
    {ω : Ω} (hτζ : τ ω ≤ ζ ω) (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω})
    (hgω : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, σ j ≠ 0 → δ ≤ |W t ω - U j t ω|) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ τ ω) :
    quadInt (shiftDrift κ ε δ σ τ ζ W U) t ω
      = ε ^ 2 / κ * ∫ s in (0 : ℝ)..(t : ℝ),
          (∑ j, σ j / (W s.toNNReal ω - U j s.toNNReal ω)) ^ 2 := by
  have hF : Continuous fun p : ℝ × (Fin m → ℝ) => shiftIntegrand κ ε δ σ p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut σ hδ)
  rw [quadInt, show shiftDrift κ ε δ σ τ ζ W U = cutDrift τ ζ (shiftIntegrand κ ε δ σ) W U from rfl,
    integral_comp_cutDrift_eq hF (fun x => x ^ 2) hτζ hWc hUc ht,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
  rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hs
  have hlt : (s.toNNReal : ℝ≥0∞) < τ ω := by
    refine lt_of_lt_of_le ?_ ht
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
    exact lt_of_le_of_ne hs.2 hst
  have hterm : ∀ j, σ j * recipCut δ (W s.toNNReal ω - U j s.toNNReal ω)
      = σ j / (W s.toNNReal ω - U j s.toNNReal ω) := fun j => by
    by_cases hσ : σ j = 0
    · simp [hσ]
    · rw [recipCut_of_le hδ (hgω _ hlt j hσ), div_eq_mul_inv]
  simp only [shiftIntegrand, addedDriftCut, hterm]
  rw [mul_pow, neg_sq, div_pow, Real.sq_sqrt hκ.le]

end Girsanov

end InteractingSLE
