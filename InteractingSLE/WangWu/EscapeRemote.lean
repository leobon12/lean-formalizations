/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksInverse
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Wang–Wu at `κ = 4`, Lemma 6.5: a uniform change of a remote weight

Packet PROVE-WW-C. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §6, Lemma 6.5 (p. 41):
"Let `Q` be the one-force law with weight `α` at `−L`, with `R` tracked at weight zero; let `P` give the same
tracked right point weight `β`. Stop by time `t₀` and before `|W|` exceeds `r < R`. For any event `E` measurable
at this stopped observation, `P(E) ≥ e^{−H} Q(E)²`, `H = β² t₀/(4(R − r)²)`."

The proof in the source has three steps, all formalized here except the last identification:

* the remote gap: the tracked right point is nondecreasing, so `V_R − W ≥ R − r` before `|W|` exceeds `r`, and
  the remote Girsanov integrand `β/(2(W − V_R))` is bounded by `|β|/(2(R − r))` (`abs_remote_le`); its squared
  integral up to `t₀` is at most `H` (`quadInt_le_of_abs_le`, `remoteEnergy`);
* the exponential `Z = exp(−∫θ dB − ½∫θ²)` changing `P` to `Q` has second moment at most `e^H`: `Z² = Z(2θ) e^{∫θ²}`
  (`sq_doleansDensity_ae_eq`, using the linearity `stochIntegral_const_mul_ae_eq` of the Itô integral) and
  `E Z(2θ) = 1` (`integral_doleansDensity`), so `E Z² ≤ e^H` (`integral_sq_doleansDensity_le`);
* Cauchy–Schwarz: `Q(E) = E_P[Z 1_E] ≤ (E_P Z²)^{1/2} P(E)^{1/2}` (`withDensity_sq_le`), whence
  **`exp_neg_mul_sq_le_measure`**: `e^{−H} Q(E)² ≤ P(E)` with `Q = girsanovMeasure P 𝓕 B θ T`.

The remaining step, "Lemma 2.6 identifies the changed SDE law" (that under `Q` the force-point process is the
one with the remote weight removed), is Lemma 2.6 of packet PROVE-WW-A (Girsanov for the force-point SDE) and
is not repeated here. The bound holds for every event `E` (not only stopped ones) once `Q` is defined as the
Girsanov measure of the stopped integrand.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

namespace Remote

/-! ### Cauchy–Schwarz for a density -/

section CauchySchwarz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Cauchy–Schwarz for a density**: `(∫⁻_E f dP)² ≤ (∫⁻ f² dP) · P(E)`. -/
theorem withDensity_sq_le {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {E : Set Ω} (hE : MeasurableSet E) :
    (P.withDensity f E) ^ 2 ≤ (∫⁻ ω, f ω ^ 2 ∂P) * P E := by
  rw [withDensity_apply _ hE, ← lintegral_indicator hE]
  have hind : (E.indicator f) = f * E.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω; by_cases h : ω ∈ E <;> simp [h]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hf
    ((aemeasurable_const (b := (1 : ℝ≥0∞))).indicator hE)
  rw [← hind] at hHolder
  have h1 : ∫⁻ ω, (E.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ (2 : ℝ) ∂P = P E := by
    have : (fun ω => (E.indicator (fun _ => (1 : ℝ≥0∞)) ω) ^ (2 : ℝ)) =
        E.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω; by_cases h : ω ∈ E <;> simp [h]
    rw [this, lintegral_indicator hE, setLIntegral_const, one_mul]
  have h2 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂P = ∫⁻ ω, f ω ^ 2 ∂P := by
    congr 1; funext ω; exact ENNReal.rpow_two (f ω)
  rw [h1, h2] at hHolder
  calc (∫⁻ ω, E.indicator f ω ∂P) ^ 2
      ≤ ((∫⁻ ω, f ω ^ 2 ∂P) ^ (1 / 2 : ℝ) * P E ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ ω, f ω ^ 2 ∂P) * P E := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (P E ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

end CauchySchwarz

/-! ### Linearity of the Itô integral in a constant factor -/

section Linear

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

open Girsanov

theorem riemannSum_const_mul (c : ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    riemannSum B (fun s ω => c * θ s ω) n t ω = c * riemannSum B θ n t ω := by
  unfold riemannSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Itô integral is homogeneous: `∫ (c θ) dB = c ∫ θ dB` almost surely. -/
theorem stochIntegral_const_mul_ae_eq [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C)
    (hθreg : IsRiemannRegular P θ) (c : ℝ) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun s ω => c * θ s ω) t =ᵐ[P] fun ω => c * stochIntegral P 𝓕 B θ t ω := by
  have hm' : StronglyAdapted 𝓕 (fun s ω => c * θ s ω) := fun s => (hθm s).const_mul c
  have hb' : ∀ s ω, |c * θ s ω| ≤ |c| * C := fun s ω => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hθb s ω) (abs_nonneg c)
  have hreg' : IsRiemannRegular P (fun s ω => c * θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.const_mul c
  refine tendstoInMeasure_ae_unique (tendstoInMeasure_riemannSum hB hm' hb' hreg' t) ?_
  have h := tendstoInMeasure_riemannSum hB hθm hθb hθreg t
  have hfun : (fun n => riemannSum B (fun s ω => c * θ s ω) n t) =
      fun n ω => c * riemannSum B θ n t ω := by
    funext n ω; exact riemannSum_const_mul c n t ω
  rw [hfun]
  have hc : TendstoInMeasure P (fun n ω => c * riemannSum B θ n t ω) atTop
      (fun ω => c * stochIntegral P 𝓕 B θ t ω) := by
    intro ε hε
    rcases eq_or_ne c 0 with h0 | h0
    · have e0 : ∀ n, {ω | ε ≤ edist (c * riemannSum B θ n t ω) (c * stochIntegral P 𝓕 B θ t ω)} = ∅ :=
        fun n => by
          ext ω
          simp only [h0, zero_mul, edist_self, mem_ofPred_eq, nonpos_iff_eq_zero, mem_empty_iff_false,
            iff_false]
          exact ne_of_gt hε
      simp only [e0, measure_empty]
      exact tendsto_const_nhds
    · have hcpos : (0 : ℝ≥0∞) < ‖c‖ₑ := by simpa using h0
      have hε' : 0 < ε / ‖c‖ₑ := ENNReal.div_pos (ne_of_gt hε) enorm_ne_top
      have e : ∀ n, {ω | ε ≤ edist (c * riemannSum B θ n t ω) (c * stochIntegral P 𝓕 B θ t ω)}
          = {ω | ε / ‖c‖ₑ ≤ edist (riemannSum B θ n t ω) (stochIntegral P 𝓕 B θ t ω)} := fun n => by
        ext ω
        simp only [mem_ofPred_eq]
        rw [edist_eq_enorm_sub, ← mul_sub, enorm_mul, ← edist_eq_enorm_sub,
          ENNReal.div_le_iff (ne_of_gt hcpos) enorm_ne_top, mul_comm]
      simp only [e]
      exact h _ hε'
  exact hc

end Linear

/-! ### The second moment of the Doléans density -/

section SecondMoment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}

open Girsanov

theorem quadInt_const_mul (c : ℝ) : quadInt (fun s ω => c * θ s ω) = fun t ω => c ^ 2 * quadInt θ t ω := by
  funext t ω
  simp only [quadInt, mul_pow, intervalIntegral.integral_const_mul]

/-- `Z_T(θ)² = Z_T(2θ) · exp(∫₀ᵀ θ²)` almost surely. -/
theorem sq_doleansDensity_ae_eq (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) :
    (fun ω => doleansDensity P 𝓕 B θ T ω ^ 2) =ᵐ[P]
      fun ω => doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) T ω * Real.exp (quadInt θ T ω) := by
  filter_upwards [stochIntegral_const_mul_ae_eq hB hθm hθb hθreg 2 T] with ω hω
  simp only [doleansDensity, quadInt_const_mul, hω, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- **The second moment of the Doléans density**: if `∫₀ᵀ θ² ≤ H` almost surely, then `E Z_T² ≤ e^H`. -/
theorem integral_sq_doleansDensity_le (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0} {H : ℝ}
    (hH : ∀ᵐ ω ∂P, quadInt θ T ω ≤ H) :
    ∫ ω, doleansDensity P 𝓕 B θ T ω ^ 2 ∂P ≤ Real.exp H := by
  have hm2 : StronglyAdapted 𝓕 (fun s ω => 2 * θ s ω) := fun s => (hθm s).const_mul 2
  have hb2 : ∀ s ω, |2 * θ s ω| ≤ 2 * C := fun s ω => by
    rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (hθb s ω) (by norm_num)
  have hreg2 : IsRiemannRegular P (fun s ω => 2 * θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.const_mul 2
  have hint2 : Integrable (doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) T) P :=
    (memLp_doleansDensity (B := B) hm2 hb2 hreg2 T).integrable one_le_two
  have hone := integral_doleansDensity (B := B) hm2 hb2 hreg2 T
  rw [integral_congr_ae (sq_doleansDensity_ae_eq hB hθm hθb hθreg T)]
  calc ∫ ω, doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) T ω * Real.exp (quadInt θ T ω) ∂P
      ≤ ∫ ω, doleansDensity P 𝓕 B (fun s ω => 2 * θ s ω) T ω * Real.exp H ∂P := by
        refine integral_mono_of_nonneg ?_ (hint2.mul_const _) ?_
        · exact ae_of_all _ fun ω => mul_nonneg (doleansDensity_pos T ω).le (Real.exp_pos _).le
        · filter_upwards [hH] with ω hω
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hω) (doleansDensity_pos T ω).le
    _ = Real.exp H := by rw [integral_mul_const, hone, one_mul]

/-- **Lemma 6.5 (the change-of-measure inequality (E3))**: if the Girsanov integrand `θ` satisfies
`∫₀ᵀ θ² ≤ H` almost surely, then for every measurable event `E`,
`e^{−H} Q(E)² ≤ P(E)` with `Q = Z_T · P` the Girsanov measure. -/
theorem exp_neg_mul_sq_le_measure (hB : IsFilteredPreBrownian B 𝓕 P) (hθm : StronglyAdapted 𝓕 θ)
    {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {T : ℝ≥0} {H : ℝ}
    (hH : ∀ᵐ ω ∂P, quadInt θ T ω ≤ H) {E : Set Ω} (hE : MeasurableSet E) :
    ENNReal.ofReal (Real.exp (-H)) * (girsanovMeasure P 𝓕 B θ T E) ^ 2 ≤ P E := by
  have hZm : AEMeasurable (fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)) P :=
    ((memLp_doleansDensity (B := B) hθm hθb hθreg T).aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have hCS := withDensity_sq_le hZm hE
  have hmem := memLp_doleansDensity (B := B) hθm hθb hθreg T
  have hsq_int : Integrable (fun ω => doleansDensity P 𝓕 B θ T ω ^ 2) P := hmem.integrable_sq
  have hlint : ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω) ^ 2 ∂P ≤
      ENNReal.ofReal (Real.exp H) := by
    have e : (fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω) ^ 2) =
        fun ω => ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω ^ 2) := by
      funext ω; rw [ENNReal.ofReal_pow (doleansDensity_pos T ω).le]
    rw [e, ← ofReal_integral_eq_lintegral_ofReal hsq_int
      (ae_of_all _ fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (integral_sq_doleansDensity_le hB hθm hθb hθreg hH)
  have hQ : girsanovMeasure P 𝓕 B θ T E ^ 2 ≤ ENNReal.ofReal (Real.exp H) * P E :=
    hCS.trans (mul_le_mul_left hlint _)
  calc ENNReal.ofReal (Real.exp (-H)) * girsanovMeasure P 𝓕 B θ T E ^ 2
      ≤ ENNReal.ofReal (Real.exp (-H)) * (ENNReal.ofReal (Real.exp H) * P E) := by gcongr
    _ = P E := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, ENNReal.ofReal_one, one_mul]

end SecondMoment

/-! ### The remote integrand and its energy -/

/-- The energy constant `H = β² t₀/(4(R − r)²)` of (E3). -/
def remoteEnergy (β t₀ R r : ℝ) : ℝ := β ^ 2 * t₀ / (4 * (R - r) ^ 2)

/-- **The remote gap.** If the tracked right point `v ≥ R` and the driver `w ≤ r < R`, the remote Girsanov
integrand `β/(2(w − v))` is bounded by `|β|/(2(R − r))`. -/
theorem abs_remote_le {β R r v w : ℝ} (hrR : r < R) (hv : R ≤ v) (hw : w ≤ r) :
    |β / (2 * (w - v))| ≤ |β| / (2 * (R - r)) := by
  have hpos : 0 < 2 * (R - r) := by linarith
  have hgap : 2 * (R - r) ≤ |2 * (w - v)| := by
    rw [abs_of_neg (by linarith : 2 * (w - v) < 0)]; linarith
  rw [abs_div]
  exact div_le_div_of_nonneg_left (abs_nonneg β) hpos hgap

/-- The squared integral of an integrand bounded by `M` and vanishing after `t₀ ≥ 0` is at most `M² t₀`
(if the square is not integrable, the Bochner integral is `0`). -/
theorem quadInt_le_of_abs_le {Ω : Type*} {θ : ℝ≥0 → Ω → ℝ} {M t₀ : ℝ} (ht₀ : 0 ≤ t₀) {ω : Ω}
    (hθb : ∀ s, |θ s ω| ≤ M) (hθ0 : ∀ s : ℝ≥0, t₀ < s → θ s ω = 0) (T : ℝ≥0) :
    Girsanov.quadInt θ T ω ≤ M ^ 2 * t₀ := by
  unfold Girsanov.quadInt
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hθb 0)
  have hsq : ∀ u : ℝ, θ u.toNNReal ω ^ 2 ≤ M ^ 2 := fun u => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hθb _) 2
  by_cases hint : IntervalIntegrable (fun u : ℝ => θ u.toNNReal ω ^ 2) volume 0 T
  · set m := min (T : ℝ) t₀ with hm
    have hm0 : 0 ≤ m := le_min (NNReal.coe_nonneg T) ht₀
    have hmT : m ≤ T := min_le_left _ _
    have hsub1 : uIcc 0 m ⊆ uIcc 0 (T : ℝ) := by
      rw [uIcc_of_le hm0, uIcc_of_le (NNReal.coe_nonneg T)]; exact Icc_subset_Icc le_rfl hmT
    have hsub2 : uIcc m (T : ℝ) ⊆ uIcc 0 (T : ℝ) := by
      rw [uIcc_of_le hmT, uIcc_of_le (NNReal.coe_nonneg T)]; exact Icc_subset_Icc hm0 le_rfl
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint.mono_set hsub1)
      (hint.mono_set hsub2)]
    have h1 : ∫ u in (0 : ℝ)..m, θ u.toNNReal ω ^ 2 ≤ ∫ _ in (0 : ℝ)..m, M ^ 2 :=
      intervalIntegral.integral_mono_on hm0 (hint.mono_set hsub1) intervalIntegrable_const
        fun u _ => hsq u
    have h2 : ∫ u in m..(T : ℝ), θ u.toNNReal ω ^ 2 ≤ ∫ _ in m..(T : ℝ), (0 : ℝ) := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hmT (hint.mono_set hsub2)
        intervalIntegrable_const fun u hu => ?_
      have hut : t₀ < u := by
        rcases le_total (T : ℝ) t₀ with h | h
        · exact absurd (hu.2) (by rw [hm, min_eq_left h] at hu; linarith [hu.1])
        · rw [hm, min_eq_right h] at hu; exact hu.1
      have : t₀ < (u.toNNReal : ℝ) := by rw [Real.coe_toNNReal u (ht₀.trans hut.le)]; exact hut
      rw [hθ0 _ this]; norm_num
    simp only [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_zero,
      sub_zero] at h1 h2
    have : m * M ^ 2 ≤ M ^ 2 * t₀ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg M)
    linarith
  · rw [intervalIntegral.integral_undef hint]
    positivity

/-- The remote integrand `θ_s = β/(2(W_s − V_s))`, stopped at `t₀` (zero afterwards), has squared integral at most
`H = β² t₀/(4(R − r)²)` along a path on which `V_s ≥ R` and `W_s ≤ r < R` for `s ≤ t₀`. -/
theorem quadInt_remote_le {Ω : Type*} {β R r t₀ : ℝ} (hrR : r < R) (ht₀ : 0 ≤ t₀)
    {θ : ℝ≥0 → Ω → ℝ} {W V : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hθ : ∀ s : ℝ≥0, (s : ℝ) ≤ t₀ → θ s ω = β / (2 * (W s ω - V s ω)))
    (hθ0 : ∀ s : ℝ≥0, t₀ < s → θ s ω = 0)
    (hV : ∀ s : ℝ≥0, (s : ℝ) ≤ t₀ → R ≤ V s ω) (hW : ∀ s : ℝ≥0, (s : ℝ) ≤ t₀ → W s ω ≤ r) (T : ℝ≥0) :
    Girsanov.quadInt θ T ω ≤ remoteEnergy β t₀ R r := by
  have hb : ∀ s, |θ s ω| ≤ |β| / (2 * (R - r)) := by
    intro s
    by_cases hs : (s : ℝ) ≤ t₀
    · rw [hθ s hs]; exact abs_remote_le hrR (hV s hs) (hW s hs)
    · push Not at hs; rw [hθ0 s hs, abs_zero]; exact div_nonneg (abs_nonneg _) (by linarith)
  refine (quadInt_le_of_abs_le ht₀ hb hθ0 T).trans (le_of_eq ?_)
  unfold remoteEnergy
  have : R - r ≠ 0 := by linarith
  rw [div_pow, sq_abs]
  field_simp
  ring

end Remote

end WangWu

end InteractingSLE
