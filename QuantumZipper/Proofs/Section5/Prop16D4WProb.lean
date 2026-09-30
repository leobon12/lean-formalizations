import QuantumZipper.Proofs.Section5.Prop16D4WEst

/-!
# Proposition 1.6, D4⁺ʷ: the perturbed canonical pairing is close in probability

Decision D24 (`DECISIONS.md`), clause (2) of D4⁺ʷ, in abstract form. For random locally good
fields `x C ω` on `V C ω`, open `U C ω ⊆ V C ω ∩ ℍ`, random continuous perturbations `φ C ω`, with
local scales `a = scaleParamOn γ x U` and `a' = scaleParamOn γ (ofFun φ + x) U`:

* (scale ratio → 1) `Q{¬(0 < a ∧ 0 < a' ∧ |a' − a| ≤ κ a)} → 0` for every `κ > 0`;
* (`φ(a·) → 0` uniformly on bounded sets) `Q{∃ z ∈ U, ‖z‖ < ρa, |φ z| > ε} → 0`;
* (tightness of the canonical area of bounded half-balls)
  `∀ θ > 0, ∃ M, eventually Q{μ^U_x(ball 0 (ρa)) > M} ≤ θ`;

then for every continuous compactly supported `f` and `δ > 0`,
`Q{δ < |∫ f dμ_{canon(ofFun φ + x)} − ∫ f dμ_{canon x}|} → 0` (`tendsto_canonical_pairing_close`).
With `hdom` (the canonical domain of `x` eventually contains `hball R`),
`∫ f dμ_{canon x} = locArea γ R f (canon x)` and the same holds with `locArea`
(`tendsto_canonical_pairing_locArea_close`), which is clause (2) of `Prop16TVWeakStmt` with
`Z C = canonicalOn γ (x C) (U C)`.

This is the Slutsky step of the paper's argument (Sheffield, arXiv:1012.4797, proof of Prop. 1.6,
p. 25: the continuous part is "approximately constant" near the marked point); the event
bookkeeping is our own elementary argument (Billingsley, *Convergence of Probability Measures*,
2nd ed., Theorem 3.1, for the Slutsky pattern).
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-- Uniform continuity turns a small scale ratio into a small change of `f(z / ·)`. -/
theorem abs_f_div_sub_le {f : ℂ → ℝ} {R : ℝ} (hfR : ∀ w, f w ≠ 0 → ‖w‖ < R) {d η : ℝ}
    (hη : 0 < η) (hd : ∀ u v : ℂ, dist u v < d → dist (f u) (f v) < η) {a a' κ : ℝ}
    (ha : 0 < a) (ha' : 0 < a') (ha2 : a ≤ 2 * a') (ha'2 : a' ≤ 2 * a)
    (hκ : |a' - a| ≤ κ * a) (hκd : 4 * R * κ < d) (z : ℂ) :
    |f (z / (a' : ℂ)) - f (z / (a : ℂ))| ≤ η := by
  by_cases h : f (z / (a' : ℂ)) = 0 ∧ f (z / (a : ℂ)) = 0
  · rw [h.1, h.2, sub_zero, abs_zero]; exact hη.le
  have hdiv : ∀ c : ℝ, 0 < c → f (z / (c : ℂ)) ≠ 0 → ‖z‖ < c * R := fun c hc hz => by
    have h1 := hfR _ hz
    rwa [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, div_lt_iff₀ hc, mul_comm] at h1
  have hz : ‖z‖ < 2 * a * R ∧ 0 < R := by
    rcases not_and_or.1 h with h' | h'
    · have h1 := hdiv a' ha' h'
      have hR : 0 < R := by
        by_contra hR; nlinarith [not_lt.1 hR, norm_nonneg z]
      exact ⟨by nlinarith, hR⟩
    · have h1 := hdiv a ha h'
      have hR : 0 < R := by
        by_contra hR; nlinarith [not_lt.1 hR, norm_nonneg z]
      exact ⟨by nlinarith, hR⟩
  have hκ0 : 0 ≤ κ := by
    by_contra hk; nlinarith [not_le.1 hk, abs_nonneg (a' - a)]
  have hdist : dist (z / (a' : ℂ)) (z / (a : ℂ)) < d := by
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have ha0' : (a' : ℂ) ≠ 0 := by exact_mod_cast ha'.ne'
    have e : z / (a' : ℂ) - z / (a : ℂ) = (((a - a') / (a * a') : ℝ) : ℂ) * z := by
      push_cast; field_simp
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (mul_pos ha ha'), abs_sub_comm]
    have hmain : |a' - a| / (a * a') * ‖z‖ ≤ 4 * R * κ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos ha ha')]
      have := mul_le_mul hκ hz.1.le (norm_nonneg z) (by positivity)
      have h5 : κ * a * (2 * a * R) ≤ 4 * R * κ * (a * a') := by
        have h6 := mul_le_mul_of_nonneg_left ha2
          (show 0 ≤ 2 * a * R * κ by have := hz.2; positivity)
        nlinarith
      linarith
    linarith
  have := hd _ _ hdist
  rw [Real.dist_eq] at this
  exact this.le

/-- **The perturbed canonical pairing is close in probability** (clause (2) of D4⁺ʷ, before
identifying the unperturbed pairing with `locArea`). -/
theorem tendsto_canonical_pairing_close {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    {γ : ℝ} (hγ : 0 < γ) (x : ℝ → Ω → FieldSample) (φ : ℝ → Ω → ℂ → ℝ)
    (U V : ℝ → Ω → Set ℂ)
    (hloc : ∀ C, ∀ᵐ ω ∂Q, IsLocallyGoodOn γ (V C ω) (x C ω) ∧ IsOpen (U C ω) ∧ U C ω ⊆ H ∧
      U C ω ⊆ V C ω ∧ ContinuousOn (φ C ω) (V C ω))
    (hscale : ∀ κ > 0, Tendsto (fun C => Q {ω | ¬ (0 < scaleParamOn γ (x C ω) (U C ω) ∧
      0 < scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) ∧
      |scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω) - scaleParamOn γ (x C ω) (U C ω)| ≤
        κ * scaleParamOn γ (x C ω) (U C ω))}) atTop (𝓝 0))
    (hφ : ∀ ρ > 0, ∀ ε > 0, Tendsto (fun C => Q {ω | ¬ ∀ z ∈ U C ω,
      ‖z‖ < ρ * scaleParamOn γ (x C ω) (U C ω) → |φ C ω z| ≤ ε}) atTop (𝓝 0))
    (htight : ∀ ρ > 0, ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, Q {ω | ¬ qAreaMeasureOn γ (x C ω) (U C ω)
      (ball 0 (ρ * scaleParamOn γ (x C ω) (U C ω))) ≤ ENNReal.ofReal M} ≤ θ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun C => Q {ω | δ <
      |∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ (ofFun (φ C ω) + x C ω) (U C ω))
          (canonicalDomainOn γ (ofFun (φ C ω) + x C ω) (U C ω)) -
        ∫ z, f z ∂qAreaMeasureOn γ (canonicalOn γ (x C ω) (U C ω))
          (canonicalDomainOn γ (x C ω) (U C ω))|}) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  -- constants
  obtain ⟨B0, hB0⟩ := hf.bounded_above_of_compact_support hfc
  set B := max B0 0
  have hB : ∀ w, |f w| ≤ B := fun w => (Real.norm_eq_abs _ ▸ hB0 w).trans (le_max_left _ _)
  have hBn : 0 ≤ B := le_max_right _ _
  obtain ⟨r, hr⟩ := hfc.isBounded.subset_ball 0
  set R := max r 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfR : ∀ w, f w ≠ 0 → ‖w‖ < R := fun w hw => by
    have := hr (subset_tsupport f hw)
    rw [mem_ball, dist_zero_right] at this
    exact this.trans_le (le_max_left _ _)
  have hθ3 : 0 < θ / 3 := ENNReal.div_pos hθ.ne' (by norm_num)
  obtain ⟨M0, hM0⟩ := htight (2 * R) (by positivity) (θ / 3) hθ3
  set M := max M0 0
  have hMn : 0 ≤ M := le_max_right _ _
  set η := δ / (2 * (M + 1))
  have hη : 0 < η := by positivity
  set t := δ / (2 * (B + 1) * (M + 1))
  have ht : 0 < t := by positivity
  set ε := Real.log (1 + t) / γ
  have hε0 : 0 ≤ ε := div_nonneg (Real.log_nonneg (by linarith)) hγ.le
  have hε : 0 < ε := div_pos (Real.log_pos (by linarith)) hγ
  have hexp : Real.exp (γ * ε) - 1 = t := by
    rw [mul_div_cancel₀ _ hγ.ne', Real.exp_log (by linarith)]; ring
  have hK : ((Real.exp (γ * ε) - 1) * B + η) * M < δ := by
    rw [hexp]
    have h1 : t * B ≤ δ / (2 * (M + 1)) := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hδ.le, hBn, hMn]
    have h2 : (t * B + η) * M ≤ δ / (M + 1) * M := by
      apply mul_le_mul_of_nonneg_right _ hMn
      have : η = δ / (2 * (M + 1)) := rfl
      rw [this]
      have e2 : δ / (M + 1) = δ / (2 * (M + 1)) + δ / (2 * (M + 1)) := by field_simp; ring
      linarith
    have h3 : δ / (M + 1) * M < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    linarith
  obtain ⟨d, hd, hdf⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf) η hη
  set κ := min (1 / 2) (d / (8 * R))
  have hκ : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ2 : κ ≤ 1 / 2 := min_le_left _ _
  have hκd : 4 * R * κ < d := by
    have : κ ≤ d / (8 * R) := min_le_right _ _
    have h8 : 4 * R * (d / (8 * R)) = d / 2 := by field_simp; ring
    nlinarith
  have e1 := (ENNReal.tendsto_nhds_zero.1 (hscale κ hκ)) (θ / 3) hθ3
  have e2 := (ENNReal.tendsto_nhds_zero.1 (hφ (2 * R) (by positivity) ε hε)) (θ / 3) hθ3
  filter_upwards [e1, e2, hM0] with C h1 h2 h3
  -- the null set
  set N := {ω | ¬ (IsLocallyGoodOn γ (V C ω) (x C ω) ∧ IsOpen (U C ω) ∧ U C ω ⊆ H ∧
      U C ω ⊆ V C ω ∧ ContinuousOn (φ C ω) (V C ω))}
  have hN : Q N = 0 := ae_iff.1 (hloc C)
  refine (measure_mono (fun ω hω => ?_ : _ ⊆ ((_ ∪ _) ∪ _) ∪ N)).trans
    (((measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add h1 h2)) h3)) hN.le)).trans
      (le_of_eq ?_))
  · simp only [mem_ofPred_eq] at hω
    by_contra hc
    simp only [mem_union, mem_ofPred_eq, not_or, not_not, N] at hc
    obtain ⟨⟨⟨⟨ha, ha', hκa⟩, hφz⟩, hμ⟩, hx, hU, hUH, hUV, hφc⟩ := hc
    set a := scaleParamOn γ (x C ω) (U C ω)
    set a' := scaleParamOn γ (ofFun (φ C ω) + x C ω) (U C ω)
    have ha2 : a ≤ 2 * a' := by
      have := (abs_le.1 hκa).1; nlinarith
    have ha'2 : a' ≤ 2 * a := by
      have := (abs_le.1 hκa).2; nlinarith
    have hbd := abs_canonical_pairing_sub_le hγ hx hU hUH hUV hφc hf hB hfR ha ha' ha'2 hε0 hMn
      (fun z hz hzn => hφz z hz (by linarith)) (abs_f_div_sub_le hfR hη hdf ha ha' ha2 ha'2 hκa hκd)
      (M := M) (by
        refine le_trans (measure_mono (ball_subset_ball (le_of_eq (by ring)))) (hμ.trans ?_)
        exact ENNReal.ofReal_le_ofReal (le_max_left _ _))
    linarith
  · rw [add_zero, ENNReal.add_thirds]

end Prop16Asm

end QuantumZipper
