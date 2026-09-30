import QuantumZipper.Proofs.Thm18.G1ProfileConv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FIRSTMODE (1): the deterministic part `dPart` is bounded near compacts of `H`

For the first-mode node `G1RestFirstModeStmt` the raw value of the pulled-back canonical wedge
field at `fc(v, s)` is `L + dPart(v, s)` (`G1RC.raw_coordChange_rescale_wedge`), where
`dPart = ∫ (p ∘ Sψ) dfc + Q log S + Q ∫ log ‖ψ'‖ dfc` (`G1RC.dPart`). Continuity of `dPart` on
`Hbar × (0, ∞)` does not bound it as `s → 0`; here we bound it uniformly for `v` within `τ₀` of a
compact `K ⊆ H` and `s ∈ (0, τ₀]`, using the logarithmic bounds `LogBd` of both integrands
(`G1RC.logBd_profile`, `G1RC.logBd_log_norm_deriv`): the folded circle `fc(v, s)` is carried by
`B̄(v, s)`, which stays in a compact part of `H`.

Main result: `G1FM.dPart_bound`. Own elementary argument (bookkeeping of proved bounds).
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM

open G1RC F1.RC3Two CA.Koebe WedgeTK CircleFubini

theorem abs_log_le_of_between {a x b : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ |Real.log a| + |Real.log b| := by
  have h1 := Real.log_le_log ha hax
  have h2 := Real.log_le_log (ha.trans_le hax) hxb
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

/-- A `LogBd` integrand is bounded on the `2τ₀`-neighbourhood of a compact `K ⊆ H`. -/
theorem logBd_near_bound {G : ℂ → ℝ} {B : ℝ} (h : LogBd G B) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) : ∃ M τ₀ : ℝ, 0 ≤ M ∧ 0 < τ₀ ∧ (∀ w ∈ K, τ₀ < w.im) ∧
      ∀ w ∈ K, ∀ u : ℂ, dist u w ≤ 2 * τ₀ → |G u| ≤ M := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 1, le_rfl, one_pos, fun w hw => absurd hw (notMem_empty w),
      fun w hw => absurd hw (notMem_empty w)⟩
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm : 0 < z0.im := hKH hz0
  have hR0' : 0 ≤ R0 := by
    have := hR0 hz0
    rw [mem_closedBall, dist_zero_right] at this
    exact (norm_nonneg _).trans this
  obtain ⟨A, hA⟩ := h.2.2.2 (R0 + z0.im)
  have hB := h.2.2.1
  refine ⟨|A| + B * (|Real.log (z0.im / 2)| + |Real.log (R0 + z0.im)|), z0.im / 4,
    by positivity, by positivity, fun w hw => ?_, fun w hw u hu => ?_⟩
  · have : z0.im ≤ w.im := hmin hw
    linarith
  have hwim : z0.im ≤ w.im := hmin hw
  have hwn : ‖w‖ ≤ R0 := by
    have := hR0 hw
    rwa [mem_closedBall, dist_zero_right] at this
  have hdu : ‖u - w‖ ≤ z0.im / 2 := by rw [← dist_eq_norm]; linarith
  have him1 : |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
  have huim : z0.im / 2 ≤ u.im := by
    rw [Complex.sub_im] at him1
    linarith [neg_abs_le (u.im - w.im)]
  have hun : ‖u‖ ≤ R0 + z0.im := by
    have := norm_le_norm_add_norm_sub' u w
    linarith [norm_sub_rev u w]
  have huH : u ∈ H := show 0 < u.im by linarith
  have hlog := abs_log_le_of_between (by linarith) huim
    ((Complex.im_le_norm u).trans hun)
  have h1 := hA u huH hun
  have h2 := mul_le_mul_of_nonneg_left hlog hB
  linarith [le_abs_self A]

/-- The folded-circle mean of a function bounded near `w` is bounded. -/
theorem abs_integral_fc_le {G : ℂ → ℝ} {M τ₀ : ℝ} {w v : ℂ}
    (hG : ∀ u : ℂ, dist u w ≤ 2 * τ₀ → |G u| ≤ M) (hv : v ∈ Hbar) (hvw : dist v w ≤ τ₀)
    {s : ℝ} (hs : 0 ≤ s) (hsτ : s ≤ τ₀) : |∫ u, G u ∂foldedCircle v s| ≤ M := by
  have hae : ∀ᵐ u ∂foldedCircle v s, ‖G u‖ ≤ M := by
    filter_upwards [foldedCircle_ae_dist_le' hv hs] with u hu
    exact hG u (by linarith [dist_triangle u v w])
  have := norm_integral_le_of_norm_le_const hae
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  exact this

/-- **The deterministic part is bounded** within `τ₀` of a compact `K ⊆ H`, for smoothing radii
`s ∈ (0, τ₀]` (for a good sample of the wedge data). -/
theorem dPart_bound {γ : ℝ} {Ω' : Type} {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} {ψ : ℂ → ℂ}
    {ω' : Ω'} {C : ℝ} (hψ : PsiGood ψ) (hS : 0 < scaleParam γ (wedge0 γ X A ω'))
    (hgm : Measurable (wg (X ω') (fun t => A t ω') (Qc γ)))
    (hgc : ContinuousOn (wg (X ω') (fun t => A t ω') (Qc γ)) (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg (X ω') (fun t => A t ω') (Qc γ) t| ≤ C * (1 - Real.log t))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ M τ₀ : ℝ, 0 ≤ M ∧ 0 < τ₀ ∧ (∀ w ∈ K, τ₀ < w.im) ∧
      ∀ w ∈ K, ∀ v : ℂ, dist v w ≤ τ₀ → ∀ s : ℝ, 0 < s → s ≤ τ₀ →
        |dPart γ X A ψ ω' (v, s)| ≤ M := by
  set S := scaleParam γ (wedge0 γ X A ω') with hSdef
  have L1 := logBd_profile hψ hS hgm hgc hbd
  have L2 := logBd_log_norm_deriv hψ
  obtain ⟨M₁, t₁, hM₁, ht₁, hK₁, hb₁⟩ := logBd_near_bound L1 hK hKH
  obtain ⟨M₂, t₂, hM₂, ht₂, -, hb₂⟩ := logBd_near_bound L2 hK hKH
  refine ⟨M₁ + |Qc γ * Real.log S| + |Qc γ| * M₂, min t₁ t₂, by positivity,
    lt_min ht₁ ht₂, fun w hw => (min_le_left _ _).trans_lt (hK₁ w hw),
    fun w hw v hvw s hs hsτ => ?_⟩
  have hv : v ∈ Hbar := by
    have h1 : |(v - w).im| ≤ ‖v - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, ← dist_eq_norm] at h1
    have h2 := hK₁ w hw
    have h3 : dist v w ≤ t₁ := hvw.trans (min_le_left _ _)
    show (0 : ℝ) ≤ v.im
    linarith [neg_abs_le (v.im - w.im)]
  have hform : dPart γ X A ψ ω' (v, s) =
      ∫ z, rp (wg (X ω') (fun t => A t ω') (Qc γ)) ((S : ℂ) * ψ z) ∂foldedCircle v s +
        Qc γ * Real.log S + Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle v s := by
    show profPart _ _ _ S _ + _ + _ = _
    rw [profPart_psi_eq hψ hS hgm hgc hbd v hs]
    rfl
  have e1 := abs_integral_fc_le (hb₁ w hw) hv (hvw.trans (min_le_left _ _)) hs.le
    (hsτ.trans (min_le_left _ _))
  have e2 := abs_integral_fc_le (hb₂ w hw) hv (hvw.trans (min_le_right _ _)) hs.le
    (hsτ.trans (min_le_right _ _))
  rw [hform]
  calc _ ≤ |∫ z, rp (wg (X ω') (fun t => A t ω') (Qc γ)) ((S : ℂ) * ψ z) ∂foldedCircle v s| +
        |Qc γ * Real.log S| + |Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle v s| :=
        abs_add_three _ _ _
    _ ≤ _ := by
        have e3 : |Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle v s| ≤ |Qc γ| * M₂ := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
        linarith

end G1FM
end Thm18Asm
end QuantumZipper
