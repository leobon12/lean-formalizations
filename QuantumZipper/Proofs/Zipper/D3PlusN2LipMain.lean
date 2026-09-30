import QuantumZipper.Proofs.Zipper.D3PlusN2LipPair
import QuantumZipper.Proofs.Zipper.D3PlusN2LipMollify
import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeDef
import QuantumZipper.Proofs.Zipper.D3PlusN2OscEquiv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-LIPDET: the first-mode node implies the Lipschitz pairing node

`n2ZPairLip_of_firstMode : N2ZFirstModeStmt → N2ZPairLipStmt` (deterministic half (D) of
`N2ZPairLipStmt`). Steps:

* (b) `n2Lip_core_bound` (`D3PlusN2LipCore`): smooth test functions, fixed smoothing radius;
* (a) `n2Lip_pair_smooth` (`D3PlusN2LipPair`): vanishing smoothing radius (clause (ii) of
  `IsRegularWith`);
* (c) here: mollification of Lipschitz test functions (`n2Lip_exists_mollify`, with an
  `L · ε` uniform error that is sent to `0`), and the scale `c` by the change of variables
  `v = c u` (`Measure.integral_comp_smul`).

Own elementary argument (the route of the N2Z-PAIROSC report); no published source states this
exact deterministic implication.
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped Real Topology NNReal

namespace QuantumZipper
namespace D3Plus

/-- The first-mode hypothesis on a regular witness `F`, as in `N2ZFirstModeStmt`. -/
def N2LipModeHyp (F : ℂ × ℝ → ℝ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ H →
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
      ‖∫ θ in (0 : ℝ)..(2 * π),
          ((F (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I), s) : ℝ) : ℂ) *
            Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C / Real.sqrt τ

/-- **Unit scale** (`c = 1`), Lipschitz test functions. -/
theorem n2Lip_det1 {F : ℂ × ℝ → ℝ} (hcont : ContinuousOn F (Hbar ×ˢ Ioi 0))
    (hlim : TendstoLocallyUniformlyOn
      (fun (ρ : ℝ) (p : ℂ × ℝ) => ∫ u, F (u, ρ) ∂foldedCircle p.1 p.2) F (𝓝[>] 0)
      (Hbar ×ˢ Ioi 0))
    (hFM : N2LipModeHyp F) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f → (∀ z ∉ K, f z = 0) →
      ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
        |∫ u, (F (u, t) - F (u, s)) * f u| ≤ C * L * Real.sqrt (max t s) := by
  obtain ⟨R, hR0, hRsub⟩ := hK.exists_cthickening_subset_open isOpen_H hKH
  set r := R / 2 with hr
  have hr0 : 0 < r := by positivity
  set K' := Metric.cthickening r K with hK'def
  have hK' : IsCompact K' := hK.cthickening
  have hK'r : Metric.cthickening r K' ⊆ H := by
    refine (Metric.cthickening_cthickening_subset hr0.le hr0.le K).trans ?_
    rw [hr, add_halves]; exact hRsub
  have hK'H : K' ⊆ H := (Metric.cthickening_mono (by linarith) K).trans hRsub
  have hK'b : K' ⊆ Hbar := hK'H.trans H_subset_Hbar
  have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
  obtain ⟨C₀, τ₀, hτ₀, hm⟩ := hFM K' hK' hK'H
  set M := max C₀ 0 with hM
  -- the ordered case
  have key : ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f → (∀ z ∉ K, f z = 0) →
      ∀ a b : ℝ, 0 < a → a ≤ b → b < min r τ₀ →
        |∫ u, (F (u, b) - F (u, a)) * f u| ≤ volume.real K' * L * M * (2 * Real.sqrt b) := by
    intro L f hf hfK a b ha hab hb
    have hb0 : 0 < b := ha.trans_le hab
    have hFt : ∀ τ, 0 < τ → ContinuousOn (fun u => F (u, τ)) K' := fun τ hτ =>
      (hcont.comp (continuousOn_id.prodMk continuousOn_const) fun z hz => ⟨hz, hτ⟩).mono hK'b
    obtain ⟨B₁, hB₁⟩ := hK'.exists_bound_of_continuousOn ((hFt b hb0).sub (hFt a ha))
    refine n2Lip_le_of_small (D := B₁ * L * volume.real K') hr0 fun ε hε hεr => ?_
    obtain ⟨f', hf'c, hf'L, hf'K, hf'f⟩ := n2Lip_exists_mollify hf hfK hε
    have hf'K' : ∀ z ∉ K', f' z = 0 := fun z hz =>
      hf'K z fun h => hz (Metric.cthickening_mono hεr K h)
    have hfK' : ∀ z ∉ K', f z = 0 := fun z hz => hfK z fun h => hz (hKK' h)
    have hsplit : ∀ u, (F (u, b) - F (u, a)) * f u =
        (F (u, b) - F (u, a)) * f' u + (F (u, b) - F (u, a)) * (f u - f' u) := fun u => by ring
    have hi1 : Integrable fun u => (F (u, b) - F (u, a)) * f' u :=
      n2Lip_intK hK' (((hFt b hb0).sub (hFt a ha)).mul hf'c.continuous.continuousOn)
        (fun z hz => by simp [hf'K' z hz])
    have hi2 : Integrable fun u => (F (u, b) - F (u, a)) * (f u - f' u) :=
      n2Lip_intK hK' (((hFt b hb0).sub (hFt a ha)).mul
        (hf.continuous.sub hf'c.continuous).continuousOn)
        (fun z hz => by simp [hf'K' z hz, hfK' z hz])
    simp_rw [hsplit]
    rw [integral_add hi1 hi2]
    have h1 := n2Lip_pair_smooth hcont hlim hK' hK'r hm hf'c hf'K' L.2 hf'L ha hab
      (hb.trans_le (min_le_left _ _)) (hb.trans_le (min_le_right _ _))
    have h2 : |∫ u, (F (u, b) - F (u, a)) * (f u - f' u)| ≤ B₁ * L * volume.real K' * ε := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K')
        (fun z hz => by simp [hf'K' z hz, hfK' z hz]), ← Real.norm_eq_abs]
      refine (norm_setIntegral_le_of_norm_le_const (C := B₁ * (L * ε)) hK'.measure_lt_top
        fun u hu => ?_).trans_eq (by ring)
      rw [norm_mul]
      refine mul_le_mul (hB₁ u hu) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hB₁ u hu))
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hf'f u
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  refine ⟨volume.real K' * M * 2, min r τ₀, lt_min hr0 hτ₀, ?_⟩
  intro L f hf hfK t ht s hs
  rcases le_total s t with hst | hts
  · rw [max_eq_left hst]
    exact (key L f hf hfK s t hs.1 hst ht.2).trans_eq (by ring)
  · rw [max_eq_right hts]
    have : (fun u => (F (u, t) - F (u, s)) * f u) = fun u => -((F (u, s) - F (u, t)) * f u) := by
      funext u; ring
    rw [this, integral_neg, abs_neg]
    exact (key L f hf hfK t s ht.1 hts hs.2).trans_eq (by ring)

/-- **Scale `c`**, by the change of variables `v = c u`. -/
theorem n2Lip_detc {F : ℂ × ℝ → ℝ} (hcont : ContinuousOn F (Hbar ×ˢ Ioi 0))
    (hlim : TendstoLocallyUniformlyOn
      (fun (ρ : ℝ) (p : ℂ × ℝ) => ∫ u, F (u, ρ) ∂foldedCircle p.1 p.2) F (𝓝[>] 0)
      (Hbar ×ˢ Ioi 0))
    (hFM : N2LipModeHyp F) {c : ℝ} (hc : 0 < c) {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (L : ℝ≥0) (f : ℂ → ℝ), LipschitzWith L f → (∀ z ∉ K, f z = 0) →
      ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
        |∫ u, (F ((c : ℂ) * u, t) - F ((c : ℂ) * u, s)) * f u| ≤
          C * L * Real.sqrt (max t s) := by
  set K₁ := (fun u : ℂ => c • u) '' K with hK₁
  have hK₁c : IsCompact K₁ := hK.image (continuous_const_smul c)
  have hK₁H : K₁ ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    show 0 < (c • u).im
    rw [Complex.smul_im]
    exact mul_pos hc (hKH hu)
  obtain ⟨C, δ, hδ, hb⟩ := n2Lip_det1 hcont hlim hFM hK₁c hK₁H
  refine ⟨(c ^ 2)⁻¹ * C * c⁻¹, δ, hδ, ?_⟩
  intro L f hf hfK t ht s hs
  set f₁ : ℂ → ℝ := fun v => f (c⁻¹ • v) with hf₁
  have hf₁L : LipschitzWith (L * ‖c⁻¹‖₊) f₁ := hf.comp (lipschitzWith_smul c⁻¹)
  have hf₁K : ∀ z ∉ K₁, f₁ z = 0 := fun z hz => by
    refine hfK _ fun h => hz ⟨c⁻¹ • z, h, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hb1 := hb (L * ‖c⁻¹‖₊) f₁ hf₁L hf₁K t ht s hs
  have hcv : ∫ u, (F ((c : ℂ) * u, t) - F ((c : ℂ) * u, s)) * f u =
      (c ^ 2)⁻¹ * ∫ v, (F (v, t) - F (v, s)) * f₁ v := by
    have := Measure.integral_comp_smul (μ := (volume : Measure ℂ))
      (fun v => (F (v, t) - F (v, s)) * f₁ v) c
    rw [Complex.finrank_real_complex, abs_of_pos (by positivity), smul_eq_mul] at this
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hf₁, Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne', Complex.ofReal_one, one_mul]
  rw [hcv, abs_mul, abs_of_pos (by positivity)]
  have hn : ‖c⁻¹‖ = c⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
  push_cast at hb1
  rw [hn] at hb1
  calc (c ^ 2)⁻¹ * |∫ v, (F (v, t) - F (v, s)) * f₁ v|
      ≤ (c ^ 2)⁻¹ * (C * (L * c⁻¹) * Real.sqrt (max t s)) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = (c ^ 2)⁻¹ * C * c⁻¹ * L * Real.sqrt (max t s) := by ring

/-- **N2Z-LIPDET.** The first-mode node implies the Lipschitz pairing node. -/
theorem n2ZPairLip_of_firstMode (hFM : N2ZFirstModeStmt) : N2ZPairLipStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hGv, hfm⟩ := hFM P X hX
  refine ⟨G, hGv, ?_⟩
  filter_upwards [hfm, hGv.reg] with ω hω hreg
  intro c hc K hK hKH
  exact n2Lip_detc (hGv.cont ω) hreg.2.2 hω hc hK hKH

/-- Consequence: the first-mode node closes the oscillation node. -/
theorem n2ZPairOsc_of_firstMode (hFM : N2ZFirstModeStmt) : N2ZPairOscStmt :=
  n2ZPairOsc_of_lip (n2ZPairLip_of_firstMode hFM)

end D3Plus
end QuantumZipper
