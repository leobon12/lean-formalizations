import QuantumZipper.Proofs.Zipper.SWCoreB7bExist
import QuantumZipper.Proofs.Zipper.SWCoreNA2Unif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (7): continuum smoothing limit of the free field on pushed semicircles

For a regular version `G` of the free field `X` and a finite-parameter Lipschitz family of class
maps, almost surely, for every small `r`, every map of the family and every centre
`t ∈ [a − r, b + r]`, the smoothed pairings `σ ↦ ∫ G(v, σ) d(fc(t,r).map Ψ_q)` converge as
`σ → 0⁺` along the continuum (`ae_free_push_continuum`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1, and Sheffield–Wang
arXiv:1605.06171 Lemmas 3.4–3.5, through `SWCore.swcNA2_tendstoUniformlyOn_smoothing` with the
pushed-semicircle bounds `swcN2_push_bounds` (the pattern of `swcB7_push_tendsto`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm.G1RC

/-- A function continuous on a compact carrier of a finite measure is integrable. -/
theorem integrable_of_continuousOn_carrier {μ : Measure ℂ} [IsFiniteMeasure μ] {Kc : Set ℂ}
    (hK : IsCompact Kc) (hμ : ∀ᵐ v ∂μ, v ∈ Kc) {f : ℂ → ℝ} (hf : ContinuousOn f Kc) :
    Integrable f μ := by
  have h := hf.integrableOn_compact (μ := μ) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h

variable {n : ℕ} {a b ρ M m L : ℝ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)}
  {Kπ : ℝ≥0} {pr : (Fin n → ℝ) → Fin n → ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **Continuum smoothing limit of the free field on the pushed semicircles, a.s.** -/
theorem ae_free_push_continuum (hab : a < b) (hρ : 0 < ρ) (hm : 0 < m)
    (hΨ : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m) (hL0 : 0 ≤ L)
    (hL : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b), ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ pr) (hπK : ∀ q, pr q ∈ K) (hπid : ∀ q ∈ K, pr q = q)
    (hX : IsFreeGFFModConstH X P) (hG : WedgeTK.IsRegVersion X P G) :
    ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ r ∈ Ioo 0 r₂, ∀ᵐ ω ∂P, ∀ q ∈ K, ∀ t ∈ Icc (a - r) (b + r),
      ∃ Y : ℝ, Tendsto (fun σ => ∫ v, G ω (v, σ) ∂((foldedCircle (t : ℂ) r).map (Ψ q)))
        (𝓝[>] 0) (𝓝 Y) := by
  obtain ⟨r₂, hr₂, h⟩ := swcN2_push_bounds hab hρ hm hΨ hL0 hL hπ hπK
  refine ⟨min r₂ (ρ / 3), lt_min hr₂ (by linarith), fun r hr => ?_⟩
  have hr' : r ∈ Ioo 0 r₂ := ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
  have hrρ : 3 * r < ρ := by have := lt_of_lt_of_le hr.2 (min_le_right _ _); linarith
  obtain ⟨hc, hH, hb⟩ := h r hr'
  obtain ⟨β, hβ, hB⟩ := swcNA2_familyBounds hc hH one_pos le_rfl one_pos le_rfl hb
  obtain ⟨Y₀, -, -, hU⟩ := swcNA2_tendstoUniformlyOn_smoothing (m := circM)
    (S := Icc 0 (2 * Real.pi)) hc hH isCompact_Icc circM_compl hβ hB hX hG
  filter_upwards [hU] with ω hω q hq t ht
  have hT : Tendsto (fun σ => ∫ v, G ω (v, σ) ∂(circM.map
      (swcN2PushΦ Ψ pr a b r (Fin.snoc q t : Fin (n + 1) → ℝ)))) (𝓝[>] 0)
      (𝓝 (Y₀ (Fin.snoc q t) ω)) :=
    (hω {Fin.snoc q t} isCompact_singleton).tendsto_at (mem_singleton _)
  rw [swcN2_push_eq hab.le hr.1 hrρ hΨ hπid hq ht] at hT
  exact ⟨_, hT⟩

end G1Side
end QuantumZipper
