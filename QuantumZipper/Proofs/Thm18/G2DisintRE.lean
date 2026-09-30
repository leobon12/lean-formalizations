import QuantumZipper.Proofs.Thm18.G2DisintRD
import QuantumZipper.Proofs.Thm18.G2DisintXE

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: the zoom error tends to `0` as `C → ∞`

The zoom of the resampled field at a margin root does not depend on the coefficient once `C` is
large (`G2ZoomLocStmt`). The expected root-kernel mass of the disagreement set tends to `0`
(`g2r_zoomErr_tendsto`, dominated convergence twice). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem g2r_kernel_mass {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) :
    ∫⁻ ω, g2rκM γ i m (g2Y (g2rφ i m) α ω) univ ∂gffBase.P < ⊤ := by
  have hc0 : 0 ≤ i.t₂ + i.r₂ := by have := i.t₂_add_r₂; have := i.hη; linarith
  have hc1 : i.t₂ + i.r₂ < 1 := by have := i.t₂_add_r₂; have := i.hη; have := i.hηδ; have := i.hδ; linarith
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (lintegral_hν_Icc_zero_lt_top hγ hγ2 hc0 hc1)
  filter_upwards [g2r_ae_pw hγ hγ2 i hm α] with ω ⟨_, h2, _⟩
  rw [h2, Measure.restrict_apply_univ]
  exact measure_mono fun x hx => hx.2

/-- **The zoom error tends to zero** (`G2ZoomLocStmt`, dominated convergence). -/
theorem g2r_zoomErr_tendsto {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G2ZoomLocStmt γ)
    (i : G3Idx) {m : ℝ} (hm : 0 < m) {α : Ω₀ → ℝ} (hα : Measurable α) {s : Set LawD}
    (hs : s ∈ lawCyl) :
    Tendsto (fun C => ∫⁻ ω, ∫⁻ x, g2xZD γ C (g2rφ i m) s (g2Y (g2rφ i m) α ω, x, α ω)
      ∂(g2rκM γ i m (g2Y (g2rφ i m) α ω)) ∂gffBase.P) atTop (𝓝 0) := by
  set φ := g2rφ i m with hφ
  set Y := g2Y φ α with hYdef
  have hYm : Measurable Y := measurable_g2Y φ hα
  have hsm := measurableSet_lawCyl hs
  have hmeasC : ∀ C, Measurable fun ω => ∫⁻ x, g2xZD γ C φ s (Y ω, x, α ω)
      ∂(g2rκM γ i m (Y ω)) := fun C => by
    have hf : Measurable fun q : Ω₀ × ℝ => g2xZD γ C φ s (Y q.1, q.2, α q.1) :=
      (measurable_g2xZD γ C φ hsm).comp ((hYm.comp measurable_fst).prodMk
        (measurable_snd.prodMk (hα.comp measurable_fst)))
    exact hf.lintegral_kernel_prod_right' (κ := (g2rκM γ i m).comap Y hYm)
  have hle1 : ∀ C p, g2xZD γ C φ s p ≤ 1 := fun C p => by
    unfold g2xZD; exact indicator_le_self' (fun _ _ => zero_le_one) p
  have h0 : Tendsto (fun C => ∫⁻ ω, ∫⁻ x, g2xZD γ C φ s (Y ω, x, α ω) ∂(g2rκM γ i m (Y ω))
      ∂gffBase.P) atTop (𝓝 (∫⁻ _ω, 0 ∂gffBase.P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun ω => g2rκM γ i m (Y ω) univ) (Eventually.of_forall hmeasC)
      (Eventually.of_forall fun C => Eventually.of_forall fun ω => ?_)
      (g2r_kernel_mass hγ hγ2 i hm α).ne ?_
    · calc ∫⁻ x, g2xZD γ C φ s (Y ω, x, α ω) ∂(g2rκM γ i m (Y ω))
          ≤ ∫⁻ _x, 1 ∂(g2rκM γ i m (Y ω)) := lintegral_mono fun x => hle1 C _
        _ = _ := lintegral_one
    · filter_upwards [g2r_ae_pw hγ hγ2 i hm α,
        hZ s hs φ (continuous_g2Phi _ _) (g2rR i m) (g2rR_pos i hm)] with ω ⟨_, h2, _, _, hW⟩ hz
      have hfin : IsFiniteMeasure (g2rκM γ i m (Y ω)) := ⟨by
        rw [h2, Measure.restrict_apply_univ]
        exact (measure_mono (fun x (hx : x ∈ g2rM i m) =>
          (⟨hx.2.1, g2rM_le_W i hm hx⟩ : x ∈ Icc 0 (g2rW i m)))).trans_lt hW⟩
      have hi := tendsto_lintegral_filter_of_dominated_convergence (μ := g2rκM γ i m (Y ω))
        (F := fun C x => g2xZD γ C φ s (Y ω, x, α ω)) (f := fun _ => 0) (fun _ => 1) (l := (atTop : Filter ℝ))
        (Eventually.of_forall fun C => (measurable_g2xZD γ C φ hsm).comp
          (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
        (Eventually.of_forall fun C => Eventually.of_forall fun x => hle1 C _)
        (by rw [lintegral_one]; exact measure_ne_top _ _) ?_
      · simpa using hi
      · rw [h2]
        refine (ae_restrict_iff' (measurableSet_g2rM i m)).2 (Eventually.of_forall fun x hx => ?_)
        have hball := g2rφ_ball_root i hm hx.1
        have e1 := hz x hball (α ω - α ω)
        have e2 := hz x hball (0 - α ω)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [e1, e2] with C h1 h2
        rw [← zoomLaw_g2Field_eq_add] at h1 h2
        symm
        unfold g2xZD
        rw [indicator_of_notMem]
        simp only [mem_setOf_eq, not_not]
        rw [h1, h2]
  simpa using h0

end Thm18Asm
end QuantumZipper
