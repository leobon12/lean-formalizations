import QuantumZipper.Proofs.Thm18.G2DisintXF
import QuantumZipper.Proofs.Thm18.G2ConstBump

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: `G2RootXDisintStmt` from zoom locality

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66). With the Gaussian bump decomposition
(`g2BumpDecompStmt_holds`), the local rule (`g2_ae_bdryM_loc`), positivity (`g2_ae_pos_g3Hν`) and
the comparison bound `g2x_bound`, the only remaining input is zoom locality `G2ZoomLocStmt`
(the zoom at the root does not see a bump away from it once `C` is large).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem g2_max_sub_min (f g ρ : ℝ) : max (f - g) (f - ρ) = f - min g ρ := by
  rcases le_total g ρ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-- **`G2RootXDisintStmt` from zoom locality.** -/
theorem g2RootXDisintStmt_of_zoom {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G2ZoomLocStmt γ) :
    G2RootXDisintStmt γ := by
  intro s hs δ η m hm
  by_cases hex : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η
  swap
  · refine ⟨1, one_pos, fun ε _ => ⟨Unit, inferInstance, 0, inferInstance, gaussianReal 0 1,
      inferInstance, fun _ a => a, gaussianReal_absolutelyContinuous 0 one_ne_zero,
      measurable_snd, fun _ => differentiable_id, fun _ a => by simp, fun κ _ =>
      ⟨fun _ => 0, measurable_const, fun _ => le_rfl, Eventually.of_forall fun C i hi => ?_⟩⟩⟩
    exact absurd ⟨i, by rw [hi], by rw [hi]⟩ hex
  obtain ⟨i₀, hδ₀, hη₀⟩ := hex
  obtain ⟨hφ1, hφ2, hφ3, hφ4, hφ5⟩ := g2xφ_bump_hyps i₀ hm
  obtain ⟨α, v, hv, hαm, hlaw, hind⟩ := g2BumpDecompStmt_holds _ hφ1 hφ2 hφ3 hφ4 hφ5
  have hindY := indepFun_g2Y hind
  have hYm := measurable_g2Y (g2xφ i₀ m) hαm
  have : IsProbabilityMeasure (gffBase.P.map α) :=
    (Measure.isProbabilityMeasure_map_iff hαm.aemeasurable).2 inferInstance
  have hN : gffBase.P.map α ≪ volume := by
    rw [hlaw]; exact gaussianReal_absolutelyContinuous 0 hv.ne'
  have hQ : IsFiniteMeasure ((gffBase.P.map (g2Y (g2xφ i₀ m) α)) ⊗ₘ g2xκM γ i₀ m) := by
    refine ⟨?_⟩
    rw [← lintegral_one, Measure.lintegral_compProd measurable_const]
    simp only [lintegral_one]
    rw [lintegral_map (Kernel.measurable_coe _ MeasurableSet.univ) hYm]
    exact g2x_kernel_mass hγ hγ2 i₀ hm α
  refine ⟨g2xR i₀ m, g2xR_pos i₀ hm, fun ε hε => ⟨(AdmIdx → ℝ) × ℝ, inferInstance,
    (gffBase.P.map (g2Y (g2xφ i₀ m) α)) ⊗ₘ g2xκM γ i₀ m, hQ, gffBase.P.map α, inferInstance,
    g2xf γ i₀ m, hN, measurable_g2xf γ i₀ m, g2xf_differentiable hγ i₀ hm,
    g2xf_deriv_pos hγ i₀ hm, fun κ hκ => ⟨g2xgap γ i₀ m κ, measurable_g2xgap γ i₀ m κ,
    g2xgap_nonneg γ i₀ m hκ.1.le, ?_⟩⟩⟩
  have hzt := g2x_zoomErr_tendsto hγ hγ2 hZ i₀ hm hαm hs
  have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  filter_upwards [hzt.eventually (gt_mem_nhds hεpos)] with C hC i hi G hG
  have hδi : i.δ = i₀.δ := by unfold G3Idx.δ; rw [hi]; exact hδ₀.symm
  have hηi : i.η = i₀.η := by unfold G3Idx.η; rw [hi]; exact hη₀.symm
  have hCi : i.C = C := by unfold G3Idx.C; rw [hi]
  have ht₁ : i.t₁ = i₀.t₁ := by unfold G3Idx.t₁; rw [hδi, hηi]
  have hr₁ : i.r₁ = i₀.r₁ := by unfold G3Idx.r₁; rw [hδi, hηi]
  obtain ⟨G', hG', hGeq⟩ := exists_outside_factor hG
  have hzoff : ∀ z, z ∉ ball (i.t₁ : ℂ) i.r₁ → g2xφ i₀ m z = 0 := fun z hz =>
    g2xφ_zero_off i₀ hm (by rwa [ht₁, hr₁] at hz)
  have hbound : (∫⁻ ω, ∫⁻ x, g2xZD γ C (g2xφ i₀ m) s (g2Y (g2xφ i₀ m) α ω, x, α ω)
      ∂(g2xκM γ i₀ m (g2Y (g2xφ i₀ m) α ω)) ∂gffBase.P).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε.le hC.le
  have hsm := measurableSet_lawCyl hs
  have hPsi := measurable_g2Psi i.t₁ i.r₁ i.t₂ i.r₂
  refine ⟨{q : ((AdmIdx → ℝ) × ℝ) × ℝ | zoomLaw γ C (g2Field γ (g2xφ i₀ m) q.1.1 0) q.1.2 ∈ s ∧
      (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ q.1.1, q.2) ∈ G'}, ?_, ?_, fun ρ hρ => ?_⟩
  · exact ((measurable_zoomLaw γ C).comp (((measurable_g2Field γ _).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)).prodMk
      (measurable_snd.comp measurable_fst)) hsm).inter
      (((hPsi.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd) hG')
  · rw [g3RootInt_eq_of_δ hδi]
    refine (g2x_bound hγ hγ2 i₀ hm hαm hindY C hsm _ hPsi hG' (fun _ ℓ => ℓ)
      measurable_snd (g3RootEvX γ i s m G) ?_).trans hbound
    · filter_upwards with ω h1 h2 h3 h4 x hx
      by_cases hxM : x ∈ g2xM i₀ m
      · rw [indicator_of_mem hxM]
        have hiff : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvX γ i s m G ↔
            (g2Y (g2xφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
              zoomLaw γ C (g2Field γ (g2xφ i₀ m) p.1 p.2.2) p.2.1 ∈ s ∧
              (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ p.1, (fun _ ℓ => ℓ) (p.1, p.2.1)
                (g2xf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G'} := by
          simp only [g3RootEvX, mem_setOf_eq, hCi, zoomLaw_eq_g2Field γ (g2xφ i₀ m) α ω,
            h3 x hxM]
          have hmarg : |x - i.t₁| + m < i.r₁ := by rw [ht₁, hr₁]; exact hxM.1
          rw [hGeq, mem_preimage, g2OutV_eq_Psi hzoff α ω]
          exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmarg, h.2⟩⟩
        by_cases hmem : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvX γ i s m G
        · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
        · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
      · rw [indicator_of_notMem hxM, indicator_of_notMem]
        intro hmem
        exact hxM ⟨by rw [← ht₁, ← hr₁]; exact hmem.2.1, hx⟩
  · rw [g3RootInt_eq_of_δ hδi]
    have hΛ : Measurable (Function.uncurry fun (ξ : (AdmIdx → ℝ) × ℝ) (ℓ : ℝ) =>
        ℓ - min (g2xgap γ i₀ m κ ξ) ρ) :=
      measurable_snd.sub (((measurable_g2xgap γ i₀ m κ).comp measurable_fst).min measurable_const)
    refine (g2x_bound hγ hγ2 i₀ hm hαm hindY C hsm _ hPsi hG'
      (fun ξ ℓ => ℓ - min (g2xgap γ i₀ m κ ξ) ρ) hΛ (g3RootEvXclip γ i s m κ ρ G) ?_).trans hbound
    filter_upwards with ω h1 h2 h3 h4 x hx
    by_cases hxM : x ∈ g2xM i₀ m
    · rw [indicator_of_mem hxM]
      have hcut : max (g3CutLen γ κ ω x) ((g3Hν γ ω (Icc x 0)).toReal - ρ) =
          g2xf γ i₀ m (g2Y (g2xφ i₀ m) α ω, x) (α ω) -
            min (g2xgap γ i₀ m κ (g2Y (g2xφ i₀ m) α ω, x)) ρ := by
        rw [g3CutLen, h4 κ hκ.1.le hκ.2 x hxM, ← h3 x hxM, g2_max_sub_min]
      have hiff : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvXclip γ i s m κ ρ G ↔
          (g2Y (g2xφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
            zoomLaw γ C (g2Field γ (g2xφ i₀ m) p.1 p.2.2) p.2.1 ∈ s ∧
            (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ p.1, (fun ξ ℓ => ℓ - min (g2xgap γ i₀ m κ ξ) ρ) (p.1, p.2.1)
              (g2xf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G'} := by
        simp only [g3RootEvXclip, mem_setOf_eq, hCi, zoomLaw_eq_g2Field γ (g2xφ i₀ m) α ω, hcut]
        have hmarg : |x - i.t₁| + m < i.r₁ := by rw [ht₁, hr₁]; exact hxM.1
        rw [hGeq, mem_preimage, g2OutV_eq_Psi hzoff α ω]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmarg, h.2⟩⟩
      by_cases hmem : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvXclip γ i s m κ ρ G
      · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
      · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
    · rw [indicator_of_notMem hxM, indicator_of_notMem]
      intro hmem
      exact hxM ⟨by rw [← ht₁, ← hr₁]; exact hmem.2.1, hx⟩

end Thm18Asm
end QuantumZipper
