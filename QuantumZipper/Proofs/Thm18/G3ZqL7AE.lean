import QuantumZipper.Proofs.Thm18.G3ZqG2DisR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (7): the G2 engine from zoom locality at quantum-typical points only

The zoom-locality hypothesis `G2ZoomLocStmtZ Z γ` of the ported G2 engine (G3ZqG2DisX/DisR) asks
the bump locality at EVERY point `x`. Its consumers (`g2x_zoomErr_tendstoZ`,
`g2r_zoomErr_tendstoZ`) use it inside a dominated convergence against the kernel
`g2xκM`/`g2rκM`, which a.s. equals the restriction of the quantum boundary length
`g3Hν γ ω = ν_h` of the free field (`g2x_ae_pw`, `g2r_ae_pw`). So only `ν_h`-a.e. `x` is needed:
`G3ZqLZoomLocAEStmt Z γ`. Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66 (the zoom at
a quantum-typical point `x`).

Verbatim copies of the consumer chain with the a.e. hypothesis; headlines
`g2RootLenSmoothZ_of_zoomLocAE`, `g2FixMixStmtZ_of_fix_zoomLocAE`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

namespace G3ZqL

/-- **Zoom locality at quantum-typical points**: `G2ZoomLocStmtZ` with "for every `x`" replaced by
"for `ν_h`-a.e. `x ∈ (−1, 1)`", `ν_h = g3Hν γ ω` the quantum boundary length of the free
field (all G2 regions lie in `(−1, 1)`). -/
def G3ZqLZoomLocAEStmt (Z : ℝ → FieldSample → ℝ → LawD) (γ : ℝ) : Prop :=
  ∀ s ∈ lawCyl, ∀ φ : ℂ → ℝ, Continuous φ → ∀ r : ℝ, 0 < r →
    ∀ᵐ ω ∂gffBase.P, ∀ᵐ (x : ℝ) ∂(g3Hν γ ω), x ∈ Ioo (-1 : ℝ) 1 → (∀ z ∈ ball (x : ℂ) r, φ z = 0) → ∀ b : ℝ,
      ∀ᶠ C in (atTop : Filter ℝ),
        (Z C (normField γ gffBase.X ω + ofFun fun z => b * φ z) x ∈ s ↔
          Z C (normField γ gffBase.X ω) x ∈ s)

end G3ZqL

variable {Z : ℝ → FieldSample → ℝ → LawD}

theorem g2x_zoomErr_tendstoAE (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G3ZqL.G3ZqLZoomLocAEStmt Z γ)
    (i : G3Idx) {m : ℝ} (hm : 0 < m) {α : Ω₀ → ℝ} (hα : Measurable α) {s : Set LawD}
    (hs : s ∈ lawCyl) :
    Tendsto (fun C => ∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C (g2xφ i m) s (g2Y (g2xφ i m) α ω, x, α ω)
      ∂(g2xκM γ i m (g2Y (g2xφ i m) α ω)) ∂gffBase.P) atTop (𝓝 0) := by
  set φ := g2xφ i m with hφ
  set Y := g2Y φ α with hYdef
  have hYm : Measurable Y := measurable_g2Y φ hα
  have hsm := measurableSet_lawCyl hs
  have hmeasC : ∀ C, Measurable fun ω => ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω)
      ∂(g2xκM γ i m (Y ω)) := fun C => by
    have hf : Measurable fun q : Ω₀ × ℝ => g2xZDZ Z γ C φ s (Y q.1, q.2, α q.1) :=
      (measurable_g2xZDZ hZm γ C φ hsm).comp ((hYm.comp measurable_fst).prodMk
        (measurable_snd.prodMk (hα.comp measurable_fst)))
    exact hf.lintegral_kernel_prod_right' (κ := (g2xκM γ i m).comap Y hYm)
  have hle1 : ∀ C p, g2xZDZ Z γ C φ s p ≤ 1 := fun C p => by
    unfold g2xZDZ; exact indicator_le_self' (fun _ _ => zero_le_one) p
  have h0 : Tendsto (fun C => ∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω) ∂(g2xκM γ i m (Y ω))
      ∂gffBase.P) atTop (𝓝 (∫⁻ _ω, 0 ∂gffBase.P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun ω => g2xκM γ i m (Y ω) univ) (Eventually.of_forall hmeasC)
      (Eventually.of_forall fun C => Eventually.of_forall fun ω => ?_)
      (g2x_kernel_mass hγ hγ2 i hm α).ne ?_
    · calc ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω) ∂(g2xκM γ i m (Y ω))
          ≤ ∫⁻ _x, 1 ∂(g2xκM γ i m (Y ω)) := lintegral_mono fun x => hle1 C _
        _ = _ := lintegral_one
    · filter_upwards [g2x_ae_pw hγ hγ2 i hm α, g3Mass_ae_eq_honest hγ hγ2 i,
        hZ s hs φ (continuous_g2Phi _ _) (g2xR i m) (g2xR_pos i hm)] with ω ⟨_, h2, _, _, hW⟩ _ hz
      have hfin : IsFiniteMeasure (g2xκM γ i m (Y ω)) := ⟨by
        rw [h2, Measure.restrict_apply_univ]
        exact (measure_mono (fun x hx => hx.2)).trans_lt hW⟩
      have hi := tendsto_lintegral_filter_of_dominated_convergence (μ := g2xκM γ i m (Y ω))
        (F := fun C x => g2xZDZ Z γ C φ s (Y ω, x, α ω)) (f := fun _ => 0) (fun _ => 1) (l := (atTop : Filter ℝ))
        (Eventually.of_forall fun C => (measurable_g2xZDZ hZm γ C φ hsm).comp
          (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
        (Eventually.of_forall fun C => Eventually.of_forall fun x => hle1 C _)
        (by rw [lintegral_one]; exact measure_ne_top _ _) ?_
      · simpa using hi
      · rw [h2]
        refine (ae_restrict_iff' (measurableSet_g2xM i m)).2 ?_
        filter_upwards [hz] with x hzx hx
        have hball := g2xφ_ball_root i hm hx.1
        have hI : x ∈ Ioo (-1 : ℝ) 1 := by
          have := i.hδ; have := hx.2.1; have := hx.2.2
          constructor <;> linarith
        have e1 := hzx hI hball (α ω - α ω)
        have e2 := hzx hI hball (0 - α ω)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [e1, e2] with C h1 h2
        rw [← zoomZ_g2Field_eq_add hZa] at h1 h2
        symm
        unfold g2xZDZ
        rw [indicator_of_notMem]
        simp only [mem_setOf_eq, not_not]
        rw [h1, h2]
  simpa using h0

theorem g2RootXDisintStmt_of_zoomAE (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G3ZqL.G3ZqLZoomLocAEStmt Z γ) :
    G2RootXDisintStmtZ Z γ := by
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
  have hzt := g2x_zoomErr_tendstoAE hZm hZa hγ hγ2 hZ i₀ hm hαm hs
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
  have hbound : (∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C (g2xφ i₀ m) s (g2Y (g2xφ i₀ m) α ω, x, α ω)
      ∂(g2xκM γ i₀ m (g2Y (g2xφ i₀ m) α ω)) ∂gffBase.P).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε.le hC.le
  have hsm := measurableSet_lawCyl hs
  have hPsi := measurable_g2Psi i.t₁ i.r₁ i.t₂ i.r₂
  refine ⟨{q : ((AdmIdx → ℝ) × ℝ) × ℝ | Z C (g2Field γ (g2xφ i₀ m) q.1.1 0) q.1.2 ∈ s ∧
      (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ q.1.1, q.2) ∈ G'}, ?_, ?_, fun ρ hρ => ?_⟩
  · exact ((hZm C).comp (((measurable_g2Field γ _).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)).prodMk
      (measurable_snd.comp measurable_fst)) hsm).inter
      (((hPsi.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd) hG')
  · rw [g3RootInt_eq_of_δ hδi]
    refine (g2x_boundZ hZm hγ hγ2 i₀ hm hαm hindY C hsm _ hPsi hG' (fun _ ℓ => ℓ)
      measurable_snd (g3RootEvXZ Z γ i s m G) ?_).trans hbound
    · filter_upwards with ω h1 h2 h3 h4 x hx
      by_cases hxM : x ∈ g2xM i₀ m
      · rw [indicator_of_mem hxM]
        have hiff : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvXZ Z γ i s m G ↔
            (g2Y (g2xφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
              Z C (g2Field γ (g2xφ i₀ m) p.1 p.2.2) p.2.1 ∈ s ∧
              (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ p.1, (fun _ ℓ => ℓ) (p.1, p.2.1)
                (g2xf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G'} := by
          simp only [g3RootEvXZ, mem_setOf_eq, hCi, zoomZ_eq_g2Field hZa γ (g2xφ i₀ m) α ω,
            h3 x hxM]
          have hmarg : |x - i.t₁| + m < i.r₁ := by rw [ht₁, hr₁]; exact hxM.1
          rw [hGeq, mem_preimage, g2OutV_eq_Psi hzoff α ω]
          exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmarg, h.2⟩⟩
        by_cases hmem : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvXZ Z γ i s m G
        · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
        · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
      · rw [indicator_of_notMem hxM, indicator_of_notMem]
        intro hmem
        exact hxM ⟨by rw [← ht₁, ← hr₁]; exact hmem.2.1, hx⟩
  · rw [g3RootInt_eq_of_δ hδi]
    have hΛ : Measurable (Function.uncurry fun (ξ : (AdmIdx → ℝ) × ℝ) (ℓ : ℝ) =>
        ℓ - min (g2xgap γ i₀ m κ ξ) ρ) :=
      measurable_snd.sub (((measurable_g2xgap γ i₀ m κ).comp measurable_fst).min measurable_const)
    refine (g2x_boundZ hZm hγ hγ2 i₀ hm hαm hindY C hsm _ hPsi hG'
      (fun ξ ℓ => ℓ - min (g2xgap γ i₀ m κ ξ) ρ) hΛ (g3RootEvXclipZ Z γ i s m κ ρ G) ?_).trans hbound
    filter_upwards with ω h1 h2 h3 h4 x hx
    by_cases hxM : x ∈ g2xM i₀ m
    · rw [indicator_of_mem hxM]
      have hcut : max (g3CutLen γ κ ω x) ((g3Hν γ ω (Icc x 0)).toReal - ρ) =
          g2xf γ i₀ m (g2Y (g2xφ i₀ m) α ω, x) (α ω) -
            min (g2xgap γ i₀ m κ (g2Y (g2xφ i₀ m) α ω, x)) ρ := by
        rw [g3CutLen, h4 κ hκ.1.le hκ.2 x hxM, ← h3 x hxM, g2_max_sub_min]
      have hiff : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvXclipZ Z γ i s m κ ρ G ↔
          (g2Y (g2xφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
            Z C (g2Field γ (g2xφ i₀ m) p.1 p.2.2) p.2.1 ∈ s ∧
            (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ p.1, (fun ξ ℓ => ℓ - min (g2xgap γ i₀ m κ ξ) ρ) (p.1, p.2.1)
              (g2xf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G'} := by
        simp only [g3RootEvXclipZ, mem_setOf_eq, hCi, zoomZ_eq_g2Field hZa γ (g2xφ i₀ m) α ω, hcut]
        have hmarg : |x - i.t₁| + m < i.r₁ := by rw [ht₁, hr₁]; exact hxM.1
        rw [hGeq, mem_preimage, g2OutV_eq_Psi hzoff α ω]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmarg, h.2⟩⟩
      by_cases hmem : (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∈ g3RootEvXclipZ Z γ i s m κ ρ G
      · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
      · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
    · rw [indicator_of_notMem hxM, indicator_of_notMem]
      intro hmem
      exact hxM ⟨by rw [← ht₁, ← hr₁]; exact hmem.2.1, hx⟩

theorem g2r_zoomErr_tendstoAE (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G3ZqL.G3ZqLZoomLocAEStmt Z γ)
    (i : G3Idx) {m : ℝ} (hm : 0 < m) {α : Ω₀ → ℝ} (hα : Measurable α) {s : Set LawD}
    (hs : s ∈ lawCyl) :
    Tendsto (fun C => ∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C (g2rφ i m) s (g2Y (g2rφ i m) α ω, x, α ω)
      ∂(g2rκM γ i m (g2Y (g2rφ i m) α ω)) ∂gffBase.P) atTop (𝓝 0) := by
  set φ := g2rφ i m with hφ
  set Y := g2Y φ α with hYdef
  have hYm : Measurable Y := measurable_g2Y φ hα
  have hsm := measurableSet_lawCyl hs
  have hmeasC : ∀ C, Measurable fun ω => ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω)
      ∂(g2rκM γ i m (Y ω)) := fun C => by
    have hf : Measurable fun q : Ω₀ × ℝ => g2xZDZ Z γ C φ s (Y q.1, q.2, α q.1) :=
      (measurable_g2xZDZ hZm γ C φ hsm).comp ((hYm.comp measurable_fst).prodMk
        (measurable_snd.prodMk (hα.comp measurable_fst)))
    exact hf.lintegral_kernel_prod_right' (κ := (g2rκM γ i m).comap Y hYm)
  have hle1 : ∀ C p, g2xZDZ Z γ C φ s p ≤ 1 := fun C p => by
    unfold g2xZDZ; exact indicator_le_self' (fun _ _ => zero_le_one) p
  have h0 : Tendsto (fun C => ∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω) ∂(g2rκM γ i m (Y ω))
      ∂gffBase.P) atTop (𝓝 (∫⁻ _ω, 0 ∂gffBase.P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun ω => g2rκM γ i m (Y ω) univ) (Eventually.of_forall hmeasC)
      (Eventually.of_forall fun C => Eventually.of_forall fun ω => ?_)
      (g2r_kernel_mass hγ hγ2 i hm α).ne ?_
    · calc ∫⁻ x, g2xZDZ Z γ C φ s (Y ω, x, α ω) ∂(g2rκM γ i m (Y ω))
          ≤ ∫⁻ _x, 1 ∂(g2rκM γ i m (Y ω)) := lintegral_mono fun x => hle1 C _
        _ = _ := lintegral_one
    · filter_upwards [g2r_ae_pw hγ hγ2 i hm α,
        hZ s hs φ (continuous_g2Phi _ _) (g2rR i m) (g2rR_pos i hm)] with ω ⟨_, h2, _, _, hW⟩ hz
      have hfin : IsFiniteMeasure (g2rκM γ i m (Y ω)) := ⟨by
        rw [h2, Measure.restrict_apply_univ]
        exact (measure_mono (fun x (hx : x ∈ g2rM i m) =>
          (⟨hx.2.1, g2rM_le_W i hm hx⟩ : x ∈ Icc 0 (g2rW i m)))).trans_lt hW⟩
      have hi := tendsto_lintegral_filter_of_dominated_convergence (μ := g2rκM γ i m (Y ω))
        (F := fun C x => g2xZDZ Z γ C φ s (Y ω, x, α ω)) (f := fun _ => 0) (fun _ => 1) (l := (atTop : Filter ℝ))
        (Eventually.of_forall fun C => (measurable_g2xZDZ hZm γ C φ hsm).comp
          (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
        (Eventually.of_forall fun C => Eventually.of_forall fun x => hle1 C _)
        (by rw [lintegral_one]; exact measure_ne_top _ _) ?_
      · simpa using hi
      · rw [h2]
        refine (ae_restrict_iff' (measurableSet_g2rM i m)).2 ?_
        filter_upwards [hz] with x hzx hx
        have hball := g2rφ_ball_root i hm hx.1
        have hI : x ∈ Ioo (-1 : ℝ) 1 := by
          have := i.hη; have := i.hηδ; have := i.hδ; have h1 := hx.2.1; have h2 := hx.2.2
          unfold G3Idx.t₂ G3Idx.r₂ at h2
          constructor <;> linarith
        have e1 := hzx hI hball (α ω - α ω)
        have e2 := hzx hI hball (0 - α ω)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [e1, e2] with C h1 h2
        rw [← zoomZ_g2Field_eq_add hZa] at h1 h2
        symm
        unfold g2xZDZ
        rw [indicator_of_notMem]
        simp only [mem_setOf_eq, not_not]
        rw [h1, h2]
  simpa using h0

theorem g2RootRDisintStmt_of_zoomAE (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hZ : G3ZqL.G3ZqLZoomLocAEStmt Z γ) :
    G2RootRDisintStmtZ Z γ := by
  intro t ht δ η m hm
  by_cases hex : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η
  swap
  · refine ⟨1, one_pos, fun ε _ => ⟨Unit, inferInstance, 0, inferInstance, gaussianReal 0 1,
      inferInstance, fun _ a => a, gaussianReal_absolutelyContinuous 0 one_ne_zero,
      measurable_snd, fun _ => differentiable_id, fun _ a => by simp, fun κ _ =>
      ⟨fun _ => 0, measurable_const, fun _ => le_rfl, Eventually.of_forall fun C i hi => ?_⟩⟩⟩
    exact absurd ⟨i, by rw [hi], by rw [hi]⟩ hex
  obtain ⟨i₀, hδ₀, hη₀⟩ := hex
  obtain ⟨hφ1, hφ2, hφ3, hφ4, hφ5⟩ := g2rφ_bump_hyps i₀ hm
  obtain ⟨α, v, hv, hαm, hlaw, hind⟩ := g2BumpDecompStmt_holds _ hφ1 hφ2 hφ3 hφ4 hφ5
  have hindY := indepFun_g2Y hind
  have hYm := measurable_g2Y (g2rφ i₀ m) hαm
  have : IsProbabilityMeasure (gffBase.P.map α) :=
    (Measure.isProbabilityMeasure_map_iff hαm.aemeasurable).2 inferInstance
  have hN : gffBase.P.map α ≪ volume := by
    rw [hlaw]; exact gaussianReal_absolutelyContinuous 0 hv.ne'
  have hQ : IsFiniteMeasure ((gffBase.P.map (g2Y (g2rφ i₀ m) α)) ⊗ₘ g2rκM γ i₀ m) := by
    refine ⟨?_⟩
    rw [← lintegral_one, Measure.lintegral_compProd measurable_const]
    simp only [lintegral_one]
    rw [lintegral_map (Kernel.measurable_coe _ MeasurableSet.univ) hYm]
    exact g2r_kernel_mass hγ hγ2 i₀ hm α
  refine ⟨g2rR i₀ m, g2rR_pos i₀ hm, fun ε hε => ⟨(AdmIdx → ℝ) × ℝ, inferInstance,
    (gffBase.P.map (g2Y (g2rφ i₀ m) α)) ⊗ₘ g2rκM γ i₀ m, hQ, gffBase.P.map α, inferInstance,
    g2rf γ i₀ m, hN, measurable_g2rf γ i₀ m, g2rf_differentiable hγ i₀ hm,
    g2rf_deriv_pos hγ i₀ hm, fun κ hκ => ⟨g2rgap γ i₀ m κ, measurable_g2rgap γ i₀ m κ,
    g2rgap_nonneg γ i₀ m hκ.1.le, ?_⟩⟩⟩
  have hzt := g2r_zoomErr_tendstoAE hZm hZa hγ hγ2 hZ i₀ hm hαm ht
  have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  filter_upwards [hzt.eventually (gt_mem_nhds hεpos)] with C hC i hi G hG
  have hδi : i.δ = i₀.δ := by unfold G3Idx.δ; rw [hi]; exact hδ₀.symm
  have hηi : i.η = i₀.η := by unfold G3Idx.η; rw [hi]; exact hη₀.symm
  have hCi : i.C = C := by unfold G3Idx.C; rw [hi]
  have ht₁ : i.t₁ = i₀.t₁ := by unfold G3Idx.t₁; rw [hδi, hηi]
  have hr₁ : i.r₁ = i₀.r₁ := by unfold G3Idx.r₁; rw [hδi, hηi]
  have ht₂ : i.t₂ = i₀.t₂ := by unfold G3Idx.t₂; rw [hηi]
  have hr₂ : i.r₂ = i₀.r₂ := by unfold G3Idx.r₂; rw [hηi]
  obtain ⟨G', hG', hGeq⟩ := exists_outside_factor hG
  have hzoff : ∀ z, z ∉ Metric.ball (i.t₂ : ℂ) i.r₂ → g2rφ i₀ m z = 0 := fun z hz =>
    g2rφ_zero_off i₀ hm (by rwa [ht₂, hr₂] at hz)
  have hbound : (∫⁻ ω, ∫⁻ x, g2xZDZ Z γ C (g2rφ i₀ m) t (g2Y (g2rφ i₀ m) α ω, x, α ω)
      ∂(g2rκM γ i₀ m (g2Y (g2rφ i₀ m) α ω)) ∂gffBase.P).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε.le hC.le
  have htm := measurableSet_lawCyl ht
  set Psi' : (AdmIdx → ℝ) → (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ≥0∞ :=
    fun y => (g2Psi i.t₁ i.r₁ i.t₂ i.r₂ y, g2rMfun γ i (g2rφ i₀ m) y) with hPsi'
  have hPsi : Measurable Psi' :=
    (measurable_g2Psi i.t₁ i.r₁ i.t₂ i.r₂).prodMk (measurable_g2rMfun γ i _)
  set G'' : Set (((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ≥0∞) × ℝ) :=
    {p | (p.1.1, p.2) ∈ G' ∧ ENNReal.ofReal p.2 ≤ p.1.2} with hG''def
  have hG'' : MeasurableSet G'' :=
    (((measurable_fst.comp measurable_fst).prodMk measurable_snd) hG').inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
        (measurable_snd.comp measurable_fst))
  have hMass : ∀ ω, g3Mass γ i ω = g2rMfun γ i (g2rφ i₀ m) (g2Y (g2rφ i₀ m) α ω) :=
    fun ω => g3Mass_eq_g2rMfun i hm i₀ ht₁ hr₁ ht₂ hr₂ α ω
  have hidx : i.t₂ + i.r₂ = i₀.t₂ + i₀.r₂ := by rw [ht₂, hr₂]
  refine ⟨{q : ((AdmIdx → ℝ) × ℝ) × ℝ | Z C (g2Field γ (g2rφ i₀ m) q.1.1 0) q.1.2 ∈ t ∧
      (Psi' q.1.1, q.2) ∈ G''}, ?_, ?_, fun ρ hρ => ?_⟩
  · exact ((hZm C).comp (((measurable_g2Field γ _).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_const)).prodMk
      (measurable_snd.comp measurable_fst)) htm).inter
      (((hPsi.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd) hG'')
  · rw [g3RootIntR_eq_of_idx hidx]
    refine (g2r_boundZ hZm hγ hγ2 i₀ hm hαm hindY C htm _ hPsi hG'' (fun _ ℓ => ℓ)
      measurable_snd (g3RootEvRZ Z γ i t m G ∩ g3TM γ i) ?_).trans hbound
    · filter_upwards with ω h1 h2 h3 h4 x hx
      by_cases hxM : x ∈ g2rM i₀ m
      · rw [indicator_of_mem hxM]
        have hmarg : |x - i.t₂| + m < i.r₂ := by rw [ht₂, hr₂]; exact hxM.1
        have hiff : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvRZ Z γ i t m G ∩ g3TM γ i ↔
            (g2Y (g2rφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
              Z C (g2Field γ (g2rφ i₀ m) p.1 p.2.2) p.2.1 ∈ t ∧
              (Psi' p.1, (fun _ ℓ => ℓ) (p.1, p.2.1)
                (g2rf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G''} := by
          simp only [g3RootEvRZ, g3TM, mem_inter_iff, mem_setOf_eq, hCi,
            zoomZ_eq_g2Field hZa γ (g2rφ i₀ m) α ω, h3 x hxM, hG''def, hPsi', hMass]
          rw [hGeq, mem_preimage, g2OutV_eq_Psi₂ hzoff α ω]
          exact ⟨fun h => ⟨h.1.1, h.1.2.2, h.2⟩, fun h => ⟨⟨h.1, hmarg, h.2.1⟩, h.2.2⟩⟩
        by_cases hmem : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvRZ Z γ i t m G ∩ g3TM γ i
        · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
        · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
      · rw [indicator_of_notMem hxM, indicator_of_notMem]
        intro hmem
        exact hxM ⟨by rw [← ht₂, ← hr₂]; exact hmem.1.2.1, hx⟩
  · rw [g3RootIntR_eq_of_idx hidx]
    have hΛ : Measurable (Function.uncurry fun (ξ : (AdmIdx → ℝ) × ℝ) (ℓ : ℝ) =>
        ℓ - min (g2rgap γ i₀ m κ ξ) ρ) :=
      measurable_snd.sub (((measurable_g2rgap γ i₀ m κ).comp measurable_fst).min measurable_const)
    refine (g2r_boundZ hZm hγ hγ2 i₀ hm hαm hindY C htm _ hPsi hG''
      (fun ξ ℓ => ℓ - min (g2rgap γ i₀ m κ ξ) ρ) hΛ (g3RootEvRclipZ Z γ i t m κ ρ G) ?_).trans hbound
    filter_upwards with ω h1 h2 h3 h4 x hx
    by_cases hxM : x ∈ g2rM i₀ m
    · rw [indicator_of_mem hxM]
      have hmarg : |x - i.t₂| + m < i.r₂ := by rw [ht₂, hr₂]; exact hxM.1
      have hcut : max (g3CutLenR γ κ ω x) ((g3Hν γ ω (Icc 0 x)).toReal - ρ) =
          g2rf γ i₀ m (g2Y (g2rφ i₀ m) α ω, x) (α ω) -
            min (g2rgap γ i₀ m κ (g2Y (g2rφ i₀ m) α ω, x)) ρ := by
        rw [g3CutLenR, h4 κ hκ.1.le hκ.2 x hxM, ← h3 x hxM, g2_max_sub_min]
      have hiff : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvRclipZ Z γ i t m κ ρ G ↔
          (g2Y (g2rφ i₀ m) α ω, x, α ω) ∈ {p : (AdmIdx → ℝ) × ℝ × ℝ |
            Z C (g2Field γ (g2rφ i₀ m) p.1 p.2.2) p.2.1 ∈ t ∧
            (Psi' p.1, (fun ξ ℓ => ℓ - min (g2rgap γ i₀ m κ ξ) ρ) (p.1, p.2.1)
              (g2rf γ i₀ m (p.1, p.2.1) p.2.2)) ∈ G''} := by
        simp only [g3RootEvRclipZ, mem_setOf_eq, hCi, zoomZ_eq_g2Field hZa γ (g2rφ i₀ m) α ω, hcut,
          hG''def, hPsi', hMass]
        rw [hGeq, mem_preimage, g2OutV_eq_Psi₂ hzoff α ω]
        exact ⟨fun h => ⟨h.1, h.2.2.1, h.2.2.2⟩, fun h => ⟨h.1, hmarg, h.2.1, h.2.2⟩⟩
      by_cases hmem : (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) ∈ g3RootEvRclipZ Z γ i t m κ ρ G
      · rw [indicator_of_mem hmem, indicator_of_mem (hiff.1 hmem)]; rfl
      · rw [indicator_of_notMem hmem, indicator_of_notMem (mt hiff.2 hmem)]
    · rw [indicator_of_notMem hxM, indicator_of_notMem]
      intro hmem
      exact hxM ⟨by rw [← ht₂, ← hr₂]; exact hmem.2.1, hx⟩

/-- **Smoothing headline, a.e. form.** -/
theorem g2RootLenSmoothZ_of_zoomLocAE {Z' : ℝ → FieldSample → ℝ → LawD}
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hZloc : G3ZqL.G3ZqLZoomLocAEStmt Z γ) (hZloc' : G3ZqL.G3ZqLZoomLocAEStmt Z' γ) :
    G2RootXLenSmoothStmtZ Z γ ∧ G2RootRLenSmoothStmtZ Z' γ :=
  ⟨g2RootXLenSmoothStmt_of_clipZ hZm hγ hγ2
      (g2RootXClipSmoothStmt_of_disintZ (g2RootXDisintStmt_of_zoomAE hZm hZa hγ hγ2 hZloc)),
    g2RootRLenSmoothStmt_of_clipZ hZm' hγ hγ2
      (g2RootRClipSmoothStmt_of_disintZ (g2RootRDisintStmt_of_zoomAE hZm' hZa' hγ hγ2 hZloc'))⟩

end Thm18Asm
end QuantumZipper
