import QuantumZipper.Proofs.Thm18.G1Z2MeasCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-MEAS, part 6: scale consistency of translated pairings from PAIR-LIM

`g1z2_scaleConsistent_translate`: for a regular sample `x` with the continuum pairing limits of
`G1.ChoiceRegularCore` (PAIR-LIM: for every dilated test measure `(ρ± dz) ∘ (c ·)⁻¹` the
circle-smoothed pairings converge as the radius `s → 0⁺`), every real translate of `x` is scale
consistent at dilated test measures: the regularized pairings along the radii `2^{-k}` and
`b 2^{-k}` agree. A translated and dilated test measure is a dilated test measure of the
translated test function (`g1z2_tmeas_map_add`, `g1z2_testFun_translate`). Own elementary
argument.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- Translation of a test measure. -/
theorem g1z2_tmeas_map_add (σ : ℂ → ℝ) (q : ℂ) :
    (G1.tmeas σ).map (· + q) = G1.tmeas fun z => σ (z - q) := by
  have hm : Measurable fun z : ℂ => z + q := measurable_add_const q
  ext s hs
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs,
    ← lintegral_indicator (hm hs), ← lintegral_indicator hs]
  rw [← lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
    (s.indicator fun w => ENNReal.ofReal (σ (w - q))) q]
  congr 1
  funext z
  by_cases hz : z + q ∈ s
  · rw [indicator_of_mem hz, indicator_of_mem (show z ∈ (· + q) ⁻¹' s from hz), add_sub_cancel_right]
  · rw [indicator_of_notMem hz, indicator_of_notMem (show z ∉ (· + q) ⁻¹' s from hz)]

/-- A real translate of a test function on `ℍ` is a test function on `ℍ`. -/
theorem g1z2_testFun_translate (ρ : TestFun H) (q : ℝ) :
    ∃ ρ' : TestFun H, ρ'.1 = fun z => ρ.1 (z - (q : ℂ)) := by
  set h : ℂ ≃ₜ ℂ := Homeomorph.addRight (-(q : ℂ)) with hh
  have hfun : (fun z => ρ.1 (z - (q : ℂ))) = ρ.1 ∘ h := by
    funext z; simp [hh, sub_eq_add_neg]
  refine ⟨⟨fun z => ρ.1 (z - (q : ℂ)), ρ.2.1.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩, rfl⟩
  · rw [hfun]; exact ρ.2.2.1.comp_homeomorph h
  · rw [hfun]
    intro z hz
    have h1 := GoodTransforms.tsupport_comp_subset (f := ρ.1) h.continuous hz
    have h2 : h z ∈ H := ρ.2.2.2 h1
    have : (h z).im = z.im := by simp [hh]
    show 0 < z.im
    rw [← this]; exact h2

theorem g1z2_tsupport_neg (f : ℂ → ℝ) : tsupport (fun z => -f z) = tsupport f := by
  unfold tsupport
  congr 1
  ext z
  simp

/-- A test measure is concentrated on `ℍ`. -/
theorem g1z2_ae_tmeas_mem_H {σ : ℂ → ℝ} (hσ : tsupport σ ⊆ H) (hm : Measurable σ) :
    ∀ᵐ z ∂(G1.tmeas σ), z ∈ H := by
  refine (ae_withDensity_iff (μ := (volume : Measure ℂ)) (f := fun z => ENNReal.ofReal (σ z))
    (p := fun z => z ∈ H) (ENNReal.measurable_ofReal.comp hm)).2 ?_
  refine Eventually.of_forall fun z hz => hσ (subset_tsupport σ ?_)
  intro h0
  exact hz (by rw [h0, ENNReal.ofReal_zero])

theorem g1z2_measurable_evalReg_fc (x : FieldSample) (s : ℝ) :
    Measurable fun v : ℂ => evalReg x (foldedCircle v s) :=
  Measurable.comp (g := fun q : FieldSample × (ℂ × ℝ) => evalReg q.1 (foldedCircle q.2.1 q.2.2))
    (f := fun v : ℂ => ((x, (v, s)) : FieldSample × (ℂ × ℝ))) IndepParams.measurable_evalReg_fc₂
    (measurable_const.prodMk (measurable_id.prodMk measurable_const))

/-- **Scale consistency of translated pairings from PAIR-LIM.** -/
theorem g1z2_scaleConsistent_translate {Q : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F)
    (hpair : ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
      (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg x (foldedCircle u s))
        ((G1.tmeas σ).map fun z => (c : ℂ) * z)) ∧
      ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg x (foldedCircle u s)
        ∂((G1.tmeas σ).map fun z => (c : ℂ) * z)) (𝓝[>] 0) (𝓝 L))
    (p : ℝ) {b : ℝ} (hb : 0 < b) {c : ℝ} (hc : 0 < c) (ρ : TestFun H) (σ : ℂ → ℝ)
    (hσ : σ = ρ.1 ∨ σ = fun z => -ρ.1 z) :
    G1.ScaleConsistentAt (translate x (p : ℂ)) Q b ((G1.tmeas σ).map fun z => (c : ℂ) * z) := by
  have hbc : 0 < b * c := mul_pos hb hc
  -- the test function and its translate
  have hσc : Continuous σ := by
    rcases hσ with rfl | rfl
    · exact ρ.2.1.continuous
    · exact ρ.2.1.continuous.neg
  have hσs : tsupport σ ⊆ H := by
    rcases hσ with rfl | rfl
    · exact ρ.2.2.2
    · rw [g1z2_tsupport_neg]; exact ρ.2.2.2
  have hσcs : HasCompactSupport σ := by
    rcases hσ with rfl | rfl
    · exact ρ.2.2.1
    · exact ρ.2.2.1.neg
  set q : ℝ := p / (b * c) with hq
  obtain ⟨ρ', hρ'⟩ := g1z2_testFun_translate ρ q
  set σ' : ℂ → ℝ := fun z => σ (z - (q : ℂ)) with hσ'
  have hσ'r : σ' = ρ'.1 ∨ σ' = fun z => -ρ'.1 z := by
    rw [hρ']
    rcases hσ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨hint, L, hL⟩ := hpair (b * c) hbc ρ' σ' hσ'r
  -- the measures
  set κ := (G1.tmeas σ).map fun z => (c : ℂ) * z with hκ
  have hmc : Measurable fun z : ℂ => (c : ℂ) * z := measurable_const_mul _
  have hmb : Measurable fun z : ℂ => (b : ℂ) * z := measurable_const_mul _
  have : IsFiniteMeasure (G1.tmeas σ) :=
    isFiniteMeasure_withDensity_ofReal (hσc.integrable_of_hasCompactSupport hσcs).2
  have : IsFiniteMeasure κ := Measure.isFiniteMeasure_map _ _
  have hκH : ∀ᵐ u ∂κ, u ∈ H := by
    rw [hκ]
    refine (ae_map_iff (p := fun u : ℂ => u ∈ H) hmc.aemeasurable isOpen_H.measurableSet).2 ?_
    exact (g1z2_ae_tmeas_mem_H hσs hσc.measurable).mono fun z hz => G1.mul_mem_H hc hz
  have hmap : κ.map (fun u => (b : ℂ) * u + (p : ℂ)) =
      (G1.tmeas σ').map fun z => ((b * c : ℝ) : ℂ) * z := by
    rw [hκ, Measure.map_map (by fun_prop) hmc, hσ', ← g1z2_tmeas_map_add,
      Measure.map_map (by fun_prop) (measurable_add_const _)]
    congr 1
    funext z
    simp only [Function.comp, hq]
    have hbc' : ((b * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hbc.ne'
    rw [mul_add, Complex.ofReal_div, mul_div_cancel₀ _ hbc']
    push_cast; ring
  have hphi : Measurable fun u : ℂ => (b : ℂ) * u + (p : ℂ) := by fun_prop
  -- the smoothed pairing along the translated dilated measure
  set Φ : ℝ → ℝ := fun s => ∫ u, evalReg x (foldedCircle ((b : ℂ) * u + (p : ℂ)) s) ∂κ with hΦ
  have hΦe : ∀ s, Φ s = ∫ v, evalReg x (foldedCircle v s)
      ∂((G1.tmeas σ').map fun z => ((b * c : ℝ) : ℂ) * z) := fun s => by
    rw [← hmap, integral_map hphi.aemeasurable
      ((g1z2_measurable_evalReg_fc x s).aestronglyMeasurable)]
  have hΦL : Tendsto Φ (𝓝[>] 0) (𝓝 L) := by
    rw [show Φ = fun s => ∫ v, evalReg x (foldedCircle v s)
      ∂((G1.tmeas σ').map fun z => ((b * c : ℝ) : ℂ) * z) from funext hΦe]
    exact hL
  have hΦi : ∀ s, 0 < s → Integrable (fun u => evalReg x (foldedCircle ((b : ℂ) * u + (p : ℂ)) s)) κ :=
    fun s hs => by
      have := hint s hs
      rw [← hmap, integrable_map_measure
        ((g1z2_measurable_evalReg_fc x s).aestronglyMeasurable) hphi.aemeasurable] at this
      exact this
  have hrad : Tendsto (fun k : ℕ => b * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hb (radius_pos k)⟩
    have := (tendsto_nhdsWithin_iff.1 RegClosure.tendsto_radius_nhdsGT).1.const_mul b
    rwa [mul_zero] at this
  -- witnesses
  have hy := hF.translate' p
  have hV := hy.rescale' Q hb
  unfold G1.ScaleConsistentAt evalReg
  -- left side
  have hleft : ∀ k : ℕ, ∫ w, avgReg (rescale (translate x (p : ℂ)) Q b) k w ∂κ =
      Φ (b * radius k) + Q * Real.log b * κ.real univ := fun k => by
    have e : ∀ᵐ u ∂κ, avgReg (rescale (translate x (p : ℂ)) Q b) k u =
        evalReg x (foldedCircle ((b : ℂ) * u + (p : ℂ)) (b * radius k)) + Q * Real.log b := by
      filter_upwards [hκH] with u hu
      rw [hV.avgReg_eq k (show u ∈ Hbar from le_of_lt (show 0 < u.im from hu)), hF.evalReg_fc_of_mem (G1.mul_mem_H hb hu |> fun h =>
        (show (b : ℂ) * u + (p : ℂ) ∈ Hbar from by
          show 0 ≤ ((b : ℂ) * u + (p : ℂ)).im
          have : 0 < ((b : ℂ) * u).im := h
          simp only [Complex.add_im, Complex.ofReal_im, add_zero]; exact this.le))
        (mul_pos hb (radius_pos k))]
    rw [integral_congr_ae e, integral_add (hΦi _ (mul_pos hb (radius_pos k)))
      (integrable_const _), integral_const, smul_eq_mul]
    ring
  -- right side
  have hright : ∀ k : ℕ, ∫ w, avgReg (translate x (p : ℂ)) k w ∂(κ.map fun z => (b : ℂ) * z) =
      Φ (radius k) := fun k => by
    rw [integral_map hmb.aemeasurable (RegClosure.measurable_avgReg_slice _ k).aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hκH] with u hu
    have hbu : (b : ℂ) * u ∈ H := G1.mul_mem_H hb hu
    rw [hy.avgReg_eq k (show (b : ℂ) * u ∈ Hbar from le_of_lt (show 0 < ((b : ℂ) * u).im from hbu)), hF.evalReg_fc_of_mem (show (b : ℂ) * u + (p : ℂ) ∈ Hbar from by
      show 0 ≤ ((b : ℂ) * u + (p : ℂ)).im
      have : 0 < ((b : ℂ) * u).im := hbu
      simp only [Complex.add_im, Complex.ofReal_im, add_zero]; exact this.le) (radius_pos k)]
  simp_rw [hleft, hright]
  have h1 : Tendsto (fun k : ℕ => Φ (b * radius k) + Q * Real.log b * κ.real univ) atTop
      (𝓝 (L + Q * Real.log b * κ.real univ)) := (hΦL.comp hrad).add_const _
  have h2 : Tendsto (fun k : ℕ => Φ (radius k)) atTop (𝓝 L) :=
    hΦL.comp RegClosure.tendsto_radius_nhdsGT
  rw [h1.limUnder_eq, h2.limUnder_eq]

end Thm18Asm
end QuantumZipper
