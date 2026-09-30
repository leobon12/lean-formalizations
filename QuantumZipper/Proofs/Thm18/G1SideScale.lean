import QuantumZipper.Proofs.Thm18.G1SideScaleDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (9): continuum smoothing limit of the wedge field on pushed semicircles, over a family

Almost surely, for all large `k`, all maps of the family and all `u ∈ [a,b]`, the pairings
`σ ↦ ∫ evalReg w (fc(v,σ)) d(fc(u, 2^{-k}).map Ψ_q)(v)` of the wedge field
`w = wedgeField (lateralPart X) A Q` are integrable for every `σ > 0` and converge as `σ → 0⁺`
(`ae_wedge_family_continuum`), the input of `Thm18Asm.G1.scaleConsistentAt_of_continuum`.

Proof: the free part by `ae_free_push_continuum` (Duplantier–Sheffield 2011 Prop. 3.1,
Sheffield–Wang arXiv:1605.06171 Lemmas 3.4–3.5, through `swcNA2_tendstoUniformlyOn_smoothing`),
countably many radii `2^{-k}`; the wedge part and the integrability by the deterministic
`wedge_continuum_of_free` on the compact carrier `Ψ_q(closedBall(u, r) ∩ ℍ̄)`, which lies in `ℍ̄`
at distance `≥ c₀` from `0`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore Thm18Asm.G1RC

set_option maxHeartbeats 800000 in
/-- **Continuum smoothing limit of the wedge field on the pushed semicircles, a.s.** -/
theorem ae_wedge_family_continuum {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    {n : ℕ} {Ψ : (Fin n → ℝ) → ℂ → ℂ} {K : Set (Fin n → ℝ)} {a b ρ M m L : ℝ}
    {Kπ : ℝ≥0} {π : (Fin n → ℝ) → Fin n → ℝ} (hab : a < b) (hρ : 0 < ρ)
    (hm : 0 < m) (hL : 0 ≤ L)
    (hcl : ∀ q ∈ K, Ψ q ∈ BdryClass a b ρ M m)
    (hlip : ∀ q ∈ K, ∀ q' ∈ K, ∀ z ∈ thickening ρ (segC a b),
      ‖Ψ q z - Ψ q' z‖ ≤ L * ‖q - q'‖)
    (hπ : LipschitzWith Kπ π) (hπK : ∀ q, π q ∈ K) (hπid : ∀ q ∈ K, π q = q)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsep : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖Ψ q z‖)
    (hHb : ∀ q ∈ K, ∀ z ∈ thickening ρ (segC a b), z ∈ Hbar → Ψ q z ∈ Hbar) :
    ∀ᵐ ω ∂P', ∀ᶠ k in atTop, ∀ q ∈ K, ∀ u ∈ Icc a b,
      (∀ σ : ℝ, 0 < σ → Integrable
        (fun v => evalReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))
          (foldedCircle v σ)) ((foldedCircle (u : ℂ) (radius k)).map (Ψ q))) ∧
      ∃ L : ℝ, Tendsto (fun σ => ∫ v, evalReg (wedgeField (lateralPart (X ω))
          (fun t => A t ω) (Qc γ)) (foldedCircle v σ) ∂((foldedCircle (u : ℂ) (radius k)).map
            (Ψ q))) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  obtain ⟨r₁, hr₁, hfree⟩ := ae_free_push_continuum hab hρ hm hcl hL hlip hπ hπK hπid hX hG
  have hk_ae : ∀ᵐ ω ∂P', ∀ k : ℕ, radius k < r₁ → ∀ q ∈ K,
      ∀ t ∈ Icc (a - radius k) (b + radius k), ∃ Y : ℝ,
        Tendsto (fun σ => ∫ v, G ω (v, σ) ∂((foldedCircle (t : ℂ) (radius k)).map (Ψ q)))
          (𝓝[>] 0) (𝓝 Y) := by
    refine ae_all_iff.2 fun k => ?_
    by_cases hk : radius k < r₁
    · filter_upwards [hfree _ ⟨radius_pos k, hk⟩] with ω h _ using h
    · exact ae_of_all _ fun ω h => absurd h hk
  have hsmall : ∀ᶠ k in atTop, radius k < min r₁ ρ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).eventually (gt_mem_nhds (lt_min hr₁ hρ))
  filter_upwards [hk_ae, hG.ae_good, WedgeCan.ae_raw_dyadic hG,
    WedgeCan4.ae_continuous_wedgeProcess hA, WedgeBdry.ae_bReg_wedgeField hγ hγ2 hα hX hA hI]
    with ω hω hgood hraw hAc hW
  filter_upwards [hsmall] with k hk q hq u hu
  set r := radius k with hrdef
  have hr : 0 < r := radius_pos k
  have hr1 : r < r₁ := lt_of_lt_of_le hk (min_le_left _ _)
  have hrρ : r < ρ := lt_of_lt_of_le hk (min_le_right _ _)
  have hball : closedBall (u : ℂ) r ⊆ thickening ρ (segC a b) := swcN2_ball_sub_thick hu hrρ
  have hψc : ContinuousOn (Ψ q) (closedBall (u : ℂ) r) := (hcl q hq).1.continuousOn.mono hball
  set φθ : ℝ → ℂ := fun θ => Ψ q (foldH (circleMap (u : ℂ) r θ)) with hφθ
  have hpt : ∀ θ, foldH (circleMap (u : ℂ) r θ) ∈ closedBall (u : ℂ) r ∩ Hbar := fun θ =>
    ⟨swcN2_fold_circle_mem hr.le θ, by
      show 0 ≤ (foldH _).im
      unfold foldH
      split_ifs with h
      · exact h
      · simp only [Complex.conj_im]; linarith⟩
  have hφc : Continuous φθ :=
    hψc.comp_continuous (CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _))
      fun θ => (hpt θ).1
  have hμeq : (foldedCircle (u : ℂ) r).map (Ψ q) = circM.map φθ := swcN2_fc_map_eq hr.le hψc
  have : IsProbabilityMeasure (circM.map φθ) :=
    (Measure.isProbabilityMeasure_map_iff hφc.measurable.aemeasurable).2 inferInstance
  set Kc : Set ℂ := Ψ q '' (closedBall (u : ℂ) r ∩ Hbar) with hKcdef
  have hKc : IsCompact Kc :=
    ((isCompact_closedBall _ _).inter_right (isClosed_le continuous_const
      Complex.continuous_im)).image_of_continuousOn (hψc.mono inter_subset_left)
  have hKH : Kc ⊆ Hbar := by
    rintro _ ⟨z, hz, rfl⟩; exact hHb q hq z (hball hz.1) hz.2
  have hsepK : ∀ v ∈ Kc, c₀ ≤ ‖v‖ := by
    rintro _ ⟨z, hz, rfl⟩; exact hsep q hq z (hball hz.1)
  have hμK : ∀ᵐ v ∂(circM.map φθ), v ∈ Kc :=
    (ae_map_iff hφc.measurable.aemeasurable hKc.isClosed.measurableSet).2
      (ae_of_all _ fun θ => ⟨_, hpt θ, rfl⟩)
  have huI : u ∈ Icc (a - r) (b + r) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨Y, hY⟩ := hω k hr1 q hq u huI
  rw [← hrdef, hμeq] at hY
  rw [hμeq]
  exact wedge_continuum_of_free hgood hraw hAc (Qc γ) hW.1.1 hKc hKH hμK hc₀ hsepK hY

end G1Side
end QuantumZipper
