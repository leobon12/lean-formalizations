import QuantumZipper.Proofs.Thm18.G1Side3Lim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (15): `HasAreaLimit` for the pulled-back canonical field, per sample

Assembly of `G1Side.tendsto_area_rect` over the rectangles `R_n` (G1Side3Lim.lean), with the
limit identified as the pullback `pullMu μ_w (s ψ)` (`G1Side.integral_pullMu`):
`hasAreaLimit_sample`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

/-- The larger rectangles `U_n`. -/
def recU (n : ℕ) : Set ℂ := rectC (-(n + 1 : ℝ)) (n + 1) (1 / (2 * (n + 1 : ℝ))) (n + 1)

theorem ball_sub_recU {n : ℕ} {z : ℂ} (hz : z ∈ recR n) {r : ℝ} (hr : r ≤ 1 / (2 * (n + 1 : ℝ))) :
    closedBall z r ⊆ recU n := by
  intro u hu
  have hd := mem_closedBall.1 hu
  have h1 := Complex.abs_re_le_norm (u - z)
  have h2 := Complex.abs_im_le_norm (u - z)
  rw [← dist_eq_norm, Complex.sub_re] at h1
  rw [← dist_eq_norm, Complex.sub_im] at h2
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr1 : r ≤ 1 := hr.trans (by rw [div_le_one (by positivity)]; linarith)
  have hr2 : 1 / (2 * (n + 1 : ℝ)) = 1 / (n + 1 : ℝ) - 1 / (2 * (n + 1 : ℝ)) := by
    field_simp; ring
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

variable {x0 : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {ψ : ℂ → ℂ} {s : ℝ}

set_option maxHeartbeats 1600000 in
/-- **The area limit of the pulled-back canonical field** (per sample). -/
theorem hasAreaLimit_sample {γ : ℝ} (hγ : 0 < γ) (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hWg : IsLQGGood γ (wedgeField (lateralPart x0) A (Qc γ)))
    {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1)) (hcw' : Tendsto cw' atTop (𝓝 1))
    (hWin : E6.WindowLimits γ (wedgeField (lateralPart x0) A (Qc γ)) cw cw')
    (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hψi : InjOn ψ H)
    (hψH : MapsTo ψ H H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hψint : ∀ d ∈ Hbar, ∀ r > 0,
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hs : 0 < s)
    (hRC3 : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale (wedgeField (lateralPart x0) A (Qc γ)) (Qc γ) s) ψ (Qc γ))
          (foldedCircle d r) =
        coordChange (rescale (wedgeField (lateralPart x0) A (Qc γ)) (Qc γ) s) ψ (Qc γ)
          (foldedCircle d r))
    (HL : ∀ n : ℕ, ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
      Tendsto (fun j => ∫ u, avgReg x0 j u
          ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
        (𝓝 (evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u))))
    (HX : ∀ n : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ recR n,
      |evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
        evalReg x0 (foldedCircle ((s : ℂ) * ψ z)
          (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η)
    (HC : ∀ n : ℕ, ∃ k₁ : ℕ, ∀ k ≥ k₁, ∀ α ∈ Icc (1 : ℝ) 2, ∀ v ∈ recU n, ∃ Y : ℝ,
      Tendsto (fun σ => ∫ u, F (u, σ)
        ∂((foldedCircle v (α * radius k)).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y)) :
    HasAreaLimit γ
      (coordChange (rescale (wedgeField (lateralPart x0) A (Qc γ)) (Qc γ) s) ψ (Qc γ))
      (pullMu (qAreaMeasure γ (wedgeField (lateralPart x0) A (Qc γ))) fun u => (s : ℂ) * ψ u) := by
  set w := wedgeField (lateralPart x0) A (Qc γ) with hw
  set Φ : ℂ → ℂ := fun u => (s : ℂ) * ψ u with hΦ
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hΦc : ContinuousOn Φ H := continuousOn_const.mul hψd.continuousOn
  have hΦi : InjOn Φ H := fun u hu v hv h => hψi hu hv (mul_left_cancel₀ hsc h)
  have hΦH : MapsTo Φ H H := fun u hu => by
    show 0 < ((s : ℂ) * ψ u).im
    rw [Complex.im_ofReal_mul]; exact mul_pos hs (hψH hu)
  have hΦ0 : ∀ z ∈ H, deriv Φ z ≠ 0 := fun z hz => by
    have hdψ : DifferentiableAt ℂ ψ z :=
      hψd.differentiableAt (isOpen_H'.mem_nhds hz)
    rw [show deriv Φ z = (s : ℂ) * deriv ψ z from deriv_const_mul _ hdψ]
    exact mul_ne_zero hsc (hψ0 z hz)
  have hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ w K < ⊤ := fun K hK hKH =>
    hWg.qAreaMeasure_spec.2.1 K hK hKH
  refine ⟨pullMu_compl_H hΦc hΦi, fun K hK hKH => ?_, fun f hf hfc hfH => ?_⟩
  · rw [pullMu_apply hΦc hΦi hK.isClosed.measurableSet, inter_eq_left.2 hKH]
    exact hμK _ (hK.image_of_continuousOn (hΦc.mono hKH)) (hΦH.image_subset.trans' (image_mono hKH))
  -- the test function lies in some `R_n`
  obtain ⟨n, hn⟩ := exists_recR hfc hfH
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the rational rectangle `R_n`
  set a : ℚ := -(n : ℚ) with ha
  set b : ℚ := (n : ℚ) with hb
  set c : ℚ := 1 / ((n : ℚ) + 1) with hcq
  set d : ℚ := (n : ℚ) with hd
  have hrect : rectC (a : ℝ) b c d = recR n := by
    simp only [recR, ha, hb, hcq, hd]; push_cast; rfl
  have hc0 : (0 : ℝ) < c := by rw [hcq]; push_cast; positivity
  -- the class of `Φ` on `R_n`, with rational constants
  obtain ⟨ρ', M', m', hρ', hm', hcl'⟩ := exists_areaClass (a := a) (b := b) (d := d)
    ((differentiableOn_const _).mul hψd) hΦi hΦH hΦ0 hc0
  obtain ⟨ρq, hρq0, hρq⟩ := exists_rat_btwn hρ'
  obtain ⟨Mq, hMq⟩ := exists_rat_gt M'
  obtain ⟨mq, hmq0, hmq⟩ := exists_rat_btwn hm'
  have hcl : Φ ∈ AreaClass a b c d ρq Mq mq :=
    areaClass_mono hcl' hρq.le hMq.le hmq.le
  -- the neighbourhood `U_n` and the continuum limits
  obtain ⟨k₁, hk₁⟩ := HC n
  set δ : ℝ := 1 / (4 * (n + 1 : ℝ)) with hδdef
  have hδ : 0 < δ := by positivity
  set ρ₀ : ℝ := min (radius k₁) δ with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (radius_pos k₁) hδ
  have hU : ∀ v ∈ recU n, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      ρ < v.im ∧ ContinuousOn ψ (closedBall v ρ) ∧ MapsTo ψ (closedBall v ρ) H ∧
      (∀ᵐ u ∂foldedCircle v ρ, deriv ψ u ≠ 0) ∧
      Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle v ρ) ∧
      ∃ Y : ℝ, Tendsto (fun σ => ∫ u, F (u, σ)
        ∂((foldedCircle v ρ).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y) := by
    intro v hv ρ hρ hρρ
    have hvim : 1 / (2 * (n + 1 : ℝ)) ≤ v.im := hv.2.1
    have hδ2 : δ < 1 / (2 * (n + 1 : ℝ)) := by
      rw [hδdef]; apply one_div_lt_one_div_of_lt (by positivity); linarith
    have hρv : ρ < v.im := by linarith [min_le_right (radius k₁) δ]
    have hbH := closedBall_subset_H hρv
    have hvH : v ∈ Hbar := show (0 : ℝ) ≤ v.im by linarith
    refine ⟨hρv, hψd.continuousOn.mono hbH, hψH.mono_left hbH, ?_, hψint v hvH ρ hρ, ?_⟩
    · filter_upwards [ae_fc_mem_closedBall hvH hρ.le] with u hu
      exact hψ0 u (hbH hu)
    · obtain ⟨k, hk, α, hα, rfl⟩ := exists_offset hρ (lt_of_lt_of_le hρρ (min_le_left _ _))
      exact hk₁ k hk α hα v hv
  have hRU : ∀ z ∈ rectC (a : ℝ) b c d, closedBall z (ρ₀ + δ) ⊆ recU n := by
    intro z hz
    rw [hrect] at hz
    refine ball_sub_recU hz ?_
    have h1 : ρ₀ ≤ δ := min_le_right _ _
    have h2 : δ + δ = 1 / (2 * (n + 1 : ℝ)) := by rw [hδdef]; field_simp; ring
    linarith
  have hfK : tsupport f ⊆ interior (rectC (a : ℝ) b c d) := by rw [hrect]; exact hn
  have HLn : ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC (a : ℝ) b c d,
      Tendsto (fun j => ∫ u, avgReg x0 j u
          ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
        (𝓝 (evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u))) := by
    rw [hrect]; exact HL n
  have HXn : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC (a : ℝ) b c d,
      |evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
        evalReg x0 (foldedCircle ((s : ℂ) * ψ z)
          (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η := by
    rw [hrect]; exact HX n
  have ht := tendsto_area_rect hγ hgood hraw hA hWg hcw hcw' hWin hψm hs hρ₀ hδ hU hRC3 hc0
    (by exact_mod_cast hρq0) (by exact_mod_cast hmq0) hcl hRU HLn HXn hf hfc hfK
  rw [integral_pullMu hΦc hΦi (hrect ▸ recR_subset_H n) hf (hfK.trans interior_subset)]
  exact ht

end G1Side
end QuantumZipper
