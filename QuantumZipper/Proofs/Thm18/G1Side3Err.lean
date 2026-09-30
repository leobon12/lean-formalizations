import QuantumZipper.Proofs.Thm18.G1Side3Split
import QuantumZipper.Proofs.Zipper.SWCoreA9Unif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (9): the offset distortion error of the dilated side map, per sample

For the unscaled wedge field `w`, the dilated map `Φ = s ψ` in an area class of the rectangle
`R`, the RC3 of the pulled-back canonical field, the continuum limits on a neighbourhood `U` of
`R` (`G1Side.evalReg_y_eq`), and, for the free sample, the convergence of the regularizations on
the pushed circles and the pushed-versus-round distortion bound (the finite-parameter area core,
`SWCore.swcNA2I_primed`), the offset distortion error of SW's area transport is small uniformly
over the offsets `α ∈ [1,2]` and the centres `z ∈ R` (`pushErrR_small`). The error splits into
the free-field distortion, the profile averages over the pushed and the round circle (both close
to the profile at `Φ z`), and `Q (∫ log|Φ'| dfc − log|Φ'(z)|)` (`SWCore.areaClass_logAvg`).
Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7); Duplantier–Sheffield 2011 (5.1).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

/-- A continuous function is averaged close to its value at `p` over a measure carried near `p`. -/
theorem abs_integral_sub_le {g : ℂ → ℝ} (hg : Continuous g) {ν : Measure ℂ}
    [IsProbabilityMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hν : ∀ᵐ u ∂ν, u ∈ K) {p : ℂ}
    {ε : ℝ} (hclose : ∀ u ∈ K, |g u - g p| ≤ ε) : |∫ u, g u ∂ν - g p| ≤ ε := by
  have hi : Integrable g ν := integrable_of_continuousOn_carrier hK hν hg.continuousOn
  have e : ∫ u, g u ∂ν - g p = ∫ u, (g u - g p) ∂ν := by
    rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e]
  have h := norm_integral_le_of_norm_le_const (μ := ν) (C := ε)
    (hν.mono fun u hu => by rw [Real.norm_eq_abs]; exact hclose u hu)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

variable {x0 : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {ψ : ℂ → ℂ} {s : ℝ}

set_option maxHeartbeats 800000 in
/-- **The offset distortion error is small, uniformly** (per sample). -/
theorem pushErrR_small {γ : ℝ} (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hW : IsRegularSample (wedgeField (lateralPart x0) A (Qc γ)))
    (hψm : Measurable ψ) (hs : 0 < s) {U : Set ℂ} {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ : 0 < δ)
    (hU : ∀ v ∈ U, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      ρ < v.im ∧ ContinuousOn ψ (closedBall v ρ) ∧ MapsTo ψ (closedBall v ρ) H ∧
      (∀ᵐ u ∂foldedCircle v ρ, deriv ψ u ≠ 0) ∧
      Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle v ρ) ∧
      ∃ Y : ℝ, Tendsto (fun σ => ∫ u, F (u, σ)
        ∂((foldedCircle v ρ).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y))
    (hRC3 : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale (wedgeField (lateralPart x0) A (Qc γ)) (Qc γ) s) ψ (Qc γ))
          (foldedCircle d r) =
        coordChange (rescale (wedgeField (lateralPart x0) A (Qc γ)) (Qc γ) s) ψ (Qc γ)
          (foldedCircle d r))
    {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m)
    (hcl : (fun u => (s : ℂ) * ψ u) ∈ AreaClass a b c d ρ M m)
    (hRU : ∀ z ∈ rectC a b c d, closedBall z (ρ₀ + δ) ⊆ U)
    (HL : ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      Tendsto (fun j => ∫ u, avgReg x0 j u
          ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
        (𝓝 (evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u))))
    (HX : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      |evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
        evalReg x0 (foldedCircle ((s : ℂ) * ψ z)
          (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      |pushErrR γ (wedgeField (lateralPart x0) A (Qc γ)) (fun u => (s : ℂ) * ψ u)
        (α * radius k) z| ≤ η := by
  intro η hη
  set Φ : ℂ → ℂ := fun u => (s : ℂ) * ψ u with hΦ
  set w := wedgeField (lateralPart x0) A (Qc γ) with hw
  set c₀ : ℝ := ρ / 2 with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  set g := profCut x0 A (Qc γ) (c₀ / 2) with hgdef
  have hg : Continuous g := continuous_profCut hgood hA (Qc γ) (by positivity)
  obtain ⟨C, Ld, r₀, hC, -, hr₀, hr₀ρ, hDB⟩ := areaClass_deriv_bounds (a := a) (b := b) (c := c)
    (d := d) (M := M) (m := m) hρ
  -- uniform continuity of `g` on a ball containing everything
  obtain ⟨εg, hεg, hUC⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) (|M| + 1)).uniformContinuousOn_of_continuous hg.continuousOn)
    (η / 6) (by positivity)
  obtain ⟨r₂, hr₂, hlog⟩ := areaClass_logAvg hc hρ hm (η / (3 * (|Qc γ| + 1))) (by positivity)
  set rmax : ℝ := min (min ρ₀ r₀) (min (ρ / (2 * C)) (min r₂ (min (εg / (2 * C)) (1 / C))))
    with hrmax
  have hrmax0 : 0 < rmax := by positivity
  have hsmall : ∀ᶠ k in atTop, 2 * radius k < rmax := by
    filter_upwards [radius_eventually_lt (by positivity : (0 : ℝ) < rmax / 2)] with k hk
    linarith
  filter_upwards [hsmall, HL, HX (η / 3) (by positivity)] with k hk hkL hkX α hα z hz
  set r := α * radius k with hrdef
  have hr : 0 < r := mul_pos (by linarith [hα.1]) (radius_pos k)
  have hrle : r < rmax := by
    have : r ≤ 2 * radius k := mul_le_mul_of_nonneg_right hα.2 (radius_pos k).le
    linarith
  have hrρ₀ : r < ρ₀ := lt_of_lt_of_le hrle ((min_le_left _ _).trans (min_le_left _ _))
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrle ((min_le_left _ _).trans (min_le_right _ _))
  have hrC : r * C ≤ ρ / 2 := by
    have := hrle.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hr2 : r ≤ r₂ :=
    hrle.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrεg : r * C ≤ εg / 2 := by
    have := hrle.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hr1 : r * C ≤ 1 := by
    have := hrle.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
    rw [le_div_iff₀ hC] at this; linarith
  -- geometry of the ball
  have hzthk : ∀ u ∈ closedBall z r, u ∈ thickening ρ (rectC a b c d) := fun u hu =>
    mem_thickening_iff.2 ⟨z, hz, lt_of_le_of_lt (mem_closedBall.1 hu) (hrr₀.trans hr₀ρ)⟩
  have hDBu : ∀ u ∈ closedBall z r, DifferentiableAt ℂ Φ u ∧ ‖deriv Φ u‖ ≤ C := fun u hu =>
    ⟨(hDB Φ hcl z hz u (closedBall_subset_closedBall hrr₀.le hu)).1,
      (hDB Φ hcl z hz u (closedBall_subset_closedBall hrr₀.le hu)).2.1⟩
  have hLip : ∀ u ∈ closedBall z r, ‖Φ u - Φ z‖ ≤ C * r := fun u hu => by
    have := (convex_closedBall z r).norm_image_sub_le_of_norm_deriv_le (fun v hv => (hDBu v hv).1)
      (fun v hv => (hDBu v hv).2) (mem_closedBall_self hr.le) hu
    exact this.trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact mem_closedBall.1 hu)
      hC.le)
  obtain ⟨hpM, hpρ⟩ : ‖Φ z‖ ≤ M ∧ ρ ≤ (Φ z).im :=
    hcl.2.2.1 z (self_subset_thickening hρ _ hz)
  -- the pushed measure
  set ν := (foldedCircle z r).map Φ with hνdef
  have hΦm : Measurable Φ := (measurable_const_mul _).comp hψm
  haveI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hΦm.aemeasurable).2
    inferInstance
  have hzH : z ∈ Hbar := show (0 : ℝ) ≤ z.im by linarith [hz.2.1]
  set K := Φ '' closedBall z r with hKdef
  have hΦc : ContinuousOn Φ (closedBall z r) := fun u hu =>
    (hDBu u hu).1.continuousAt.continuousWithinAt
  have hK : IsCompact K := (isCompact_closedBall z r).image_of_continuousOn hΦc
  have hνK : ∀ᵐ u ∂ν, u ∈ K :=
    (ae_map_iff hΦm.aemeasurable hK.isClosed.measurableSet).2
      ((ae_fc_mem_closedBall hzH hr.le).mono fun u hu => mem_image_of_mem _ hu)
  have hKc : K ⊆ {u : ℂ | c₀ ≤ u.im} := by
    rintro _ ⟨u, hu, rfl⟩
    have := (hcl.2.2.1 u (hzthk u hu)).2
    show c₀ ≤ (Φ u).im
    linarith
  -- the round circle
  set p := Φ z with hpdef
  set ρ' := r * ‖deriv Φ z‖ with hρ'def
  have hdz : 0 < ‖deriv Φ z‖ := lt_of_lt_of_le hm (hcl.2.2.2 z hz)
  have hρ' : 0 < ρ' := mul_pos hr hdz
  have hρ'C : ρ' ≤ r * C := mul_le_mul_of_nonneg_left (hDBu z (mem_closedBall_self hr.le)).2 hr.le
  have hpim : c₀ + ρ' ≤ p.im := by linarith
  -- the three identities
  have hy := evalReg_y_eq hgood hraw hA hW hψm hs hρ₀ hδ hU hRC3 hr hrρ₀
    (closedBall_subset_closedBall (by linarith) |>.trans (hRU z hz))
  have hsplit := evalReg_wedge_split (Q := Qc γ) hgood hraw hA hc₀ hK hKc hνK (hkL α hα z hz)
  have hround := evalReg_wedge_fc (Q := Qc γ) hgood hraw hA hc₀ hρ' hpim
  have hpH : p ∈ Hbar := show (0 : ℝ) ≤ p.im by linarith
  have hFx : F (p, ρ') = evalReg x0 (foldedCircle p ρ') :=
    (hgood.1.evalReg_fc_of_mem hpH hρ').symm
  -- the profile terms
  have hgν : |∫ u, g u ∂ν - g p| ≤ η / 6 := by
    refine abs_integral_sub_le hg hK hνK fun v hv => ?_
    obtain ⟨u, hu, rfl⟩ := hv
    have h1 := hLip u hu
    have hpb : p ∈ closedBall (0 : ℂ) (|M| + 1) := mem_closedBall_zero_iff.2
      (hpM.trans (by linarith [le_abs_self M]))
    have hvb : Φ u ∈ closedBall (0 : ℂ) (|M| + 1) := by
      rw [mem_closedBall_zero_iff]
      calc ‖Φ u‖ ≤ ‖p‖ + ‖Φ u - p‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ |M| + 1 := by linarith [le_abs_self M, mul_comm C r]
    have hd : dist (Φ u) p < εg := by
      rw [dist_eq_norm]; linarith [mul_comm C r]
    exact (le_of_lt (hUC _ hvb _ hpb hd))
  have hgρ : |∫ u, g u ∂foldedCircle p ρ' - g p| ≤ η / 6 := by
    refine abs_integral_sub_le hg (isCompact_closedBall p ρ') (ae_fc_mem_closedBall hpH hρ'.le)
      fun v hv => ?_
    have hdv := mem_closedBall.1 hv
    have hpb : p ∈ closedBall (0 : ℂ) (|M| + 1) := mem_closedBall_zero_iff.2
      (hpM.trans (by linarith [le_abs_self M]))
    have hvb : v ∈ closedBall (0 : ℂ) (|M| + 1) := by
      rw [mem_closedBall_zero_iff]
      calc ‖v‖ ≤ ‖p‖ + dist v p := by rw [dist_eq_norm]; exact norm_le_norm_add_norm_sub' _ _
        _ ≤ |M| + 1 := by linarith [le_abs_self M]
    exact le_of_lt (hUC _ hvb _ hpb (by linarith))
  -- assembly
  have hX := hkX α hα z hz
  have hL := hlog Φ hcl z hz r hr hr2
  unfold pushErrR
  rw [hy]
  show |evalReg w ν + Qc γ * ∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r -
      Qc γ * Real.log ‖deriv Φ z‖ - evalReg w (foldedCircle p ρ')| ≤ η
  rw [hsplit, hround, hFx]
  have hQ : |Qc γ * (∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r - Real.log ‖deriv Φ z‖)| ≤
      η / 3 := by
    rw [abs_mul]
    calc |Qc γ| * |∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r - Real.log ‖deriv Φ z‖|
        ≤ (|Qc γ| + 1) * (η / (3 * (|Qc γ| + 1))) :=
          mul_le_mul (by linarith) hL (abs_nonneg _) (by positivity)
      _ = η / 3 := by field_simp
  have e : evalReg x0 ν + ∫ u, g u ∂ν + Qc γ * ∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r -
      Qc γ * Real.log ‖deriv Φ z‖ - (evalReg x0 (foldedCircle p ρ') + ∫ u, g u ∂foldedCircle p ρ') =
      (evalReg x0 ν - evalReg x0 (foldedCircle p ρ')) +
        ((∫ u, g u ∂ν - g p) - (∫ u, g u ∂foldedCircle p ρ' - g p)) +
        Qc γ * (∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r - Real.log ‖deriv Φ z‖) := by ring
  rw [e]
  have hX' : |evalReg x0 ν - evalReg x0 (foldedCircle p ρ')| ≤ η / 3 := hX
  have t1 := abs_add_le (evalReg x0 ν - evalReg x0 (foldedCircle p ρ') +
      ((∫ u, g u ∂ν - g p) - (∫ u, g u ∂foldedCircle p ρ' - g p)))
    (Qc γ * (∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r - Real.log ‖deriv Φ z‖))
  have t2 := abs_add_le (evalReg x0 ν - evalReg x0 (foldedCircle p ρ'))
    ((∫ u, g u ∂ν - g p) - (∫ u, g u ∂foldedCircle p ρ' - g p))
  have t3 := abs_sub (∫ u, g u ∂ν - g p) (∫ u, g u ∂foldedCircle p ρ' - g p)
  calc _ ≤ |evalReg x0 ν - evalReg x0 (foldedCircle p ρ')| +
        (|∫ u, g u ∂ν - g p| + |∫ u, g u ∂foldedCircle p ρ' - g p|) +
        |Qc γ * (∫ u, Real.log ‖deriv Φ u‖ ∂foldedCircle z r - Real.log ‖deriv Φ z‖)| := by
        linarith
    _ ≤ η / 3 + (η / 6 + η / 6) + η / 3 := by gcongr
    _ = η := by ring

end G1Side
end QuantumZipper
