import QuantumZipper.Proofs.Thm18.G1Side3Cont
import QuantumZipper.Proofs.Zipper.AreaWinDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (12): the area limit of the pulled-back canonical field on one rectangle, per sample

For one sample, `x = coordChange (rescale w Q s) ψ Q` (canonical wedge field pulled back by the
side map) and a rational rectangle `R ⊂ ℍ` on which `Φ = s ψ` is in an area class: along all
radii `α 2^{-k}` (`goodFilter`),

  `∫ f d(areaR γ x (α 2^{-k})) → ∫ pullTest Φ R f dμ_w`

for every test function supported in the interior of `R` (`tendsto_area_rect`). This is
Sheffield–Wang's area transport along all radii (`SWCore.a9_tendsto_goodFilter`, arXiv:1605.06171
proof of Thm 1.4) for the unscaled wedge field `w` (window limits: `WedgeWindowStmt`) and the map
`Φ`, with the distortion input `G1Side.pushErrR_small`; the approximations of `x` and of
`coordChange w Φ Q` agree on the circles inside `R` (`G1Side.evalReg_y_eq`,
`G1Side.raw_rescale_eq`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open SWCore

/-- Area approximations agree on test functions whose support sees equal densities. -/
theorem integral_areaR_congr {γ : ℝ} {x x' : FieldSample} {r : ℝ} {f : ℂ → ℝ}
    (h : ∀ z ∈ tsupport f, areaDens γ x r z = areaDens γ x' r z) :
    ∫ z, f z ∂areaR γ x r = ∫ z, f z ∂areaR γ x' r := by
  set T := tsupport f
  have hTm : MeasurableSet T := (isClosed_tsupport f).measurableSet
  have hz : ∀ z, z ∉ T → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have e1 : ∫ z, f z ∂areaR γ x r = ∫ z in T, f z ∂areaR γ x r :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
  have e2 : ∫ z, f z ∂areaR γ x' r = ∫ z in T, f z ∂areaR γ x' r :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
  rw [e1, e2]
  unfold areaR
  rw [restrict_withDensity hTm, restrict_withDensity hTm]
  have hae : (fun z => ENNReal.ofReal (areaDens γ x r z)) =ᵐ[(volume.restrict H).restrict T]
      fun z => ENNReal.ofReal (areaDens γ x' r z) :=
    (ae_restrict_mem hTm).mono fun z hz => by simp only [h z hz]
  rw [withDensity_congr_ae hae]

theorem tendsto_goodRad_zero : Tendsto goodRad goodFilter (𝓝 0) := by
  unfold goodFilter goodRad
  have h1 : Tendsto (fun i : ℕ × ℝ => radius i.1) (atTop ×ˢ 𝓟 (Icc 1 2)) (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp tendsto_fst
  refine squeeze_zero_norm' ?_ (by simpa using h1.const_mul 2)
  filter_upwards [prod_mem_prod univ_mem (mem_principal_self _)] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [hi.2.1]) (radius_pos _).le)]
  exact mul_le_mul_of_nonneg_right hi.2.2 (radius_pos _).le

theorem goodRad_pos_eventually : ∀ᶠ i in goodFilter, 0 < goodRad i := by
  unfold goodFilter
  filter_upwards [prod_mem_prod univ_mem (mem_principal_self _)] with i hi
  exact mul_pos (by linarith [hi.2.1]) (radius_pos _)

variable {x0 : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {ψ : ℂ → ℂ} {s : ℝ}

set_option maxHeartbeats 800000 in
/-- **Area limit on one rectangle, per sample.** -/
theorem tendsto_area_rect {γ : ℝ} (hγ : 0 < γ) (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    (hA : Continuous A) (hWg : IsLQGGood γ (wedgeField (lateralPart x0) A (Qc γ)))
    {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1)) (hcw' : Tendsto cw' atTop (𝓝 1))
    (hWin : E6.WindowLimits γ (wedgeField (lateralPart x0) A (Qc γ)) cw cw')
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
    {a b c d ρ M m : ℚ} (hc : (0 : ℝ) < c) (hρ : (0 : ℝ) < ρ) (hm : (0 : ℝ) < m)
    (hcl : (fun u => (s : ℂ) * ψ u) ∈ AreaClass a b c d ρ M m)
    (hRU : ∀ z ∈ rectC a b c d, closedBall z (ρ₀ + δ) ⊆ U)
    (HL : ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      Tendsto (fun j => ∫ u, avgReg x0 j u
          ∂((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u)) atTop
        (𝓝 (evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u))))
    (HX : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ α ∈ Icc (1 : ℝ) 2, ∀ z ∈ rectC a b c d,
      |evalReg x0 ((foldedCircle z (α * radius k)).map fun u => (s : ℂ) * ψ u) -
        evalReg x0 (foldedCircle ((s : ℂ) * ψ z)
          (α * radius k * ‖deriv (fun u => (s : ℂ) * ψ u) z‖))| ≤ η)
    {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) :
    Tendsto (fun i => ∫ z, f z ∂areaR γ
        (coordChange (rescale (wedgeField (lateralPart x0) A (Qc γ)) (Qc γ) s) ψ (Qc γ))
        (goodRad i)) goodFilter
      (𝓝 (∫ v, pullTest (fun u => (s : ℂ) * ψ u) (rectC a b c d) f v
        ∂qAreaMeasure γ (wedgeField (lateralPart x0) A (Qc γ)))) := by
  set w := wedgeField (lateralPart x0) A (Qc γ) with hw
  have hW : IsRegularSample w := hWg.1
  have hErr := pushErrR_small hgood hraw hA hW hψm hs hρ₀ hδ hU hRC3 hc hρ hm hcl hRU HL HX
  have hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ w K < ⊤ := fun K hK hKH =>
    hWg.qAreaMeasure_spec.2.1 K hK hKH
  have h9 := a9_tendsto_goodFilter hγ hcw hcw' hWin hμK (fun N j => E6.measurable_supWin hW γ N j)
    (fun N j => E6.measurable_infWin hW γ N j) hc hρ hm hcl hErr hf hfs hfK
  refine h9.congr' ?_
  filter_upwards [goodRad_pos_eventually, tendsto_goodRad_zero.eventually (gt_mem_nhds hρ₀)]
    with i hi0 hiρ
  refine integral_areaR_congr fun z hz => ?_
  have hzR : z ∈ rectC a b c d := interior_subset (hfK hz)
  have hball : closedBall z (goodRad i + δ) ⊆ U :=
    (closedBall_subset_closedBall (by linarith)).trans (hRU z hzR)
  have hy := evalReg_y_eq hgood hraw hA hW hψm hs hρ₀ hδ hU hRC3 hi0 hiρ hball
  have hzU : z ∈ U := hball (mem_closedBall_self (by linarith))
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hU z hzU _ hi0 hiρ
  have hraw_eq := raw_rescale_eq hgood hraw hA hW hψm hi0 h1 h2 h3 h4 h5 hs h6
  have hzH : z ∈ Hbar := show (0 : ℝ) ≤ z.im by linarith
  unfold areaDens
  rw [hy, ← hraw_eq, hRC3 z hzH _ hi0]

end G1Side
end QuantumZipper
