import QuantumZipper.Proofs.Zipper.F1ReflLaw
import QuantumZipper.Proofs.Zipper.F1B4dBasic
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.Zipper.F1ReflReg
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.WedgeFinZeroCoupling

/-!
# B4(d): the pathwise input, reduced to two regularity statements

`WedgeReflPathStmt` (F1B4d) asks, a.s., `data (canonical W)(−·̄) = data (canonical Wσ)`. We split
it as `canonical Wσ = canonical (W(−·̄))` (from `RegEq Wσ (W(−·̄))`, open input
`WedgeLatReflRegStmt`) and the deterministic identity
`data ((canonical x)(−·̄)) = data (canonical (x(−·̄)))` for a good sample `x` with positive scale
whose circle-average pairings have continuum limits (`dataH_reflectH_canonical`). The latter is
exactly the point that the regularized pairings of `(canonical x)(−·̄)` are limits along the radii
`b·2^{-k}` (`b = scaleParam γ x`) while those of `canonical (x(−·̄))` are limits along `2^{-k}`;
the continuum-limit hypothesis `ContPair` identifies them (open input `WedgeContPairStmt`).

Own elementary arguments.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace F1
namespace B4d

variable {x : FieldSample} {F : ℂ × ℝ → ℝ}

theorem foldH_neg_conj (c : ℂ) : foldH (-conj c) = -conj (foldH c) := by
  unfold foldH
  by_cases h : 0 ≤ c.im
  · have h' : 0 ≤ (-conj c).im := by simpa using h
    rw [if_pos h, if_pos h']
  · have h' : ¬ 0 ≤ (-conj c).im := by simpa using h
    rw [if_neg h, if_neg h']
    simp

theorem neg_conj_mul (b : ℝ) (u : ℂ) : -conj ((b : ℂ) * u) = (b : ℂ) * -conj u := by
  simp [map_mul, Complex.conj_ofReal]

theorem tendsto_mul_radius {b : ℝ} (hb : 0 < b) :
    Tendsto (fun k => b * radius k) atTop (𝓝[>] 0) := by
  have h0 : Tendsto (fun k => b * radius k) atTop (𝓝 0) := by
    simpa using (tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT).const_mul b
  exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0
    (Eventually.of_forall fun k => mul_pos hb (radius_pos k))

/-! ## 1. Circle coordinates -/

theorem reflectH_rescale_fc (h : IsRegularWith x F) (Q : ℝ) {b : ℝ} (hb : 0 < b) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    RegClosure.reflectH (rescale x Q b) (foldedCircle c r) =
      rescale (RegClosure.reflectH x) Q b (foldedCircle c r) := by
  rw [RegClosure.rescale_fc_eq h.reflectH' Q hb c hr]
  show evalReg (rescale x Q b) ((foldedCircle c r).map fun z => -conj z) = _
  rw [fc_map_negConj, (h.rescale' Q hb).evalReg_fc _ hr]
  simp only [RegClosure.foldH_mul_pos _ hb, foldH_neg_conj, neg_conj_mul]

/-! ## 2. Test pairings (the continuum-limit point) -/

theorem reflectH_rescale_eq_of_lim (h : IsRegularWith x F) (Q : ℝ) {b : ℝ} (hb : 0 < b)
    (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar)
    (hνK : ∀ᵐ u ∂ν, u ∈ K) {L : ℝ}
    (hlim : Tendsto (fun r => ∫ u, F ((b : ℂ) * -conj u, r) ∂ν) (𝓝[>] 0) (𝓝 L)) :
    RegClosure.reflectH (rescale x Q b) ν = rescale (RegClosure.reflectH x) Q b ν := by
  have hνH : ∀ᵐ u ∂ν, u ∈ Hbar := hνK.mono fun u hu => hKH hu
  have hint : ∀ r, 0 < r → Integrable (fun u => F ((b : ℂ) * -conj u, r)) ν := by
    intro r hr
    have hcont : ContinuousOn (fun u => F ((b : ℂ) * -conj u, r)) Hbar :=
      h.1.comp (by fun_prop) (fun u hu =>
        ⟨RegClosure.mapsTo_mul_pos hb (RegClosure.mapsTo_neg_conj hu), hr⟩)
    have := (hcont.mono hKH).integrableOn_compact (μ := ν) hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hνK] at this
  have hL : RegClosure.reflectH (rescale x Q b) ν = L + Q * Real.log b * ν.real univ := by
    refine (h.rescale' Q hb).evalReg_map_eq (m := fun z => -conj z) (by fun_prop)
      RegClosure.mapsTo_neg_conj hνH
      (G := fun k => ∫ u, F ((b : ℂ) * -conj u, b * radius k) ∂ν + Q * Real.log b * ν.real univ)
      (fun k => ?_) ((hlim.comp (tendsto_mul_radius hb)).add_const _)
    show ∫ u, (F ((b : ℂ) * -conj u, b * radius k) + Q * Real.log b) ∂ν = _
    rw [integral_add (hint _ (mul_pos hb (radius_pos k))) (integrable_const _), integral_const,
      smul_eq_mul, mul_comm (ν.real univ)]
  have hR : rescale (RegClosure.reflectH x) Q b ν = L + Q * Real.log b * ν.real univ := by
    unfold rescale coordChange
    have hd : ∀ z, Real.log ‖deriv (fun w : ℂ => (b : ℂ) * w) z‖ = Real.log b := fun z => by
      rw [WedgeMeas.deriv_mul_left', Complex.norm_real, Real.norm_of_nonneg hb.le]
    rw [integral_congr_ae (ae_of_all _ hd), integral_const, smul_eq_mul,
      h.reflectH'.evalReg_map_eq (m := fun z => (b : ℂ) * z) (by fun_prop)
        (RegClosure.mapsTo_mul_pos hb) hνH
        (G := fun k => ∫ u, F ((b : ℂ) * -conj u, radius k) ∂ν)
        (fun k => by
          show ∫ u, F (-conj ((b : ℂ) * u), radius k) ∂ν = _
          simp only [neg_conj_mul])
        (hlim.comp RegClosure.tendsto_radius_nhdsGT)]
    ring
  rw [hL, hR]

theorem H_subset_Hbar : H ⊆ Hbar := fun z (hz : 0 < z.im) => show 0 ≤ z.im from hz.le

/-- The density measure `f⁺ dz` of a continuous compactly supported `f` is finite and lives on
`tsupport f`. -/
theorem withDensity_facts {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    IsFiniteMeasure (volume.withDensity fun z => ENNReal.ofReal (f z)) ∧
      ∀ᵐ u ∂(volume.withDensity fun z => ENNReal.ofReal (f z)), u ∈ tsupport f := by
  refine ⟨isFiniteMeasure_withDensity_ofReal
    (hf.integrable_of_hasCompactSupport hfs).hasFiniteIntegral, ?_⟩
  rw [ae_iff]
  have e : {u | ¬ u ∈ tsupport f} = (tsupport f)ᶜ := rfl
  rw [e, withDensity_apply _ (isClosed_tsupport f).measurableSet.compl]
  refine le_antisymm ?_ (by simp)
  calc ∫⁻ a in (tsupport f)ᶜ, ENNReal.ofReal (f a) = ∫⁻ _ in (tsupport f)ᶜ, 0 :=
        setLIntegral_congr_fun (isClosed_tsupport f).measurableSet.compl fun u hu => by
          rw [image_eq_zero_of_notMem_tsupport hu, ENNReal.ofReal_zero]
    _ ≤ 0 := by simp

/-! ## 3. The deterministic identity -/

theorem scaleParam_reflectH {γ : ℝ} (hx : IsLQGGood γ x) :
    scaleParam γ (RegClosure.reflectH x) = scaleParam γ x := by
  unfold scaleParam
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  rw [GoodTransforms.qAreaMeasure_reflectH hx, Measure.map_apply (by fun_prop)
    (measurableSet_ball.inter (isOpen_H.measurableSet))]
  have e : (fun z : ℂ => -conj z) ⁻¹' (Metric.ball 0 a ∩ H) = Metric.ball 0 a ∩ H := by
    ext z
    simp [H, Metric.mem_ball, dist_zero_right]
  rw [e]

end B4d

/-! ## 4. The wedge-level reduction -/

/-- **Open input (i) of B4(d)**: the wedge field built from the reflected GFF agrees, after
regularization, with the reflection of the wedge field (the radial part of `X` is reflection
invariant and `lateralPart` commutes with the reflection). -/
def WedgeLatReflRegStmt (γ α : ℝ) : Prop :=
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', avgReg (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) (Qc γ)) =
      avgReg (RegClosure.reflectH (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))

end F1
end QuantumZipper
