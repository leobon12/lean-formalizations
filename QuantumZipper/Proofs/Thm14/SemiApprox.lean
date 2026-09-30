import QuantumZipper.Proofs.Thm14.SemiApproxConv
import QuantumZipper.Proofs.Thm14.FcRPairFixed

/-!
# SEMI-APPROX, part 5: `SemiApproxExists`

For every real centre `c` and radius `s > 0`, the polar-product smoothings `saTF c s hs j`
(`SemiApproxDens`) satisfy `SemiApprox κ T c s` (`semiApprox_saTF`), hence
`semiApproxExists : SemiApproxExists`, and with `fcRPairingLimit_of_semiApprox`,
`fcRPairingLimit : FcRPairingLimit`.

The energy field: `kernelCov2` of the pair `(Ψ_j', σ')` expands into four kernel covariances of
parametrized measures `(saM.withDensity w).map (f ∘ Γ_e)` (`tdens_saPsi`, `fc_eq_saM`), each
converging to `kernelCov neumannH σ' σ'` by `sa_kernelCov_tendsto`. The deterministic field:
`sa_integral_tendsto`. Own elementary argument (see `handoff/FCR-PAIR.md`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

open CharFun

theorem saEps_tendsto (s : ℝ) : Tendsto (saEps s) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => 4 * ((j : ℝ) + 1)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num)
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact (tendsto_const_nhds (x := s)).div_atTop h

theorem abs_saEps_le {s : ℝ} (hs : 0 < s) (j : ℕ) : |saEps s j| ≤ s / 4 := by
  rw [abs_of_pos (saEps_pos hs j)]; exact saEps_le hs j

/-- **The semicircle smoothings satisfy `SemiApprox`.** -/
theorem semiApprox_saTF (κ : ℝ) {T : ℝ} (hT : 0 < T) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    SemiApprox κ T (c : ℂ) s (saTF c s hs) := by
  obtain ⟨M1, hM1, hW1⟩ := saW_le
  obtain ⟨M2, hM2, hW2⟩ := saWinf_le
  have hM0 : 0 ≤ max M1 M2 := hM1.trans (le_max_left _ _)
  have hMa : ∀ j p, (saW j p : ℝ) ≤ max M1 M2 := fun j p => (hW1 j p).trans (le_max_left _ _)
  have hMb : ∀ (_ : ℕ) p, (saWinf p : ℝ) ≤ max M1 M2 := fun _ p =>
    (hW2 p).trans (le_max_right _ _)
  have he := abs_saEps_le hs
  have he0 : ∀ _ : ℕ, |(0 : ℝ)| ≤ s / 4 := fun _ => sa_abs_zero_le hs
  have hl := saEps_tendsto s
  have hl0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hcA : ∀ p : ℝ × ℝ, p ∈ saBox → Tendsto (fun j => saW j p) atTop (𝓝 (saWinf p)) :=
    fun p hp => saW_tendsto hp.2
  have hcB : ∀ p : ℝ × ℝ, p ∈ saBox → Tendsto (fun _ : ℕ => saWinf p) atTop (𝓝 (saWinf p)) :=
    fun _ _ => tendsto_const_nhds
  refine ⟨fun j z => saPsi_nonneg c s hs j z, fun j => integral_saPsi c s hs j, ?_, ?_⟩
  · intro W hW
    have hfm := TwoPoint.measurable_revMap hW hT.le
    have hA : ∀ j, (tdens (saTF c s hs j).1).map (revMap W T) =
        (saM.withDensity fun p => (saW j p : ℝ≥0∞)).map (revMap W T ∘ saGam c s (saEps s j)) :=
      fun j => by
        show (tdens (saPsi c s j)).map _ = _
        rw [tdens_saPsi c s hs j, Measure.map_map hfm (continuous_saGam _ _ _).measurable]
    have hB : (foldedCircle (c : ℂ) s).map (revMap W T) =
        (saM.withDensity fun p => (saWinf p : ℝ≥0∞)).map (revMap W T ∘ saGam c s 0) := by
      rw [fc_eq_saM c hs.le, Measure.map_map hfm (continuous_saGam _ _ _).measurable]
    simp only [kernelCov2]
    simp_rw [hA, hB]
    have t1 := sa_kernelCov_tendsto hW hT.le c hs he he hl hl measurable_saW measurable_saW
      measurable_saWinf measurable_saWinf hM0 hMa hMa hcA hcA
    have t2 := sa_kernelCov_tendsto hW hT.le c hs he he0 hl hl0 (w₂ := fun _ => saWinf)
      measurable_saW (fun _ => measurable_saWinf) measurable_saWinf measurable_saWinf hM0 hMa hMb
      hcA hcB
    have t3 := sa_kernelCov_tendsto hW hT.le c hs he0 he hl0 hl (w₁ := fun _ => saWinf)
      (fun _ => measurable_saWinf) measurable_saW measurable_saWinf measurable_saWinf hM0 hMb hMa
      hcB hcA
    have := ((t1.sub t2).sub t3).add (tendsto_const_nhds (x := kernelCov neumannH
      ((saM.withDensity fun p => (saWinf p : ℝ≥0∞)).map (revMap W T ∘ saGam c s 0))
      ((saM.withDensity fun p => (saWinf p : ℝ≥0∞)).map (revMap W T ∘ saGam c s 0))))
    rw [sub_self, zero_sub, neg_add_cancel] at this
    exact this
  · intro W hW
    have hhm := TReg.measurable_hTrev κ hW hT.le
    have hint : ∀ (w : ℝ × ℝ → ℝ≥0), Measurable w → ∀ e : ℝ,
        ∫ z, hTrev κ W T z ∂((saM.withDensity fun p => (w p : ℝ≥0∞)).map (saGam c s e)) =
          ∫ p, (w p : ℝ) * hTrev κ W T (saGam c s e p) ∂saM := by
      intro w hw e
      rw [integral_map (continuous_saGam _ _ _).aemeasurable hhm.aestronglyMeasurable,
        integral_withDensity_eq_integral_smul hw]
      simp only [NNReal.smul_def, smul_eq_mul]
    have hψ : ∀ j, ∫ z, (saTF c s hs j).1 z * hTrev κ W T z =
        ∫ z, hTrev κ W T z ∂(tdens (saPsi c s j)) := by
      intro j
      show ∫ z, saPsi c s j z * _ = _
      unfold CharFun.tdens
      have : (fun z => ENNReal.ofReal (saPsi c s j z)) =
          fun z => ((Real.toNNReal (saPsi c s j z) : ℝ≥0) : ℝ≥0∞) := rfl
      rw [this, integral_withDensity_eq_integral_smul (show Measurable fun z =>
        Real.toNNReal (saPsi c s j z) from measurable_real_toNNReal.comp
        (saPsi_contDiff c s hs j).continuous.measurable)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [Function.comp_apply, NNReal.smul_def, smul_eq_mul,
        Real.coe_toNNReal _ (saPsi_nonneg c s hs j z)]
    simp_rw [hψ, tdens_saPsi c s hs, hint _ (measurable_saW _)]
    rw [fc_eq_saM c hs.le, hint _ measurable_saWinf]
    exact sa_integral_tendsto κ hW hT.le c hs he hl measurable_saW hM0 hMa hcA

/-- **`SemiApproxExists` holds.** -/
theorem semiApproxExists : SemiApproxExists := fun κ T _ hT c s hs =>
  ⟨saTF c s hs, semiApprox_saTF κ hT c hs⟩

/-- **`FcRPairingLimit` holds** (the last analytic input of Theorem 1.4(b)). -/
theorem fcRPairingLimit : FcRPairingLimit := fcRPairingLimit_of_semiApprox semiApproxExists

end Thm14WDG
end QuantumZipper
