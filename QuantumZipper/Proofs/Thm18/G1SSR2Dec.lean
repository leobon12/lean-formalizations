import QuantumZipper.Proofs.Thm18.G1SSR2Prof
import QuantumZipper.Proofs.Thm18.G1RCProfile
import QuantumZipper.Proofs.Thm18.G1ProfileGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (6): circle values of the rescaled wedge field at circles centred in `ℍ`

Theorem 1.8, G1 zoom, toward `G1SidePushUCRepStmt`. For a good free sample `x` with witness `F`,
a continuous radial path `A` and `S > 0`, the rescaled wedge field
`y = rescale (wedgeField (lateralPart x) A Q) Q S` has, at every folded circle `fc(v, σ)` with
`v ∈ ℍ`, `σ > 0`,
`evalReg y fc(v, σ) = F(S v, S σ) + smoothFun (rp g) (S v) (S σ) + Q log S`
(`evalReg_rescale_wedge_fc`), `g = wg x A Q` the wedge profile. Proof: the regularized averages
(`G1RC.avgReg_rescale_wedge`, off the dyadic circles about `0`, which `fc(v, σ)` does not charge
for large `k`, `G1RC.eventually_ae_norm_ne_radius`), the smoothing limit of the free witness, and
for the profile the exchange of folded-circle means (`G1RC.LogBd.integral_swap`) and continuity.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1SSR2

open F1.RC3Two G1RC

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {C : ℝ}

theorem evalReg_rescale_wedge_fc (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S)
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t))
    {v : ℂ} (hv : v ∈ H) {σ : ℝ} (hσ : 0 < σ) :
    evalReg (rescale (wedgeField (lateralPart x) A Q) Q S) (foldedCircle v σ) =
      F ((S : ℂ) * v, S * σ) + GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * v) (S * σ) +
        Q * Real.log S := by
  set g := wg x A Q with hgdef
  have hgm : Measurable g := measurable_wg h.cont
  have hgc : ContinuousOn g (Ioi 0) := continuousOn_wg h.good h.cont
  have hF := h.good.1
  have hSσ : 0 < S * σ := mul_pos hS hσ
  have hmS : Measurable fun w : ℂ => (S : ℂ) * w := measurable_const_mul _
  have hSv : (S : ℂ) * v ∈ H := G1.mul_mem_H hS hv
  have hSvb : (S : ℂ) * v ∈ Hbar := H_subset_Hbar hSv
  -- the gap
  have hgap : ∀ᶠ k : ℕ in atTop, ∀ᵐ w ∂foldedCircle v σ, ‖w‖ ≠ radius k := by
    have := eventually_ae_norm_ne_radius (ψ := id) measurable_id differentiableOn_id v hσ
    simpa only [Measure.map_id] using this
  -- the two parts, integrable
  have hFint : ∀ k : ℕ, Integrable (fun w => F ((S : ℂ) * w, S * radius k)) (foldedCircle v σ) :=
    fun k => RegClosure.integrable_fc (hF.1.comp ((continuousOn_const.mul continuousOn_id).prodMk
      continuousOn_const) fun w hw => ⟨RegClosure.mapsTo_mul_pos hS hw,
        show (0 : ℝ) < S * radius k from mul_pos hS (radius_pos k)⟩) v hσ.le
  have hPint : ∀ k : ℕ, Integrable (fun w => GoodSample.smoothFun (rp g) ((S : ℂ) * w)
      (S * radius k)) (foldedCircle v σ) := fun k =>
    RegClosure.integrable_fc ((continuous_smoothFun_rp hgm hgc hbd
      (mul_pos hS (radius_pos k))).comp (continuous_const.mul continuous_id)).continuousOn v hσ.le
  have hsum : ∀ᶠ k : ℕ in atTop, ∫ w, avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k w
      ∂foldedCircle v σ = ∫ w, F ((S : ℂ) * w, S * radius k) ∂foldedCircle v σ +
        ∫ w, GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k) ∂foldedCircle v σ +
        Q * Real.log S := by
    filter_upwards [hgap] with k hk
    have e : ∫ w, avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k w ∂foldedCircle v σ =
        ∫ w, (F ((S : ℂ) * w, S * radius k) +
          GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k) + Q * Real.log S)
          ∂foldedCircle v σ := by
      refine integral_congr_ae ?_
      filter_upwards [hk, TwoPoint.foldedCircle_ae_mem_H v hσ] with w hw hwH
      rw [avgReg_rescale_wedge h Q hS (H_subset_Hbar hwH) hw]
      rfl
    rw [e, integral_add (f := fun w => F ((S : ℂ) * w, S * radius k) +
        GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k))
        (g := fun _ => Q * Real.log S) ((hFint k).add (hPint k)) (integrable_const _),
      integral_add (f := fun w => F ((S : ℂ) * w, S * radius k))
        (g := fun w => GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k))
        (hFint k) (hPint k), integral_const]
    simp
  -- limit of the free part
  have hρ : Tendsto (fun k : ℕ => S * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hS (radius_pos k)⟩
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul S
  have hmapfc : (foldedCircle v σ).map (fun w => (S : ℂ) * w) =
      foldedCircle ((S : ℂ) * v) (S * σ) := WedgeTK.fc_map_mul v σ hS
  have hA1 : Tendsto (fun k : ℕ => ∫ w, F ((S : ℂ) * w, S * radius k) ∂foldedCircle v σ) atTop
      (𝓝 (F ((S : ℂ) * v, S * σ))) := by
    have ht := (hF.2.2.tendsto_at (show ((S : ℂ) * v, S * σ) ∈ Hbar ×ˢ Ioi 0 from
      ⟨hSvb, hSσ⟩)).comp hρ
    refine ht.congr fun k => ?_
    simp only [Function.comp]
    rw [← hmapfc, integral_map hmS.aemeasurable]
    exact (hF.1.comp (continuous_id.prodMk continuous_const).continuousOn fun u hu =>
      ⟨hu, show (0 : ℝ) < S * radius k from mul_pos hS (radius_pos k)⟩).aestronglyMeasurable
        isClosed_Hbar.measurableSet |>.mono_measure (by
          rw [hmapfc]
          exact (Measure.restrict_eq_self_of_ae_mem (by
            filter_upwards [TwoPoint.foldedCircle_ae_mem_H ((S : ℂ) * v) hSσ] with u hu
            exact H_subset_Hbar hu)).ge)
  -- limit of the profile part
  have hL := logBd_rp hgm hgc hbd
  set Φ : ℂ → ℝ := fun u => GoodSample.smoothFun (rp g) u (S * σ) with hΦ
  have hΦc : Continuous Φ := continuous_smoothFun_rp hgm hgc hbd hSσ
  have hA2 : Tendsto (fun k : ℕ => ∫ w, GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k)
      ∂foldedCircle v σ) atTop (𝓝 (GoodSample.smoothFun (rp g) ((S : ℂ) * v) (S * σ))) := by
    have hcont := RegClosure.continuousOn_integral_fc_fun hΦc.continuousOn
    have h0 : Tendsto (fun k : ℕ => ((S : ℂ) * v, S * radius k)) atTop
        (𝓝 ((S : ℂ) * v, (0 : ℝ))) :=
      tendsto_const_nhds.prodMk_nhds (hρ.mono_right nhdsWithin_le_nhds)
    have ht := ((hcont _ (mem_univ _)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall fun _ => mem_univ _⟩))
    have hv0 : ∫ u, Φ u ∂foldedCircle ((S : ℂ) * v) 0 = Φ ((S : ℂ) * v) := by
      rw [RegSample.fc_zero, integral_dirac, CircleFubini.foldH_of_mem' hSvb]
    rw [hv0] at ht
    refine ht.congr fun k => ?_
    simp only [Function.comp, hΦ]
    have e1 : ∫ w, GoodSample.smoothFun (rp g) ((S : ℂ) * w) (S * radius k) ∂foldedCircle v σ =
        ∫ u, GoodSample.smoothFun (rp g) u (S * radius k) ∂foldedCircle ((S : ℂ) * v) (S * σ) := by
      rw [← hmapfc, integral_map hmS.aemeasurable ((continuous_smoothFun_rp hgm hgc hbd
        (mul_pos hS (radius_pos k))).aestronglyMeasurable)]
    rw [e1]
    simp only [GoodSample.smoothFun]
    exact (hL.integral_swap _ hSσ (mul_pos hS (radius_pos k))).symm
  have hlim := ((hA1.add hA2).add_const (Q * Real.log S)).congr' (hsum.mono fun k hk => hk.symm)
  exact hlim.limUnder_eq

end G1SSR2
end Thm18Asm
end QuantumZipper
