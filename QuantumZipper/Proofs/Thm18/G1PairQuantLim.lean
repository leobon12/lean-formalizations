import QuantumZipper.Proofs.Thm18.G1PairQuantDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PAIR-QUANT (3): PAIR-LIM for every test function from the countable certificate

For a regular sample `x` satisfying the countable certificate `CountCond x`, PAIR-LIM holds for
every scale `c > 0` and every test function (`pairLimAll_of_count`). The scale is removed by the
change of variables `v = c u` (`MeasureTheory.Measure.integral_comp_smul`): the pairing with the
Lipschitz function `f = max(±ρ, 0)` at scale `c` is a constant multiple of the pairing at scale
`1` with `f(c⁻¹ ·)`, which is Lipschitz and vanishes off the compact `c · tsupport ρ ⊆ H`; then
`lipBound_of_count` and the oscillation criterion give the limit. Integrability at each radius is
continuity on a compact set.

Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

/-- **PAIR-LIM for all scales and test functions from the countable certificate.** -/
theorem pairLimAll_of_count {x : FieldSample} (hreg : IsRegularSample x) (hc : CountCond x) :
    PairLimAll x := by
  obtain ⟨F, hFx⟩ := hreg
  have hF := hFx.1
  intro c hc0 ρ σ hσ
  obtain ⟨hs, hcs, hH⟩ := ρ.2
  set K := tsupport ρ.1 with hKdef
  have hK : IsCompact K := hcs
  have hσK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧ HasCompactSupport σ ∧
      ∀ z ∉ K, σ z = 0 := by
    rcases hσ with rfl | rfl
    · exact ⟨hs, hcs, fun z hz => image_eq_zero_of_notMem_tsupport hz⟩
    · exact ⟨hs.neg, hcs.neg, fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]⟩
  obtain ⟨hσs, hσc, hσ0⟩ := hσK
  obtain ⟨Lσ, hLσ⟩ := hσs.lipschitzWith_of_hasCompactSupport hσc (by simp)
  set f : ℂ → ℝ := fun z => max (σ z) 0 with hfdef
  have hf : LipschitzWith Lσ f := hLσ.max_const 0
  have hf0 : ∀ z ∉ K, f z = 0 := fun z hz => by simp [hfdef, hσ0 z hz]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hemb : MeasurableEmbedding (fun z : ℂ => (c : ℂ) * z) :=
    (Homeomorph.mulLeft₀ (c : ℂ) hc').toMeasurableEquiv.measurableEmbedding
  have hcu : ∀ u ∈ K, (c : ℂ) * u ∈ Hbar := fun u hu => by
    have h1 : 0 < u.im := hH hu
    show (0 : ℝ) ≤ ((c : ℂ) * u).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  -- the pairing at scale `c`, as an `F`-integral
  have hpair : ∀ s : ℝ, 0 < s → ∫ u, evalReg x (foldedCircle u s)
      ∂((G1.tmeas σ).map fun z => (c : ℂ) * z) = ∫ u, F ((c : ℂ) * u, s) * f u := by
    intro s hs0
    rw [hemb.integral_map]
    show ∫ u, evalReg x (foldedCircle ((c : ℂ) * u) s)
      ∂(volume.withDensity fun z => ENNReal.ofReal (σ z)) = _
    rw [D3Plus.integral_withDensity_ofReal_eq hσs.continuous]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    by_cases hu : u ∈ K
    · simp only [hfdef]; rw [hFx.evalReg_fc_of_mem (hcu u hu) hs0]
    · simp [hfdef, hσ0 u hu]
  refine ⟨fun s hs0 => ?_, ?_⟩
  · -- integrability at each radius
    rw [hemb.integrable_map_iff]
    change Integrable (fun u => evalReg x (foldedCircle ((c : ℂ) * u) s))
      (volume.withDensity fun z => ENNReal.ofReal (σ z))
    refine (integrable_withDensity_iff_integrable_smul' (f := fun z => ENNReal.ofReal (σ z))
      (ENNReal.measurable_ofReal.comp hσs.continuous.measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).2 ?_
    have hco : ContinuousOn (fun u => F ((c : ℂ) * u, s) * f u) K :=
      (hF.comp ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
        fun u hu => ⟨hcu u hu, hs0⟩).mul hf.continuous.continuousOn
    refine ((hco.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero
      fun u hu => by simp [hf0 u hu]).congr (ae_of_all _ fun u => ?_)
    by_cases hu : u ∈ K
    · simp only [smul_eq_mul, ENNReal.toReal_ofReal', hfdef]
      rw [hFx.evalReg_fc_of_mem (hcu u hu) hs0, mul_comm]
    · simp [hfdef, hσ0 u hu]
  · -- change of variables to scale `1`
    set f' : ℂ → ℝ := fun v => f ((c⁻¹ : ℝ) • v) with hf'def
    set K' : Set ℂ := (fun v : ℂ => (c⁻¹ : ℝ) • v) ⁻¹' K with hK'def
    have hK' : IsCompact K' :=
      (Homeomorph.smulOfNeZero (c⁻¹ : ℝ) (inv_ne_zero hc0.ne') (α := ℂ)).isCompact_preimage.2 hK
    have hK'H : K' ⊆ H := fun v hv => by
      have h1 : 0 < ((c⁻¹ : ℝ) • v).im := hH hv
      rw [Complex.smul_im, smul_eq_mul] at h1
      show 0 < v.im
      exact (mul_pos_iff_of_pos_left (inv_pos.2 hc0)).1 h1
    have hf' : LipschitzWith (Lσ * ‖(c⁻¹ : ℝ)‖₊) f' := hf.comp (lipschitzWith_smul _)
    have hf'0 : ∀ z ∉ K', f' z = 0 := fun z hz => hf0 _ hz
    obtain ⟨C, δ, hδ, hb⟩ := lipBound_of_count hFx hc hK' hK'H hf' hf'0
    obtain ⟨L, hL⟩ := exists_tendsto_of_sqrt_bound hδ hb
    refine ⟨|((c : ℝ) ^ Module.finrank ℝ ℂ)⁻¹| • L, ?_⟩
    refine (hL.const_smul _).congr' (eventually_nhdsWithin_of_forall fun s hs0 => ?_)
    have hs0' : (0 : ℝ) < s := hs0
    show _ = ∫ u, evalReg x (foldedCircle u s) ∂((G1.tmeas σ).map fun z => (c : ℂ) * z)
    rw [hpair s hs0', ← Measure.integral_comp_smul volume (fun v => F (v, s) * f' v) c]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hf'def, Complex.real_smul]
    rw [Complex.ofReal_inv, inv_mul_cancel_left₀ hc']

end G1Rest
end Thm18Asm
end QuantumZipper
