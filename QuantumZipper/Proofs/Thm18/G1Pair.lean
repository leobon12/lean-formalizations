import QuantumZipper.Proofs.Thm18.G1Rescale

/-!
# G1, part 3: scale consistency from the continuum limit of smoothed pairings

The last clause of `G1.ChoiceRegular` (scale consistency of the regularization at dilated test
measures, `ScaleConsistentAt`) is reduced to the PAIR-LIM form used in the repository for the
free field (`PairLim.ae_tendsto_pairRaw_continuum`): the circle-smoothed pairings
`s ↦ ∫ evalReg x (fc(u, s)) dν(u)` converge as `s → 0⁺`. For a regular sample the
regularization is the limit along `s = 2^{-k}`, and the rescaled field is regularized along
`s = b 2^{-k}`; a continuum limit makes the two agree.

* `scaleConsistentAt_of_continuum` (deterministic);
* `isFiniteMeasure_tmeas`, `ae_tmeas_map_mem_Hbar`: the dilated signed parts of a test
  function are finite measures carried by `ℍ̄`;
* `choiceRegular_of_continuum`: `ChoiceRegular` from its first four clauses and the continuum
  limit at every dilated signed part.

Own elementary argument (Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, §3.1, for the
circle-average smoothing that PAIR-LIM supplies).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1

/-- **Scale consistency from a continuum limit.** For a regular sample `x`, a finite measure `ν`
carried by `ℍ̄`, and `b > 0`: if the smoothed pairings `s ↦ ∫ evalReg x (fc(u, s)) d(b_* ν)`
are integrable and converge as `s → 0⁺`, then `ScaleConsistentAt x Q b ν`. -/
theorem scaleConsistentAt_of_continuum {x : FieldSample} (hx : IsRegularSample x) (Q : ℝ)
    {b : ℝ} (hb : 0 < b) {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ u ∂ν, u ∈ Hbar)
    (hint : ∀ s : ℝ, 0 < s → Integrable (fun u => evalReg x (foldedCircle u s))
      (ν.map fun z => (b : ℂ) * z))
    {L : ℝ} (hcont : Tendsto (fun s => ∫ u, evalReg x (foldedCircle u s)
      ∂(ν.map fun z => (b : ℂ) * z)) (𝓝[>] 0) (𝓝 L)) :
    ScaleConsistentAt x Q b ν := by
  obtain ⟨F, hF⟩ := hx
  have hF' := hF.congr_evalReg
  have hm : Measurable (fun z : ℂ => (b : ℂ) * z) := measurable_const_mul _
  have e : ∀ s : ℝ, 0 < s → ∫ u, evalReg x (foldedCircle ((b : ℂ) * u) s) ∂ν =
      ∫ u, evalReg x (foldedCircle u s) ∂(ν.map fun z => (b : ℂ) * z) := fun s hs =>
    (integral_map hm.aemeasurable (hint s hs).aestronglyMeasurable).symm
  have h1 : evalReg x (ν.map fun z => (b : ℂ) * z) = L :=
    hF'.evalReg_map_eq hm (RegClosure.mapsTo_mul_pos hb) hν (fun k => e _ (radius_pos k))
      (hcont.comp RegClosure.tendsto_radius_nhdsGT)
  have hbr : Tendsto (fun k => b * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hb (radius_pos k)⟩
    simpa using ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul b)
  have hG : ∀ k : ℕ, ∫ u, ((fun q : ℂ × ℝ => evalReg x (foldedCircle q.1 q.2))
        ((b : ℂ) * (id u), b * radius k) + Q * Real.log b) ∂ν =
      ∫ u, evalReg x (foldedCircle u (b * radius k)) ∂(ν.map fun z => (b : ℂ) * z) +
        ν.real univ * (Q * Real.log b) := by
    intro k
    have hi : Integrable (fun u => evalReg x (foldedCircle ((b : ℂ) * u) (b * radius k))) ν :=
      (hint _ (mul_pos hb (radius_pos k))).comp_measurable hm
    show ∫ u, (evalReg x (foldedCircle ((b : ℂ) * u) (b * radius k)) + Q * Real.log b) ∂ν = _
    rw [integral_add hi (integrable_const _), integral_const, smul_eq_mul,
      e _ (mul_pos hb (radius_pos k))]
  have h2 : evalReg (rescale x Q b) (ν.map id) =
      L + ν.real univ * (Q * Real.log b) :=
    (hF'.rescale' Q hb).evalReg_map_eq measurable_id (mapsTo_id _) hν hG
      ((hcont.comp hbr).add tendsto_const_nhds)
  rw [Measure.map_id] at h2
  unfold ScaleConsistentAt
  rw [h2, h1]
  ring

theorem isFiniteMeasure_tmeas {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    IsFiniteMeasure (tmeas g) :=
  isFiniteMeasure_withDensity_ofReal (hg.integrable_of_hasCompactSupport hgc).hasFiniteIntegral

theorem ae_tmeas_map_mem_Hbar {g : ℂ → ℝ} (hg : Continuous g) (hgH : tsupport g ⊆ H) {c : ℝ}
    (hc : 0 < c) : ∀ᵐ u ∂((tmeas g).map fun z => (c : ℂ) * z), u ∈ Hbar := by
  have hm : Measurable (fun z : ℂ => (c : ℂ) * z) := measurable_const_mul _
  refine (ae_map_iff hm.aemeasurable isClosed_Hbar.measurableSet).2 ?_
  show ∀ᵐ z ∂(volume.withDensity fun z => ENNReal.ofReal (g z)), (c : ℂ) * z ∈ Hbar
  rw [ae_withDensity_iff (f := fun z => ENNReal.ofReal (g z))
    (ENNReal.measurable_ofReal.comp hg.measurable)]
  refine Eventually.of_forall fun z hz => RegClosure.mapsTo_mul_pos hc ?_
  have hz' : g z ≠ 0 := fun h0 => hz (by simp [h0])
  exact le_of_lt (show 0 < z.im from hgH (subset_tsupport g hz'))

/-- **`ChoiceRegular` from the continuum limit of smoothed pairings.** -/
theorem choiceRegular_of_continuum {γ : ℝ} {y : FieldSample} {ψ : ℂ → ℂ}
    (hint : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    (hexact : ∀ d ∈ Hbar, ∀ r > 0, evalReg (coordChange y ψ (Qc γ)) (foldedCircle d r) =
      coordChange y ψ (Qc γ) (foldedCircle d r))
    (hgood : IsLQGGood γ (coordChange y ψ (Qc γ)))
    (hs : 0 < scaleParam γ (coordChange y ψ (Qc γ)))
    (hpair : ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ, (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
      (∀ s : ℝ, 0 < s → Integrable (fun u => evalReg (coordChange y ψ (Qc γ)) (foldedCircle u s))
        ((tmeas σ).map fun z => (c : ℂ) * z)) ∧
      ∃ L : ℝ, Tendsto (fun s => ∫ u, evalReg (coordChange y ψ (Qc γ)) (foldedCircle u s)
        ∂((tmeas σ).map fun z => (c : ℂ) * z)) (𝓝[>] 0) (𝓝 L)) :
    ChoiceRegular γ y ψ := by
  refine ⟨hint, hexact, hgood, hs, fun b hb c hc ρ σ hσ => ?_⟩
  obtain ⟨hsm, hsc, hsH⟩ := ρ.2
  have hσc : Continuous σ ∧ HasCompactSupport σ ∧ tsupport σ ⊆ H := by
    rcases hσ with rfl | rfl
    · exact ⟨hsm.continuous, hsc, hsH⟩
    · exact ⟨hsm.continuous.neg, hsc.neg, by
        rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hsH⟩
  obtain ⟨hσ1, hσ2, hσ3⟩ := hσc
  have := isFiniteMeasure_tmeas hσ1 hσ2
  have hbc : 0 < b * c := mul_pos hb hc
  have hmap : ((tmeas σ).map fun z => (c : ℂ) * z).map (fun z => (b : ℂ) * z) =
      (tmeas σ).map fun z => ((b * c : ℝ) : ℂ) * z := by
    rw [Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
    congr 1
    funext z
    simp only [Function.comp, Complex.ofReal_mul]
    ring
  obtain ⟨hi, L, hL⟩ := hpair (b * c) hbc ρ σ hσ
  refine scaleConsistentAt_of_continuum hgood.1 (Qc γ) hb (ae_tmeas_map_mem_Hbar hσ1 hσ3 hc)
    (L := L) (fun s hs' => ?_) ?_
  · rw [hmap]; exact hi s hs'
  · rw [hmap]; exact hL

end G1
end Thm18Asm
end QuantumZipper
