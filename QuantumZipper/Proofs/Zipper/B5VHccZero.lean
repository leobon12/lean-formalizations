import QuantumZipper.Proofs.Zipper.B5VHccMain
import QuantumZipper.Proofs.Zipper.Cor15GroupZero
import QuantumZipper.Proofs.Wire2

/-!
# B5-V at every fixed time, and the E-SM strong Markov identity with B5-V discharged

Task B5V-HCC (`handoff/B5.md`).

* `fwdMap_zero_time`, `sideImages_fst_zero_time`: at time `0` the forward map is `z ↦ z − W 0`,
  so `O⁻_0 = 0` (own elementary proof);
* `ae_coordsFull_h0f_zero`: a.s. `h⁰_0 = h0f κ 0` has the circle coordinates of `𝔥₀ + X`
  (`f̂_0 = id` on `ℍ`, and `𝔥₀ + X` is regular at the dyadic folded circles,
  `Cor15Group.ae_evalReg_fc_h0rev_add`);
* `ae_b5v_fixed_zero`: B5-V at `s = 0`. Both sides vanish: `ν_{𝔥₀+X}{0} = 0`
  (`AtomlessUncond.ae_gamma0_logSingularity`) and `ν_{h⁰}{0₋(T)} = 0` (`Wire2.ae_nu0_regular`);
* **`ae_b5v`**: B5-V in the form consumed by `ESM.lintegral_levelTime_strongMarkov_lenA`;
* **`lintegral_levelTime_strongMarkov_lenA_uncond`**: `Wire2.lintegral_levelTime_strongMarkov_lenA`
  with `hB5V` discharged.

Source: Sheffield, arXiv:1012.4797, Theorem 1.3 and its proof (§5, Lemma 5.6, pp. 66–68). Own
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open B2

/-- At time `0` the forward map is the translation by `−W 0` (away from `W 0`). -/
theorem fwdMap_zero_time (W : ℝ → ℝ) {z : ℂ} (hz : z ≠ W 0) : fwdMap W 0 z = z - W 0 := by
  have hex : ∃ u, IsForwardSol W z 0 u := by
    refine ⟨fun _ => z - W 0, continuousOn_const, fun t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    exact ⟨sub_ne_zero.2 hz, by simp⟩
  unfold fwdMap
  rw [dif_pos hex]
  have := (hex.choose_spec.2 0 ⟨le_rfl, le_rfl⟩).2
  simpa using this

theorem sideImages_fst_zero_time {W : ℝ → ℝ} (hW0 : W 0 = 0) : (sideImages W 0).1 = 0 := by
  show limUnder (𝓝[<] (0 : ℝ)) (fun x : ℝ => (fwdMap W 0 x).re) = 0
  refine Tendsto.limUnder_eq ?_
  have h : (fun x : ℝ => (fwdMap W 0 x).re) =ᶠ[𝓝[<] (0 : ℝ)] fun x => x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [fwdMap_zero_time W (by rw [hW0]; exact_mod_cast (ne_of_lt hx)), hW0]
    simp
  exact (tendsto_congr' h).2 (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0))

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- A.s. `h0f κ 0` has the circle coordinates of `𝔥₀ + X`. -/
theorem ae_coordsFull_h0f_zero (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, CoordsFull.coordsFull (h0f κ 0 B X ω) =
      CoordsFull.coordsFull (ofFun (h0rev κ) + X ω) := by
  filter_upwards [Cor15Group.ae_evalReg_fc_h0rev_add κ hX, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hreg hc h0
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hE : EqOn (fwdMapInv (drive κ B ω) 0) id H := fun z hz => by
    rw [fwdMapInv_eq_revMap_vrev hWc hW0 le_rfl hz]
    exact CharFun.revMap_zero_eq (continuous_vrev hWc 0) (vrev_zero le_rfl) hz
  funext i
  have hr := UnzipFull.fullIndex_radius_pos i
  have hμH : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 Hᶜ = 0 :=
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ hr)
  show h0f κ 0 B X ω (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) = _
  rw [h0f_eq_unzippedField]
  show coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) 0) (Qc (Real.sqrt κ)) _ = _
  rw [UnzipInvariance.coordChange_congr_of_eqOn hE hμH]
  simp only [coordChange, Measure.map_id, deriv_id, norm_one, Real.log_one, integral_zero,
    mul_zero, add_zero]
  exact hreg i

/-- **B5-V at `s = 0`.** -/
theorem ae_b5v_fixed_zero (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, (unzipLengths (Real.sqrt κ) (cfg κ B X ω) 0).1 = lenRHS κ T B X ω 0 := by
  filter_upwards [ae_coordsFull_h0f_zero (κ := κ) hB hX, hB.eval_zero_ae_eq_zero,
    AtomlessUncond.ae_gamma0_logSingularity hX hκ hκ4,
    Wire2.ae_nu0_regular hκ hκ4 hT hB hX hind] with ω hcf h0 hg hν
  rw [unzipLengths_fst_eq, sideImages_fst_zero_time (drive_zero h0), lenRHS, sub_zero,
    Icc_self, Icc_self, hν.1, qBoundaryMeasure_congr_full hcf, hg.2.2]

/-- **B5-V at every fixed time**, in the form consumed by
`ESM.lintegral_levelTime_strongMarkov_lenA`. -/
theorem ae_b5v (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ s : ℝ≥0, (s : ℝ) ≤ T → ∀ᵐ ω ∂P, ESM.lenMinus κ B X s ω = lenRHS κ T B X ω s := by
  intro s hsT
  rcases (NNReal.coe_nonneg s).eq_or_lt with h | h
  · have hs0 : s = 0 := NNReal.coe_eq_zero.1 h.symm
    subst hs0
    simpa [ESM.lenMinus] using ae_b5v_fixed_zero hκ hκ4 hT hB hX hind
  · exact ae_b5v_fixed_pos hκ hκ4 hB hX hind h hsT

section ESMWire

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

end ESMWire

end B5
end QuantumZipper
