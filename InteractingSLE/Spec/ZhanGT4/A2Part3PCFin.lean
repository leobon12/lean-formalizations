/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFinSmall

/-!
# A.2 part 3: unconditional physical and mapped pair contact

Packet PROVE-ZHAN-A2P3-PC. Finite contact before strip life ends uses the
first-contact arc argument. Contact at the strip end uses the real-ray lemma
and Aux. 3. Together they discharge both finite physical-contact obligations
and both requested pair-contact statements.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory Bornology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2X.P3

open QuantumZipper

/-- The first-contact case strictly before the large strip end, for a simple
small trace rooted at an original large left mark. -/
theorem finitePhysicalContact_of_contact_lt_lifeEnd
    {a : ℝ} {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {w₂ b₂ : ℝ≥0 → ℝ} {vL₂ : Fin nL → ℝ≥0 → ℝ} {vR₂ : Fin nR → ℝ≥0 → ℝ}
    {ζ₂ : ℝ≥0∞} (hp₂ : IsIntegratedSLEPath a xL xR ρL ρR w₂ vL₂ vR₂ b₂ ζ₂)
    {i j : Fin nL} (hij : i ≤ j) {x r : ℝ} (hx : xL j = x)
    {w₁ : ℝ≥0 → ℝ} {ζ₁ : ℝ≥0∞} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w₁ ζ₁ η) (hi : InjOn η {t | (t : ℝ≥0∞) ≤ ζ₁})
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ₁ → η t ∈ H)
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < ζ₁)
    (hc : contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ (vL₂ i) ζ₂)
      x (Strip.extPath w₁) q < lifeEnd w₂ (vL₂ i) ζ₂) :
    FinitePhysicalContact x r w₁ w₂ (vL₂ i) ζ₂ q := by
  let c := contactTime 0 (Strip.extPath w₂) (lifeEnd w₂ (vL₂ i) ζ₂)
    x (Strip.extPath w₁) q
  let T : ℝ≥0 := c.toNNReal
  have hT : (T : ℝ≥0∞) = c := ENNReal.coe_toNNReal (ne_top_of_lt hc)
  have hTL : (T : ℝ≥0∞) < lifeEnd w₂ (vL₂ i) ζ₂ := hT ▸ hc
  obtain ⟨R, hTR, hRL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTL
  obtain ⟨S, hRS, hSL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hRL
  have hSζ : (S : ℝ≥0∞) < ζ₂ := hSL.trans_le (lifeEnd_le_lifetime _ _ _)
  have hRS' : R < S := ENNReal.coe_lt_coe.1 hRS
  have hTR' : T < R := ENNReal.coe_lt_coe.1 hTR
  let U := frozenDrive w₂ (S : ℝ)
  have hf := hp₂.isForcePath
  have hU : Continuous U := continuous_frozenDrive_of_lt hf.continuousOn_w
    (by simpa only [ENNReal.ofReal_coe_nnreal] using hSζ)
  have hU0 : U 0 = 0 := by
    rw [show U = frozenDrive w₂ (S : ℝ) from rfl, frozenDrive_zero S.coe_nonneg, hf.w_zero]
  have hUeq : ∀ s : ℝ, 0 ≤ s → s < S → U s = w₂ s.toNNReal :=
    fun s hs hsS => frozenDrive_eq ⟨hs, hsS.le⟩
  have hgap : ∀ t : ℝ≥0, t < S → vL₂ j t < w₂ t := by
    intro t ht
    have htL := (ENNReal.coe_lt_coe.2 ht).trans hSL
    have htζ := htL.trans_le (lifeEnd_le_lifetime _ _ _)
    exact (hf.antitone_vL htζ hij).trans_lt
      ((isStripLife_of_lt_lifeEnd htL).2 t le_rfl)
  have hsol := isForwardSol_gapL_before_horizon hp₂ hSζ.le hgap hUeq
    (NNReal.coe_lt_coe.2 hRS')
  rw [hx] at hsol
  obtain ⟨α, hα, hα0, hαH, hK⟩ := exists_arc_of_simple_generatingTrace hη hi hH hq0 hq x
  obtain ⟨p, hpB, hpH, hpK⟩ := exists_contact_mem_closure_hullBefore_of_arc hU hU0
    hT hTL hTR' (fun s hs => (frozenDrive_eq
      ⟨hs.1, hs.2.trans (NNReal.coe_le_coe.2 hRS'.le)⟩).symm)
    (NNReal.coe_pos.2 hq0) hα hα0 hαH hK hsol
  refine ⟨p, ?_, Or.inl ⟨hpH, hpK⟩⟩
  change p ∈ closure (preContactHulls (Strip.extPath w₂) c)
  rw [← hT, preContactHulls_coe_eq_hullBefore]
  exact hpB

/-- **Finite physical contact, G3**, with no additional mathematical hypothesis. -/
theorem finitePhysicalContactG3Statement (κ : ℝ) : FinitePhysicalContactG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
    𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  have hEnd := ae_finitePhysicalContact_of_contact_eq_lifeEnd
    (by linarith only [hκ4] : 0 < κ) hx
    (xL := ![x, y]) (fun i => by
      fin_cases i
      · change x ≤ x
        exact le_rfl
      · change y ≤ x
        exact hyx.le) hpair.1 0
  filter_upwards [hpair.1.ae_isIntegratedSLEPath, hEnd,
    ae_smallG3_simple_trace hκ4 hκ8 hyx hx hpair.2.1]
    with ω hp₂ he hs hq hcfin
  by_cases hc : contactTime 0 (Strip.extPath (W₂ · ω))
      (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y (Strip.extPath (W₁ · ω)) q =
      lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)
  · exact he y (W₁ · ω) q (by rwa [← hc]) hc
  · obtain ⟨η, hη, hi, hH⟩ := hs
    exact finitePhysicalContact_of_contact_lt_lifeEnd hp₂ (i := 0) (j := 1)
      (by decide) (by rfl) hη hi hH hq0 hq
      (lt_of_le_of_ne (min_le_left _ _) hc)

/-- **Finite physical contact, Eight**, with no additional mathematical hypothesis. -/
theorem finitePhysicalContactEightStatement (κ : ℝ) : FinitePhysicalContactEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂
    𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  have hEnd := ae_finitePhysicalContact_of_contact_eq_lifeEnd
    (by linarith only [hκ8] : 0 < κ) hx
    (xL := ![x]) (fun i => by fin_cases i; exact le_rfl) hpair.1 0
  filter_upwards [hpair.1.ae_isIntegratedSLEPath, hEnd,
    ae_smallEight_simple_trace hκ8 hx hpair.2.1]
    with ω hp₂ he hs hq hcfin
  by_cases hc : contactTime 0 (Strip.extPath (W₂ · ω))
      (lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x (Strip.extPath (W₁ · ω)) q =
      lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)
  · exact he x (W₁ · ω) q (by rwa [← hc]) hc
  · obtain ⟨η, hη, hi, hH⟩ := hs
    exact finitePhysicalContact_of_contact_lt_lifeEnd hp₂ (i := 0) (j := 0)
      le_rfl (by simp only [Matrix.cons_val_zero]) hη hi hH hq0 hq
      (lt_of_le_of_ne (min_le_left _ _) hc)

/-- **A.2 part 3, (I2), G3.** -/
theorem pairContactG3Statement (κ : ℝ) : PairContactG3Statement.{u} κ :=
  pairContactG3Statement_of_finitePhysicalContact (finitePhysicalContactG3Statement κ)

/-- **A.2 part 3, (I2), Eight.** -/
theorem pairContactEightStatement (κ : ℝ) : PairContactEightStatement.{u} κ :=
  pairContactEightStatement_of_finitePhysicalContact (finitePhysicalContactEightStatement κ)

end InteractingSLE.ZhanGT4.A2X.P3
