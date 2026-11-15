/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EFamIdent
import InteractingSLE.Spec.ZhanGT4.A1ELawSample

/-!
# Zhan's A.1 under R83, (Eight), large-curve direction: the unprotected and the trivial frozen times

Packet PROVE-A1-EIGHTFAM (patched marginals throughout).

* **`imgZero_facts`** (generic): at the stop `τ = 0` of a conditioning driver continuous near `0`, the frozen hull is
  empty and the chart is the identity, so the contact time is the image curve's lifetime, the canonical clock is the
  identity, the canonical image driver is the curve's own driver and the canonical image lifetime is the lifetime;
* **`eightFst_law_unprot`**: beyond the small exit the raw cap vanishes (`isSeedSampleLaw_of_cap_zero_of_law` with
  `eightFst_law_prot` at the exit);
* **`eightFst_zero_ident`**: at `σ = 0` the canonical image of the large curve is the curve itself, every canonical
  force is its mark `VL₂ 0` (the three marks sit at the small source `x`), the raw caps are the large exits;
* **`eightFst_law_zero`**: the one-sample law at `σ = 0` (density `1`; the residual is `B₂` because the three image
  weights sum to `0`);
* **`eightFst_geom_zero`**: the deterministic geometry at `σ = 0` up to every cap before `lifeEnd`.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace InteractingSLE.ZhanGT4.A1EFam
open QuantumZipper (H fwdMap fwdHull drive IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm A1Forces A1MultiMark A1Family A1RLaw


section Zero

/-- **The canonical image at a trivial frozen hull** (stop `τ = 0`, conditioning driver continuous near `0`): the
contact time is the lifetime, the clock is the identity, the canonical image driver is the curve's own driver before its
lifetime, and the canonical image lifetime is the lifetime. -/
theorem imgZero_facts {xk : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞}
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ' : ℝ, (0 : ℝ) < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) :
    A2X.contactTime 0 wj ζj xk wk 0 = ζj ∧
      (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < ζj → A1Ref.imgClk 0 wj xk wk 0 t = t) ∧
      (∀ s : ℝ, 0 ≤ s → ENNReal.ofReal s < ζj → A1Ref.imgDrv 0 wj ζj xk wk 0 s = wj s) ∧
      A1Ref.imgLife 0 wj ζj xk wk 0 = ζj := by
  obtain ⟨τ', hτ', hcτ'⟩ := hk
  have hmap : physMap xk wk 0 = id := funext fun z => by
    simp only [physMap, hk0, fwdMap_zero_eq_sub, id]
    push_cast; ring
  have hhull : physHull xk wk 0 = ∅ := by
    rw [physHull_congr le_rfl hτ' (A1Ref.stopDrv_eqOn wk τ').symm, physHull_eq_fwdHull]
    exact QuantumZipper.RS.fwdHull_zero_eq_empty ((A1Ref.continuous_stopDrv hcτ' hτ'.le).add continuous_const)
  have hct : A2X.contactTime 0 wj ζj xk wk 0 = ζj := by
    unfold A2X.contactTime
    simp [hhull]
  -- a continuous driver agreeing with `wj` slightly beyond `t`
  have hext : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < ζj →
      ∃ T' : ℝ, t < T' ∧ ENNReal.ofReal T' < ζj ∧ ContinuousOn wj (Icc 0 T') := fun t ht0 ht => by
    obtain ⟨r, hr0, htr, hrζ⟩ := ENNReal.lt_iff_exists_real_btwn.1 ht
    exact ⟨r, ((ENNReal.ofReal_lt_ofReal_iff').1 htr).1, hrζ, hj r hrζ⟩
  have hclk : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < ζj → A1Ref.imgClk 0 wj xk wk 0 t = t := fun t ht0 ht => by
    rcases ht0.eq_or_lt with h0 | hpos
    · rw [← h0]; exact A1Ref.imgClk_zero
    obtain ⟨T', htT', -, hcT'⟩ := hext t ht0 ht
    have hT'0 : 0 ≤ T' := ht0.trans htT'.le
    simp only [A1Ref.imgClk, hpos, ↓reduceIte, hmap, image_id, A1Ref.physHull_zero]
    rw [LocalExt.fwdHull_congr_of_eqOn_of_lt ht0 htT' (A1Ref.stopDrv_eqOn wj T').symm,
      hcapSet_fwdHull (A1Ref.continuous_stopDrv hcT' hT'0) ht0]
    ring
  refine ⟨hct, hclk, fun s hs0 hs => ?_, ?_⟩
  · obtain ⟨T, hsT, hTζ, -⟩ := hext s hs0 hs
    obtain ⟨T', hTT', hT'ζ, hcT'⟩ := hext T (hs0.trans hsT.le) hTζ
    have hT'0 : 0 ≤ T' := (hs0.trans hsT.le).trans hTT'.le
    have hgood : A1Ref.IsGoodTime 0 wj ζj xk wk 0 T := ⟨hs0.trans_lt hsT, by rw [hct]; exact hTζ⟩
    set V := A1Ref.stopDrv wj T' with hV
    have hVc : Continuous V := A1Ref.continuous_stopDrv hcT' hT'0
    have hVe : EqOn V wj (Icc 0 T') := A1Ref.stopDrv_eqOn wj T'
    have hV0 : V 0 = 0 := by rw [hVe ⟨le_rfl, hT'0⟩, hj0]
    have hW' : A1Ref.IsImgDrvOn 0 wj xk wk 0 T V := by
      refine ⟨hVc, ?_, fun t ht => ?_⟩
      · rw [hmap, hV0]
        exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using tendsto_id)
      · rw [hclk t ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) hTζ), hmap, image_id,
          A1Ref.physHull_zero]
        exact LocalExt.fwdHull_congr_of_eqOn_of_lt ht.1 (ht.2.trans_lt hTT') hVe
    have hT0 : 0 ≤ T := hs0.trans hsT.le
    have hsI : s ∈ Icc 0 (A1Ref.imgClk 0 wj xk wk 0 T) := by
      rw [hclk T hT0 hTζ]; exact ⟨hs0, hsT.le⟩
    rw [A1Ref.imgDrv_eqOn hj hj0 ⟨τ', hτ', hcτ'⟩ hk0 le_rfl hgood hW' hsI]
    exact hVe ⟨hs0, hsT.le.trans hTT'.le⟩
  · unfold A1Ref.imgLife
    rw [hct]
    refine le_antisymm (iSup₂_le fun s hs => ?_) (ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
    · rw [hclk s s.coe_nonneg (by rwa [ENNReal.ofReal_coe_nnreal]), ENNReal.ofReal_coe_nnreal]
      exact hs.le
    · refine le_iSup₂_of_le r hr ?_
      rw [hclk r r.coe_nonneg (by rwa [ENNReal.ofReal_coe_nnreal]), ENNReal.ofReal_coe_nnreal]

end Zero

section Frame
variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
variable {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}


/-- **The unprotected one-sample law** (frozen small time beyond the small exit): the raw cap vanishes and the density
is the protected one at the exit, so A1-EIGHTLAW's `isSeedSampleLaw_of_cap_zero_of_law` applies to
`eightFst_law_prot` at `σ = S₁ᵐ(x₀)`. -/
theorem eightFst_law_unprot [𝓖₂.IsRightContinuous] (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : eightS₁ x W₁ ζ₁ m x₀ < σ) :
    IsSeedSampleLaw (P₂.withDensity fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ m (x₀, y))
      (fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) t (x₀, y))
      (fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => σ) (x₀, y))
      (fun i t y => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x₀, y)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
        (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
          W₁ (fun _ => σ) s (x₀, y))
        (fun i s => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x₀, y)) (fun j _ => (j.elim0 : ℝ)) t)
      (fun k y => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ σ k (x₀, y)) m := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  have hpos : 0 < eightS₁ x W₁ ζ₁ m x₀ := NNReal.coe_pos.1 (hgood₁ m x₀).2.1
  have h := eightFst_law_prot hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hpos le_rfl
  have e : (fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ σ m (x₀, y)) =
      fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ (eightS₁ x W₁ ζ₁ m x₀) m (x₀, y) := funext fun y => by
    simp only [eightFstD, min_eq_right hσ.le, min_self]
  rw [e]
  refine isSeedSampleLaw_of_cap_zero_of_law h (fun y => ?_) (fun y => ?_)
  · rw [seedCapacityNoise_zero, show rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ (fun _ => σ) 0 (x₀, y) = 0 from cImgDrvM_zero _ _ _ _ _ _ _ _,
      zero_div]
  · unfold eightFstCap
    refine capFst_of_nonpos ?_
    simp only [eightFstOwn, not_le.2 hσ, ↓reduceIte, le_refl]

/-- **The large Eight direction at the trivial frozen time `σ = 0`** (patched data): the canonical image is the large
curve itself — the masked canonical driver is `W₂`, the image lifetime is `lifeEnd`, every canonical force is the
large curve's own mark `VL₂ 0` (the three frozen-chart marks all sit at the small curve's source), and the raw caps are
the large exits. -/
theorem eightFst_zero_ident (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) (x₀ : X) (y : Y) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => 0) t (x₀, y) = W₂ t y) ∧
    rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => 0) (x₀, y) = lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) ∧
    (∀ i (t : ℝ≥0), (t : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y) = VL₂ 0 t y) ∧
    ∀ k, eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y) = eightS₂ x W₂ ζ₂ k y := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -, -, -, -, hS₂pos, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  have hζ₁ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt bot_le (hgood₁ 0 x₀).1
  obtain ⟨τ', hτ', hcτ'⟩ := exists_gt_continuousOn_extPath (h₁.path x₀).2.2.2.1 hζ₁
  rw [NNReal.coe_zero] at hτ'
  have hjo : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 T) := fun T hT =>
    A1Ref.continuousOn_extPath_Icc (h₂.path y).2.2.2.1 (hT.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _))
  have hj0 : Strip.extPath (W₂ · y) 0 = 0 := by simp [Strip.extPath, (h₂.path y).1]
  have hk0 : Strip.extPath (W₁ · x₀) 0 = 0 := by simp [Strip.extPath, (h₁.path x₀).1]
  obtain ⟨hct, hclk, hdrv, hlife⟩ := imgZero_facts (xk := x) hjo hj0 ⟨τ', hτ', hcτ'⟩ hk0
  have hL0 : (0 : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) :=
    lt_of_le_of_lt bot_le (eightFst_lt_lifeEnd hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ 0 x₀ y)
  have hdrv' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      A1Ref.imgDrv 0 (Strip.extPath (W₂ · y)) (lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x
        (Strip.extPath (W₁ · x₀)) 0 t = W₂ t y := fun t ht => by
    rw [hdrv t t.coe_nonneg (by rwa [ENNReal.ofReal_coe_nnreal]), extPath_coe]
  have hdrv0 : A1Ref.imgDrv 0 (Strip.extPath (W₂ · y)) (lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x
      (Strip.extPath (W₁ · x₀)) 0 0 = 0 := by
    rw [hdrv 0 le_rfl (by rwa [ENNReal.ofReal_zero]), hj0]
  have hI1 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) →
      rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => 0) t (x₀, y) = W₂ t y := fun t ht => by
    simp only [rDrvFst, A1Ref.cImgDrvM, A1Ref.cImgDrv, A1Ref.cImgSrc, hζ₁, ↓reduceIte, NNReal.coe_zero]
    rw [hdrv' t ht, hdrv0, sub_zero]
  refine ⟨hI1, ?_, fun i t ht => ?_, fun k => ?_⟩
  · simp only [rLifeFst, A1Ref.cImgLifeM, A1Ref.cImgLife, hζ₁, ↓reduceIte, NNReal.coe_zero]
    exact hlife
  · -- the forces: every mark sits at `x`, whose flow is the large curve's own mark
    obtain ⟨hw0₁, hvl0₁, hvr0₁, -⟩ := h₁.path x₀
    have hp : largeEightMarks (x - 0) (W₁ · x₀) (fun i t => VL₁ i t x₀) (fun j t => VR₁ j t x₀) 0 i = x := by
      have h0 := hvr0₁ 0
      have h1 := hvl0₁ 0
      simp only [Matrix.cons_val_zero] at h0 h1
      fin_cases i
      · show x - 0 + VR₁ 0 0 x₀ = x
        rw [h0]; ring
      · show x - 0 + W₁ 0 x₀ = x
        rw [show W₁ 0 x₀ = 0 from hw0₁]; ring
      · show x - 0 + VL₁ 0 0 x₀ = x
        rw [h1]; ring
    have hvL0 : VL₂ 0 0 y = x := by simpa using (h₂.path y).2.1 0
    by_cases ht0 : t = 0
    · subst ht0
      rw [eightFstVL_zero, hvL0]
      have h0 := hvr0₁ 0
      have h0' := hvr0₁ 1
      have h1 := hvl0₁ 0
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h0' h1
      fin_cases i
      · show VR₁ 0 0 x₀ - VR₁ 1 0 x₀ = x
        rw [h0, h0']; ring
      · show W₁ 0 x₀ - VR₁ 1 0 x₀ = x
        rw [show W₁ 0 x₀ = 0 from hw0₁, h0']; ring
      · show VL₁ 0 0 x₀ - VR₁ 1 0 x₀ = x
        rw [h1, h0']; ring
    · unfold eightFstVL
      rw [ite_eq_right_of_eq_false _ _ (eq_false ht0)]
      have hlt : ENNReal.ofReal (t : ℝ) < A1Ref.imgLife 0 (Strip.extPath (W₂ · y))
          (lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x (Strip.extPath (W₁ · x₀)) 0 := by
        rw [hlife, ENNReal.ofReal_coe_nnreal]; exact ht
      simp only [rForceFst, canonForce, Set.mem_ofPred_eq, hζ₁, true_and, NNReal.coe_zero, hlt, ↓reduceIte]
      rw [hdrv' t ht, hdrv0, hp]
      have hst : A1Ref.stopDrv (A1Ref.imgDrv 0 (Strip.extPath (W₂ · y)) (lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x
          (Strip.extPath (W₁ · x₀)) 0) t = A1Ref.stopDrv (Strip.extPath (W₂ · y)) t := funext fun s => by
        simp only [A1Ref.stopDrv]
        have hm : max 0 (min s t) ∈ Icc (0 : ℝ) t :=
          ⟨le_max_left _ _, max_le t.coe_nonneg (min_le_right _ _)⟩
        exact hdrv _ hm.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hm.2) (by rwa [ENNReal.ofReal_coe_nnreal]))
      rw [hst]
      have hlt₂ : (t : ℝ≥0∞) < ζ₂ y := ht.trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _)
      obtain ⟨-, -, -, -, hcvL, -, -, -, -, -, -, -, -, hvLeq, -⟩ := id (h₂.path y)
      have hveq : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₂ y →
          VL₂ 0 s y = x + ∫ r in (0 : ℝ)..s, 2 / (VL₂ 0 r.toNNReal y - W₂ r.toNNReal y) := fun s hs => by
        simpa using hvLeq s hs 0
      have hsep : ∀ r ≤ t, VL₂ 0 r y ≠ W₂ r y := fun r hr =>
        ((A2X.P3.isStripLife_of_lt_lifeEnd ht).2 r hr).ne
      have hct' : ContinuousOn (Strip.extPath (W₂ · y)) (Icc 0 (t : ℝ)) :=
        hjo t (by rwa [ENNReal.ofReal_coe_nnreal])
      have hv := A1G3Calc.isForwardSol_of_force (hcvL 0) hveq hlt₂ hsep hct' (fun _ _ => rfl)
      rw [fwdRe_stopDrv_eq hct' t.coe_nonneg hv,
        QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨t.coe_nonneg, le_rfl⟩]
      simp only [Complex.ofReal_re, extPath_coe]
      ring
  · -- the caps: the clock is the identity
    have hOwn : eightFstOwn x W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y) = eightS₂ x W₂ ζ₂ k y := by
      simp only [eightFstOwn, zero_le, ↓reduceIte]
    have hL := eightFst_lt_lifeEnd hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y
    have hG : A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y)) (lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) x
        (Strip.extPath (W₁ · x₀)) ((0 : ℝ≥0) : ℝ) (eightFstOwn x W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y)) := by
      rw [hOwn, NNReal.coe_zero]
      exact ⟨hS₂pos k y, by rw [hct, ENNReal.ofReal_coe_nnreal]; exact hL⟩
    unfold eightFstCap
    rw [capFst_eq_of_isGoodTime (z := (x₀, y)) (τ := fun _ => (0 : ℝ≥0)) (T := eightFstOwn x W₁ ζ₁ W₂ ζ₂ 0 k)
      hζ₁ hjo (h₂.path y).1 ⟨τ', by rw [NNReal.coe_zero]; exact hτ', hcτ'⟩ (h₁.path x₀).1 hG, hOwn,
      NNReal.coe_zero, hclk _ (NNReal.coe_nonneg _) (by rw [ENNReal.ofReal_coe_nnreal]; exact hL)]
    exact Real.toNNReal_coe

/-- **The one-sample law at the trivial frozen time `σ = 0`** (patched data): the density is `1`, the canonical image is
the large curve itself and the residual is the large curve's own Brownian motion (the three image weights sum to `0`),
so `IsSeedSampleLaw` holds with `𝓖₂` and `B₂`. -/
theorem eightFst_law_zero [𝓖₂.IsRightContinuous] (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) :
    IsSeedSampleLaw (P₂.withDensity fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 m (x₀, y))
      (fun t y => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => 0) t (x₀, y))
      (fun y => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => 0) (x₀, y))
      (fun i t y => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y)) (fun j _ _ => (j.elim0 : ℝ))
      (fun t y => seedCapacityNoise κ (largeEightImgRhoL κ) ![]
        (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
          W₁ (fun _ => 0) s (x₀, y))
        (fun i s => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x₀, y)) (fun j _ => (j.elim0 : ℝ)) t)
      (fun k y => eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y)) m := by
  have hκ : 0 < κ := by linarith
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, -, -, -, -, -, -, hlt₂⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hS₂ : ∀ k, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ k ω : WithTop ℝ≥0) := fun k =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) (-x) k
  have hid := fun y => eightFst_zero_ident hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y
  have hL : ∀ y, (eightS₂ x W₂ ζ₂ m y : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) := fun y =>
    eightFst_lt_lifeEnd hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ y
  have hlt : ∀ y (s : ℝ≥0), s ≤ eightS₂ x W₂ ζ₂ m y → (s : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) :=
    fun y s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hL y)
  -- the density is `1`
  have e : (fun y => eightFstD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 m (x₀, y)) = fun _ => 1 := funext fun y => by
    simp only [eightFstD, zero_le, min_eq_left, NNReal.coe_zero, seedHeightField_zero_left, ENNReal.ofReal_one]
  rw [e, show (fun _ : Y => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  -- the cap is the large exit
  have hcap : ∀ y, eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y) = eightS₂ x W₂ ζ₂ m y := fun y =>
    (hid y).2.2.2 m
  have hE : ∀ s : ℝ≥0, MeasurableSet[𝓖₂ s] {y | s < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y)} :=
    fun s => by
    simp only [hcap]
    have h := (hS₂ m).measurableSet_gt s
    simpa only [WithTop.coe_lt_coe] using h
  -- the residual is the large curve's Brownian motion before the exit
  have hNres : ∀ y (t : ℝ≥0), t ≤ eightS₂ x W₂ ζ₂ m y →
      B₂ t y = seedCapacityNoise κ (largeEightImgRhoL κ) ![]
        (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
          W₁ (fun _ => 0) s (x₀, y))
        (fun i s => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x₀, y)) (fun j _ => (j.elim0 : ℝ)) t := by
    intro y t ht'
    obtain ⟨hI1, -, hI3, -⟩ := hid y
    have hint : ∀ i, ∫ s in (0 : ℝ)..t, largeEightImgRhoL κ i /
        (rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
          (fun _ => 0) s.toNNReal (x₀, y) - eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i s.toNNReal (x₀, y)) =
        largeEightImgRhoL κ i * ∫ s in (0 : ℝ)..t, (W₂ s.toNNReal y - VL₂ 0 s.toNNReal y)⁻¹ := fun i => by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le t.coe_nonneg] at hs
      have hs' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
      simp only [hI1 _ (hlt y _ (hs'.trans ht')), hI3 i _ (hlt y _ (hs'.trans ht')), div_eq_mul_inv]
    have hsum : ∑ i, largeEightImgRhoL κ i = 0 := by
      simp only [Fin.sum_univ_three, largeEightImgRhoL, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    have hW : W₂ t y = Real.sqrt κ * B₂ t y := by
      have h := drive_eq_extPath_largeEight (h₂.path y) (hlt₂ m y) t ⟨t.coe_nonneg, ht'⟩
      simp only [Real.toNNReal_coe, extPath_coe] at h
      exact h.symm
    unfold seedCapacityNoise
    simp only [hint, ← Finset.sum_mul, hsum, zero_mul, Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
    rw [hI1 t (hlt y t ht'), hW]
    field_simp
  refine ⟨𝓖₂, B₂, h₂.evol.1, hB₂, hE, fun s g hg => ?_, Eventually.of_forall fun y t ht =>
    hNres y t (by rw [← hcap y]; exact ht)⟩
  obtain ⟨r, hr, hcase⟩ := hg
  set E := {y | s < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y)} with hEdef
  have hrE : ∀ y ∈ E, r ≤ eightS₂ x W₂ ζ₂ m y := fun y hy => by
    have h : s < eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 m (x₀, y) := hy
    rw [hcap y] at h
    exact hr.trans h.le
  have hle : 𝓖₂ r ≤ 𝓖₂ s := 𝓖₂.mono hr
  have key : ∀ (f g' : Y → ℝ), (∀ y ∈ E, f y = g' y) → Measurable[𝓖₂ r] g' → ∀ U : Set ℝ, MeasurableSet U →
      MeasurableSet[𝓖₂ s] (f ⁻¹' U ∩ E) := fun f g' hfg hg' U hU =>
    measurableSet_preimage_inter_of_eqOn (𝓜 := {A | MeasurableSet[𝓖₂ s] A}) hfg ((hle _ (hg' hU)).inter (hE s))
  rcases hcase with ⟨U, hU, hA | ⟨i, hA⟩ | ⟨j, hA⟩ | hA⟩ | ⟨k, hA⟩ | hA
  · rw [hA]
    exact key _ (W₂ r) (fun y hy => (hid y).1 r (hlt y r (hrE y hy)))
      (h₂.progW.stronglyAdapted r).measurable U hU
  · rw [hA]
    exact key _ (VL₂ 0 r) (fun y hy => (hid y).2.2.1 i r (hlt y r (hrE y hy)))
      ((h₂.progVL 0).stronglyAdapted r).measurable U hU
  · exact j.elim0
  · rw [hA]
    exact key _ (B₂ r) (fun y hy => (hNres y r (hrE y hy)).symm) (h₂.evol.1.2.1 r) U hU
  · rw [hA]
    have e2 : {y | eightFstCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y) ≤ r} =
        {y | eightS₂ x W₂ ζ₂ k y ≤ r} := by
      ext y
      simp only [Set.mem_ofPred_eq, (hid y).2.2.2 k]
    rw [e2]
    have h := (hS₂ k).measurableSet_le r
    simp only [WithTop.coe_le_coe] at h
    exact (hle _ h).inter (hE s)
  · rw [hA]
    have e3 : {y | (r : ℝ≥0∞) < rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁ (fun _ => 0) (x₀, y)} ∩ E = E := by
      ext y
      refine ⟨fun h => h.2, fun hy => ⟨?_, hy⟩⟩
      show (r : ℝ≥0∞) < rLifeFst _ _ _ _ _ _ _ _
      rw [(hid y).2.1]
      exact hlt y r (hrE y hy)
    rw [e3]
    exact hE s

/-- **The deterministic geometry at the trivial frozen time `σ = 0`** (patched data): up to every cap before
`lifeEnd`, the canonical image (the large curve with its mark `VL₂ 0` in all three slots) is a seeded image geometry of
the initial word `![x, x, x]`. -/
theorem eightFst_geom_zero (hκ8 : 8 ≤ κ) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (x₀ : X) (y : Y) {cap : ℝ≥0}
    (hcap : (cap : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y)) :
    SeedImageGeometry (eightFstWord W₁ VL₁ VR₁ 0 x₀) ![] (largeEightImgRhoL κ) ![]
      (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x W₁
        (fun _ => 0) (min t cap) (x₀, y))
      (fun i t => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i (min t cap) (x₀, y)) (fun j _ => (j.elim0 : ℝ)) cap := by
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  obtain ⟨-, hgood₁, -⟩ := eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cof hne)
  have hζ₁ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt bot_le (hgood₁ 0 x₀).1
  obtain ⟨hI1, -, hI3, -⟩ := eightFst_zero_ident hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ x₀ y
  have hlt : ∀ t : ℝ≥0, ((min t cap : ℝ≥0) : ℝ≥0∞) < lifeEnd (W₂ · y) (VL₂ 0 · y) (ζ₂ y) := fun t =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hcap
  have hζ : ∀ t : ℝ≥0, t ≤ cap → (t : ℝ≥0∞) < ζ₂ y := fun t ht =>
    (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hcap).trans_le (A2X.P3.lifeEnd_le_lifetime _ _ _)
  have ew : (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) x
      W₁ (fun _ => 0) (min t cap) (x₀, y)) = fun t => W₂ (min t cap) y := funext fun t => hI1 _ (hlt t)
  have ev : (fun i t => eightFstVL x W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ 0 i (min t cap) (x₀, y)) =
      fun _ t => VL₂ 0 (min t cap) y := funext fun i => funext fun t => hI3 i _ (hlt t)
  rw [ew, ev]
  obtain ⟨hw0₁, hvl0₁, hvr0₁, -⟩ := h₁.path x₀
  obtain ⟨hw0, hvl0, -, hcw, hcvL, -, -, -, -, -, hint, -, -, hvLeq, -⟩ := id (h₂.path y)
  have hword : ∀ i, eightFstWord W₁ VL₁ VR₁ 0 x₀ i = x := fun i => by
    have h0 := hvr0₁ 0
    have h0' := hvr0₁ 1
    have h1 := hvl0₁ 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h0' h1
    fin_cases i
    · show VR₁ 0 0 x₀ - VR₁ 1 0 x₀ = x
      rw [h0, h0']; ring
    · show W₁ 0 x₀ - VR₁ 1 0 x₀ = x
      rw [show W₁ 0 x₀ = 0 from hw0₁, h0']; ring
    · show VL₁ 0 0 x₀ - VR₁ 1 0 x₀ = x
      rw [h1, h0']; ring
  have hvL0 : VL₂ 0 0 y = x := by simpa using hvl0 0
  have hcmin : Continuous fun t : ℝ≥0 => min t cap := continuous_id.min continuous_const
  have hmem : ∀ t : ℝ≥0, min t cap ∈ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ₂ y} := fun t => hζ _ (min_le_right _ _)
  have hmin : ∀ (t : ℝ≥0) (s : ℝ), s ∈ Icc (0 : ℝ) t → t ≤ cap → min s.toNNReal cap = s.toNNReal :=
    fun t s hs htc => min_eq_left ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans htc)
  refine A1SeedGeom.seedImageGeometry_of_isSeedWord (isSeedWord_eightFstWord hx h₁.path 0 x₀ hζ₁)
    (by rw [min_eq_left (_root_.zero_le : (0 : ℝ≥0) ≤ cap)]; exact hw0) (fun i => by
      rw [min_eq_left (_root_.zero_le : (0 : ℝ≥0) ≤ cap), hvL0, hword]) (fun j => j.elim0)
    (hcw.comp_continuous hcmin hmem) (fun _ => (hcvL 0).comp_continuous hcmin hmem) (fun j => j.elim0)
    (fun t ht i => ?_) (fun t ht j => j.elim0) (fun t ht i => ?_) (fun t ht j => j.elim0) (fun t ht0 ht i => ?_)
    (fun t ht0 ht j => j.elim0)
  · refine (hint t (hζ t ht) 0).congr fun s hs => ?_
    rw [uIoc_of_le t.coe_nonneg] at hs
    simp only [hmin t s ⟨hs.1.le, hs.2⟩ ht]
  · have h := hvLeq t (hζ t ht) 0
    simp only [Matrix.cons_val_zero] at h
    rw [min_eq_left ht, h, hword]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le t.coe_nonneg] at hs
    simp only [hmin t s hs ht]
  · rw [min_eq_left ht]
    exact (A2X.P3.isStripLife_of_lt_lifeEnd (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hcap)).2 t le_rfl

end Frame
end InteractingSLE.ZhanGT4.A1EFam
