/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgFrame

/-!
# G3 large direction: force gaps and canonical good horizons

The protected exits precede the strip lifetime of the large curve and the first
contact with every protected small prefix.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap drive IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y]
    (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω)
    (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- Both large force gaps have a positive deterministic lower bound on the rectangle. -/
theorem g3Fst_gaps (k : ℕ) (x₀ : X) :
    ∃ δ R : ℝ, 0 < δ ∧ ∀ y₀,
      A1G3Id.G3Field.PathOn κ ![x, y] ![] ![] W₂ VL₂ VR₂ B₂ ζ₂ y₀
        (g3S₂ x y W₂ ζ₂ k y₀) δ ∧
      ∀ r : ℝ≥0, r ≤ g3S₂ x y W₂ ζ₂ k y₀ → ∀ i, |W₂ r y₀ - VL₂ i r y₀| ≤ R := by
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, -, -, -, -, -, -, hgood₂, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨-, hlt, -, -, hK₂, -, -⟩ :=
    g3Fst_frame hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ (s := 0) (NNReal.coe_nonneg _)
  exact g3_large_gaps (xR := ![0, x - y, -y]) (isProtectedPairG_cofG hne k)
    (by simpa using hqlo) (by simpa using qlo_le_cofGq hne k)
    (hF.zero_mem_closure₁ k) h₂ (by simp) (by simp) hlt (hgood₂ k) hK₂

/-- The rectangle exit is strictly before the canonical strip lifetime of the inner mark. -/
theorem g3Fst_lt_lifeEnd (k : ℕ) (x₀ : X) (y₀ : Y) :
    (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀) := by
  obtain ⟨δ, R, hδ, hp⟩ := g3Fst_gaps hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
  have h := (hp y₀).1
  refine A2X.P3.lt_lifeEnd_of_isStripLife h.path.2.2.2.1 (h.path.2.2.2.2.1 0)
    ⟨h.lt, fun r hr => ?_⟩
  have hrζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) h.lt
  have hle := vL_le_of_path h.path 0 hrζ (W := Strip.extPath (W₂ · y₀))
    (fun _ _ => rfl) r ⟨r.coe_nonneg, le_rfl⟩
  simp only [extPath_coe] at hle
  refine lt_of_le_of_ne hle fun he => ?_
  change VL₂ 0 r y₀ = W₂ r y₀ at he
  have hg := h.gap r hr 0
  rw [he, sub_self, abs_zero] at hg
  linarith

/-- At every protected positive frozen time, the canonical large exit is a good horizon. -/
theorem g3Fst_isGoodTime (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀))
      (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ (g3S₂ x y W₂ ζ₂ k y₀) := by
  obtain ⟨a, W', hown⟩ := exists_ownData_g3Fst hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
    (by exact_mod_cast hσ) (by exact_mod_cast hσS)
  have h := hown y₀
  have hlife := g3Fst_lt_lifeEnd hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ y₀
  have hlt : (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < ζ₂ y₀ := hlife.trans_le (lifeEnd_le _ _ _)
  obtain ⟨T', hT', hcT'⟩ := exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 hlt
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  obtain ⟨-, hgood₁, -, -, -, -, -, -, -, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
  obtain ⟨r, hr, hcr⟩ := exists_continuousOn_extPath_beyond (h₁.path x₀).2.2.2.1 (hgood₁ k x₀).1
  have hcsmall : Continuous (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀) :=
    continuous_eightDrv (h₁.path x₀).2.2.2.1 (hgood₁ k x₀).1
  have heq : physHull y (Strip.extPath (W₁ · x₀)) σ =
      fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ := by
    rw [A1G3Row.fwdHull_sub_const_eq_physHull, neg_neg]
    exact A1SeedGeom.physHull_congr_of_continuousOn hcr hcsmall.continuousOn
      σ.coe_nonneg ((NNReal.coe_le_coe.2 hσS).trans_lt hr)
      (fun u hu => (eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀
        ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hσS)⟩).symm)
  refine A1Good.isGoodTime_of_disjoint_loc hT' hcT' h.pos
    (by rwa [ENNReal.ofReal_coe_nnreal]) ?_
  rw [heq, A1Ref.physHull_zero,
    ← A1Common.fwdHull_stopDrv_self (NNReal.coe_nonneg _) hT' hcT']
  exact h.disj.symm

end InteractingSLE.ZhanGT4.A1G3Lg

