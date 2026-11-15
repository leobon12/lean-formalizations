/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LgGood
import InteractingSLE.Spec.ZhanGT4.A1G3LgMarks
import InteractingSLE.Spec.ZhanGT4.A1G3LawCol
import InteractingSLE.Spec.ZhanGT4.A1LargeDensD9

/-!
# G3 large direction: frozen-curve geometric hypotheses

Protected G3 rectangles and their frozen marked points supply the geometric
hypotheses of the landed frozen-curve density theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Lg

open QuantumZipper (fwdHull fwdMap drive IsForwardSol)
open A2X A1Ref A1Marg A1SeedField A1EightSeed A1EightFin A1G3Calc A1Common A1Asm
  A1G3Law A1ELaw A1G3RR A1G3Id Girsanov A1G3Row A1LargeDens A1MultiMark A1Family

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y}
  {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable [IsProbabilityMeasure P₂]
  [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous]

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y]
    (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω)
    (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- The frozen-curve geometric hypotheses hold for any continuous replacement driver
agreeing with the large driver before its protected exit. -/
theorem g3Fst_d10Hyp (k : ℕ) (x₀ : X) {σ : ℝ≥0} (hσ : 0 < σ)
    (hσS : σ ≤ g3S₁ x y W₁ ζ₁ k x₀) {B : ℝ≥0 → Y → ℝ} {a W' : Y → ℝ → ℝ}
    (hown₁ : ∀ y₀, OwnData (drive κ B y₀)
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
      (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀))
    (hdrive : ∀ y₀, EqOn (drive κ B y₀) (Strip.extPath (W₂ · y₀))
      (Icc 0 (g3S₂ x y W₂ ζ₂ k y₀ : ℝ))) :
    ∃ r a₀ γ Γ lam L : ℝ,
      FrzD10Hyp κ B W' a
        (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
        (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ)
        (largeG3RR κ) (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ σ - -y)
        ![VR₁ 1 σ x₀ - -y, VR₁ 0 σ x₀ - -y, VL₁ 0 σ x₀ - -y]
        (g3S₂ x y W₂ ζ₂ k) (fun y₀ => (g3S₂ x y W₂ ζ₂ k y₀ : ℝ))
        r a₀ γ Γ lam L (cofGTm (-y) (x - y) ![x - y] k) := by
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  have hF := isEnclFamily_cofG hne
  have hpp := isProtectedPairG_cofG hne k
  obtain ⟨-, hgood₁, -, -, -, -, -, hgood₂, hpos₂, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  obtain ⟨hWsc, -, -, -, -, hKs, hKf⟩ :=
    g3Fst_frame hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ (NNReal.coe_le_coe.2 hσS)
  have hK0 : ∀ y₀, fwdHull (drive κ B y₀) (g3S₂ x y W₂ ζ₂ k y₀) ⊆
      transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] k) := by
    intro y₀
    have hst : Continuous (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀) :=
      continuous_eightDrv (h₂.path y₀).2.2.2.1
        (by
          obtain ⟨-, hlt, -⟩ := g3Fst_frame hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀
            (NNReal.coe_le_coe.2 hσS)
          exact hlt y₀)
    rw [← YuanCorollary13.fwdHull_eq_of_eqOn_Icc hst (hown₁ y₀).cont
      (NNReal.coe_nonneg _) (fun u hu =>
        (eightDrv_eqOn W₂ (g3S₂ x y W₂ ζ₂) k y₀ hu).trans ((hdrive y₀ hu).symm))]
    exact hKs y₀
  obtain ⟨yref⟩ := nonempty_of_isProbabilityMeasure P₂
  have : Nonempty Y := ⟨yref⟩
  obtain ⟨-, hrec, -⟩ := g3_isSourceColumnG hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k yref
    (hpos₂ k yref) le_rfl
  have hlo := vL_le_of_path (h₁.path x₀) 0 (hgood₁ k x₀).1
    (eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀)
  have hhi := le_vR_of_path (h₁.path x₀) 0 (hgood₁ k x₀).1
    (eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀)
  have hset := g3Setup_of_isSourceRecordG hpp (hrec x₀) rfl rfl
    (fun t ht => Icc_subset_uIcc ⟨hlo t ht, hhi t ht⟩)
  have hs : (σ : ℝ) ∈ Ioc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀) :=
    ⟨by exact_mod_cast hσ, NNReal.coe_le_coe.2 hσS⟩
  let V : Fin 3 → ℝ := fun i => g3Marks VL₁ VR₁ x₀ (Fin.rev i) σ
  have hV : V = ![VR₁ 1 σ x₀, VR₁ 0 σ x₀, VL₁ 0 σ x₀] := by
    funext i
    fin_cases i <;> norm_num [V, g3Marks, Fin.rev, Strip.extPath]
  obtain ⟨ν, M, hν, hdL, hqL, hqH, hqW, hζq, hζM, hζν, hζνmk⟩ :=
    frozen_mark_frame (V := V) hpp.pair hset.view.cont₁ hset.view.zero₁ hset.view.pos₁ hset.view.K₁ hs
      (fun i => A1G3RR.G3Setup.marks_le hset hs (hlo σ (Ioc_subset_Icc_self hs)) (Fin.rev i))
      (fun i => (hset.mark (Fin.rev i)).ne σ hs)
      ((hset.inj σ hs).comp Fin.rev_injective)
  have hζvec : (fun i => V i - -y) = ![VR₁ 1 σ x₀ - -y, VR₁ 0 σ x₀ - -y, VL₁ 0 σ x₀ - -y] := by
    rw [hV]; funext i; fin_cases i <;> rfl
  have hζval := fun i => congrFun hζvec i
  simp_rw [hζval] at hζq hζM hζν hζνmk
  have hW0 := eightDrv_zero (S₁ := g3S₁ x y W₁ ζ₁) (m := k) (h₁.path x₀).1
  have hWfH : (((fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) 0 : ℝ) : ℂ) ∈
      closure (transl (-(-y)) (cofGH₁ (-y) (x - y) ![x - y] k)) := by
    have h := mem_closure_transl (hF.zero_mem_closure₁ k) (-(-y))
    simpa only [hW0, zero_sub, ofReal_neg, ofReal_zero, zero_add] using h
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ := exists_frzD10Hyp_left_marks
    (hF.hull₂ k) (isHPHull_transl hpp.pair.hull₁ _) hpp.pair.sep_pos
    (A1ELaw.sep_transl hpp.pair.sep _) hdL hqL hqH (M := M) hν 3
    (cofGTm (-y) (x - y) ![x - y] k)
  exact ⟨r, a₀, γ, Γ, lam, L, hH κ B W' a (largeG3RR κ)
    ![VR₁ 1 σ x₀ - -y, VR₁ 0 σ x₀ - -y, VL₁ 0 σ x₀ - -y]
    (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) σ
    (g3S₂ x y W₂ ζ₂ k) (fun y₀ => (g3S₂ x y W₂ ζ₂ k y₀ : ℝ)) hown₁
    (fun _ => le_rfl) (fun y₀ => (hgood₂ k y₀).1) hK0 hWsc hWfH hqW
    hs.1 (hs.2.trans (hgood₁ k x₀).2.2.1) hKf hζq hζM hζν hζνmk⟩

end InteractingSLE.ZhanGT4.A1G3Lg
