/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawFst
import InteractingSLE.Spec.ZhanGT4.A1G3LawFstFam
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndId
import InteractingSLE.Spec.ZhanGT4.A1GoodEight

/-!
# G3 large direction: protected enclosures and good horizons

The large driver is stopped at its rectangle exit, so it is continuous at every sample.
The enclosure and good-time results below use only the two regular marginals.
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

/-- The cofinal G3 rectangles provide separated enclosures in the large curve's frame. -/
theorem g3Fst_frame (k : ℕ) (x₀ : X) {s : ℝ} (hsS : s ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    Continuous (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) ∧
    (∀ y₀, (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < ζ₂ y₀) ∧
    (∀ y₀, 0 < (g3S₂ x y W₂ ζ₂ k y₀ : ℝ)) ∧
    (∀ y₀, (g3S₂ x y W₂ ζ₂ k y₀ : ℝ) ≤ cofGTm (-y) (x - y) ![x - y] k) ∧
    (∀ y₀, fwdHull (Strip.extPath (W₂ · y₀)) (g3S₂ x y W₂ ζ₂ k y₀) ⊆
      transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] k)) ∧
    (∀ y₀, fwdHull (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
      (g3S₂ x y W₂ ζ₂ k y₀) ⊆ transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] k)) ∧
    fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) s ⊆
      transl (-(-y)) (cofGH₁ (-y) (x - y) ![x - y] k) := by
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, -, -, -, -, -, hgood₂, hpos₂, hlt₂⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hK₂ : ∀ y₀, fwdHull (Strip.extPath (W₂ · y₀)) (g3S₂ x y W₂ ζ₂ k y₀) ⊆
      transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] k) := by
    intro y₀
    have he : g3S₂ x y W₂ ζ₂ k y₀ = lifeExit (W₂ · y₀) (ζ₂ y₀)
        (transl (-(-y)) (cofGH₂ (-y) (x - y) ![x - y] k))
        (cofGN (-y) (x - y) ![x - y] k) := by
      rw [g3S₂, lifeExit_add_const, ← transl_neg_eq_preimage]
    rw [he]
    exact fwdHull_lifeExit_subset (h₂.path y₀).2.2.2.1 (h₂.path y₀).1
      (hF.hull₂ k) (by rw [← he]; exact hlt₂ k y₀)
  refine ⟨(continuous_eightDrv (h₁.path x₀).2.2.2.1 (hgood₁ k x₀).1).sub continuous_const,
    hlt₂ k, hpos₂ k, fun y₀ => (hgood₂ k y₀).1, hK₂, fun y₀ => ?_, ?_⟩
  · rw [show eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀ =
        stopDrv (Strip.extPath (W₂ · y₀)) (g3S₂ x y W₂ ζ₂ k y₀) from rfl]
    obtain ⟨r, hr, hcr⟩ :=
      exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 (hlt₂ k y₀)
    have he : fwdHull (stopDrv (Strip.extPath (W₂ · y₀)) (g3S₂ x y W₂ ζ₂ k y₀))
        (g3S₂ x y W₂ ζ₂ k y₀) = fwdHull (Strip.extPath (W₂ · y₀))
        (g3S₂ x y W₂ ζ₂ k y₀) :=
      A1Common.fwdHull_stopDrv_self (S := (g3S₂ x y W₂ ζ₂ k y₀ : ℝ))
        (NNReal.coe_nonneg _) hr hcr
    exact he ▸ hK₂ y₀
  · rw [fwdHull_sub_const]
    exact image_mono ((QuantumZipper.fwdHull_mono.1 hsS).trans (hgood₁ k x₀).2.2.2)

/-- A continuous image chain exists for the stopped large driver against a protected small prefix. -/
theorem exists_ownData_g3Fst (k : ℕ) (x₀ : X) {s : ℝ} (hs : 0 < s)
    (hsS : s ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    ∃ a W' : Y → ℝ → ℝ, ∀ y₀,
      OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
        (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) s)
        (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) s)
        (g3S₂ x y W₂ ζ₂ k y₀) (a y₀) (W' y₀) := by
  obtain ⟨hWc, hlt, hpos, -, -, hK₂, hK₁⟩ :=
    g3Fst_frame hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k x₀ hsS
  have hqlo : 0 < x - y := sub_pos.2 hyx
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun i => by fin_cases i; simp; linarith)
      (fun i => by fin_cases i; simp; linarith)
  have hpp := (isEnclFamily_cofG hne).pp k
  have hc : ∀ y₀, Continuous (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀) := fun y₀ =>
    continuous_eightDrv (h₂.path y₀).2.2.2.1 (hlt y₀)
  have h0 : ∀ y₀, eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀ 0 = 0 := fun y₀ =>
    eightDrv_zero (h₂.path y₀).1
  have h : ∀ y₀, ∃ a W', OwnData (eightDrv W₂ (g3S₂ x y W₂ ζ₂) k y₀)
      (fwdHull (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) s)
      (frzChart (fun u => eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀ u - -y) s)
      (g3S₂ x y W₂ ζ₂ k y₀) a W' := fun y₀ =>
    exists_ownData_of_encl (hc y₀) (h0 y₀) (hpos y₀) hWc hs.le hpp.sep_pos
      (fun a ha b hb => by rw [norm_sub_rev]; exact sep_transl hpp.sep _ b hb a ha)
      (hK₂ y₀) hK₁
  choose a W' haW using h
  exact ⟨a, W', haW⟩

end InteractingSLE.ZhanGT4.A1G3Lg
