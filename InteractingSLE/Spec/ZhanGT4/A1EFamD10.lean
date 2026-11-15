/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1GoodRepl

/-!
# Zhan's A.1 under R83, (Eight), large-curve direction: the (D10) hypotheses at a protected sample

Packet PROVE-A1-EIGHTFAM. A1-EIGHTLAW's `eightFst_isSeedSampleLaw` builds A1-LARGEDENS's frozen-curve hypotheses
`FrzD10Hyp` inside its proof. The family identification (FAMILY's `rDrvFst_eq_seedCapacityDriver`, MULTIMARK's
`rFrzFst_eq_capForce`, FORCES's `seedImageGeometry_rDrvFst_largeEight_force`) needs their consequences at the same
data: the clock facts of the seeded quadratic clock, the forward solutions of the frozen-chart marks and the
separation of the marks from the image driver. This file exposes them.

* **`eightFst_frzD10Hyp`**: at every small sample `x₀` and own time `s ∈ (0, S₁ᵐ(x₀)]`, for every image chain
  `(a, W')` of `√κB₂` against the frozen small hull up to the large exit, the hypotheses `FrzD10Hyp` hold (frozen
  driver `eightDrv − (−x)`, frozen tip and the seeds `x⁺`, `x⁻` as marks);
* **`FrzD10Hyp.clock_facts`**: the clock facts of seeded data carrying the chain (A1-LARGEDENS's `seedClock_facts`);
* **`FrzD10Hyp.frzImg_ne`**: an alive mark's image never meets the image driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1EFam

open QuantumZipper (H fwdMap fwdHull drive IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin A1ELaw
  A1Good A1LargeDens A1Asm

section Frame

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The frozen-curve (D10) hypotheses of the large Eight direction** at a protected small sample: the data of
A1-EIGHTLAW's `eightFst_isSeedSampleLaw`, with the constants of A1-LARGEDENS's `exists_frzD10Hyp_left_marks`. -/
theorem eightFst_frzD10Hyp {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
    {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (m : ℕ) (x₀ : X) {s : ℝ} (hs : 0 < s) (hsS : s ≤ eightS₁ x W₁ ζ₁ m x₀) {a W' : Y → ℝ → ℝ}
    (hown₁ : ∀ y, OwnData (drive κ B₂ y) (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s)
      (frzChart (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s) (eightS₂ x W₂ ζ₂ m y) (a y) (W' y)) :
    ∃ r a₀ γ Γ lam L Tm : ℝ, FrzD10Hyp κ B₂ W' a
      (fwdHull (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s)
      (fun z => fwdMap (fun u => eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ u - -x) s z +
        ((eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ s - -x : ℝ) : ℂ))
      (largeEightRR κ) (eightDrv W₁ (eightS₁ x W₁ ζ₁) m x₀ s - -x)
      ![Strip.extPath (VR₁ 0 · x₀) s - -x, Strip.extPath (VL₁ 0 · x₀) s - -x]
      (eightS₂ x W₂ ζ₂ m) (fun y => (eightS₂ x W₂ ζ₂ m y : ℝ)) r a₀ γ Γ lam L Tm := by
  have hκ : 0 < κ := by linarith
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  obtain ⟨-, hgood₁, hsep₁, hc₂, h0₂, hgood₂, hS₂pos, -⟩ :=
    eight_rect hκ8 hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hpp := hF.pp m
  obtain ⟨-, -, -, hWsc, hsep, hdrive, hK₁, hK₂⟩ := eightFst_frame hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m x₀ hsS
  -- the frozen small curve at `s`: driver, seeds and the protected point
  set S₁ := eightS₁ x W₁ ζ₁ with hS₁def
  have hlt₁ : (S₁ m x₀ : ℝ≥0∞) < ζ₁ x₀ := (hgood₁ m x₀).1
  have hWc : Continuous (eightDrv W₁ S₁ m x₀) := continuous_eightDrv (h₁.path x₀).2.2.2.1 hlt₁
  have hW0 : eightDrv W₁ S₁ m x₀ 0 = 0 := eightDrv_zero (h₁.path x₀).1
  have hne' : ∀ t : ℝ≥0, 0 < t → t ≤ S₁ m x₀ → VL₁ 0 t x₀ ≠ W₁ t x₀ ∧ VR₁ 0 t x₀ ≠ W₁ t x₀ := fun t ht htS =>
    hsep₁ x₀ t ht (lt_of_le_of_lt (ENNReal.coe_le_coe.2 htS) hlt₁)
  have hhi : IsSeedCoordinate (eightDrv W₁ S₁ m x₀) (Strip.extPath (VR₁ 0 · x₀)) (S₁ m x₀) :=
    isSeedCoordinate_vR_of_path (h₁.path x₀) 0 rfl hlt₁ (fun t ht htS => (hne' t ht htS).2)
      (eightDrv_eqOn W₁ S₁ m x₀)
  have hq2 : Disjoint (ball (cofq (-x) ![] m : ℂ) (2 * cofd (-x) ![] m)) (fwdHull (eightDrv W₁ S₁ m x₀) (S₁ m x₀)) :=
    hpp.prot.mono_right ((hgood₁ m x₀).2.2.2.trans subset_union_left)
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_disjoint_ball hWc hW0 hpp.prot_pos.ne' (NNReal.coe_nonneg _)
    (by have := hpp.rad_pos; positivity) hq2
  have hsI : s ∈ Icc (0 : ℝ) (S₁ m x₀) := ⟨hs.le, hsS⟩
  have hgq : fwdMap (eightDrv W₁ S₁ m x₀) s (cofq (-x) ![] m : ℂ) = u s := fwdMap_eq_of_isForwardSol hWc hu hsI
  have hRq : Strip.extPath (VR₁ 0 · x₀) s < (u s).re + eightDrv W₁ S₁ m x₀ s :=
    hhi.lt_gmap hWc (by rw [hW0]; exact hpp.prot_pos) hu hsI
  -- the order of the seeds and the driver at `s`
  have hsN : 0 < s.toNNReal := Real.toNNReal_pos.2 hs
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ₁ x₀ := by
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hlt₁
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.le]; exact hsS
  obtain ⟨hLW, hWR⟩ := hg₁ x₀ s.toNNReal hsN hsζ
  have hWs : eightDrv W₁ S₁ m x₀ s = W₁ s.toNNReal x₀ := eightDrv_eqOn W₁ S₁ m x₀ hsI
  have h1 : Strip.extPath (VL₁ 0 · x₀) s < eightDrv W₁ S₁ m x₀ s := by rw [hWs]; exact hLW
  have h2 : eightDrv W₁ S₁ m x₀ s < Strip.extPath (VR₁ 0 · x₀) s := by rw [hWs]; exact hWR
  set vr := Strip.extPath (VR₁ 0 · x₀) s with hvr
  set vl := Strip.extPath (VL₁ 0 · x₀) s with hvl
  set wv := eightDrv W₁ S₁ m x₀ s with hwv
  -- the marks in A1-LARGEDENS's frame
  have hgqx : (fwdMap (fun u => eightDrv W₁ S₁ m x₀ u - -x) s ((cofq (-x) ![] m + -(-x) : ℝ) : ℂ)).re =
      (u s).re := by
    rw [fwdMap_sub_const]
    have e : (((cofq (-x) ![] m + -(-x) : ℝ) : ℂ) + ((-x : ℝ) : ℂ)) = (cofq (-x) ![] m : ℂ) := by push_cast; ring
    rw [e, hgq]
  set ν := min (min (vr - wv) (wv - vl)) (vr - vl) with hν
  have hνpos : 0 < ν := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hν1 : ν ≤ vr - wv := (min_le_left _ _).trans (min_le_left _ _)
  have hν2 : ν ≤ wv - vl := (min_le_left _ _).trans (min_le_right _ _)
  have hν3 : ν ≤ vr - vl := min_le_right _ _
  have hζq : ∀ k, ![vr - -x, vl - -x] k <
      (fwdMap (fun u => eightDrv W₁ S₁ m x₀ u - -x) s ((cofq (-x) ![] m + -(-x) : ℝ) : ℂ)).re +
        (fun u => eightDrv W₁ S₁ m x₀ u - -x) s := by
    intro k
    rw [hgqx]
    fin_cases k
    · show vr - -x < (u s).re + (wv - -x)
      linarith
    · show vl - -x < (u s).re + (wv - -x)
      linarith
  have hζM : ∀ k, |![vr - -x, vl - -x] k| ≤ |vr - -x| + |vl - -x| := by
    intro k
    fin_cases k
    · show |vr - -x| ≤ _
      linarith [abs_nonneg (vl - -x)]
    · show |vl - -x| ≤ _
      linarith [abs_nonneg (vr - -x)]
  have hζν : ∀ k, ν ≤ |![vr - -x, vl - -x] k - (fun u => eightDrv W₁ S₁ m x₀ u - -x) s| := by
    intro k
    fin_cases k
    · show ν ≤ |vr - -x - (wv - -x)|
      rw [abs_of_pos (by linarith)]; linarith
    · show ν ≤ |vl - -x - (wv - -x)|
      rw [abs_of_neg (by linarith)]; linarith
  have hζνmk : ∀ k l, k ≠ l → ν ≤ |![vr - -x, vl - -x] k - ![vr - -x, vl - -x] l| := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · exact absurd rfl hkl
    · show ν ≤ |vr - -x - (vl - -x)|
      rw [abs_of_pos (by linarith)]; linarith
    · show ν ≤ |vl - -x - (vr - -x)|
      rw [abs_of_neg (by linarith)]; linarith
    · exact absurd rfl hkl
  have hqneg : cofq (-x) ![] m + -(-x) < 0 := by linarith [hpp.prot_lt]
  have hqH := disjoint_ball_transl hpp.prot (-(-x))
  have hqH' : Disjoint (ball ((cofq (-x) ![] m + -(-x) : ℝ) : ℂ) (2 * cofd (-x) ![] m))
      (transl (-(-x)) (cofH₂ (-x) ![] m) ∪ transl (-(-x)) (cofH₁ (-x) ![] m)) := by
    have e : transl (-(-x)) (cofH₂ (-x) ![] m) ∪ transl (-(-x)) (cofH₁ (-x) ![] m) =
        transl (-(-x)) (cofH₁ (-x) ![] m ∪ cofH₂ (-x) ![] m) := by
      unfold transl; rw [image_union, union_comm]
    rw [e]; exact hqH
  have hW₂H : (((fun u => eightDrv W₁ S₁ m x₀ u - -x) 0 : ℝ) : ℂ) ∈ closure (transl (-(-x)) (cofH₁ (-x) ![] m)) := by
    have h0 := mem_closure_transl (hF.zero_mem_closure₁ m) (-(-x))
    have e : (((fun u => eightDrv W₁ S₁ m x₀ u - -x) 0 : ℝ) : ℂ) = 0 + ((-(-x) : ℝ) : ℂ) := by
      simp only [hW0]; push_cast; ring
    rw [e]; exact h0
  have hqW : (fun u => eightDrv W₁ S₁ m x₀ u - -x) 0 < cofq (-x) ![] m + -(-x) := by
    simp only [hW0]; linarith [hpp.prot_pos]
  have := nonempty_of_isFilteredBrownianReal h₂.evol.1
  obtain ⟨r, a₀, γ, Γ, lam, L, hmain⟩ :=
    exists_frzD10Hyp_left_marks (Ω := Y) (hF.hull₂ m) (isHPHull_transl hpp.hull₁ _) hpp.sep_pos hsep hpp.rad_pos
      hqneg hqH' (M := |vr - -x| + |vl - -x|) hνpos 2 (cofTm (-x) ![] m)
  exact ⟨r, a₀, γ, Γ, lam, L, cofTm (-x) ![] m, hmain κ B₂ W' a (largeEightRR κ) ![vr - -x, vl - -x]
    (fun u => eightDrv W₁ S₁ m x₀ u - -x) s (eightS₂ x W₂ ζ₂ m) (fun y => (eightS₂ x W₂ ζ₂ m y : ℝ)) hown₁
    (fun y => le_rfl) (fun y => (hgood₂ m y).1) hK₁ hWsc hW₂H hqW hs (hsS.trans (hgood₁ m x₀).2.2.1) hK₂ hζq hζM
    hζν hζνmk⟩

end Frame

end InteractingSLE.ZhanGT4.A1EFam
