/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightSeedCongr
import InteractingSLE.Spec.ZhanGT4.MTildeMartFrozen

/-!
# Zhan's A.1 (R80): the frozen-curve logarithm `ℓ` reads its data at `t` and the own maps on `[0, t]`, and does not
see the order of the marks

Packet PROVE-A1-G3ROW. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407: the
density (D6) "with the conformal map of `K₂(I)` frozen" is a function of the stopped paths alone, a product over the
marks).

The large-curve direction has two descriptions of the same frozen-curve density `M̃`: A1-EIGHTFIN's opposite view
`eView` (image chain chosen by A15's `tSel`, marks in the small curve's order `x⁻, x⁺`) and A1-LARGEDENS's
`frzDataOf` (image chain of the large Brownian driver, marks in the image word's order `x⁺, x⁻`). This file proves
that they have the same logarithm:

* **`pairSum_comp_perm`**: the pair sum of a symmetric function is invariant under a permutation of the indices
  (`two_mul_pairSum`: `2 Σ_{m<k} f = Σ_{m,k} f − Σ_m f m m`);
* **`FrzData.ell_congr_perm`**: two frozen data with the same parameter, own maps and driver on `[0, t]`, the same
  image chain at `t`, the same tip, and charges/marks that agree up to a permutation `e`, have the same `ℓ(t, ·)`;
* **`FrzData.ell_congr_of_ownData`**: the own maps and image chains agree when the two drivers agree on `[0, U]` and
  both carry an image chain (`OwnData`) against the same frozen hull and chart (A1-EIGHTSEED's `OwnData` congruence).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H fwdMap fwdHull)

/-! ### Pair sums of symmetric functions -/

section PairSum

variable {n : ℕ}

/-- **`2 Σ_{m<k} f m k = Σ_{m,k} f m k − Σ_m f m m`** for a symmetric `f`. -/
theorem two_mul_pairSum {f : Fin n → Fin n → ℝ} (hf : ∀ m k, f m k = f k m) :
    2 * pairSum f = ∑ p : Fin n × Fin n, f p.1 p.2 - ∑ m, f m m := by
  set g : Fin n × Fin n → ℝ := fun p => f p.1 p.2 with hg
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n × Fin n))
    (fun p => p.1 < p.2) g
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)) (fun p => p.1 = p.2) g
  have hdiag : ∑ p ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => p.1 = p.2), g p = ∑ m, f m m := by
    refine Finset.sum_nbij' Prod.fst (fun m => (m, m)) (fun _ _ => Finset.mem_univ _) (fun m _ => ?_)
      (fun p hp => ?_) (fun _ _ => rfl) (fun p hp => ?_)
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact Prod.ext rfl hp.2
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [hg]
      rw [hp.2]
  have hlow : ∑ p ∈ ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => ¬ p.1 = p.2), g p = pairSum f := by
    unfold pairSum
    refine Finset.sum_nbij' Prod.swap Prod.swap (fun p hp => ?_) (fun p hp => ?_)
      (fun p _ => Prod.swap_swap p) (fun p _ => Prod.swap_swap p) (fun p _ => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp ⊢
      exact lt_of_le_of_ne hp.1 (Ne.symm hp.2)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp ⊢
      exact ⟨hp.le, hp.ne'⟩
    · simp only [hg, Prod.fst_swap, Prod.snd_swap]
      exact hf _ _
  have hupper : ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), g p = pairSum f := rfl
  have hfull : ∑ p : Fin n × Fin n, f p.1 p.2 = ∑ p : Fin n × Fin n, g p := rfl
  rw [hfull, ← hsplit, ← hsplit2, hdiag, hlow, hupper]
  ring

/-- **The pair sum of a symmetric function does not see the order of the indices.** -/
theorem pairSum_comp_perm {f : Fin n → Fin n → ℝ} (hf : ∀ m k, f m k = f k m) (e : Equiv.Perm (Fin n)) :
    pairSum (fun m k => f (e m) (e k)) = pairSum f := by
  have h₁ := two_mul_pairSum (f := fun m k => f (e m) (e k)) fun m k => hf _ _
  have h₂ := two_mul_pairSum hf
  have hs : ∑ p : Fin n × Fin n, f (e p.1) (e p.2) = ∑ p : Fin n × Fin n, f p.1 p.2 :=
    Equiv.sum_comp (e.prodCongr e) fun p => f p.1 p.2
  have hd : ∑ m, f (e m) (e m) = ∑ m, f m m := Equiv.sum_comp e fun m => f m m
  rw [hs, hd] at h₁
  linarith

end PairSum

/-! ### Congruence of the frozen-curve logarithm -/

namespace FrzData

variable {n : ℕ}

/-- **Congruence of `ℓ` up to a permutation of the marks**: two frozen data with the same parameter, the same own maps
and driver on `[0, t]`, the same image chain at `t` (forward map and driver value at the clock), the same tip, and
charges and marks `d₂.r = d₁.r ∘ e`, `d₂.ζ = d₁.ζ ∘ e`, have the same logarithm `ℓ(t, x)` at every `x`. -/
theorem ell_congr_perm {d₁ d₂ : FrzData n} {t : ℝ} (ht : 0 ≤ t) (hκ : d₁.κ = d₂.κ) (e : Equiv.Perm (Fin n))
    (hr : ∀ m, d₂.r m = d₁.r (e m))
    (hext : ∀ v ∈ Icc (0 : ℝ) t, ownExt d₁.W d₁.W' d₁.a d₁.φ v = ownExt d₂.W d₂.W' d₂.a d₂.φ v)
    (hW : ∀ v ∈ Icc (0 : ℝ) t, d₁.W v = d₂.W v) (hmap : fwdMap d₁.W' (d₁.a t) = fwdMap d₂.W' (d₂.a t))
    (hdrv : d₁.W' (d₁.a t) = d₂.W' (d₂.a t)) (hζ₀ : d₁.ζ₀ = d₂.ζ₀) (hζ : ∀ m, d₂.ζ m = d₁.ζ (e m)) (x : ℝ) :
    d₁.ell t x = d₂.ell t x := by
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hF : ∀ k, d₁.F k t = d₂.F k t := fun k => by
    funext y
    unfold F
    rw [hext t htt]
  have hA20 : d₁.A20 t = d₂.A20 t := by
    unfold A20 frzImg
    rw [hmap, hdrv, hζ₀]
  have hA21 : d₁.A21 t = d₂.A21 t := by
    unfold A21 frzImgD
    rw [hmap, hζ₀]
  have hB0 : ∀ m, d₂.B0 t m = d₁.B0 t (e m) := fun m => by
    unfold B0 frzImg
    rw [hmap, hdrv, hζ]
  have hB1 : ∀ m, d₂.B1 t m = d₁.B1 t (e m) := fun m => by
    unfold B1 frzImgD
    rw [hmap, hζ]
  have hL : frzLogF d₁.W d₁.W' d₁.a d₁.φ t = frzLogF d₂.W d₂.W' d₂.a d₂.φ t := by
    unfold frzLogF
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [uIcc_of_le ht] at hv
    unfold frzRate frzA
    rw [hext v hv, hW v hv]
  have hsum₁ : ∑ m, (dualGamma d₂.κ (d₂.r m) * Real.log (d₂.B1 t m) +
      -(d₂.κ / 4) * d₂.r m * Real.log (d₂.A20 t - d₂.B0 t m)) =
      ∑ m, (dualGamma d₁.κ (d₁.r m) * Real.log (d₁.B1 t m) +
        -(d₁.κ / 4) * d₁.r m * Real.log (d₁.A20 t - d₁.B0 t m)) := by
    simp only [hr, hB1, hB0, ← hκ, ← hA20]
    exact Equiv.sum_comp e fun m => dualGamma d₁.κ (d₁.r m) * Real.log (d₁.B1 t m) +
      -(d₁.κ / 4) * d₁.r m * Real.log (d₁.A20 t - d₁.B0 t m)
  have hpair : pairSum (fun m k => dualDelta d₂.κ (d₂.r m) (d₂.r k) * Real.log (d₂.B0 t m - d₂.B0 t k)) =
      pairSum (fun m k => dualDelta d₁.κ (d₁.r m) (d₁.r k) * Real.log (d₁.B0 t m - d₁.B0 t k)) := by
    simp only [hr, hB0, ← hκ]
    refine pairSum_comp_perm (f := fun m k => dualDelta d₁.κ (d₁.r m) (d₁.r k) *
      Real.log (d₁.B0 t m - d₁.B0 t k)) (fun m k => ?_) e
    rw [← Real.log_neg_eq_log, neg_sub]
    unfold dualDelta
    ring
  have hsumS : ∑ m, d₂.r m * Real.log (d₂.F 0 t x - d₂.B0 t m) =
      ∑ m, d₁.r m * Real.log (d₁.F 0 t x - d₁.B0 t m) := by
    simp only [hr, hB0, ← hF]
    exact Equiv.sum_comp e fun m => d₁.r m * Real.log (d₁.F 0 t x - d₁.B0 t m)
  unfold ell LT LS dualLogTime dualLogSpace
  rw [hsum₁, hpair, hsumS, hL, hA21, hA20, hκ]
  simp only [hF]

/-- **`ℓ` of two image chains of drivers agreeing on `[0, U]`**, against the same frozen hull `A` and chart `φ`, with
the same parameter and tip and with charges and marks agreeing up to a permutation `e`: the logarithms agree at every
`t ≤ min (min T₁ T₂) U` (A1-EIGHTSEED's `OwnData` congruence: same clock, image driver and own maps). -/
theorem ell_congr_of_ownData {d₁ d₂ : FrzData n} {A : Set ℂ} {φ : ℂ → ℂ} {T₁ T₂ U : ℝ}
    (h₁ : OwnData d₁.W A φ T₁ d₁.a d₁.W') (h₂ : OwnData d₂.W A φ T₂ d₂.a d₂.W') (hφ₁ : d₁.φ = φ) (hφ₂ : d₂.φ = φ)
    (hW : EqOn d₁.W d₂.W (Icc 0 U)) (hκ : d₁.κ = d₂.κ) (e : Equiv.Perm (Fin n)) (hr : ∀ m, d₂.r m = d₁.r (e m))
    (hζ₀ : d₁.ζ₀ = d₂.ζ₀) (hζ : ∀ m, d₂.ζ m = d₁.ζ (e m)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (min (min T₁ T₂) U))
    (x : ℝ) : d₁.ell t x = d₂.ell t x := by
  have hsub : ∀ v ∈ Icc (0 : ℝ) t, v ∈ Icc (0 : ℝ) (min (min T₁ T₂) U) := fun v hv => ⟨hv.1, hv.2.trans ht.2⟩
  refine ell_congr_perm ht.1 hκ e hr (fun v hv => ?_) (fun v hv => hW ⟨(hsub v hv).1,
    (hsub v hv).2.trans (min_le_right _ _)⟩) (OwnData.fwdMap_img_eq_of_eqOn h₁ h₂ hW ht)
    (OwnData.imgDrv_clock_eq_of_eqOn h₁ h₂ hW ht) hζ₀ hζ x
  rw [hφ₁, hφ₂]
  exact OwnData.ownExt_congr_of_eqOn h₁ h₂ hW (hsub v hv)

end FrzData

end InteractingSLE.ZhanGT4
