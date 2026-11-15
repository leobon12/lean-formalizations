/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteBounds

/-!
# The deterministic seeded (D9) bound

Packet PROVE-ZHAN-GT4-A22. The previously explicit separated-source
scale is now supplied by the protected enclosures and the original flow.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (fwdMap fwdHull)

/-- **Seeded (D9), with all scales obtained from the enclosures.** The finite
marks belong to the seed-coordinate interval; no positive lower bound for
their own gaps is assumed or needed in this estimate. -/
theorem exists_seeded_d9_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hpH₂ : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (Tm κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) (Vhi t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) (Vhi t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂)
            κ rr (W₂ t₂) p V).normEll t| ≤ coefTot κ rr * L := by
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right hH₁ hH₂ hδ hsep hpH₂ hq hqp hd hqH Tm
  obtain ⟨r, L, hr, hL, hb⟩ :=
    exists_abs_normEll_le_right_of_remote_scale hH₁ hH₂ hδ hsep hd hqH Tm Lrem κ rr
  refine ⟨r, L, hr, hL, ?_⟩
  intro W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI
  let s := SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V
  have hW0H : (W 0 : ℂ) ∈ closure H₁ :=
    closure_mono hK₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rwa [hW₂0]
  exact hb s W₂ Vlo Vhi T t₂ h rfl rfl rfl hW₂ ht₂ ht₂m hW0H hW₂H
    (by change W 0 < q; rwa [h.zero]) (by rwa [hW₂0]) hK₁ hK₂ hlo hhi hWI hVI
    (hrem κ rr W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI)

namespace SeedData

/-- The separated-source scales supply every remote noncollision in the
band family. Positive interval derivatives supply the image noncollisions. -/
theorem gapVal_ne_zero_of_remoteScale {n : ℕ} (s : SeedData n) {t L : ℝ} {I : Set ℝ}
    (hremote : s.RemoteScale t L) (hI : Convex ℝ I)
    (hd : DifferentiableOn ℝ (s.F 0 t) I) (hder : ∀ x ∈ I, 0 < deriv (s.F 0 t) x)
    (hF1 : ∀ x ∈ I, s.F 1 t x = deriv (s.F 0 t) x)
    (hW : s.W t ∈ I) (hV : ∀ m, s.V m t ∈ I)
    (hVW : ∀ m, s.V m t ≠ s.W t) (hVV : Function.Injective (fun m => s.V m t)) :
    ∀ i, s.gapVal i t ≠ 0 := by
  have nz : ∀ {u : ℝ}, InScale L u → u ≠ 0 := by
    intro u hu he
    change Real.exp (-L) ≤ |u| ∧ |u| ≤ Real.exp L at hu
    rw [he, abs_zero] at hu
    exact (not_le_of_gt (Real.exp_pos _)) hu.1
  have h0 := (div_ne_zero_iff.1 (nz hremote.driver))
  have hm := fun m => div_ne_zero_iff.1 (nz (hremote.mark m))
  exact s.gapVal_ne_zero_of_deriv hI hd hder hF1 hW hV (nz hremote.A21)
    (sub_ne_zero.1 h0.1).symm (fun m => sub_ne_zero.1 (hm m).1)
    (sub_ne_zero.1 h0.2).symm hVW (fun m => sub_ne_zero.1 (hm m).2) hVV

end SeedData

end InteractingSLE.ZhanGT4
