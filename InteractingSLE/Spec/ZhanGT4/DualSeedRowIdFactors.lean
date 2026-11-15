/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdData

/-!
# The concrete common factors of the seeded rectangle

Packet PROVE-ZHAN-GT4-A22. Reuse the two-view tip identities and transport
each integrated seed through its actual protected chart neighbourhood.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
namespace TwoViewRect
variable {n : ℕ} {κ S T : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ}
  {as Ws bt Wt : ℝ → ℝ → ℝ} {V : Fin n → ℝ → ℝ}
  (h : TwoViewRect W₁ W₂ S T as Ws bt Wt)
include h

/-- The actual mutual-tip values and derivatives in the seeded views.
These are independent of whether the remaining accesses are seeds. -/
theorem seed_tip_factors {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) T) :
    (seedTView κ r W₁ W₂ bt Wt V s).F 0 t (W₂ t - W₂ 0) =
        (seedSView κ r W₁ W₂ as Ws V t).A20 s - W₂ 0 ∧
    (seedTView κ r W₁ W₂ bt Wt V s).F 1 t (W₂ t - W₂ 0) = frzImgD (Ws t) (as t) (W₂ t) s ∧
    (seedTView κ r W₁ W₂ bt Wt V s).A20 t =
        (seedSView κ r W₁ W₂ as Ws V t).A 0 s - W₂ 0 ∧
    (seedTView κ r W₁ W₂ bt Wt V s).A21 t =
        (seedSView κ r W₁ W₂ as Ws V t).A 1 s := by
  obtain ⟨S', hSS', h₁, q₁, hq₁⟩ := h.sOwn t ht
  obtain ⟨T', hTT', h₂, q₂, hq₂⟩ := h.tOwn s hs
  have hs' : s ∈ Icc (0 : ℝ) S' := ⟨hs.1, hs.2.trans hSS'⟩
  have ht' : t ∈ Icc (0 : ℝ) T' := ⟨ht.1, ht.2.trans hTT'⟩
  have a0 := sView_F_zero (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) h₁ hs' h₂ ht' hq₂
  have a1 := sView_F_one (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) h₁ hs' h₂ ht' hq₂
  have b0 := tView_F_zero (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) h₁ hs' h₂ ht' hq₁
  have b1 := tView_F_one (n := 0) (κ := 1) (r := fun _ => 0) (p := fun _ => 0) h₁ hs' h₂ ht' hq₁
  refine ⟨b0, b1, ?_, a1.symm⟩
  change frzImg (Wt s) (bt s) (W₁ s - W₂ 0) t = frzA W₁ (Ws t) (as t) (frzChart W₂ t) 0 s - W₂ 0
  change frzA W₁ (Ws t) (as t) (frzChart W₂ t) 0 s =
    frzImg (Wt s) (bt s) (W₁ s - W₂ 0) t + W₂ 0 at a0
  linarith only [a0]

/-- Clearance in the first chart transports all integrated seeds. It also
proves aliveness of their actual opposite image-flow solutions. -/
theorem seed_mark_factors (hS : 0 < S) (hT : 0 < T) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) S)
    (hc : ∀ m, ∃ ρ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) T,
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull W₂ t)) :
    ∀ m, (∃ q, IsForwardSol (Wt s) ((V m s - W₂ 0 : ℝ) : ℂ) (bt s T) q) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        (seedTView κ r W₁ W₂ bt Wt V s).B0 t m =
          (seedSView κ r W₁ W₂ as Ws V t).B0 s m - W₂ 0 ∧
        (seedTView κ r W₁ W₂ bt Wt V s).B1 t m =
          (seedSView κ r W₁ W₂ as Ws V t).B1 s m := by
  have h₁ : ∀ t ∈ Icc (0 : ℝ) T,
      OwnData W₁ (fwdHull W₂ t) (frzChart W₂ t) S (as t) (Ws t) := by
    intro t ht
    obtain ⟨S', hSS', hown, -⟩ := h.sOwn t ht
    exact hown.restrict hS hSS'
  obtain ⟨T', hTT', hown₂, -⟩ := h.tOwn s hs
  have h₂ := hown₂.restrict hT hTT'
  intro m
  obtain ⟨ρ, hρ, hc⟩ := hc m
  obtain ⟨q, hq, he⟩ := OwnData.seed_access_value_deriv_translated h₁ hs h₂ hρ hc
  refine ⟨⟨q, hq⟩, fun t ht => ?_⟩
  have hev := he t ht
  constructor
  · change frzImg (Wt s) (bt s) (V m s - W₂ 0) t =
      (ownExt W₁ (Ws t) (as t) (frzChart W₂ t) s (V m s)).re - W₂ 0
    linarith only [hev.1]
  · exact hev.2.symm

end TwoViewRect
end InteractingSLE.ZhanGT4
