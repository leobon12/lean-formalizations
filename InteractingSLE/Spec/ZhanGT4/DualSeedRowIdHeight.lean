/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdNormalize
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedOriginal

/-!
# Identification of the concrete seeded height-field row

Packet PROVE-ZHAN-GT4-A22. Subtract the two actual opposite logarithms,
then exponentiate. The surviving first-prefix reference factors cancel.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
namespace TwoViewRect
variable {n : ℕ} {κ S T : ℝ} {r : Fin n → ℝ} {W₁ W₂ : ℝ → ℝ}
  {as Ws bt Wt : ℝ → ℝ → ℝ} {V : Fin n → ℝ → ℝ}
  (h : TwoViewRect W₁ W₂ S T as Ws bt Wt)
include h

/-- Actual seeded row identification in logarithmic form. All common
factor identities and both axis normalizations are proved from the maps. -/
theorem seed_log_increment_eq (hκ : κ ≠ 0) (hS : 0 < S) (hT : 0 < T)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) T)
    {q₁ q₂ : ℝ → ℂ} (hq₁ : IsForwardSol W₁ ((W₂ 0 : ℝ) : ℂ) S q₁)
    (hW₂ : Continuous W₂) (hq₂ : IsForwardSol W₂ (0 : ℂ) T q₂)
    (hV : ∀ m, V m 0 = 0)
    (hc : ∀ m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) T,
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull W₂ v))
    (hne : ∀ v ∈ Icc (0 : ℝ) T, ∀ i, (seedSView κ r W₁ W₂ as Ws V v).gapVal i s ≠ 0) :
    (seedSView κ r W₁ W₂ as Ws V t).normEll s - (seedSView κ r W₁ W₂ as Ws V t).normEll 0 =
      (seedTView κ r W₁ W₂ bt Wt V s).seedAccessEll (-W₂ 0) t (W₂ t - W₂ 0) -
        (seedTView κ r W₁ W₂ bt Wt V s).seedAccessEll (-W₂ 0) 0 (W₂ 0 - W₂ 0) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have he := h.seed_fused_log_eq hκ hS hT hs ht hq₁ hW₂ hq₂ hV hc (hne t ht)
  have he0 := h.seed_fused_log_eq hκ hS hT hs h0 hq₁ hW₂ hq₂ hV hc (hne 0 h0)
  obtain ⟨S', hSS', hown, -⟩ := h.sOwn 0 h0
  have hz := seedSView_normEll_zero_height (κ := κ) r V hW₂ hown ⟨hs.1, hs.2.trans hSS'⟩
  have hz0 := seedSView_normEll_zero_height (κ := κ) r V hW₂ hown ⟨le_rfl, hown.pos.le⟩
  linarith only [he, he0, hz, hz0]

end TwoViewRect

/-- The actual height-field row, stopped in the second clock, is the
concrete fused opposite-view density. This identifies the process used
by the source-record martingale theorem. -/
theorem seedHeightField_row_eq_density {Ω : Type*} {n : ℕ} {κ S : ℝ} {r : Fin n → ℝ}
    {W₁ : ℝ → ℝ} {W₂ : Ω → ℝ → ℝ} {as Ws bt Wt : Ω → ℝ → ℝ → ℝ}
    {V : Fin n → ℝ → ℝ} {T : Ω → ℝ≥0} {s : ℝ}
    (hκ : κ ≠ 0) (hS : 0 < S) (hT : ∀ ω, 0 < T ω)
    (h : ∀ ω, TwoViewRect W₁ (W₂ ω) S (T ω) (as ω) (Ws ω) (bt ω) (Wt ω))
    (hs : s ∈ Icc (0 : ℝ) S)
    (hq₁ : ∀ ω, ∃ q, IsForwardSol W₁ ((W₂ ω 0 : ℝ) : ℂ) S q)
    (hW₂ : ∀ ω, Continuous (W₂ ω)) (hq₂ : ∀ ω, ∃ q, IsForwardSol (W₂ ω) (0 : ℂ) (T ω) q)
    (hV : ∀ m, V m 0 = 0)
    (hc : ∀ ω m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull (W₂ ω) v))
    (hne : ∀ ω v, v ∈ Icc (0 : ℝ) (T ω) →
      ∀ i, (seedSView κ r W₁ (W₂ ω) (as ω) (Ws ω) V v).gapVal i s ≠ 0) :
    ∀ (t : ℝ≥0) ω,
      seedHeightField (fun v ω => seedSView κ r W₁ (W₂ ω) (as ω) (Ws ω) V v)
        ω s (min (t : ℝ) (T ω)) =
      (seedTView κ r W₁ (W₂ ω) (bt ω) (Wt ω) V s).seedAccessDensity (-W₂ ω 0) (T ω) t := by
  intro t ω
  obtain ⟨q₁, hq₁⟩ := hq₁ ω
  obtain ⟨q₂, hq₂⟩ := hq₂ ω
  have he := (h ω).seed_log_increment_eq hκ hS (NNReal.coe_pos.2 (hT ω)) hs
    ⟨le_min t.coe_nonneg (T ω).coe_nonneg, min_le_right _ _⟩ hq₁ (hW₂ ω) hq₂ hV (hc ω) (hne ω)
  exact congrArg Real.exp he

end InteractingSLE.ZhanGT4
