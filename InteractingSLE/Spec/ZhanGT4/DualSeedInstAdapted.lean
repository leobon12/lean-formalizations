/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstVersion

/-!
# The selected seeded row martingale from protected enclosures

Packet PROVE-ZHAN-GT4-A22. All rectangle, clearance, alive-flow, D9,
scale and source-gap inputs are derived from the enclosures.
The boundary source version is constructed from adapted interior maps.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (IsForwardSol fwdMap fwdHull)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The actual chosen row has the martingale, continuity, boundedness and
entrance-one properties from the original force equation and enclosures. -/
theorem seedSrc_row_facts_of_adapted_enclosures {n : ℕ} {P : Measure Ω} {κ S p s δ q d Tm : ℝ}
    {H₁ H₂ : Set ℂ} (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q d) (hκ : 0 < κ)
    (rr : Fin n → ℝ) (W₁ Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ)
    (W₂ : Ω → ℝ → ℝ)
    (𝓕 : Filtration ℝ≥0 mΩ) (B D : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0)
    (hS : 0 < S) (hT : ∀ ω, 0 < T ω) (hs : s ∈ Ioc (0 : ℝ) S)
    (h0 : ∀ ω, W₂ ω 0 = p)
    (hdW : ∀ ω, (fun u => W₂ ω u - W₂ ω 0) = driftDriver (Real.sqrt (16 / κ)) B D ω)
    (hW₁ : Continuous W₁) (hW₁0 : W₁ 0 = 0)
    (hW₂ : ∀ ω, Continuous (W₂ ω))
    (hK₁ : fwdHull W₁ S ⊆ H₁) (hK₂ : ∀ ω, fwdHull (W₂ ω) (T ω) ⊆ H₂)
    (hlo : IsSeedCoordinate W₁ Vlo S) (hhi : IsSeedCoordinate W₁ Vhi S)
    (hseed : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hVI : ∀ m, V m s ∈ uIcc (Vlo s) (Vhi s)) (hinj : Function.Injective fun m => V m s)
    (hSm : S ≤ Tm) (hTTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hDm : ∀ u, Measurable[𝓕 u] (D u))
    (hBc : ∀ ω, Continuous (B · ω)) (hDc : ∀ ω, Continuous (D · ω))
    (X : ℝ≥0 → Ω → ℝ) (hXm : Adapted 𝓕 X) (hXc : ∀ ω, Continuous (X · ω))
    (hWX : ∀ ω, W₂ ω = fun u => X u.toNNReal ω)
    (hStop : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hD : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω),
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal ω)
        (mirrorSourceCharge κ rr /
          (W₂ ω t - (frzChart (W₂ ω) t 0).re)) (Icc (0 : ℝ) (T ω)) t) :
    Martingale (fun (t : ℝ≥0) ω =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v)
        ω s (min (t : ℝ) (T ω))) 𝓕 P ∧
    (∀ ω, Continuous fun t : ℝ≥0 =>
      seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v)
        ω s (min (t : ℝ) (T ω))) ∧
    (∃ C : ℝ, ∀ (t : ℝ≥0) ω, |seedHeightField
      (fun v ω => seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v)
        ω s (min (t : ℝ) (T ω))| ≤ C) ∧
    ∀ ω, seedHeightField (fun v ω => seedSView κ rr W₁ (W₂ ω)
      (seedSrcClock W₁ S (W₂ ω)) (seedSrcDriver W₁ S (W₂ ω)) V v) ω s 0 = 1 := by
  have hsI := Ioc_subset_Icc_self hs
  have hsrc₁ : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ :=
    closure_mono hK₁ (start_mem_closure_fwdHull hW₁ hS)
  have hzero : (0 : ℂ) ∈ closure H₁ := by simpa only [hW₁0, ofReal_zero] using hsrc₁
  have hsep' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := by
    intro a ha z hz
    rw [norm_sub_rev]
    exact hp.sep z hz a ha
  obtain ⟨_, _, _, _, hsource₁⟩ := exists_source_gap_bounds_of_enclosure hp.hull₁ hp.sep_pos
    (disjoint_ball_of_enclosure_source hp.sep_pos hp.sep hp.src)
  obtain ⟨q₁, hq₁⟩ := (hsource₁ W₁ S hW₁ hS.le hsrc₁ hK₁).1
  obtain ⟨c₀, C₀, hc₀, hC₀, hsource₂⟩ := exists_source_gap_bounds_of_enclosure hp.hull₂ hp.sep_pos
    (disjoint_ball_of_enclosure_source hp.sep_pos hsep' (p := 0) hzero)
  have hq₂ : ∀ ω, ∃ q, IsForwardSol (W₂ ω) (0 : ℂ) (T ω) q := by
    intro ω
    exact (hsource₂ (W₂ ω) (T ω) (hW₂ ω) (T ω).coe_nonneg
      (by simpa only [h0 ω] using hp.src) (hK₂ ω)).1
  have hrect := fun ω => twoViewRect_seedSrc_of_enclosures hp hW₁ (hW₂ ω) hW₁0 (h0 ω)
    hS (NNReal.coe_pos.2 (hT ω)) hK₁ (hK₂ ω)
  obtain ⟨r, hr, hclear⟩ := exists_seed_clearance_of_enclosures hp.hull₁ hp.hull₂ hp.sep_pos hp.sep
  have hc : ∀ ω m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull (W₂ ω) v) := by
    intro ω m
    refine ⟨r, hr, fun v hv => ?_⟩
    exact (hclear W₁ Vlo Vhi S hW₁ hsrc₁ hK₁ hlo hhi s hsI (V m s) (hVI m)).mono_right
      (Set.image_mono (((QuantumZipper.fwdHull_mono).1 hv.2).trans (hK₂ ω)))
  obtain ⟨rad, a₀, γ, Γ, lam, hr, ha, hg, hd9⟩ := exists_seedTView_D9Const_of_enclosures
    hp rr W₁ Vlo Vhi V hW₁ hW₁0 hS hs hSm hK₁ hlo hhi hseed hVI hinj
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha hg Γ lam Tm
  have hne : ∀ ω v, v ∈ Icc (0 : ℝ) (T ω) → ∀ i,
      (seedSView κ rr W₁ (W₂ ω) (seedSrcClock W₁ S (W₂ ω))
        (seedSrcDriver W₁ S (W₂ ω)) V v).gapVal i s ≠ 0 := by
    intro ω v hv
    exact (hrect ω).seed_gapVal_ne hS (NNReal.coe_pos.2 (hT ω)) hs hv
      (by simpa only [h0 ω] using hq₁) hseed hinj (hc ω)
  have hsourceM : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => seedPrefixSource W₂ p T ω u := by
    intro u
    have hh := measurable_seedPrefixSource hXm hXc hStop
      (fun ω => by simpa only [hWX ω] using hq₂ ω) p u
    convert hh using 1
    funext ω
    simp only [seedPrefixSource, ← hWX]
  have hcoef : (16 / κ) * (-1 / 2 + ∑ m, -(κ / 4) * rr m) = mirrorSourceCharge κ rr := by
    rw [mul_add, Finset.mul_sum]
    convert mirrorSourceCharge_eq hκ.ne' rr using 1
    ring
  exact seedHeightField_row_facts_of_source_version hκ rr W₁ V W₂
    (fun ω => seedSrcClock W₁ S (W₂ ω)) (fun ω => seedSrcDriver W₁ S (W₂ ω))
    (fun ω => seedTSrcClock W₁ (W₂ ω) (T ω)) (fun ω => seedTSrcDriver W₁ (W₂ ω) (T ω))
    𝓕 B D T hS hT hsI h0 hdW hrect
    (fun ω => ⟨q₁, by simpa only [h0 ω] using hq₁⟩) hW₂ hq₂
    (fun m => (hseed m).zero.trans hW₁0) hc hne
    hB hDm hBc hDc (seedPrefixSource W₂ p T) hsourceM
    (fun ω u hu => by simp only [seedPrefixSource, hu.2, ↓reduceIte]) hStop
    hr ha hg hc₀ hC₀ hL hTTm
    (fun ω => hd9 (W₂ ω) (T ω) (hW₂ ω) (h0 ω) (NNReal.coe_pos.2 (hT ω)) (hTTm ω) (hK₂ ω))
    (fun m => (hseed m).ne s hs) hinj
    (fun ω => (hsource₂ (W₂ ω) (T ω) (hW₂ ω) (T ω).coe_nonneg
      (by simpa only [h0 ω] using hp.src) (hK₂ ω)).2)
    (fun ω t ht => by simpa only [hcoef] using hD ω t ht)

end InteractingSLE.ZhanGT4
