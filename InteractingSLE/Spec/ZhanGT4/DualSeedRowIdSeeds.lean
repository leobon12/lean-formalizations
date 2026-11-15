/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRowIdHeight
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformOrder

/-!
# Seeded row noncollision from the actual integrated force coordinates

Packet PROVE-ZHAN-GT4-A22. The ordinary opposite accesses are distinct
integrated seeds at the fixed positive first prefix. Flow injectivity and the
seed omission theorem discharge all finite-band nonvanishing conditions.
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

/-- The actual integrated seed coordinates and chart clearances imply
nonvanishing of every normalized band factor at positive first time. -/
theorem seed_gapVal_ne (hS : 0 < S) (hT : 0 < T) {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) T)
    {q : ℝ → ℂ} (hq : IsForwardSol W₁ ((W₂ 0 : ℝ) : ℂ) S q)
    (hseed : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hinj : Function.Injective fun m => V m s)
    (hc : ∀ m, ∃ ρ > (0 : ℝ), ∀ v ∈ Icc (0 : ℝ) T,
      Disjoint (ball (V m s : ℂ) ρ) (frzChart W₁ s '' fwdHull W₂ v)) :
    ∀ i, (seedSView κ r W₁ W₂ as Ws V t).gapVal i s ≠ 0 := by
  let d := seedSView κ r W₁ W₂ as Ws V t
  let e := seedTView κ r W₁ W₂ bt Wt V s
  have hsI := Ioc_subset_Icc_self hs
  obtain ⟨S', hSS', ho₁, q₁, hq₁⟩ := h.sOwn t ht
  obtain ⟨T', hTT', ho₂', q₂, hq₂'⟩ := h.tOwn s hsI
  have ho₂ := ho₂'.restrict hT hTT'
  have hq₂ := isForwardSol_restrict hq₂' (ho₂'.mapsTo_clock ⟨hT.le, hTT'⟩).2
  have hs' : s ∈ Icc (0 : ℝ) S' := ⟨hs.1.le, hs.2.trans hSS'⟩
  have hf := h.seed_tip_factors (κ := κ) (r := r) (V := V) hsI ht
  have hm := h.seed_mark_factors (κ := κ) (r := r) hS hT hsI hc
  choose qa hqa using fun m => (hm m).1
  have hv : d.W s - d.V₀ s ≠ 0 := by
    have hn := source_centered_re_ne ho₁.cont hq hsI
    change W₁ s - ((fwdMap W₁ s (W₂ 0)).re + W₁ s) ≠ 0
    simpa only [sub_add_eq_sub_sub_swap, sub_self, zero_sub, neg_ne_zero] using hn
  have hp : W₂ 0 ≠ W₁ 0 := by
    have hn := source_centered_re_ne ho₁.cont hq ⟨le_rfl, hS.le⟩
    simpa only [fwdMap_zero_eq_sub, sub_re, ofReal_re, sub_ne_zero] using hn
  have hvV (m : Fin n) : d.V₀ s ≠ d.V m s := by
    change (fwdMap W₁ s (W₂ 0)).re + W₁ s ≠ V m s
    rw [fwdMap_eq_of_isForwardSol ho₁.cont hq hsI]
    rcases lt_or_gt_of_ne hp with hlt | hgt
    · exact ((hseed m).gmap_lt ho₁.cont hlt hq hsI).ne
    · exact ((hseed m).lt_gmap ho₁.cont hgt hq hsI).ne'
  have h0 : d.A20 s - d.A 0 s ≠ 0 := ho₁.frzImg_sub_ne_zero hq₁ hs'
  have h21 : d.A21 s ≠ 0 :=
    div_ne_zero (deriv_fwdMap_real ho₁.contW' hq₁ (ho₁.mapsTo_clock hs')).2.ne'
      (deriv_fwdMap_real ho₁.cont hq hsI).2.ne'
  have hm0 (m : Fin n) : d.A20 s - d.B0 s m ≠ 0 := by
    have hn := ho₂.frzImg_sub_ne_zero (hqa m) ht
    have hdriver : e.A 0 t = e.F 0 t (W₂ t - W₂ 0) := rfl
    change e.B0 t m - e.A 0 t ≠ 0 at hn
    rw [hdriver, hf.1, (hm m).2 t ht |>.1] at hn
    intro he
    apply hn
    linarith only [he]
  have hmW (m : Fin n) : d.B0 s m - d.A 0 s ≠ 0 := by
    have hn := ho₂.frzImg_sub_frzImg_ne_zero (hqa m) hq₂
      (by intro he; exact (hseed m).ne s hs (by linarith only [he])) ht
    change e.B0 t m - e.A20 t ≠ 0 at hn
    rw [(hm m).2 t ht |>.1, hf.2.2.1] at hn
    intro he
    apply hn
    linarith only [he]
  have hm1 (m : Fin n) : d.B1 s m ≠ 0 := by
    have hn := (deriv_fwdMap_real ho₂.contW' (hqa m) (ho₂.mapsTo_clock ht)).2.ne'
    change e.B1 t m ≠ 0 at hn
    rw [(hm m).2 t ht |>.2] at hn
    exact hn
  have hmk (m k : Fin n) (hmk : m ≠ k) : d.B0 s m - d.B0 s k ≠ 0 := by
    have hn := ho₂.frzImg_sub_frzImg_ne_zero (hqa m) (hqa k) (by intro he; exact hinj.ne hmk (by linarith only [he])) ht
    change e.B0 t m - e.B0 t k ≠ 0 at hn
    rw [(hm m).2 t ht |>.1, (hm k).2 t ht |>.1] at hn
    intro he
    apply hn
    linarith only [he]
  intro i
  rcases i with i | ⟨i, m⟩ | ⟨i, m, k⟩
  · fin_cases i
    · exact h0
    · exact h21
    · change d.V₀ s - d.W s ≠ 0
      exact sub_ne_zero.2 (sub_ne_zero.1 hv).symm
  · fin_cases i
    · exact hmW m
    · exact hm0 m
    · exact hm1 m
    · exact sub_ne_zero.2 ((hseed m).ne s hs)
    · exact sub_ne_zero.2 (hvV m)
  · by_cases he : m = k
    · simp only [SeedData.gapVal, he, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
    · fin_cases i
      · simpa [SeedData.gapVal, he] using hmk m k he
      · simpa [SeedData.gapVal, he, seedSView, SeedData.fromSource] using sub_ne_zero.2 (hinj.ne he)

end TwoViewRect
end InteractingSLE.ZhanGT4
