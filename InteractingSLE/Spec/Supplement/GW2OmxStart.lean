/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxSoft
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# GW2's open lines: the stage-start comparison of two bounded harmonic extensions

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start identity, deterministic). If a bounded harmonic extension `u`
of `f`, dilated by `λ > 0`, is another one `v` of `g` plus a constant `C` on `ℍ`, then the data agree the same way
off the jump sets, and the constant is the difference of the far-right heights:

* `data_eq_of_bhe_dil`: `f (λ x) = g x + C` off the jump sets;
* **`const_eq_far_of_bhe_dil`**: `C = hf − hg` when `f` and `g` are eventually `hf` and `hg` to the right.

At the stage start this pins the additive constant of the kernel's and the instance's means, so the two words' data
agree exactly after the angle shift and `GW2Omx.eqOn_bhe_dil_of_data_eq` flows them to every later stage time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Omx

/-- **Data of dilated bounded harmonic extensions differing by a constant.** -/
theorem data_eq_of_bhe_dil {f g : ℝ → ℝ} {S T : Set ℝ} {u v : ℂ → ℝ} (hu : IsBoundedHarmonicExtension f S u)
    (hv : IsBoundedHarmonicExtension g T v) {lam C : ℝ} (hlam : 0 < lam)
    (h : ∀ z ∈ H, u ((lam : ℂ) * z) = v z + C) {x : ℝ} (hxS : lam * x ∉ S) (hxT : x ∉ T) :
    f (lam * x) = g x + C := by
  have hmap : Tendsto (fun z : ℂ => (lam : ℂ) * z) (𝓝[H] (x : ℂ)) (𝓝[H] ((lam * x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun z : ℂ => (lam : ℂ) * z := continuous_const.mul continuous_id
      have h1 := (hc.tendsto (x : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
      simpa [Complex.ofReal_mul] using h1
    · filter_upwards [self_mem_nhdsWithin] with z hz
      show 0 < ((lam : ℂ) * z).im
      have hz' : 0 < z.im := hz
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos hlam hz'
  have h1 : Tendsto (fun z : ℂ => u ((lam : ℂ) * z)) (𝓝[H] (x : ℂ)) (𝓝 (f (lam * x))) :=
    (hu.2.2 _ hxS).comp hmap
  have h2 : Tendsto (fun z : ℂ => u ((lam : ℂ) * z)) (𝓝[H] (x : ℂ)) (𝓝 (g x + C)) := by
    refine ((hv.2.2 x hxT).add_const C).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz using (h z hz).symm
  have := Exist.StagedLaw.neBot_nhdsWithin_H_real x
  exact tendsto_nhds_unique h1 h2

/-- **The constant is the difference of the far-right heights.** -/
theorem const_eq_far_of_bhe_dil {f g : ℝ → ℝ} {S T : Set ℝ} (hS : S.Finite) (hT : T.Finite) {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension f S u) (hv : IsBoundedHarmonicExtension g T v) {lam C : ℝ} (hlam : 0 < lam)
    (h : ∀ z ∈ H, u ((lam : ℂ) * z) = v z + C) {hf hg : ℝ} (hfar : ∃ B : ℝ, ∀ y, B < y → y ∉ S → f y = hf)
    (hgar : ∃ B : ℝ, ∀ y, B < y → y ∉ T → g y = hg) : C = hf - hg := by
  obtain ⟨B₁, hB₁⟩ := hfar
  obtain ⟨B₂, hB₂⟩ := hgar
  set a : ℝ := max (B₁ / lam) B₂ with ha
  have hfin : ((fun y => y / lam) '' S ∪ T).Finite := (hS.image _).union hT
  obtain ⟨x, hxI, hxF⟩ := ((Set.Ioi_infinite a).sdiff hfin).nonempty
  have hxa : a < x := hxI
  have hxS : lam * x ∉ S := fun hs => hxF (Or.inl ⟨lam * x, hs, by field_simp⟩)
  have hxT : x ∉ T := fun ht => hxF (Or.inr ht)
  have hx1 : B₁ < lam * x := by
    have : B₁ / lam < x := lt_of_le_of_lt (le_max_left _ _) hxa
    rwa [div_lt_iff₀ hlam, mul_comm] at this
  have hx2 : B₂ < x := lt_of_le_of_lt (le_max_right _ _) hxa
  have e := data_eq_of_bhe_dil hu hv hlam h hxS hxT
  rw [hB₁ _ hx1 hxS, hB₂ _ hx2 hxT] at e
  linarith

end InteractingSLE.Theorem14.GW2Omx
