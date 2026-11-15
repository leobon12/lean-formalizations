/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3Word
import QuantumZipper.Proofs.Complex.BasicsAutomorphisms

/-!
# Lemma GW3: component charts are unique up to dilation

Packet PROVE-T14-GW5 (a step of Lemma GW3's field law `GW4.GW3FieldLawStatement`, which is asserted "for every choice
of component charts"). The frozen `IsComponentChart` docstring: "such charts exist for the Jordan components of GW4
(Carathéodory) and differ by the scalings `w ↦ a w`, `a > 0`". This file proves the scaling claim for an open component
whenever the two walks share no nondegenerate connected set (GW4, proof, p. 637: "An interior common open subarc is
impossible … A common original-real interval is also impossible").

## Proof

For two component charts `c, c'` of the open component `C`, `φ = fwd' ∘ inv` is a conformal automorphism of `ℍ`,
hence a real Möbius map `w ↦ (a w + b)/(c w + d)` with `ad − bc > 0` (QuantumZipper's
`exists_realMobius_of_bijOn_H`). At a real point `x` off the pole, the boundary limit of `inv` at `x` is the boundary
limit of `inv'` at `φ(x)`; it lies on `R` if `x > 0` (resp. `φ(x) > 0`) and on `L` if `x < 0` (resp. `φ(x) < 0`). If
`φ` sent an interval of one sign into the other sign, the boundary map of `inv` would send that interval into
`R ∩ L`; its image is connected, hence a point, and the boundary map of an injective holomorphic map is not constant on
an interval (`GW3Word.false_of_tendsto_const`). An elementary sign analysis then forces `c = 0` and `b = 0`.

## Main results

* `exists_dilation_of_isComponentChart` : `fwd' ∘ inv = (r ·)` on `ℍ` for some `r > 0`;
* `inv_eq_of_isComponentChart` : `inv' w = inv (w / r)` on `ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Theorem14

namespace GW3Law

open GW3Word

/-- **The boundary limit through a real Möbius map**: if `inv = inv' ∘ φ` on `ℍ` for a real Möbius map `φ` (positive
determinant) and `x` is a real point off the pole, then `inv` tends at `x` to the limit of `inv'` at `φ(x)`. -/
theorem tendsto_comp_realMobius {inv inv' : ℂ → ℂ} {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    (hcomp : ∀ w ∈ H, inv w = inv' (QuantumZipper.CA.realMobius a b c d w)) {x : ℝ} (hx : c * x + d ≠ 0)
    {p' : ℂ} (hp' : Tendsto inv' (𝓝[H] (((a * x + b) / (c * x + d) : ℝ) : ℂ)) (𝓝 p')) :
    Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p') := by
  have hden : (c : ℂ) * (x : ℂ) + d ≠ 0 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.2 hx
  have hcont : ContinuousAt (QuantumZipper.CA.realMobius a b c d) (x : ℂ) := by
    unfold QuantumZipper.CA.realMobius
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
  have hval : QuantumZipper.CA.realMobius a b c d (x : ℂ) = (((a * x + b) / (c * x + d) : ℝ) : ℂ) := by
    unfold QuantumZipper.CA.realMobius; push_cast; rfl
  have hφ : Tendsto (QuantumZipper.CA.realMobius a b c d) (𝓝[H] (x : ℂ))
      (𝓝[H] (((a * x + b) / (c * x + d) : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun w hw =>
      QuantumZipper.CA.realMobius_mem_H hdet hw⟩
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  exact (hp'.comp hφ).congr' (eventually_nhdsWithin_of_forall fun w hw => (hcomp w hw).symm)

/-- **Component charts are unique up to dilation.** Two component charts `c, c'` of the same open component `C`
between `R` and `L` satisfy `fwd'(inv w) = r w` on `ℍ` for some `r > 0`, provided `R ∩ L` contains no nondegenerate
connected set. -/
theorem exists_dilation_of_isComponentChart {R L C : Set ℂ} {c c' : Chart} (hc : IsComponentChart R L C c)
    (hc' : IsComponentChart R L C c') (hCo : IsOpen C)
    (hRL : ∀ S ⊆ R ∩ L, IsPreconnected S → S.Subsingleton) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ H, c'.1 (c.2.1 w) = (r : ℂ) * w := by
  have hdi := differentiableOn_inv_of_isComponentChart hc hCo
  have hinj : InjOn c.2.1 H := hc.2.2.2.1.2.injOn
  obtain ⟨hd, hmF, hmI, hinv, hlim, -, -⟩ := hc
  obtain ⟨hd', hmF', hmI', hinv', hlim', -, -⟩ := hc'
  -- `φ = fwd' ∘ inv` is a conformal automorphism of `ℍ`, hence a real Möbius map
  have hφd : DifferentiableOn ℂ (fun w => c'.1 (c.2.1 w)) H := by
    intro w hw
    have h1 : DifferentiableAt ℂ c'.1 (c.2.1 w) :=
      (hd' _ (hmI hw)).differentiableAt (hCo.mem_nhds (hmI hw))
    exact h1.comp_differentiableWithinAt w (hdi w hw)
  have hφb : BijOn (fun w => c'.1 (c.2.1 w)) H H :=
    (hinv'.bijOn hmF' hmI').comp (hinv.symm.bijOn hmI hmF)
  obtain ⟨a, b, cc, d, hdet, hφ⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hφd hφb
  have hcomp : ∀ w ∈ H, c.2.1 w = c'.2.1 (QuantumZipper.CA.realMobius a b cc d w) := by
    intro w hw
    rw [← hφ hw]
    exact (hinv'.1 (hmI hw)).symm
  set m : ℝ → ℝ := fun x => (a * x + b) / (cc * x + d) with hm
  -- the boundary map of `inv`
  set q : ℝ → ℂ := fun x => extendFrom H c.2.1 (x : ℂ) with hq
  have hqc : Continuous q := continuous_extendFrom_ofReal hdi.continuousOn fun x => (hlim x).imp fun p hp => hp.1
  have hqlim : ∀ x : ℝ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (q x)) := fun x =>
    tendsto_extendFrom ((hlim x).imp fun p hp => hp.1)
  have hside : ∀ x : ℝ, cc * x + d ≠ 0 → (0 < x → q x ∈ R) ∧ (x < 0 → q x ∈ L) ∧
      (0 < m x → q x ∈ R) ∧ (m x < 0 → q x ∈ L) := by
    intro x hx
    have hNe : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    obtain ⟨p, hp, hpR, hpL⟩ := hlim x
    obtain ⟨p', hp', hpR', hpL'⟩ := hlim' (m x)
    have e1 : q x = p := tendsto_nhds_unique (hqlim x) hp
    have e2 : q x = p' := tendsto_nhds_unique (hqlim x) (tendsto_comp_realMobius hdet hcomp hx hp')
    exact ⟨fun h => e1 ▸ hpR h, fun h => e1 ▸ hpL h, fun h => e2 ▸ hpR' h, fun h => e2 ▸ hpL' h⟩
  -- an interval sent to the other sign is impossible
  have hint : ∀ u v : ℝ, u < v → (∀ x ∈ Ioo u v, cc * x + d ≠ 0 ∧ ((0 < x ∧ m x < 0) ∨ (x < 0 ∧ 0 < m x))) →
      False := by
    intro u v huv hI
    have hRLq : MapsTo q (Ioo u v) (R ∩ L) := by
      intro x hx
      obtain ⟨hx0, hx1⟩ := hI x hx
      obtain ⟨h1, h2, h3, h4⟩ := hside x hx0
      rcases hx1 with ⟨hp, hn⟩ | ⟨hn, hp⟩
      · exact ⟨h1 hp, h4 hn⟩
      · exact ⟨h3 hp, h2 hn⟩
    have hsub := hRL _ (hRLq.image_subset) (isPreconnected_Ioo.image q hqc.continuousOn)
    set x₀ := (u + v) / 2 with hx₀
    have hx₀I : x₀ ∈ Ioo u v := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
    exact false_of_tendsto_const hdi hinj huv fun x hx =>
      (hsub (mem_image_of_mem q hx) (mem_image_of_mem q hx₀I)) ▸ hqlim x
  by_cases hc0 : cc = 0
  · have had : 0 < a * d := by rw [hc0, mul_zero, sub_zero] at hdet; exact hdet
    have hd0 : d ≠ 0 := fun h => by rw [h, mul_zero] at had; exact lt_irrefl _ had
    have ha0 : a ≠ 0 := fun h => by rw [h, zero_mul] at had; exact lt_irrefl _ had
    have hmx : ∀ x : ℝ, m x * (d * d) = a * d * (x + b / a) := by
      intro x
      simp only [hm, hc0, zero_mul, zero_add]
      field_simp
    have hdd : 0 < d * d := mul_self_pos.2 hd0
    have hden : ∀ x : ℝ, cc * x + d ≠ 0 := fun x => by rw [hc0, zero_mul, zero_add]; exact hd0
    by_cases hb0 : b = 0
    · refine ⟨a / d, by rw [div_pos_iff]; rcases lt_or_gt_of_ne hd0 with h | h
                        · exact Or.inr ⟨by nlinarith, h⟩
                        · exact Or.inl ⟨by nlinarith, h⟩, fun w hw => ?_⟩
      show (fun w => c'.1 (c.2.1 w)) w = _
      rw [hφ hw]
      unfold QuantumZipper.CA.realMobius
      rw [hc0, hb0]
      have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0
      push_cast
      simp only [zero_mul, zero_add, add_zero]
      rw [div_eq_iff hd', div_mul_eq_mul_div, div_mul_cancel₀ _ hd']
    · exfalso
      set s := -(b / a) with hs
      have hs0 : s ≠ 0 := by
        rw [hs, neg_ne_zero]; exact div_ne_zero hb0 ha0
      rcases lt_or_gt_of_ne hs0 with hsn | hsp
      · refine hint s 0 hsn fun x hx => ⟨hden x, Or.inr ⟨hx.2, ?_⟩⟩
        have h1 := hmx x
        have h2 : 0 < a * d * (x + b / a) := mul_pos had (by rw [hs] at hx; linarith [hx.1])
        nlinarith
      · refine hint 0 s hsp fun x hx => ⟨hden x, Or.inl ⟨hx.1, ?_⟩⟩
        have h1 := hmx x
        have h2 : a * d * (x + b / a) < 0 := mul_neg_of_pos_of_neg had (by rw [hs] at hx; linarith [hx.2])
        nlinarith
  · exfalso
    set x₀ := -d / cc with hx₀
    set D := a * d - b * cc with hD
    set t₁ := D / (|a * cc| + 1) with ht₁
    have hpos : 0 < |a * cc| + 1 := by positivity
    have ht₁0 : 0 < t₁ := div_pos hdet hpos
    have hlt : |a * cc| * t₁ < D := by
      rw [ht₁, mul_div_assoc', div_lt_iff₀ hpos]
      nlinarith [abs_nonneg (a * cc)]
    have hcc2 : 0 < cc * cc := mul_self_pos.2 hc0
    -- at `x = x₀ + t`, `m x · cc² t = −D + a cc t`
    have hmt : ∀ t : ℝ, t ≠ 0 → cc * (x₀ + t) + d ≠ 0 ∧ m (x₀ + t) * (cc * cc * t) = -D + a * cc * t := by
      intro t ht
      have e : cc * (x₀ + t) + d = cc * t := by rw [hx₀]; field_simp; ring
      refine ⟨by rw [e]; exact mul_ne_zero hc0 ht, ?_⟩
      simp only [hm]
      rw [e, hD, hx₀]
      field_simp
      ring
    have hneg : ∀ t : ℝ, t ≠ 0 → |t| < t₁ → -D + a * cc * t < 0 := by
      intro t _ htt
      have h1 : a * cc * t ≤ |a * cc| * |t| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |a * cc| * |t| ≤ |a * cc| * t₁ := mul_le_mul_of_nonneg_left htt.le (abs_nonneg _)
      linarith
    rcases le_or_gt 0 x₀ with hx0 | hx0
    · refine hint x₀ (x₀ + t₁) (by linarith) fun x hx => ?_
      have ht : x - x₀ ≠ 0 := by linarith [hx.1]
      obtain ⟨hden, he⟩ := hmt (x - x₀) ht
      rw [add_sub_cancel] at hden he
      refine ⟨hden, Or.inl ⟨by linarith [hx.1], ?_⟩⟩
      have h1 := hneg (x - x₀) ht (by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.2])
      have h2 : 0 < cc * cc * (x - x₀) := mul_pos hcc2 (by linarith [hx.1])
      nlinarith
    · refine hint (x₀ - t₁) x₀ (by linarith) fun x hx => ?_
      have ht : x - x₀ ≠ 0 := by linarith [hx.2]
      obtain ⟨hden, he⟩ := hmt (x - x₀) ht
      rw [add_sub_cancel] at hden he
      refine ⟨hden, Or.inr ⟨by linarith [hx.2], ?_⟩⟩
      have h1 := hneg (x - x₀) ht (by rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.1])
      have h2 : cc * cc * (x - x₀) < 0 := mul_neg_of_pos_of_neg hcc2 (by linarith [hx.2])
      nlinarith

/-- **The inverse charts differ by the dilation**: under the hypotheses of `exists_dilation_of_isComponentChart`,
`inv' w = inv (w / r)` on `ℍ`. -/
theorem inv_eq_of_isComponentChart {R L C : Set ℂ} {c c' : Chart} (hc : IsComponentChart R L C c)
    (hc' : IsComponentChart R L C c') (hCo : IsOpen C)
    (hRL : ∀ S ⊆ R ∩ L, IsPreconnected S → S.Subsingleton) :
    ∃ r : ℝ, 0 < r ∧ (∀ w ∈ H, c'.1 (c.2.1 w) = (r : ℂ) * w) ∧ ∀ w ∈ H, c'.2.1 w = c.2.1 (w / r) := by
  obtain ⟨r, hr, hφ⟩ := exists_dilation_of_isComponentChart hc hc' hCo hRL
  refine ⟨r, hr, hφ, fun w hw => ?_⟩
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hwr : w / r ∈ H := by
    show 0 < (w / (r : ℂ)).im
    rw [Complex.div_ofReal_im]; exact div_pos hw hr
  have h1 := hφ (w / r) hwr
  rw [mul_div_cancel₀ w hr0] at h1
  calc c'.2.1 w = c'.2.1 (c'.1 (c.2.1 (w / r))) := by rw [h1]
    _ = c.2.1 (w / r) := hc'.2.2.2.1.1 (hc.2.2.1 hwr)

end GW3Law

end Theorem14

end InteractingSLE
