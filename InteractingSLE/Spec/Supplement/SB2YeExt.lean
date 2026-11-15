/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XqLift

/-!
# The boundary extension of a chart inverse read through a stage chart

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2`'s chart package). Let `cℓ` be a conformal chart whose inverse has
boundary limits `Fℓ` on `ℍ̄`, and `G` a continuous `ℍ`-valued map within bounded distance of the identity such that
`cℓ.2.1 ∘ G` has boundary limits `F` on `ℍ̄` (the canonical chart's inverse, `G = cℓ.1 ∘ Φ.2.1`). Then:

* **`exists_bdryExt_of_cluster`**: `G` has boundary limits `g` on `ℍ̄` (SB2LIFT's clustering lemma
  `Mn.tendsto_of_cluster` along a convergent subsequence of `G (p + i/(n+1))`), with `Fℓ ∘ g = F`, `g` continuous on
  `ℍ̄` with values in `ℍ̄` and within the same distance of the identity;
* **`finite_fibre_of_comp`**: `g` has finite fibres on `ℍ̄` if `F` has (`g⁻¹{z} ⊆ F⁻¹{Fℓ z}`).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

variable {cℓ : Chart} {Fℓ G F : ℂ → ℂ} {C : ℝ}

/-- The approach sequence `p + i/(n+1)` lies in `ℍ` and tends to `p`. -/
theorem approach_facts {p : ℂ} (hp : p ∈ Hbar) :
    (∀ n : ℕ, p + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I ∈ H) ∧
      Tendsto (fun n : ℕ => p + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 p) := by
  refine ⟨fun n => ?_, ?_⟩
  · show 0 < (p + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I).im
    have hp' : 0 ≤ p.im := hp
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_one, mul_zero, add_zero]
    linarith
  · have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa using this.mul_const Complex.I
    simpa using tendsto_const_nhds.add h2

/-- **The boundary extension by clustering.** -/
theorem exists_bdryExt_of_cluster (hℓ : cℓ.IsConformal) (hFℓ : ∀ q ∈ Hbar, Tendsto cℓ.2.1 (𝓝[H] q) (𝓝 (Fℓ q)))
    (hGc : ContinuousOn G H) (hGH : ∀ y ∈ H, G y ∈ H) (hGb : ∀ y ∈ H, ‖G y - y‖ ≤ C)
    (hF : ∀ p ∈ Hbar, Tendsto (fun y => cℓ.2.1 (G y)) (𝓝[H] p) (𝓝 (F p))) :
    ∃ g : ℂ → ℂ, (∀ p ∈ Hbar, Tendsto G (𝓝[H] p) (𝓝 (g p))) ∧ (∀ p ∈ Hbar, Fℓ (g p) = F p) ∧
      ContinuousOn g Hbar ∧ EqOn g G H ∧ (∀ p ∈ Hbar, g p ∈ Hbar) ∧ ∀ p ∈ Hbar, ‖g p - p‖ ≤ C := by
  have hex : ∀ p : ℂ, ∃ w : ℂ, p ∈ Hbar → Tendsto G (𝓝[H] p) (𝓝 w) := by
    intro p
    by_cases hp : p ∈ Hbar
    · obtain ⟨huH, hu⟩ := approach_facts hp
      set u := fun n : ℕ => p + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I with hudef
      have hbd : ∀ n, G (u n) ∈ closedBall p (C + 1) := by
        intro n
        rw [mem_closedBall, dist_eq_norm]
        have h1 := hGb (u n) (huH n)
        have h2 : ‖u n - p‖ ≤ 1 := by
          simp only [hudef, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs]
          rw [abs_of_pos (by positivity)]
          rw [div_le_one (by positivity)]
          linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        calc ‖G (u n) - p‖ = ‖(G (u n) - u n) + (u n - p)‖ := by ring_nf
          _ ≤ ‖G (u n) - u n‖ + ‖u n - p‖ := norm_add_le _ _
          _ ≤ C + 1 := add_le_add h1 h2
      obtain ⟨w, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hbd
      refine ⟨w, fun _ => ?_⟩
      exact Mn.tendsto_of_cluster hℓ hFℓ hGc hGH hGb hp (hF p hp) (Eventually.of_forall fun n => huH (φ n))
        (hu.comp hφ.tendsto_atTop) hlim
    · exact ⟨0, fun h => absurd h hp⟩
  choose g hg using hex
  have hgt : ∀ p ∈ Hbar, Tendsto G (𝓝[H] p) (𝓝 (g p)) := fun p hp => hg p hp
  have hgc : ContinuousOn g Hbar := GW1P.continuousOn_of_tendsto hgt
  have hgH : EqOn g G H := fun y hy => by
    have hyH : y ∈ Hbar := QuantumZipper.H_subset_Hbar hy
    have : (𝓝[H] y).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hgt y hyH) ((hGc y hy).tendsto.mono_left (le_of_eq rfl))
  have hmem : ∀ p ∈ Hbar, g p ∈ Hbar := by
    intro p hp
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    have hcl : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    exact hcl.mem_of_tendsto (hgt p hp) (eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.H_subset_Hbar (hGH y hy))
  refine ⟨g, hgt, fun p hp => ?_, hgc, hgH, hmem, fun p hp => ?_⟩
  · have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    have h1 : Tendsto G (𝓝[H] p) (𝓝[H] (g p)) :=
      tendsto_nhdsWithin_iff.2 ⟨hgt p hp, eventually_nhdsWithin_of_forall fun y hy => hGH y hy⟩
    exact tendsto_nhds_unique ((hFℓ (g p) (hmem p hp)).comp h1) (hF p hp)
  · have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    have h1 : Tendsto (fun y => G y - y) (𝓝[H] p) (𝓝 (g p - p)) :=
      (hgt p hp).sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    exact le_of_tendsto h1.norm (eventually_nhdsWithin_of_forall fun y hy => hGb y hy)

/-- **Finite fibres through the composition**: `g⁻¹{z} ⊆ F⁻¹{Fℓ z}` on `ℍ̄`. -/
theorem finite_fibre_of_comp {g : ℂ → ℂ} (hcomp : ∀ p ∈ Hbar, Fℓ (g p) = F p)
    (hFf : ∀ z, (F ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite) : ∀ z, (g ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite := by
  intro z
  refine (hFf (Fℓ z)).subset fun p hp => ⟨?_, hp.2⟩
  show F p = Fℓ z
  rw [← hcomp p hp.2, show g p = z from hp.1]

end InteractingSLE.Theorem14.SB.Sx
