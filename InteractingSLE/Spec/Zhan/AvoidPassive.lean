/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Ito.Loewner
import QuantumZipper.Proofs.RS.RealAlive

/-!
# Passive real points are never swallowed (`κ ≤ 4`)

Packet PROVE-ZHAN-B. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/`,
text dump L1336–1361, ruling R35): in the proof of the avoidance lemma, "no finite original prefix hits
either new target, by the preceding simplicity/noncollision argument"; Specification §2.2, "A
passive-mark consequence" (`source/spec/p001-048.md`): for `κ ≤ 4` a real point that is not a force
point is never swallowed while the force points stay away from the driver.

* `IsIntegratedSLEEvolution.ae_real_alive_of_forall_ne`: for an integrated `SLE_κ(ρ)` evolution with
  `0 < κ ≤ 4`, almost surely, on every time interval `[0, t]`, `t < ζ`, on which no force point meets
  the driver, every real `x ≠ 0` has a forward Loewner solution (is not swallowed). Proof: the localized
  Girsanov comparison (`Dimension.exists_brownian_localization`) writes the driver as `√κ X` on `[0, t]`
  with the law of `X` absolutely continuous with respect to a Brownian law, and ordinary `SLE_κ`,
  `κ ≤ 4`, swallows no real point (QuantumZipper's `RS.ae_real_alive`, Rohde–Schramm Lemma 6.2).
* `IsIntegratedSLEEvolution.ae_real_alive_of_hasAdmissiblePartialSums`: for an ordered word with all
  marks separated from the seed and admissible side partial sums (Aux. lemma 6), almost surely the
  lifetime is infinite and no real `x ≠ 0` is ever swallowed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Passive real points are not swallowed before the first collision (`κ ≤ 4`).** -/
theorem IsIntegratedSLEEvolution.ae_real_alive_of_forall_ne [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (∀ s : ℝ≥0, s ≤ t → (∀ i, W s ω ≠ VL i s ω) ∧ ∀ i, W s ω ≠ VR i s ω) →
      ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (x : ℂ) t v := by
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hloc := fun n : ℕ => Dimension.exists_brownian_localization hκ hE 0 (n : ℝ≥0) (hδ n)
  choose X hXm μ hμprob hμBM hac hXeq using hloc
  have hal : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (drive κ canonBM (X n ω)) (x : ℂ) T v := fun n => by
    have := hμprob n
    have h := ae_real_alive (hμBM n) hκ hκ4
    exact ae_of_ae_map (hXm n).aemeasurable ((hac n).ae_le h)
  filter_upwards [ae_all_iff.2 hal, ae_all_iff.2 hXeq, hE.2.2.2.2] with ω hal hx hp t ht hne x hx0
  obtain ⟨δ, hδpos, hgap⟩ := hp.exists_gapsGE_of_ne ht hne
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ δ ∧ (t : ℝ) ≤ n := by
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδpos
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge (t : ℝ)
    refine ⟨max n₁ n₂, (one_div_le_one_div_of_le (by positivity) ?_).trans hn₁.le, ?_⟩
    · exact_mod_cast Nat.add_le_add_right (le_max_left n₁ n₂) 1
    · exact hn₂.trans (by exact_mod_cast le_max_right n₁ n₂)
  obtain ⟨v, hv⟩ := hal n x hx0 t t.coe_nonneg
  have hW0 : W 0 ω = 0 := hp.1
  refine ⟨v, (Ito.isForwardSol_iff_of_eqOn (fun s hs => ?_) v).2 hv⟩
  have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
  have hsn : s.toNNReal ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]; exact (NNReal.coe_le_coe.2 hst).trans (by exact_mod_cast hn.2)
  have hsζ : ((0 + s.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [zero_add]; exact lt_of_le_of_lt (by exact_mod_cast hst) ht
  have key := hx n s.toNNReal hsn hsζ fun r _ hr => by
    rw [zero_add] at hr
    obtain ⟨hL, hR⟩ := hgap r (hr.trans hst)
    exact ⟨fun i => hn.1.trans (hL i), fun i => hn.1.trans (hR i)⟩
  rw [zero_add, hW0, sub_zero] at key
  simp only [drive, canonBM]
  exact key

/-- **Separated admissible words: no real point is ever swallowed (`κ ≤ 4`).** -/
theorem IsIntegratedSLEEvolution.ae_real_alive_of_hasAdmissiblePartialSums [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0)
    (hxR : ∀ i, 0 < xR i) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s : ℝ => W s.toNNReal ω) (x : ℂ) T v := by
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE,
    hE.ae_real_alive_of_forall_ne hκ hκ4, hE.2.2.2.2] with ω h6 hal hp
  obtain ⟨hζ, hsep⟩ := h6
  refine ⟨hζ, fun x hx T hT => ?_⟩
  have hne : ∀ s : ℝ≥0, s ≤ T.toNNReal → (∀ i, W s ω ≠ VL i s ω) ∧ ∀ i, W s ω ≠ VR i s ω := by
    intro s _
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with hs | hs
    · subst hs
      have h0 : W 0 ω = 0 := hp.1
      refine ⟨fun i => ?_, fun i => ?_⟩
      · have hv : VL i 0 ω = xL i := hp.2.1 i
        rw [h0, hv]; exact (hxL i).ne'
      · have hv : VR i 0 ω = xR i := hp.2.2.1 i
        rw [h0, hv]; exact (hxR i).ne
    · exact ⟨fun i => ((hsep s hs).1 i).ne', fun i => ((hsep s hs).2 i).ne⟩
  have h := hal T.toNNReal (by rw [hζ]; exact ENNReal.coe_lt_top) hne x hx
  rwa [Real.coe_toNNReal _ hT] at h

end InteractingSLE
