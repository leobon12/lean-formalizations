/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37FlatClockProofCover
import InteractingSLE.Spec.Sec7.Aux37GermCf
import InteractingSLE.Spec.Sec6.Prop65Point
import InteractingSLE.GFF.LocalSets.Prop38Version

/-!
# Aux. lemma 37's flat clock, part 3: from bump pairings to the unchanged component

Packet PROVE-FLATCLOCK. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L95, p. 198): "Countably
many rational points and harmonicity give the same assertion throughout each unchanged active component."

* `eqOn_component_of_bump` (pathwise): let `D₂ ⊆ D₁ ⊆ ℍ` be open, `U` a connected component of `D₂` that is also a
  component of `D₁`, and `v₁`, `v₂` harmonic representatives of `T₁` on `D₁` and `T₂` on `D₂`. If `T₁` and `T₂` agree on
  every radial bump `b_{y,1/(n+1)}` with `y` in a dense set whose variances in `D₁` and `D₂` coincide, then `v₁ = v₂` on
  `U`. (For a bump inside `U` both variances are the variance in `U`, `LocalSets.zeroGFFTestCov_eq_of_isClopen`; the
  pairing is the value at the centre times the bump mass, `GFF.integral_mul_bumpFun_of_harmonic`; continuity and
  density conclude.)
* **`flatClockStatement_of_nested`**: `Aux37Germ.FlatClockStatement P Q E g` from three almost sure statements at every
  pair `r ≤ s` in `Q`: `E r`, `E s` relatively closed, `E r ⊆ E s`, and for every test function `φ`, equal variances
  of `φ` in `ℍ ∖ E r` and `ℍ ∖ E s` force `g r (φ) = g s (φ)` (the output of
  `IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq`).

No Theorem 1.2/1.3 (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.FlatClockProof

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open LocalSets

/-- The radial bump of radius `1/(n+1)` about `y` (zero when its closed disc leaves `ℍ`). -/
def bumpN (n : ℕ) (y : ℂ) : TestOn upperHalfPlaneOpens :=
  bumpTestH (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat y

/-! ### The pathwise comparison -/

/-- **Two harmonic representatives agreeing in the bump pairings on an unchanged component agree on it.** -/
theorem eqOn_component_of_bump {D₁ D₂ : Set ℂ} (hD₁ : IsOpen D₁) (hD₂ : IsOpen D₂) (hD₁H : D₁ ⊆ H)
    (hD₂₁ : D₂ ⊆ D₁) {T₁ T₂ : DistOn upperHalfPlaneOpens} {v₁ v₂ : ℂ → ℝ}
    (hv₁ : InnerProductSpace.HarmonicOnNhd v₁ D₁)
    (hT₁ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ D₁ → T₁ φ = ∫ z, v₁ z * φ z)
    (hv₂ : InnerProductSpace.HarmonicOnNhd v₂ D₂)
    (hT₂ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ D₂ → T₂ φ = ∫ z, v₂ z * φ z)
    {S : Set ℂ} (hS : Dense S)
    (hbump : ∀ n : ℕ, ∀ y ∈ S, zeroGFFTestCov D₁ (bumpN n y) (bumpN n y) =
      zeroGFFTestCov D₂ (bumpN n y) (bumpN n y) → T₁ (bumpN n y) = T₂ (bumpN n y))
    {z : ℂ} (hcomp : connectedComponentIn D₂ z = connectedComponentIn D₁ z) :
    ∀ w ∈ connectedComponentIn D₂ z, v₁ w = v₂ w := by
  set U := connectedComponentIn D₂ z with hU
  have hUo : IsOpen U := hD₂.connectedComponentIn
  have hU₂ : U ⊆ D₂ := connectedComponentIn_subset _ _
  have hU₁ : U ⊆ D₁ := hU₂.trans hD₂₁
  have hD₂H : D₂ ⊆ H := hD₂₁.trans hD₁H
  -- at the centre of a bump inside `U` the two representatives agree
  have hcentre : ∀ n : ℕ, ∀ y ∈ S, closedBall y (1 / ((n : ℝ) + 1)) ⊆ U → v₁ y = v₂ y := by
    intro n y hy hB
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hyim : 1 / ((n : ℝ) + 1) < y.im := (closedBall_subset_H_iff hδ.le).1 (hB.trans (hU₁.trans hD₁H))
    have hcoe : ⇑(bumpN n y) = GFF.bumpFun y (1 / ((n : ℝ) + 1)) := coe_bumpTestH_of_lt hδ hyim
    have hsupp : tsupport (bumpN n y) ⊆ U := by
      rw [hcoe]
      exact (GFF.tsupport_bumpFun_subset hδ).trans hB
    have hvar₁ : zeroGFFTestCov D₁ (bumpN n y) (bumpN n y) = zeroGFFTestCov U (bumpN n y) (bumpN n y) := by
      have hUeq : U = connectedComponentIn D₁ z := hcomp
      have hdiff : IsOpen (D₁ \ U) := by
        rw [hUeq]; exact Sec6.Prop65.isOpen_diff_connectedComponentIn hD₁ z
      exact zeroGFFTestCov_eq_of_isClopen hD₁ hD₁H hUo hU₁ hdiff _ hsupp
    have hvar₂ : zeroGFFTestCov D₂ (bumpN n y) (bumpN n y) = zeroGFFTestCov U (bumpN n y) (bumpN n y) :=
      zeroGFFTestCov_eq_of_isClopen hD₂ hD₂H hUo hU₂ (Sec6.Prop65.isOpen_diff_connectedComponentIn hD₂ z) _ hsupp
    have hT := hbump n y hy (hvar₁.trans hvar₂.symm)
    rw [hT₁ _ (hsupp.trans hU₁), hT₂ _ (hsupp.trans hU₂), hcoe,
      GFF.integral_mul_bumpFun_of_harmonic hUo (hv₁.mono hU₁) hδ hB,
      GFF.integral_mul_bumpFun_of_harmonic hUo (hv₂.mono hU₂) hδ hB] at hT
    have hm : 0 < (1 / ((n : ℝ) + 1)) ^ 2 * GFF.bumpMass := by
      have := GFF.bumpMass_pos; positivity
    exact mul_right_cancel₀ hm.ne' hT
  -- continuity and density
  intro w hw
  by_contra hne
  have hc : ContinuousAt (fun x => v₁ x - v₂ x) w :=
    ((hv₁.mono hU₁).continuousOn.continuousAt (hUo.mem_nhds hw)).sub
      ((hv₂.mono hU₂).continuousOn.continuousAt (hUo.mem_nhds hw))
  have hpos : 0 < |v₁ w - v₂ w| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨ε, hε, hεc⟩ := Metric.continuousAt_iff.1 hc _ hpos
  obtain ⟨ε', hε', hε'U⟩ := Metric.isOpen_iff.1 hUo w hw
  set ρ := min ε ε' / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  obtain ⟨y, hyS, hyw⟩ := hS.exists_dist_lt w hρ0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hρ0
  have hB : closedBall y (1 / ((n : ℝ) + 1)) ⊆ U := by
    intro x hx
    refine hε'U (mem_ball.2 ?_)
    have h1 := mem_closedBall.1 hx
    have h2 : dist x w ≤ dist x y + dist y w := dist_triangle _ _ _
    have h3 : ρ ≤ ε' / 2 := by
      rw [hρ]; exact div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two
    rw [dist_comm] at hyw
    linarith
  have hyeq := hcentre n y hyS hB
  have hdy : dist y w < ε := by
    have : ρ ≤ ε / 2 := by
      rw [hρ]; exact div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two
    rw [dist_comm] at hyw
    linarith
  have := hεc hdy
  rw [Real.dist_eq, hyeq, sub_self, zero_sub, abs_neg] at this
  exact lt_irrefl _ this

/-! ### The flat clock from the nested comparisons -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The flat clock** (`Aux37Germ.FlatClockStatement`) from almost sure statements at every pair `r ≤ s` of `Q`:
relative closedness, `E r ⊆ E s`, and "equal variances force equal means" for every test function. -/
theorem flatClockStatement_of_nested {Q : Set ℝ≥0} {E : ℝ≥0 → Ω → Set ℂ}
    {g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hAc : ∀ t ∈ Q, ∀ᵐ ω ∂P, E t ω ⊆ H ∧ IsOpen (H \ E t ω))
    (hsub : ∀ r ∈ Q, ∀ s ∈ Q, r ≤ s → ∀ᵐ ω ∂P, E r ω ⊆ E s ω)
    (hnest : ∀ r ∈ Q, ∀ s ∈ Q, r ≤ s → ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      zeroGFFTestCov (H \ E r ω) φ φ = zeroGFFTestCov (H \ E s ω) φ φ → g r ω φ = g s ω φ) :
    Aux37Germ.FlatClockStatement P Q E g := by
  intro r hr s hs hrs
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have : Countable S := hSc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ y : S,
      zeroGFFTestCov (H \ E r ω) (bumpN n y) (bumpN n y) = zeroGFFTestCov (H \ E s ω) (bumpN n y) (bumpN n y) →
        g r ω (bumpN n y) = g s ω (bumpN n y) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro y
    exact hnest r hr s hs hrs _
  filter_upwards [hAc r hr, hAc s hs, hsub r hr s hs hrs, hall] with ω hr' hs' hrs' hω vr vs hvr hvrr hvs hvsr z _
    hcomp
  exact eqOn_component_of_bump hr'.2 hs'.2 sdiff_subset (sdiff_subset_sdiff_right hrs') hvr hvrr hvs hvsr hSd
    (fun n y hy => hω n ⟨y, hy⟩) hcomp

end InteractingSLE.Sec7.FlatClockProof
