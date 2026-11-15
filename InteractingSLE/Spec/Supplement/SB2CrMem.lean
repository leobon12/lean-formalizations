/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrSafe

/-!
# K2's (L) from deterministic physical lines under a STRICT time change

Packet PROVE-SB2-CONDFIN (round 8, D44). The member-identity companion of `Cr.hasSafeLaw_of_lineLawS`:
`Aux79.hasSafeMembers_of_lineMembers` with the strict first passage (`Cr.linePieceS`), so the capacity-time
filtration's `q`-events need only be cut by `{q < Qc t}`, and the line facts are needed only where the clock is
positive.

* **`hasSafeMembers_of_lineMembersS`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cr

open Restart.DomainMarkov Restart.DomainMarkov.Aux79 Restart.DomainMarkov.K2 Coupling Ito LocalSets LQGMetric
  LQGMetric.MarkovZB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {F : Set Ω} {Qc : ℝ≥0 → Ω → ℝ≥0}

/-- **(L) from the member identities on deterministic physical lines, under a strict time change.** -/
theorem hasSafeMembers_of_lineMembersS [IsProbabilityMeasure P] {𝓖 𝓗' : Filtration ℝ≥0 mΩ}
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Qc t ω) (hm : ∀ ω, Monotone fun t => Qc t ω) (h0 : ∀ ω, Qc 0 ω = 0)
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | q < Qc t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < ζ ω → ∃ t, q ≤ Qc t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR ζ ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] ({ω | 0 < Qc t ω} ∩ lineSafe Qc W ζ (ballsK Fb) t))
    (hline : ∀ (t : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ H → ∀ E : Set Ω, MeasurableSet[𝓖 t] E →
      (∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ 0 < Qc t ω ∧ ω ∈ lineSafe Qc W ζ (ballsK Fb) t) →
      ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
        ∫ ω in E, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
          projFactor (ballsOpen Fb) f Ξ * ∫ ω in E, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P) :
    HasSafeMembers P 𝓗' F ζ W X := by
  intro s Fb hFbH D hD hDs f Ξ
  have hcexp : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) := fun φ =>
    (by fun_prop : Measurable fun x : ℝ => Complex.exp (Complex.I * x)).comp (hX φ)
  have hnorm : ∀ (φ : TestOn upperHalfPlaneOpens) ω, ‖Complex.exp (Complex.I * (X ω φ : ℂ))‖ ≤ 1 := fun φ ω => by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, le_refl]
  set a : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) with ha
  set b : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω Ξ : ℂ)) with hb
  have hai : Integrable a P :=
    Integrable.of_bound (hcexp _).aestronglyMeasurable 1 (Eventually.of_forall (hnorm _))
  have hbi : Integrable b P :=
    Integrable.of_bound (hcexp _).aestronglyMeasurable 1 (Eventually.of_forall (hnorm _))
  set S : ℝ≥0 → Set Ω := lineSafe Qc W ζ (ballsK Fb) with hSdef
  set E : ℕ → ℕ → Set Ω := linePieceS Qc s D S with hEdef
  have hDm : MeasurableSet D := 𝓗'.le s _ hD
  have hEm : ∀ n k, MeasurableSet[𝓖 (dyT n k)] (E n k) :=
    measurableSet_linePieceS hQa (h𝓗' s D hD) (hS Fb)
  have hEm' : ∀ n k, MeasurableSet (E n k) := fun n k => 𝓖.le _ _ (hEm n k)
  have hsum : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator a ω ∂P =
      projFactor (ballsOpen Fb) f Ξ * ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator b ω ∂P := fun n => by
    rw [integral_finsetSum _ fun k _ => hai.indicator (hEm' n k),
      integral_finsetSum _ fun k _ => hbi.indicator (hEm' n k), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator (hEm' n k), integral_indicator (hEm' n k)]
    refine hline (dyT n k) Fb hFbH (E n k) (hEm n k) ?_ f Ξ
    filter_upwards [hDs] with ω hω hωE
    exact ⟨(hω (linePieceS_subset D S n k hωE)).1, pos_of_mem_linePieceS hωE, hωE.2⟩
  have hreach' : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 ≤ r → ω ∈ F → (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ∃ t, (r : ℝ).toNNReal ≤ Qc t ω :=
    ae_all_iff.2 fun r => (hreach (r : ℝ).toNNReal).mono fun ω h _ => h
  have hgood : ∀ᵐ ω ∂P, ω ∈ D → (∃ t, s < Qc t ω) ∧
      (∀ t : ℕ → ℝ≥0, Tendsto (fun n => Qc (t n) ω) atTop (𝓝 s) → ∀ᶠ n in atTop, ω ∈ S (t n)) := by
    filter_upwards [hDs, hreg, hreach'] with ω hω hp hr hωD
    obtain ⟨hωF, hsζ, hdis⟩ := hω hωD
    refine ⟨?_, fun t ht => eventually_mem_lineSafe (isCompact_ballsK Fb) hFbH (hp hωF) hsζ hdis t ht⟩
    obtain ⟨r, hr0, hsr, hrζ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hsζ
    have hq : (s : ℝ≥0∞) < (((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := hsr
    obtain ⟨t, ht⟩ := hr r hr0 hωF hrζ
    exact ⟨t, lt_of_lt_of_le (ENNReal.coe_lt_coe.1 hq) ht⟩
  have hlim : ∀ c : Ω → ℂ, ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator c ω) atTop
      (𝓝 (D.indicator c ω)) := fun c =>
    ae_tendsto_sum_linePieceS (P := P) (D := D) (S := S) hc hm h0 (fun _ _ => c) c (by
      filter_upwards [hgood] with ω hω hωD
      exact ⟨(hω hωD).1, (hω hωD).2, tendsto_const_nhds⟩)
  have hT : ∀ c : Ω → ℂ, Measurable c → (∀ ω, ‖c ω‖ ≤ 1) →
      Tendsto (fun n => ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (E n k).indicator c ω ∂P) atTop
        (𝓝 (∫ ω in D, c ω ∂P)) := fun c hcm hcn => by
    rw [← integral_indicator hDm]
    exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        (hcm.aestronglyMeasurable.indicator (hEm' n k)))
      (integrable_const 1) (fun n => Eventually.of_forall fun ω =>
        norm_sum_linePieceS_le hc hm h0 (fun _ _ => c) n _ fun k _ => hcn ω) (hlim c)
  have hTa := hT a (hcexp _) (hnorm _)
  have hTb := (hT b (hcexp _) (hnorm _)).const_mul (projFactor (ballsOpen Fb) f Ξ)
  exact tendsto_nhds_unique (hTa.congr fun n => hsum n) hTb

end InteractingSLE.Theorem14.SB.Cr
