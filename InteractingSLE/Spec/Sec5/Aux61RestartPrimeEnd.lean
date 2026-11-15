import InteractingSLE.Spec.Sec5.Aux61RestartComponent
import InteractingSLE.Foundations.PrimeEnd.Basic

/-!
# Restart charts with the original target retained as a prime end

Packet PROVE-AUX61-R1; ruling R71. The current access and the original target
are prime-end markings. Normalizing these two markings preserves the original
target even when the retained component has a nonsimple boundary.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

/-- Two distinct boundary markings of the half-plane can be sent to zero and
infinity by a real Möbius map of positive determinant. -/
theorem exists_realMobius_marking (p q : OnePoint ℝ) (hpq : p ≠ q) :
    ∃ a b c d : ℝ, 0 < a * d - b * c ∧
      mobiusBdry a b c d p = (0 : ℝ) ∧ mobiusBdry a b c d q = OnePoint.infty := by
  cases p with
  | infty =>
    cases q with
    | infty => exact (hpq rfl).elim
    | coe y =>
      refine ⟨0, -1, 1, -y, by norm_num, ?_, ?_⟩
      · simp only [mobiusBdry_infty, one_ne_zero, ↓reduceIte, zero_div]
      · simp only [mobiusBdry_coe, one_mul, add_neg_cancel, ↓reduceIte]
  | coe x =>
    cases q with
    | infty =>
      refine ⟨1, -x, 0, 1, by norm_num, ?_, ?_⟩
      · simp only [mobiusBdry_coe, zero_mul, zero_add, one_ne_zero,
          ↓reduceIte, one_mul, add_neg_cancel, zero_div]
      · simp only [mobiusBdry_infty, ↓reduceIte]
    | coe y =>
      have hxy : x ≠ y := fun heq => hpq (congrArg OnePoint.some heq)
      have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
      refine ⟨y - x, -x * (y - x), -1, y, ?_, ?_, ?_⟩
      · nlinarith [sq_pos_of_ne_zero hyx]
      · have hden : -1 * x + y ≠ 0 := by
          simpa only [neg_one_mul, sub_eq_add_neg, add_comm] using hyx
        have hnum : (y - x) * x + -x * (y - x) = 0 := by ring
        simp only [mobiusBdry_coe, hden, ↓reduceIte, hnum, zero_div]
      · simp only [mobiusBdry_coe, neg_one_mul, neg_add_cancel, ↓reduceIte]

/-- Normalize any half-plane chart at two specified prime ends. This changes
neither the component nor the original target marking. -/
theorem exists_hChart_marking {D : Set ℂ} (hDo : IsOpen D) (ψ : HChart D)
    (seed target : PrimeEnd D) (hne : seed ≠ target) :
    ∃ φ : HChart D, PrimeEnd.mk φ (0 : ℝ) = seed ∧
      PrimeEnd.mk φ OnePoint.infty = target := by
  obtain ⟨p, hp⟩ := PrimeEnd.mk_surjective_of_isOpen hDo ψ seed
  obtain ⟨q, hq⟩ := PrimeEnd.mk_surjective_of_isOpen hDo ψ target
  have hpq : p ≠ q := fun heq => hne (hp.symm.trans (heq ▸ hq))
  obtain ⟨a, b, c, d, hdet, ha, hb⟩ := exists_realMobius_marking p q hpq
  have hmob : IsConformalBijection (realMobius a b c d) H H := by
    refine ⟨?_, QuantumZipper.CA.bijOn_realMobius_H hdet⟩
    exact (((differentiable_id.const_mul (a : ℂ)).add_const (b : ℂ)).differentiableOn.div
      ((differentiable_id.const_mul (c : ℂ)).add_const (d : ℂ)).differentiableOn
      fun z hz => QuantumZipper.CA.realMobius_denom_ne_zero hdet hz)
  let φ : HChart D := ⟨realMobius a b c d ∘ ψ.1,
    isConformalBijection_comp hmob ψ.2⟩
  have hEq : EqOn φ.1 (realMobius a b c d ∘ ψ.1) D := fun _ _ => rfl
  refine ⟨φ, ?_, ?_⟩
  · simpa only [ha] using (PrimeEnd.mk_mobiusBdry hdet hEq p).trans hp
  · simpa only [hb] using (PrimeEnd.mk_mobiusBdry hdet hEq q).trans hq

/-- The chart of the actual retained component, normalized at its current access
and its original target. Only the two genuine prime-end marks are supplied. -/
theorem exists_restart_targetChart {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b : ℂ}
    (hr : 0 ≤ r) (hKo : IsOpen (H \ K))
    (hKu : ∀ z ∈ LocalSets.lowerUnion K,
      ¬ Bornology.IsBounded (connectedComponentIn (LocalSets.lowerUnion K) z))
    (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0)
    (hb : b ∈ retainedDomain K η r)
    (seed target : PrimeEnd (restartComponent K η r b)) (hne : seed ≠ target) :
    ∃ φ : HChart (restartComponent K η r b), PrimeEnd.mk φ (0 : ℝ) = seed ∧
      PrimeEnd.mk φ OnePoint.infty = target := by
  obtain ⟨ho, hconn, hsc, hH⟩ := restartComponent_properties hr hKo hKu hc h0 hb
  have hproper : restartComponent K η r b ≠ univ := by
    intro heq
    have hz : (0 : ℂ) ∈ restartComponent K η r b := heq ▸ mem_univ _
    exact lt_irrefl (0 : ℝ) (hH hz)
  obtain ⟨Φ, hΦ, -⟩ := exists_isConformalBijection_ball ho hconn hsc hproper
    (mem_connectedComponentIn hb)
  exact exists_hChart_marking ho ⟨QuantumZipper.CA.cayleyInv ∘ Φ,
    isConformalBijection_comp isConformalBijection_cayleyInv hΦ⟩ seed target hne

end InteractingSLE.Sec5.Aux61Restart
