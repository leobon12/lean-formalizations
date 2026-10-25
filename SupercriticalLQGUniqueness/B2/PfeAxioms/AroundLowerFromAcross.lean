import SupercriticalLQGUniqueness.B2.PfeAxioms.AroundAcrossFinite
import SupercriticalLQGUniqueness.B2.PfeAxioms.AcrossFiniteLowerTail

 


set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem around_lower_tail_of_across_lower_tail
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ι → Ω → LSCMetric) (A : EuclideanAnnulus)
    (hcont : ∀ i, ∀ᵐ ω ∂P,
      Continuous (B2.PfeWeyl.euclidForget (E i ω)))
    (hcross : ∀ B : EuclideanAnnulus, ∀ η : ℝ, 0 < η →
      ∃ M : ℝ, 0 < M ∧ ∀ i,
        P {ω | acrossDist (E i ω) B < ENNReal.ofReal M⁻¹} ≤
          ENNReal.ofReal η) :
    ∀ η : ℝ, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ i,
      P {ω | aroundDist (E i ω) A < ENNReal.ofReal M⁻¹} ≤
        ENNReal.ofReal η := by
  classical
  obtain ⟨d, _hd, q, hqFin, hqNe, _hqSub, hbound⟩ :=
    exists_finite_across_bound_around A
  letI : Fintype q := hqFin.fintype
  intro η hη
  let δ : ℝ := η / ((Fintype.card q : ℝ) + 1)
  have hδ : 0 < δ := div_pos hη (by positivity)
  have hEach (z : q) :
      ∃ M : ℝ, 0 < M ∧ ∀ i,
        P {ω | acrossDist (E i ω) (radialCoverAnnulus d z) <
          ENNReal.ofReal M⁻¹} ≤ ENNReal.ofReal δ :=
    hcross (radialCoverAnnulus d z) δ hδ
  choose Mz hMz hTail using hEach
  have hqUniv : (Finset.univ : Finset q).Nonempty := by
    obtain ⟨z, hz⟩ := hqNe
    exact ⟨⟨z, hz⟩, Finset.mem_univ _⟩
  let Mmax : ℝ := (Finset.univ : Finset q).sup' hqUniv Mz
  let M : ℝ := Mmax + 1
  have hM : 0 < M := by
    obtain ⟨z, _⟩ := hqUniv
    have hz : Mz z ≤ Mmax := Finset.le_sup' Mz (Finset.mem_univ z)
    dsimp [M]
    linarith [hMz z]
  have hInv (z : q) : ENNReal.ofReal M⁻¹ ≤ ENNReal.ofReal (Mz z)⁻¹ := by
    apply ENNReal.ofReal_le_ofReal
    apply (inv_le_inv₀ hM (hMz z)).2
    have hz : Mz z ≤ Mmax := Finset.le_sup' Mz (Finset.mem_univ z)
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro i
  have hsub : ∀ᵐ ω ∂P,
      aroundDist (E i ω) A < ENNReal.ofReal M⁻¹ →
        ω ∈ ⋃ z : q,
          {ω | acrossDist (E i ω) (radialCoverAnnulus d z) <
            ENNReal.ofReal M⁻¹} := by
    filter_upwards [hcont i] with ω hc hω
    by_contra hn
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hn
    have hlow : ENNReal.ofReal M⁻¹ ≤
        ⨅ z ∈ q, acrossDist (E i ω) (radialCoverAnnulus d z) := by
      apply le_iInf
      intro z
      apply le_iInf
      intro hz
      exact hn ⟨z, hz⟩
    exact (not_lt_of_ge (hlow.trans (hbound (E i ω) hc))) hω
  calc
    P {ω | aroundDist (E i ω) A < ENNReal.ofReal M⁻¹} ≤
        P (⋃ z : q,
          {ω | acrossDist (E i ω) (radialCoverAnnulus d z) <
            ENNReal.ofReal M⁻¹}) := measure_mono_ae hsub
    _ ≤ ∑ z : q,
          P {ω | acrossDist (E i ω) (radialCoverAnnulus d z) <
            ENNReal.ofReal M⁻¹} := by
      simpa only using (measure_iUnion_fintype_le P
        (fun z : q => {ω | acrossDist (E i ω)
          (radialCoverAnnulus d z) < ENNReal.ofReal M⁻¹}))
    _ ≤ ∑ _z : q, ENNReal.ofReal δ := by
      apply Finset.sum_le_sum
      intro z _
      exact (measure_mono (fun ω hω => lt_of_lt_of_le hω (hInv z))).trans
        (hTail z i)
    _ ≤ ENNReal.ofReal η := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [δ]
      have hc : 0 ≤ (Fintype.card q : ℝ) := Nat.cast_nonneg _
      rw [← mul_div_assoc]
      exact (div_le_iff₀ (by linarith :
        0 < (Fintype.card q : ℝ) + 1)).2 (by nlinarith)

end SupercriticalLQGUniqueness.B2.PfeAxioms
