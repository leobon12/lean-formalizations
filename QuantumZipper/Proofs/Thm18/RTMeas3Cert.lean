import QuantumZipper.Proofs.Thm18.RTMeas3Zip
import QuantumZipper.Proofs.Thm18.RTMeas2Off

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS3, part 4: the pieces of a good configuration carry the open-arc certificate

If the field of a configuration has a global boundary limit `ν` (LQG-good) without atoms
(`AtomQ`) and with infinite length of `[0,∞)` (`InfQ`), and its curve meets `ℝ` only at `0`,
then the pieces (the field read off the curve) carry `CertO`: they agree (regularized) with the
field off the curve (`regEqOff_offConfig`), so on `ℝ ∖ {0}` their boundary approximations are
eventually those of the field on every compact window (`eventually_restrict_bdryApprox_eq`) and
they have the local limit `ν|_{ℝ∖{0}}` (`isVagueLimitOnR_congr_off`); the arc readings are then
`ν` of the arcs. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Cor15Group

theorem certO_offConfig {γ : ℝ} {c : AreaConfig} (hc : Continuous c.drv) (h0 : c.drv 0 = 0)
    (hR : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ∉ curveOf c.drv) (hg : IsLQGGood γ c.fld)
    (hat : AtomQ γ c.fld) (hinf : InfQ γ c.fld) : CertO γ (offConfig γ c).fld := by
  set y := (offConfig γ c).fld with hy
  set Yf := c.fld with hYf
  have hK := D74.isClosed_curveOf c.drv
  have hEq : RegEqOff (curveOf c.drv) Yf y := fun k z h => (regEqOff_offConfig γ hc h0 k z h).symm
  have hν := isVagueLimitR_qBoundaryMeasure_of_isLQGGood hg
  set ν := qBoundaryMeasure γ Yf with hνdef
  have := hν.1
  have hI0 : ∀ t ∈ U0, (t : ℂ) ∉ curveOf c.drv := fun t ht => hR t ht
  have hlim : IsVagueLimitOnR U0 (bdryApprox γ y) (ν.restrict U0) :=
    isVagueLimitOnR_congr_off hK hEq γ hI0 (LocLen.isVagueLimitOnR_of_isVagueLimitR hν isOpen_U0)
  have hreg : IsRegularSample Yf := hg.1
  have hsub : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → Ioo a b ⊆ U0 := by
    rintro a b (hb | ha) t ht
    · exact (ht.2.trans_le hb).ne
    · exact (ha.trans_lt ht.1).ne'
  have hatom : ∀ s, ν {s} = 0 := measure_singleton_eq_zero_of_atomQ hν hat
  have hrd : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → LocLen.arcRd γ y a b = ν (Icc a b) := by
    intro a b hab
    rw [LocLen.arcRd_eq_arcLen isOpen_U0 hlim (hsub a b hab),
      LocLen.arcLen_eq_of_isVagueLimitOnR hlim (hsub a b hab),
      Measure.restrict_apply isOpen_Ioo.measurableSet, inter_eq_left.2 (hsub a b hab)]
    refine le_antisymm (measure_mono Ioo_subset_Icc_self) ?_
    calc ν (Icc a b) ≤ ν (Ioo a b ∪ ({a} ∪ {b})) := measure_mono fun t ht => by
          rcases eq_or_ne t a with rfl | ha
          · exact Or.inr (Or.inl rfl)
          rcases eq_or_ne t b with rfl | hb
          · exact Or.inr (Or.inr rfl)
          exact Or.inl ⟨lt_of_le_of_ne ht.1 ha.symm, lt_of_le_of_ne ht.2 hb⟩
      _ ≤ ν (Ioo a b) + (ν {a} + ν {b}) := (measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _))
      _ = ν (Ioo a b) := by rw [hatom, hatom, add_zero, add_zero]
  refine ⟨fun n hsubn hpq => ?_, fun N => ?_, fun n m => ?_, fun N => ?_⟩
  · -- the window certificate
    have hC : ∀ u ∈ Icc (wp n) (wq n), (u : ℂ) ∉ curveOf c.drv := fun u hu => hR u (hsubn hu)
    obtain ⟨K, hK'⟩ := (eventually_restrict_bdryApprox_eq hK hEq γ isCompact_Icc
      hC).exists_forall_of_atTop
    refine ⟨⟨K, fun k hk => ?_⟩, LocLen.R2b.lCert_of_lim hpq
      (ν := (ν.restrict U0).restrict (Ioo (wp n) (wq n)))
      (E1.isVagueLimitOnR_restrict_open hlim isOpen_Ioo (Ioo_subset_Icc_self.trans hsubn))⟩
    have e := congrArg (fun m : Measure ℝ => m (Icc (wp n) (wq n))) (hK' k hk)
    simp only [Measure.restrict_apply measurableSet_Icc, inter_self] at e
    rw [← e]
    exact (LogSing.isFiniteMeasureOnCompacts_bdryApprox hreg γ k).lt_top_of_isCompact isCompact_Icc
  · rw [hrd _ _ (Or.inl le_rfl), hrd _ _ (Or.inr le_rfl)]
    exact ⟨isCompact_Icc.measure_lt_top, isCompact_Icc.measure_lt_top⟩
  · obtain ⟨k, hk⟩ := hat (2 * n + 1) (m + 1)
    refine ⟨k, fun j hj => ?_⟩
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hcell : ∀ i : ℤ, |i| ≤ ((m + 1 : ℕ) : ℤ) * 2 ^ k →
        ν (Icc ((i : ℝ) / 2 ^ k) (((i : ℝ) + 1) / 2 ^ k)) ≤ (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ :=
      fun i hi => by rw [← Thm14WDG.mIcc_eq hν]; exact hk i hi
    have hjm : (j : ℤ) ≤ ((m + 1 : ℕ) : ℤ) * 2 ^ k := by
      have : (j : ℤ) ≤ (m : ℤ) * 2 ^ k := by exact_mod_cast hj
      push_cast; nlinarith [pow_pos (show (0 : ℤ) < 2 by norm_num) k]
    have hab : ∀ i : ℤ, 0 ≤ i → i ≤ j → |i| ≤ ((m + 1 : ℕ) : ℤ) * 2 ^ k := fun i h1 h2 => by
      rw [abs_of_nonneg h1]; exact h2.trans hjm
    have hab' : ∀ i : ℤ, -((j : ℤ) + 1) ≤ i → i ≤ 0 → |i| ≤ ((m + 1 : ℕ) : ℤ) * 2 ^ k :=
      fun i h1 h2 => by
        rw [abs_of_nonpos h2]
        have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        push_cast at hjm ⊢; nlinarith
    have hsum : (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ + (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ =
        ((n : ℝ≥0∞) + 1)⁻¹ := by
      have e2 : (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1) = 2 * ((n : ℝ≥0∞) + 1) := by push_cast; ring
      rw [e2, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← two_mul,
        ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    have hj1 : (((j : ℤ) - 1 : ℤ) : ℝ) = (j : ℝ) - 1 := by push_cast; ring
    have hj0 : (((j : ℤ)) : ℝ) = (j : ℝ) := by push_cast; ring
    constructor
    · rw [hrd (dl k j) (dr k j) (Or.inr (le_max_left _ _))]
      calc ν (Icc (dl k j) (dr k j))
          ≤ ν (Icc ((((j : ℤ) - 1 : ℤ) : ℝ) / 2 ^ k) (((((j : ℤ) - 1 : ℤ) : ℝ) + 1) / 2 ^ k) ∪
              Icc ((((j : ℤ)) : ℝ) / 2 ^ k) (((((j : ℤ)) : ℝ) + 1) / 2 ^ k)) :=
            measure_mono fun t ht => by
              rw [hj1, hj0]
              rcases le_total t ((j : ℝ) / 2 ^ k) with h | h
              · refine Or.inl ⟨?_, by rw [show (j : ℝ) - 1 + 1 = j by ring]; exact h⟩
                exact (le_max_right _ _).trans ht.1
              · exact Or.inr ⟨h, ht.2⟩
        _ ≤ _ + _ := measure_union_le _ _
        _ ≤ (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ + (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ := by
            rcases Nat.eq_zero_or_pos j with hj0' | hjpos
            · exact add_le_add (hcell _ (hab' _ (by omega) (by omega)))
                (hcell _ (hab _ (by omega) le_rfl))
            · exact add_le_add (hcell _ (hab _ (by omega) (by omega)))
                (hcell _ (hab _ (by omega) le_rfl))
        _ = _ := hsum
    · have hdl : -dl k j ≤ 0 := by unfold dl; linarith [le_max_left 0 (((j : ℝ) - 1) / 2 ^ k)]
      rw [hrd _ _ (Or.inl hdl)]
      have hjn : (((-(j : ℤ) - 1 : ℤ)) : ℝ) = -(j : ℝ) - 1 := by push_cast; ring
      have hjn0 : (((-(j : ℤ) : ℤ)) : ℝ) = -(j : ℝ) := by push_cast; ring
      calc ν (Icc (-dr k j) (-dl k j))
          ≤ ν (Icc ((((-(j : ℤ) - 1 : ℤ)) : ℝ) / 2 ^ k) (((((-(j : ℤ) - 1 : ℤ)) : ℝ) + 1) / 2 ^ k) ∪
              Icc ((((-(j : ℤ) : ℤ)) : ℝ) / 2 ^ k) (((((-(j : ℤ) : ℤ)) : ℝ) + 1) / 2 ^ k)) :=
            measure_mono fun t ht => by
              rw [hjn, hjn0]
              have h1 : -dr k j = (-(j : ℝ) - 1) / 2 ^ k := by unfold dr; ring
              have h2 : -dl k j ≤ (-(j : ℝ) + 1) / 2 ^ k := by
                unfold dl
                have := le_max_right 0 (((j : ℝ) - 1) / 2 ^ k)
                have e : (-(j : ℝ) + 1) / 2 ^ k = -(((j : ℝ) - 1) / 2 ^ k) := by ring
                rw [e]; linarith
              rcases le_total t (-(j : ℝ) / 2 ^ k) with h | h
              · refine Or.inl ⟨h1 ▸ ht.1, ?_⟩
                rw [show -(j : ℝ) - 1 + 1 = -(j : ℝ) by ring]; exact h
              · exact Or.inr ⟨h, ht.2.trans h2⟩
        _ ≤ _ + _ := measure_union_le _ _
        _ ≤ (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ + (((2 * n + 1 : ℕ) : ℝ≥0∞) + 1)⁻¹ :=
            add_le_add (hcell _ (hab' _ (by omega) (by omega)))
              (hcell _ (hab' _ (by omega) (by omega)))
        _ = _ := hsum
  · have hU : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici 0 := by
      ext t
      simp only [mem_iUnion, mem_Icc, mem_Ici]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨⌈t⌉₊, h, Nat.le_ceil t⟩⟩
    have htop : ν (Ici 0) = ⊤ := measure_Ici_eq_top_of_infQ hν hinf
    have ht : Tendsto (fun n : ℕ => ν (Icc (0 : ℝ) n)) atTop (𝓝 ⊤) := by
      rw [← htop, ← hU]
      exact tendsto_measure_iUnion_atTop fun n m hnm =>
        Icc_subset_Icc_right (by exact_mod_cast hnm)
    obtain ⟨r, hr⟩ := (ht.eventually (lt_mem_nhds (ENNReal.natCast_lt_top N))).exists
    exact ⟨r, by rw [hrd _ _ (Or.inr le_rfl)]; exact hr.le⟩

end RTMeas
end R18
end QuantumZipper
