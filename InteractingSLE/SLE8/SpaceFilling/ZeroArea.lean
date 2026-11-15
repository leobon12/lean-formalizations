import InteractingSLE.SLE8.SpaceFilling.Moment
import InteractingSLE.SLE8.SpaceFilling.Cover
import InteractingSLE.SLE8.SpaceFilling.ZeroAreaDet
import InteractingSLE.Frozen.SLE8.ContinuousTrace

/-!
# κ = 8 space filling, Proposition 5: fixed-time hull boundaries have zero area

Source: the user's note *Space filling of a continuous SLE₈ trace*
(`source/external/SLE8SF/sle8_space_filling_formalization.pdf`, §3, Proposition 5 and its proof,
p. 5).

**Proposition 5.** For chordal SLE₈ (`W = √8 B`) and each deterministic `t > 0`, almost surely
`H^{14/9}(∂K_t ∩ ℍ) = 0` and `area(∂K_t) = 0`.

Here `K_t ∩ ℍ = fwdHull (drive 8 B ω) t` and `D_t = ℍ \ K_t`; boundaries are taken in `ℂ`, and
`∂K_t ∩ ℍ = ∂D_t ∩ ℍ` (`frontier_fwdHull_inter_H`). The statements hold for every `t ≥ 0`.

## Proof (the note's)

* **Tonelli and Lemma 3** (`lintegral_dyEnergy_le`): with `|D_m(L)| = 2L 2^m`,
  `E[E_{L,h}(F_t)] ≤ C_{L,h} Σ_m 2^{m/18} 2^m 2^{-10m/9} = C_{L,h} Σ_m 2^{-m/18} < ∞`, so the weighted
  energy is finite almost surely, simultaneously for all `L ≥ 1` and `h = 1/k`
  (`ae_dyEnergy_lt_top`).
* **(L1)**: the frozen trace theorem (`ae_exists_continuous_trace`) makes `γ` a continuous Loewner
  trace (`ae_exists_isLoewnerTrace`), so `F_t` extends continuously to `ℍ̄`
  (`IsLoewnerTrace.fiber_hyps`), and Lemma 4 applies to `f = F̄_t`.
* **Cover** (`frontier_inter_H_subset_iUnion`, using (L3)): `∂D_t ∩ ℍ` is covered by the countably
  many sets `F̄_t([-L, L]) ∩ {Im w ≥ 2h}`, each of zero `H^{14/9}`-measure.
* Since `14/9 < 2`, this part of the boundary has zero area; the rest lies on `ℝ`.

## Main results

* `ae_hausdorffMeasure_frontier_fwdHull_inter_H_eq_zero`, `ae_volume_frontier_fwdHull_eq_zero`,
  and the joint form `ae_hausdorffMeasure_and_volume_frontier_fwdHull_eq_zero` — **Proposition 5**
  for `∂K_t`; the same for `∂D_t`: `ae_hausdorffMeasure_frontier_inter_H_eq_zero`,
  `ae_volume_frontier_eq_zero`; and for every `K ⊆ ℍ̄` with `K ∩ ℍ = K_t ∩ ℍ`:
  `ae_forall_hausdorffMeasure_and_volume_frontier_eq_zero`.
* `ae_hausdorffMeasure_frontier_inter_H_eq_zero_of_ae_isLoewnerTrace` — the proof under the
  hypothesis of the note's Theorem 1 (an almost surely continuous trace), in the generation form
  `IsLoewnerTrace`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.SLE8.SpaceFilling

open QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {t h : ℝ}

/-! ## The expected weighted energy -/

/-- Lemma 3 at a Whitney point: `E[a_I^{14/9}] ≤ C_{L,h} |I|^{10/9}` for `I ∈ D_m(L)`. -/
theorem lintegral_dyWeight_rpow_le (hB : IsBrownianReal B P) (ht : 0 ≤ t) {L m : ℕ} {j : ℤ}
    (hj : j ∈ dyIdx L m) (hh : 0 < h) :
    ∫⁻ ω, ENNReal.ofReal (dyWeight (fwdMapInv (drive 8 B ω) t) h m j ^ (14 / 9 : ℝ)) ∂P ≤
      ENNReal.ofReal (h ^ (-(2 / 9 : ℝ)) * ((L : ℝ) ^ 2 + 1) ^ (1 / 3 : ℝ) *
        (1 / 2 ^ m) ^ (10 / 9 : ℝ)) := by
  have hx : |((j : ℝ) + 1 / 2) / 2 ^ m| ≤ L := by simpa using abs_dyPt_re_le hj
  have hy : (0 : ℝ) < 1 / 2 ^ m := by positivity
  have hy1 : (1 : ℝ) / 2 ^ m ≤ 1 := by
    rw [div_le_one (two_pow_pos_real m)]; exact one_le_pow₀ (by norm_num)
  refine le_trans (le_of_eq ?_)
    (lintegral_indicator_rpow_deriv_fwdMapInv_le_of_abs_le hB ht hx hy hy1 hh)
  refine lintegral_congr fun ω => ?_
  simp only [dyWeight, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [dyPt]
  split_ifs
  · rfl
  · rw [Real.zero_rpow (by norm_num), ENNReal.ofReal_zero]

/-- The weight is measurable in `ω` for a version of `B` with continuous paths started at `0`. -/
theorem measurable_ofReal_dyWeight_rpow (hBm : ∀ s, Measurable (B s))
    (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (ht : 0 ≤ t) (h : ℝ) (m : ℕ) (j : ℤ) :
    Measurable fun ω => ENNReal.ofReal (dyWeight (fwdMapInv (drive 8 B ω) t) h m j ^ (14 / 9 : ℝ)) := by
  obtain ⟨hF, hD⟩ := measurable_fwdMapInv_deriv_drive hBm hBc hB0 8 ht (dyPt_mem_H m j)
  have hw : Measurable fun ω => dyWeight (fwdMapInv (drive 8 B ω) t) h m j := by
    unfold dyWeight
    exact Measurable.ite (measurableSet_le measurable_const (Complex.measurable_im.comp hF))
      (measurable_const.mul hD) measurable_const
  exact (hw.pow_const _).ennreal_ofReal

/-- The weighted energy is measurable in `ω` (same version of `B`). -/
theorem measurable_dyEnergy (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (ht : 0 ≤ t) (L : ℕ) (h : ℝ) :
    Measurable fun ω => dyEnergy (fwdMapInv (drive 8 B ω) t) L h := by
  unfold dyEnergy
  refine Measurable.tsum fun m => Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ fun j _ => measurable_ofReal_dyWeight_rpow hBm hBc hB0 ht h m j

/-- The counting identity `2^{m/18} · |D_m(L)| · c 2^{-10m/9} = 2Lc (2^{-1/18})^m`. -/
theorem dyadic_count_identity (L : ℕ) (c : ℝ) (m : ℕ) :
    (2 : ℝ) ^ ((m : ℝ) / 18) * (((2 * L * 2 ^ m : ℕ) : ℝ) * (c * (1 / 2 ^ m) ^ (10 / 9 : ℝ))) =
      2 * L * c * ((2 : ℝ) ^ (-(1 / 18 : ℝ))) ^ m := by
  have h2m : (1 : ℝ) / 2 ^ m = (2 : ℝ) ^ (-(m : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  rw [h2m, ← Real.rpow_mul (by norm_num), ← two_rpow_mul_nat]
  push_cast
  rw [← Real.rpow_natCast 2 m]
  have e : (2 : ℝ) ^ ((m : ℝ) / 18) * 2 ^ (m : ℝ) * 2 ^ (-(m : ℝ) * (10 / 9)) =
      2 ^ (-(1 / 18 : ℝ) * m) := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1; ring
  calc (2 : ℝ) ^ ((m : ℝ) / 18) * (2 * L * 2 ^ (m : ℝ) * (c * 2 ^ (-(m : ℝ) * (10 / 9))))
      = 2 * L * c * ((2 : ℝ) ^ ((m : ℝ) / 18) * 2 ^ (m : ℝ) * 2 ^ (-(m : ℝ) * (10 / 9))) := by
        ring
    _ = _ := by rw [e]

/-- `Σ_m (2^{-1/18})^m < ∞` in `[0, ∞]`. -/
theorem tsum_ofReal_two_rpow_pow_ne_top :
    ∑' m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 18 : ℝ))) ^ m ≠ ∞ := by
  rw [ENNReal.tsum_geometric, ne_eq, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le,
    ← ENNReal.ofReal_one]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

/-- **Tonelli and Lemma 3.** `E[E_{L,h}(F_t)] ≤ 2L C_{L,h} Σ_m 2^{-m/18}`. -/
theorem lintegral_dyEnergy_le (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hB : IsBrownianReal B P) (ht : 0 ≤ t) (L : ℕ) (hh : 0 < h) :
    ∫⁻ ω, dyEnergy (fwdMapInv (drive 8 B ω) t) L h ∂P ≤
      ENNReal.ofReal (2 * L * (h ^ (-(2 / 9 : ℝ)) * ((L : ℝ) ^ 2 + 1) ^ (1 / 3 : ℝ))) *
        ∑' m : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 18 : ℝ))) ^ m := by
  set c : ℝ := h ^ (-(2 / 9 : ℝ)) * ((L : ℝ) ^ 2 + 1) ^ (1 / 3 : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hmeasm : ∀ m : ℕ, Measurable fun ω => ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) / 18)) *
      ∑ j ∈ dyIdx L m, ENNReal.ofReal (dyWeight (fwdMapInv (drive 8 B ω) t) h m j ^ (14 / 9 : ℝ)) :=
    fun m => Measurable.const_mul
      (Finset.measurable_sum _ fun j _ => measurable_ofReal_dyWeight_rpow hBm hBc hB0 ht h m j) _
  unfold dyEnergy
  rw [lintegral_tsum fun m => (hmeasm m).aemeasurable]
  · rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun m => ?_
    have hmeas : Measurable fun ω => ∑ j ∈ dyIdx L m,
        ENNReal.ofReal (dyWeight (fwdMapInv (drive 8 B ω) t) h m j ^ (14 / 9 : ℝ)) :=
      Finset.measurable_sum _ fun j _ => measurable_ofReal_dyWeight_rpow hBm hBc hB0 ht h m j
    rw [lintegral_const_mul _ hmeas,
      lintegral_finsetSum _ fun j _ => measurable_ofReal_dyWeight_rpow hBm hBc hB0 ht h m j]
    calc ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) / 18)) * ∑ j ∈ dyIdx L m,
          ∫⁻ ω, ENNReal.ofReal (dyWeight (fwdMapInv (drive 8 B ω) t) h m j ^ (14 / 9 : ℝ)) ∂P
        ≤ ENNReal.ofReal ((2 : ℝ) ^ ((m : ℝ) / 18)) *
            ((dyIdx L m).card • ENNReal.ofReal (c * (1 / 2 ^ m) ^ (10 / 9 : ℝ))) :=
          mul_le_mul' le_rfl (Finset.sum_le_card_nsmul _ _ _ fun j hj =>
            lintegral_dyWeight_rpow_le hB ht hj hh)
      _ = ENNReal.ofReal (2 * L * c) * ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 18 : ℝ))) ^ m := by
          rw [card_dyIdx, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
            dyadic_count_identity]

/-- **The weighted energy is finite almost surely**, simultaneously for all `L ≥ 1` and
`h = 1/k`. -/
theorem ae_dyEnergy_lt_top (hBm : ∀ s, Measurable (B s)) (hBc : ∀ ω, Continuous (B · ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hB : IsBrownianReal B P) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ L k : ℕ,
      dyEnergy (fwdMapInv (drive 8 B ω) t) (L + 1) (1 / ((k : ℝ) + 1)) < ∞ := by
  refine ae_all_iff.2 fun L => ae_all_iff.2 fun k => ?_
  have hh : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  refine ae_lt_top' (measurable_dyEnergy hBm hBc hB0 ht _ _).aemeasurable ?_
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top tsum_ofReal_two_rpow_pow_ne_top)
    (lintegral_dyEnergy_le hBm hBc hB0 hB ht (L + 1) hh)

/-! ## Proposition 5 -/

/-- **Proposition 5 under the hypothesis of Theorem 1**: if almost surely the SLE₈ chain has a
continuous Loewner trace (in the generation form `IsLoewnerTrace`), then for each deterministic
`t ≥ 0`, almost surely `H^{14/9}(∂D_t ∩ ℍ) = 0`. -/
theorem ae_hausdorffMeasure_frontier_inter_H_eq_zero_of_ae_isLoewnerTrace
    (hB : IsBrownianReal B P) (ht : 0 ≤ t)
    (htr : ∀ᵐ ω ∂P, ∃ η, IsLoewnerTrace (drive 8 B ω) η) :
    ∀ᵐ ω ∂P, μH[14 / 9] (frontier (H \ fwdHull (drive 8 B ω) t) ∩ H) = 0 := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hB''br, hB''eq⟩ := RS.exists_good_version0 hB
  filter_upwards [ae_dyEnergy_lt_top hB''m hB''c hB''0 hB''br ht, htr, hB''eq] with
    ω hEω hη' hω
  obtain ⟨η, hη⟩ := hη'
  have hdr : drive 8 B ω = drive 8 B'' ω := funext fun s => by simp [drive, hω]
  rw [hdr] at hη ⊢
  have hW : Continuous (drive 8 B'' ω) := drive_continuous (hB''c ω)
  have hW0 : drive 8 B'' ω 0 = 0 := by simp [drive, hB''0]
  obtain ⟨hfd, hfc, hfi, -⟩ := hη.fiber_hyps hW hW0 ht
  have heq : EqOn (extendFrom H (fwdMapInv (drive 8 B'' ω) t)) (fwdMapInv (drive 8 B'' ω) t) H :=
    fun z hz => extendFrom_H_eq (InteractingSLE.continuousOn_fwdMapInv hW hW0 ht) hz
  refine measure_mono_null (frontier_inter_H_subset_iUnion hW hW0 ht hfc)
    (measure_iUnion_null fun L => measure_iUnion_null fun k => ?_)
  refine hausdorffMeasure_image_Icc_inter_eq_zero hfd hfi hfc (by omega) (by positivity) ?_
  rw [dyEnergy_congr heq]
  exact (hEω L k).ne

/-- **(L1) for SLE₈.** Almost surely the SLE₈ chain has a continuous Loewner trace (the frozen
Theorem 1.1 of the SLE₈ note, `ae_exists_continuous_trace`, in the form `IsLoewnerTrace`). -/
theorem ae_exists_isLoewnerTrace (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ η, IsLoewnerTrace (drive 8 B ω) η := by
  filter_upwards [ae_exists_continuous_trace hB] with ω hω
  obtain ⟨γ, -, hγc, -, hγ0, hgen⟩ := hω
  exact ⟨_, isLoewnerTrace_of_connectedComponentIn hγc hγ0 hgen⟩

/-- **Proposition 5** (domain form): for each deterministic `t ≥ 0`, almost surely
`H^{14/9}(∂D_t ∩ ℍ) = 0`, `D_t = ℍ \ K_t`. -/
theorem ae_hausdorffMeasure_frontier_inter_H_eq_zero (hB : IsBrownianReal B P) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, μH[14 / 9] (frontier (H \ fwdHull (drive 8 B ω) t) ∩ H) = 0 :=
  ae_hausdorffMeasure_frontier_inter_H_eq_zero_of_ae_isLoewnerTrace hB ht
    (ae_exists_isLoewnerTrace hB)

/-- **Proposition 5**: for each deterministic `t ≥ 0`, almost surely `H^{14/9}(∂K_t ∩ ℍ) = 0`. -/
theorem ae_hausdorffMeasure_frontier_fwdHull_inter_H_eq_zero (hB : IsBrownianReal B P)
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, μH[14 / 9] (frontier (fwdHull (drive 8 B ω) t) ∩ H) = 0 := by
  filter_upwards [ae_hausdorffMeasure_frontier_inter_H_eq_zero hB ht] with ω hω
  rwa [frontier_fwdHull_inter_H]

/-- **Proposition 5** (area, domain form): for each deterministic `t ≥ 0`, almost surely
`area(∂D_t) = 0`. -/
theorem ae_volume_frontier_eq_zero (hB : IsBrownianReal B P) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, volume (frontier (H \ fwdHull (drive 8 B ω) t)) = 0 := by
  filter_upwards [ae_hausdorffMeasure_frontier_inter_H_eq_zero hB ht] with ω hω
  exact volume_frontier_eq_zero_of_hausdorffMeasure
    (sdiff_subset.trans QuantumZipper.H_subset_Hbar) hω

/-- **Proposition 5** (area): for each deterministic `t ≥ 0`, almost surely `area(∂K_t) = 0`. -/
theorem ae_volume_frontier_fwdHull_eq_zero (hB : IsBrownianReal B P) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, volume (frontier (fwdHull (drive 8 B ω) t)) = 0 := by
  filter_upwards [ae_hausdorffMeasure_frontier_fwdHull_inter_H_eq_zero hB ht] with ω hω
  exact volume_frontier_eq_zero_of_hausdorffMeasure
    (fun _ hz => QuantumZipper.H_subset_Hbar hz.1) hω

/-- **Proposition 5**, both conclusions: for each deterministic `t ≥ 0`, almost surely
`H^{14/9}(∂K_t ∩ ℍ) = 0` and `area(∂K_t) = 0`. -/
theorem ae_hausdorffMeasure_and_volume_frontier_fwdHull_eq_zero (hB : IsBrownianReal B P)
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, μH[14 / 9] (frontier (fwdHull (drive 8 B ω) t) ∩ H) = 0 ∧
      volume (frontier (fwdHull (drive 8 B ω) t)) = 0 := by
  filter_upwards [ae_hausdorffMeasure_frontier_fwdHull_inter_H_eq_zero hB ht] with ω hω
  exact ⟨hω, volume_frontier_eq_zero_of_hausdorffMeasure
    (fun _ hz => QuantumZipper.H_subset_Hbar hz.1) hω⟩

/-- **Proposition 5 for any closed hull.** Almost surely, for every `K ⊆ ℍ̄` with
`K ∩ ℍ = K_t ∩ ℍ` (`fwdHull`), whichever closed half-plane hull `K_t` is meant:
`H^{14/9}(∂K ∩ ℍ) = 0` and `area(∂K) = 0`. -/
theorem ae_forall_hausdorffMeasure_and_volume_frontier_eq_zero (hB : IsBrownianReal B P)
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, K ⊆ Hbar → K ∩ H = fwdHull (drive 8 B ω) t →
      μH[14 / 9] (frontier K ∩ H) = 0 ∧ volume (frontier K) = 0 := by
  filter_upwards [ae_hausdorffMeasure_frontier_fwdHull_inter_H_eq_zero hB ht] with ω hω K hK hKH
  have h1 : μH[14 / 9] (frontier K ∩ H) = 0 := by
    rw [frontier_inter_H_eq_of_inter_H_eq hKH]; exact hω
  exact ⟨h1, volume_frontier_eq_zero_of_hausdorffMeasure hK h1⟩

end InteractingSLE.SLE8.SpaceFilling
