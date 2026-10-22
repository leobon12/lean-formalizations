import HigherDimLQGMetric.DGZ.TightNondegPt
import HigherDimLQGContinuity.Core.Interfaces

/-!
# Uniform DGZ Lemma 6.5: point-to-point distances are not too small (packet U4)

Blueprint Part D, `d:lem-u65`(a) (NA3 §2.7, N-M14; [8]-bp `r2:lem:65` verbatim). Port of
`HigherDimLQGMetric.DGZ.nondeg_pt` (`DGZ/TightNondegPt.lean`) with the constant chosen before `ξ`.

**Statement** (`nondeg_pt_unif`). Let `d ≥ 2`, `κ` admissible, `q ∈ (0, 1)` and `0 < r ≤ r_d := 1/(10√d)`. There
is `c = c(d, q, r) > 0` such that for **every** `ξ ≥ 0`, every dyadic realization, every `n`, `x ∈ ∂B_r(0)` and
`y ∈ ∂B_{2r}(0)`: `P[D_n(x, y; B_{3r}(0)) > c a^ξ_n(q)] ≥ c`.

**Proof.** The sealed proof verbatim; it uses `ξ` only through `0 ≤ ξ` (monotonicity of the functional
`φ ↦ D^ξ[φ](x, y; V)` for FKG, `DGZ.isMonotoneFunctional_lfppDistOn`), and its constant
`c := min(1/(2J), 1 - q^{1/J})`, `J = 2⌈1/(2r)⌉`, does not involve `ξ`. The equal-step chain of rigid motions
(`DGZ.npChain*`, L3b3's zigzag), FKG for decreasing events (`DGZ.fkg_decreasing_le`), the invariance of the law under
rigid motions and the lower-quantile bound `P[D_n(0, e₁; B₂(0)) < a^ξ_n(q)] ≤ q` are all `ξ`-free.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLQGMetric.DGZ
open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-- **Uniform DGZ Lemma 6.5** (Part D `d:lem-u65`(a); port of `DGZ.nondeg_pt`): for `d ≥ 2`, `κ` admissible,
`q ∈ (0, 1)` and `0 < r ≤ 1/(10√d)` there is `c > 0` with `P[D_n(x, y; B_{3r}(0)) > c a^ξ_n(q)] ≥ c` for every
`ξ ≥ 0`, every dyadic realization, every `n`, `x ∈ ∂B_r(0)` and `y ∈ ∂B_{2r}(0)`. -/
theorem nondeg_pt_unif (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {q : ℝ≥0∞} (hq0 : 0 < q)
    (hq1 : q < 1) {r : ℝ} (hr : 0 < r) (hrd : r * (10 * Real.sqrt d) ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : ℝ, 0 ≤ ξ → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ), IsDyadicRealization κ P W H → ∀ n : ℕ,
        ∀ x ∈ lsph (0 : Rd d) r, ∀ y ∈ lsph (0 : Rd d) (2 * r),
          ENNReal.ofReal c ≤ P {ω | c * aQ P H ξ n q <
            lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 * r)) x y} := by
  have hd0 : 0 < d := by omega
  -- the chain parameters
  set K : ℕ := ⌈1 / (2 * r)⌉₊ with hK
  have hK1 : 1 ≤ K := Nat.one_le_iff_ne_zero.2 fun h0 => by
    have := Nat.ceil_eq_zero.1 h0
    have : 0 < 1 / (2 * r) := by positivity
    linarith
  have hKr : 1 ≤ 2 * K * r := by
    have h1 : 1 / (2 * r) ≤ K := Nat.le_ceil _
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  set s : ℝ := 1 / (2 * K) with hs
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hs0 : 0 < s := by positivity
  have hsr : s ≤ r := by
    rw [hs, div_le_iff₀ (by positivity)]; linarith
  set J : ℕ := 2 * K with hJ
  have hJpos : (0 : ℝ) < J := by positivity
  have hJs : (J : ℝ) * s = 1 := by rw [hJ, hs]; push_cast; field_simp
  -- the quantile constant
  set qr : ℝ := q.toReal with hqr
  have hqne : q ≠ ⊤ := ne_top_of_lt hq1
  have hqr0 : 0 < qr := ENNReal.toReal_pos hq0.ne' hqne
  have hqr1 : qr < 1 := by
    have := (ENNReal.toReal_lt_toReal hqne ENNReal.one_ne_top).2 hq1
    rwa [ENNReal.toReal_one] at this
  set c' : ℝ := 1 - qr ^ (1 / (J : ℝ)) with hc'
  have hc'0 : 0 < c' := by
    have : qr ^ (1 / (J : ℝ)) < 1 := Real.rpow_lt_one hqr0.le hqr1 (by positivity)
    linarith
  set c : ℝ := min (1 / (2 * J)) c' with hc
  have hc0 : 0 < c := lt_min (by positivity) hc'0
  refine ⟨c, hc0, fun ξ hξ Ω _ P W H hH n x hx y hy => ?_⟩
  have hW := hH.whiteNoise
  have := hW.isProbabilityMeasure
  have hX := hH.band n
  set a := aQ P H ξ n q with ha
  have ha0 : 0 < a := tight_aQ_pos hd0 hH ξ n hq0 hq1
  set t : ℝ := a / (2 * J) with ht
  -- geometry
  set ϱ : ℝ := ‖y - x‖ with hϱ
  have hϱr : r ≤ ϱ := np_le_norm_sub hx hy
  have hsϱ : s ≤ ϱ := hsr.trans hϱr
  have hϱ3 : ϱ ≤ Real.sqrt d * (3 * r) := np_norm_sub_le hx hy
  have hx3 : x ∈ obox (0 : Rd d) (3 * r) := np_lsph_subset_obox (by linarith) hx
  have hy3 : y ∈ obox (0 : Rd d) (3 * r) := np_lsph_subset_obox (by linarith) hy
  set T : ℕ → Rd d → Rd d := fun i z => npChainBase d s x y i + (1 : ℝ) • npChainRefl d s x y i z
    with hT
  set Vi : ℕ → Set (Rd d) := fun i => T i '' obox (0 : Rd d) (3 * r) with hVi
  have hVcube : ∀ i, i < J → Vi i ⊆ cube d := by
    rintro i hi _ ⟨w, hw, rfl⟩
    have hz := norm_zigzag_le hd hs0.le hsϱ i
    have his : (i : ℝ) * s ≤ 1 := by
      have : (i : ℝ) ≤ J := by exact_mod_cast hi.le
      nlinarith
    have hwx : ‖w - x‖ ≤ Real.sqrt d * (4 * r) := norm_sub_le_of_forall_abs_le fun j => by
      have h1 := hw j
      have h2 := hx.1 j
      simp only [PiLp.zero_apply, sub_zero] at h1 h2
      calc |w j - x j| ≤ |w j| + |x j| := abs_sub _ _
        _ ≤ 4 * r := by linarith
    have hnorm : ‖T i w‖ < 2 := by
      simp only [hT, npChainBase]
      rw [sim_one_apply]
      calc ‖npChainPt d s x y i + npChainRefl d s x y i (w - x)‖
          ≤ ‖npChainPt d s x y i‖ + ‖npChainRefl d s x y i (w - x)‖ := norm_add_le _ _
        _ = ‖npChainPt d s x y i‖ + ‖w - x‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ (i * s + ϱ) + Real.sqrt d * (4 * r) := by rw [npChainPt]; linarith
        _ < 2 := by nlinarith
    intro j
    exact lt_of_le_of_lt (HigherDimLFPP.DGZ.abs_apply_le_norm _ j) hnorm
  have hVopen : ∀ i, IsOpen (Vi i) := fun i =>
    isOpen_image_sim _ _ one_pos (HigherDimLFPP.DGZ.isOpen_obox 0 (3 * r))
  have hj : ∀ i, PcwJoined (Vi i) (npChainPt d s x y i) (npChainPt d s x y (i + 1)) := by
    intro i
    rw [← npChain_sim_left s x y i, ← npChain_sim_right hd hs0.le hsϱ i]
    exact PcwJoined.of_convex (convex_image_sim _ _ _ (HigherDimLFPP.DGZ.convex_obox 0 _))
      (mem_image_of_mem _ hx3) (mem_image_of_mem _ hy3)
  -- the chain bound for `D_n(0, e₁; B₂(0))`
  have hchain : ∀ ω, lfppDistance d ξ (fun z => H n z ω) ≤
      ∑ i ∈ Finset.range J, lfppDistOn ξ (fun z => H n z ω) (Vi i) (T i x) (T i y) := by
    intro ω
    set Wi' : ℕ → Set (Rd d) := fun i => if i < J then Vi i else cube d with hWi'
    have hW' : ∀ i, Wi' i ⊆ cube d := fun i => by
      simp only [hWi']
      split_ifs with h'
      · exact hVcube i h'
      · exact le_rfl
    have hj' : ∀ i < J, PcwJoined (Wi' i) (npChainPt d s x y i) (npChainPt d s x y (i + 1)) :=
      fun i hi => by simp only [hWi', ite_eq_left hi]; exact hj i
    have hsum := lfppDistOn_le_sum (ζ := ξ) ((hX.continuous ω)) (npChainPt d s x y) Wi' hW' J hj'
    have h0 : npChainPt d s x y 0 = 0 := by rw [npChainPt, zigzag_zero]
    have h1 : npChainPt d s x y J = e₁ d := by
      rw [npChainPt, hJ, zigzag_two_mul]
      have : 2 * (K : ℝ) * s = 1 := by rw [← hJs, hJ]; push_cast; ring
      rw [this, one_smul]
    rw [h0, h1, ← lfppDistance_eq_lfppDistOn] at hsum
    refine hsum.trans_eq (Finset.sum_congr rfl fun i hi => ?_)
    have hi' : i < J := Finset.mem_range.1 hi
    simp only [hWi', ite_eq_left hi']
    have e1 : T i x = npChainPt d s x y i := npChain_sim_left s x y i
    have e2 : T i y = npChainPt d s x y (i + 1) := npChain_sim_right hd hs0.le hsϱ i
    rw [e1, e2]
  -- FKG for the decreasing events
  have hfkg := fkg_decreasing_le hκ hW (tb_inv_two_pow_pos n) hX
    (isCompact_cbox (0 : Rd d) 2) (Finset.range J)
    (F := fun i φ => lfppDistOn ξ φ (Vi i) (T i x) (T i y))
    (fun i hi => isSupContinuousOn_lfppDistOn
      ((hVcube i (Finset.mem_range.1 hi)).trans cube_subset_cbox_two) ξ _ _)
    (fun i _ => isMonotoneFunctional_lfppDistOn hξ _ _ _) (fun _ => t)
  -- the law of each summand
  have hX1 : IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n / 1) (1 / 1) (H n) :=
    hX.congr_band (div_one _).symm (div_one _).symm
  set p₀ : ℝ≥0∞ := P {ω | lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 * r)) x y ≤ t}
    with hp₀
  have hterm : ∀ i, P {ω | lfppDistOn ξ (fun z => H n z ω) (Vi i) (T i x) (T i y) ≤ t} = p₀ := by
    intro i
    have hlaw := hX.map_lfppDistOn_sim_eq hX1 hW hW hκ (npChainRefl d s x y i)
      (npChainBase d s x y i) one_pos (tb_inv_two_pow_pos n) ξ
      (HigherDimLFPP.DGZ.isOpen_obox 0 (3 * r))
    have hev := measure_apply_le_eq_of_map_eq
      (fun q => measurable_lfppDistOn hX.continuous hX.measurable (hVopen i) ξ _ _)
      (fun q => (measurable_lfppDistOn hX.continuous hX.measurable
        (HigherDimLFPP.DGZ.isOpen_obox 0 (3 * r)) ξ q.1 q.2).const_mul _) hlaw (x, y) t
    simp only [one_mul] at hev
    exact hev
  -- `P[D_n(0, e₁) ≤ a/2] < q`
  have hsub : (⋂ i ∈ Finset.range J,
      {ω | lfppDistOn ξ (fun z => H n z ω) (Vi i) (T i x) (T i y) ≤ t}) ⊆
      {ω | lfppDistance d ξ (fun z => H n z ω) ≤ a / 2} := by
    intro ω hω
    simp only [mem_iInter, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq]
    calc lfppDistance d ξ (fun z => H n z ω)
        ≤ ∑ i ∈ Finset.range J, lfppDistOn ξ (fun z => H n z ω) (Vi i) (T i x) (T i y) :=
          hchain ω
      _ ≤ ∑ _i ∈ Finset.range J, t := Finset.sum_le_sum fun i hi => hω i hi
      _ = a / 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ht]
          field_simp
  have hlt := tight_measure_le_lt_of_lt_aQ hH ξ n hq0 hq1 (x := a / 2) (by linarith)
  have hpow : p₀ ^ J < q := by
    calc p₀ ^ J = ∏ _i ∈ Finset.range J, p₀ := by rw [Finset.prod_const, Finset.card_range]
      _ = ∏ i ∈ Finset.range J,
            P {ω | lfppDistOn ξ (fun z => H n z ω) (Vi i) (T i x) (T i y) ≤ t} :=
          Finset.prod_congr rfl fun i _ => (hterm i).symm
      _ ≤ _ := hfkg
      _ ≤ _ := measure_mono hsub
      _ < q := hlt
  -- from `p₀^J < q` to `p₀ < q^{1/J}`
  have hp₀ne : p₀ ≠ ⊤ := measure_ne_top _ _
  set p : ℝ := p₀.toReal with hp
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hpp : p₀ = ENNReal.ofReal p := (ENNReal.ofReal_toReal hp₀ne).symm
  have hpJ : p ^ J < qr := by
    have h1 : ENNReal.ofReal (p ^ J) < ENNReal.ofReal qr := by
      rw [ENNReal.ofReal_pow hp0, ← hpp, hqr, ENNReal.ofReal_toReal hqne]
      exact hpow
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  have hproot : p < qr ^ (1 / (J : ℝ)) := by
    by_contra hge
    push Not at hge
    have : qr ≤ p ^ J := by
      calc qr = (qr ^ (1 / (J : ℝ))) ^ J := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hqr0.le, one_div_mul_cancel hJpos.ne',
              Real.rpow_one]
        _ ≤ p ^ J := pow_le_pow_left₀ (Real.rpow_nonneg hqr0.le _) hge J
    linarith
  -- conclusion
  have hDm : MeasurableSet
      {ω | lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 * r)) x y ≤ t} :=
    measurableSet_le (measurable_lfppDistOn hX.continuous hX.measurable
      (HigherDimLFPP.DGZ.isOpen_obox 0 (3 * r)) ξ x y) measurable_const
  have hcompl : P {ω | t < lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 * r)) x y} =
      1 - p₀ := by
    rw [← prob_compl_eq_one_sub hDm]
    congr 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  have hct : c * a ≤ t := by
    rw [ht, div_eq_mul_inv, mul_comm a]
    exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (by rw [one_div])) ha0.le
  calc ENNReal.ofReal c ≤ ENNReal.ofReal (1 - p) :=
        ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans (by rw [hc']; linarith))
    _ = 1 - p₀ := by rw [ENNReal.ofReal_sub _ hp0, ENNReal.ofReal_one, ← hpp]
    _ = P {ω | t < lfppDistOn ξ (fun z => H n z ω) (obox (0 : Rd d) (3 * r)) x y} := hcompl.symm
    _ ≤ _ := measure_mono fun ω hω => lt_of_le_of_lt hct hω

end HigherDimLQGContinuity
