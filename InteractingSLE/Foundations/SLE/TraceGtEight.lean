import InteractingSLE.Foundations.SLE.TailBound
import QuantumZipper.Proofs.RS.TraceGrid
import QuantumZipper.Proofs.RS.TraceMain
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.TraceGen

/-!
# Rohde–Schramm: the SLE trace for `κ > 8`

Design `planning/INFRA-GEO.md` §3 "SLE", packet GEO-RS8; design handoff
`planning/handoffs/INFRA-GEO-ARCH.md` §D.2.

QuantumZipper proves the existence of the SLE trace for `0 < κ < 8` (`QuantumZipper.RS.ae_sleTrace_good`
and its consumers). Its only `κ`-dependent input is the grid bound `ae_grid_bound_le_eight`, whose
tail estimate (E2) needs `ζ ≥ 0`. For `κ > 8` we replace E2 by `rs_tail_bound_axis_of_rsZeta_nonpos`
(`ζ ≤ 0`, file `TailBound.lean`) at `r = rsR1 κ`, where `λ + ζ = (8+κ)²/(16κ) > 2`. Everything after
the grid bound (the interpolation `tr2_interp`, the radial-limit argument `trace_of_radialBound`,
the generation of the hulls and the measurable version) is deterministic or `κ`-agnostic and is
reused from QuantumZipper; the proofs below mirror `RS/TraceGrid.lean`, `RS/TraceMain.lean`,
`RS/TraceMeas.lean` and `RS/TraceGen.lean`.

## Main statements (namespace `InteractingSLE`, all for `κ > 8`)

* `ae_grid_bound_of_eight_lt`: for `θ < θ₁(κ) = 2(κ−8)²/((8+κ)(8+3κ))`, a.s. for every `N` there is
  `C` with `‖(f̂_{k/4ⁿ})'(i2^{−n})‖ ≤ C 2^{n(1−θ)}` whenever `k/4ⁿ ≤ N`.
* `ae_radial_bound_of_eight_lt`: there is `δ > 0` such that a.s. `‖(f̂_t)'(iy)‖ ≤ C_N y^{δ−1}` on
  `[0,N] × (0,1]`.
* `ae_sleTrace_good_of_eight_lt`: the trace `η = sleTrace κ B ω` exists, `η 0 = 0`, `η` is
  continuous on `[0,∞)`, and `‖f̂_t(iy) − η(t)‖ ≤ C_N y^δ`.
* `exists_measurable_sleTrace_of_eight_lt`: a jointly measurable, continuous version of the trace.
* `rohdeSchrammTraceGen_of_eight_lt`: `QuantumZipper.Blueprint.RohdeSchrammTraceGen κ` (the trace
  generates the hulls).

References: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 3.6
(p. 16), Thm 5.1 (p. 20); A. Kemppainen, *Schramm–Loewner Evolution* (2017), Prop. 5.10, Thm 5.2,
Def. 5.3 (pp. 76, 99, 111–112).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Real

namespace InteractingSLE

open QuantumZipper QuantumZipper.RS

section SLE

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The grid bound for `κ > 8` -/

/-- The per-level decay factor `q = 2^{−((1−θ)λ + ζ)}` of the grid bound for `κ > 8`, at
`r = rsR1 κ`. -/
def rsGridQ8 (κ θ : ℝ) : ℝ :=
  (2 : ℝ) ^ (-((1 - θ) * rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ)))

theorem rsGridQ8_pos (κ θ : ℝ) : 0 < rsGridQ8 κ θ := Real.rpow_pos_of_pos (by norm_num) _

/-- `4 q < 1` for `κ > 8` and `θ < θ₁(κ)`. -/
theorem four_mul_rsGridQ8_lt_one {κ θ : ℝ} (hκ : 8 < κ) (hθ : θ < rsTheta1 κ) :
    4 * rsGridQ8 κ θ < 1 := by
  have hkey := two_lt_rsGridExp_of_eight_lt hκ hθ
  have h14 : ((1 : ℝ) / 2) ^ (2 : ℝ) = 1 / 4 := by
    rw [Real.rpow_two]
    norm_num
  have hlt := Real.rpow_lt_rpow_of_exponent_gt (x := (1 : ℝ) / 2)
    (y := (1 - θ) * rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ)) (z := (2 : ℝ)) (by norm_num)
    (by norm_num) hkey
  rw [h14] at hlt
  have hq : rsGridQ8 κ θ =
      ((1 : ℝ) / 2) ^ ((1 - θ) * rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ)) := by
    rw [rsGridQ8, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hq]
  linarith

/-- **One grid point, `κ > 8`.** `rs_tail_bound_axis_of_rsZeta_nonpos` with `r = rsR1 κ`,
`β = θ`, `y = 2^{−n}` and `T ≤ N`:
`P{‖(u_T)'(i2^{−n})‖ > 2^{n(1−θ)}} ≤ (1 + 4N)^{−ζ/2} qⁿ`. -/
theorem rs_grid_tail_le_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) (θ : ℝ)
    (n : ℕ) {T N : ℝ} (hT : 0 ≤ T) (hTN : T ≤ N) :
    P {ω | (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) <
        ‖deriv (revMap (drive κ B ω) T) (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) * Complex.I)‖}
      ≤ ENNReal.ofReal ((1 + 4 * N) ^ (-rsZeta κ (rsR1 κ) / 2) * (rsGridQ8 κ θ) ^ n) := by
  have hκ0 : 0 < κ := by linarith
  have hy : 0 < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hy1 : (2 : ℝ) ^ (-(n : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  have h := rs_tail_bound_axis_of_rsZeta_nonpos (B := B) hB hκ0 (rsR1_nonneg hκ0) hT hy
    (rsLam_rsR1_nonneg hκ0) (rsZeta_rsR1_neg hκ).le θ
  rw [rpow_two_neg_natCast_sub_one n θ,
    rpow_two_neg_natCast_mul n ((1 - θ) * rsLam κ (rsR1 κ) + rsZeta κ (rsR1 κ))] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [rsGridQ8]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)
  refine Real.rpow_le_rpow (by positivity) ?_ (by linarith [rsZeta_rsR1_neg hκ])
  have hy2 : ((2 : ℝ) ^ (-(n : ℝ))) ^ 2 ≤ 1 := pow_le_one₀ hy.le hy1
  linarith

/-- **Grid bound on the imaginary axis at dyadic times, `κ > 8`** (RS Thm 3.6 and (3.19);
Kemppainen Prop. 5.10). For `θ < θ₁(κ) = 2(κ−8)²/((8+κ)(8+3κ))` and `N ∈ ℕ`, almost surely
there is `C` with `‖(f̂_{k/4ⁿ})'(i2^{−n})‖ ≤ C 2^{n(1−θ)}` for all `n, k` with `k/4ⁿ ≤ N`.
Mirror of QuantumZipper's `ae_grid_bound_le_eight`, with the `ζ ≤ 0` tail bound. -/
theorem ae_grid_bound_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) {θ : ℝ}
    (hθ : θ < rsTheta1 κ) (N : ℕ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ n k : ℕ, (k : ℝ) / 4 ^ n ≤ N →
      ‖deriv (fwdMapInv (drive κ B ω) ((k : ℝ) / 4 ^ n)) (Complex.I / 2 ^ n)‖ ≤
        C * 2 ^ ((n : ℝ) * (1 - θ)) := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB'pre : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hB'0 : ∀ᵐ ω ∂P, B' 0 ω = 0 := by
    filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω h1 h2
    rw [h1 0, h2]
  have hq0 : 0 < rsGridQ8 κ θ := rsGridQ8_pos κ θ
  have h4q : 4 * rsGridQ8 κ θ < 1 := four_mul_rsGridQ8_lt_one hκ hθ
  set K : ℝ := (1 + 4 * (N : ℝ)) ^ (-rsZeta κ (rsR1 κ) / 2) with hKdef
  have hK0 : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  -- per-level probability bound
  have hFn : ∀ n : ℕ, P (gridBad κ θ B' N n) ≤
      ENNReal.ofReal (((N : ℝ) * (4 : ℝ) ^ n + 1) * (K * (rsGridQ8 κ θ) ^ n)) := by
    intro n
    have hsub : gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0} ⊆
        ⋃ k ∈ Finset.range (N * 4 ^ n + 1), gridBadRev κ θ B' N n k := by
      rintro ω ⟨⟨k, hk, hbad⟩, h0⟩
      simp only [gridVal] at hbad
      refine Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ?_⟩⟩
      simp only [gridBadRev]
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have ht : 0 ≤ (k : ℝ) / 4 ^ n := by positivity
      have hp : (((2 : ℝ) ^ (-(n : ℝ)) : ℝ) : ℂ) * Complex.I ∈ H :=
        mul_I_mem_H (Real.rpow_pos_of_pos (by norm_num) _)
      have hder := deriv_fwdMapInv_eq_deriv_revMap_revBM κ ht (hB'c ω) h0 hp
      rw [lt_div_iff₀ hpos, one_mul] at hbad
      rwa [hder] at hbad
    have hG0c : P ({ω | B' 0 ω = 0} : Set Ω)ᶜ = 0 := by
      have h : P {ω | ¬ B' 0 ω = 0} = 0 := ae_iff.1 hB'0
      rwa [← show ({ω | B' 0 ω = 0} : Set Ω)ᶜ = {ω | ¬ B' 0 ω = 0} by ext ω; simp] at h
    have h1 : gridBad κ θ B' N n ⊆
        {ω | B' 0 ω = 0}ᶜ ∪ (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0}) := by
      intro ω hω
      by_cases h : ω ∈ {ω | B' 0 ω = 0}
      · exact Or.inr ⟨hω, h⟩
      · exact Or.inl h
    calc P (gridBad κ θ B' N n)
        ≤ P ({ω | B' 0 ω = 0}ᶜ ∪ (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0})) := measure_mono h1
      _ ≤ P {ω | B' 0 ω = 0}ᶜ + P (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0}) :=
          measure_union_le _ _
      _ = P (gridBad κ θ B' N n ∩ {ω | B' 0 ω = 0}) := by rw [hG0c, zero_add]
      _ ≤ P (⋃ k ∈ Finset.range (N * 4 ^ n + 1), gridBadRev κ θ B' N n k) := measure_mono hsub
      _ ≤ ∑ k ∈ Finset.range (N * 4 ^ n + 1), P (gridBadRev κ θ B' N n k) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range (N * 4 ^ n + 1), ENNReal.ofReal (K * (rsGridQ8 κ θ) ^ n) :=
          Finset.sum_le_sum fun k hk => by
            have hT : 0 ≤ (k : ℝ) / 4 ^ n := by positivity
            have hkN : (k : ℝ) / 4 ^ n ≤ N := by
              have hk' : k ≤ N * 4 ^ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
              have hk'' : (k : ℝ) ≤ (N : ℝ) * (4 : ℝ) ^ n := by exact_mod_cast hk'
              rw [div_le_iff₀ (by positivity)]
              exact hk''
            exact rs_grid_tail_le_of_eight_lt
              (UnzipInvariance.isBrownianReal_revBM hB'pre hB'c ((k : ℝ) / 4 ^ n).toNNReal)
              hκ θ n hT hkN
      _ = ENNReal.ofReal (((N : ℝ) * (4 : ℝ) ^ n + 1) * (K * (rsGridQ8 κ θ) ^ n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            (show ((N * 4 ^ n + 1 : ℕ) : ℝ) = (N : ℝ) * (4 : ℝ) ^ n + 1 by push_cast; ring)]
          exact (ENNReal.ofReal_mul (by positivity)).symm
  -- summability of the level probabilities
  have hsumm : Summable fun n : ℕ => ((N : ℝ) * (4 : ℝ) ^ n + 1) * (K * (rsGridQ8 κ θ) ^ n) := by
    have h4qnn : 0 ≤ 4 * rsGridQ8 κ θ := by linarith
    have hgeom4 : Summable fun n : ℕ => (4 * rsGridQ8 κ θ) ^ n :=
      summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg h4qnn]; exact h4q)
    have hgeomq : Summable fun n : ℕ => (rsGridQ8 κ θ) ^ n :=
      summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg hq0.le]; exact lt_of_le_of_lt (by linarith) h4q)
    have h : Summable fun n : ℕ =>
        K * ((N : ℝ) * (4 * rsGridQ8 κ θ) ^ n + 1 * (rsGridQ8 κ θ) ^ n) :=
      ((hgeom4.mul_left (N : ℝ)).add (hgeomq.mul_left 1)).mul_left K
    have hfun : (fun n : ℕ => K * ((N : ℝ) * (4 * rsGridQ8 κ θ) ^ n + 1 * (rsGridQ8 κ θ) ^ n)) =
        fun n : ℕ => ((N : ℝ) * (4 : ℝ) ^ n + 1) * (K * (rsGridQ8 κ θ) ^ n) := by
      funext n
      rw [mul_pow]
      ring
    rwa [hfun] at h
  have htsum : (∑' n, P (gridBad κ θ B' N n)) ≠ ∞ := by
    have h1 : ∑' n, P (gridBad κ θ B' N n) ≤
        ∑' n, ENNReal.ofReal (((N : ℝ) * (4 : ℝ) ^ n + 1) * (K * (rsGridQ8 κ θ) ^ n)) :=
      ENNReal.tsum_le_tsum hFn
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (by positivity) (mul_nonneg hK0 (pow_nonneg hq0.le n))) hsumm] at h1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  -- Borel–Cantelli: a.s. only finitely many bad levels
  filter_upwards [ae_eventually_notMem htsum, hB'eq] with ω hω heq
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.1 hω
  set C : ℝ := 1 + ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (N * 4 ^ n + 1),
    gridVal κ θ B' ω n k with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => gridVal_nonneg κ θ B' ω i j)
  have hdrive : drive κ B' ω = drive κ B ω := by
    funext t
    simp only [drive]
    rw [heq t.toNNReal]
  refine ⟨C, fun n k hk => ?_⟩
  rw [← hdrive, ← ofReal_two_neg_rpow_mul_I n]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) * (1 - θ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hkn : k ≤ N * 4 ^ n := by
    have h1 : (k : ℝ) ≤ (N : ℝ) * (4 : ℝ) ^ n := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ n)] at hk
      exact hk
    have h2 : ((N * 4 ^ n : ℕ) : ℝ) = (N : ℝ) * (4 : ℝ) ^ n := by push_cast; ring
    rw [← h2] at h1
    exact_mod_cast h1
  have hkF : k ∈ Finset.range (N * 4 ^ n + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hkn)
  rcases le_or_gt m n with hmn | hmn
  · have hnot : ω ∉ gridBad κ θ B' N n := hm n hmn
    have hle : gridVal κ θ B' ω n k ≤ 1 := by
      by_contra hc
      exact hnot (show ∃ k ∈ Finset.range (N * 4 ^ n + 1), 1 < gridVal κ θ B' ω n k from
        ⟨k, hkF, not_le.mp hc⟩)
    exact (div_le_iff₀ hpos).mp (hle.trans hC1)
  · have hinner : gridVal κ θ B' ω n k ≤
        ∑ k' ∈ Finset.range (N * 4 ^ n + 1), gridVal κ θ B' ω n k' :=
      Finset.single_le_sum (fun j _ => gridVal_nonneg κ θ B' ω n j) hkF
    have houter : (∑ k' ∈ Finset.range (N * 4 ^ n + 1), gridVal κ θ B' ω n k') ≤
        ∑ n' ∈ Finset.range (m + 1), ∑ k' ∈ Finset.range (N * 4 ^ n' + 1),
          gridVal κ θ B' ω n' k' :=
      Finset.single_le_sum (f := fun n' : ℕ =>
          ∑ k' ∈ Finset.range (N * 4 ^ n' + 1), gridVal κ θ B' ω n' k')
        (fun i _ => Finset.sum_nonneg fun j _ => gridVal_nonneg κ θ B' ω i j)
        (Finset.mem_range.2 (Nat.lt_succ_of_lt hmn))
    have hC : gridVal κ θ B' ω n k ≤ C := by
      rw [hCdef]
      linarith
    exact (div_le_iff₀ hpos).mp hC

/-! ### Radial derivative bound and the trace for `κ > 8` -/

/-- **Almost sure radial derivative bound, `κ > 8`** (Kemppainen (6.18), p. 112). There is a
deterministic `δ > 0` such that a.s., for every `N`, `‖(f̂_t)'(iy)‖ ≤ C y^{δ−1}` on
`[0,N] × (0,1]`. Mirror of QuantumZipper's `ae_radial_bound` (`κ < 8`), with
`ae_grid_bound_of_eight_lt` at `θ = θ₁(κ)/2`. -/
theorem ae_radial_bound_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∃ δ > (0 : ℝ), ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) N,
      ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖deriv (fwdMapInv (drive κ B ω) t) ((y : ℂ) * Complex.I)‖ ≤ C * y ^ (δ - 1) := by
  obtain ⟨A, hA1, hA⟩ := tr2_interp
  have hθ₁ := rsTheta1_pos hκ
  have hθ₁1 := rsTheta1_lt_one hκ
  set θ := rsTheta1 κ / 2 with hθdef
  have hθ : 0 < θ := by positivity
  have hθlt : θ < rsTheta1 κ := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  set a := 1 / 2 - θ / (8 * A) with hadef
  have hA0 : 0 < A := by linarith
  have hq : θ / (8 * A) ≤ θ / 8 := div_le_div_of_nonneg_left hθ.le (by norm_num) (by linarith)
  have hq0 : 0 < θ / (8 * A) := by positivity
  have ha0 : 0 < a := by linarith
  have halt : a < 1 / 2 := by linarith
  refine ⟨θ / 2, by positivity, ?_⟩
  filter_upwards [ae_all_iff.2 fun N : ℕ => ae_grid_bound_of_eight_lt hB hκ hθlt N,
    bm_holder hB halt, hB.cont, hB.eval_zero_ae_eq_zero] with ω hgrid hhol hc h0
  intro N
  obtain ⟨Cg, hCg⟩ := hgrid N
  obtain ⟨Ch, hCh⟩ := hhol (N : ℝ≥0)
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  refine ⟨2 * A ^ 3 * max Cg 0 * (1 + (Real.sqrt κ * |Ch|) ^ 2) ^ A, by positivity,
    fun t ht y hy => ?_⟩
  have hgrid' : ∀ n k : ℕ, (k : ℝ) / 4 ^ n ≤ N →
      ‖deriv (fwdMapInv (drive κ B ω) ((k : ℝ) / 4 ^ n)) (Complex.I / 2 ^ n)‖ ≤
        max Cg 0 * 2 ^ ((n : ℝ) * (1 - θ)) := fun n k hk =>
    (hCg n k hk).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by norm_num) _))
  have h := hA (drive κ B ω) hW hW0 N θ a (max Cg 0) (Real.sqrt κ * |Ch|) hθ hθ1 ha0 halt.le
    (le_max_right _ _) (by positivity) hgrid' (drive_holder_of hCh) t ht y hy
  have hexp : θ - 1 - (2 - 4 * a) * A = θ / 2 - 1 := by
    rw [hadef]; field_simp; ring
  rwa [hexp] at h

/-- **Rohde–Schramm trace for κ > 8** (RS05 Thm 5.1 with Thm 3.6; Kemppainen Thm 5.2), in the
shape of QuantumZipper's `RS.ae_sleTrace_good` (κ < 8). -/
theorem ae_sleTrace_good_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∃ δ > (0 : ℝ), ∀ᵐ ω ∂P, QuantumZipper.sleTrace κ B ω 0 = 0 ∧
      ContinuousOn (QuantumZipper.sleTrace κ B ω) (Ici 0) ∧
      ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖QuantumZipper.fwdMapInv (QuantumZipper.drive κ B ω) t (y * I) -
          QuantumZipper.sleTrace κ B ω t‖ ≤ C * y ^ δ := by
  obtain ⟨δ, hδ, h⟩ := ae_radial_bound_of_eight_lt hB hκ
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0
  set W := drive κ B ω with hWdef
  have hW : Continuous W := drive_continuous hc
  have hW0 : W 0 = 0 := drive_zero h0
  have key : ∀ N : ℕ,
      (∀ t ∈ Icc 0 (N : ℝ), Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (trace W t))) ∧
      (∀ t ∈ Icc 0 (N : ℝ), ∀ y ∈ Ioc (0 : ℝ) 1,
        ‖fwdMapInv W t (y * Complex.I) - trace W t‖ ≤ (Classical.choose (hω N)) / δ * y ^ δ) ∧
      ContinuousOn (trace W) (Icc 0 (N : ℝ)) := fun N =>
    trace_of_radialBound hδ (Classical.choose_spec (hω N)).1 hW hW0
      (Classical.choose_spec (hω N)).2
  refine ⟨?_, ?_, fun N => ⟨_, (key N).2.1⟩⟩
  · -- `η 0 = 0`: `f̂_0 = id` on `ℍ`
    have ht := (key 0).1 0 ⟨le_rfl, by simp⟩
    have hid : ∀ y : ℝ, 0 < y → fwdMapInv W 0 (y * Complex.I) = y * Complex.I := by
      intro y hy
      have hyH : (y : ℂ) * Complex.I ∈ H := mul_I_mem_H hy
      rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 le_rfl hyH]
      have hVc : Continuous fun r : ℝ => W (0 - r) - W 0 := by fun_prop
      obtain ⟨u, hu⟩ := exists_isReverseSol _ hVc _ hyH 0 le_rfl
      rw [revMap_eq _ hVc _ le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2]
      simp
    have ht2 : Tendsto (fun y : ℝ => fwdMapInv W 0 (y * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : ℝ) * Complex.I)) := by
      refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun y hy => (hid y hy).symm) ?_
      exact ((Complex.continuous_ofReal.mul continuous_const).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have := tendsto_nhds_unique ht ht2
    simpa [sleTrace, hWdef] using this
  · intro t ht
    have hlt : t < ((⌈t⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil t]
    have hc := (key (⌈t⌉₊ + 1)).2.2 t ⟨ht, hlt.le⟩
    refine hc.mono_of_mem_nhdsWithin ?_
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds hlt)

/-! ### A measurable continuous version -/

/-- Measurable continuous version for κ > 8 (mirror of `RS.exists_measurable_sleTrace`). -/
theorem exists_measurable_sleTrace_of_eight_lt (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 8 < κ) :
    ∃ η : Ω → ℝ → ℂ, Measurable (Function.uncurry η) ∧ Measurable η ∧
      (∀ ω, Continuous (η ω)) ∧ ∀ᵐ ω ∂P, EqOn (η ω) (QuantumZipper.sleTrace κ B ω) (Ici 0) := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hae⟩ : ∃ B'' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B'' t)) ∧
      (∀ ω, Continuous (B'' · ω)) ∧ (∀ ω, B'' 0 ω = 0) ∧ ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
    refine ⟨fun t ω => B' t ω - B' 0 ω, fun t => (hB'm t).sub (hB'm 0),
      fun ω => (hB'c ω).sub continuous_const, fun ω => sub_self _, ?_⟩
    filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω h h0 t
    simp [h, h0]
  have hB''br : IsBrownianReal B'' P :=
    ⟨hB.toIsPreBrownianReal.congr fun t => hae.mono fun ω h => (h t).symm, ae_of_all _ hB''c⟩
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good_of_eight_lt hB''br hκ
  obtain ⟨G, hGm, hG, hGae⟩ : ∃ G : Set Ω, MeasurableSet G ∧
      (∀ ω ∈ G, ContinuousOn (sleTrace κ B'' ω) (Ici 0) ∧
        ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
          ‖fwdMapInv (drive κ B'' ω) t (y * Complex.I) - sleTrace κ B'' ω t‖ ≤ C * y ^ δ) ∧
      ∀ᵐ ω ∂P, ω ∈ G := by
    obtain ⟨S, hS, hSm, hSp⟩ :=
      (hgood.mono fun ω h => And.intro h.2.1 h.2.2).exists_measurable_mem
    exact ⟨S, hSm, hSp, hS⟩
  -- the approximants and the limit, in the `(t, ω)` orientation
  obtain ⟨y, hy0, hyT⟩ : ∃ y : ℕ → ℝ, (∀ n, 0 < y n) ∧ Tendsto y atTop (𝓝[>] 0) :=
    ⟨fun n => 1 / ((n : ℝ) + 1), fun n => by positivity,
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩⟩
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → Ω → ℂ, ∀ n t, F n t = G.indicator
      (fun ω => fwdMapInv (drive κ B'' ω) (max t 0) ((y n : ℂ) * Complex.I)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → Ω → ℂ, ∀ t, g t =
      G.indicator (fun ω => sleTrace κ B'' ω (max t 0)) := ⟨_, fun _ => rfl⟩
  have hFm : ∀ n, Measurable (Function.uncurry (F n)) := by
    intro n
    refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun t => ?_)
    · by_cases hω : ω ∈ G
      · simp only [hF, indicator_of_mem hω]
        refine continuous_comp_max_zero (f := fun t => fwdMapInv (drive κ B'' ω) t _)
          (continuousOn_Ici_of_Icc fun N hN => ?_)
        exact continuousOn_fwdMapInv_mul_I (drive_continuous (hB''c ω))
          (by simp [drive, hB''0]) (hy0 n) hN
      · simp only [hF, indicator_of_notMem hω]
        exact continuous_const
    · rw [hF]
      exact (measurable_fwdMapInv_drive hB''m hB''c hB''0 κ (le_max_right t 0)
        (by simpa using hy0 n)).indicator hGm
  have hlim : Tendsto (fun n => Function.uncurry (F n)) atTop (𝓝 (Function.uncurry g)) := by
    rw [tendsto_pi_nhds]
    rintro ⟨t, ω⟩
    by_cases hω : ω ∈ G
    · simp only [Function.uncurry_apply_pair, hF, hg, indicator_of_mem hω]
      obtain ⟨C, hC⟩ := (hG ω hω).2 ⌈max t 0⌉₊
      have hmem : max t 0 ∈ Icc (0 : ℝ) ⌈max t 0⌉₊ := ⟨le_max_right _ _, Nat.le_ceil _⟩
      exact (tendsto_fwdMapInv_of_rpow_bound hδ (hC _ hmem)).comp hyT
    · simp only [Function.uncurry_apply_pair, hF, hg, indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hgm : Measurable (Function.uncurry g) := measurable_of_tendsto_metrizable hFm hlim
  refine ⟨fun ω t => g t ω, hgm.comp measurable_swap, ?_, fun ω => ?_, ?_⟩
  · exact measurable_pi_iff.2 fun t => hgm.comp (measurable_const.prodMk measurable_id)
  · by_cases hω : ω ∈ G
    · simp only [hg, indicator_of_mem hω]
      exact continuous_comp_max_zero (hG ω hω).1
    · simp only [hg, indicator_of_notMem hω]
      exact continuous_const
  · filter_upwards [hGae, hae] with ω hω h t ht
    have hdr : drive κ B'' ω = drive κ B ω := by funext s; simp [drive, h]
    simp only [hg, indicator_of_mem hω, max_eq_left (show (0 : ℝ) ≤ t from ht)]
    simp only [sleTrace, hdr]

end SLE

/-! ### Generation of the hulls -/

/-- Generation for κ > 8 in QuantumZipper's Blueprint form: almost surely the trace exists, is
continuous, and `ℍ \ K_t` is the component of `ℍ \ η[0,t]` containing `M i` for every `M`
bounding `‖η‖` on `[0,t]` (RS Thm 5.1, p. 20; Kemppainen Thm 5.2, Def. 5.3, p. 76). Mirror of
QuantumZipper's `rohdeSchrammTraceGen_of_lt_eight`, using the deterministic generation step
`compl_fwdHull_eq_connectedComponentIn_of_norm_lt`. -/
theorem rohdeSchrammTraceGen_of_eight_lt {κ : ℝ} (hκ : 8 < κ) :
    QuantumZipper.Blueprint.RohdeSchrammTraceGen κ := by
  intro Ω _ P _ B hB
  obtain ⟨δ, hδ, h⟩ := ae_sleTrace_good_of_eight_lt hB hκ
  filter_upwards [h, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0
  obtain ⟨h0', hcont, hbd⟩ := hω
  refine ⟨h0', hcont, fun t ht M hM => ?_⟩
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  obtain ⟨C, hC⟩ := hbd ⌈t⌉₊
  have hunif := tendstoUniformlyOn_fwdMapInv_mul_I_of_bound (W := drive κ B ω) (t := t) hδ
    (C := C) fun s hs y hy => hC s ⟨hs.1, hs.2.trans (Nat.le_ceil t)⟩ y hy
  exact compl_fwdHull_eq_connectedComponentIn_of_norm_lt hW hW0 ht hunif
    (hcont.mono Icc_subset_Ici_self) hM

end InteractingSLE
