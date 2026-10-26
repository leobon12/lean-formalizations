import SupercriticalConformalCovariance.Cover.Local

/-!
# Good covers, part 2: display (10)

Source: the paper, l. 441–447 ("Choose p close enough to one to apply annular near-independence with
failure exponent greater than 10. At lattice centers of mesh ε²/100 in a neighborhood of K, test
geometrically separated radii in [ε², ε]. Lemma 5.1, annular near-independence, and a union bound imply
(10)"), and Lemma 2.1, l. 133–138.

* `centre_tail` (one lattice centre; annular near-independence): if every `F z (8^{-k} ε)` is a.s. an event
  of `localSigma h z r` (implied by `σ(h|_{cl A_{r/2,2r}(z)})` mod constants) with probability `≥ p`, then all of `k = 1, …, M` fail with
  probability `≤ c e^{-aM}`. From the sealed SLU iteration `annulus_iteration_ae_translated_open` (certified
  LM Lemma 3.1(1)) on the enlarged open annuli `A_{3r/7, 9r/4}(z)` of reference radius `3r`
  (`localSigma`; the corrected reference radius `3r`).
* `display10_uniform`: the union bound over the `O(ε^{-4})` lattice centres with uniform constants:
  `P[coverEvent F K ε fails] ≤ c (200R₀ + 5)² ε^q` for `K ⊆ B̄_{R₀}(0)` and `ε ≤ min(ρ, r₀)`, `ε < 1/8`.
  Per-centre failure exponent `4 + q` (the paper's "greater than 10" is `q > 6`).
* `display10`: (10) as printed, `P[coverEvent F K ε] → 1` as `ε ↓ 0`, with the polynomial rate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Cover

open LQGMetric LQGMetric.Blueprint

/-! ## 1. One centre -/

theorem scaleRad_succ (ε : ℝ) (k : ℕ) : scaleRad ε (k + 1) = 8⁻¹ * scaleRad ε k := by
  simp only [scaleRad, pow_succ]; ring

theorem scaleRad_antitone {ε : ℝ} (hε : 0 ≤ ε) : Antitone (scaleRad ε) := fun i j hij =>
  mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij) hε

/-- **one centre** (annular near-independence at the radii `8^{-k} ε`): the constants depend only on `a` -/
theorem centre_tail (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (F : ℂ → ℝ → Set Ω) (z : ℂ) (ε : ℝ), 0 < ε →
        (∀ k : ℕ, AEEventIn P (localSigma h z (scaleRad ε k)) (F z (scaleRad ε k))) →
        (∀ k : ℕ, ENNReal.ofReal p ≤ P (F z (scaleRad ε k))) →
        ∀ M : ℕ, 0 < M → P {ω | ∀ k ∈ Finset.Icc 1 M, ω ∉ F z (scaleRad ε k)} ≤
          ENNReal.ofReal (c * Real.exp (-a * M)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open
      (1 / 7) (3 / 4) (by norm_num) (by norm_num) (by norm_num) a ha (1 / 2) (by norm_num)
      (by norm_num)
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh F z ε hε hloc hp M hM
  set R : ℕ → ℝ := fun k => 3 * scaleRad ε k with hRdef
  have hR0 : ∀ k, 0 < R k := fun k => mul_pos (by norm_num) (scaleRad_pos hε k)
  have hanti : Antitone R := fun i j hij =>
    mul_le_mul_of_nonneg_left (scaleRad_antitone hε.le hij) (by norm_num)
  have hratio : ∀ k, R (k + 1) / R k ≤ 1 / 7 := by
    intro k
    rw [div_le_iff₀ (hR0 k)]
    have := scaleRad_pos hε k
    simp only [hRdef, scaleRad_succ]
    nlinarith
  have hE : ∀ k, AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (R k) z))
      (annulus z (1 / 7 * R k) (3 / 4 * R k))) (F z (scaleRad ε k)) := hloc
  have HB := hmain P h hh z R (fun k => F z (scaleRad ε k)) hR0 hanti hratio hE hp M
  calc P {ω | ∀ k ∈ Finset.Icc 1 M, ω ∉ F z (scaleRad ε k)}
        ≤ P {ω | (countOcc (fun k => F z (scaleRad ε k)) M ω : ℝ) < 1 / 2 * M} := by
        refine measure_mono fun ω hbad => ?_
        have h0 : countOcc (fun k => F z (scaleRad ε k)) M ω = 0 := by
          classical
          unfold countOcc
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro k hk hkF
          exact hbad k hk hkF
        show (countOcc (fun k => F z (scaleRad ε k)) M ω : ℝ) < 1 / 2 * M
        rw [h0]
        have : (0 : ℝ) < M := by exact_mod_cast hM
        push_cast; linarith
    _ ≤ ENNReal.ofReal (c * Real.exp (-a * M)) := HB

/-! ## 2. Arithmetic of the scales and of the union bound -/

/-- the scale `M` with `ε ≤ 8^{-M} < 8ε` -/
theorem exists_scale (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ M : ℕ, ε ≤ (8 : ℝ)⁻¹ ^ M ∧ (8 : ℝ)⁻¹ ^ M < 8 * ε := by
  classical
  have hex : ∃ n : ℕ, (8 : ℝ)⁻¹ ^ n < ε := exists_pow_lt_of_lt_one hε0 (by norm_num)
  set n₀ := Nat.find hex with hn₀
  have hn₀0 : n₀ ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hn₀, h0, pow_zero] at this
    linarith
  refine ⟨n₀ - 1, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
  have h1 := Nat.find_spec hex
  rw [← hn₀, show n₀ = (n₀ - 1) + 1 by omega, pow_succ] at h1
  linarith

/-- `e^{-(4+q) log 8 · M} ≤ 8⁴ 8^q ε⁴ ε^q` when `8^{-M} < 8ε` -/
theorem exp_neg_scale_le {q ε : ℝ} (hq : 0 < q) (hε0 : 0 < ε) {M : ℕ}
    (hM : (8 : ℝ)⁻¹ ^ M < 8 * ε) :
    Real.exp (-((4 + q) * Real.log 8) * M) ≤ (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ 4 * ε ^ q := by
  set x : ℝ := (8 : ℝ)⁻¹ ^ M with hx
  have hx0 : 0 < x := pow_pos (by norm_num) M
  have e1 : Real.exp (-((4 + q) * Real.log 8) * M) = x ^ (4 + q) := by
    rw [Real.rpow_def_of_pos hx0, hx, Real.log_pow, Real.log_inv]
    congr 1; ring
  have h4q : (0 : ℝ) ≤ 4 + q := by linarith
  rw [e1]
  calc x ^ (4 + q) ≤ ((8 : ℝ) * ε) ^ (4 + q) := Real.rpow_le_rpow hx0.le hM.le h4q
    _ = (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ 4 * ε ^ q := by
        rw [Real.rpow_add (by positivity), Real.mul_rpow (by norm_num) hε0.le,
          Real.mul_rpow (by norm_num) hε0.le, Real.rpow_ofNat, Real.rpow_ofNat]
        ring

/-- rounding to the grid `δℤ`: `|t − δ⌊t/δ⌉| ≤ δ/2`, and `|⌊t/δ⌉| ≤ M` if `|t|/δ + 1 ≤ M` -/
theorem round_grid {δ t : ℝ} (hδ : 0 < δ) {M : ℕ} (ht : |t| / δ + 1 ≤ M) :
    |t - δ * (round (t / δ) : ℝ)| ≤ δ / 2 ∧ round (t / δ) ∈ Finset.Icc (-(M : ℤ)) M := by
  have h1 := abs_sub_round (t / δ)
  have e : t - δ * (round (t / δ) : ℝ) = δ * (t / δ - round (t / δ)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [e, abs_mul, abs_of_pos hδ]
    nlinarith
  · have h2 : |t / δ| = |t| / δ := by rw [abs_div, abs_of_pos hδ]
    have h3 := abs_le.1 h1
    have h4 := abs_le.1 (le_of_eq h2 : |t / δ| ≤ |t| / δ)
    have hlo : ((-(M : ℤ) : ℤ) : ℝ) ≤ (round (t / δ) : ℝ) := by push_cast; linarith
    have hhi : (round (t / δ) : ℝ) ≤ ((M : ℤ) : ℝ) := by push_cast; linarith
    exact Finset.mem_Icc.2 ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- the count of the lattice box: `(2M + 1)² ε⁴ ≤ (200R₀ + 5)²` when `M ε²/100 ≤ R₀ + 2ε²/100` -/
theorem box_card_arith {ε R₀ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {M : ℕ}
    (hM : (M : ℝ) * (ε ^ 2 / 100) ≤ R₀ + 2 * (ε ^ 2 / 100)) :
    (2 * M + 1 : ℝ) ^ 2 * ε ^ 4 ≤ (200 * R₀ + 5) ^ 2 := by
  have hε2 : ε ^ 2 ≤ 1 := pow_le_one₀ hε0.le hε1.le
  have hb : (2 * M + 1 : ℝ) * ε ^ 2 ≤ 200 * R₀ + 5 := by
    have e : (2 * M + 1 : ℝ) * ε ^ 2 = 200 * ((M : ℝ) * (ε ^ 2 / 100)) + ε ^ 2 := by ring
    rw [e]; linarith only [hM, hε2]
  have hb0 : 0 ≤ (2 * M + 1 : ℝ) * ε ^ 2 := by positivity
  have e : (2 * M + 1 : ℝ) ^ 2 * ε ^ 4 = ((2 * M + 1 : ℝ) * ε ^ 2) ^ 2 := by ring
  rw [e]
  exact pow_le_pow_left₀ hb0 hb 2

/-! ## 3. Display (10) -/

/-- **display (10), quantitative and uniform**: `p ∈ (0,1)` and `c > 0` depend only on `q`. For every
whole-plane GFF `h`, every family `F` of events that are annulus-local with probability `≥ p` on
`cl B_ρ(K) × (0, r₀]`, and every `K ⊆ B̄_{R₀}(0)`, the good cover at scale `ε` fails with probability
at most `c (200R₀ + 5)² ε^q`, for every `ε ∈ (0, 1/8)` with `ε ≤ ρ` and `ε ≤ r₀`. -/
theorem display10_uniform (q : ℝ) (hq : 0 < q) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (F : ℂ → ℝ → Set Ω) (K : Set ℂ) (R₀ : ℝ), 0 ≤ R₀ →
        K ⊆ closedBall 0 R₀ → ∀ ρ r₀ : ℝ, IsAnnulusLocalOn P h F K ρ r₀ →
        IsProbLowerOn P F K ρ r₀ p → ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ε ≤ ρ → ε ≤ r₀ →
        P (coverEvent F K ε)ᶜ ≤ ENNReal.ofReal (c * (200 * R₀ + 5) ^ 2 * ε ^ q) := by
  have ha : 0 < (4 + q) * Real.log 8 := mul_pos (by linarith) (Real.log_pos (by norm_num))
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := centre_tail _ ha
  refine ⟨p, c * (8 : ℝ) ^ 4 * (8 : ℝ) ^ q, hp0, hp1, by positivity, ?_⟩
  intro Ω _ P _ h hh F K R₀ hR₀ hKR ρ r₀ hloc hprob ε hε0 hε8 hερ hεr
  have hε1 : ε < 1 := by linarith
  obtain ⟨M, hM1, hM2⟩ := exists_scale ε hε0 hε1
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0, pow_zero] at hM2; linarith
    · exact h0
  set δ : ℝ := ε ^ 2 / 100 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδε : δ ≤ ε := by
    have : ε ^ 2 ≤ ε := by rw [sq]; nlinarith
    rw [hδ]; linarith
  set Mb : ℕ := ⌈R₀ / δ⌉₊ + 1 with hMbdef
  have hMlt : (Mb : ℝ) < R₀ / δ + 2 := by
    rw [hMbdef]; push_cast
    linarith [Nat.ceil_lt_add_one (show 0 ≤ R₀ / δ by positivity)]
  have hMx : (Mb : ℝ) * δ ≤ R₀ + 2 * δ := by
    have := mul_le_mul_of_nonneg_right hMlt.le hδ0.le
    rwa [add_mul, div_mul_cancel₀ _ hδ0.ne'] at this
  set Box : Finset (ℤ × ℤ) := Finset.Icc (-(Mb : ℤ)) Mb ×ˢ Finset.Icc (-(Mb : ℤ)) Mb with hBox
  classical
  -- the failure event at the lattice point `δ m` (empty unless `δ m ∈ cl B_ε(K)`)
  set Fail : ℤ × ℤ → Set Ω := fun m => if meshPt ε m ∈ cthickening ε K then
    {ω | ∀ k ∈ Finset.Icc 1 M, ω ∉ F (meshPt ε m) (scaleRad ε k)} else ∅ with hFail
  have hsub : (coverEvent F K ε)ᶜ ⊆ ⋃ m ∈ Box, Fail m := by
    intro ω hω
    simp only [coverEvent, mem_compl_iff, mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨x, hx, hy⟩ := hω
    have hxn : ‖x‖ ≤ R₀ := by simpa using hKR hx
    have hbd : ∀ t : ℝ, |t| ≤ ‖x‖ → |t| / δ + 1 ≤ Mb := by
      intro t ht
      have : |t| / δ ≤ R₀ / δ := div_le_div_of_nonneg_right (ht.trans hxn) hδ0.le
      rw [hMbdef]; push_cast
      linarith [Nat.le_ceil (R₀ / δ)]
    obtain ⟨hre1, hre2⟩ := round_grid hδ0 (hbd _ (Complex.abs_re_le_norm x))
    obtain ⟨him1, him2⟩ := round_grid hδ0 (hbd _ (Complex.abs_im_le_norm x))
    set m : ℤ × ℤ := (round (x.re / δ), round (x.im / δ)) with hm
    have hdist : ‖x - meshPt ε m‖ ≤ δ := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have er : (x - meshPt ε m).re = x.re - δ * (round (x.re / δ) : ℝ) := by
        simp [meshPt, hm, hδ]
      have ei : (x - meshPt ε m).im = x.im - δ * (round (x.im / δ) : ℝ) := by
        simp [meshPt, hm, hδ]
      rw [er, ei]
      linarith
    have hcen : meshPt ε m ∈ cthickening ε K := by
      refine mem_cthickening_of_dist_le _ x ε K hx ?_
      rw [dist_comm, dist_eq_norm]; linarith
    refine mem_biUnion (x := m) (Finset.mem_coe.2 (Finset.mem_product.2 ⟨hre2, him2⟩)) ?_
    simp only [hFail, ite_eq_left hcen, mem_ofPred_eq]
    intro k hk hkF
    have hkM := Finset.mem_Icc.1 hk
    have hpow : (8 : ℝ)⁻¹ ^ M ≤ (8 : ℝ)⁻¹ ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) hkM.2
    have hεk : ε ≤ (8 : ℝ)⁻¹ ^ k := hM1.trans hpow
    have hzr : (meshPt ε m, scaleRad ε k) ∈ coverFamily K ε := ⟨m, k, hkM.1, hεk, hcen, rfl⟩
    have hr1 : ε ^ 2 ≤ scaleRad ε k := (coverFamily_radius hε0.le hzr).1
    have hxb : x ∈ ball (meshPt ε m) (scaleRad ε k / 2) := by
      rw [mem_ball, dist_eq_norm]
      have : δ < ε ^ 2 / 2 := by
        have := pow_pos hε0 2
        rw [hδ]; linarith
      linarith
    exact hy _ hzr hxb hkF
  have hFm : ∀ m ∈ Box, P (Fail m) ≤
      ENNReal.ofReal (c * ((8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ 4 * ε ^ q)) := by
    intro m _
    simp only [hFail]
    split_ifs with hm
    · have hmρ : meshPt ε m ∈ cthickening ρ K := cthickening_mono hερ K hm
      have hrad : ∀ k, scaleRad ε k ∈ Ioc (0 : ℝ) r₀ := fun k =>
        ⟨scaleRad_pos hε0 k, (scaleRad_le hε0.le k).trans hεr⟩
      refine (H P h hh F (meshPt ε m) ε hε0 (fun k => hloc _ hmρ _ (hrad k))
        (fun k => hprob _ hmρ _ (hrad k)) M hMpos).trans ?_
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (exp_neg_scale_le hq hε0 hM2) hc.le)
    · simp
  have hcard : (Box.card : ℝ) = (2 * Mb + 1 : ℝ) ^ 2 := by
    rw [hBox, Finset.card_product, Int.card_Icc]
    have : ((Mb : ℤ) + 1 - -(Mb : ℤ)).toNat = 2 * Mb + 1 := by omega
    rw [this]; push_cast; ring
  calc P (coverEvent F K ε)ᶜ ≤ P (⋃ m ∈ Box, Fail m) := measure_mono hsub
    _ ≤ ∑ m ∈ Box, P (Fail m) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Box, ENNReal.ofReal (c * ((8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ 4 * ε ^ q)) :=
        Finset.sum_le_sum hFm
    _ = ENNReal.ofReal ((Box.card : ℝ) *
          (c * ((8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ 4 * ε ^ q))) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (p := (Box.card : ℝ)) (by positivity), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (c * (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * (200 * R₀ + 5) ^ 2 * ε ^ q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hcard]
        have hbox := box_card_arith hε0 hε1 hMx
        have hk : 0 ≤ c * (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ q := by positivity
        calc (2 * Mb + 1 : ℝ) ^ 2 * (c * ((8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ 4 * ε ^ q))
            = c * (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ q * ((2 * Mb + 1 : ℝ) ^ 2 * ε ^ 4) := by ring
          _ ≤ c * (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * ε ^ q * (200 * R₀ + 5) ^ 2 :=
              mul_le_mul_of_nonneg_left hbox hk
          _ = c * (8 : ℝ) ^ 4 * (8 : ℝ) ^ q * (200 * R₀ + 5) ^ 2 * ε ^ q := by ring

/-- for any set `A`, `1 − P[Aᶜ] ≤ P[A]` (outer measure; no measurability needed) -/
theorem one_sub_measure_compl_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) : 1 - P Aᶜ ≤ P A := by
  have h1 : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    calc (1 : ℝ≥0∞) = P univ := measure_univ.symm
      _ = P (A ∪ Aᶜ) := by rw [union_compl_self]
      _ ≤ P A + P Aᶜ := measure_union_le _ _
  exact tsub_le_iff_right.2 h1

/-- **display (10)** (l. 441–447): for `p` close enough to one (depending only on the rate `q`), if the
events are annulus-local with probability `≥ p` on a neighbourhood `cl B_ρ(K) × (0, r₀]` of the bounded
set `K`, then `P[∀x ∈ K ∃(z, r) ∈ coverFamily K ε : x ∈ B_{r/2}(z), F_{z,r}] → 1` as `ε ↓ 0`, at the rate
`1 − C ε^q`. -/
theorem display10 (q : ℝ) (hq : 0 < q) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (F : ℂ → ℝ → Set Ω) (K : Set ℂ), Bornology.IsBounded K →
        ∀ ρ r₀ : ℝ, 0 < ρ → 0 < r₀ → IsAnnulusLocalOn P h F K ρ r₀ →
        IsProbLowerOn P F K ρ r₀ p →
        (∃ C ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
          P (coverEvent F K ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ q)) ∧
        Tendsto (fun ε => P (coverEvent F K ε)) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨p, c, hp0, hp1, -, H⟩ := display10_uniform q hq
  refine ⟨p, hp0, hp1, ?_⟩
  intro Ω _ P _ h hh F K hK ρ r₀ hρ hr₀ hloc hprob
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  set R₀ : ℝ := max R 0
  have hKR : K ⊆ closedBall 0 R₀ := fun x hx =>
    mem_closedBall_zero_iff.2 ((hR x hx).trans (le_max_left _ _))
  set ε₁ : ℝ := min (min ρ r₀) (1 / 8)
  have hε₁ : 0 < ε₁ := lt_min (lt_min hρ hr₀) (by norm_num)
  set C : ℝ := c * (200 * R₀ + 5) ^ 2
  have hbound : ∀ ε ∈ Ioo (0 : ℝ) ε₁, P (coverEvent F K ε)ᶜ ≤ ENNReal.ofReal (C * ε ^ q) := by
    rintro ε ⟨hε0, hε⟩
    have h1 : ε < min ρ r₀ := hε.trans_le (min_le_left _ _)
    exact H P h hh F K R₀ (le_max_right _ _) hKR ρ r₀ hloc hprob ε hε0
      (hε.trans_le (min_le_right _ _)) (h1.le.trans (min_le_left _ _))
      (h1.le.trans (min_le_right _ _))
  refine ⟨⟨C, ε₁, hε₁, hbound⟩, ?_⟩
  -- the rate `ofReal (C ε^q) → 0`
  have hrate : Tendsto (fun ε : ℝ => ENNReal.ofReal (C * ε ^ q)) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => C * ε ^ q) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 q (Or.inr hq.le))
    have h0 : C * (0 : ℝ) ^ q = 0 := by rw [Real.zero_rpow hq.ne', mul_zero]
    have := (ENNReal.tendsto_ofReal (hc.tendsto)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0, ENNReal.ofReal_zero] at this
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) ε₁ := Ioo_mem_nhdsGT hε₁
  have hcompl : Tendsto (fun ε => P (coverEvent F K ε)ᶜ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
      (Eventually.of_forall fun _ => zero_le) (hev.mono fun ε hε => hbound ε hε)
  have hlow : Tendsto (fun ε => 1 - P (coverEvent F K ε)ᶜ) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hcompl
      (Or.inl ENNReal.one_ne_top)
    rwa [tsub_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun ε => one_sub_measure_compl_le P _) (fun ε => prob_le_one)

end SupercriticalConformalCovariance.Cover
