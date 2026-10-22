import HigherDimLQGMetric.DGZ.TightBasics
import HigherDimLQGMetric.DGZ.LengthIn
import HigherDimLQGMetric.DGZ.FieldTails

/-!
# DGZ Lemma 6.7: deterministic and Gaussian tools (packet L5a)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 6.7 (TeX l. 3054–3106, p. 60);
blueprint Part C, Lemma `r2:lem:67` (Steps 2 and 3).

* `acrossDist_ge_sum_shells` (blueprint Step 3, "a crossing of `B_R \ B_r` contains disjoint
  sub-crossings of every shell in between"): for nested disjoint shells
  `B_{ρ'_i}(0) \ B_{ρ_i}(0)` between radii `r` and `R`,
  `Σ_i D(across B_{ρ'_i}(0) \ B_{ρ_i}(0)) ≤ D(across B_R(0) \ B_r(0))`.
* `exists_sup_tail_growing` (blueprint Step 2, "covering `B̄_{2^{k+1}}(0)` by `(2^{k+2}+1)^d` unit
  boxes"): for every version `G` of `H_{1,b}`, `b ∈ [1, 2]`, and every integer `M ≥ 0`,
  `P[sup_{B̄_M(0)} |G| > C₀ + u] ≤ (2M + 1)^d · 2 exp(-u²/(2 log 2))`, uniformly in `b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (latPt cbox obox)

variable {d : ℕ}

/-! ### Superadditivity of crossing distances over nested shells -/

/-- **Nested shells** (blueprint `r2:lem:67`, Step 3): if the shells
`B̄_{ρ'_i}(0) \ B_{ρ_i}(0)` (`i < J`) lie between the radii `r` and `R` and are nested and disjoint
(`ρ'_i ≤ ρ_j` for `i < j`), then
`Σ_{i<J} D(across B_{ρ'_i}(0) \ B_{ρ_i}(0)) ≤ D(across B_R(0) \ B_r(0))` for every continuous
field. -/
theorem acrossDist_ge_sum_shells (hd0 : 0 < d) {ξ : ℝ} {φ : Rd d → ℝ} (hφ : Continuous φ)
    {r R : ℝ} (hr : 0 ≤ r) (J : ℕ) (ρ ρ' : ℕ → ℝ) (hρ : ∀ i < J, ρ i < ρ' i)
    (hrρ : ∀ i < J, r ≤ ρ i) (hρR : ∀ i < J, ρ' i ≤ R)
    (hnest : ∀ i j, i < j → j < J → ρ' i ≤ ρ j) :
    ∑ i ∈ Finset.range J, acrossDist ξ φ 0 (ρ' i) (ρ i) ≤ acrossDist ξ φ 0 R r := by
  rcases Nat.eq_zero_or_pos J with rfl | hJ
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact acrossDist_nonneg ξ φ 0 R r
  have hR : 0 ≤ R := hr.trans ((hrρ 0 hJ).trans ((hρ 0 hJ).le.trans (hρR 0 hJ)))
  show _ ≤ lfppSetDist ξ φ univ (lsph 0 r) (lsph 0 R)
  refine le_lfppSetDist (lsph_nonempty hd0 0 hr) (lsph_nonempty hd0 0 hR) fun x hx y hy => ?_
  refine HigherDimLFPP.le_lfppDistOn (pcwJoined_univ x y) fun γ hγ _ => ?_
  have hcross : ∀ i, i < J → ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ 1 ∧
      acrossDist ξ φ 0 (ρ' i) (ρ i) ≤ ∫ τ in s..t, lfppIntegrand ξ φ γ τ ∧
      ∀ τ ∈ Ioo s t, γ τ ∈ obox (0 : Rd d) (ρ' i) \ cbox (0 : Rd d) (ρ i) := by
    intro i hi
    obtain ⟨t₀, t₁, h0, h01, h1, hγ0, hγ1, -, hin⟩ :=
      (isShellPair_box (0 : Rd d) (hρ i hi)).exists_crossing_of_le zero_le_one hγ.continuousOn
        (by rw [hγ.source]; exact cbox_mono (hrρ i hi) hx.1)
        (by rw [hγ.target]; intro hyo; exact hy.2 (obox_mono (hρR i hi) hyo))
    exact ⟨t₀, t₁, h0, h01, h1,
      acrossDist_le_integral hφ (hρ i hi) hγ h0 h01.le h1 (Or.inl ⟨hγ0.1, hγ1.2⟩), hin⟩
  choose! s t hs0 hst ht1 hint hin using hcross
  have hdisj : Set.Pairwise (↑(Finset.range J) : Set ℕ)
      fun i j => Disjoint (Ioo (s i) (t i)) (Ioo (s j) (t j)) := by
    intro i hi j hj hij
    have hiJ : i < J := Finset.mem_range.1 hi
    have hjJ : j < J := Finset.mem_range.1 hj
    rw [Set.disjoint_left]
    intro τ hτi hτj
    have h1 := hin i hiJ τ hτi
    have h2 := hin j hjJ τ hτj
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact h2.2 (HigherDimLFPP.DGZ.obox_subset_cbox _ _ (obox_mono (hnest i j hlt hjJ) h1.1))
    · exact h1.2 (HigherDimLFPP.DGZ.obox_subset_cbox _ _ (obox_mono (hnest j i hlt hiJ) h2.1))
  have hsum := sum_integral_le_lfppLengthIn (ξ := ξ) (S := univ) hφ hγ (Finset.range J) s t
    (fun i hi => ⟨hs0 i (Finset.mem_range.1 hi), (hst i (Finset.mem_range.1 hi)).le,
      ht1 i (Finset.mem_range.1 hi)⟩) (fun _ _ _ _ => mem_univ _) hdisj
  rw [lfppLengthIn_univ] at hsum
  exact (Finset.sum_le_sum fun i hi => hint i (Finset.mem_range.1 hi)).trans hsum

/-! ### Suprema of a unit-scale band on growing boxes -/

/-- The lattice points `latPt 1 g`, `g ∈ [-M, M]^d`, with boxes of radius `1` cover `B̄_M(0)`. -/
lemma td_cbox_subset_iUnion (M : ℕ) :
    cbox (0 : Rd d) M ⊆ ⋃ g ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) M),
      cbox (latPt 1 g) 1 := by
  intro z hz
  refine mem_iUnion₂.2 ⟨fun i => ⌊z i⌋, Fintype.mem_piFinset.2 fun i => ?_, fun i => ?_⟩
  · have h := hz i
    simp only [PiLp.zero_apply, sub_zero] at h
    rw [abs_le] at h
    rw [Finset.mem_Icc]
    constructor
    · have := Int.floor_mono h.1
      rwa [show (-(M : ℝ)) = ((-(M : ℤ) : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast] at this
    · have := Int.floor_mono h.2
      rwa [show ((M : ℝ)) = (((M : ℤ) : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast] at this
  · simp only [HigherDimLFPP.DGZ.latPt_apply, one_mul]
    rw [abs_of_nonneg (sub_nonneg.2 (Int.floor_le _))]
    have := Int.lt_floor_add_one (z i)
    linarith

/-- **Unit-scale bands on growing boxes** (blueprint `r2:lem:67`, Step 2): there is `C₀ ≥ 0` such
that for every version `G` of `H_{1,b}`, `b ∈ [1, 2]`, over any white noise, every integer `M ≥ 0`
and every `u ≥ 0`:
`P[∃ z ∈ B̄_M(0), |G z| > C₀ + u] ≤ (2M + 1)^d · 2 exp(-u²/(2 log 2))`. -/
theorem exists_sup_tail_growing {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {b : ℝ}, 1 ≤ b → b ≤ 2 → ∀ {G : Rd d → Ω → ℝ},
        IsBandVersion P W κ 1 b G → ∀ (M : ℕ) {u : ℝ}, 0 ≤ u →
          P {ω | ∃ z ∈ cbox (0 : Rd d) M, C₀ + u < |G z ω|} ≤
            ENNReal.ofReal ((2 * M + 1) ^ d * (2 * Real.exp (-u ^ 2 / (2 * Real.log 2)))) := by
  obtain ⟨C, hC0, hC⟩ := exists_sup_cbox_gaussian_tail hκ (R := 1) zero_le_one
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨Real.sqrt (2 * d) * Real.log 2 + C * Real.sqrt (Real.log 2) + C, by positivity,
    fun {Ω} _ {P} {W} hW {b} hb1 hb2 {G} hG M {u} hu => ?_⟩
  rcases eq_or_lt_of_le hb1 with hb | hb
  · -- `b = 1`: the version vanishes a.s.
    subst hb
    have h0 := ae_forall_eq_zero_of_isBandVersion_self hκ hW one_pos hG
    have hnull : P {ω | ∃ z ∈ cbox (0 : Rd d) M,
        Real.sqrt (2 * d) * Real.log 2 + C * Real.sqrt (Real.log 2) + C + u < |G z ω|} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h0)
      obtain ⟨z, -, hz⟩ := hω
      intro hall
      rw [hall z, abs_zero] at hz
      have : 0 ≤ Real.sqrt (2 * d) * Real.log 2 + C * Real.sqrt (Real.log 2) + C + u := by
        positivity
      linarith
    rw [hnull]
    exact zero_le
  · -- `1 < b ≤ 2`: a union bound over the unit boxes
    have hlb : 0 < Real.log b := Real.log_pos hb
    have hlb2 : Real.log b ≤ Real.log 2 := Real.log_le_log (by linarith) hb2
    set S := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) M) with hS
    have hcard : (S.card : ℝ) = (2 * M + 1) ^ d := by
      rw [hS, Fintype.card_piFinset_const, Int.card_Icc]
      push_cast
      rw [show ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 by omega]
      push_cast
      ring
    have hsub : {ω | ∃ z ∈ cbox (0 : Rd d) M,
        Real.sqrt (2 * d) * Real.log 2 + C * Real.sqrt (Real.log 2) + C + u < |G z ω|} ⊆
        ⋃ g ∈ S, {ω | ∃ z ∈ cbox (latPt 1 g) (1 * b),
          Real.sqrt (2 * d) * Real.log (b / 1) + C * Real.sqrt (Real.log (b / 1)) + C + u <
            |G z ω|} := by
      intro ω hω
      obtain ⟨z, hz, hlt⟩ := hω
      obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.1 (td_cbox_subset_iUnion M hz)
      refine mem_iUnion₂.2 ⟨g, hg, z, fun i => (hzg i).trans (by linarith), ?_⟩
      rw [div_one]
      have h1 : Real.sqrt (2 * d) * Real.log b ≤ Real.sqrt (2 * d) * Real.log 2 :=
        mul_le_mul_of_nonneg_left hlb2 (Real.sqrt_nonneg _)
      have h2 : C * Real.sqrt (Real.log b) ≤ C * Real.sqrt (Real.log 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlb2) hC0
      linarith
    have hone : ∀ g ∈ S, P {ω | ∃ z ∈ cbox (latPt 1 g) (1 * b),
        Real.sqrt (2 * d) * Real.log (b / 1) + C * Real.sqrt (Real.log (b / 1)) + C + u <
          |G z ω|} ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2))) := by
      intro g _
      refine (hC hW one_pos hb1 hG (latPt 1 g) hu).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_one]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)
    calc _ ≤ P (⋃ g ∈ S, {ω | ∃ z ∈ cbox (latPt 1 g) (1 * b),
          Real.sqrt (2 * d) * Real.log (b / 1) + C * Real.sqrt (Real.log (b / 1)) + C + u <
            |G z ω|}) := measure_mono hsub
      _ ≤ ∑ g ∈ S, P {ω | ∃ z ∈ cbox (latPt 1 g) (1 * b),
          Real.sqrt (2 * d) * Real.log (b / 1) + C * Real.sqrt (Real.log (b / 1)) + C + u <
            |G z ω|} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _g ∈ S, ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log 2))) :=
          Finset.sum_le_sum hone
      _ = ENNReal.ofReal ((2 * M + 1) ^ d * (2 * Real.exp (-u ^ 2 / (2 * Real.log 2)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← hcard, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]

end DGZ

end HigherDimLQGMetric
