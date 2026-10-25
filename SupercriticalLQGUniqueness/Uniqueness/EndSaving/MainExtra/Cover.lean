import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.OffCentre
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RepairedInterfaces.RepairedAssembly
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.TwoSet.MeshCount




 















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra

open LQGMetric (DistC IsWholePlaneGFF)
open LQGMetric.Blueprint (countOcc fieldSigmaClosed0)

 

theorem exists_decreasing_enum (F : Finset ℝ) (hpos : ∀ r ∈ F, 0 < r)
    (hsep : ∀ r ∈ F, ∀ s ∈ F, r < s → 8 * r ≤ s) (hn : 0 < F.card) :
    ∃ sel : ℕ → ℝ, (∀ k, 1 ≤ k → 0 < sel k) ∧ (∀ k, 1 ≤ k → sel (k + 1) ≤ sel k) ∧
      (∀ k, 1 ≤ k → sel (k + 1) / sel k ≤ 1 / 8) ∧
      (∀ k, 1 ≤ k → k ≤ F.card → sel k ∈ F) := by
  classical
  set n := F.card with hn_def
  set e := F.orderEmbOfFin hn_def.symm with he
  set f : ℕ → ℝ := fun i => if hi : i < n then e ⟨i, hi⟩ else 0 with hf
  have hf_mem : ∀ i, i < n → f i ∈ F := fun i hi => by
    simp only [hf, hi, dite_true]
    exact F.orderEmbOfFin_mem _ _
  have hf_lt : ∀ i j, i < j → j < n → f i < f j := by
    intro i j hij hj
    have hi : i < n := hij.trans hj
    simp only [hf, hi, hj, dite_true]
    exact e.strictMono (Fin.mk_lt_mk.mpr hij)
  have hf_pos : ∀ i, i < n → 0 < f i := fun i hi => hpos _ (hf_mem i hi)
  have hf_sep : ∀ i j, i < j → j < n → 8 * f i ≤ f j := fun i j hij hj =>
    hsep _ (hf_mem i (hij.trans hj)) _ (hf_mem j hj) (hf_lt i j hij hj)
  set sel : ℕ → ℝ := fun k => if k ≤ n then f (n - k) else f 0 * (8 : ℝ)⁻¹ ^ (k - n) with hsel
  have hf0 : 0 < f 0 := hf_pos 0 hn
  have hpos' : ∀ k, 1 ≤ k → 0 < sel k := by
    intro k hk
    by_cases hkn : k ≤ n
    · simp only [hsel, hkn, ite_true]
      exact hf_pos _ (by omega)
    · simp only [hsel, hkn, ite_false]
      positivity
  have hratio : ∀ k, 1 ≤ k → sel (k + 1) ≤ 1 / 8 * sel k := by
    intro k hk
    by_cases hkn : k + 1 ≤ n
    · have hk' : k ≤ n := by omega
      simp only [hsel, hkn, hk', ite_true]
      have := hf_sep (n - (k + 1)) (n - k) (by omega) (by omega)
      linarith
    · by_cases hkn' : k ≤ n
      · have hk_eq : k = n := by omega
        simp only [hsel, hkn, hkn', ite_true, ite_false]
        rw [show k + 1 - n = 1 by omega, show n - k = 0 by omega, pow_one]
        ring_nf
        exact le_rfl
      · simp only [hsel, hkn, hkn', ite_false]
        rw [show k + 1 - n = (k - n) + 1 by omega, pow_succ]
        ring_nf
        exact le_rfl
  refine ⟨sel, hpos', fun k hk => ?_, fun k hk => ?_, fun k hk hkn => ?_⟩
  · have h1 := hratio k hk
    have h2 := hpos' k hk
    linarith
  · rw [div_le_iff₀ (hpos' k hk)]
    linarith [hratio k hk]
  · simp only [hsel, hkn, ite_true]
    exact hf_mem _ (by omega)

 
theorem exp_count_le_pow_five {ε N : ℝ} (hε : 0 < ε)
    (hN : (5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8) ≤ N) :
    Real.exp (-(8 * Real.log 8) * N) ≤ ε ^ 5 := by
  have hl : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h1 : 5 * Real.log ε⁻¹ ≤ 8 * Real.log 8 * N := by
    have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 8 * Real.log 8)
    have e : 8 * Real.log 8 * ((5 / 8 : ℝ) * (Real.log ε⁻¹ / Real.log 8)) =
        5 * Real.log ε⁻¹ := by field_simp
    linarith
  have h2 : ε ^ 5 = Real.exp (-(5 * Real.log ε⁻¹)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hε, Real.log_inv]
    congr 1
    push_cast
    ring
  rw [h2]
  exact Real.exp_le_exp.2 (by linarith)

 


theorem perCentre_failure :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∃ c : ℝ, 1 ≤ c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (z : ℂ) (F : Finset ℝ) (wc : ℝ → ℂ) (Ev : ℝ → Set Ω),
        (∀ r ∈ F, 0 < r) → (∀ r ∈ F, ∀ s ∈ F, r < s → 8 * r ≤ s) →
        (∀ r ∈ F, dist (wc r) z ≤ r / 50) →
        (∀ r ∈ F, ∃ E₀ : Set Ω, MeasurableSet[fieldSigmaClosed0 h
          {x | r ≤ dist x (wc r) ∧ dist x (wc r) ≤ 4 * r}] E₀ ∧ Ev r =ᵐ[P] E₀) →
        (∀ r ∈ F, ENNReal.ofReal p ≤ P (Ev r)) →
        P {ω | ∀ r ∈ F, ω ∉ Ev r} ≤
          ENNReal.ofReal (c * Real.exp (-(8 * Real.log 8) * F.card)) := by
  classical
  have ha : 0 < 8 * Real.log 8 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 8); positivity
  obtain ⟨p, c, hp0, hp1, hc, H⟩ := annulusOffcenterAt_part1 (1 / 250) (1 / 5) (4 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (8 * Real.log 8) ha
    (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, hp0, hp1, max c 1, le_max_right _ _, ?_⟩
  intro Ω _ P _ h hh z F wc Ev hpos hsep hwc hloc hprob
  rcases Nat.eq_zero_or_pos F.card with h0 | hn
  · rw [h0, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  obtain ⟨sel, hs0, hsA, hsr, hsF⟩ := exists_decreasing_enum F hpos hsep hn
  set n := F.card with hn_def
  set rr : ℕ → ℝ := fun k => 5 * sel k with hrr
  set zc : ℕ → ℂ := fun k => if k ≤ n then wc (sel k) else z with hzc
  set E : ℕ → Set Ω := fun k => if k ≤ n then Ev (sel k) else univ with hE
  have hkey := H P h hh z rr zc E
    (fun k hk => by simp only [hrr]; linarith [hs0 k hk])
    (fun k hk => by simp only [hrr]; linarith [hsA k hk])
    (fun k hk => by
      simp only [hrr]
      rw [mul_div_mul_left _ _ (by norm_num : (5 : ℝ) ≠ 0)]
      exact (hsr k hk).trans (by norm_num))
    (fun k hk => by
      by_cases hkn : k ≤ n
      · simp only [hzc, hkn, ite_true, hrr]
        have := hwc _ (hsF k hk hkn)
        linarith
      · simp only [hzc, hkn, ite_false, hrr, dist_self]
        linarith [hs0 k hk])
    (fun k hk => by
      by_cases hkn : k ≤ n
      · have hzck : zc k = wc (sel k) := by simp only [hzc, hkn, ite_true]
        have hEk : E k = Ev (sel k) := by simp only [hE, hkn, ite_true]
        have hrrk : rr k = 5 * sel k := rfl
        rw [hzck, hEk, hrrk]
        obtain ⟨E₀, hE₀, hae⟩ := hloc _ (hsF k hk hkn)
        refine ⟨E₀, ?_, hae⟩
        have e1 : 1 / 5 * (5 * sel k) = sel k := by ring
        have e2 : 4 / 5 * (5 * sel k) = 4 * sel k := by ring
        rw [e1, e2]
        exact hE₀
      · simp only [hE, hkn, ite_false]
        exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩)
    (fun k hk => by
      by_cases hkn : k ≤ n
      · simp only [hE, hkn, ite_true]
        exact hprob _ (hsF k hk hkn)
      · simp only [hE, hkn, ite_false, measure_univ]
        exact ENNReal.ofReal_le_one.2 hp1.le)
    n hn
  have hsub : {ω | ∀ r ∈ F, ω ∉ Ev r} ⊆ {ω | (countOcc E n ω : ℝ) < 1 / 2 * n} := by
    intro ω hω
    have h0 : countOcc E n ω = 0 := by
      unfold countOcc
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun k hk => ?_)
      obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
      simp only [hE, hkn, ite_true]
      exact hω _ (hsF k hk1 hkn)
    simp only [Set.mem_ofPred_eq, h0, Nat.cast_zero]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    linarith
  refine (measure_mono hsub).trans (hkey.trans (ENNReal.ofReal_le_ofReal ?_))
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

 
theorem gridPt_nearIdx (m : ℝ) (x : ℂ) :
    LQGMetric.GM.gridPt m (⌊x.re / m + 1 / 2⌋, ⌊x.im / m + 1 / 2⌋) = TwoScale.TwoSet.nearestGrid m x := by
  apply Complex.ext <;> simp [LQGMetric.GM.gridPt, TwoScale.TwoSet.nearestGrid] <;> ring

 



theorem r51b_cover :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsWholePlaneGFF h P →
        ∀ (R : EndSaving.Interfaces.AdmissibleRadii)
          (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set Ω),
        (∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii), ∃ E₀ : Set Ω,
          MeasurableSet[fieldSigmaClosed0 h
            {x : ℂ | (r : ℝ) ≤ dist x z ∧ dist x z ≤ 4 * (r : ℝ)}] E₀ ∧
          event z r hr =ᵐ[P] E₀) →
        (∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
          ENNReal.ofReal p ≤ P (event z r hr)) →
        ∀ (b ε : Set.Ioi (0 : ℝ)), (ε : ℝ) < 1 →
        ∀ F : Finset ℝ, (F : Set ℝ) = R.radii ∩ Set.Icc (ε ^ 2 * (b : ℝ)) (ε * (b : ℝ)) →
        (5 / 8 : ℝ) * (Real.log (ε : ℝ)⁻¹ / Real.log 8) ≤ F.card →
        P {ω | ¬ ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
            ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
              (ε : ℝ) ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
              LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈ Metric.ball z ((r : ℝ) / 25) ∧
              ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr} ≤
          ENNReal.ofReal (C * ε) := by
  classical
  obtain ⟨p, hp0, hp1, c, hc1, H⟩ := perCentre_failure
  refine ⟨p, hp0, hp1, 643 ^ 2 * c, by positivity, ?_⟩
  intro Ω _ P _ h hh R event hloc hprob b ε hε1 F hF hcard
  have hb : (0 : ℝ) < b := b.2
  have hε : (0 : ℝ) < ε := ε.2
  have hFmem : ∀ r ∈ F, r ∈ R.radii ∧ (ε : ℝ) ^ 2 * b ≤ r ∧ r ≤ ε * b := by
    intro r hr
    have : r ∈ (F : Set ℝ) := hr
    rw [hF] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  have hFpos : ∀ r ∈ F, 0 < r := fun r hr => (R.subset_unit (hFmem r hr).1).1
  have hFsep : ∀ r ∈ F, ∀ s ∈ F, r < s → 8 * r ≤ s := fun r hr s hs hrs =>
    R.separated (hFmem r hr).1 (hFmem s hs).1 hrs
  set m := TwoScale.TwoSet.meshStep ε (b / 10) with hm
  have hm_pos : 0 < m := TwoScale.TwoSet.meshStep_pos hε (by positivity)
  have hm_le : m ≤ (ε : ℝ) ^ 2 * b / 80 := by rw [hm, TwoScale.TwoSet.meshStep]; ring_nf; exact le_rfl
  set G := TwoScale.TwoSet.meshSites ε (b / 10) 40 with hG
  
  set wc : ℂ → ℝ → ℂ := fun z' r => TwoScale.TwoSet.nearestGrid (r / 100) z' with hwc
  set Ev : ℂ → ℝ → Set Ω := fun z' r =>
    if hr : r ∈ R.radii ∧ 0 < r then event (wc z' r) ⟨r, hr.2⟩ hr.1 else ∅ with hEv
  have hEvF : ∀ z', ∀ r (hr : r ∈ F), Ev z' r = event (wc z' r) ⟨r, hFpos r hr⟩ (hFmem r hr).1 := by
    intro z' r hr
    simp only [hEv]
    split_ifs with hc
    · rfl
    · exact absurd ⟨(hFmem r hr).1, hFpos r hr⟩ hc
  have hsite : ∀ z' ∈ G, P {ω | ∀ r ∈ F, ω ∉ Ev z' r} ≤
      ENNReal.ofReal (c * Real.exp (-(8 * Real.log 8) * F.card)) := by
    intro z' _
    refine H P h hh z' F (wc z') (Ev z') hFpos hFsep (fun r hr => ?_) (fun r hr => ?_)
      (fun r hr => ?_)
    · have := TwoScale.TwoSet.nearestGrid_norm_lt (show 0 < r / 100 by linarith [hFpos r hr]) z'
      rw [dist_eq_norm, norm_sub_rev]
      linarith [hFpos r hr]
    · rw [hEvF z' r hr]
      exact hloc (wc z' r) ⟨r, hFpos r hr⟩ (hFmem r hr).1
    · rw [hEvF z' r hr]
      exact hprob (wc z' r) ⟨r, hFpos r hr⟩ (hFmem r hr).1
  
  have hcover : {ω | ¬ ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
        (ε : ℝ) ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈ Metric.ball z ((r : ℝ) / 25) ∧
        ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr} ⊆
      ⋃ z' ∈ G, {ω | ∀ r ∈ F, ω ∉ Ev z' r} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_forall, not_not] at hnot
    apply hω
    intro z hz
    set z' := TwoScale.TwoSet.nearestGrid m z with hz'
    have hz'G : z' ∈ G := by
      refine TwoScale.TwoSet.nearestGrid_mem_meshSites hε (by positivity) z ?_
      have hz3 : ‖z‖ < 3 * b := by simpa [dist_zero_right] using hz
      have : m ≤ b / 80 := by
        have hε2 : (ε : ℝ) ^ 2 ≤ 1 := by nlinarith
        nlinarith
      linarith
    obtain ⟨r, hrF, hωr⟩ := hnot z' hz'G
    obtain ⟨hrR, hrlo, hrhi⟩ := hFmem r hrF
    have hr0 := hFpos r hrF
    rw [hEvF z' r hrF] at hωr
    refine ⟨⟨r, hr0⟩, hrR, (⌊z'.re / (r / 100) + 1 / 2⌋, ⌊z'.im / (r / 100) + 1 / 2⌋),
      hrlo, hrhi, ?_, ?_⟩
    · show LQGMetric.GM.gridPt (r / 100) _ ∈ Metric.ball z (r / 25)
      rw [gridPt_nearIdx, Metric.mem_ball]
      have h1 : dist (TwoScale.TwoSet.nearestGrid (r / 100) z') z' < r / 100 := by
        have := TwoScale.TwoSet.nearestGrid_norm_lt (show 0 < r / 100 by linarith) z'
        rw [dist_eq_norm, norm_sub_rev]
        exact this
      have h2 : dist z' z < m := by
        have := TwoScale.TwoSet.nearestGrid_norm_lt hm_pos z
        rw [dist_eq_norm, norm_sub_rev]
        exact this
      have h3 := dist_triangle (TwoScale.TwoSet.nearestGrid (r / 100) z') z' z
      have h4 : m ≤ r / 80 := by
        calc m ≤ (ε : ℝ) ^ 2 * b / 80 := hm_le
          _ ≤ r / 80 := by linarith
      linarith
    · show ω ∈ event (LQGMetric.GM.gridPt (r / 100) _) ⟨r, hr0⟩ hrR
      rw [gridPt_nearIdx]
      exact hωr
  have hG_card : (G.card : ℝ) ≤ (16 * 40 + 3) ^ 2 * ((ε : ℝ) ^ 4)⁻¹ :=
    TwoScale.TwoSet.meshSites_card_le_epsilon_inv_four hε hε1.le (by positivity) (by norm_num)
  have hexp := exp_count_le_pow_five hε hcard
  calc P {ω | ¬ ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
        ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
          (ε : ℝ) ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
          LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈ Metric.ball z ((r : ℝ) / 25) ∧
          ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr}
      ≤ P (⋃ z' ∈ G, {ω | ∀ r ∈ F, ω ∉ Ev z' r}) := measure_mono hcover
    _ ≤ ∑ z' ∈ G, P {ω | ∀ r ∈ F, ω ∉ Ev z' r} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _z' ∈ G, ENNReal.ofReal (c * Real.exp (-(8 * Real.log 8) * F.card)) :=
        Finset.sum_le_sum hsite
    _ = ENNReal.ofReal (G.card * (c * Real.exp (-(8 * Real.log 8) * F.card))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (643 ^ 2 * c * ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hc0 : 0 ≤ c := by linarith
        have hε4 : (0 : ℝ) < (ε : ℝ) ^ 4 := by positivity
        calc (G.card : ℝ) * (c * Real.exp (-(8 * Real.log 8) * F.card))
            ≤ ((16 * 40 + 3) ^ 2 * ((ε : ℝ) ^ 4)⁻¹) * (c * (ε : ℝ) ^ 5) := by
              gcongr
          _ = 643 ^ 2 * c * ε := by field_simp; ring

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra
