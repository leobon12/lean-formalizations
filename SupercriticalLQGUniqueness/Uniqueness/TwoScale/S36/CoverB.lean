import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Cover




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 
def relRad (b : Ioi (0 : ℝ)) (k : ℕ) : Ioi (0 : ℝ) :=
  ⟨(8 : ℝ) ^ (-(k : ℤ)) * b, mem_Ioi.mpr (mul_pos (zpow_pos (by norm_num) _) b.2)⟩

theorem relRad_val (b : Ioi (0 : ℝ)) (k : ℕ) :
    (relRad b k : ℝ) = (8 : ℝ) ^ (-(k : ℤ)) * b := rfl

 

theorem site_iterationB :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∀ (cMinus cPlus : ℝ≥0∞), 0 < cMinus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
          (C θ : Ioi (0 : ℝ)) (w : ℂ) (b : Ioi (0 : ℝ)) (R : Finset ℕ),
        R.Nonempty → (∀ k ∈ R, 1 ≤ k) →
        (∀ k ∈ R, ENNReal.ofReal p ≤ P {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q w
          (relRad b k) q a K C θ cMinus.toReal cPlus.toReal}) →
        P {ω | ∀ k ∈ R, h ω ∉ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q w
          (relRad b k) q a K C θ cMinus.toReal cPlus.toReal} ≤
          ENNReal.ofReal (c * Real.exp (-iterRate * R.card)) := by
  have hrate : 0 < iterRate := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ := Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open
    (1 / 7) (3 / 4) (by norm_num) (by norm_num) (by norm_num) iterRate hrate (1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM q a K C θ w b R hRne hR1
    hprob
  set N := R.card with hNdef
  have hN : 1 ≤ N := Finset.card_pos.mpr hRne
  have hb : 0 < (b : ℝ) := b.2
  let js : ℕ → ℕ := extEnum R
  have hjs : StrictMono js := extEnum_strictMono R hR1
  let Att : ℕ → Set Ω := fun k => {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q w
    (relRad b k) q a K C θ cMinus.toReal cPlus.toReal}
  let rad : ℕ → ℝ := fun k => 3 * (relRad b (js k) : ℝ)
  have hrad : ∀ k, rad k = 3 * ((8 : ℝ) ^ (-(js k : ℤ)) * b) := fun k => rfl
  have hradpos : ∀ k, 0 < rad k := fun k => by
    rw [hrad]
    positivity
  have hanti : Antitone rad := by
    intro k k' hkk'
    rw [hrad, hrad]
    have hle : js k ≤ js k' := hjs.monotone hkk'
    have : (8 : ℝ) ^ (-(js k' : ℤ)) ≤ (8 : ℝ) ^ (-(js k : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have := mul_le_mul_of_nonneg_right this hb.le
    linarith
  have hratio : ∀ k, rad (k + 1) / rad k ≤ 1 / 7 := by
    intro k
    rw [div_le_iff₀ (hradpos k), hrad, hrad]
    have hlt : js k + 1 ≤ js (k + 1) := hjs (Nat.lt_succ_self k)
    have h8 : (8 : ℝ) ^ (-(js (k + 1) : ℤ)) ≤ (8 : ℝ) ^ (-((js k : ℤ) + 1)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hsplit : (8 : ℝ) ^ (-((js k : ℤ) + 1)) = (8 : ℝ) ^ (-(js k : ℤ)) / 8 := by
      rw [neg_add, zpow_add₀ (by norm_num : (8 : ℝ) ≠ 0), zpow_neg_one]
      ring
    have hpos : 0 < (8 : ℝ) ^ (-(js k : ℤ)) := by positivity
    rw [hsplit] at h8
    have h8b := mul_le_mul_of_nonneg_right h8 hb.le
    have hpb : 0 < (8 : ℝ) ^ (-(js k : ℤ)) * b := mul_pos hpos hb
    have : (8 : ℝ) ^ (-(js k : ℤ)) / 8 * b = (8 : ℝ) ^ (-(js k : ℤ)) * b / 8 := by ring
    rw [this] at h8b
    linarith
  let E : ℕ → Set Ω := fun k => if 1 ≤ k ∧ k ≤ N then Att (js k) else univ
  have hEloc : ∀ k, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (rad k) w))
        (LQGMetric.Blueprint.annulus w ((1 / 7 : ℝ) * rad k) ((3 / 4 : ℝ) * rad k))) (E k) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · have hEk : E k = Att (js k) := ite_eq_left hk
      rw [hEk]
      exact attained_centered_local P h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM w
        (relRad b (js k)) q a K C θ _
        (eventCarrier_subset_iterAnnulus w (relRad b (js k))) (rad k)
    · have hEk : E k = univ := ite_eq_right hk
      rw [hEk]
      exact ⟨univ, MeasurableSet.univ, ae_eq_refl _⟩
  have hEprob : ∀ k, ENNReal.ofReal p ≤ P (E k) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · have hEk : E k = Att (js k) := ite_eq_left hk
      rw [hEk]
      exact hprob (js k) (extEnum_mem R hk.1 hk.2)
    · have hEk : E k = univ := ite_eq_right hk
      rw [hEk, measure_univ]
      exact ENNReal.ofReal_le_one.mpr hp1.le
  have hiter := hmain P h hh.1 w rad E hradpos hanti hratio hEloc hEprob N
  refine (measure_mono ?_).trans hiter
  intro ω hω
  have hzero : LQGMetric.Blueprint.countOcc E N ω = 0 := by
    classical
    unfold LQGMetric.Blueprint.countOcc
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk hkE
    have hk' : 1 ≤ k ∧ k ≤ N := Finset.mem_Icc.mp hk
    have hEk : E k = Att (js k) := ite_eq_left hk'
    rw [hEk] at hkE
    exact hω (js k) (extEnum_mem R hk'.1 hk'.2) hkE
  change (LQGMetric.Blueprint.countOcc E N ω : ℝ) < 1 / 2 * N
  rw [hzero, Nat.cast_zero]
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

 

theorem exp_rate_le_eps {ε : ℝ} (hε0 : 0 < ε) (N : ℕ)
    (hN : Real.log ε⁻¹ / Real.log 8 ≤ 8 * N) :
    Real.exp (-iterRate * N) ≤ ε ^ 100 := by
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h1 : Real.log ε⁻¹ ≤ 8 * N * Real.log 8 := (div_le_iff₀ hlog8).mp hN
  rw [Real.log_inv] at h1
  rw [← Real.exp_log (pow_pos hε0 100), Real.log_pow]
  apply Real.exp_le_exp.mpr
  unfold iterRate
  push_cast
  nlinarith

 




theorem cover_probB :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∀ (cMinus cPlus : ℝ≥0∞), 0 < cMinus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
          (C θ : Ioi (0 : ℝ)) (B : ℝ), 0 ≤ B → ∀ (b : Ioi (0 : ℝ)) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∀ (R : Finset ℕ), R.Nonempty →
        (∀ k ∈ R, 1 ≤ k ∧ ε ^ 2 ≤ (8 : ℝ) ^ (-(k : ℤ)) ∧ (8 : ℝ) ^ (-(k : ℤ)) ≤ ε) →
        Real.exp (-iterRate * R.card) ≤ ε ^ 100 →
        (∀ (w : ℂ), ∀ k ∈ R, ENNReal.ofReal p ≤ P {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q
          w (relRad b k) q a K C θ cMinus.toReal cPlus.toReal}) →
        ∃ S : Set Ω, MeasurableSet S ∧
          P Sᶜ ≤ ENNReal.ofReal (c * (200 * (B + 1) + 3) ^ 2 * ε ^ 96) ∧
          ∀ ω ∈ S, ∀ x ∈ Metric.closedBall (0 : ℂ) (B * b), ∃ (c' : ℂ) (r : ℝ),
            (∃ (hr : 0 < r) (hCircle : ℝ), TwoScale.S36Events.Attained (D (h ω)) (D' (h ω)) (ξ : ℝ) Q c'
              ⟨r, hr⟩ q a K C θ cMinus.toReal cPlus.toReal hCircle) ∧
            ε ^ 2 * b ≤ r ∧ r ≤ ε * b ∧ x ∈ Metric.ball c' (r / 2) := by
  obtain ⟨p, c, hp0, hp1, hc0, hsite⟩ := site_iterationB
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM q a K C θ B hB b ε hε0 hε1 R
    hRne hRk hrate hprob
  have hb : 0 < (b : ℝ) := b.2
  have hR1 : ∀ k ∈ R, 1 ≤ k := fun k hk => (hRk k hk).1
  set m : ℝ := ε ^ 2 * b / 100 with hmdef
  set box := LQGMetric.CONF.gridBox m (b * (B + 1)) 0 with hboxdef
  let site : ℤ × ℤ → ℂ := fun k => ⟨k.1 * m, k.2 * m⟩
  let Fail : ℤ × ℤ → Set Ω := fun k => {ω | ∀ j ∈ R, h ω ∉ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q
    (site k) (relRad b j) q a K C θ cMinus.toReal cPlus.toReal}
  have hFail : ∀ k, P (Fail k) ≤ ENNReal.ofReal (c * Real.exp (-iterRate * R.card)) := fun k =>
    hsite P h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM q a K C θ (site k) b R hRne hR1
      (hprob (site k))
  let S : Set Ω := ⋂ k ∈ box, (toMeasurable P (Fail k))ᶜ
  have hSm : MeasurableSet S :=
    Finset.measurableSet_biInter _ fun k _ => (measurableSet_toMeasurable P _).compl
  refine ⟨S, hSm, ?_, ?_⟩
  · have hSc : Sᶜ = ⋃ k ∈ box, toMeasurable P (Fail k) := by
      simp only [S, compl_iInter, compl_compl]
    rw [hSc]
    have hbudget := TwoScale.Stopping.fine_mesh_union_budget hε0 hε1 hb hB hc0.le 0
      (fun _ => c * Real.exp (-iterRate * R.card))
      (fun k _ => mul_le_mul_of_nonneg_left hrate hc0.le)
    calc P (⋃ k ∈ box, toMeasurable P (Fail k))
        ≤ ∑ k ∈ box, P (toMeasurable P (Fail k)) := measure_biUnion_finset_le _ _
      _ = ∑ k ∈ box, P (Fail k) := by simp only [measure_toMeasurable]
      _ ≤ ∑ k ∈ box, ENNReal.ofReal (c * Real.exp (-iterRate * R.card)) :=
          Finset.sum_le_sum fun k _ => hFail k
      _ = ENNReal.ofReal (∑ k ∈ box, c * Real.exp (-iterRate * R.card)) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
      _ ≤ ENNReal.ofReal (c * (200 * (B + 1) + 3) ^ 2 * ε ^ 96) :=
          ENNReal.ofReal_le_ofReal hbudget
  · intro ω hω x hx
    have hxU : x ∈ (fun u : ℂ => ((b : ℝ) : ℂ) * u) '' Metric.closedBall (0 : ℂ) B := by
      refine ⟨x / ((b : ℝ) : ℂ), ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hb.le,
          div_le_iff₀ hb]
        exact mem_closedBall_zero_iff.mp hx
      · change ((b : ℝ) : ℂ) * (x / ((b : ℝ) : ℂ)) = x
        have hbC : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
        field_simp
    obtain ⟨k, hk, hkx⟩ := TwoScale.Stopping.fine_mesh_site_in_box (U := Metric.closedBall (0 : ℂ) B)
      (B := B) subset_rfl hε0 hε1 hb hxU
    have hωk : ω ∉ Fail k := fun hF =>
      (mem_iInter₂.mp hω k hk) (subset_toMeasurable P _ hF)
    have hωk' : ∃ j ∈ R, h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q (site k)
        (relRad b j) q a K C θ cMinus.toReal cPlus.toReal := by
      by_contra hno
      push Not at hno
      exact hωk hno
    obtain ⟨j, hjR, hjE⟩ := hωk'
    obtain ⟨hCircle, -, hAtt⟩ := hjE
    obtain ⟨-, hj2, hj1⟩ := hRk j hjR
    have hlow : ε ^ 2 * b ≤ (relRad b j : ℝ) := by
      rw [relRad_val]
      exact mul_le_mul_of_nonneg_right hj2 hb.le
    have hhigh : (relRad b j : ℝ) ≤ ε * b := by
      rw [relRad_val]
      exact mul_le_mul_of_nonneg_right hj1 hb.le
    refine ⟨site k, (relRad b j : ℝ), ⟨(relRad b j).2, hCircle, hAtt⟩, hlow, hhigh, ?_⟩
    have hhalf := TwoScale.Stopping.fine_mesh_half_radius hε0 hb hlow x
    rw [Metric.mem_ball]
    have hsite : site k = LQGMetric.CONF.conf36Grid (ε ^ 2 * b / 100) x := hkx
    rw [hsite]
    exact hhalf

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
