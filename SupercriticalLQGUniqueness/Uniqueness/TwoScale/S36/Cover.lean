import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.E1Clause
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.S35Deterministic
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces




 















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 

def extEnum (R : Finset ℕ) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ R.card then R.orderEmbOfFin rfl ⟨i - 1, by omega⟩
  else if i = 0 then 0 else R.sup id + i

theorem extEnum_mem (R : Finset ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ R.card) :
    extEnum R i ∈ R := by
  unfold extEnum
  rw [dite_eq_left ⟨h1, h2⟩]
  exact Finset.orderEmbOfFin_mem R rfl _

theorem extEnum_strictMono (R : Finset ℕ) (hR1 : ∀ j ∈ R, 1 ≤ j) :
    StrictMono (extEnum R) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hle : ∀ (k : Fin R.card), R.orderEmbOfFin rfl k ≤ R.sup id := fun k =>
    Finset.le_sup (f := id) (Finset.orderEmbOfFin_mem R rfl k)
  by_cases hi0 : i = 0
  · subst hi0
    have h0 : extEnum R 0 = 0 := by
      unfold extEnum
      rw [dite_eq_right (by omega), ite_eq_left rfl]
    rw [h0]
    by_cases h1 : 1 ≤ R.card
    · have hmem := extEnum_mem R le_rfl h1
      exact hR1 _ hmem
    · unfold extEnum
      rw [dite_eq_right (by omega), ite_eq_right (by omega)]
      omega
  · by_cases hin : i ≤ R.card
    · by_cases hin' : i + 1 ≤ R.card
      · unfold extEnum
        rw [dite_eq_left ⟨by omega, hin⟩, dite_eq_left ⟨by omega, hin'⟩]
        apply (R.orderEmbOfFin rfl).strictMono
        change i - 1 < i + 1 - 1
        omega
      · unfold extEnum
        rw [dite_eq_left ⟨by omega, hin⟩, dite_eq_right (by omega), ite_eq_right (by omega)]
        have := hle ⟨i - 1, by omega⟩
        omega
    · unfold extEnum
      rw [dite_eq_right (by omega), ite_eq_right hi0, dite_eq_right (by omega), ite_eq_right (by omega)]
      omega

 

 
def iterRate : ℝ := 800 * Real.log 8

theorem eventCarrier_subset_iterAnnulus (w : ℂ) (r : Ioi (0 : ℝ)) :
    TwoScale.S36Events.eventCarrier w r ⊆
      (LQGMetric.Blueprint.annulus w ((1 / 7 : ℝ) * (3 * (r : ℝ))) ((3 / 4 : ℝ) * (3 * (r : ℝ))) :
        Set ℂ) := by
  intro x hx
  have hr : 0 < (r : ℝ) := r.2
  have h1 : dist x w ≤ 2 * r := Metric.mem_closedBall.mp hx.1
  have h2 : r / 2 ≤ dist x w := not_lt.mp fun h => hx.2 (Metric.mem_ball.mpr h)
  change (1 / 7 : ℝ) * (3 * (r : ℝ)) < ‖x - w‖ ∧ ‖x - w‖ < (3 / 4 : ℝ) * (3 * (r : ℝ))
  rw [← dist_eq_norm]
  constructor <;> linarith

 



theorem site_iteration :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∀ (cMinus cPlus : ℝ≥0∞), 0 < cMinus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
          (C θ : Ioi (0 : ℝ)) (w : ℂ) (R : Finset ℕ),
        R.Nonempty → (∀ j ∈ R, 1 ≤ j) →
        (∀ j ∈ R, ENNReal.ofReal p ≤ P {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q w
          (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal}) →
        P {ω | ∀ j ∈ R, h ω ∉ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q w
          (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal} ≤
          ENNReal.ofReal (c * Real.exp (-iterRate * R.card)) := by
  have hrate : 0 < iterRate := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ := Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open
    (1 / 7) (3 / 4) (by norm_num) (by norm_num) (by norm_num) iterRate hrate (1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM q a K C θ w R hRne hR1 hprob
  set N := R.card with hNdef
  have hN : 1 ≤ N := Finset.card_pos.mpr hRne
  let js : ℕ → ℕ := extEnum R
  have hjs : StrictMono js := extEnum_strictMono R hR1
  let Att : ℕ → Set Ω := fun j => {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q w
    (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal}
  let rad : ℕ → ℝ := fun k => 3 * (EndSaving.Interfaces.dyadicRadius (js k) : ℝ)
  have hrad : ∀ k, rad k = 3 * (8 : ℝ) ^ (-(js k : ℤ)) := fun k => rfl
  have hradpos : ∀ k, 0 < rad k := fun k => by
    rw [hrad]
    positivity
  have hanti : Antitone rad := by
    intro k k' hkk'
    rw [hrad, hrad]
    have hle : js k ≤ js k' := hjs.monotone hkk'
    have : (8 : ℝ) ^ (-(js k' : ℤ)) ≤ (8 : ℝ) ^ (-(js k : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
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
    nlinarith
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
        (EndSaving.Interfaces.dyadicRadius (js k)) q a K C θ _
        (eventCarrier_subset_iterAnnulus w (EndSaving.Interfaces.dyadicRadius (js k))) (rad k)
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

 

theorem exp_rate_le (n N : ℕ) (hN : n ≤ 8 * N) :
    Real.exp (-iterRate * N) ≤ ((8 : ℝ) ^ (-(n : ℤ))) ^ 100 := by
  have h8 : (8 : ℝ) ^ (-(n : ℤ)) = Real.exp (-(n : ℝ) * Real.log 8) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    ring
  rw [h8, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  unfold iterRate
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hnN : (n : ℝ) ≤ 8 * N := by exact_mod_cast hN
  push_cast
  nlinarith

 



theorem cover_prob :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ (D D' : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∀ (cMinus cPlus : ℝ≥0∞), 0 < cMinus → cPlus < ⊤ →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
          (C θ : Ioi (0 : ℝ)) (B : ℝ), 0 ≤ B → ∀ (n : ℕ), 1 ≤ n → ∀ (R : Finset ℕ),
        R ⊆ Finset.Icc n (2 * n) → n ≤ 8 * R.card →
        (∀ (w : ℂ), ∀ j ∈ R, ENNReal.ofReal p ≤ P {ω | h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q
          w (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal}) →
        ∃ S : Set Ω, MeasurableSet S ∧
          P Sᶜ ≤ ENNReal.ofReal (c * (200 * (B + 1) + 3) ^ 2 * ((8 : ℝ) ^ (-(n : ℤ))) ^ 96) ∧
          ∀ ω ∈ S, ∀ x ∈ Metric.closedBall (0 : ℂ) B, ∃ (c' : ℂ) (r : ℝ),
            (∃ (hr : 0 < r) (hCircle : ℝ), TwoScale.S36Events.Attained (D (h ω)) (D' (h ω)) (ξ : ℝ) Q c'
              ⟨r, hr⟩ q a K C θ cMinus.toReal cPlus.toReal hCircle) ∧
            ((8 : ℝ) ^ (-(n : ℤ))) ^ 2 * 1 ≤ r ∧ r ≤ (8 : ℝ) ^ (-(n : ℤ)) * 1 ∧
            x ∈ Metric.ball c' (r / 2) := by
  obtain ⟨p, c, hp0, hp1, hc0, hsite⟩ := site_iteration
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM q a K C θ B hB n hn R hRsub
    hRcard hprob
  set ε : ℝ := (8 : ℝ) ^ (-(n : ℤ)) with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hR1 : ∀ j ∈ R, 1 ≤ j := fun j hj => le_trans hn (Finset.mem_Icc.mp (hRsub hj)).1
  have hRne : R.Nonempty := by
    rw [← Finset.card_pos]
    omega
  set m : ℝ := ε ^ 2 * 1 / 100 with hmdef
  set box := LQGMetric.CONF.gridBox m (1 * (B + 1)) 0 with hboxdef
  let site : ℤ × ℤ → ℂ := fun k => ⟨k.1 * m, k.2 * m⟩
  let Fail : ℤ × ℤ → Set Ω := fun k => {ω | ∀ j ∈ R, h ω ∉ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q
    (site k) (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal}
  have hFail : ∀ k, P (Fail k) ≤ ENNReal.ofReal (c * Real.exp (-iterRate * R.card)) := fun k =>
    hsite P h hh ξ Q hQ D D' hD hD' cMinus cPlus hm0 hMt hm hM q a K C θ (site k) R hRne hR1
      (hprob (site k))
  let S : Set Ω := ⋂ k ∈ box, (toMeasurable P (Fail k))ᶜ
  have hSm : MeasurableSet S :=
    Finset.measurableSet_biInter _ fun k _ => (measurableSet_toMeasurable P _).compl
  refine ⟨S, hSm, ?_, ?_⟩
  · have hSc : Sᶜ = ⋃ k ∈ box, toMeasurable P (Fail k) := by
      simp only [S, compl_iInter, compl_compl]
    rw [hSc]
    have hbudget := TwoScale.Stopping.fine_mesh_union_budget hε0 hε1 one_pos hB hc0.le 0
      (fun _ => c * Real.exp (-iterRate * R.card))
      (fun k _ => mul_le_mul_of_nonneg_left (exp_rate_le n R.card hRcard) hc0.le)
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
    have hxU : x ∈ (fun u : ℂ => ((1 : ℝ) : ℂ) * u) '' Metric.closedBall (0 : ℂ) B :=
      ⟨x, hx, by simp⟩
    obtain ⟨k, hk, hkx⟩ := TwoScale.Stopping.fine_mesh_site_in_box (U := Metric.closedBall (0 : ℂ) B)
      (B := B) subset_rfl hε0 hε1 one_pos hxU
    have hωk : ω ∉ Fail k := fun hF =>
      (mem_iInter₂.mp hω k hk) (subset_toMeasurable P _ hF)
    have hωk' : ∃ j ∈ R, h ω ∈ TwoScale.S36Events.AttainedEvent D D' (ξ : ℝ) Q (site k)
        (EndSaving.Interfaces.dyadicRadius j) q a K C θ cMinus.toReal cPlus.toReal := by
      by_contra hno
      push Not at hno
      exact hωk hno
    obtain ⟨j, hjR, hjE⟩ := hωk'
    obtain ⟨hCircle, -, hAtt⟩ := hjE
    have hjI := Finset.mem_Icc.mp (hRsub hjR)
    have hrj : ((EndSaving.Interfaces.dyadicRadius j : ℝ)) = (8 : ℝ) ^ (-(j : ℤ)) := rfl
    have hlow : ε ^ 2 * 1 ≤ (EndSaving.Interfaces.dyadicRadius j : ℝ) := by
      rw [mul_one, hrj, hεdef, ← zpow_natCast, ← zpow_mul]
      exact zpow_le_zpow_right₀ (by norm_num) (by push_cast; omega)
    have hhigh : (EndSaving.Interfaces.dyadicRadius j : ℝ) ≤ ε * 1 := by
      rw [mul_one, hrj, hεdef]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    refine ⟨site k, (EndSaving.Interfaces.dyadicRadius j : ℝ), ⟨(EndSaving.Interfaces.dyadicRadius j).2, hCircle, hAtt⟩,
      hlow, hhigh, ?_⟩
    have hhalf := TwoScale.Stopping.fine_mesh_half_radius hε0 one_pos hlow x
    rw [Metric.mem_ball]
    have hsite : site k = LQGMetric.CONF.conf36Grid (ε ^ 2 * 1 / 100) x := hkx
    rw [hsite]
    exact hhalf

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
