import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Good




 
















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 
def scale16 (s : Ioi (0 : ℝ)) (j : ℕ) : Ioi (0 : ℝ) :=
  ⟨(16 : ℝ) ^ (-(j : ℤ)) * s, mem_Ioi.mpr (mul_pos (zpow_pos (by norm_num) _) s.2)⟩

theorem scale16_val (s : Ioi (0 : ℝ)) (j : ℕ) :
    (scale16 s j : ℝ) = (16 : ℝ) ^ (-(j : ℤ)) * s := rfl

 

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
      rw [dite_eq_right (by omega), ite_eq_right hi0, dite_eq_right (by omega),
        ite_eq_right (by omega)]
      omega

 
theorem goodCarrier_subset_iterAnnulus (w : ℂ) (t : ℝ) :
    goodCarrier w t ⊆
      (LQGMetric.Blueprint.annulus w ((1 / 4 : ℝ) * (3 * t)) ((3 / 4 : ℝ) * (3 * t)) : Set ℂ) := by
  intro x hx
  change (1 / 4 : ℝ) * (3 * t) < ‖x - w‖ ∧ ‖x - w‖ < (3 / 4 : ℝ) * (3 * t)
  obtain ⟨h1, h2⟩ := hx
  constructor <;> linarith

 


theorem goodAnn_site_iteration (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (ξ : Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ (D : DistC → LSCMetric),
        IsWeakLQGMetric ξ Q D → ∀ (M : ℝ) (w : ℂ) (s : Ioi (0 : ℝ)) (R : Finset ℕ),
        R.Nonempty → (∀ j ∈ R, 1 ≤ j) →
        (∀ j ∈ R, ENNReal.ofReal p ≤ P {ω | h ω ∈ goodAnn ξ Q D M w (scale16 s j)}) →
        P {ω | ∀ j ∈ R, h ω ∉ goodAnn ξ Q D M w (scale16 s j)} ≤
          ENNReal.ofReal (c * Real.exp (-a * R.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ := Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open
    (1 / 4) (3 / 4) (by norm_num) (by norm_num) (by norm_num) a ha (1 / 2)
    (by norm_num) (by norm_num)
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ Q hQ D hD M w s R hRne hR1 hprob
  set N := R.card with hNdef
  have hN : 1 ≤ N := Finset.card_pos.mpr hRne
  have hs : 0 < (s : ℝ) := s.2
  let js : ℕ → ℕ := extEnum R
  have hjs : StrictMono js := extEnum_strictMono R hR1
  let Att : ℕ → Set Ω := fun j => {ω | h ω ∈ goodAnn ξ Q D M w (scale16 s j)}
  let rad : ℕ → ℝ := fun k => 3 * (scale16 s (js k) : ℝ)
  have hrad : ∀ k, rad k = 3 * ((16 : ℝ) ^ (-(js k : ℤ)) * s) := fun k => rfl
  have hradpos : ∀ k, 0 < rad k := fun k => by
    rw [hrad]
    positivity
  have hanti : Antitone rad := by
    intro k k' hkk'
    rw [hrad, hrad]
    have hle : js k ≤ js k' := hjs.monotone hkk'
    have : (16 : ℝ) ^ (-(js k' : ℤ)) ≤ (16 : ℝ) ^ (-(js k : ℤ)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have := mul_le_mul_of_nonneg_right this hs.le
    linarith
  have hratio : ∀ k, rad (k + 1) / rad k ≤ 1 / 4 := by
    intro k
    rw [div_le_iff₀ (hradpos k), hrad, hrad]
    have hlt : js k + 1 ≤ js (k + 1) := hjs (Nat.lt_succ_self k)
    have h16 : (16 : ℝ) ^ (-(js (k + 1) : ℤ)) ≤ (16 : ℝ) ^ (-((js k : ℤ) + 1)) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hsplit : (16 : ℝ) ^ (-((js k : ℤ) + 1)) = (16 : ℝ) ^ (-(js k : ℤ)) / 16 := by
      rw [neg_add, zpow_add₀ (by norm_num : (16 : ℝ) ≠ 0), zpow_neg_one]
      ring
    have hpos : 0 < (16 : ℝ) ^ (-(js k : ℤ)) := by positivity
    rw [hsplit] at h16
    have h16b := mul_le_mul_of_nonneg_right h16 hs.le
    have hpb : 0 < (16 : ℝ) ^ (-(js k : ℤ)) * s := mul_pos hpos hs
    have : (16 : ℝ) ^ (-(js k : ℤ)) / 16 * s = (16 : ℝ) ^ (-(js k : ℤ)) * s / 16 := by ring
    rw [this] at h16b
    linarith
  let E : ℕ → Set Ω := fun k => if 1 ≤ k ∧ k ≤ N then Att (js k) else univ
  have hEloc : ∀ k, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (rad k) w))
        (LQGMetric.Blueprint.annulus w ((1 / 4 : ℝ) * rad k) ((3 / 4 : ℝ) * rad k))) (E k) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · have hEk : E k = Att (js k) := ite_eq_left hk
      rw [hEk]
      exact goodAnn_centered_local P h hh ξ Q hQ D hD M w (scale16 s (js k)) _
        (goodCarrier_subset_iterAnnulus w (scale16 s (js k))) (rad k)
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

 


theorem goodAnn_no_good_scale (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (a : ℝ) (ha : 0 < a) :
    ∃ M c : ℝ, 1 ≤ M ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ (w : ℂ) (s : Ioi (0 : ℝ)) (R : Finset ℕ), R.Nonempty → (∀ j ∈ R, 1 ≤ j) →
        P {ω | ∀ j ∈ R, h ω ∉ goodAnn ξ Q D M w (scale16 s j)} ≤
          ENNReal.ofReal (c * Real.exp (-a * R.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hiter⟩ := goodAnn_site_iteration a ha
  obtain ⟨M, hM, hprob⟩ := exists_goodAnn_prob ξ Q D hD p hp0 hp1
  refine ⟨M, c, hM, hc0, ?_⟩
  intro Ω _ P _ h hh w s R hRne hR1
  exact hiter P h hh ξ Q hQ D hD M w s R hRne hR1 (fun j _ => hprob P h hh w (scale16 s j))

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
