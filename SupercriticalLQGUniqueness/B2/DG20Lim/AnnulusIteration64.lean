import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedLMAnnulus
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Asymptotics
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def geoRad64 (ρ₀ t : ℝ) : ℝ := ρ₀ * (64 : ℝ) ^ (-t)

lemma geoRad64_pos {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (t : ℝ) : 0 < geoRad64 ρ₀ t :=
  mul_pos hρ₀ (Real.rpow_pos_of_pos (by norm_num) _)

lemma geoRad64_succ_div_le {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {s t : ℝ} (hst : s + 1 ≤ t) :
    geoRad64 ρ₀ t / geoRad64 ρ₀ s ≤ 1 / 64 := by
  unfold geoRad64
  rw [mul_div_mul_left _ _ hρ₀.ne', ← Real.rpow_sub (by norm_num)]
  calc (64 : ℝ) ^ (-t - -s) ≤ (64 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 64 := by rw [Real.rpow_neg_one]; norm_num

 
theorem annulus_iteration_finset64 (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsWholePlaneGFF h P →
        ∀ (z : ℂ) (ρ₀ : ℝ), 0 < ρ₀ → ∀ (S : Finset ℕ), S.Nonempty → ∀ (E : ℕ → Set Ω),
          (∀ i ∈ S, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigma
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (geoRad64 ρ₀ i) z))
              (LQGMetric.Blueprint.annulus z (1 / 64 * geoRad64 ρ₀ i) (1 / 2 * geoRad64 ρ₀ i)))
            (E i)) →
          (∀ i ∈ S, ENNReal.ofReal p ≤ P (E i)) →
          P {ω | ∀ i ∈ S, ω ∉ E i} ≤ ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    Uniqueness.Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open (1 / 64) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) a ha (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh z ρ₀ hρ₀ S hS E hloc hprob
  classical
  set K := S.card with hKdef
  have hK : 0 < K := Finset.card_pos.2 hS
  let e : Fin K ↪o ℕ := S.orderEmbOfFin rfl
  let g : ℕ → ℕ := fun j => if hj : j < K then e ⟨j, hj⟩ else e ⟨K - 1, by omega⟩ + 1 + j
  have hg : StrictMono g := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    by_cases h1 : n + 1 < K
    · have h0 : n < K := by omega
      simp only [g, h0, h1, ↓reduceDIte]
      exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self n))
    · have h1' : ¬ n + 1 < K := h1
      simp only [g, h1', ↓reduceDIte]
      by_cases h0 : n < K
      · simp only [h0, ↓reduceDIte]
        have hn : n = K - 1 := by omega
        subst hn
        omega
      · simp only [h0, ↓reduceDIte]
        omega
  have hgS : ∀ j, j < K → g j ∈ S := by
    intro j hj
    simp only [g, hj, ↓reduceDIte]
    exact Finset.orderEmbOfFin_mem S rfl _
  let t : ℕ → ℝ := fun k => if k = 0 then -1 else ((g (k - 1) : ℕ) : ℝ)
  have ht : ∀ k, t k + 1 ≤ t (k + 1) := by
    intro k
    have hk1 : t (k + 1) = ((g k : ℕ) : ℝ) := by simp [t]
    rw [hk1]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [t]
    · have hk0 : k ≠ 0 := hk.ne'
      have : t k = ((g (k - 1) : ℕ) : ℝ) := by simp [t, hk0]
      rw [this]
      have hlt : g (k - 1) < g k := hg (by omega)
      exact_mod_cast hlt
  let r : ℕ → ℝ := fun k => geoRad64 ρ₀ (t k)
  let E' : ℕ → Set Ω := fun k => if k ≠ 0 ∧ k - 1 < K then E (g (k - 1)) else univ
  have hr : ∀ k, 0 < r k := fun k => geoRad64_pos hρ₀ _
  have hratio : ∀ k, r (k + 1) / r k ≤ 1 / 64 := fun k => geoRad64_succ_div_le hρ₀ (ht k)
  have hanti : Antitone r := by
    refine antitone_nat_of_succ_le fun k => ?_
    have h1 := hratio k
    rw [div_le_iff₀ (hr k)] at h1
    linarith [hr k]
  have hE'loc : ∀ k, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
        (LQGMetric.Blueprint.annulus z (1 / 64 * r k) (1 / 2 * r k))) (E' k) := by
    intro k
    by_cases hk : k ≠ 0 ∧ k - 1 < K
    · have hrk : r k = geoRad64 ρ₀ ((g (k - 1) : ℕ) : ℝ) := by simp [r, t, hk.1]
      have hE : E' k = E (g (k - 1)) := by simp [E', hk.1, hk.2]
      rw [hE, hrk]
      exact hloc _ (hgS _ hk.2)
    · simp only [E', hk, ↓reduceIte]
      exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
  have hE'prob : ∀ k, ENNReal.ofReal p ≤ P (E' k) := by
    intro k
    by_cases hk : k ≠ 0 ∧ k - 1 < K
    · have hE : E' k = E (g (k - 1)) := by simp [E', hk.1, hk.2]
      rw [hE]
      exact hprob _ (hgS _ hk.2)
    · simp only [E', hk, ↓reduceIte, measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le
  have hLM := hmain P h hh z r E' hr hanti hratio hE'loc hE'prob K
  refine le_trans (measure_mono ?_) hLM
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  have hzero : LQGMetric.Blueprint.countOcc E' K ω = 0 := by
    unfold LQGMetric.Blueprint.countOcc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hmem
    rw [Finset.mem_Icc] at hk
    have hk' : k ≠ 0 ∧ k - 1 < K := ⟨by omega, by omega⟩
    have hE : E' k = E (g (k - 1)) := by simp [E', hk'.1, hk'.2]
    rw [hE] at hmem
    exact hω _ (hgS _ hk'.2) hmem
  rw [hzero]
  have : (0 : ℝ) < K := by exact_mod_cast hK
  push_cast
  linarith

end SupercriticalLQGUniqueness.B2.DG20Lim
