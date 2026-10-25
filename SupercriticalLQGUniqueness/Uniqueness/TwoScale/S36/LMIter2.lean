import LQGMetric.Papers.LM.L3_4M6
import LQGMetric.Papers.LM.L3_4Incr




 














set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric LQGMetric.LM

open MeasureTheory ProbabilityTheory LQGMetric.Blueprint in
 



def LMLem3_1b : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → ∀ p : ℝ, 0 < p → p < 1 →
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ b < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω), AnnulusIterHyp h s₁ s₂ r E →
        (∀ k, ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K))


open MeasureTheory ProbabilityTheory LQGMetric.Blueprint in
 
theorem lmLem3_1b_of_inputQ (hIn : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 →
    LMAnnulusIterInputQ s₁ s₂) : LMLem3_1b := by
  intro s₁ s₂ hs₁ hs₁₂ hs₂ p hp0 hp1
  obtain ⟨C, M₁, M₀, c₀, hC, hc₀, H⟩ := hIn s₁ s₂ hs₁ hs₁₂ hs₂
  set M := max (M₀ 1 (1 / 2)) (M₁ p)
  set CM := C M
  have hCM : 0 < CM := hC M
  set q := min ((p / 4) ^ 4 / CM) 1 with hqdef
  have hq0 : 0 < q := lt_min (by positivity) one_pos
  have hq1 : q ≤ 1 := min_le_right _ _
  set φ := 1 - q + q * Real.exp (-1) with hφdef
  have he1 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
  have hφ0 : 0 < φ := by have := Real.exp_pos (-1); nlinarith
  have hφ1 : φ < 1 := by nlinarith
  set γ := -Real.log φ / 2 with hγdef
  have hγ : 0 < γ := by have := Real.log_neg hφ0 hφ1; rw [hγdef]; linarith
  set b := min (γ / 2) (1 / 2) with hbdef
  have hb0 : 0 < b := lt_min (by linarith) (by norm_num)
  have hb1 : b < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set a := min 1 (γ / 2) with hadef
  have ha : 0 < a := lt_min one_pos (by linarith)
  refine ⟨a, b, c₀ 1 (1 / 2) + 1, ha, hb0, hb1, by linarith [hc₀ 1 (1 / 2)], ?_⟩
  intro Ω _ P _ h hh r E hE hpE K
  obtain ⟨hr0, hrA, hrs, hEm⟩ := hE
  obtain ⟨Good, hGood, hmono, h38, h310⟩ := H P h hh r hr0 hrA hrs
  have hq : ∀ k, ∀ᵐ ω ∂P, ω ∈ Good M k →
      q ≤ P[(E k).indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ω := by
    intro k
    filter_upwards [h38 p hp0 hp1.le M (le_max_right _ _) k (E k) (hEm k)] with ω hω hG
    exact (min_le_left _ _).trans ((hω hG).2 (real_ge_of_ofReal_le (hpE k)))
  have hρ : Real.exp (1 * γ) * φ ≤ Real.exp (-γ) := by
    have : φ = Real.exp (-(2 * γ)) := by
      rw [hγdef, show -(2 * (-Real.log φ / 2)) = Real.log φ by ring, Real.exp_log hφ0]
    rw [this, ← Real.exp_add]; apply le_of_eq; congr 1; ring
  have hmain := prob_countOcc_lt_le (lmFiltration P hh.1 hr0 hrA) (G := Good M) (E := E)
    (hGood M) (fun k => annSigma_le_lmFiltration hh.1 hr0 hrA (by linarith) hrs k _ (hEm k))
    (q := q) (l := 1) (α := γ) (β := 1 / 2) (b := b) hq0.le hq1
    zero_le_one hγ.le (by rw [hbdef]; exact (min_le_left _ _).trans (by linarith)) hγ.le hρ hq K
  have h4 := (prob_countOcc_mono (P := P) (G := Good (M₀ 1 (1 / 2))) (G' := Good M)
    (fun k => hmono _ _ k (le_max_left _ _)) (1 / 2) K).trans
    (h310 1 one_pos (1 / 2) (by norm_num) (by norm_num) K)
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have e1 : Real.exp (-1 * K) ≤ Real.exp (-a * K) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left (1 : ℝ) (γ / 2)])
  have e2 : Real.exp (-(γ * (1 / 2)) * K) ≤ Real.exp (-a * K) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right (1 : ℝ) (γ / 2)])
  apply measure_le_ofReal_of_real
  have hc0 := hc₀ 1 (1 / 2)
  calc P.real {ω | (countOcc E K ω : ℝ) < b * K}
      ≤ c₀ 1 (1 / 2) * Real.exp (-1 * K) + Real.exp (-(γ * (1 / 2)) * K) := by linarith
    _ ≤ c₀ 1 (1 / 2) * Real.exp (-a * K) + Real.exp (-a * K) := by gcongr
    _ = (c₀ 1 (1 / 2) + 1) * Real.exp (-a * K) := by ring


open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace InnerProductSpace LQGMetric.Blueprint in
 
theorem lmLem3_1b_of_leaf (hL : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMGoodScaleLeaf s₁ s₂) :
    LMLem3_1b :=
  lmLem3_1b_of_inputQ fun s₁ s₂ h1 h2 h3 =>
    lmAnnulusIterInputQ_of MQ.mqLem4_1Gen (h1.trans h2) h3 (hL s₁ s₂ h1 h2 h3)


open MeasureTheory ProbabilityTheory Filter Set Finset LQGMetric.Blueprint in
 
theorem lmLem3_1b_of_dom
    (hD : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMScaleDomLeaf s₁ s₂) : LMLem3_1b :=
  lmLem3_1b_of_leaf fun s₁ s₂ h1 h2 h3 => lmGoodScaleLeaf_of_dom (hD s₁ s₂ h1 h2 h3)


open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace LQGMetric.Blueprint in
 
theorem lmLem3_1b_of_incr
    (hI : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMIncrLeaf s₁ s₂) : LMLem3_1b :=
  lmLem3_1b_of_dom fun s₁ s₂ h1 h2 h3 => lmScaleDomLeaf_of_incr h1 h2 h3 (hI s₁ s₂ h1 h2 h3)


open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace LQGMetric.Blueprint LQGMetric.GM in
 
theorem lmLem3_1b_of_nest (hN : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestLeaf s₁) : LMLem3_1b :=
  lmLem3_1b_of_incr fun s₁ _ h1 h2 h3 => lmIncrLeaf_of_nest (h1.trans h2) h3 (hN s₁ h1 (h2.trans h3))


open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace LQGMetric.Blueprint LQGMetric.GM in
 
theorem lmLem3_1b_of_core (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCoreLeaf s₁)
    (hH : LMHarmCenterLeaf) : LMLem3_1b :=
  lmLem3_1b_of_nest fun s₁ h1 h2 => lmNestLeaf_of_core (hC s₁ h1 h2) hH


open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace Topology LQGMetric.Blueprint LQGMetric.GM in
 
theorem lmLem3_1b_of_canon (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCanonLeaf s₁)
    (hH : LMHarmCenterLeaf) : LMLem3_1b :=
  lmLem3_1b_of_core (fun s₁ h1 h2 => lmNestCoreLeaf_of_canon (hC s₁ h1 h2)) hH


open MeasureTheory ProbabilityTheory Filter Set Finset Metric InnerProductSpace Topology LQGMetric.Blueprint LQGMetric.GM LQGMetric.CircleAvg LQGMetric.MarkovGauss LQGMetric.MarkovZB LQGMetric.MarkovNorm in
 
theorem lmLem3_1b_of_canon' (hC : ∀ s₁ : ℝ, 0 < s₁ → s₁ < 1 → LMNestCanonLeaf s₁) :
    LMLem3_1b :=
  lmLem3_1b_of_canon hC lmHarmCenterLeaf


open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace LQGMetric.Blueprint LQGMetric.MarkovGauss LQGMetric.MarkovNorm in
 
theorem lmLem3_1b : LMLem3_1b :=
  lmLem3_1b_of_canon' fun s₁ _ _ => lmNestCanonLeaf s₁

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
