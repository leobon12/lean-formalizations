import SmallGammaGeodesics.Core.Interfaces
import LQGMetric.Papers.LM.T1_6Chain

/-!
# Deterministic chaining for an extended-valued function (track CC, packet CC8a, target T1)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379), proof of
Theorem 1.6, l. 838–882, as formalized in `LQGMetric.LM.chain_main` and `LQGMetric.LM.lm_chain_det`
(`LQGMetric/Papers/LM/T1_6Chain.lean`, `T1_6Cross.lean`). Plan: `planning/audits/
CC0-conformal-covariance-plan.md`, Details (a) **D13** step 2 (chaining for `d := D^ϕ`).

The LQGMetric lemmas are stated for a `ContMetric` `D'`. Their proofs use only the triangle
inequality of `D'` and `D'(x, x) = 0`. Here `D'` is replaced by an arbitrary function
`d : ℂ → ℂ → ℝ≥0∞` with these two properties, as needed for the transported domain metric
`D^ϕ = CC.confMetric …`, which may take the value `∞`. The bounds become `ENNReal.ofReal (C * …)`.

* `chain_main_ext`: generalizes `LM.chain_main`. The geometric backward search
  `LM.chain_back` involves no metric and is reused verbatim.
* `chainDetExt : ChainDetExt` (**T1**): generalizes `LM.lm_chain_det`. The construction of the
  crossing times is LM's (l. 844–847), copied from `lm_chain_det`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- `ofReal a + ofReal b ≤ ofReal c` from `a + b ≤ c` with `a, b ≥ 0` -/
lemma ofReal_add_le_ofReal {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ c) :
    ENNReal.ofReal a + ENNReal.ofReal b ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_add ha hb]
  exact ENNReal.ofReal_le_ofReal h

/-- **The chaining bound** (LM l. 877–880; generalizes `LQGMetric.LM.chain_main` to an
`ℝ≥0∞`-valued `d` with the triangle inequality and `d x x = 0`): every point `u` of the circle
`∂B_{r_j}(w_j)` is within `d`-distance `C (T_j − T_0)` of a point of `cl B_{2ε}(p_0)`. -/
theorem chain_main_ext (d : ℂ → ℂ → ℝ≥0∞) (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hd0 : ∀ x, d x x = 0) {C ε : ℝ} (hC : 0 ≤ C) (p w : ℕ → ℂ) (r T : ℕ → ℝ) (J : ℕ)
    (hT : Monotone T)
    (hin : ∀ i, 1 ≤ i → i ≤ J → ‖p (i - 1) - w i‖ < r i / 2)
    (hon : ∀ i, 1 ≤ i → i ≤ J → ‖p i - w i‖ = r i) (hr : ∀ i, 0 < r i) (hrε : ∀ i, r i ≤ ε)
    (hdiam : ∀ i, 1 ≤ i → i ≤ J → ∀ u ∈ sphere (w i) (r i), ∀ v ∈ sphere (w i) (r i),
      d u v ≤ ENNReal.ofReal (C * (T i - T (i - 1)))) :
    ∀ j, 1 ≤ j → j ≤ J → ∀ u ∈ sphere (w j) (r j),
      ∃ x, ‖x - p 0‖ ≤ 2 * ε ∧ d x u ≤ ENNReal.ofReal (C * (T j - T 0)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hjJ u hu
    have hpj : ‖p (j - 1) - w j‖ < r j := by linarith [hin j hj1 hjJ, hr j]
    rcases LM.chain_back p w r J hin hon hr j hjJ (j - 1) (by omega) hpj with
      ⟨i', h1, h2, y, hy1, hy2⟩ | h0
    · obtain ⟨x, hx, hxy⟩ := ih i' (by omega) h1 (by omega) y hy1
      refine ⟨x, hx, ?_⟩
      have hyu := hdiam j hj1 hjJ y hy2 u hu
      have hmono : T i' ≤ T (j - 1) := hT (by omega)
      have hT0 : T 0 ≤ T i' := hT (Nat.zero_le i')
      have hTj : T (j - 1) ≤ T j := hT (Nat.sub_le j 1)
      calc d x u ≤ d x y + d y u := htri x y u
        _ ≤ ENNReal.ofReal (C * (T i' - T 0)) + ENNReal.ofReal (C * (T j - T (j - 1))) :=
          add_le_add hxy hyu
        _ ≤ ENNReal.ofReal (C * (T j - T 0)) :=
          ofReal_add_le_ofReal (mul_nonneg hC (by linarith)) (mul_nonneg hC (by linarith))
            (by nlinarith)
    · refine ⟨u, ?_, ?_⟩
      · have hu' : ‖u - w j‖ = r j := by rw [mem_sphere, dist_eq_norm] at hu; exact hu
        calc ‖u - p 0‖ = ‖(u - w j) - (p 0 - w j)‖ := by congr 1; ring
          _ ≤ ‖u - w j‖ + ‖p 0 - w j‖ := norm_sub_le _ _
          _ ≤ 2 * ε := by linarith [hrε j]
      · rw [hd0]
        exact zero_le

/-- **T1: LM Theorem 1.6, deterministic step, extended-metric form** (LM l. 844–880; generalizes
`LQGMetric.LM.lm_chain_det` from a `ContMetric` to any `ℝ≥0∞`-valued `d` with the triangle
inequality and `d x x = 0`). If every point of a path `P : [0,1] → ℂ` lies in a ball
`B_{r/2}(w)` with `r ∈ [ρ, ε]` and `(w, r)` good, where good means that whenever `P` crosses
`A_{r/2, r}(w)` between times `a ≤ b` all points of `∂B_r(w)` are `d`-within `C (ℓ(b) − ℓ(a))`,
then `d(x, y) ≤ C (ℓ(1) − ℓ(0))` for some `x ∈ cl B_{2ε}(P 0)`, `y ∈ cl B_{2ε}(P 1)`. -/
theorem chainDetExt : ChainDetExt := by
  intro d htri hd0 C ε ρ hC hρ P hPc ℓ hℓ good hcov hgood
  classical
  choose! W R hρR hRε hin hg using hcov
  -- the exit predicate and the next crossing time
  let Ex : ℝ → Prop := fun s => ∃ t ∈ Icc s 1, R s ≤ ‖P t - W s‖
  have hivt : ∀ s ∈ Icc (0 : ℝ) 1, Ex s → ∃ t ∈ Icc s 1, ‖P t - W s‖ = R s := by
    intro s hs ⟨t₁, ht₁, hR⟩
    have hsub : Icc s t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht₁.2
    have hf : ContinuousOn (fun t => ‖P t - W s‖) (Icc s t₁) :=
      ((hPc.mono hsub).sub continuousOn_const).norm
    have hmem : R s ∈ Icc ‖P s - W s‖ ‖P t₁ - W s‖ :=
      ⟨by linarith [hin s hs, hρR s hs], hR⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc ht₁.1 hf hmem
    exact ⟨t, ⟨ht.1, ht.2.trans ht₁.2⟩, hft⟩
  let nx : ℝ → ℝ := fun s =>
    if h : s ∈ Icc (0 : ℝ) 1 ∧ Ex s then Classical.choose (hivt s h.1 h.2) else s
  have hnx : ∀ s ∈ Icc (0 : ℝ) 1, nx s ∈ Icc s 1 ∧ (Ex s → ‖P (nx s) - W s‖ = R s) := by
    intro s hs
    by_cases h : Ex s
    · have hh : s ∈ Icc (0 : ℝ) 1 ∧ Ex s := ⟨hs, h⟩
      have := Classical.choose_spec (hivt s hs h)
      simp only [nx, dite_eq_left hh]
      exact ⟨this.1, fun _ => this.2⟩
    · have hh : ¬ (s ∈ Icc (0 : ℝ) 1 ∧ Ex s) := fun h' => h h'.2
      simp only [nx, dite_eq_right hh]
      exact ⟨⟨le_rfl, hs.2⟩, fun h' => absurd h' h⟩
  let S : ℕ → ℝ := fun n => nx^[n] 0
  have hS0 : S 0 = 0 := rfl
  have hSs : ∀ n, S (n + 1) = nx (S n) := fun n => Function.iterate_succ_apply' nx n 0
  have hSI : ∀ n, S n ∈ Icc (0 : ℝ) 1 := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, zero_le_one⟩
    | succ n ih =>
      rw [hSs]; have := (hnx _ ih).1; exact ⟨ih.1.trans this.1, this.2⟩
  have hSle : ∀ n, S n ≤ S (n + 1) := fun n => by rw [hSs]; exact (hnx _ (hSI n)).1.1
  have hSmono : Monotone S := monotone_nat_of_le_succ hSle
  -- uniform continuity: each exit step takes parameter time at least `η`
  obtain ⟨η, hη, hηP⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hPc) (ρ / 2) (by linarith)
  have hstep : ∀ n, Ex (S n) → S n + η ≤ S (n + 1) := by
    intro n hE
    by_contra hlt
    push Not at hlt
    have h1 := (hnx _ (hSI n)).2 hE
    rw [← hSs] at h1
    have hd : dist (S (n + 1)) (S n) < η := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hSle n])]; linarith
    have hP := hηP _ (hSI (n + 1)) _ (hSI n) hd
    rw [dist_eq_norm] at hP
    have h2 := hin _ (hSI n)
    have h3 := hρR _ (hSI n)
    have : ‖P (S (n + 1)) - W (S n)‖ ≤ ‖P (S (n + 1)) - P (S n)‖ + ‖P (S n) - W (S n)‖ := by
      calc ‖P (S (n + 1)) - W (S n)‖ = ‖(P (S (n + 1)) - P (S n)) + (P (S n) - W (S n))‖ := by
            congr 1; ring
        _ ≤ _ := norm_add_le _ _
    linarith
  have hstop : ∃ n, ¬ Ex (S n) := by
    by_contra hall
    push Not at hall
    have hlin : ∀ n : ℕ, (n : ℝ) * η ≤ S n := by
      intro n
      induction n with
      | zero => simp only [Nat.cast_zero, zero_mul, hS0, le_refl]
      | succ n ih => push_cast; linarith [hstep n (hall n)]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
    have := hlin n
    have h1 : 1 < (n : ℝ) * η := by rwa [div_lt_iff₀ hη] at hn
    linarith [(hSI n).2]
  let J := Nat.find hstop
  have hJ : ¬ Ex (S J) := Nat.find_spec hstop
  have hbefore : ∀ i < J, Ex (S i) := fun i hi => by
    have := Nat.find_min hstop hi; push Not at this; exact this
  -- the chain data
  have hT : Monotone (fun n => ℓ (S n)) :=
    monotone_nat_of_le_succ fun n => hℓ (hSI n) (hSI (n + 1)) (hSle n)
  have hin' : ∀ i, 1 ≤ i → i ≤ J → ‖P (S (i - 1)) - W (S (i - 1))‖ < R (S (i - 1)) / 2 :=
    fun i _ _ => hin _ (hSI _)
  have hon' : ∀ i, 1 ≤ i → i ≤ J → ‖P (S i) - W (S (i - 1))‖ = R (S (i - 1)) := by
    intro i hi1 hiJ
    have he : i = (i - 1) + 1 := by omega
    have h := (hnx _ (hSI (i - 1))).2 (hbefore (i - 1) (by omega))
    rw [← hSs, ← he] at h
    exact h
  have hr' : ∀ i, 0 < R (S (i - 1)) := fun i => lt_of_lt_of_le hρ (hρR _ (hSI _))
  have hdiam : ∀ i, 1 ≤ i → i ≤ J → ∀ u ∈ sphere (W (S (i - 1))) (R (S (i - 1))),
      ∀ v ∈ sphere (W (S (i - 1))) (R (S (i - 1))),
      d u v ≤ ENNReal.ofReal (C * (ℓ (S i) - ℓ (S (i - 1)))) := by
    intro i hi1 hiJ
    exact hgood _ _ (hg _ (hSI _)) _ (hSI _) _ (hSI _) (hSmono (Nat.sub_le i 1))
      (hin' i hi1 hiJ) (hon' i hi1 hiJ)
  -- the endpoint
  have hend : ‖P (S J) - P 1‖ ≤ 2 * ε := by
    have h1 : ‖P 1 - W (S J)‖ < R (S J) := by
      by_contra hc; push Not at hc; exact hJ ⟨1, ⟨(hSI J).2, le_rfl⟩, hc⟩
    have h2 := hin _ (hSI J)
    have h3 := hRε _ (hSI J)
    calc ‖P (S J) - P 1‖ = ‖(P (S J) - W (S J)) - (P 1 - W (S J))‖ := by congr 1; ring
      _ ≤ ‖P (S J) - W (S J)‖ + ‖P 1 - W (S J)‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith [hρR _ (hSI J), hρ]
  have hℓ1 : ℓ (S J) - ℓ (S 0) ≤ ℓ 1 - ℓ 0 := by
    rw [hS0]; linarith [hℓ (hSI J) ⟨zero_le_one, le_rfl⟩ (hSI J).2]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · refine ⟨P (S J), P (S J), ?_, hend, ?_⟩
    · rw [hJ0, hS0, sub_self, norm_zero]
      linarith [hRε _ (hSI 0), hρR _ (hSI 0), hρ]
    · rw [hd0]
      exact zero_le
  · obtain ⟨x, hx, hxu⟩ := chain_main_ext d htri hd0 hC (fun n => P (S n)) (fun j => W (S (j - 1)))
      (fun j => R (S (j - 1))) (fun n => ℓ (S n)) J hT hin' hon' hr'
      (fun i => hRε _ (hSI _)) hdiam J hJ0 le_rfl (P (S J))
      (by rw [mem_sphere, dist_eq_norm]; exact hon' J hJ0 le_rfl)
    refine ⟨x, P (S J), by simpa only [hS0] using hx, hend, ?_⟩
    calc d x (P (S J)) ≤ ENNReal.ofReal (C * (ℓ (S J) - ℓ (S 0))) := hxu
      _ ≤ ENNReal.ofReal (C * (ℓ 1 - ℓ 0)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hℓ1 hC)

end SmallGammaGeodesics.CC
