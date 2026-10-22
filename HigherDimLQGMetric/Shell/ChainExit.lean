import HigherDimLQGMetric.Shell.ChainCore
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.IntermediateValue

/-!
# Finite exit-time chain of good balls

Port of the crossing-time construction in `LQGMetric.LM.lm_chain_det` from `ℂ` to `Rd d`.
Every exit moves the path by at least half the minimum good radius. Uniform continuity
therefore makes the chain finite.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Finite crossing times and their good balls, with the final ball containing the path's end. -/
theorem exists_sphere_exits {ρ ε : ℝ} (hρ : 0 < ρ) (P : ℝ → Rd d)
    (hP : ContinuousOn P (Icc 0 1)) (good : Rd d → ℝ → Prop)
    (hcov : ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r, ρ ≤ r ∧ r ≤ ε ∧
      ‖P s - w‖ < r / 2 ∧ good w r) :
    ∃ (W : ℝ → Rd d) (R : ℝ → ℝ) (S : ℕ → ℝ) (J : ℕ),
      (∀ s ∈ Icc (0 : ℝ) 1, ρ ≤ R s) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, R s ≤ ε) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ‖P s - W s‖ < R s / 2) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, good (W s) (R s)) ∧
      S 0 = 0 ∧ (∀ n, S n ∈ Icc (0 : ℝ) 1) ∧ Monotone S ∧
      (∀ i < J, ‖P (S (i + 1)) - W (S i)‖ = R (S i)) ∧
      ‖P 1 - W (S J)‖ < R (S J) := by
  classical
  choose! W R hρR hRε hin hg using hcov
  let Ex : ℝ → Prop := fun s => ∃ t ∈ Icc s 1, R s ≤ ‖P t - W s‖
  have hivt : ∀ s ∈ Icc (0 : ℝ) 1, Ex s →
      ∃ t ∈ Icc s 1, ‖P t - W s‖ = R s := by
    intro s hs ⟨t₁, ht₁, hR⟩
    have hsub : Icc s t₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs.1 ht₁.2
    have hf : ContinuousOn (fun t => ‖P t - W s‖) (Icc s t₁) :=
      ((hP.mono hsub).sub continuousOn_const).norm
    have hmem : R s ∈ Icc ‖P s - W s‖ ‖P t₁ - W s‖ :=
      ⟨by linarith [hin s hs, hρR s hs], hR⟩
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc ht₁.1 hf hmem
    exact ⟨t, ⟨ht.1, ht.2.trans ht₁.2⟩, hft⟩
  let nx : ℝ → ℝ := fun s =>
    if h : s ∈ Icc (0 : ℝ) 1 ∧ Ex s then Classical.choose (hivt s h.1 h.2) else s
  have hnx : ∀ s ∈ Icc (0 : ℝ) 1,
      nx s ∈ Icc s 1 ∧ (Ex s → ‖P (nx s) - W s‖ = R s) := by
    intro s hs
    by_cases h : Ex s
    · have hh : s ∈ Icc (0 : ℝ) 1 ∧ Ex s := ⟨hs, h⟩
      have := Classical.choose_spec (hivt s hs h)
      simp only [nx, hh]
      exact ⟨this.1, fun _ => this.2⟩
    · have hh : ¬ (s ∈ Icc (0 : ℝ) 1 ∧ Ex s) := fun h' => h h'.2
      simp only [nx, hh]
      exact ⟨⟨le_rfl, hs.2⟩, fun h' => absurd h' h⟩
  let S : ℕ → ℝ := fun n => nx^[n] 0
  have hS0 : S 0 = 0 := rfl
  have hSs : ∀ n, S (n + 1) = nx (S n) := fun n => Function.iterate_succ_apply' nx n 0
  have hSI : ∀ n, S n ∈ Icc (0 : ℝ) 1 := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, zero_le_one⟩
    | succ n ih =>
      rw [hSs]
      have := (hnx _ ih).1
      exact ⟨ih.1.trans this.1, this.2⟩
  have hSle : ∀ n, S n ≤ S (n + 1) := fun n => by
    rw [hSs]
    exact (hnx _ (hSI n)).1.1
  have hSmono : Monotone S := monotone_nat_of_le_succ hSle
  obtain ⟨η, hη, hηP⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) (ρ / 2) (by linarith)
  have hstep : ∀ n, Ex (S n) → S n + η ≤ S (n + 1) := by
    intro n hE
    by_contra hlt
    push Not at hlt
    have h1 := (hnx _ (hSI n)).2 hE
    rw [← hSs] at h1
    have hd : dist (S (n + 1)) (S n) < η := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hSle n])]
      linarith
    have hP' := hηP _ (hSI (n + 1)) _ (hSI n) hd
    rw [dist_eq_norm] at hP'
    have h2 := hin _ (hSI n)
    have h3 := hρR _ (hSI n)
    have htri : ‖P (S (n + 1)) - W (S n)‖ ≤
        ‖P (S (n + 1)) - P (S n)‖ + ‖P (S n) - W (S n)‖ := by
      calc
        ‖P (S (n + 1)) - W (S n)‖ =
            ‖(P (S (n + 1)) - P (S n)) + (P (S n) - W (S n))‖ := by
              congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  have hstop : ∃ n, ¬ Ex (S n) := by
    by_contra hall
    push Not at hall
    have hlin : ∀ n : ℕ, (n : ℝ) * η ≤ S n := by
      intro n
      induction n with
      | zero => simp [hS0]
      | succ n ih => push_cast; linarith [hstep n (hall n)]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / η)
    have h1 : 1 < (n : ℝ) * η := by rwa [div_lt_iff₀ hη] at hn
    linarith [hlin n, (hSI n).2]
  let J := Nat.find hstop
  have hJ : ¬ Ex (S J) := Nat.find_spec hstop
  have hbefore : ∀ i < J, Ex (S i) := fun i hi => by
    have := Nat.find_min hstop hi
    push Not at this
    exact this
  refine ⟨W, R, S, J, hρR, hRε, hin, hg, hS0, hSI, hSmono, ?_, ?_⟩
  · intro i hi
    have := (hnx _ (hSI i)).2 (hbefore i hi)
    rwa [← hSs] at this
  · by_contra hc
    push Not at hc
    exact hJ ⟨1, ⟨(hSI J).2, le_rfl⟩, hc⟩

end HigherDimLQGMetric
