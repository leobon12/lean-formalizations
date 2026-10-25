import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic




 









set_option autoImplicit false

noncomputable section

open Set

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36


 
def reachSet (F : Finset ℂ) (ρ : ℝ) (c₁ : ℂ) : ℕ → Finset ℂ
  | 0 => {c₁}
  | k + 1 => by
      classical
      exact reachSet F ρ c₁ k ∪
        F.filter fun c => ∃ c' ∈ reachSet F ρ c₁ k, dist c c' < 2 * ρ

theorem reachSet_succ (F : Finset ℂ) (ρ : ℝ) (c₁ : ℂ) (k : ℕ) (c : ℂ) :
    c ∈ reachSet F ρ c₁ (k + 1) ↔
      c ∈ reachSet F ρ c₁ k ∨ (c ∈ F ∧ ∃ c' ∈ reachSet F ρ c₁ k, dist c c' < 2 * ρ) := by
  classical
  simp only [reachSet, Finset.mem_union, Finset.mem_filter]

theorem reachSet_subset (F : Finset ℂ) (ρ : ℝ) {c₁ : ℂ} (hc₁ : c₁ ∈ F) (k : ℕ) :
    reachSet F ρ c₁ k ⊆ F := by
  induction k with
  | zero =>
      intro c hc
      simp only [reachSet, Finset.mem_singleton] at hc
      rw [hc]
      exact hc₁
  | succ k ih =>
      intro c hc
      rcases (reachSet_succ F ρ c₁ k c).mp hc with h | h
      · exact ih h
      · exact h.1

theorem reachSet_mono (F : Finset ℂ) (ρ : ℝ) (c₁ : ℂ) (k : ℕ) :
    reachSet F ρ c₁ k ⊆ reachSet F ρ c₁ (k + 1) := fun c hc =>
  (reachSet_succ F ρ c₁ k c).mpr (Or.inl hc)

theorem dist_reachSet (F : Finset ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (c₁ : ℂ) (k : ℕ) :
    ∀ c ∈ reachSet F ρ c₁ k, dist c c₁ ≤ 2 * ρ * k := by
  induction k with
  | zero =>
      intro c hc
      simp only [reachSet, Finset.mem_singleton] at hc
      rw [hc, dist_self, Nat.cast_zero, mul_zero]
  | succ k ih =>
      intro c hc
      rcases (reachSet_succ F ρ c₁ k c).mp hc with h | ⟨-, c', hc', hcc'⟩
      · have hk := ih c h
        push_cast
        have : 2 * ρ * (k : ℝ) ≤ 2 * ρ * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith
      · have := ih c' hc'
        have htri := dist_triangle c c' c₁
        push_cast
        linarith

theorem reachSet_stable (F : Finset ℂ) (ρ : ℝ) (c₁ : ℂ) {j : ℕ}
    (hj : reachSet F ρ c₁ (j + 1) = reachSet F ρ c₁ j) :
    ∀ n, reachSet F ρ c₁ (j + n) = reachSet F ρ c₁ j := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have e : j + (n + 1) = (j + n) + 1 := by omega
      rw [e]
      ext c
      rw [reachSet_succ, ih, ← reachSet_succ, hj]

theorem exists_reachSet_stable (F : Finset ℂ) (ρ : ℝ) {c₁ : ℂ} (hc₁ : c₁ ∈ F) :
    ∃ j ≤ F.card, reachSet F ρ c₁ (j + 1) = reachSet F ρ c₁ j := by
  have key : ∀ k, (∃ j ≤ k, reachSet F ρ c₁ (j + 1) = reachSet F ρ c₁ j) ∨
      k + 1 ≤ (reachSet F ρ c₁ k).card := by
    intro k
    induction k with
    | zero =>
        right
        simp [reachSet]
    | succ k ih =>
        rcases ih with ⟨j, hjk, hj⟩ | hcard
        · exact Or.inl ⟨j, hjk.trans (Nat.le_succ k), hj⟩
        · by_cases hst : reachSet F ρ c₁ (k + 1) = reachSet F ρ c₁ k
          · exact Or.inl ⟨k, Nat.le_succ k, hst⟩
          · right
            have hss : reachSet F ρ c₁ k ⊂ reachSet F ρ c₁ (k + 1) :=
              Finset.ssubset_iff_subset_ne.mpr ⟨reachSet_mono F ρ c₁ k, fun h => hst h.symm⟩
            have := Finset.card_lt_card hss
            omega
  rcases key F.card with h | hcard
  · exact h
  · exfalso
    have := Finset.card_le_card (reachSet_subset F ρ hc₁ F.card)
    omega

 
theorem dist_le_of_preconnected_cover {S : Set ℂ} (hS : IsPreconnected S) (F : Finset ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hcov : S ⊆ ⋃ c ∈ F, Metric.ball c ρ) {y₁ y₂ : ℂ} (h₁ : y₁ ∈ S)
    (h₂ : y₂ ∈ S) : dist y₁ y₂ ≤ 2 * ρ * (F.card + 1) := by
  obtain ⟨c₁, hc₁F, hy₁⟩ : ∃ c₁ ∈ F, y₁ ∈ Metric.ball c₁ ρ := by
    have := hcov h₁
    simp only [mem_iUnion, exists_prop] at this
    exact this
  obtain ⟨j, hjF, hj⟩ := exists_reachSet_stable F ρ hc₁F
  set R := reachSet F ρ c₁ j with hRdef
  let O₁ : Set ℂ := ⋃ c ∈ R, Metric.ball c ρ
  let O₂ : Set ℂ := ⋃ c ∈ F.filter (fun c => c ∉ R), Metric.ball c ρ
  have hO₁ : IsOpen O₁ := isOpen_biUnion fun c _ => Metric.isOpen_ball
  have hO₂ : IsOpen O₂ := isOpen_biUnion fun c _ => Metric.isOpen_ball
  have hdisj : Disjoint O₁ O₂ := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp only [O₁, O₂, mem_iUnion, exists_prop, Finset.mem_filter] at hy1 hy2
    obtain ⟨c, hcR, hyc⟩ := hy1
    obtain ⟨c', ⟨hc'F, hc'R⟩, hyc'⟩ := hy2
    apply hc'R
    have hmem : c' ∈ reachSet F ρ c₁ (j + 1) := by
      rw [reachSet_succ]
      right
      refine ⟨hc'F, c, hcR, ?_⟩
      have := dist_triangle c' y c
      rw [Metric.mem_ball] at hyc hyc'
      rw [dist_comm c' y] at this
      linarith
    rw [hj] at hmem
    exact hmem
  have hcov' : S ⊆ O₁ ∪ O₂ := by
    intro y hy
    have := hcov hy
    simp only [mem_iUnion, exists_prop] at this
    obtain ⟨c, hcF, hyc⟩ := this
    by_cases hcR : c ∈ R
    · exact Or.inl (mem_biUnion hcR hyc)
    · exact Or.inr (mem_biUnion (Finset.mem_filter.mpr ⟨hcF, hcR⟩) hyc)
  have hc₁R : c₁ ∈ R := by
    have h0 : c₁ ∈ reachSet F ρ c₁ 0 := by simp [reachSet]
    have := reachSet_stable F ρ c₁ hj
    have hmono : ∀ k, reachSet F ρ c₁ 0 ⊆ reachSet F ρ c₁ k := by
      intro k
      induction k with
      | zero => exact subset_rfl
      | succ k ih => exact ih.trans (reachSet_mono F ρ c₁ k)
    exact hmono j h0
  have hSO₁ : S ⊆ O₁ := hS.subset_left_of_subset_union hO₁ hO₂ hdisj hcov'
    ⟨y₁, h₁, mem_biUnion hc₁R hy₁⟩
  have hy₂ := hSO₁ h₂
  simp only [O₁, mem_iUnion, exists_prop] at hy₂
  obtain ⟨c₂, hc₂R, hy₂c⟩ := hy₂
  have hc₂ := dist_reachSet F hρ.le c₁ j c₂ hc₂R
  rw [Metric.mem_ball] at hy₁ hy₂c
  have htri1 := dist_triangle y₁ c₁ y₂
  have htri2 := dist_triangle c₁ c₂ y₂
  have hjle : (j : ℝ) ≤ F.card := by exact_mod_cast hjF
  rw [dist_comm c₂ c₁] at hc₂
  rw [dist_comm y₂ c₂] at hy₂c
  have hbound : 2 * ρ * (j : ℝ) ≤ 2 * ρ * F.card := by
    have : 0 ≤ 2 * ρ := by linarith
    exact mul_le_mul_of_nonneg_left hjle this
  have h1 : dist y₁ y₂ ≤ dist y₁ c₁ + (dist c₁ c₂ + dist c₂ y₂) := by linarith
  linarith

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
