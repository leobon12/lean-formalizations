import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore.Section4Counting
import LQGMetric.Papers.DFGPS.P4_1StepCross




 





set_option autoImplicit false
noncomputable section

open Set Metric Finset
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery

 


theorem finite_completed_excursions {P : ℝ → ℂ} {O F : Set ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hP : ContinuousOn P (Icc 0 T))
    (hO : IsOpen O) (hFclosed : IsClosed F) (hFcompact : IsCompact F)
    (hFO : F ⊆ O) (h0 : P 0 ∉ O) (hTOut : P T ∉ O) :
    let a : ℝ → ℝ := fun q => sSup {u ∈ Icc 0 q | P u ∉ O}
    let b : ℝ → ℝ := fun q => sInf {u ∈ Icc q T | P u ∉ O}
    let active : Set ℝ := {q | q ∈ Ioo 0 T ∧ P q ∈ O ∧
      ({u ∈ Icc (a q) (b q) | P u ∈ F}).Nonempty}
    {e : ℝ × ℝ × ℝ × ℝ | ∃ q ∈ active,
      e = (a q, b q,
        sInf {u ∈ Icc (a q) (b q) | P u ∈ F},
        sSup {u ∈ Icc (a q) (b q) | P u ∈ F})}.Finite := by
  have hdisj : Disjoint F Oᶜ := Set.disjoint_left.mpr (by
    intro x hx hy
    exact hy (hFO hx))
  obtain ⟨ρ, hρ, hsep⟩ :=
    exists_pos_forall_lt_edist hFcompact hO.isClosed_compl hdisj
  have hρreal : (0 : ℝ) < ρ := hρ
  have hsepReal : ∀ x ∈ F, ∀ y ∈ Oᶜ, (ρ : ℝ) ≤ dist x y := by
    intro x hx y hy
    have h := hsep x hx y hy
    have h' : ENNReal.ofReal (ρ : ℝ) < ENNReal.ofReal (dist x y) := by
      simpa only [edist_dist, ENNReal.coe_nnreal_eq] using h
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hρreal.le).mp h')
  have hclosure : closure F ⊆ O := by
    simpa only [hFclosed.closure_eq] using hFO
  simpa only [hFclosed.closure_eq] using
    (Toolkit.PlanarSeparation.finiteCanonicalExcursionTuples hT hP hO h0 hTOut
      hclosure hρreal (by
        intro x hx y hy
        exact hsepReal x (by simpa only [hFclosed.closure_eq] using hx) y hy)
      (V := F))

 

theorem ball_segments_disjoint_times {ι : Type*} (S : Finset ι)
    (P : ℝ → ℂ) (z : ι → ℂ) (r s t : ι → ℝ)
    (hball : ∀ i ∈ S, ∀ u ∈ Icc (s i) (t i), P u ∈ ball (z i) (r i))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (ball (z i) (r i)) (ball (z j) (r j)))
    (hst : ∀ i ∈ S, s i ≤ t i) :
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i < s j ∨ t j < s i := by
  intro i hi j hj hij
  by_contra hc
  push Not at hc
  have hu_i : max (s i) (s j) ∈ Icc (s i) (t i) :=
    ⟨le_max_left _ _, max_le (hst i hi) hc.1⟩
  have hu_j : max (s i) (s j) ∈ Icc (s j) (t j) :=
    ⟨le_max_right _ _, max_le hc.2 (hst j hj)⟩
  exact Set.disjoint_left.mp (hdisj i hi j hj hij)
    (hball i hi _ hu_i) (hball j hj _ hu_j)

 

theorem ball_segments_length_sum_le {ι : Type*} (D : LSCMetric)
    (S : Finset ι) (P : ℝ → ℂ) (z : ι → ℂ) (r s t : ι → ℝ)
    {a b : ℝ}
    (hball : ∀ i ∈ S, ∀ u ∈ Icc (s i) (t i), P u ∈ ball (z i) (r i))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (ball (z i) (r i)) (ball (z j) (r j)))
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hab : ∀ i ∈ S, a ≤ s i ∧ t i ≤ b) :
    ∑ i ∈ S, D.len P (s i) (t i) ≤ D.len P a b := by
  have htimes := ball_segments_disjoint_times S P z r s t hball hdisj hst
  exact LQGMetric.DFGPS.P41.sum_curveLength_le
    (D.pt ∘ P) S s t hst htimes a b hab

 
theorem disjoint_intervals_sum_le {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      t i < s j ∨ t j < s i) :
    ∀ a b : ℝ, a ≤ b →
      (∀ i ∈ S, a ≤ s i ∧ t i ≤ b) →
      ∑ i ∈ S, (t i - s i) ≤ b - a := by
  classical
  induction S using Finset.induction_on_max_value t with
  | empty =>
      intro a b hab _
      simp only [sum_empty]
      linarith
  | insert i S hi hmax ih =>
      intro a b hab hwithin
      have hS : ∀ j ∈ S, t j < s i := by
        intro j hj
        have hne : i ≠ j := fun h => hi (h ▸ hj)
        rcases hdisj i (mem_insert_self _ _) j (mem_insert_of_mem hj) hne with h | h
        · have hjst := hst j (mem_insert_of_mem hj)
          have hjmax := hmax j hj
          linarith
        · exact h
      have hwithinS : ∀ j ∈ S, a ≤ s j ∧ t j ≤ s i := by
        intro j hj
        exact ⟨(hwithin j (mem_insert_of_mem hj)).1, (hS j hj).le⟩
      have hai := hwithin i (mem_insert_self _ _)
      have ih' := ih (fun j hj => hst j (mem_insert_of_mem hj))
        (fun j hj k hk hjk => hdisj j (mem_insert_of_mem hj)
          k (mem_insert_of_mem hk) hjk) a (s i) hai.1
        hwithinS
      rw [sum_insert hi]
      linarith

 

theorem ball_segments_card_charge {ι : Type*} (S : Finset ι)
    (P : ℝ → ℂ) (z : ι → ℂ) (r s t : ι → ℝ)
    {a b c : ℝ} (hab : a ≤ b)
    (hball : ∀ i ∈ S, ∀ u ∈ Icc (s i) (t i), P u ∈ ball (z i) (r i))
    (hdisj : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      Disjoint (ball (z i) (r i)) (ball (z j) (r j)))
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hwithin : ∀ i ∈ S, a ≤ s i ∧ t i ≤ b)
    (hcharge : ∀ i ∈ S, c ≤ t i - s i) :
    c * (S.card : ℝ) ≤ b - a := by
  have htimes := ball_segments_disjoint_times S P z r s t hball hdisj hst
  have hsum := disjoint_intervals_sum_le S s t hst htimes a b hab hwithin
  have hpoint : ∑ i ∈ S, c ≤ ∑ i ∈ S, (t i - s i) :=
    sum_le_sum (fun i hi => hcharge i hi)
  have h := hpoint.trans hsum
  simp only [sum_const, nsmul_eq_mul] at h
  nlinarith


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery
