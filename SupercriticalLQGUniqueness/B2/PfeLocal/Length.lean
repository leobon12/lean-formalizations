import SupercriticalLQGUniqueness.B2.Iface.Statements
import LQGMetric.Papers.LM.T1_7N1

 





set_option autoImplicit false
noncomputable section

open Set LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 


theorem lsc_len_add (D : LSCMetric) (P : ℝ → ℂ) {a s b : ℝ}
    (has : a ≤ s) (hsb : s ≤ b) :
    D.len P a b = D.len P a s + D.len P s b := by
  exact (curveLength_add (D.pt ∘ P) has hsb).symm

 


theorem internal_le_len (D : LSCMetric) (Y : Set ℂ) (P : ℝ → ℂ) (a b : ℝ)
    (hP : D.IsCurve P a b) (hY : ∀ t ∈ Icc a b, P t ∈ Y) :
    D.internal Y (⟨P a, hY a ⟨le_rfl, hP.1⟩⟩,
      ⟨P b, hY b ⟨hP.1, le_rfl⟩⟩) ≤ D.len P a b := by
  unfold LSCMetric.internal
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hY <|
      iInf_le_of_le rfl <| iInf_le_of_le rfl le_rfl

 

theorem edist_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    D.1 (P a, P b) ≤ D.len P a b := by
  exact LQGMetric.MetricGeometry.edist_le_curveLength (D.pt ∘ P) hab

 


theorem edist_le_internal (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D.1 ((p.1 : ℂ), (p.2 : ℂ)) ≤ D.internal Y p := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hY => le_iInf fun ha => le_iInf fun hb => ?_
  rw [← ha, ← hb]
  exact edist_le_len D P hP.1

 



theorem sum_len_le_len (D : LSCMetric) (P : ℝ → ℂ) (a : ℝ)
    (σ τ : ℕ → ℝ) (hstart : a ≤ σ 0)
    (hseg : ∀ i, σ i ≤ τ i) (hsep : ∀ i, τ i ≤ σ (i + 1)) :
    ∀ (n : ℕ) (b : ℝ), (∀ i < n, τ i ≤ b) →
      (∑ i ∈ Finset.range n, D.len P (σ i) (τ i)) ≤ D.len P a b := by
  have hσmono : Monotone σ :=
    monotone_nat_of_le_succ (fun i => (hseg i).trans (hsep i))
  intro n
  induction n with
  | zero =>
      intro b _
      simp only [Finset.sum_range_zero]
      exact bot_le
  | succ n ih =>
      intro b hb
      have hprev : ∀ i < n, τ i ≤ σ n := by
        intro i hi
        exact (hsep i).trans (hσmono (by omega))
      have han : a ≤ σ n := hstart.trans (hσmono (Nat.zero_le n))
      calc
        (∑ i ∈ Finset.range (n+1), D.len P (σ i) (τ i))
            = (∑ i ∈ Finset.range n, D.len P (σ i) (τ i)) + D.len P (σ n) (τ n) := by
                rw [Finset.sum_range_succ]
        _ ≤ D.len P a (σ n) + D.len P (σ n) (τ n) :=
          add_le_add (ih (σ n) hprev) le_rfl
        _ = D.len P a (τ n) := by
          exact curveLength_add (D.pt ∘ P) han (hseg n)
        _ ≤ D.len P a b := by
          exact curveLength_mono (D.pt ∘ P) le_rfl
            (hb n (Nat.lt_succ_self n))

end SupercriticalLQGUniqueness.B2.PfeLocal
