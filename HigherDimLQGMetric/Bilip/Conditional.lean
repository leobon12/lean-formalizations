import HigherDimLQGMetric.Bilip.Observation
import LQGMetric.Papers.DFGPS.L2_19CI

/-!
# Conditional shell observations

Event form of the conditional-independence calculation in MA5 A17. The
general lemmas in this file do not assume the sample space is standard Borel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open LQGMetric
open LQGMetric.GM.Bilip

namespace HigherDimLQGMetric.BilipProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- Locality conditioned on a subfield implies locality conditioned on the
whole field, with any outside observations retained. -/
theorem condIndep_full_of_local {G H A B : MeasurableSpace Ω}
    (hG : G ≤ H) (hH : H ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hCI : CondIndepEv G A (H ⊔ B) P) :
    CondIndepEv H (G ⊔ A) (H ⊔ B) P := by
  have hGm : G ≤ mΩ := hG.trans hH
  have hHBm : H ⊔ B ≤ mΩ := sup_le hH hB
  have hCI' : CondIndepEv G (A ⊔ G) ((H ⊔ B) ⊔ G) P :=
    LQGMetric.DFGPS.L219.condIndepEv_sup_cond hGm hA hHBm hCI
  have hEq : (H ⊔ B) ⊔ G = H ⊔ B := sup_eq_left.mpr (hG.trans le_sup_left)
  rw [hEq] at hCI'
  refine condIndepEv_of_condExp_sup_eq hH (sup_le hGm hA) hHBm fun E hE => ?_
  have hE' : MeasurableSet[A ⊔ G] E := by
    rw [show A ⊔ G = G ⊔ A from sup_comm A G]
    exact hE
  have hM := condExp_sup_eq_of_condIndepEv hGm hHBm (sup_le hA hGm)
    hCI'.symm hE'
  rw [hEq] at hM
  have hMG : P⟦E | H⟧ =ᵐ[P] P⟦E | G⟧ :=
    LQGMetric.DFGPS.L219.condExp_sandwich hG hH hHBm
      (le_sup_left.trans (le_aeClosure _))
      (LQGMetric.integrable_indOne ((sup_le hGm hA) E hE)) hM
  have hEq₂ : (H ⊔ B) ⊔ H = H ⊔ B := sup_eq_left.mpr le_sup_left
  rw [hEq₂]
  exact hM.trans hMG.symm

/-- The conditional probability of an inside event given the full field is a
function of the shell field alone. -/
theorem condExp_full_eq_local {G H A B : MeasurableSpace Ω}
    (hG : G ≤ H) (hH : H ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hCI : CondIndepEv G A (H ⊔ B) P)
    {E : Set Ω} (hE : MeasurableSet[G ⊔ A] E) :
    P⟦E | H⟧ =ᵐ[P] P⟦E | G⟧ := by
  have hGm : G ≤ mΩ := hG.trans hH
  have hHBm : H ⊔ B ≤ mΩ := sup_le hH hB
  have hCI' : CondIndepEv G (A ⊔ G) ((H ⊔ B) ⊔ G) P :=
    LQGMetric.DFGPS.L219.condIndepEv_sup_cond hGm hA hHBm hCI
  have hEq : (H ⊔ B) ⊔ G = H ⊔ B := sup_eq_left.mpr (hG.trans le_sup_left)
  rw [hEq] at hCI'
  have hE' : MeasurableSet[A ⊔ G] E := by
    rw [show A ⊔ G = G ⊔ A from sup_comm A G]
    exact hE
  have hM := condExp_sup_eq_of_condIndepEv hGm hHBm (sup_le hA hGm)
    hCI'.symm hE'
  rw [hEq] at hM
  exact LQGMetric.DFGPS.L219.condExp_sandwich hG hH hHBm
    (le_sup_left.trans (le_aeClosure _))
    (LQGMetric.integrable_indOne ((sup_le hGm hA) E hE)) hM

/-- Finite shell events have product conditional probabilities given the whole
field when each inside observation is local and all other inside observations
are recoverable from its outside observation. -/
theorem condExp_biInter_eq_prod
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (G A B : ℕ → MeasurableSpace Ω)
    (hG : ∀ i, G i ≤ H) (hA : ∀ i, A i ≤ mΩ)
    (hB : ∀ i, B i ≤ mΩ)
    (hCI : ∀ i, CondIndepEv (G i) (A i) (H ⊔ B i) P)
    (hNest : ∀ i j, i ≠ j → A j ≤ aeClosure P (H ⊔ B i))
    (E : ℕ → Set Ω) (hE : ∀ i, MeasurableSet[G i ⊔ A i] (E i))
    (I : Finset ℕ) :
    P⟦⋂ i ∈ I, E i | H⟧ =ᵐ[P]
      fun ω => ∏ i ∈ I, (P⟦E i | H⟧) ω := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      have hbase : (⋂ i ∈ (∅ : Finset ℕ), E i) = (Set.univ : Set Ω) := by simp
      rw [hbase]
      simp only [Set.indicator_univ]
      change P[fun _ => (1 : ℝ) | H] =ᵐ[P] fun _ => 1
      rw [condExp_const hH]
  | @insert i I hi ih =>
      let F : Set Ω := ⋂ j ∈ I, E j
      have hF : MeasurableSet[aeClosure P (H ⊔ B i)] F := by
        change MeasurableSet[aeClosure P (H ⊔ B i)] (⋂ j ∈ I, E j)
        refine Finset.measurableSet_biInter I (fun j hj => ?_)
        have hjne : i ≠ j := fun heq => hi (heq ▸ hj)
        have hG' : G j ≤ aeClosure P (H ⊔ B i) :=
          (hG j).trans (le_sup_left.trans (le_aeClosure _))
        exact (sup_le hG' (hNest i j hjne)) (E j) (hE j)
      have hCIH := condIndep_full_of_local (mΩ := mΩ) P (hG i) hH
        (hA i) (hB i) (hCI i)
      have hCIext : CondIndepEv H (G i ⊔ A i)
          (aeClosure P (H ⊔ B i)) P :=
        CondIndepEv.of_le_aeClosure hCIH (le_aeClosure _) le_rfl
      have hprod := hCIext (E i) F (hE i) hF
      have hstep : P⟦⋂ j ∈ insert i I, E j | H⟧ =ᵐ[P]
          fun ω => ∏ j ∈ insert i I, (P⟦E j | H⟧) ω := by
        filter_upwards [hprod, ih] with ω hp hi'
        simp only [Finset.set_biInter_insert, Finset.prod_insert hi, F] at hp hi' ⊢
        simp only [Pi.mul_apply] at hp ⊢
        rw [hp, hi']
      exact hstep

end HigherDimLQGMetric.BilipProb
