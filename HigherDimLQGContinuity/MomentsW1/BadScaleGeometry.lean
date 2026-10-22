import HigherDimLQGMetric.DGZ.Sec41Config

/-! # Fine-field bad-scale geometry -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Relation

namespace HigherDimLQGContinuity

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLQGMetric.DGZ

/-- A coarse site is nice when it is good and its neighboring fine sites are good. -/
def wnNice {d : ℕ} (O₁ O₂ : Set (Zd d)) : Set (Zd d) :=
  {y | y ∈ O₁ ∧ ∀ z, WithinInf 1 z (2 • y) → z ∈ O₂}

private theorem wnNice_coarse {d : ℕ} {O₁ O₂ : Set (Zd d)} :
    wnNice O₁ O₂ ⊆ O₁ := fun _ hy => hy.1

private theorem wnNice_fine {d : ℕ} {O₁ O₂ : Set (Zd d)}
    {y : Zd d} (hy : y ∈ wnNice O₁ O₂) : 2 • y ∈ O₂ :=
  hy.2 _ (withinInf_refl (by norm_num) _)

private theorem wnNice_mid {d : ℕ} {O₁ O₂ : Set (Zd d)}
    {y y' : Zd d} (hy : y ∈ wnNice O₁ O₂) (hyy' : LAdj y y') : y + y' ∈ O₂ := by
  apply hy.2
  intro i
  have h := hyy'.withinInf i
  rw [Pi.add_apply, two_smul_apply]
  rw [abs_le] at h ⊢
  omega

/-- A small rough-site configuration has a nearby site free at both adjacent scales.
This uses the certified hole lemma and the refinement of coarse lattice paths. -/
theorem wnBadScale_free_of_smallClusters {d : ℕ} (hd : 2 ≤ d)
    {O₁ O₂ : Set (Zd d)} {D' : ℕ} {R : ℤ}
    (hsmall : SmallClusters (wnNice O₁ O₂) D')
    (hN : ∀ y : Zd d, y ∉ wnNice O₁ O₂ → WithinInf R y 0)
    (hO₁ : ∀ y : Zd d, y ∉ O₁ → WithinInf R y 0)
    (hO₂ : ∀ y : Zd d, y ∉ O₂ → WithinInf R y 0)
    (hR : 0 ≤ R) (x : Zd d) :
    ∃ y : Zd d, WithinInf (2 * (D' : ℤ) + 3) x (2 • y) ∧
      FreeSite O₂ (2 • y) ∧ FreeSite O₁ y := by
  let x' : Zd d := fun i => x i / 2
  obtain ⟨y, hyx', hyN⟩ := holeLemma d hd (wnNice O₁ O₂) D' hsmall x'
  let v : Zd d := fun _ => R + 1
  have hvN : ¬ WithinInf R v 0 := by
    intro h
    have h0 := h ⟨0, by omega⟩
    simp only [v, Pi.zero_apply, sub_zero, abs_le] at h0
    omega
  have hpath : ReflTransGen (StepIn (wnNice O₁ O₂) LAdj) y v :=
    freeToInfinity d hd (wnNice O₁ O₂) D' hsmall R hN y v hyN hvN
  refine ⟨y, ?_, ?_, ?_⟩
  · intro i
    have h1 := hyx' i
    rw [two_smul_apply]
    simp only [x'] at h1
    rw [abs_le] at h1 ⊢
    omega
  · have hpath' : ReflTransGen (StepIn O₂ LAdj) (2 • y) (2 • v) :=
      reflTransGen_two_smul (fun y hy => wnNice_fine hy)
        (fun y y' hy _ h => wnNice_mid hy h) hpath
    have hvO₂ : ¬ WithinInf R (2 • v) 0 := by
      intro h
      have h0 := h ⟨0, by omega⟩
      simp only [two_smul_apply, v, Pi.zero_apply, sub_zero, abs_le] at h0
      omega
    exact freeSite_of_reflTransGen hd hO₂ hvO₂ hpath'
  · have hpath' : ReflTransGen (StepIn O₁ LAdj) y v :=
      reflTransGen_stepIn_mono wnNice_coarse hpath
    exact freeSite_of_reflTransGen hd hO₁ hvN hpath'

end HigherDimLQGContinuity
