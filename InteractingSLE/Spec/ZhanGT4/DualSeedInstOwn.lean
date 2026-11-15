/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedInstD9
import InteractingSLE.Spec.ZhanGT4.DualA1Left

/-!
# Uniform own-map estimates in the opposite seeded view

Packet PROVE-ZHAN-GT4-A22. The own-map estimates do not depend on the
marks. We specialize the existing protected left-view theorem to no marks.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
namespace InteractingSLE.ZhanGT4
open QuantumZipper (fwdMap fwdHull)

/-- Translation conjugates the full enclosure image as well as hull images. -/
theorem frzChart_image_transl (W : ℝ → ℝ) (c s : ℝ) (E : Set ℂ) :
    frzChart (fun u => W u - c) s '' transl (-c) E =
      transl (-c) (frzChart W s '' E) := by
  unfold transl
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  simp only [frzChart_sub_const, ofReal_neg, neg_add_cancel_right]
  ring_nf

/-- The protected point supplies the opposite own-map clearance and
derivative lower bound, independently of all integrated seed accesses. -/
theorem exists_seedTOwn_bounds_of_enclosures {H₁ H₂ : Set ℂ} {δ p q d : ℝ}
    (hp : A1SeedField.IsProtectedPair H₁ H₂ δ p q d) (Tm : ℝ) :
    ∃ r a₀ : ℝ, 0 < r ∧ 0 < a₀ ∧
      ∀ (W₁ W₂ : ℝ → ℝ) (S T s : ℝ) (a U : ℝ → ℝ),
        Continuous W₁ → Continuous W₂ → W₁ 0 = 0 → W₂ 0 = p →
        0 < S → s ∈ Ioc (0 : ℝ) S → S ≤ Tm → T ≤ Tm →
        fwdHull W₁ S ⊆ H₁ → fwdHull W₂ T ⊆ H₂ →
        OwnData (fun u => W₂ u - p) (fwdHull (fun u => W₁ u - p) s)
          (frzChart (fun u => W₁ u - p) s) T a U →
        (∀ t ∈ Icc (0 : ℝ) T, Disjoint (ball ((W₂ t - p : ℝ) : ℂ) r)
          (frzChart (fun u => W₂ u - p) t '' fwdHull (fun u => W₁ u - p) s)) ∧
        ∀ t ∈ Icc (0 : ℝ) T,
          a₀ ≤ frzA (fun u => W₂ u - p) U a (frzChart (fun u => W₁ u - p) s) 1 t := by
  have hsep : ∀ x ∈ H₁, ∀ y ∈ H₂, 2 * δ ≤ ‖x - y‖ := by
    intro x hx y hy
    rw [norm_sub_rev]
    exact hp.sep y hy x hx
  have hprot : Disjoint (ball ((q - p : ℝ) : ℂ) (2 * d))
      (transl (-p) H₂ ∪ transl (-p) H₁) := by
    have hh := disjoint_ball_transl hp.prot (-p)
    simpa only [transl, Set.image_union, sub_eq_add_neg, union_comm] using hh
  obtain ⟨r, a₀, γ, Γ, L, hr, ha, _, hb⟩ := exists_twoCurveD9_left
    (isHPHull_transl hp.hull₂ (-p)) (isHPHull_transl hp.hull₁ (-p)) hp.sep_pos
    (sep_transl hsep (-p)) hp.rad_pos (sub_neg.2 hp.prot_lt) hprot
    (p := fun m : Fin 0 => Fin.elim0 m) (fun m => Fin.elim0 m)
    (fun i => Fin.elim0 i) Tm
  refine ⟨r, a₀, hr, ha, ?_⟩
  intro W₁ W₂ S T s a U hW₁ hW₂ h01 h02 hS hs hSm hTm hK₁ hK₂ ho
  have hsrc : ((((fun u => W₁ u - p) 0) : ℝ) : ℂ) ∈ closure (transl (-p) H₁) := by
    have hh := mem_closure_transl (closure_mono hK₁ (start_mem_closure_fwdHull hW₁ hS)) (-p)
    simpa only [ofReal_sub, ofReal_neg, sub_eq_add_neg, ofReal_add] using hh
  have hq : (fun u => W₁ u - p) 0 < q - p := by
    change W₁ 0 - p < q - p
    rw [h01]
    linarith [hp.prot_pos]
  have hb' := hb (fun u => W₂ u - p) (fun u => W₁ u - p) s T a U 1
    (fun m : Fin 0 => Fin.elim0 m) ho (hW₁.sub continuous_const) hsrc hq hs.1
    (hs.2.trans hSm) hTm (fwdHull_sub_const_subset hK₂)
    (fwdHull_sub_const_subset (((QuantumZipper.fwdHull_mono).1 hs.2).trans hK₁))
  exact ⟨hb'.d9.clr, hb'.d9.A1⟩

end InteractingSLE.ZhanGT4
