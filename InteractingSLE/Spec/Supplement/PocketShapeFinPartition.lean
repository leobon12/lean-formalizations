/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeFinArc

/-!
# The two connected pieces of a closed Jordan-boundary partition

PROVE-POCKETSHAPE continuation. A real parametrization of the boundary with one point
removed sends the two half-lines to the two closed pieces. Its endpoint limits recover
connectedness of both closed pieces as well as their punctured versions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.PocketShapeFin

/-- Recover one closed piece from a half-line parametrization and its endpoint limits. -/
theorem connected_piece_of_halfline {A B : Set ℂ} {a e : ℂ} (_hae : a ≠ e)
    (hAB : A ∩ B = {a, e}) {f : ℝ → ℂ} (hfc : Continuous f)
    (hfi : Function.Injective f) (hf0 : f 0 = a)
    (hfr : range f = (A ∪ B) \ {e}) (hfe : Tendsto f atTop (𝓝 e))
    (hpos : f '' Ioi 0 ⊆ A) (hneg : f '' Iio 0 ⊆ B) :
    IsPreconnected A ∧ IsPreconnected (A \ {a, e}) := by
  have hfa : ∀ x, x ≠ 0 → f x ≠ a := fun x hx he => hx (hfi (he.trans hf0.symm))
  have hfne : ∀ x, f x ≠ e := fun x => (show f x ∈ (A ∪ B) \ {e} from
    hfr ▸ mem_range_self x).2
  have heq : f '' Ioi 0 = A \ {a, e} := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨hpos ⟨x, hx, rfl⟩, fun he => by
        rcases he with he | he
        · exact hfa x (ne_of_gt hx) he
        · exact hfne x he⟩
    · intro z hz
      have hze : z ≠ e := fun he => hz.2 (Or.inr he)
      obtain ⟨x, rfl⟩ : z ∈ range f := hfr ▸ ⟨Or.inl hz.1, hze⟩
      have hx0 : x ≠ 0 := fun he => hz.2 (Or.inl (he ▸ hf0))
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · have hi : f x ∈ ({a, e} : Set ℂ) := by
          rw [← hAB]
          exact ⟨hz.1, hneg ⟨x, hx, rfl⟩⟩
        exact (hz.2 hi).elim
      · exact ⟨x, hx, rfl⟩
  have hp : IsPreconnected (f '' Ioi 0) := isPreconnected_Ioi.image _ hfc.continuousOn
  have ha_cl : a ∈ closure (f '' Ioi 0) := by
    rw [← hf0]
    apply hfc.continuousAt.continuousWithinAt.mem_closure_image
    rw [closure_Ioi]
    exact mem_Ici.2 le_rfl
  have he_cl : e ∈ closure (f '' Ioi 0) :=
    isClosed_closure.mem_of_tendsto hfe ((eventually_gt_atTop (0 : ℝ)).mono
      (fun x hx => subset_closure ⟨x, hx, rfl⟩))
  refine ⟨hp.subset_closure hpos ?_, heq ▸ hp⟩
  intro z hz
  by_cases hza : z = a
  · exact hza ▸ ha_cl
  by_cases hze : z = e
  · exact hze ▸ he_cl
  exact subset_closure (heq ▸ ⟨hz, fun he => by
    rcases he with he | he
    · exact hza he
    · exact hze he⟩)

/-- A continuous bijective real parametrization, with the same omitted-point limits at
both infinities, identifies the connected pieces of a closed two-point partition. -/
theorem connected_partition_of_real_param {A B : Set ℂ} {a e : ℂ}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∩ B = {a, e}) (hae : a ≠ e)
    (hAn : (A \ {a, e}).Nonempty) (hBn : (B \ {a, e}).Nonempty)
    {f : ℝ → ℂ} (hfc : Continuous f) (hfi : Function.Injective f) (hf0 : f 0 = a)
    (hfr : range f = (A ∪ B) \ {e})
    (hft : Tendsto f atTop (𝓝 e)) (hfb : Tendsto f atBot (𝓝 e)) :
    (IsPreconnected A ∧ IsPreconnected (A \ {a, e})) ∧
      (IsPreconnected B ∧ IsPreconnected (B \ {a, e})) := by
  have hsplit : ∀ S : Set ℝ, IsPreconnected S → (∀ x ∈ S, x ≠ 0) →
      f '' S ⊆ A ∨ f '' S ⊆ B := by
    intro S hS hS0
    refine isPreconnected_iff_subset_of_disjoint_closed.1
      (hS.image _ hfc.continuousOn) A B hA hB ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (show f x ∈ (A ∪ B) \ {e} from hfr ▸ mem_range_self x).1
    · rw [hAB, eq_empty_iff_forall_notMem]
      rintro _ ⟨⟨x, hx, rfl⟩, he | he⟩
      · exact hS0 x hx (hfi (he.trans hf0.symm))
      · exact (show f x ∈ (A ∪ B) \ {e} from hfr ▸ mem_range_self x).2 he
  have hp := hsplit (Ioi 0) isPreconnected_Ioi (fun x hx => ne_of_gt hx)
  have hn := hsplit (Iio 0) isPreconnected_Iio (fun x hx => ne_of_lt hx)
  have hcontra : ∀ D E : Set ℂ, D ∩ E = {a, e} → (E \ {a, e}).Nonempty →
      A ∪ B = D ∪ E → f '' Ioi 0 ⊆ D → f '' Iio 0 ⊆ D → False := by
    intro D E hDE ⟨z, hz⟩ hU hp hn
    have hze : z ≠ e := fun he => hz.2 (Or.inr he)
    obtain ⟨x, hfx⟩ : z ∈ range f := by
      rw [hfr, hU]
      exact ⟨Or.inr hz.1, hze⟩
    have hx0 : x ≠ 0 := fun he => hz.2 (Or.inl (hfx.symm.trans (he ▸ hf0)))
    have hxD : f x ∈ D := by
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · exact hn ⟨x, hx, rfl⟩
      · exact hp ⟨x, hx, rfl⟩
    exact hz.2 (hDE ▸ ⟨hfx ▸ hxD, hz.1⟩)
  have hswap : ∀ D E : Set ℂ, D ∩ E = {a, e} → A ∪ B = D ∪ E →
      f '' Ioi 0 ⊆ D → f '' Iio 0 ⊆ E →
      (IsPreconnected D ∧ IsPreconnected (D \ {a, e})) ∧
        (IsPreconnected E ∧ IsPreconnected (E \ {a, e})) := by
    intro D E hDE hU hp hn
    have hfr' : range f = (D ∪ E) \ {e} := by rw [hfr, hU]
    have hd := connected_piece_of_halfline hae hDE hfc hfi hf0 hfr' hft hp hn
    let g : ℝ → ℂ := fun x => f (-x)
    have hgr : range g = (E ∪ D) \ {e} := by
      rw [← union_comm D E, ← hfr']
      exact neg_surjective.range_comp f
    have hgpos : g '' Ioi 0 ⊆ E := by
      rintro _ ⟨x, hx, rfl⟩
      exact hn ⟨-x, mem_Iio.2 (neg_lt_zero.2 (mem_Ioi.1 hx)), rfl⟩
    have hgneg : g '' Iio 0 ⊆ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hp ⟨-x, mem_Ioi.2 (neg_pos.2 (mem_Iio.1 hx)), rfl⟩
    have he := connected_piece_of_halfline (f := g) hae (by rwa [inter_comm])
      (hfc.comp continuous_neg) (hfi.comp neg_injective) (by simpa only [g, neg_zero, Function.comp_def] using hf0)
      hgr (hfb.comp tendsto_neg_atTop_atBot) hgpos hgneg
    exact ⟨hd, he⟩
  rcases hp with hp | hp <;> rcases hn with hn | hn
  · exact (hcontra A B hAB hBn rfl hp hn).elim
  · exact hswap A B hAB rfl hp hn
  · exact (hswap B A (by rwa [inter_comm]) (union_comm _ _) hp hn).symm
  · exact (hcontra B A (by rwa [inter_comm]) hAn (union_comm _ _) hp hn).elim

end InteractingSLE.Theorem14.PocketShapeFin
