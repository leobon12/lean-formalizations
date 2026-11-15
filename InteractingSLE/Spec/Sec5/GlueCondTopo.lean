/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop38Geom
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.WangWu.UnboundedComponent

/-!
# Unbounded components for a hull and for its reflection

Packet PROVE-GLUECOND. Proposition 3.8 (`LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`) compares the union mean
with the mean of a set `A₂` under the hypothesis that every component of `A₂ ∪ {Im ≤ 0}` is unbounded. On the glued
space of §4.2 the two sets are a flow-line hull `K_q` (a compact `ℍ`-hull) and the reflected counterflow hull
`R(K′_t)`, `R(z) = −1/z`, of a compact `ℍ`-hull `K′_t` that need not be connected or simple (`κ′ > 4`).

* `closure_inter_nonempty_of_isBounded` (**boundary bumping**): if `X ⊆ ℂ` is closed and preconnected and `B` is
  closed and meets `X`, every bounded component of `X ∖ B` has closure meeting `B`. Proof: otherwise a compact
  neighbourhood `Y` of the component inside `X ∖ B` is a compact Hausdorff space in which the component is the
  intersection of clopen sets; one of them misses the rim of `Y`, and is then clopen in `X`.
* `not_isBounded_lowerUnion_of_isHPHull`: for a compact `ℍ`-hull `K`, every component of `K ∪ {Im ≤ 0}` is unbounded.
* `not_isBounded_lowerUnion_image_negInv`: for a compact `ℍ`-hull `K`, every component of `R(K) ∪ {Im ≤ 0}` is
  unbounded. A component of `K` (bounded) has, by boundary bumping in `K ∪ {Im ≤ 0}`, a real point `x` in its closure:
  its image under `R` is unbounded if `x = 0`, and otherwise its closure contains the real point `R(x)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace InteractingSLE.Sec5.GlueCond

open QuantumZipper (H)
open WangWu (negInv)
open LocalSets (lowerUnion)

/-- **Boundary bumping.** If `X ⊆ ℂ` is closed and preconnected and `B` is closed and meets `X`, then every bounded
component of `X ∖ B` has closure meeting `B`. -/
theorem closure_inter_nonempty_of_isBounded {X B : Set ℂ} (hX : IsClosed X) (hXc : IsPreconnected X)
    (hB : IsClosed B) (hXB : (X ∩ B).Nonempty) {w : ℂ} (hw : w ∈ X \ B)
    (hCb : Bornology.IsBounded (connectedComponentIn (X \ B) w)) :
    (closure (connectedComponentIn (X \ B) w) ∩ B).Nonempty := by
  set C := connectedComponentIn (X \ B) w with hCdef
  by_contra hne
  have hdis : Disjoint (closure C) B := Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)
  have hK₀ : IsCompact (closure C) := hCb.isCompact_closure
  obtain ⟨δ, hδ, hδB⟩ := hK₀.exists_thickening_subset_open hB.isOpen_compl
    (fun x hx => Set.disjoint_left.1 hdis hx)
  set Y : Set ℂ := X ∩ cthickening (δ / 2) (closure C) with hYdef
  have hYc : IsCompact Y := (hK₀.cthickening (r := δ / 2)).inter_left hX
  have hYB : ∀ y ∈ Y, y ∉ B := fun y hy =>
    hδB (cthickening_subset_thickening' hδ (by linarith) _ hy.2)
  have : CompactSpace Y := isCompact_iff_compactSpace.1 hYc
  have hwC : w ∈ C := mem_connectedComponentIn hw
  have hwY : w ∈ Y := ⟨hw.1, self_subset_cthickening _ (subset_closure hwC)⟩
  set y₀ : Y := ⟨w, hwY⟩ with hy₀
  -- the component of `y₀` in `Y` lies in `C`
  have hcomp : Subtype.val '' connectedComponent y₀ ⊆ C := by
    refine (isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn).subset_connectedComponentIn
      ⟨y₀, mem_connectedComponent, rfl⟩ ?_
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y.2.1, hYB y y.2⟩
  set T : Set ℂ := thickening (δ / 2) (closure C) with hTdef
  have hCT : C ⊆ T := fun x hx => self_subset_thickening (by linarith) _ (subset_closure hx)
  -- the rim of `Y`
  set Z : Set Y := {y | (y : ℂ) ∉ T} with hZdef
  have hZc : IsCompact Z :=
    (isOpen_thickening.preimage continuous_subtype_val).isClosed_compl.isCompact
  have hZdis : Disjoint Z (⋂ s : {s : Set Y // IsClopen s ∧ y₀ ∈ s}, s.1) := by
    rw [← connectedComponent_eq_iInter_isClopen]
    refine Set.disjoint_left.2 fun y hyZ hy => hyZ ?_
    exact hCT (hcomp ⟨y, hy, rfl⟩)
  obtain ⟨u, hu⟩ := hZc.elim_finite_subfamily_closed (fun s : {s : Set Y // IsClopen s ∧ y₀ ∈ s} => s.1)
    (fun s => s.2.1.isClosed) hZdis
  set U' : Set Y := ⋂ s ∈ u, s.1 with hU'def
  have hU'clopen : IsClopen U' := isClopen_biInter_finset fun s _ => s.2.1
  have hy₀U' : y₀ ∈ U' := mem_iInter₂.2 fun s _ => s.2.2
  have hU'T : ∀ y ∈ U', (y : ℂ) ∈ T := fun y hy => by
    by_contra h
    exact Set.disjoint_left.1 hu h hy
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 hU'clopen.isOpen
  have hUc : IsClosed (Subtype.val '' U') := (hU'clopen.isClosed.isCompact.image continuous_subtype_val).isClosed
  have hsub : X ∩ (O ∩ T) ⊆ Subtype.val '' U' := by
    rintro x ⟨hxX, hxO, hxT⟩
    have hxY : x ∈ Y := ⟨hxX, thickening_subset_cthickening _ _ hxT⟩
    refine ⟨⟨x, hxY⟩, ?_, rfl⟩
    rw [← hOU]
    exact hxO
  obtain ⟨b, hbX, hbB⟩ := hXB
  have hbU : b ∉ Subtype.val '' U' := by
    rintro ⟨y, -, rfl⟩
    exact hYB y y.2 hbB
  have hwO : w ∈ O := by
    have : y₀ ∈ Subtype.val ⁻¹' O := hOU ▸ hy₀U'
    exact this
  have hcover : X ⊆ (O ∩ T) ∪ (Subtype.val '' U')ᶜ := by
    intro x hxX
    by_cases hx : x ∈ Subtype.val '' U'
    · obtain ⟨y, hy, rfl⟩ := hx
      refine Or.inl ⟨?_, hU'T y hy⟩
      have : y ∈ Subtype.val ⁻¹' O := hOU ▸ hy
      exact this
    · exact Or.inr hx
  obtain ⟨x, hxX, ⟨hxO, hxT⟩, hxU⟩ := hXc (O ∩ T) (Subtype.val '' U')ᶜ (hO.inter isOpen_thickening)
    hUc.isOpen_compl hcover ⟨w, hw.1, hwO, hU'T y₀ hy₀U'⟩ ⟨b, hbX, hbU⟩
  exact hxU (hsub ⟨hxX, hxO, hxT⟩)

/-- A compact `ℍ`-hull together with the closed lower half-plane is closed. -/
theorem isClosed_union_lowerHalf {K : Set ℂ} (hK : IsHPHull K) : IsClosed (K ∪ {z : ℂ | z.im ≤ 0}) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  rw [closure_union, (isClosed_le Complex.continuous_im continuous_const).closure_eq] at hx
  rcases hx with hx | hx
  · by_cases him : x.im ≤ 0
    · exact Or.inr him
    · left
      by_contra hxK
      have hxH : x ∈ H \ K := ⟨lt_of_not_ge him, hxK⟩
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hx _ hK.isOpen hxH
      exact hy1.2 hy2
  · exact Or.inr hx

/-- **Every component of `K ∪ {Im ≤ 0}` is unbounded** for a compact `ℍ`-hull `K`. -/
theorem not_isBounded_lowerUnion_of_isHPHull {K : Set ℂ} (hK : IsHPHull K) :
    ∀ z ∈ lowerUnion K, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion K) z) := by
  intro z hz hb
  have hpre : IsPreconnected (lowerUnion K) := hK.isPreconnected_union_lowerHalf
  rw [hpre.connectedComponentIn hz] at hb
  exact not_isBounded_lowerHalf (hb.subset subset_union_right)

theorem zero_notMem_H : (0 : ℂ) ∉ H := fun h => by
  have : (0 : ℝ) < (0 : ℂ).im := h
  simp at this

theorem continuousAt_negInv_of_ne {x : ℂ} (hx : x ≠ 0) : ContinuousAt negInv x :=
  (continuousAt_inv₀ hx).neg

theorem im_negInv_of_im_eq_zero {x : ℂ} (hx : x.im = 0) : (negInv x).im = 0 := by
  simp [negInv, Complex.inv_im, hx]

/-- **Every component of `R(K) ∪ {Im ≤ 0}` is unbounded** for a compact `ℍ`-hull `K`, `R(z) = −1/z`. -/
theorem not_isBounded_lowerUnion_image_negInv {K : Set ℂ} (hK : IsHPHull K) :
    ∀ z ∈ lowerUnion (negInv '' K),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (negInv '' K)) z) := by
  set F := lowerUnion (negInv '' K) with hFdef
  set L : Set ℂ := {z : ℂ | z.im ≤ 0} with hLdef
  have hLF : L ⊆ F := subset_union_right
  -- a component meeting `L` contains `L`
  have hcompL : ∀ z ∈ F, ∀ x ∈ connectedComponentIn F z, x ∈ L →
      ¬ Bornology.IsBounded (connectedComponentIn F z) := by
    intro z hz x hx hxL hb
    have hsub : L ⊆ connectedComponentIn F x := isPreconnected_lowerHalf.subset_connectedComponentIn hxL hLF
    rw [← connectedComponentIn_eq hx] at hsub
    exact not_isBounded_lowerHalf (hb.subset hsub)
  intro z hz
  rcases hz with ⟨w, hwK, rfl⟩ | hzL
  swap
  · exact hcompL z (Or.inr hzL) z (mem_connectedComponentIn (Or.inr hzL)) hzL
  have hwH : w ∈ H := hK.1 hwK
  set X := K ∪ L with hXdef
  have hwXB : w ∈ X \ L := ⟨Or.inl hwK, fun h => (not_le.2 (show (0 : ℝ) < w.im from hwH)) h⟩
  set C := connectedComponentIn (X \ L) w with hCdef
  have hCK : C ⊆ K := fun x hx => by
    obtain ⟨hxX, hxL⟩ := connectedComponentIn_subset _ _ hx
    rcases hxX with h | h
    · exact h
    · exact absurd h hxL
  have hCb : Bornology.IsBounded C := hK.2.1.subset hCK
  obtain ⟨x, hxC, hxL⟩ := closure_inter_nonempty_of_isBounded (isClosed_union_lowerHalf hK)
    hK.isPreconnected_union_lowerHalf (isClosed_le Complex.continuous_im continuous_const)
    ⟨0, Or.inr (show (0 : ℂ).im ≤ 0 by simp), show (0 : ℂ).im ≤ 0 by simp⟩ hwXB hCb
  -- the image of `C` is a preconnected subset of `F` through `negInv w`
  have hCH : C ⊆ H := fun y hy => hK.1 (hCK hy)
  have hP : IsPreconnected (negInv '' C) :=
    isPreconnected_connectedComponentIn.image _ fun y hy => (continuousAt_negInv_of_ne (fun h0 =>
      zero_notMem_H (h0 ▸ hCH hy))).continuousWithinAt
  have hPF : negInv '' C ⊆ F := fun y ⟨c, hc, hcy⟩ => Or.inl ⟨c, hCK hc, hcy⟩
  have hzP : negInv w ∈ negInv '' C := ⟨w, mem_connectedComponentIn hwXB, rfl⟩
  have hPcomp : negInv '' C ⊆ connectedComponentIn F (negInv w) := hP.subset_connectedComponentIn hzP hPF
  -- `x` is real
  have hxim : x.im = 0 := by
    have h1 : 0 ≤ x.im := by
      have hcl : closure C ⊆ {y : ℂ | 0 ≤ y.im} :=
        closure_minimal (fun y hy => le_of_lt (show (0 : ℝ) < y.im from hCH hy))
          (isClosed_le continuous_const Complex.continuous_im)
      exact hcl hxC
    exact le_antisymm hxL h1
  by_cases hx0 : x = 0
  · -- the image of `C` is unbounded
    intro hb
    have hPb : Bornology.IsBounded (negInv '' C) := hb.subset hPcomp
    obtain ⟨R, hR⟩ := hPb.subset_closedBall 0
    have hx0C : (0 : ℂ) ∈ closure C := hx0 ▸ hxC
    obtain ⟨c, hcC, hc⟩ := Metric.mem_closure_iff.1 hx0C (1 / (|R| + 1)) (by positivity)
    have hcH : c ∈ H := hCH hcC
    have hc0 : c ≠ 0 := fun h => zero_notMem_H (h ▸ hcH)
    have hcn : ‖c‖ < 1 / (|R| + 1) := by simpa [dist_eq_norm] using hc
    have hRc := hR ⟨c, hcC, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hRc
    have hnorm : ‖negInv c‖ = ‖c‖⁻¹ := by simp [negInv, norm_inv]
    rw [hnorm] at hRc
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have h1 : 1 / (|R| + 1) ≤ ‖c‖ := by
      rw [one_div]
      calc (|R| + 1)⁻¹ ≤ R⁻¹ ⊔ (|R| + 1)⁻¹ := le_sup_right
        _ ≤ ‖c‖ := by
          rcases le_or_gt R 0 with hR0 | hR0
          · exact absurd (hRc.trans hR0) (not_le.2 (inv_pos.2 hcpos))
          · refine sup_le ?_ ?_
            · rw [inv_le_comm₀ hR0 hcpos]; exact hRc
            · rw [inv_le_comm₀ (by positivity) hcpos]
              exact hRc.trans (by rw [abs_of_pos hR0]; linarith)
    linarith
  · -- the closure of the image of `C` contains the real point `R(x)`
    have hxcl : negInv x ∈ closure (negInv '' C) := mem_closure_image (continuousAt_negInv_of_ne hx0) hxC
    have hxL' : negInv x ∈ L := show (negInv x).im ≤ 0 from (im_negInv_of_im_eq_zero hxim).le
    have hP' : IsPreconnected (insert (negInv x) (negInv '' C)) :=
      hP.subset_closure (subset_insert _ _) (insert_subset hxcl subset_closure)
    have hP'F : insert (negInv x) (negInv '' C) ⊆ F := insert_subset (hLF hxL') hPF
    have hsub : insert (negInv x) (negInv '' C) ⊆ connectedComponentIn F (negInv w) :=
      hP'.subset_connectedComponentIn (subset_insert _ _ hzP) hP'F
    exact hcompL (negInv w) (Or.inl ⟨w, hwK, rfl⟩) (negInv x) (hsub (mem_insert _ _)) hxL'

end InteractingSLE.Sec5.GlueCond
