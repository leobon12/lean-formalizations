import QuantumZipper.Proofs.Zipper.LocLenF1FlowDet
import QuantumZipper.Proofs.Zipper.FlowRegAliveDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6b-2 (part 2): the arc of `η(U, U+S)` avoids the root images and the tip

Deterministic. For a continuous driver `W` with `W 0 = 0`, `U, S ≥ 0`, and `W_U r =
W (U + max r 0) − W U` (the driver of `zipCapDown γ U`), if no nonzero real point is swallowed
by time `U + S`:
* `sideImages_fst_le_shift`: `O⁻_{U+S}(W) ≤ O⁻_S(W_U)`;
* `sideImages_snd_le_shift`: `O⁺_S(W_U) ≤ O⁺_{U+S}(W)`;
* **`arcs_subset_compl_offSet`**: the two open arcs `(O⁻_S(W_U), 0) ∪ (0, O⁺_S(W_U))` (the images
  of the two sides of `η(U, U+S)` at time `U + S`) lie off `offSet W (U+S) = {O⁻_{U+S}, 0, O⁺_{U+S}}`.

Sheffield arXiv:1012.4797 p. 70 (the boundary arcs of `η[0,t]` are nested along the flow).
Own elementary proof: the flow property `g_{U+S} = g^{(U)}_S ∘ g_U` (`F1.isForwardSol_shift`,
Lawler, *Conformally invariant processes in the plane*, §4.1) and order preservation of the real
forward flow (`F1.isForwardSol_lt_of_lt`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace LocLen

/-- Real solutions started left of `W 0 = 0` stay negative. -/
theorem re_neg_isForwardSol_real {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ}
    (hT : 0 ≤ T) (hx : x < 0) {v : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) :
    ∀ t ∈ Icc (0 : ℝ) T, (v t).re < 0 := by
  intro t ht
  have hn := RS.isForwardSol_neg hv
  rw [show -((x : ℂ)) = ((-x : ℝ) : ℂ) by push_cast; ring] at hn
  have h := re_pos_isForwardSol_real hW.neg hT hn
    (by rw [Pi.neg_apply, hW0, neg_zero]; linarith) t ht
  simp only [Complex.neg_re] at h
  linarith

/-- **Left side images are nested**: `O⁻_{U+S}(W) ≤ O⁻_S(W_U)`. -/
theorem sideImages_fst_le_shift {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {U S : ℝ}
    (hU : 0 ≤ U) (hS : 0 ≤ S)
    (halive : ∀ x : ℝ, x < 0 → ∃ v, IsForwardSol W (x : ℂ) (U + S) v) :
    (sideImages W (U + S)).1 ≤ (sideImages (fun r => W (U + max r 0) - W U) S).1 := by
  set V : ℝ → ℝ := fun r => W (U + max r 0) - W U with hV
  have hVc : Continuous V :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hV]
  have hUS : 0 ≤ U + S := add_nonneg hU hS
  obtain ⟨L, hL⟩ := F1.exists_tendsto_fwdMap_left hW hW0 hUS
  obtain ⟨l, hl⟩ := F1.exists_tendsto_fwdMap_left hVc hV0 hS
  show limUnder (𝓝[<] (0 : ℝ)) (fun x : ℝ => (fwdMap W (U + S) x).re) ≤
    limUnder (𝓝[<] (0 : ℝ)) (fun x : ℝ => (fwdMap V S x).re)
  rw [hL.limUnder_eq, hl.limUnder_eq]
  refine le_of_tendsto hL ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : x < 0 := hx
  obtain ⟨v, hv⟩ := halive x hx
  have hmemU : U ∈ Icc (0 : ℝ) (U + S) := ⟨hU, by linarith⟩
  have hmemUS : U + S ∈ Icc (0 : ℝ) (U + S) := ⟨hUS, le_rfl⟩
  set y := (v U).re with hy
  have hvU : v U = (y : ℂ) :=
    Complex.ext (by simp [hy]) (by simp [im_isForwardSol_real hW hUS hv U hmemU])
  have hyneg : y < 0 := re_neg_isForwardSol_real hW hW0 hUS hx hv U hmemU
  have hneg : (v (U + S)).re < 0 := re_neg_isForwardSol_real hW hW0 hUS hx hv _ hmemUS
  have hsh := F1.isForwardSol_shift hU hS hv
  rw [hvU] at hsh
  rw [F1.fwdMap_eq_of_isForwardSol hv hmemUS]
  refine ge_of_tendsto hl ?_
  filter_upwards [Ioo_mem_nhdsLT hyneg] with y' hy'
  by_cases h : ∃ w, IsForwardSol V (y' : ℂ) S w
  · obtain ⟨w, hw⟩ := h
    rw [F1.fwdMap_eq_of_isForwardSol hw ⟨hS, le_rfl⟩]
    exact (F1.isForwardSol_lt_of_lt hS hy'.1 hsh hw S ⟨hS, le_rfl⟩).le
  · simp only [fwdMap, dif_neg h, Complex.zero_re]
    exact hneg.le

/-- **Right side images are nested**: `O⁺_S(W_U) ≤ O⁺_{U+S}(W)`. -/
theorem sideImages_snd_le_shift {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {U S : ℝ}
    (hU : 0 ≤ U) (hS : 0 ≤ S)
    (halive : ∀ x : ℝ, 0 < x → ∃ v, IsForwardSol W (x : ℂ) (U + S) v) :
    (sideImages (fun r => W (U + max r 0) - W U) S).2 ≤ (sideImages W (U + S)).2 := by
  set V : ℝ → ℝ := fun r => W (U + max r 0) - W U with hV
  have hVc : Continuous V :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hV0 : V 0 = 0 := by simp [hV]
  have hUS : 0 ≤ U + S := add_nonneg hU hS
  obtain ⟨R, hR⟩ := F1.exists_tendsto_fwdMap_right hW hW0 hUS
  obtain ⟨r, hr⟩ := F1.exists_tendsto_fwdMap_right hVc hV0 hS
  show limUnder (𝓝[>] (0 : ℝ)) (fun x : ℝ => (fwdMap V S x).re) ≤
    limUnder (𝓝[>] (0 : ℝ)) (fun x : ℝ => (fwdMap W (U + S) x).re)
  rw [hR.limUnder_eq, hr.limUnder_eq]
  refine ge_of_tendsto hR ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : 0 < x := hx
  obtain ⟨v, hv⟩ := halive x hx
  have hmemU : U ∈ Icc (0 : ℝ) (U + S) := ⟨hU, by linarith⟩
  have hmemUS : U + S ∈ Icc (0 : ℝ) (U + S) := ⟨hUS, le_rfl⟩
  set y := (v U).re with hy
  have hvU : v U = (y : ℂ) :=
    Complex.ext (by simp [hy]) (by simp [im_isForwardSol_real hW hUS hv U hmemU])
  have hypos : 0 < y := re_pos_isForwardSol_real hW hUS hv (by rw [hW0]; exact hx) U hmemU
  have hpos : 0 < (v (U + S)).re :=
    re_pos_isForwardSol_real hW hUS hv (by rw [hW0]; exact hx) _ hmemUS
  have hsh := F1.isForwardSol_shift hU hS hv
  rw [hvU] at hsh
  rw [F1.fwdMap_eq_of_isForwardSol hv hmemUS]
  refine le_of_tendsto hr ?_
  filter_upwards [Ioo_mem_nhdsGT hypos] with y' hy'
  by_cases h : ∃ w, IsForwardSol V (y' : ℂ) S w
  · obtain ⟨w, hw⟩ := h
    rw [F1.fwdMap_eq_of_isForwardSol hw ⟨hS, le_rfl⟩]
    exact (F1.isForwardSol_lt_of_lt hS hy'.2 hw hsh S ⟨hS, le_rfl⟩).le
  · simp only [fwdMap, dif_neg h, Complex.zero_re]
    exact hpos.le

/-- **The two open arcs of `η(U, U+S)` at time `U + S` avoid `offSet W (U+S)`.** -/
theorem arcs_subset_compl_offSet {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {U S : ℝ}
    (hU : 0 ≤ U) (hS : 0 ≤ S)
    (halive : ∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol W (x : ℂ) (U + S) v) :
    Ioo (sideImages (fun r => W (U + max r 0) - W U) S).1 0 ∪
        Ioo 0 (sideImages (fun r => W (U + max r 0) - W U) S).2 ⊆ (offSet W (U + S))ᶜ := by
  have hUS : 0 ≤ U + S := add_nonneg hU hS
  have h1 := sideImages_fst_le_shift hW hW0 hU hS fun x hx => halive x hx.ne
  have h2 := sideImages_snd_le_shift hW hW0 hU hS fun x hx => halive x hx.ne'
  have hL0 := sideImages_fst_nonpos_of_cont hW hW0 hUS
  have hR0 := sideImages_snd_nonneg_of_cont hW hW0 hUS
  rintro z hz hmem
  simp only [offSet, mem_insert_iff, mem_singleton_iff] at hmem
  rcases hz with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hmem with h | h | h <;> linarith

end LocLen
end QuantumZipper
