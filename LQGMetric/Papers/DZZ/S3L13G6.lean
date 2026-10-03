import LQGMetric.Papers.DZZ.S3L13G5

/-!
# DZZ Lemma 3.13, cell geometry VI: assembling the box sequence along a good cell sequence (P2-DZZ313G)

DZZ arXiv:1807.00422 `LBM_LGDarXiv.tex` l. 1327–1331: along a good sequence of cells `𝖢_1, …, 𝖢_{d₀}` joining
`u` and `v`, concatenate the corridors of `𝒞_j` from `x_{j−1}` to `x_j` (doors of `exists_door`, corridors of
`exists_corridor`), starting at the box of `u` and ending with an arbitrary path in `𝒞_{d₀}` to the box of `v`.
In the first cell we use `x_0 = u` (the door square at `u` lies in `(𝖢_1)_large°`, controlled by the
goodness of `u`, as in DZZ's "arbitrary sequence of boxes in `𝒞_1`"); in the last cell the goodness of `v`.

`l313_assemble`: every box `B` of the sequence lies in a cell `𝖢` with `n_B = n_𝖢 + 2k` (`s_B = ε² s_𝖢`,
`ε = 2^{-k}`) and every `z ∈ 𝕍` within `ε s_𝖢/10` of `B` has `s_{z,δ} ≥ ε s_𝖢`; the length is
`≤ d₀ · 4^{2k}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DZZ

open DyBox

variable {m : DyBox → ℝ} {δ : ℝ}

/-- A box of the sequence: inside a cell `𝖢` at level `n_𝖢 + 2k`, all points of `𝕍` within `ε s_𝖢/10`
in cells of side `≥ ε s_𝖢`. -/
def L313Safe (m : DyBox → ℝ) (δ : ℝ) (k : ℕ) (b : DyBox) : Prop :=
  ∃ C : DyBox, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧ b.n = C.n + 2 * k ∧
    ∀ z ∈ dzzV, l313Near ((2 : ℝ)⁻¹ ^ k * C.side / 10) b z →
      (2 : ℝ)⁻¹ ^ k * C.side ≤ cellSide m δ z

lemma boxAt_mem_self {N : ℕ} {v : ℂ} (hv : v ∈ dzzV) : (boxAt N v).Mem v := ⟨hv, rfl⟩

/-- The last cell: an arbitrary chain to the box of `v` (DZZ l. 1329), controlled by the goodness of `v`. -/
lemma l313_last {k : ℕ} {v : ℂ} (hv : IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) v) {C s0 : DyBox}
    (hC : IsCell m δ C) (hCv : C.Mem v) (hs0 : s0.n = C.n + 2 * k)
    (hs0C : s0.closedBox ⊆ C.closedBox) :
    ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s0 ∧ (L.getLast hL).Mem v ∧
      L.IsChain Neighbour ∧ (∀ b ∈ L, L313Safe m δ k b) ∧ L.length ≤ 4 ^ (2 * k) := by
  have hvC : v ∈ C.largeBox := closedBox_sub_largeBox' C (mem_closedBox_of_mem hCv)
  have hε1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := side_pos' C
  obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := exists_chain_in_box (show C.n ≤ C.n + 2 * k by omega)
    hs0 rfl hs0C (boxAt_sub_cell hCv (show C.n ≤ C.n + 2 * k by omega))
  refine ⟨L, hL, h1, by rw [h2]; exact boxAt_mem_self hCv.1, h3, fun b hb => ?_, by
    rwa [show C.n + 2 * k - C.n = 2 * k by omega] at h4⟩
  obtain ⟨hbn, hbC⟩ := h5 b hb
  refine ⟨C, hC, hbC, hbn, fun z hz hn => le_cellSide_of_goodPoint hv hC hvC hbC ?_ hz hn⟩
  nlinarith

/-- **Assembly along the good cell sequence `C :: l`**, entering `C` at the door point `x0` of the box
`s0`. -/
theorem l313_tail {k : ℕ} (hk : 4 ≤ k) {v : ℂ} (hv : IsGoodPoint m δ ((2 : ℝ)⁻¹ ^ k) v) :
    ∀ (l : List DyBox) (C : DyBox) (x0 : ℂ) (s0 : DyBox), IsCell m δ C → (∀ c ∈ l, IsCell m δ c) →
      IsGoodSeq ((2 : ℝ)⁻¹ ^ k) (C :: l) → ((C :: l).getLast (List.cons_ne_nil _ _)).Mem v →
      s0.n = C.n + 2 * k → s0.closedBox ⊆ C.closedBox → x0 ∈ s0.closedBox →
      (∀ z ∈ dzzV, l313Door ((2 : ℝ)⁻¹ ^ k * C.side / 2) x0 z →
        (2 : ℝ)⁻¹ ^ k * C.side ≤ cellSide m δ z) →
      ∃ L : List DyBox, ∃ hL : L ≠ [], L.head hL = s0 ∧ (L.getLast hL).Mem v ∧
        L.IsChain Neighbour ∧ (∀ b ∈ L, L313Safe m δ k b) ∧
        L.length ≤ (l.length + 1) * 4 ^ (2 * k)
  | [], C, x0, s0, hC, _, _, hlast, hs0, hs0C, _, _ => by
    obtain ⟨L, hL, h1, h2, h3, h4, h5⟩ := l313_last hv hC hlast hs0 hs0C
    exact ⟨L, hL, h1, h2, h3, h4, by simpa using h5⟩
  | C' :: l', C, x0, s0, hC, hcells, hG, hlast, hs0, hs0C, hx0, hdoor0 => by
    rw [IsGoodSeq, List.isChain_cons_cons] at hG
    obtain ⟨⟨hN, hr⟩, hG'⟩ := hG
    have hC' := hcells C' List.mem_cons_self
    obtain ⟨x, s, s', D1, D2, hss'⟩ := exists_door hC hC' hN (by omega) hr
    obtain ⟨L1, hL1, a1, a2, a3, a4, a5⟩ :=
      exists_corridor hk hs0 hs0C hx0 D1.1 D1.2.1 D1.2.2.1
    have hlast' : ((C' :: l').getLast (List.cons_ne_nil _ _)).Mem v := by
      rwa [List.getLast_cons (List.cons_ne_nil _ _)] at hlast
    obtain ⟨L2, hL2, b1, b2, b3, b4, b5⟩ := l313_tail hk hv l' C' x s' hC'
      (fun c hc => hcells c (List.mem_cons_of_mem _ hc)) hG' hlast' D2.1 D2.2.1 D2.2.2.1
      D2.2.2.2.2
    have hs := side_pos' C
    have hε1 : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine ⟨L1 ++ L2, List.append_ne_nil_of_left_ne_nil hL1 _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.head_append_of_ne_nil hL1]; exact a1
    · rw [List.getLast_append_of_ne_nil _ hL2]; exact b2
    · refine a3.append b3 fun p hp q hq => ?_
      rw [List.getLast?_eq_some_getLast hL1, a2, Option.mem_some_iff] at hp
      rw [List.head?_eq_some_head hL2, b1, Option.mem_some_iff] at hq
      rw [← hp, ← hq]; exact hss'
    · intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨hbn, hbC, hcov⟩ := a5 b hb
        refine ⟨C, hC, hbC, hbn, fun z hz hn => ?_⟩
        rcases hcov z hn with ho | hd | hd
        · obtain ⟨o1, o2, o3, o4⟩ := ho
          rw [cellSide_eq_of_ho hC hz o1.le o2 o3.le o4]; nlinarith
        · exact hdoor0 z hz hd
        · exact D1.2.2.2.2 z hz hd
      · exact b4 b hb
    · rw [List.length_append, List.length_cons]
      calc L1.length + L2.length ≤ 4 ^ (2 * k) + (l'.length + 1) * 4 ^ (2 * k) := add_le_add a4 b5
        _ = (l'.length + 1 + 1) * 4 ^ (2 * k) := by ring

end DZZ
end LQGMetric
