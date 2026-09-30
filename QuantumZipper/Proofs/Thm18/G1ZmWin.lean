import QuantumZipper.Proofs.Thm18.G1ZmRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM (3): the Palm window carries boundary mass exactly `U`

`measure_g1Win_eq`: for an atomless measure `μ` on `ℝ`, finite on the side segments and of
infinite mass on the side half-line, the Palm window `{x ∈ half : μ(seg x) ≤ V}` has mass exactly
`V` (`V < ∞`). With `measure_g1Win_le` (G1ZmRed) this is the normalization of the Palm-window
integral: `U⁻¹ E ν(window) = 1`, so the limit of `U⁻¹ E ∫_window Γ(zoom) dν` is the wedge value
(Sheffield, arXiv:1012.4797, p. 70: the Palm point is "sampled uniformly from quantum measure" on
a segment of quantum length `U`). Own elementary proof (AGENT_GUIDE cost rule): continuity of the
measure from above at the right end of the window.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Zm

/-- The right-side case of `measure_g1Win_eq`. -/
theorem measure_win_right_eq (μ : Measure ℝ) {V : ℝ≥0∞} (h0 : ∀ x, μ {x} = 0)
    (hfin : ∀ x, μ (Icc 0 x) ≠ ⊤) (hinf : μ (Ioi 0) = ⊤) :
    μ {x | 0 < x ∧ μ (Icc 0 x) ≤ V} = V ∨ V = ⊤ := by
  by_cases hVt : V = ⊤
  · exact Or.inr hVt
  left
  set T := {x : ℝ | 0 < x ∧ μ (Icc 0 x) ≤ V} with hT
  have hle : μ T ≤ V := by
    have := measure_g1Win_le μ false V
    simpa [g1SideHalf, g1SideSeg] using this
  refine le_antisymm hle ?_
  -- `T` is bounded above
  have hmono : Monotone fun x : ℝ => μ (Icc 0 x) := fun a b h =>
    measure_mono (Icc_subset_Icc_right h)
  have hbig : ∃ n : ℕ, V < μ (Icc 0 (n : ℝ)) := by
    have hU : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici 0 := by
      ext x
      simp only [mem_iUnion, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨n, h, -⟩; exact h
      · intro h; obtain ⟨n, hn⟩ := exists_nat_ge x; exact ⟨n, h, hn⟩
    have hmon : Monotone fun n : ℕ => Icc (0 : ℝ) n := fun a b h =>
      Icc_subset_Icc_right (by exact_mod_cast h)
    have hsup : μ (Ici 0) = ⨆ n : ℕ, μ (Icc (0 : ℝ) n) := by
      rw [← hU]; exact hmon.measure_iUnion
    have htop : μ (Ici 0) = ⊤ := top_unique (hinf ▸ measure_mono Ioi_subset_Ici_self)
    rw [htop] at hsup
    by_contra hc
    push_neg at hc
    have : (⊤ : ℝ≥0∞) ≤ V := hsup ▸ iSup_le hc
    exact hVt (top_unique this)
  obtain ⟨N, hN⟩ := hbig
  have hTN : ∀ x ∈ T, x < N := fun x hx => by
    by_contra hc
    push_neg at hc
    exact absurd (hx.2.trans_lt hN) (not_lt.2 (hmono hc))
  -- the right end of the window
  classical
  set s : ℝ := if T.Nonempty then sSup T else 0 with hs
  have hbdd : BddAbove T := ⟨N, fun x hx => (hTN x hx).le⟩
  have hs0 : 0 ≤ s := by
    rw [hs]; split_ifs with h
    · obtain ⟨x, hx⟩ := h; exact hx.1.le.trans (le_csSup hbdd hx)
    · exact le_rfl
  have hout : ∀ n : ℕ, V < μ (Icc 0 (s + 1 / ((n : ℝ) + 1))) := by
    intro n
    have hpos : 0 < s + 1 / ((n : ℝ) + 1) := by positivity
    by_contra hc
    push_neg at hc
    have hmem : s + 1 / ((n : ℝ) + 1) ∈ T := ⟨hpos, hc⟩
    have hne : T.Nonempty := ⟨_, hmem⟩
    have h2 := le_csSup hbdd hmem
    have hsT : s = sSup T := by rw [hs, if_pos hne]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [h2, hsT]
  have hinter : (⋂ n : ℕ, Icc (0 : ℝ) (s + 1 / ((n : ℝ) + 1))) = Icc 0 s := by
    ext x
    simp only [mem_iInter, mem_Icc]
    constructor
    · intro h
      refine ⟨(h 0).1, le_of_forall_pos_lt_add fun e he => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt he
      exact lt_of_le_of_lt (h n).2 (by linarith)
    · rintro ⟨h1, h2⟩ n
      exact ⟨h1, h2.trans (le_add_of_nonneg_right (by positivity))⟩
  have hanti : Antitone fun n : ℕ => Icc (0 : ℝ) (s + 1 / ((n : ℝ) + 1)) := by
    intro a b hab
    refine Icc_subset_Icc_right ((add_le_add_iff_left s).2 ?_)
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hVs : V ≤ μ (Icc 0 s) := by
    rw [← hinter, hanti.measure_iInter (fun n => measurableSet_Icc.nullMeasurableSet)
      ⟨0, hfin _⟩]
    exact le_iInf fun n => (hout n).le
  -- `(0, s) ⊆ T`
  have hsub : Ioo 0 s ⊆ T := by
    intro y hy
    have hne : T.Nonempty := by
      by_contra hc
      rw [hs, if_neg hc] at hy
      exact absurd hy.2 (not_lt.2 hy.1.le)
    rw [hs, if_pos hne] at hy
    obtain ⟨z, hz, hyz⟩ := exists_lt_of_lt_csSup hne hy.2
    exact ⟨hy.1, (hmono hyz.le).trans hz.2⟩
  calc V ≤ μ (Icc 0 s) := hVs
    _ ≤ μ (Ioo 0 s ∪ {0} ∪ {s}) := measure_mono fun x hx => by
        rcases eq_or_lt_of_le hx.1 with h | h
        · exact Or.inl (Or.inr h.symm)
        · rcases eq_or_lt_of_le hx.2 with h' | h'
          · exact Or.inr h'
          · exact Or.inl (Or.inl ⟨h, h'⟩)
    _ ≤ μ (Ioo 0 s) + μ {0} + μ {s} := (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ = μ (Ioo 0 s) := by rw [h0, h0, add_zero, add_zero]
    _ ≤ μ T := measure_mono hsub

/-- **The Palm window has boundary mass exactly `V`.** -/
theorem measure_g1Win_eq (μ : Measure ℝ) (left : Bool) {V : ℝ≥0∞} (hV : V ≠ ⊤)
    (h0 : ∀ x, μ {x} = 0) (hfin : ∀ x, μ (g1SideSeg left x) ≠ ⊤)
    (hinf : μ (g1SideHalf left) = ⊤) :
    μ {x | x ∈ g1SideHalf left ∧ μ (g1SideSeg left x) ≤ V} = V := by
  cases left
  · have h := measure_win_right_eq μ (V := V) h0 (by simpa [g1SideSeg] using hfin)
      (by simpa [g1SideHalf] using hinf)
    simpa [g1SideHalf, g1SideSeg, hV] using h
  · set e : ℝ ≃ᵐ ℝ := MeasurableEquiv.neg ℝ
    set μ' : Measure ℝ := μ.map e
    have hmap : ∀ S : Set ℝ, μ' S = μ (Neg.neg ⁻¹' S) := fun S => e.map_apply S
    have hseg : ∀ x, μ' (Icc 0 x) = μ (Icc (-x) 0) := fun x => by
      rw [hmap]; congr 1; ext t; simp
    have h := measure_win_right_eq μ' (V := V) (fun x => by rw [hmap]; simpa using h0 (-x))
      (fun x => by rw [hseg]; simpa [g1SideSeg] using hfin (-x))
      (by rw [hmap]; simpa [g1SideHalf] using hinf)
    rcases h with h | h
    · rw [hmap] at h
      refine Eq.trans ?_ h
      congr 1
      ext x
      simp only [g1SideHalf, g1SideSeg, if_true, mem_setOf_eq, mem_Iio, mem_preimage, hseg,
        neg_neg, Left.neg_pos_iff]
    · exact absurd h hV

end G1Zm
end Thm18Asm
end QuantumZipper
