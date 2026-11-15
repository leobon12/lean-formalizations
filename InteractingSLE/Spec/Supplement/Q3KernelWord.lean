/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3KernelConfig
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalFlow
import InteractingSLE.Spec.Supplement.GW1ActiveWord

/-!
# The side word and the flowed word of a force word with flowed marks

Packet PROVE-Q3-REL2, item (A)4 of `planning/handoffs/PROVE-Q3-REL.md` §4.1. `IsRelConfigOff` asks that the
counterflow word at `t` and the relative word at `u` be **side words** (`BHMean.IsSideWord`): at every real point
`x ≠ 0` off the jump set whose inverse-map landing point lies on the closed hull, the word is `λ` (`x > 0`) or
`−λ` (`x < 0`). For the force boundary data of marks lying outside the hull image `[a_L, a_R]` (every mark
flowed by the real Loewner flow from a nonnegative, resp. nonpositive, position does), this holds with `λ = π/√κ`:

* `le_chartAR_of_mem_closure`, `chartAL_le_of_mem_closure`: a real point whose landing point lies on the closed hull is
  in `[a_L, a_R]` (`RelTrans.extendFrom_notMem_closure_of_chartAR_lt` and its left twin);
* **`isSideWord_forceBoundaryData`**: the side-word clause for marks right of `a_R` and left of `a_L` that lie in the
  jump set;
* **`isSideWord_forceBoundaryData_markPos`**: the same for the flowed marks `markPos W u xR`, `markPosL W u xL` of
  nonnegative, resp. nonpositive, initial positions (`markPos W u 0 = a_R`, monotonicity);
* `markPos_le_iff_of_alive`, **`isFlowedWord_forceBoundaryData_markPos`** (`BHMean.IsFlowedWord`): off the hull image
  a real point `x` is the centred image of an alive point `y` (`F̄_u(x) = y`), `markPos W u y = x`, and monotonicity of
  the flowed marks transports the counts of marks left/right of `x` to those of `y`; inside the hull image the
  landing point lies on the closed hull (`RelTrans.Icc_subset_hullImage`).

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Supp8.Q3Kernel

open WangWu (chartAL chartAR)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {u : ℝ}

theorem le_chartAR_of_mem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u)
    {x : ℝ} (hx : extendFrom H (fwdMapInv W u) (x : ℂ) ∈ closure (fwdHull W u)) : x ≤ chartAR W u :=
  not_lt.1 fun h => RelTrans.extendFrom_notMem_closure_of_chartAR_lt hη hW hW0 hu h hx

theorem chartAL_le_of_mem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u)
    {x : ℝ} (hx : extendFrom H (fwdMapInv W u) (x : ℂ) ∈ closure (fwdHull W u)) : chartAL W u ≤ x :=
  not_lt.1 fun h => RelTrans.extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hu h hx

/-- **The side word of a force word whose marks lie outside the hull image** (`λ = π/√κ`). If every right mark lies at
or right of `a_R`, every left mark at or left of `a_L`, and all marks lie in the jump set `S`, then the force boundary
data is a side word for the chain at time `u`. -/
theorem isSideWord_forceBoundaryData (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u)
    (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {pL : Fin nL → ℝ} {pR : Fin nR → ℝ}
    (hpL : ∀ i, pL i ≤ chartAL W u) (hpR : ∀ j, chartAR W u ≤ pR j) {S : Finset ℝ} (hSL : ∀ i, pL i ∈ S)
    (hSR : ∀ j, pR j ∈ S) :
    BHMean.IsSideWord (forceBoundaryData κ ρL ρR pL pR) S (fwdMapInv W u) (fwdHull W u) (Real.pi / Real.sqrt κ) := by
  intro x hxS hx0 hxK
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hxL := chartAL_le_of_mem_closure hη hW hW0 hu hxK
    have hempty : Finset.univ.filter (fun i => x < pL i) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun i _ hi => ?_
      have h1 : pL i ≤ x := (hpL i).trans hxL
      exact absurd (le_antisymm h1 hi.le ▸ hSL i) hxS
    simp only [forceBoundaryData, hneg, ↓reduceIte, hempty, Finset.sum_empty, add_zero, mul_one,
      not_lt.2 hneg.le]
  · have hxR := le_chartAR_of_mem_closure hη hW hW0 hu hxK
    have hempty : Finset.univ.filter (fun j => pR j ≤ x) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun j _ hj => ?_
      have h1 : x ≤ pR j := hxR.trans (hpR j)
      exact absurd (le_antisymm hj h1 ▸ hSR j) hxS
    simp only [forceBoundaryData, not_lt.2 hpos.le, ↓reduceIte, hempty, Finset.sum_empty, add_zero, mul_one, hpos]

/-- **The side word of a force word with flowed marks.** For initial positions `xL ≤ 0 ≤ xR`, the force boundary data
of the flowed marks `markPosL W u xL`, `markPos W u xR` is a side word at time `u` (for any finite jump set containing
the flowed marks). -/
theorem isSideWord_forceBoundaryData_markPos (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hu : 0 ≤ u) (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {S : Finset ℝ}
    (hSL : ∀ i, Exist.StagedLaw.markPosL W u (xL i) ∈ S) (hSR : ∀ j, Exist.StagedLaw.markPos W u (xR j) ∈ S) :
    BHMean.IsSideWord (forceBoundaryData κ ρL ρR (fun i => Exist.StagedLaw.markPosL W u (xL i))
      (fun j => Exist.StagedLaw.markPos W u (xR j))) S (fwdMapInv W u) (fwdHull W u) (Real.pi / Real.sqrt κ) := by
  refine isSideWord_forceBoundaryData hη hW hW0 hu κ ρL ρR (fun i => ?_) (fun j => ?_) hSL hSR
  · rw [← Sec5.CrossCond.StagedFinal.markPosL_zero_eq_chartAL hW hW0 hu]
    exact Theorem14.GW1W.markPosL_mono hW hW0 hu le_rfl (hxL i)
  · rw [← Sec5.CrossCond.StagedFinal.markPos_zero_eq_chartAR hW hW0 hu]
    exact Theorem14.GW1W.markPos_mono hW hW0 hu le_rfl (hxR j)

/-! ### The flowed word -/

open MartChar.RealFlow in
/-- **Ordering of flowed marks against an alive point.** If `r > 0` is alive at `u` with centred image `x`, then for a
nonnegative initial position `a` whose flowed mark is not `x`: `markPos W u a ≤ x ↔ a ≤ r`. -/
theorem markPos_le_iff_of_alive (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) {r x a : ℝ} (hr0 : 0 < r)
    (hv : QuantumZipper.IsForwardSol W (r : ℂ) u (fun s => (cflow W r s : ℂ))) (hc : cflow W r u = x) (ha : 0 ≤ a)
    (hax : Exist.StagedLaw.markPos W u a ≠ x) : Exist.StagedLaw.markPos W u a ≤ x ↔ a ≤ r := by
  have hmr : Exist.StagedLaw.markPos W u r = x := by
    rw [Exist.StagedLaw.markPos_eq hW hW0 hu (Exist.StagedLaw.isMark_of_isForwardSol hW hW0 hr0 hu hv)]
    simpa using hc
  constructor
  · intro hle
    by_contra hlt
    push Not at hlt
    have h1 : x ≤ Exist.StagedLaw.markPos W u a := hmr ▸ Theorem14.GW1W.markPos_mono hW hW0 hu hr0.le hlt.le
    exact hax (le_antisymm hle h1)
  · intro hle
    exact hmr ▸ Theorem14.GW1W.markPos_mono hW hW0 hu ha hle

open MartChar.RealFlow in
/-- **The flowed word of a force word with flowed marks** (`u > 0`). For initial positions `xL ≤ 0 ≤ xR` in the jump
set `S₀` (the left ones suffice), the force boundary data of the flowed marks is the flowed word of the initial
force boundary data, for every finite jump set `S` containing `0` and the flowed marks: at a real point `x ∉ S`
landing off the closed hull at `y` (with `y ∉ S₀`), the flowed word at `x` is the initial word at `y`. -/
theorem isFlowedWord_forceBoundaryData_markPos (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hu : 0 < u) (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {S S₀ : Finset ℝ} (h0S : (0 : ℝ) ∈ S)
    (hSL : ∀ i, Exist.StagedLaw.markPosL W u (xL i) ∈ S) (hSR : ∀ j, Exist.StagedLaw.markPos W u (xR j) ∈ S)
    (hS₀L : ∀ i, xL i ∈ S₀) :
    BHMean.IsFlowedWord (forceBoundaryData κ ρL ρR (fun i => Exist.StagedLaw.markPosL W u (xL i))
      (fun j => Exist.StagedLaw.markPos W u (xR j))) (forceBoundaryData κ ρL ρR xL xR) S S₀ (fwdMapInv W u)
      (fwdHull W u) := by
  intro x hxS hxK hyS
  by_cases hR : chartAR W u < x
  · have hM : rightImg W 0 u < x + W u := by rw [WangWu.chartAR] at hR; linarith
    obtain ⟨r, hr0, hal, hg⟩ := Restart.RetAux79.exists_alive_gImg_eq hW hu.le hM
    have hv := WangWu.isForwardSol_of_alive hW hal
    have hc : cflow W r u = x := by simp only [gImg] at hg; linarith
    have hland := Sec5.CrossRestart.extendFrom_eq_of_isForwardSol_real hη hW hW0 hu.le hv
    simp only [hc] at hland
    rw [hland, Complex.ofReal_re] at hyS ⊢
    have hx0 : ¬ x < 0 := by
      have := WangWu.chartAR_nonneg hW hu.le
      linarith
    have hr0' : ¬ r < 0 := not_lt.2 hr0.le
    have hfilt : Finset.univ.filter (fun j => Exist.StagedLaw.markPos W u (xR j) ≤ x) =
        Finset.univ.filter (fun j => xR j ≤ r) := by
      refine Finset.filter_congr fun j _ => ?_
      have hk := markPos_le_iff_of_alive hW hW0 hu.le hr0 hv hc (hxR j) (fun h => hxS (h ▸ hSR j))
      rw [hk]
    simp only [forceBoundaryData, hx0, hr0', ↓reduceIte, hfilt]
  · by_cases hL : x < chartAL W u
    · have hM : rightImg (fun s => -W s) 0 u < -x - W u := by rw [WangWu.chartAL] at hL; linarith
      obtain ⟨y, hy0, hal, hg⟩ := Restart.RetAux79.exists_alive_gImg_eq hW.neg hu.le hM
      have hvn := WangWu.isForwardSol_of_alive hW.neg hal
      have hv := WangWu.isForwardSol_neg_of_alive hW hal
      have hv' : QuantumZipper.IsForwardSol W ((-y : ℝ) : ℂ) u (fun s => -(cflow (fun s => -W s) y s : ℂ)) := by
        rw [Complex.ofReal_neg]; exact hv
      have hg' : -W u + cflow (fun s => -W s) y u = -x - W u := hg
      have hc : cflow (fun s => -W s) y u = -x := by linarith
      have hland := Sec5.CrossRestart.extendFrom_eq_of_isForwardSol_real hη hW hW0 hu.le hv'
      simp only [hc, Complex.ofReal_neg, neg_neg] at hland
      rw [hland, Complex.neg_re, Complex.ofReal_re] at hyS ⊢
      have hx0 : x < 0 := lt_of_lt_of_le hL (WangWu.chartAL_nonpos hW hu.le)
      have hy0' : -y < 0 := by linarith
      have hW'0 : (fun s => -W s) 0 = 0 := by simp [hW0]
      have hfilt : Finset.univ.filter (fun i => x < Exist.StagedLaw.markPosL W u (xL i)) =
          Finset.univ.filter (fun i => -y < xL i) := by
        refine Finset.filter_congr fun i _ => ?_
        have hyi : xL i ≠ -y := fun h => hyS (h ▸ hS₀L i)
        have hmx : Exist.StagedLaw.markPos (fun s => -W s) u (-xL i) ≠ -x := fun h => hxS (by
          have : Exist.StagedLaw.markPosL W u (xL i) = x := by
            unfold Exist.StagedLaw.markPosL; rw [h, neg_neg]
          exact this ▸ hSL i)
        have hk := markPos_le_iff_of_alive (W := fun s => -W s) hW.neg hW'0 hu.le hy0 hvn hc (a := -xL i)
          (by linarith [hxL i]) hmx
        unfold Exist.StagedLaw.markPosL
        constructor
        · intro h
          by_contra hle
          push Not at hle
          have hm := hk.1 (by linarith)
          exact hyi (by linarith)
        · intro h
          have hm := hk.2 (by linarith)
          have hlt := lt_of_le_of_ne hm hmx
          linarith
      simp only [forceBoundaryData, hx0, hy0', ↓reduceIte, hfilt]
    · exfalso
      push Not at hR hL
      have hx0 : x ≠ 0 := fun h => hxS (h ▸ h0S)
      rcases eq_or_lt_of_le (le_trans hL hR) with heq | hlt
      · have h1 := WangWu.chartAL_nonpos hW hu.le
        have h2 := WangWu.chartAR_nonneg hW hu.le
        exact hx0 (by linarith)
      · exact hxK (RelTrans.Icc_subset_hullImage hη hW hW0 hu hlt ⟨hL, hR⟩)

end InteractingSLE.Supp8.Q3Kernel
