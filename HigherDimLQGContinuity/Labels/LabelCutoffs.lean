import HigherDimLQGContinuity.Labels.LabelDefs

/-!
# Finite index cutoffs for all source labels

Every side-`μ` cell contained in a reserved box has bounded integer index.
Every point of the `ν` grid in such a box has bounded integer index.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

/-- The least convenient integer cutoff for a cell index relative to its origin. -/
def labelCellCutoff {d : ℕ} (S : SiteData d) (μ : ℝ) : ℕ :=
  ⌈S.boxHalfSide / μ⌉₊ + 2

/-- A fixed integer cutoff for `ν`-grid points in the collector annulus. -/
def labelLeadCutoff (ν : ℝ) : ℕ := ⌈(5 / 2 : ℝ) / ν⌉₊ + 2

private theorem labelIndex_mem_of_abs_mul_le {d K : ℕ} {a B : ℝ}
    (ha : 0 < a) (hK : B / a ≤ (K : ℝ))
    (k : Fin d → ℤ) (hk : ∀ i, |a * (k i : ℝ)| ≤ B) :
    k ∈ labelIndexFinset d K := by
  classical
  rw [labelIndexFinset, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hki : |(k i : ℝ)| ≤ B / a := by
    have h := hk i
    rw [abs_mul, abs_of_pos ha] at h
    apply (le_div_iff₀ ha).2
    nlinarith [abs_nonneg (k i : ℝ)]
  have hbound : |(k i : ℝ)| ≤ K := hki.trans hK
  have hlo : -((K : ℤ) : ℝ) ≤ (k i : ℝ) := by
    have h := (abs_le.mp hbound).1
    simpa using h
  have hhi : (k i : ℝ) ≤ ((K : ℤ) : ℝ) := by
    simpa using (abs_le.mp hbound).2
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- A source cell contained in the reserved box fits the finite cell cutoff. -/
theorem cell_index_mem_labelCutoff {d : ℕ} (S : SiteData d)
    {μ : ℝ} (hμ : 0 < μ) (e : S.Edge) (k : Fin d → ℤ)
    (hcell : cell μ (S.edgeCenter e) k ⊆ S.box e) :
    k ∈ labelIndexFinset d (labelCellCutoff S μ) := by
  let x : Rd d := WithLp.toLp 2 fun i => (S.edgeCenter e) i + μ * (k i : ℝ)
  have hxcell : x ∈ cell μ (S.edgeCenter e) k := by
    intro i
    dsimp [x]
    constructor
    · exact le_rfl
    · nlinarith [hμ.le]
  have hxbox := hcell hxcell
  have hk : ∀ i, |μ * (k i : ℝ)| ≤ S.boxHalfSide := by
    intro i
    have h := hxbox i
    simpa only [x, PiLp.toLp_apply, add_sub_cancel_left] using h
  have hK : S.boxHalfSide / μ ≤ (labelCellCutoff S μ : ℝ) := by
    unfold labelCellCutoff
    have hceil := Nat.le_ceil (S.boxHalfSide / μ)
    push_cast
    linarith
  exact labelIndex_mem_of_abs_mul_le hμ hK k hk

/-- A grid vertex in a reserved box fits the finite lead cutoff. -/
theorem grid_index_mem_labelCutoff {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν : ℝ} (hν : 0 < ν) (e : S.Edge) (k : Fin d → ℤ)
    (hkbox : (WithLp.toLp 2 fun i => ν * (k i : ℝ) : Rd d) ∈ S.box e) :
    k ∈ labelIndexFinset d (labelLeadCutoff ν) := by
  let x : Rd d := WithLp.toLp 2 fun i => ν * (k i : ℝ)
  have hxC : x ∈ siteC d := interior_subset (S.box_subset_interior_C hd e hkbox)
  have hxnorm : ‖x‖ ≤ 5 / 2 := by
    simpa only [siteC, annCl, mem_ofPred_eq, sub_zero] using hxC.2
  have hk : ∀ i, |ν * (k i : ℝ)| ≤ 5 / 2 := by
    intro i
    have hi := PiLp.norm_apply_le x i
    simpa only [x, PiLp.toLp_apply, Real.norm_eq_abs] using hi.trans hxnorm
  have hK : (5 / 2 : ℝ) / ν ≤ (labelLeadCutoff ν : ℝ) := by
    unfold labelLeadCutoff
    have hceil := Nat.le_ceil ((5 / 2 : ℝ) / ν)
    push_cast
    linarith
  exact labelIndex_mem_of_abs_mul_le hν hK k hk

/-- Re-encode a finite set whose members satisfy a proven cutoff. -/
def encodeLabelIndices {d K : ℕ} (Q : Finset (Fin d → ℤ))
    (hQ : ∀ k ∈ Q, k ∈ labelIndexFinset d K) :
    Finset (LabelIndex d K) := by
  classical
  exact Q.attach.image fun k => ⟨k.1, hQ k.1 k.2⟩

theorem labelCellIndices_encode {d K : ℕ} (Q : Finset (Fin d → ℤ))
    (hQ : ∀ k ∈ Q, k ∈ labelIndexFinset d K) :
    labelCellIndices (encodeLabelIndices Q hQ) = Q := by
  classical
  unfold labelCellIndices encodeLabelIndices
  rw [Finset.image_image]
  simpa only [Function.comp_def] using Finset.attach_image_val (s := Q)

end HigherDimLQGContinuity
