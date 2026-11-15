/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHiCompare

/-!
# Aux. lemma 108, driver form: the energy of a neutral change of weights

Packet PROVE-TRIALS-HI. Specification p. 358, (HBT3): "`∫₀ᵗ a_s² ds = ‖f‖²_∇ − G_{ℍ∖K_t}(v, v) ≤ ‖f‖²_∇`" — the
energy of
the drift change between the reference and the proposed configuration is bounded as long as the hull stays in the
buffer. In driver form the drift change of weights `ρ → ρ'` on one side is `Σ_k c_k/(W − V_k)` with charges
`c_k = ρ'_k − ρ_k`. When the charges of a side are **neutral** (`Σ_k c_k = 0`: the reference and proposed side totals
agree), the square is controlled pointwise by the *oscillation density* of the side:

  `(Σ_k c_k / X_k)² ≤ (Σ_k |c_k|)² (1/X_near² − 1/X_far²)`  for `X_near ≤ X_k ≤ X_far`

(`sq_sum_div_le_of_sum_eq_zero`: `(Σ c_k/X_k)² = Σ_{k,l} c_k c_l (1/(X_k X_l) − 1/X_near²)` and every
`1/(X_k X_l)` lies in `[1/X_far², 1/X_near²]`). Hence the energy of the change on `[0, T]` is at most
`2κ⁻¹ ((Σ|c^L|)² osc^L_T + (Σ|c^R|)² osc^R_T)`, `osc_T = ∫₀ᵀ (1/X_near² − 1/X_far²)` (`changeEnergy_le_osc`), where
`near`/`far` are the nearest and the outermost mark of a side. No Green function and no field are used. The
oscillation `osc` is `½ log(g'_t(x_far)/g'_t(x_near))`, the distortion of the Loewner map on the side; it stays bounded
on the successful reference events of Aux. lemmas 109–111.

## Main results

* `sq_sum_div_le_of_sum_eq_zero` (every finite family of neutral charges);
* `sideOsc`, `changeEnergy_le_osc` (every `κ > 0`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi

open Zhan Sec2 Girsanov Coupling

/-! ### Neutral charges -/

/-- **The square of a neutral sum of inverse distances** is bounded by the oscillation of the inverse squares over
the range of the distances. -/
theorem sq_sum_div_le_of_sum_eq_zero {ι : Type*} [Fintype ι] (c X : ι → ℝ) {a b : ℝ} (ha : 0 < a)
    (hX : ∀ i, a ≤ X i ∧ X i ≤ b) (hc : ∑ i, c i = 0) :
    (∑ i, c i / X i) ^ 2 ≤ (∑ i, |c i|) ^ 2 * (1 / a ^ 2 - 1 / b ^ 2) := by
  have hXpos : ∀ i, 0 < X i := fun i => lt_of_lt_of_le ha (hX i).1
  set K := 1 / a ^ 2 - 1 / b ^ 2 with hK
  have hterm : ∀ i j, c i * c j * (1 / (X i * X j) - 1 / a ^ 2) ≤ |c i| * |c j| * K := by
    intro i j
    have hXi := hX i
    have hXj := hX j
    have hpi := hXpos i
    have hpj := hXpos j
    have h1 : 1 / (X i * X j) ≤ 1 / a ^ 2 := by
      rw [div_le_div_iff₀ (mul_pos hpi hpj) (pow_pos ha 2), one_mul, one_mul, sq]
      exact mul_le_mul hXi.1 hXj.1 ha.le hpi.le
    have hbpos : 0 < b := lt_of_lt_of_le hpi hXi.2
    have h2 : 1 / b ^ 2 ≤ 1 / (X i * X j) := by
      rw [div_le_div_iff₀ (pow_pos hbpos 2) (mul_pos hpi hpj), one_mul, one_mul, sq]
      exact mul_le_mul hXi.2 hXj.2 hpj.le hbpos.le
    have habs : |1 / (X i * X j) - 1 / a ^ 2| ≤ K := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    calc c i * c j * (1 / (X i * X j) - 1 / a ^ 2) ≤ |c i * c j * (1 / (X i * X j) - 1 / a ^ 2)| :=
          le_abs_self _
      _ = |c i| * |c j| * |1 / (X i * X j) - 1 / a ^ 2| := by rw [abs_mul, abs_mul]
      _ ≤ |c i| * |c j| * K := mul_le_mul_of_nonneg_left habs (by positivity)
  have e1 : (∑ i, c i / X i) ^ 2 = ∑ i, ∑ j, c i * c j * (1 / (X i * X j) - 1 / a ^ 2) := by
    have h0 : ∑ i, ∑ j, c i * c j * (1 / a ^ 2) = 0 := by
      have : ∑ i, ∑ j, c i * c j * (1 / a ^ 2) = (∑ i, c i) * (∑ j, c j) * (1 / a ^ 2) := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
      rw [this, hc, zero_mul, zero_mul]
    have h1 : (∑ i, c i / X i) ^ 2 = ∑ i, ∑ j, c i * c j * (1 / (X i * X j)) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have := hXpos i
      have := hXpos j
      field_simp
    rw [h1]
    have : ∀ i j, c i * c j * (1 / (X i * X j) - 1 / a ^ 2) =
        c i * c j * (1 / (X i * X j)) - c i * c j * (1 / a ^ 2) := fun i j => by ring
    simp_rw [this, Finset.sum_sub_distrib, h0, sub_zero]
  rw [e1]
  calc ∑ i, ∑ j, c i * c j * (1 / (X i * X j) - 1 / a ^ 2) ≤ ∑ i, ∑ j, |c i| * |c j| * K :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = (∑ i, |c i|) ^ 2 * K := by
        rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

/-! ### The energy of a neutral change of weights -/

section Energy

variable {Ω : Type*} {nL nR : ℕ}

/-- **The oscillation of a side** on `[0, T]`: `∫₀ᵀ (1/X_near² − 1/X_far²)` for the distances `X_near ≤ X_far` of the
nearest and the outermost mark of the side to the driver. -/
def sideOsc (near far : ℝ≥0 → ℝ) (T : ℝ≥0) : ℝ :=
  ∫ s in (0 : ℝ)..(T : ℝ), (1 / near s.toNNReal ^ 2 - 1 / far s.toNNReal ^ 2)

/-- **The energy of a change of weights with neutral sides is bounded by the side oscillations** (every `κ > 0`):
if on `[0, T]` the left distances `W − V^{L,i}` lie between those of the nearest (index `0`) and of the outermost left
mark, the nearest one positive, and the same on the right, and if `Σ (ρ'^L − ρ^L) = 0 = Σ (ρ'^R − ρ^R)`, then
`changeEnergy ≤ 2κ⁻¹ ((Σ|Δρ^L|)² osc^L_T + (Σ|Δρ^R|)² osc^R_T)`. -/
theorem changeEnergy_le_osc {κ : ℝ} (hκ : 0 < κ) {ρL ρL' : Fin (nL + 1) → ℝ} {ρR ρR' : Fin (nR + 1) → ℝ}
    (hnL : ∑ i, (ρL' i - ρL i) = 0) (hnR : ∑ j, (ρR' j - ρR j) = 0) {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {ω : Ω} {T : ℝ≥0}
    (hWc : Continuous fun s => W s ω) (hLc : ∀ i, Continuous fun s => VL i s ω)
    (hRc : ∀ j, Continuous fun s => VR j s ω)
    (hL : ∀ s : ℝ≥0, s ≤ T → ∀ i, 0 < W s ω - VL 0 s ω ∧ W s ω - VL 0 s ω ≤ W s ω - VL i s ω ∧
      W s ω - VL i s ω ≤ W s ω - VL (Fin.last nL) s ω)
    (hR : ∀ s : ℝ≥0, s ≤ T → ∀ j, 0 < VR 0 s ω - W s ω ∧ VR 0 s ω - W s ω ≤ VR j s ω - W s ω ∧
      VR j s ω - W s ω ≤ VR (Fin.last nR) s ω - W s ω) :
    changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω ≤
      2 / κ * ((∑ i, |ρL' i - ρL i|) ^ 2 * sideOsc (fun s => W s ω - VL 0 s ω)
          (fun s => W s ω - VL (Fin.last nL) s ω) T +
        (∑ j, |ρR' j - ρR j|) ^ 2 * sideOsc (fun s => VR 0 s ω - W s ω)
          (fun s => VR (Fin.last nR) s ω - W s ω) T) := by
  set A := (∑ i, |ρL' i - ρL i|) ^ 2 with hA
  set C := (∑ j, |ρR' j - ρR j|) ^ 2 with hC
  set f : ℝ → ℝ := fun s => (∑ j, weightDiff ρL ρL' ρR ρR' j /
    (W s.toNNReal ω - allMarks VL VR j s.toNNReal ω)) ^ 2 with hf
  set gL : ℝ → ℝ := fun s => 1 / (W s.toNNReal ω - VL 0 s.toNNReal ω) ^ 2 -
    1 / (W s.toNNReal ω - VL (Fin.last nL) s.toNNReal ω) ^ 2 with hgL
  set gR : ℝ → ℝ := fun s => 1 / (VR 0 s.toNNReal ω - W s.toNNReal ω) ^ 2 -
    1 / (VR (Fin.last nR) s.toNNReal ω - W s.toNNReal ω) ^ 2 with hgR
  have hTr : (0 : ℝ) ≤ T := T.coe_nonneg
  have hmem : ∀ s ∈ Icc (0 : ℝ) T, s.toNNReal ≤ T := fun s hs => by
    rw [Real.toNNReal_le_iff_le_coe]; exact hs.2
  -- continuity on `[0, T]`
  have hcR : Continuous fun s : ℝ => s.toNNReal := continuous_real_toNNReal
  have hW' : Continuous fun s : ℝ => W s.toNNReal ω := hWc.comp hcR
  have hL' : ∀ i, Continuous fun s : ℝ => VL i s.toNNReal ω := fun i => (hLc i).comp hcR
  have hR' : ∀ j, Continuous fun s : ℝ => VR j s.toNNReal ω := fun j => (hRc j).comp hcR
  have hposL : ∀ s ∈ Icc (0 : ℝ) T, ∀ i, 0 < W s.toNNReal ω - VL i s.toNNReal ω := fun s hs i => by
    obtain ⟨h1, h2, -⟩ := hL _ (hmem s hs) i; linarith
  have hposR : ∀ s ∈ Icc (0 : ℝ) T, ∀ j, 0 < VR j s.toNNReal ω - W s.toNNReal ω := fun s hs j => by
    obtain ⟨h1, h2, -⟩ := hR _ (hmem s hs) j; linarith
  have hfc : ContinuousOn f (Icc (0 : ℝ) T) := by
    refine ContinuousOn.pow (continuousOn_finsetSum _ fun j _ => ?_) 2
    refine continuousOn_const.div ((hW'.sub ?_).continuousOn) fun s hs => ?_
    · cases j using Fin.addCases with
      | left i => simpa [allMarks] using hL' i
      | right i => simpa [allMarks] using hR' i
    · cases j using Fin.addCases with
      | left i => simpa [allMarks] using (hposL s hs i).ne'
      | right i =>
        have := hposR s hs i
        simp only [allMarks, Fin.addCases_right]
        linarith
  have hgLc : ContinuousOn gL (Icc (0 : ℝ) T) := by
    refine ContinuousOn.sub ?_ ?_
    · exact continuousOn_const.div ((hW'.sub (hL' 0)).pow 2).continuousOn fun s hs =>
        (pow_pos (hposL s hs 0) 2).ne'
    · exact continuousOn_const.div ((hW'.sub (hL' _)).pow 2).continuousOn fun s hs =>
        (pow_pos (hposL s hs _) 2).ne'
  have hgRc : ContinuousOn gR (Icc (0 : ℝ) T) := by
    refine ContinuousOn.sub ?_ ?_
    · exact continuousOn_const.div (((hR' 0).sub hW').pow 2).continuousOn fun s hs =>
        (pow_pos (hposR s hs 0) 2).ne'
    · exact continuousOn_const.div (((hR' _).sub hW').pow 2).continuousOn fun s hs =>
        (pow_pos (hposR s hs _) 2).ne'
  have hfi : IntervalIntegrable f volume 0 T := (hfc.mono (by rw [uIcc_of_le hTr])).intervalIntegrable
  have hgLi : IntervalIntegrable gL volume 0 T := (hgLc.mono (by rw [uIcc_of_le hTr])).intervalIntegrable
  have hgRi : IntervalIntegrable gR volume 0 T := (hgRc.mono (by rw [uIcc_of_le hTr])).intervalIntegrable
  -- the pointwise bound
  have hpt : ∀ s ∈ Icc (0 : ℝ) T, f s ≤ 2 * A * gL s + 2 * C * gR s := by
    intro s hs
    set t := s.toNNReal
    have ht := hmem s hs
    have hsplit : (∑ j, weightDiff ρL ρL' ρR ρR' j / (W t ω - allMarks VL VR j t ω)) =
        (∑ i, (ρL' i - ρL i) / (W t ω - VL i t ω)) - ∑ j, (ρR' j - ρR j) / (VR j t ω - W t ω) := by
      rw [Fin.sum_univ_add]
      simp only [weightDiff, allMarks, Fin.addCases_left, Fin.addCases_right]
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← neg_sub (VR j t ω) (W t ω), div_neg]
    have hLb := sq_sum_div_le_of_sum_eq_zero (fun i => ρL' i - ρL i) (fun i => W t ω - VL i t ω)
      (hL t ht 0).1 (fun i => ⟨(hL t ht i).2.1, (hL t ht i).2.2⟩) hnL
    have hRb := sq_sum_div_le_of_sum_eq_zero (fun j => ρR' j - ρR j) (fun j => VR j t ω - W t ω)
      (hR t ht 0).1 (fun j => ⟨(hR t ht j).2.1, (hR t ht j).2.2⟩) hnR
    show (∑ j, weightDiff ρL ρL' ρR ρR' j / (W t ω - allMarks VL VR j t ω)) ^ 2 ≤ 2 * A * gL s + 2 * C * gR s
    rw [hsplit]
    set a := ∑ i, (ρL' i - ρL i) / (W t ω - VL i t ω)
    set b := ∑ j, (ρR' j - ρR j) / (VR j t ω - W t ω)
    have hab : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + b)]
    have e1 : 2 * A * gL s = 2 * (A * (1 / (W t ω - VL 0 t ω) ^ 2 - 1 / (W t ω - VL (Fin.last nL) t ω) ^ 2)) := by
      simp only [hgL]; ring
    have e2 : 2 * C * gR s = 2 * (C * (1 / (VR 0 t ω - W t ω) ^ 2 - 1 / (VR (Fin.last nR) t ω - W t ω) ^ 2)) := by
      simp only [hgR]; ring
    rw [e1, e2]
    linarith
  have hmono := intervalIntegral.integral_mono_on hTr hfi ((hgLi.const_mul (2 * A)).add (hgRi.const_mul (2 * C)))
    hpt
  rw [intervalIntegral.integral_add (hgLi.const_mul _) (hgRi.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  have hk : 0 ≤ 1 / κ := by positivity
  calc changeEnergy κ ρL ρL' ρR ρR' W VL VR T ω = 1 / κ * ∫ s in (0 : ℝ)..(T : ℝ), f s := rfl
    _ ≤ 1 / κ * (2 * A * (∫ s in (0 : ℝ)..(T : ℝ), gL s) + 2 * C * ∫ s in (0 : ℝ)..(T : ℝ), gR s) :=
        mul_le_mul_of_nonneg_left hmono hk
    _ = _ := by
        simp only [sideOsc, hgL, hgR, A, C]
        field_simp

end Energy

end TrialsHi

end Sec7

end InteractingSLE
