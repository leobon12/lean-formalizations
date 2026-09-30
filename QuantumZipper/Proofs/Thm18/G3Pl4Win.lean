import QuantumZipper.Proofs.Thm18.G3PlX
import QuantumZipper.Proofs.Thm18.G3FidProxy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): the Palm window of the wedge vs the capped window

The wedge Palm window `{x < 0 : ν[x, 0] ≤ U}` (`g1zWedgeWin`) and the capped window of scheme `C`
`{x < 0 : ν[x, 0] ≤ U ∧ ν[x, 0] ≤ ν[−δ, 0]}` (`g3plXWin`) coincide when `ν[−δ, 0] ≥ U`; in general
the uncapped window has `ν`-mass at most `U` (`g3pl4_measure_win_le`: it is an interval ending at
`0` all of whose closed sub-intervals `[x, 0]` have mass `≤ U`). Hence the Palm-window functional
`g3plPhi` of any field and its capped version `g3pl4PhiCap` (whose expectation under `h_C` is
`g3plHonX`, `g3plHonX_eq_phiCap`) differ by at most `U · 1{ν[−δ, 0] < U}`
(`g3pl4_phiCap_le_phi`, `g3pl4_phi_le_phiCap`): after division by `U` the discrepancy is the
probability that `ν[−δ, 0] < U`, which tends to `0` as `U → 0` when `ν[−δ, 0] > 0` a.s.
(Sheffield, arXiv:1012.4797, p. 71: the Palm point is sampled from the boundary length on a
window). Own elementary argument (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **The uncapped Palm window has mass at most `U`.** -/
theorem g3pl4_measure_win_le (ν : Measure ℝ) (u : ℝ≥0∞) :
    ν {x : ℝ | x < 0 ∧ ν (Icc x 0) ≤ u} ≤ u := by
  set S := {x : ℝ | x < 0 ∧ ν (Icc x 0) ≤ u} with hS
  have up : ∀ x ∈ S, ∀ x', x ≤ x' → x' < 0 → x' ∈ S := fun x hx x' hxx' hx' =>
    ⟨hx', (measure_mono (Icc_subset_Icc_left hxx')).trans hx.2⟩
  -- a monotone family of intervals `Icc (v n) 0` with `v n ∈ S` covering `S`
  have key : ∀ v : ℕ → ℝ, Antitone v → (∀ n, v n ∈ S) → S ⊆ ⋃ n, Icc (v n) 0 → ν S ≤ u := by
    intro v hv hvS hcov
    refine (measure_mono hcov).trans ?_
    have hmono : Monotone fun n => Icc (v n) (0 : ℝ) := fun m n hmn =>
      Icc_subset_Icc_left (hv hmn)
    rw [hmono.measure_iUnion]
    exact iSup_le fun n => (hvS n).2
  rcases S.eq_empty_or_nonempty with hE | hne
  · rw [hE, measure_empty]; exact bot_le
  by_cases hb : BddBelow S
  · by_cases hinf : sInf S ∈ S
    · refine (measure_mono (μ := ν) (s := S) (t := Icc (sInf S) 0)
        fun x hx => ⟨csInf_le hb hx, hx.1.le⟩).trans hinf.2
    · obtain ⟨v, hv, hvlim, hvS⟩ := exists_seq_tendsto_sInf hne hb
      refine key v hv hvS fun x hx => ?_
      have hlt : sInf S < x := lt_of_le_of_ne (csInf_le hb hx) fun h => hinf (h ▸ hx)
      obtain ⟨n, hn⟩ := (hvlim.eventually (gt_mem_nhds hlt)).exists
      exact mem_iUnion.2 ⟨n, hn.le, hx.1.le⟩
  · have hm : ∀ n : ℕ, (-((n : ℝ) + 1)) ∈ S := by
      intro n
      obtain ⟨x, hx, hxn⟩ : ∃ x ∈ S, x < -((n : ℝ) + 1) := by
        by_contra h
        push Not at h
        exact hb ⟨-((n : ℝ) + 1), h⟩
      exact up x hx _ hxn.le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    refine key (fun n => -((n : ℝ) + 1)) (fun m n hmn => ?_) hm fun x hx => ?_
    · have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      simp only; linarith
    · obtain ⟨n, hn⟩ := exists_nat_ge (-x)
      exact mem_iUnion.2 ⟨n, by linarith, hx.1.le⟩

theorem g3pl4_ind_mul_le_one {α β : Type*} (s : Set α) (t : Set β) (a : α) (b : β) :
    s.indicator (1 : α → ℝ≥0∞) a * t.indicator 1 b ≤ 1 := by
  unfold Set.indicator
  split_ifs <;> simp

theorem g3pl4_restrict_Iio {ν : Measure ℝ} {W : Set ℝ} (hW : W ⊆ Iio 0) :
    (ν.restrict (g1SideHalf true)).restrict W = ν.restrict W := by
  rw [show g1SideHalf true = Iio 0 by simp [g1SideHalf], Measure.restrict_restrict' measurableSet_Iio,
    inter_eq_left.2 hW]

end R18
end QuantumZipper
