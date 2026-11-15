/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MtDrv

/-!
# Drivers from hulls known on a dense set of times (deterministic)

Packet PROVE-SB2-CANON, round 4 ((P4): the identification of the canonical driver). The versions' hull clause holds at
each B-time almost surely, so at one sample only on a countable dense set of times. Loewner hulls are
right-continuous in
time (`fwdHull W t = {z ∈ ℍ | swallowTime W z ≤ t}`), so hulls that agree on a set `D` of times that accumulates at
every time from the right agree at every time (**`fwdHull_eq_of_dense`**), and then two continuous drivers from `0`
agree (**`eqOn_of_fwdHull_dense`**, through `Mt.eqOn_of_fwdHull_eq_add_const`).

R48: no source theorem is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull swallowTime)

namespace InteractingSLE.Theorem14.SB.Cz

/-- **Hulls agreeing on a right-dense set of times agree.** -/
theorem fwdHull_eq_of_dense {W₁ W₂ : ℝ → ℝ} {D : Set ℝ} {t : ℝ}
    (hD : ∀ ε > 0, ∃ s ∈ D, t < s ∧ s < t + ε) (h : ∀ s ∈ D, fwdHull W₁ s = fwdHull W₂ s) :
    fwdHull W₁ t = fwdHull W₂ t := by
  have key : ∀ {V₁ V₂ : ℝ → ℝ}, (∀ s ∈ D, fwdHull V₁ s = fwdHull V₂ s) → fwdHull V₁ t ⊆ fwdHull V₂ t := by
    intro V₁ V₂ hV z hz
    refine ⟨hz.1, ?_⟩
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    -- `c > ofReal t`: pick `s ∈ D` with `t < s` and `ofReal s < c`
    have ht : ENNReal.ofReal t < c := hc
    by_cases hctop : c = ⊤
    · rw [hctop]
      obtain ⟨s, hsD, hts, -⟩ := hD 1 one_pos
      have hz' : z ∈ fwdHull V₁ s := ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal hts.le)⟩
      rw [hV s hsD] at hz'
      exact hz'.2.trans ENNReal.ofReal_lt_top.le
    have htc : t < c.toReal := by
      by_cases ht0 : t < 0
      · exact lt_of_lt_of_le ht0 ENNReal.toReal_nonneg
      · exact (ENNReal.ofReal_lt_iff_lt_toReal (not_lt.1 ht0) hctop).1 ht
    obtain ⟨s, hsD, hts, hsc⟩ := hD (c.toReal - t) (by linarith)
    have hz' : z ∈ fwdHull V₁ s := ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal hts.le)⟩
    rw [hV s hsD] at hz'
    refine hz'.2.trans ?_
    rw [← ENNReal.ofReal_toReal hctop]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  exact Subset.antisymm (key h) (key fun s hs => (h s hs).symm)

/-- **Continuous drivers from `0` whose hulls agree on a right-dense set of times agree.** -/
theorem eqOn_of_fwdHull_dense {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂) (hW₁0 : W₁ 0 = 0)
    (hW₂0 : W₂ 0 = 0) {D : Set ℝ} {S : ℝ} (hS : 0 < S)
    (hD : ∀ t ∈ Icc (0 : ℝ) S, ∀ ε > 0, ∃ s ∈ D, t < s ∧ s < t + ε) (h : ∀ s ∈ D, fwdHull W₁ s = fwdHull W₂ s) :
    EqOn W₁ W₂ (Icc 0 S) := by
  refine (Mt.eqOn_of_fwdHull_eq_add_const hW₁ hW₂ hW₁0 hW₂0 hS (d := 0) fun s hs => ?_).2
  rw [fwdHull_eq_of_dense (hD s hs) h]
  ext z
  simp

end InteractingSLE.Theorem14.SB.Cz
