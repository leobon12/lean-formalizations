/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Exhaust

/-!
# Aux. lemma 50 for `κ ≥ 8`: the common Borel kernel approximants

Packet PROVE-AUX50C. Specification Aux. lemma 50, last paragraph (`source/spec/p241-288.md` L26–L33): "Before comparing
two couplings, fix common measurable versions of (HGV1) under their one common driving marginal. […] This defines
Borel path functions once under the common law, and the same functions apply in every coupling with that marginal."

The approximants of the conditional characteristic function of the field given the history at `N` are explicit Borel
functions of the recorded history (`kerApprox`): the frozen piece means read from the history's characteristic
functional (`Aux50Hit.charMean`), the Green energy of the active domain at `N` (`histC`) and the retained energy of the
pocket pieces (`histPocQ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3 LQGMetric LocalSets WholeField Coupling Aux50Hit Sec4 LawUnique WangWu

variable {nL nR : ℕ}

/-! ### The Green energy of the active domain, from the history -/

/-- `G_{D_N}(φ, φ)` read from a history (through the time-`N` kernel of `Aux50Hit.vtKerH`, `0` off the alive set). -/
def histC (N : ℕ) (φ : TestOn upperHalfPlaneOpens) (γ : HistorySpace nL nR) : ℝ :=
  ∫ a, ∫ b, φ a * (vtKerH (N : ℝ) (N : ℝ) (γ, a, b)).toReal * φ b

theorem measurable_histC (N : ℕ) (φ : TestOn upperHalfPlaneOpens) :
    Measurable (histC (nL := nL) (nR := nR) N φ) := by
  set g : (HistorySpace nL nR × ℂ) × ℂ → ℝ := fun x => φ x.1.2 *
    (vtKerH (N : ℝ) (N : ℝ) (x.1.1, x.1.2, x.2)).toReal * φ x.2 with hgdef
  have hg : Measurable g := by
    have hφ : Measurable (φ : ℂ → ℝ) := φ.continuous.measurable
    have hm : Measurable fun x : (HistorySpace nL nR × ℂ) × ℂ => (x.1.1, x.1.2, x.2) :=
      (measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact ((hφ.comp (measurable_snd.comp measurable_fst)).mul
      (ENNReal.measurable_toReal.comp ((measurable_vtKerH _ _).comp hm))).mul (hφ.comp measurable_snd)
  have e : histC (nL := nL) (nR := nR) N φ = fun γ => ∫ a, ∫ b, g ((γ, a), b) := rfl
  rw [e]
  exact (hg.stronglyMeasurable.integral_prod_right'.integral_prod_right').measurable

/-- The history kernel at time `N` is the active-domain kernel of the regularized driver. -/
theorem vtKerH_toReal_eq (N : ℕ) (γ : HistorySpace nL nR) (a b : ℂ) :
    (vtKerH (N : ℝ) (N : ℝ) (γ, a, b)).toReal = aGreen (Ito.rpath (regPath γ)) N a b := by
  have hNN : ((N : ℝ).toNNReal : ℝ) = N := Real.coe_toNNReal _ (Nat.cast_nonneg N)
  unfold vtKerH aGreen
  by_cases h : (γ, a) ∈ aliveH (nL := nL) (nR := nR) (N : ℝ).toNNReal ∧
      (γ, b) ∈ aliveH (nL := nL) (nR := nR) (N : ℝ).toNNReal
  · have ha : a ∈ actDom (Ito.rpath (regPath γ)) N := by
      have := h.1; simp only [aliveH, mem_ofPred_eq] at this; rwa [hNN] at this
    have hb : b ∈ actDom (Ito.rpath (regPath γ)) N := by
      have := h.2; simp only [aliveH, mem_ofPred_eq] at this; rwa [hNN] at this
    rw [ite_eq_left ⟨Nat.cast_nonneg N, le_rfl, h.1, h.2⟩, hNN]
    simp only [ha, hb, and_self, ↓reduceIte, vtKer]
  · rw [ite_eq_right fun h' => h ⟨h'.2.2.1, h'.2.2.2⟩, ENNReal.toReal_top]
    have : ¬ (a ∈ actDom (Ito.rpath (regPath γ)) N ∧ b ∈ actDom (Ito.rpath (regPath γ)) N) := by
      rintro ⟨ha, hb⟩
      refine h ⟨?_, ?_⟩
      · show a ∈ H \ fwdHull _ _; rw [hNN]; exact ha
      · show b ∈ H \ fwdHull _ _; rw [hNN]; exact hb
    simp only [this, ↓reduceIte]

/-! ### The approximants -/

open scoped Classical in
/-- **The retained energy of the pocket pieces at scale `n`**, read from the history at `N`. -/
def histPocQ (N : ℕ) (φ : TestOn upperHalfPlaneOpens) (n : ℕ) (γ : HistorySpace nL nR) : ℝ :=
  histQ N ((∑ k ∈ pIdx φ n, (if histPoc N (tsupport (pouTest φ n k)) γ then (1 : ℝ) else 0) • pouTest φ n k :
    TestOn upperHalfPlaneOpens) : ℂ → ℝ) (stopHistory (cstop (N : ℝ≥0)) γ)

open scoped Classical in
theorem measurable_histPocQ (N : ℕ) (φ : TestOn upperHalfPlaneOpens) (n : ℕ) :
    Measurable (histPocQ (nL := nL) (nR := nR) N φ n) := by
  -- finitely many patterns
  set s := pIdx φ n
  set pat : HistorySpace nL nR → Finset (ℤ × ℤ) := fun γ => s.filter fun k => histPoc N (tsupport (pouTest φ n k)) γ
  have hpat : ∀ t, MeasurableSet {γ : HistorySpace nL nR | pat γ = t} := by
    intro t
    have e : {γ : HistorySpace nL nR | pat γ = t} =
        if t ⊆ s then ⋂ k ∈ s, {γ | (histPoc N (tsupport (pouTest φ n k)) γ ↔ k ∈ t)} else ∅ := by
      split_ifs with ht
      · ext γ
        simp only [mem_ofPred_eq, mem_iInter, pat]
        constructor
        · rintro rfl k hk; simp [hk]
        · intro hγ
          ext k
          simp only [Finset.mem_filter]
          exact ⟨fun h' => (hγ k h'.1).1 h'.2, fun h' => ⟨ht h', (hγ k (ht h')).2 h'⟩⟩
      · ext γ
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro rfl
        exact ht (Finset.filter_subset _ s)
    rw [e]
    split_ifs
    · refine MeasurableSet.biInter s.countable_toSet fun k _ => ?_
      by_cases hkt : k ∈ t
      · simp only [hkt, iff_true]
        exact measurableSet_histPoc N (pouTest φ n k).hasCompactSupport.isCompact (pouTest φ n k).tsupport_subset
      · simp only [hkt, iff_false]
        exact (measurableSet_histPoc N (pouTest φ n k).hasCompactSupport.isCompact
          (pouTest φ n k).tsupport_subset).compl
    · exact MeasurableSet.empty
  have e : histPocQ (nL := nL) (nR := nR) N φ n = fun γ => ∑ t ∈ s.powerset,
      {γ : HistorySpace nL nR | pat γ = t}.indicator
        (fun γ => histQ N ((∑ k ∈ t, pouTest φ n k : TestOn upperHalfPlaneOpens) : ℂ → ℝ)
          (stopHistory (cstop (N : ℝ≥0)) γ)) γ := by
    funext γ
    rw [Finset.sum_eq_single (pat γ)]
    · have hsum : (∑ k ∈ pIdx φ n, (if histPoc N (tsupport (pouTest φ n k)) γ then (1 : ℝ) else 0) •
          pouTest φ n k) = ∑ k ∈ pat γ, pouTest φ n k := by
        rw [show (pat γ) = s.filter fun k => histPoc N (tsupport (pouTest φ n k)) γ from rfl, Finset.sum_filter]
        refine Finset.sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
      rw [indicator_of_mem (show γ ∈ {γ' : HistorySpace nL nR | pat γ' = pat γ} from rfl), histPocQ, hsum]
    · intro t _ hne
      exact indicator_of_notMem (fun h' => hne h'.symm) _
    · intro hn
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ s)) hn
  rw [e]
  refine Finset.measurable_sum _ fun t _ => ?_
  exact ((measurable_histQ N _).comp (measurable_stopHistory (measurable_cstop _))).indicator (hpat t)

/-- **The approximating kernel at scale `n`** (a Borel function of the recorded history at `N`):
`exp(i ∑ₖ m_{τₖ}(ψₖ) − ½ (G_{D_N}(φ, φ) + Q_{U_N}(φ_S)))`, the frozen piece means read from the characteristic
functional of the history. -/
def kerApprox (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (N : ℕ) (φ : TestOn upperHalfPlaneOpens) (n : ℕ)
    (γ : HistorySpace nL nR) : ℂ :=
  cexp (((∑ k ∈ pIdx φ n, charMean (histG κ ρL ρR) (pouTest φ n k)
      (stopHistory (safeRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n) γ) : ℝ) : ℂ) * I) *
    ((Real.exp (-(1 / 2) * (histC N φ (stopHistory (cstop (N : ℝ≥0)) γ) + histPocQ N φ n γ)) : ℝ) : ℂ)

theorem measurable_kerApprox (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (N : ℕ) (φ : TestOn upperHalfPlaneOpens)
    (n : ℕ) : Measurable (kerApprox κ ρL ρR N φ n) := by
  have hm : Measurable fun γ : HistorySpace nL nR => ∑ k ∈ pIdx φ n, charMean (histG κ ρL ρR) (pouTest φ n k)
      (stopHistory (safeRule (tsupport (pouTest φ n k)) (testLow (pouTest φ n k)) N n) γ) :=
    Finset.measurable_sum _ fun k _ => (measurable_charMean (measurable_histG κ ρL ρR) _).comp
      (measurable_stopHistory (measurable_safeRule (pouTest φ n k).tsupport_subset (testLow_pos _) N n))
  have hq : Measurable fun γ : HistorySpace nL nR =>
      histC N φ (stopHistory (cstop (N : ℝ≥0)) γ) + histPocQ N φ n γ :=
    ((measurable_histC N φ).comp (measurable_stopHistory (measurable_cstop _))).add (measurable_histPocQ N φ n)
  exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hm).mul_const _)).mul
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hq)))

end Aux50Ge8

end InteractingSLE
