import HigherDimLQGMetric.LfppTight.CrossScaleDirect
import HigherDimLQGMetric.LfppTight.NormalizeMetric
import HigherDimLQGMetric.LfppTight.BddContTail
import HigherDimLQGMetric.LfppTight.CrossCompare

/-! A8 for an LGF plus a random bounded continuous perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_cross_bddCont_direct (hL1e : L1e_law)
    {d : ℕ} {κ : Rd d → ℝ} {ξ Q : ℝ}
    (hDGZ : DGZ.DGZHyp d κ ξ Q)
    (hAdapter : DGZ.RealEpsAdapterShape d κ ξ Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusBddCont h P)
    {p C : ℝ} (hp : p < 1) (hC : 0 < C) :
    ∃ R ε₀ : ℝ, 1 < R ∧ 0 < ε₀ ∧
      ∀ r : ℝ, 0 < r → ∀ x : Rd d, ∀ ε ∈ Ioo (0 : ℝ) (ε₀ * r),
        ENNReal.ofReal p ≤ P {ω |
          supPairs (lfppDist κ ξ ε (h ω)) (ball x r) ≤
            ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
              (sphere x r) (sphere x (R * r))} := by
  by_cases hp0 : p ≤ 0
  · refine ⟨2, 1, by norm_num, by norm_num, fun r hr x ε hε => ?_⟩
    simp only [ENNReal.ofReal_eq_zero.mpr hp0]
    exact bot_le
  have hp0' : 0 < p := lt_of_not_ge hp0
  obtain ⟨_, f, hfm, hfb, hb⟩ := hh
  let b : Ω → DistRd d := fun ω => h ω - ofCont (f ω)
  have hb' : IsWholeSpaceLGF b P := hb
  have hconv : ∀ᵐ ω ∂P, b ω ∈ convSet d :=
    hb'.ae_exists_tendsto_sphereAvgSeq hDGZ.dim one_pos 0
  let g : Ω → DistRd d := fun ω =>
    addConst (b ω) (-sphereAvg (b ω) 1 0)
  have hg : IsNormalizedLGF g P :=
    hb'.isNormalizedLGF_normalize (by have := hDGZ.dim; omega) hconv
  let c : Ω → ℝ := fun ω => sphereAvg (b ω) 1 0
  have hbc (ω : Ω) : b ω = addConst (g ω) (c ω) := by
    dsimp [g, c]
    rw [addConst_addConst, neg_add_cancel, addConst_zero]
  have hhb (ω : Ω) : h ω = addFun (b ω) (f ω) := by
    dsimp [b, addFun]
    abel
  let p' : ℝ := (1 + p) / 2
  let θ : ℝ := (1 - p) / 4
  have hp'0 : 0 < p' := by dsimp [p']; linarith
  have hp' : p' < 1 := by dsimp [p']; linarith
  have hθ : 0 < θ := by dsimp [θ]; linarith
  obtain ⟨M, hM, htail⟩ := l6a_exists_bddCont_tail P f hfm hfb hθ
  let L : ℝ := ∫ z : Rd d, |convKernel κ z|
  let a : ℝ := Real.exp (|ξ| * (M * L))
  have ha : 0 < a := Real.exp_pos _
  let C' : ℝ := C * a ^ 2
  have hC' : 0 < C' := mul_pos hC (sq_pos_of_pos ha)
  obtain ⟨R, ε₀, hR, hε₀, hcross⟩ := l6a_cross_normalized_direct
    hL1e hDGZ hAdapter P g hg hp' hC'
  refine ⟨R, ε₀, hR, hε₀, ?_⟩
  intro r hr x ε hε
  let EG : Set Ω := {ω |
    supPairs (lfppDist κ ξ ε (g ω)) (ball x r) ≤
      ENNReal.ofReal C'⁻¹ * infPairs (lfppDist κ ξ ε (g ω))
        (sphere x r) (sphere x (R * r))}
  let EH : Set Ω := {ω |
    supPairs (lfppDist κ ξ ε (h ω)) (ball x r) ≤
      ENNReal.ofReal C⁻¹ * infPairs (lfppDist κ ξ ε (h ω))
        (sphere x r) (sphere x (R * r))}
  let EB : Set Ω := {ω | ∃ z : Rd d, M < |f ω z|}
  have hG : ENNReal.ofReal p' ≤ P EG := hcross r hr x ε hε
  have hB : P EB ≤ ENNReal.ofReal θ := htail
  have hcomp := l6a_ae_lfppDist_addFun_compare hDGZ.dim κ hDGZ.kernel ξ
    P b hb' f hε.1 M
  have hnorm := l6a_ae_lfppDist_addConst_normalized hDGZ.dim κ
    hDGZ.kernel ξ P g hg b c hbc
  have hsub : ∀ᵐ ω ∂P, ω ∈ EG → ω ∈ EH ∪ EB := by
    filter_upwards [hcomp, hnorm] with ω hw hn hgω
    by_cases hbad : ω ∈ EB
    · exact Or.inr hbad
    · have hgood : ∀ z, |f ω z| ≤ M := by
        intro z
        exact le_of_not_gt fun hz => hbad ⟨z, hz⟩
      left
      let Dh : Rd d × Rd d → ℝ := lfppDist κ ξ ε (h ω)
      let Db : Rd d × Rd d → ℝ := lfppDist κ ξ ε (b ω)
      let Dg : Rd d × Rd d → ℝ := lfppDist κ ξ ε (g ω)
      have hDB (q : Rd d × Rd d) : Dh q ≤ a * Db q := by
        simpa only [Dh, Db, a, L, ← hhb ω] using (hw hgood q).1
      have hBD (q : Rd d × Rd d) : Db q ≤ a * Dh q := by
        simpa only [Dh, Db, a, L, ← hhb ω] using (hw hgood q).2
      have ht : 0 < Real.exp (ξ * c ω) := Real.exp_pos _
      have hBG : Db = fun q => Real.exp (ξ * c ω) * Dg q := by
        funext q
        exact hn ε hε.1 q
      have h := l6a_cross_of_perturb_normalized Dh Db Dg
        (ball x r) (sphere x r) (sphere x (R * r)) ha ht hC
        hDB hBD hBG hgω
      exact h
  have hbound : P EG ≤ P EH + ENNReal.ofReal θ := by
    calc
      P EG ≤ P (EH ∪ EB) := measure_mono_ae hsub
      _ ≤ P EH + P EB := measure_union_le _ _
      _ ≤ P EH + ENNReal.ofReal θ := by gcongr
  have hsum : ENNReal.ofReal p + ENNReal.ofReal θ ≤ ENNReal.ofReal p' := by
    rw [← ENNReal.ofReal_add hp0'.le hθ.le]
    exact ENNReal.ofReal_le_ofReal (by dsimp [p', θ]; linarith)
  have hq : ENNReal.ofReal p + ENNReal.ofReal θ ≤
      P EH + ENNReal.ofReal θ := hsum.trans (hG.trans hbound)
  exact (ENNReal.add_le_add_iff_right (by simp : ENNReal.ofReal θ ≠ ⊤)).mp hq

end HigherDimLQGMetric
