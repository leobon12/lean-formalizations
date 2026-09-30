import QuantumZipper.Proofs.Thm18.G3PalmRTightMom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-PALMRTIGHT, part 3: `G3PalmRTightStmt γ` and `G3GeoStmt γ`

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, p. 71: "we may choose `δ` small enough
so that with high probability `R(x) ∈ B₁(0)`"), in the rooted-measure form of `G3PalmR.lean`
(Duplantier–Sheffield, arXiv:0808.1560, §3.3).

For a root `x ∈ (−δ, 0)`, a.s. `ν^x = c(ω) m^x` on `[−1, 1]` (`ae_qBoundaryMeasure_palm_apply`,
`0 < c < ∞`), so the bad event `ν^x[¼,½] < 4δ ν^x[−¼,0]` is `m^x[¼,½] < 4δ m^x[−¼,0]`, which
forces `ν_Z[¼,½] < η` or `S_x ≥ K` once `4δK < η` (`palmM_Icc_ge`, `palmM_le_palmS`); both have
probability `≤ ε/2` uniformly in the root (`palm_tight_lower`, `palm_tight_upper`).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw (palmFreeField)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- **The uniform rooted-measure bound holds** for `0 < γ < 2`. -/
theorem g3PalmRTightStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G3PalmRTightStmt γ := by
  haveI := gffBase.prob
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨n, hn, hlow⟩ := palm_tight_lower gffBase.gff hγ hγ2 hε2
  obtain ⟨K, hK, hup⟩ := palm_tight_upper gffBase.gff hγ hγ2 hε2
  set η : ℝ := (n : ℝ)⁻¹ with hη
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hη0 : 0 < η := inv_pos.2 hnpos
  have hηE : ENNReal.ofReal η = (n : ℝ≥0∞)⁻¹ := by
    rw [hη, ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
  have hδ0 : 0 < min (1 / 8) (η / (4 * K)) := lt_min (by norm_num) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hδ0] with δ hδ x hx
  have hδ8 : δ < 1 / 8 := hδ.2.trans_le (min_le_left _ _)
  have hδK : 4 * δ * K < η := by
    have h := hδ.2.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hxa : |x| ≤ 1 := abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hx5 : |x| + 1 ≤ 5 := by linarith
  set Nset : Set Ω₀ := {ω | ¬ ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc (-1) 1 →
      qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) A =
        ENNReal.ofReal (Real.exp (γ / 2 * palmK γ x 5 X₀ ω)) * palmM γ x 5 X₀ ω A}
  have hN : gffBase.P Nset = 0 :=
    ae_iff.1 (ae_qBoundaryMeasure_palm_apply gffBase.gff hγ hγ2 (by norm_num) hx5)
  set L : Set Ω₀ := {ω | qBoundaryMeasure γ (BdryExist.zField X₀ 5 ω) (Icc (1 / 4) (1 / 2)) <
      (n : ℝ≥0∞)⁻¹}
  set U : Set Ω₀ := {ω | ENNReal.ofReal K ≤ palmS γ x 5 X₀ ω}
  have hsub : {ω | qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (1 / 4) (1 / 2)) <
      ENNReal.ofReal (4 * δ) *
        qBoundaryMeasure γ (palmFreeField γ refS X₀ x ω) (Icc (-(1 / 4)) 0)} ⊆ Nset ∪ L ∪ U := by
    intro ω hbad
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨hgood, hL⟩, hU⟩ := hnot
    simp only [Nset, mem_setOf_eq, not_not] at hgood
    simp only [L, mem_setOf_eq, not_lt] at hL
    simp only [U, mem_setOf_eq, not_le] at hU
    have e1 := hgood (Icc (1 / 4) (1 / 2)) measurableSet_Icc
      (Icc_subset_Icc (by norm_num) (by norm_num))
    have e2 := hgood (Icc (-(1 / 4)) 0) measurableSet_Icc
      (Icc_subset_Icc (by norm_num) (by norm_num))
    simp only [mem_setOf_eq] at hbad
    rw [e1, e2, mul_left_comm] at hbad
    have hc0 : ENNReal.ofReal (Real.exp (γ / 2 * palmK γ x 5 X₀ ω)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have hlo : (n : ℝ≥0∞)⁻¹ ≤ palmM γ x 5 X₀ ω (Icc (1 / 4) (1 / 2)) :=
      hL.trans (palmM_Icc_ge (by linarith [hx.2]) (by linarith [hx.1]) 5 ω)
    have hhi : palmM γ x 5 X₀ ω (Icc (-(1 / 4)) 0) ≤ palmS γ x 5 X₀ ω :=
      palmM_le_palmS hγ 5 ω measurableSet_Icc fun t ht =>
        abs_le.2 ⟨by linarith [ht.1, hx.2], by linarith [ht.2, hx.1]⟩
    have hlt : ENNReal.ofReal (4 * δ) * palmM γ x 5 X₀ ω (Icc (-(1 / 4)) 0) <
        (n : ℝ≥0∞)⁻¹ := by
      calc ENNReal.ofReal (4 * δ) * palmM γ x 5 X₀ ω (Icc (-(1 / 4)) 0)
          ≤ ENNReal.ofReal (4 * δ) * ENNReal.ofReal K := by gcongr; exact hhi.trans hU.le
        _ = ENNReal.ofReal (4 * δ * K) := (ENNReal.ofReal_mul (by linarith [hδ.1])).symm
        _ < ENNReal.ofReal η := (ENNReal.ofReal_lt_ofReal_iff hη0).2 hδK
        _ = (n : ℝ≥0∞)⁻¹ := hηE
    exact lt_asymm hbad (ENNReal.mul_lt_mul_right hc0 ENNReal.ofReal_ne_top (hlt.trans_le hlo))
  calc gffBase.P _ ≤ gffBase.P (Nset ∪ L ∪ U) := measure_mono hsub
    _ ≤ gffBase.P Nset + gffBase.P L + gffBase.P U :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ 0 + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
        gcongr
        · exact hN.le
        · exact hup x hxa
    _ = ENNReal.ofReal ε := by
        rw [zero_add, ← ENNReal.ofReal_add hε2.le hε2.le]
        congr 1; ring

end Thm18Asm
end QuantumZipper
