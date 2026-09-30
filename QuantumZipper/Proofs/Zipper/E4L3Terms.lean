import QuantumZipper.Proofs.Zipper.E4L3Conv
import QuantumZipper.Proofs.Loewner.CaraR1

/-!
# E4-L3, deterministic inputs III: the collision field and the coordinate shifts

`handoff/E4.md`, item L3. Defines the collision target field `targetColl` (the statement of
`handoff/E-PLAN-2-statements.lean.txt`, `EPLAN2.targetColl`, verbatim: `targetField` with the
image `F x` of the point replaced by `0`; it is *not* defined through `targetField` at `τ_x`,
where `realRevMap` is a junk value) and proves, as `s ↑ τ = τ_x`:

* `tendsto_realRevMap_hit`: `realRevMap V s x → 0` for `x ≠ 0` (R1, `CaraR`; the negative side
  as in `E4Grid.tendsto_realRevMap_hit_neg` of `E4LimBasic`, repeated here to keep the files
  independent);
* `tendsto_energy`: the Neumann energy of `ϖ_s − ϖ_τ` tends to `0`;
* `tendsto_shift_fc`, `tendsto_shift_varpi`: convergence of the shift integrals;
* `coordsFull_targetColl`: the coordinates of `targetColl`.

Own elementary arguments (dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace E4Grid

open E1 TwoPoint PalmNorm B2 RealLine CoordsFull

/-- The collision target field: `targetField` with `F x` replaced by `0`
(`EPLAN2.targetColl` of `handoff/E-PLAN-2-statements.lean.txt`). -/
def targetColl (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (Y : FieldSample) : FieldSample :=
  addConst (PalmNorm.normAt (varpiT V t ϖ)
    (ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) + Y)) (-(qt κ V t ϖ))

theorem coordsFull_targetColl (κ : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (Y : FieldSample) :
    coordsFull (targetColl κ V t ϖ Y) = fun j =>
      (ofFun (shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0)
          (foldedCircle (fullIndex j).1 (fullIndex j).2) -
        ofFun (shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) (varpiT V t ϖ) -
          qt κ V t ϖ) +
      (Y (foldedCircle (fullIndex j).1 (fullIndex j).2) - Y (varpiT V t ϖ)) := by
  funext j
  simp only [coordsFull, targetColl, normAt, addConst, Pi.add_apply, measure_univ,
    ENNReal.toReal_one, mul_one]
  ring

variable {V : ℝ → ℝ}

/-- R1 on both sides: the real flow of `x ≠ 0` tends to `0` at its hitting time. -/
theorem tendsto_realRevMap_hit (hV : Continuous V) (hV0 : V 0 = 0) {x τ : ℝ} (hx : x ≠ 0)
    (hτ : realHitTime V x = ENNReal.ofReal τ) :
    Tendsto (fun s => realRevMap V s x) (𝓝[<] τ) (𝓝 0) := by
  rcases hx.lt_or_gt with hx | hx
  · have hxV : x < V 0 := by rw [hV0]; exact hx
    have hτ' : realHitTime (-V) (-x) = ENNReal.ofReal τ := by
      rw [CaraR.realHitTime_neg (W := V)]; exact hτ
    have h := (CaraR.tendsto_realRevMap_hitTime hV.neg (x := -x)
      (by simp only [Pi.neg_apply]; linarith) hτ').neg
    rw [neg_zero] at h
    have hτpos : 0 < τ := by
      have := realHitTime_pos hV hxV.ne
      rw [hτ] at this
      exact ENNReal.ofReal_pos.1 this
    refine h.congr' (eventually_of_mem (Ioo_mem_nhdsLT hτpos) fun s hs => ?_)
    have hsol : ∃ u, IsRealRevSol V (-(-x)) s u := by
      rw [neg_neg]
      exact exists_isRealRevSol_of_lt_realHitTime
        (by rw [hτ]; exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 hs.2)
    rw [CaraR.realRevMap_neg hV hs.1.le hsol, neg_neg, neg_neg]
  · exact CaraR.tendsto_realRevMap_hitTime hV (by rw [hV0]; exact hx) hτ

variable {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} {α C τ : ℝ}

/-- **Energy continuity**: `kernelCov2 N (ϖ_s, ϖ_τ) (ϖ_s, ϖ_τ) → 0`. -/
theorem tendsto_energy (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0)
    (hα : 0 < α) (hF : IsFrostman ϖ α C) (hτ : 0 < τ) :
    Tendsto (fun s => kernelCov2 neumannH (varpiT V s ϖ, varpiT V τ ϖ)
      (varpiT V s ϖ, varpiT V τ ϖ)) (𝓝[<] τ) (𝓝 0) := by
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hK hKH hϖK hα hF hs
  have h1 := tendsto_kk hV hK hKH hϖK hα hF hτ
  have h2 := tendsto_kernelCov_left hV hK hKH hϖK hτ (hg τ hτ.le)
  have h3 := ((h1.sub h2).sub h2).add_const
    (kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ))
  rw [show kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) -
      kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) -
      kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) +
      kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ) = 0 by ring] at h3
  refine h3.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
  simp only [kernelCov2]
  rw [CoordChange.kernelCov_comm_of_admissible (hg τ hτ.le).adm (hg s hs.1.le).adm]

/-- The shift integral against a fixed good measure `ν` (a folded circle). -/
theorem tendsto_shift_fc (κ : ℝ) (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hα : 0 < α) (hF : IsFrostman ϖ α C) (hτ : 0 < τ) {a : ℝ → ℝ}
    (ha : Tendsto a (𝓝[<] τ) (𝓝 0)) {ν : Measure ℂ} (hν : GoodMeas ν) :
    Tendsto (fun s => ∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (a s) u ∂ν)
      (𝓝[<] τ) (𝓝 (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V τ ϖ) 0 u ∂ν)) := by
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hK hKH hϖK hα hF hs
  have hcomm : ∀ s, 0 ≤ s → kernelCov neumannH ν (varpiT V s ϖ) =
      kernelCov neumannH (varpiT V s ϖ) ν := fun s hs =>
    CoordChange.kernelCov_comm_of_admissible hν.adm (hg s hs).adm
  rw [integral_shiftFun_eq hν (hg τ hτ.le).adm, hcomm τ hτ.le]
  have hN : Tendsto (fun s => neuPot ν (a s)) (𝓝[<] τ) (𝓝 (neuPot ν ((0 : ℝ) : ℂ))) :=
    (hν.continuous_neuPot.tendsto _).comp ((Complex.continuous_ofReal.tendsto 0).comp ha)
  refine (tendsto_const_nhds.add (Tendsto.const_mul _ (hN.sub
    (tendsto_kernelCov_left hV hK hKH hϖK hτ hν)))).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
  rw [integral_shiftFun_eq hν (hg s hs.1.le).adm, hcomm s hs.1.le]

theorem measurable_h0rev (κ : ℝ) : Measurable (h0rev κ) := by
  show Measurable fun z : ℂ => 2 / Real.sqrt κ * Real.log ‖z‖
  exact measurable_const.mul (Real.measurable_log.comp measurable_norm)

theorem continuousOn_h0rev_snd (κ : ℝ) (a₀ : ℝ) :
    ContinuousOn (Function.uncurry fun (_ : ℝ) (w : ℂ) => h0rev κ w)
      (Icc (a₀ - 1) (a₀ + 1) ×ˢ H) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  have hp0 : p.2 ≠ 0 := fun h => by
    have := hp.2; rw [h] at this; exact (lt_irrefl _ (show (0 : ℂ).im > 0 from this))
  show ContinuousAt (fun p : ℝ × ℂ => 2 / Real.sqrt κ * Real.log ‖p.2‖) p
  exact continuousAt_const.mul (ContinuousAt.log (by fun_prop) (norm_ne_zero_iff.2 hp0))

theorem continuousOn_neumannH_real (a₀ : ℝ) :
    ContinuousOn (Function.uncurry fun (a : ℝ) (w : ℂ) => neumannH (a : ℂ) w)
      (Icc (a₀ - 1) (a₀ + 1) ×ˢ H) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  have hw : 0 < p.2.im := hp.2
  have h1 : (p.1 : ℂ) ≠ p.2 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have h2 : (p.1 : ℂ) ≠ conj p.2 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  show ContinuousAt (fun p : ℝ × ℂ => neumannH (p.1 : ℂ) p.2) p
  unfold neumannH
  refine ((ContinuousAt.log (by fun_prop) ?_).neg).sub (ContinuousAt.log (by fun_prop) ?_)
  · exact norm_ne_zero_iff.2 (sub_ne_zero.2 h1)
  · exact norm_ne_zero_iff.2 (sub_ne_zero.2 h2)

/-- The shift integral against `ϖ_s` itself. -/
theorem tendsto_shift_varpi (κ : ℝ) (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hα : 0 < α) (hF : IsFrostman ϖ α C) (hτ : 0 < τ) {a : ℝ → ℝ}
    (ha : Tendsto a (𝓝[<] τ) (𝓝 0)) :
    Tendsto (fun s => ∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (a s) u
        ∂(varpiT V s ϖ)) (𝓝[<] τ)
      (𝓝 (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V τ ϖ) 0 u ∂(varpiT V τ ϖ))) := by
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hK hKH hϖK hα hF hs
  have eh : ∀ s, 0 ≤ s → ∫ u, h0rev κ u ∂(varpiT V s ϖ) = ∫ z, h0rev κ (revMap V s z) ∂ϖ :=
    fun s hs => integral_map (measurable_revMap hV hs).aemeasurable
      (measurable_h0rev κ).aestronglyMeasurable
  have eN : ∀ s, 0 ≤ s → ∀ b : ℝ, neuPot (varpiT V s ϖ) (b : ℂ) =
      ∫ z, neumannH (b : ℂ) (revMap V s z) ∂ϖ := fun s hs b =>
    integral_map (measurable_revMap hV hs).aemeasurable
      (measurable_neumannH.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hH := tendsto_integral_comp_revMap hV hK hKH hϖK hτ (G := fun _ w => h0rev κ w)
    ((measurable_h0rev κ).comp measurable_snd) (a := fun _ => 0) (a₀ := 0) tendsto_const_nhds
    (continuousOn_h0rev_snd κ 0)
  have hN := tendsto_integral_comp_revMap hV hK hKH hϖK hτ
    (G := fun (b : ℝ) w => neumannH (b : ℂ) w)
    (measurable_neumannH.comp ((Complex.measurable_ofReal.comp measurable_fst).prodMk
      measurable_snd)) ha (continuousOn_neumannH_real 0)
  rw [integral_shiftFun_eq (hg τ hτ.le) (hg τ hτ.le).adm, eh τ hτ.le, eN τ hτ.le]
  refine (hH.add (Tendsto.const_mul _ (hN.sub
    (tendsto_kk hV hK hKH hϖK hα hF hτ)))).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
  rw [integral_shiftFun_eq (hg s hs.1.le) (hg s hs.1.le).adm, eh s hs.1.le, eN s hs.1.le]

end E4Grid
end QuantumZipper
