import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinCirc
import QuantumZipper.Proofs.Zipper.D3PlusN2H2Obstr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 free-field regularization: the deterministic core (task N2H2-FREE)

On a good sample `x` (regular with witness `g`, raw dyadic semicircle values about `0`:
`GoodRad x g`), whose radial profile `ρ ↦ g(0, ρ)` agrees on `(0, R]` with a log-dominated
profile `ψ` (`LogDom`), and whose regularizations converge to the raw value at every dyadic
folded circle, the nested regularization of the lateral part of `x − c` at a finite measure `ν`
carried by a compact part of `Hbar \ {0}` inside `ball 0 R` (with `log‖·‖` integrable and
convergent regularizations of `g`) equals the single one:

  `evalReg (lateralPart (x − c)) ν = evalReg x ν − ∫ radAvgReg x ‖w‖ dν`

(`evalReg_lat_sub_const_of_good`), and its rescaled form `evalReg_lat_sub_const_win`.

Source: the pathwise splitting `h = h† + h_{|·|}(0)` of Duplantier–Miller–Sheffield,
arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78. The bookkeeping (the constant drops out on
the convergence event, `N2H2Obs.lateralPart_addConst_of_good`; dominated convergence through the
deterministic core `evalReg_split_core` with `M = Z = x`, `α = c₀ = 0`) is own elementary work.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK N2H2Obs

/-- A constant radial profile is log-dominated. -/
theorem logDom_const_free (k R : ℝ) : LogDom (fun _ => k) R |k| 0 :=
  ⟨measurable_const, continuousOn_const, le_rfl, fun ρ _ _ => by simp⟩

/-- Support of a folded circle: in `Hbar`, off `0`, inside `closedBall 0 (‖d‖ + s)`. -/
theorem ae_fc_supp_free (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ u ∂foldedCircle d s, u ∈ Hbar ∧ u ≠ 0 ∧ ‖u‖ ≤ ‖d‖ + s := by
  have hb : ∀ᵐ u ∂foldedCircle d s, u ∈ Metric.closedBall ((0 : ℝ) : ℂ) (‖d‖ + s) :=
    (ae_iff (p := fun u => u ∈ Metric.closedBall ((0 : ℝ) : ℂ) (‖d‖ + s))).2
      (by simpa only [Set.compl_def] using foldedCircle_compl_closedBall (d := d) hs)
  filter_upwards [RegClosure.fc_ae_mem_Hbar d s, F1.ae_ne_zero_fc d hs, hb] with u h1 h2 h3
  exact ⟨h1, h2, by simpa using h3⟩

section Core

variable {x : FieldSample} {g : ℂ × ℝ → ℝ} {ψ : ℝ → ℝ} {R C D : ℝ}

/-- The lateral part of `x − c` at a folded circle where the regularization converges to the
raw value: the constant drops out and the radial part is `ψ`. -/
theorem lateralPart_sub_const_fc (hg : GoodRad x g) (hψ : LogDom ψ R C D) (hR : 0 < R)
    (hψg : ∀ ρ, 0 < ρ → ρ ≤ R → g (0, ρ) = ψ ρ) (c : ℝ) {d : ℂ} {s : ℝ} (hs : 0 < s)
    (hds : ‖d‖ + s ≤ R)
    (hE : Tendsto (fun k => ∫ w, avgReg x k w ∂foldedCircle d s) atTop
      (𝓝 (x (foldedCircle d s)))) :
    lateralPart (fun μ => x μ - (μ Set.univ).toReal * c) (foldedCircle d s) =
      x (foldedCircle d s) - ∫ u, ψ ‖u‖ ∂foldedCircle d s := by
  have e : (fun μ : Measure ℂ => x μ - (μ Set.univ).toReal * c) = addConst x (-c) := by
    funext μ; simp only [addConst]; ring
  have hsupp := ae_fc_supp_free d hs
  have hpt : ∀ᵐ u ∂foldedCircle d s, ψ ‖u‖ = g (0, ‖u‖) := by
    filter_upwards [hsupp] with u hu
    exact (hψg _ (norm_pos_iff.2 hu.2.1) (hu.2.2.trans hds)).symm
  have hψi : Integrable (fun u : ℂ => ψ ‖u‖) (foldedCircle d s) :=
    hψ.integrable_comp_norm hR hds hsupp (CoordReg.integrable_log_norm_foldedCircle d s)
  rw [e, lateralPart_addConst_of_good hg (-c) (isAdmissibleH_foldedCircle' d hs)
    (hψi.congr hpt), if_pos ⟨_, hE⟩]
  unfold lateralPart evalReg
  rw [hE.limUnder_eq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hsupp] with u hu
  rw [hg.radAvgReg_eq (norm_pos_iff.2 hu.2.1), hψg _ (norm_pos_iff.2 hu.2.1) (hu.2.2.trans hds)]

/-- **Nested regularization equals single regularization** (deterministic core). -/
theorem evalReg_lat_sub_const_of_good (hg : GoodRad x g) (hψ : LogDom ψ R C D) (hR : 0 < R)
    (hψg : ∀ ρ, 0 < ρ → ρ ≤ R → g (0, ρ) = ψ ρ)
    (hE : ∀ n k : ℕ, ∀ d ∈ range (dyadicRoundC n),
      Tendsto (fun k' => ∫ w, avgReg x k' w ∂foldedCircle d (radius k)) atTop
        (𝓝 (x (foldedCircle d (radius k)))))
    (c : ℝ) {ν : Measure ℂ} [IsFiniteMeasure ν] {m : ℝ} (hm : m < R)
    (hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) ν) {l : ℝ}
    (hGl : Tendsto (fun k => ∫ w, g (w, radius k) ∂ν) atTop (𝓝 l)) :
    evalReg (lateralPart fun μ => x μ - (μ Set.univ).toReal * c) ν =
      evalReg x ν - ∫ w, radAvgReg x ‖w‖ ∂ν := by
  set S := Metric.closedBall (0 : ℂ) m ∩ Hbar with hS_def
  have hSc : IsCompact S := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hνS : ∀ᵐ w ∂ν, w ∈ S := by
    filter_upwards [hν] with w hw
    exact ⟨by rw [mem_closedBall_zero_iff]; exact hw.2.2, hw.1⟩
  have hGi : ∀ k : ℕ, Integrable (fun w => g (w, radius k)) ν := fun k => by
    have hc : ContinuousOn (fun w => g (w, radius k)) S :=
      hg.1.1.comp (continuousOn_id.prodMk continuousOn_const)
        (fun z hz => ⟨hz.2, radius_pos k⟩)
    have := hc.integrableOn_compact (μ := ν) hSc
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hνS] at this
  have hM : ∀ n k, ∀ d ∈ range (dyadicRoundC n), ‖d‖ + radius k ≤ R →
      x (foldedCircle d (radius k)) = x (foldedCircle d (radius k)) +
        ∫ u, (0 : ℝ) * -Real.log ‖u‖ ∂foldedCircle d (radius k) + 0 := by
    intro n k d _ _; simp
  have hY : ∀ n k, ∀ d ∈ range (dyadicRoundC n), ‖d‖ + radius k ≤ R →
      (lateralPart fun μ => x μ - (μ Set.univ).toReal * c) (foldedCircle d (radius k)) =
        x (foldedCircle d (radius k)) - ∫ u, ψ ‖u‖ ∂foldedCircle d (radius k) :=
    fun n k d hd hdk => lateralPart_sub_const_fc hg hψ hR hψg c (radius_pos k) hdk (hE n k d hd)
  have hZ : ∀ k, ∀ w ∈ Hbar, ‖w‖ + radius k < R →
      Tendsto (fun n => x (foldedCircle (dyadicRoundC n w) (radius k))) atTop
        (𝓝 (g (w, radius k))) := fun k w hw _ => hg.1.2.1 k w hw
  obtain ⟨-, hsplit⟩ := evalReg_split_core (M := x)
    (Y := lateralPart fun μ => x μ - (μ Set.univ).toReal * c) (Z := x)
    (Φ := fun k w => g (w, radius k)) (α := 0) (c₀ := 0) hψ hR le_rfl hm hM hY hZ hν hlog
    (Eventually.of_forall hGi) hGl
  have hrad : ∫ w, radAvgReg x ‖w‖ ∂ν = ∫ w, (ψ ‖w‖ + 0 * -Real.log ‖w‖ + 0) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hν] with w hw
    rw [hg.radAvgReg_eq (norm_pos_iff.2 hw.2.1),
      hψg _ (norm_pos_iff.2 hw.2.1) (hw.2.2.trans hm.le)]
    ring
  rw [hrad, hsplit]
  ring

/-- **Rescaled form** at a window measure `μ` and scale `a > 0`. -/
theorem evalReg_lat_sub_const_win (hg : GoodRad x g) (hψ : LogDom ψ R C D) (hR : 0 < R)
    (hψg : ∀ ρ, 0 < ρ → ρ ≤ R → g (0, ρ) = ψ ρ)
    (hE : ∀ n k : ℕ, ∀ d ∈ range (dyadicRoundC n),
      Tendsto (fun k' => ∫ w, avgReg x k' w ∂foldedCircle d (radius k)) atTop
        (𝓝 (x (foldedCircle d (radius k)))))
    (c : ℝ) {a : ℝ} (ha : 0 < a) {μ : Measure ℂ} [IsFiniteMeasure μ] {m : ℝ} (hm : m < R)
    (hν : ∀ᵐ w ∂(μ.map fun z => (a : ℂ) * z), w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m)
    (hlog : Integrable (fun w => Real.log ‖w‖) (μ.map fun z => (a : ℂ) * z)) {l : ℝ}
    (hGl : Tendsto (fun k => ∫ w, g (w, radius k) ∂(μ.map fun z => (a : ℂ) * z)) atTop
      (𝓝 l)) :
    evalReg (lateralPart fun μ => x μ - (μ Set.univ).toReal * c)
        (μ.map fun z => (a : ℂ) * z) =
      evalReg x (μ.map fun z => (a : ℂ) * z) - ∫ z, radAvgReg x (a * ‖z‖) ∂μ := by
  rw [evalReg_lat_sub_const_of_good hg hψ hR hψg hE c hm hν hlog hGl,
    (F1.measurableEmbedding_mul_real ha).integral_map]
  simp only [F1.norm_mul_real ha]

end Core

end D3Plus
end QuantumZipper
