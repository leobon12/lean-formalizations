import QuantumZipper.Proofs.Zipper.D3PlusN2TmZRadTV
import QuantumZipper.Proofs.NonVacuity

/-!
# N2-zero: the circle-average embedding scale tends to `0` in probability

Task N2-TMZERO, input (c) of `N2ZModelLocStmt` and of the heart's mixing step.
`tendsto_prob_Tc_lt`: `P(Tc(c_L) < S) → 0` as `L → ∞`, for every `S`; hence
`tendsto_prob_n2EmbScale_gt`: `P(n2EmbScale L > δ) → 0` for every `δ > 0`.

Route (own wiring of proved results): realize a wedge radial process on `P ⊗ P` from the forward
path `zRadB X r ∘ fst` (`isBrownianReal_zRadB`) and an independent backward path
`WedgeTK.radialBMpos X ∘ snd`; then `Wire5.prob_Tc_lt_le_prob_wedge_high_uncond` (Williams path
decomposition, DMS arXiv:1409.7055 p. 78 claim (b)) and `ZoomRadial.tendsto_prob_wedge_high`.
The event `{Tc < S}` is handled as an arbitrary set (`Measure.prod_prod` needs no measurability).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

theorem tendsto_prob_Tc_lt {γ α r : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hγ : 0 < γ) (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) (S : ℝ) :
    Tendsto (fun L => P {ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω < S})
      atTop (𝓝 0) := by
  set S' := max S 0 with hS'def
  have hS' : 0 ≤ S' := le_max_right _ _
  set B : ℝ≥0 → Ω × Ω → ℝ := fun t ω => zRadB X r t ω.1 with hBdef
  set B' : ℝ≥0 → Ω × Ω → ℝ := fun t ω => WedgeTK.radialBMpos X t ω.2 with hB'def
  have hB : IsBrownianReal B (P.prod P) :=
    NonVacuity.nv_isBrownianReal (measurePreserving_fst (μ := P) (ν := P))
      (isBrownianReal_zRadB hX hr)
  have hB' : IsBrownianReal B' (P.prod P) :=
    NonVacuity.nv_isBrownianReal (measurePreserving_snd (μ := P) (ν := P))
      (WedgeTK.isBrownianReal_radialBMpos hX)
  have hInd : IndepFun (pathOf B) (pathOf B') (P.prod P) :=
    NonVacuity.nv_indepFun_prod (μ := P) (ν := P) (pathOf (zRadB X r))
      (pathOf (WedgeTK.radialBMpos X))
  set A : ℝ → Ω × Ω → ℝ := fun t ω => wedgePath α (Qc γ) (fun s => B s ω) (fun s => B' s ω) t
    with hAdef
  have hA : IsWedgeProcess α (Qc γ) A (P.prod P) := ⟨B, B', hB, hB', hInd, fun ω t => rfl⟩
  have hhigh := (ZoomRadial.tendsto_prob_wedge_high hA hα S').comp (tendsto_n2Lev hγ α r)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hhigh
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [(tendsto_n2Lev hγ α r).eventually_gt_atTop 0] with L hL
  have hle := Wire5.prob_Tc_lt_le_prob_wedge_high_uncond hα hB hB' hInd (A := A)
    (fun ω t => rfl) hL hS'
  have e : {ω : Ω × Ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) B ω < S'} =
      {ω : Ω | ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω < S'} ×ˢ univ := by
    ext ω
    simp only [mem_setOf_eq, mem_prod, mem_univ, and_true]
    exact Iff.rfl
  rw [e, Measure.prod_prod, measure_univ, mul_one] at hle
  refine le_trans (measure_mono ?_) hle
  intro ω hω
  simp only [mem_setOf_eq] at hω ⊢
  exact lt_of_lt_of_le hω (le_max_left _ _)

/-- **The embedding scale tends to `0` in probability.** -/
theorem tendsto_prob_n2EmbScale_gt {γ α r : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hγ : 0 < γ) (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun L => P {ω | δ < n2EmbScale γ α L r X ω}) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_prob_Tc_lt hγ hα hr hX (-Real.log (δ / r))) (fun _ => bot_le)
    (fun L => measure_mono fun ω hω => ?_)
  simp only [mem_setOf_eq, n2EmbScale] at hω ⊢
  set T := ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω
  have h1 : δ / r < Real.exp (-T) := by rw [div_lt_iff₀ hr]; linarith [mul_comm r (Real.exp (-T))]
  have h2 := Real.log_lt_log (div_pos hδ hr) h1
  rw [Real.log_exp] at h2
  linarith

end D3Plus
end QuantumZipper
