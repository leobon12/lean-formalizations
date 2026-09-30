import QuantumZipper.Proofs.Zipper.E4L3Terms
import QuantumZipper.Proofs.Zipper.RegContMain
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# E4-L3: right-side law continuity at the collision time

`handoff/E4.md`, item L3, for Sheffield, arXiv:1012.4797, proof of Lemma 5.6 (pp. 66–68)
(the passage from the Palm-zip identity at live times to the collision time `τ_x`), with
Thm 4.5 (p. 51) for the normalized field. For a continuous driver `V` with `V 0 = 0`, a point
`x ≠ 0` with hitting time `τ` (`realHitTime V x = ofReal τ`), a normalizer `ϖ` and a free field
`X'` on `(Ω', P')`, and a bounded continuous functional `f ≤ 1` of finitely many coordinates:

```
theorem tendsto_lintegral_targetField_coll :
    Tendsto (fun s => ∫⁻ ω', f (fun j => coordsFull (targetField κ V s ϖ x (X' ω')) (I j)) ∂P')
      (𝓝[<] τ) (𝓝 (∫⁻ ω', f (fun j => coordsFull (targetColl κ V τ ϖ (X' ω')) (I j)) ∂P'))
```

Proof: each coordinate is `c_j(s) + (X'(μ_j) − X'(ϖ_τ)) − (X'(ϖ_s) − X'(ϖ_τ))`; the
deterministic parts converge (`E4L3Terms`, with `realRevMap V s x → 0` by R1), and
`X'(ϖ_s) − X'(ϖ_τ)` is a centred Gaussian whose variance, the Neumann energy of `ϖ_s − ϖ_τ`,
tends to `0` (`tendsto_energy`), so it tends to `0` in probability (Chebyshev). Convergence in
probability implies convergence in distribution (mathlib,
`TendstoInMeasure.tendstoInDistribution`), which is tested against the bounded continuous `f`.
Own elementary argument; no published source beyond the paper's implicit use.
-/

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace QuantumZipper
namespace E4Grid

open E1 TwoPoint PalmNorm B2 RealLine CoordsFull

/-- Abstract form: a shift `c(s) → c₀` plus a common noise `U` minus a scalar noise `Z_s → 0` in
probability converges in law, tested against a bounded continuous `f ≤ 1`. -/
theorem tendsto_lintegral_of_shift {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {m : ℕ} {l : Filter ℝ} [l.NeBot] [l.IsCountablyGenerated]
    (c : ℝ → Fin m → ℝ) (c₀ : Fin m → ℝ) (Z : ℝ → Ω' → ℝ) (U : Ω' → Fin m → ℝ)
    (hUm : Measurable U) (hZm : ∀ s, Measurable (Z s)) (hc : Tendsto c l (𝓝 c₀))
    (hZ : ∀ ε : ℝ, 0 < ε → Tendsto (fun s => P' {ω | ε ≤ |Z s ω|}) l (𝓝 0))
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ y, f y ≤ 1) :
    Tendsto (fun s => ∫⁻ ω, f (fun j => c s j + U ω j - Z s ω) ∂P') l
      (𝓝 (∫⁻ ω, f (fun j => c₀ j + U ω j) ∂P')) := by
  set Y : ℝ → Ω' → Fin m → ℝ := fun s ω j => c s j + U ω j - Z s ω with hYdef
  set Y₀ : Ω' → Fin m → ℝ := fun ω j => c₀ j + U ω j with hY₀def
  have hYm : ∀ s, Measurable (Y s) := fun s => measurable_pi_iff.2 fun j =>
    (measurable_const.add ((measurable_pi_apply j).comp hUm)).sub (hZm s)
  have hTIM : TendstoInMeasure P' Y l Y₀ := by
    rw [tendstoInMeasure_iff_dist]
    intro ε hε
    have hev : ∀ᶠ s in l, dist (c s) c₀ < ε / 2 := hc (Metric.ball_mem_nhds _ (half_pos hε))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hZ (ε / 2) (half_pos hε))
      (Eventually.of_forall fun _ => zero_le) (hev.mono fun s hs => measure_mono ?_)
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hd : dist (Y s ω) (Y₀ ω) ≤ dist (c s) c₀ + |Z s ω| := by
      refine (dist_pi_le_iff (by positivity)).2 fun j => ?_
      have hj := dist_le_pi_dist (c s) c₀ j
      simp only [hYdef, hY₀def, Real.dist_eq] at hj ⊢
      calc |c s j + U ω j - Z s ω - (c₀ j + U ω j)| = |(c s j - c₀ j) - Z s ω| := by ring_nf
        _ ≤ |c s j - c₀ j| + |Z s ω| := abs_sub _ _
        _ ≤ _ := by linarith
    linarith
  have hTD := hTIM.tendstoInDistribution (fun s => (hYm s).aemeasurable)
  have hne : ∀ y, f y ≠ ⊤ := fun y => ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 y)
  have hcont : Continuous fun y => (f y).toNNReal :=
    ENNReal.continuousOn_toNNReal.comp_continuous hf hne
  have hb : ∀ y, ((f y).toNNReal : ℝ) ≤ 1 := fun y => by
    rw [ENNReal.coe_toNNReal_eq_toReal]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hf1 y)
  set g : (Fin m → ℝ) →ᵇ ℝ≥0 := BoundedContinuousFunction.mkOfBound
    ⟨fun y => (f y).toNNReal, hcont⟩ 1 fun y y' => by
      rw [NNReal.dist_eq]
      have := hb y; have := hb y'
      have := (f y).toNNReal.coe_nonneg; have := (f y').toNNReal.coe_nonneg
      rw [abs_le]; constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith
  have e : ∀ y, ((g y : ℝ≥0) : ℝ≥0∞) = f y := fun y => ENNReal.coe_toNNReal (hne y)
  have key := (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 hTD.tendsto) g
  simp only [ProbabilityMeasure.coe_mk, e] at key
  have hY₀m : Measurable Y₀ := measurable_pi_iff.2 fun j =>
    measurable_const.add ((measurable_pi_apply j).comp hUm)
  rw [lintegral_map hf.measurable hY₀m] at key
  exact key.congr fun s => lintegral_map hf.measurable (hYm s)

variable {V : ℝ → ℝ} {ϖ : Measure ℂ}

/-- **E4-L3.** Right-side law continuity at the hitting time `τ` of `x`. -/
theorem tendsto_lintegral_targetField_coll (κ : ℝ) (hV : Continuous V) (hV0 : V 0 = 0)
    {x τ : ℝ} (hx : x ≠ 0) (hτ : realHitTime V x = ENNReal.ofReal τ) (hϖ : IsNormalizer ϖ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X' : Ω' → FieldSample} (hX' : IsFreeGFFModConstH X' P') {m : ℕ} (I : Fin m → ℕ)
    {f : (Fin m → ℝ) → ℝ≥0∞} (hf : Continuous f) (hf1 : ∀ y, f y ≤ 1) :
    Tendsto (fun s => ∫⁻ ω', f (fun j => coordsFull (targetField κ V s ϖ x (X' ω')) (I j)) ∂P')
      (𝓝[<] τ)
      (𝓝 (∫⁻ ω', f (fun j => coordsFull (targetColl κ V τ ϖ (X' ω')) (I j)) ∂P')) := by
  have := hϖ.prob
  obtain ⟨K, hKc, hKH, hK0⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  have hτpos : 0 < τ := by
    have := realHitTime_pos hV (show x ≠ V 0 by rw [hV0]; exact hx)
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  have ha := tendsto_realRevMap_hit hV hV0 hx hτ
  have hg := fun s (hs : 0 ≤ s) => varpiT_good hV hKc hKH hK0 hα hF hs
  set μj : Fin m → Measure ℂ := fun j => foldedCircle (fullIndex (I j)).1 (fullIndex (I j)).2
  have hμ : ∀ j, GoodMeas (μj j) := fun j => fc_good _ (by simp only [fullIndex]; positivity)
  set c : ℝ → Fin m → ℝ := fun s j =>
    (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (realRevMap V s x) u ∂μj j) -
      (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V s ϖ) (realRevMap V s x) u
        ∂varpiT V s ϖ) - qt κ V s ϖ
  set c₀ : Fin m → ℝ := fun j =>
    (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V τ ϖ) 0 u ∂μj j) -
      (∫ u, shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V τ ϖ) 0 u ∂varpiT V τ ϖ) - qt κ V τ ϖ
  set Z : ℝ → Ω' → ℝ := fun s ω => X' ω (varpiT V s ϖ) - X' ω (varpiT V τ ϖ)
  set U : Ω' → Fin m → ℝ := fun ω j => X' ω (μj j) - X' ω (varpiT V τ ϖ)
  have eL : ∀ s ω, (fun j => coordsFull (targetField κ V s ϖ x (X' ω)) (I j)) =
      fun j => c s j + U ω j - Z s ω := fun s ω => by
    funext j
    simp only [coordsFull_targetField, c, U, Z, μj, ofFun]
    ring
  have eR : ∀ ω, (fun j => coordsFull (targetColl κ V τ ϖ (X' ω)) (I j)) =
      fun j => c₀ j + U ω j := fun ω => by
    funext j
    simp only [coordsFull_targetColl, c₀, U, μj, ofFun]
  simp only [eL, eR]
  have hUm : Measurable U := measurable_pi_iff.2 fun j =>
    (hX'.measurable_coord _).sub (hX'.measurable_coord _)
  have hZm : ∀ s, Measurable (Z s) := fun s =>
    (hX'.measurable_coord _).sub (hX'.measurable_coord _)
  refine tendsto_lintegral_of_shift c c₀ Z U hUm hZm ?_ ?_ hf hf1
  · refine tendsto_pi_nhds.2 fun j => ?_
    exact ((tendsto_shift_fc κ hV hKc hKH hK0 hα hF hτpos ha (hμ j)).sub
      (tendsto_shift_varpi κ hV hKc hKH hK0 hα hF hτpos ha)).sub
      (tendsto_qt κ hV hKc hKH hK0 hτpos)
  · intro ε hε
    have hε2 : ENNReal.ofReal (ε ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    set g2 := gaussianAbsMoment (2 * 1)
    have hE := tendsto_energy hV hKc hKH hK0 hα hF hτpos
    have hlim : Tendsto (fun s => ENNReal.ofReal (|kernelCov2 neumannH (varpiT V s ϖ,
        varpiT V τ ϖ) (varpiT V s ϖ, varpiT V τ ϖ)| ^ 1 * g2) / ENNReal.ofReal (ε ^ 2))
        (𝓝[<] τ) (𝓝 0) := by
      have h1 : Tendsto (fun s => |kernelCov2 neumannH (varpiT V s ϖ, varpiT V τ ϖ)
          (varpiT V s ϖ, varpiT V τ ϖ)| ^ 1 * g2) (𝓝[<] τ) (𝓝 0) := by
        simpa using (hE.abs.pow 1).mul_const g2
      have h2 := ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal h1) (Or.inr hε2)
      simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhdsLT hτpos] with s hs
    have hs1 := (hg s hs.1.le).prob
    have hτ1 := (hg τ hτpos.le).prob
    have hmass : varpiT V s ϖ univ = varpiT V τ ϖ univ := by simp only [measure_univ]
    have hL := RegCont.lintegral_pow_diff_le hX' (hg s hs.1.le).adm (hg τ hτpos.le).adm hmass 1
      le_rfl
    calc P' {ω | ε ≤ |Z s ω|}
        ≤ P' {ω | ENNReal.ofReal (ε ^ 2) ≤ ENNReal.ofReal (|Z s ω| ^ (2 * 1))} := by
          refine measure_mono fun ω hω => ?_
          simp only [mem_ofPred_eq] at hω ⊢
          exact ENNReal.ofReal_le_ofReal (by
            rw [mul_one]; exact pow_le_pow_left₀ hε.le hω 2)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (|Z s ω| ^ (2 * 1)) ∂P') / ENNReal.ofReal (ε ^ 2) :=
          meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp
            ((continuous_abs.measurable.comp (hZm s)).pow_const _)).aemeasurable hε2 ENNReal.ofReal_ne_top
      _ ≤ _ := ENNReal.div_le_div_right hL _

end E4Grid
end QuantumZipper
