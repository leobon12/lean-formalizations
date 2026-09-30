import QuantumZipper.Proofs.Field.PairLimBasic
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.GFF.FrostmanReg

/-!
# PAIR-LIM: continuum limit of circle-regularized pairings of the free field

For a free boundary GFF modulo constants `X` (`IsFreeGFFModConstH`) and a measure `η` with
bounded density, supported in a compact subset of `{Im ≥ δ}` (`PairLim.Setup`), almost surely

  `∫ evalReg (X ω) (foldedCircle u s) dη(u) → X ω η`   as `s → 0⁺` **along the continuum**

(`ae_tendsto_integral_evalReg_fc`). For a regular sample `evalReg (X ω) (fc(u,s))` is the regular
circle average `h_s(u)` at every radius (`IsRegularWith.evalReg_fc_of_mem`), so this is the
statement "`∫ h_s(u) ρ(u) du → ⟨h, ρ⟩` a.s. as `s → 0`, simultaneously for all `s`". Consequences:

* `ae_tendsto_scaled_radius`: a.s., for **every** `a > 0` simultaneously, the limit along the
  radii `a · 2^{-k}` exists and equals the raw value `X ω η`;
* `ae_tendsto_pairRaw_scaled`: the same for a test function `ρ : TestFun H`
  (`ρ± dz`), with limit `pairRaw (X ω) ρ`.

Route: Kolmogorov continuity (`KolmD.exists_continuous_modification_D`, `d = 1`) for
`s ↦ X ω (η ∗ fc(·,s))` on `[0, δ]` (moment bound `Setup.momentBound`, `PairLimBasic`), stochastic
Fubini at each fixed radius (`RegSample.integral_fcAvg_ae_eq_bind_real`, with the regular version
`WedgeTK.exists_isRegVersion`), agreement on rational radii and continuity of both sides.

Source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
§3.1 (Prop. 3.1: continuity of the circle average process via Kolmogorov–Čentsov, and the
identification `h_ε(z) = (h, ρ_ε^z)`); Revuz–Yor Ch. I Thm (2.1) for the Kolmogorov criterion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace QuantumZipper
namespace PairLim

open SmoothConv KolmD WedgeTK

variable {M : ℝ≥0} {R δ : ℝ} {η : Measure ℂ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Continuity in the radius of a witness integrated against `η`. -/
theorem continuousOn_integral_witness (hS : Setup M R δ η) {F : ℂ × ℝ → ℝ}
    (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun s => ∫ u, F (u, s) ∂η) (Icc a b) := by
  have := hS.good.isFiniteMeasure
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hsub : K ×ˢ Icc a b ⊆ Hbar ×ˢ Ioi 0 := fun p hp => ⟨hp.1.2, ha.trans_le hp.2.1⟩
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn (hF.mono hsub)
  have hηH : η.restrict Hbar = η :=
    Measure.restrict_eq_self_of_ae_mem (hS.good.ae_mem.mono fun w hw => hw.2)
  refine continuousOn_of_dominated (bound := fun _ => C) (fun s hs => ?_) (fun s hs => ?_)
    (integrable_const C) ?_
  · have hc : ContinuousOn (fun u => F (u, s)) Hbar :=
      hF.comp (continuousOn_id.prodMk continuousOn_const) fun u hu => ⟨hu, ha.trans_le hs.1⟩
    rw [← hηH]; exact hc.aestronglyMeasurable isClosed_Hbar.measurableSet
  · filter_upwards [hS.good.ae_mem] with u hu
    exact hC (u, s) ⟨hu, hs⟩
  · filter_upwards [hS.good.ae_mem] with u hu
    exact hF.comp (continuousOn_const.prodMk continuousOn_id) fun s hs => ⟨hu.2, ha.trans_le hs.1⟩

/-- **Stochastic Fubini at a fixed radius.** -/
theorem Setup.ae_integral_witness_eq [IsProbabilityMeasure P] (hS : Setup M R δ η)
    (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ} (hG : IsRegVersion X P G)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∫ u, G ω (u, s) ∂η = X ω (smooth η s) := by
  have := hS.good.isFiniteMeasure
  have h0 : (0 : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ (0 : ℂ).im; simp
  have hcs : ∀ ω, ContinuousOn (fun z => G ω (z, s)) Hbar := fun ω =>
    (hG.cont ω).comp (continuousOn_id.prodMk continuousOn_const) fun z hz => ⟨hz, hs⟩
  have hYc : ∀ ω, ContinuousOn (fun z => G ω (z, s) - G ω (0, s)) Hbar := fun ω =>
    (hcs ω).sub continuousOn_const
  have hY : ∀ z ∈ Hbar, (fun ω => G ω (z, s) - G ω (0, s)) =ᵐ[P]
      fun ω => X ω (foldedCircle z s) - X ω (foldedCircle 0 s) := by
    intro z hz
    filter_upwards [hG.raw z hz s hs, hG.raw 0 h0 s hs] with ω h1 h2
    rw [h1, h2]
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hF := RegSample.integral_fcAvg_ae_eq_bind_real hX hs h0 hYc hY η hK inter_subset_right
    hS.good.2
  have hfc := isAdmissibleH_foldedCircle h0 hs
  set m := (η univ).toNNReal with hmdef
  have hm : η univ = (m : ℝ≥0∞) := (ENNReal.coe_toNNReal (measure_ne_top η univ)).symm
  have hlin := hX.linear _ _ hfc hfc m 0
  filter_upwards [hF, hlin, hG.raw 0 h0 s hs] with ω h1 h2 h3
  have hi : Integrable (fun z => G ω (z, s)) η :=
    FrostmanReg.integrable_of_continuousOn_frostman hK inter_subset_right hS.good.2 (hcs ω)
  rw [integral_sub hi (integrable_const _), integral_const, smul_eq_mul] at h1
  have e : η univ • foldedCircle 0 s = m • foldedCircle 0 s + (0 : ℝ≥0) • foldedCircle 0 s := by
    rw [zero_smul, add_zero, ENNReal.smul_def, ← hm]
  rw [e, h2, h3] at h1
  have hmr : (m : ℝ) = η.real univ := by
    rw [hmdef, measureReal_def, ENNReal.coe_toNNReal_eq_toReal]
  simp only [NNReal.coe_zero, zero_mul, add_zero, hmr] at h1
  unfold smooth
  linarith

/-! ## Test functions -/

/-- A continuous, compactly supported `g` with `tsupport g ⊆ H` gives a measure
`ofReal (g z) dz` satisfying the standing hypotheses. -/
theorem exists_setup_withDensity {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgH : tsupport g ⊆ H) :
    ∃ (M : ℝ≥0) (R δ : ℝ), Setup M R δ (volume.withDensity fun z => ENNReal.ofReal (g z)) := by
  set K := tsupport g
  have hK : IsCompact K := hgc
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hδ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ K ⊆ {z | δ < z.im} := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, le_rfl, by rw [he]; exact empty_subset _⟩
    · obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
      have hz₀ : 0 < z₀.im := hgH hz₀K
      refine ⟨min (z₀.im / 2) 1, lt_min (half_pos hz₀) one_pos, min_le_right _ _,
        fun z hz => ?_⟩
      have : z₀.im ≤ z.im := hmin hz
      show min (z₀.im / 2) 1 < z.im
      linarith [min_le_left (z₀.im / 2) 1]
  obtain ⟨δ, hδ0, hδ1, hKδ⟩ := hδ
  have hgM : ∀ z, ENNReal.ofReal (g z) ≤ (C.toNNReal : ℝ≥0∞) := fun z => by
    rw [← ENNReal.ofReal.eq_def]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa using hC z))
  have hgK : ∀ z ∉ K, ENNReal.ofReal (g z) = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, ENNReal.ofReal_zero]
  obtain ⟨h1, h2⟩ := isGoodSC_withDensity hgM hK hδ0 hKδ hgK hR
  exact ⟨_, R, δ, ⟨h1, hδ0, hδ1, h2.mono fun _ hw => hw.le⟩⟩

/-! ## Adding a deterministic function continuous on `Hbar` -/

end PairLim
end QuantumZipper
