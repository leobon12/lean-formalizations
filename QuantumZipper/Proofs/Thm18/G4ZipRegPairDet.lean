import QuantumZipper.Proofs.Thm18.G4ZipRegCore
import QuantumZipper.Proofs.LQG.GoodMeasurableReg
import QuantumZipper.Proofs.Field.PairLim

/-!
# Theorem 1.8, node G4-ZIPREG: continuum limits as a countable (measurable) condition

Deterministic part of the proof of `WedgePairContStmt` (`G4ZipRegCore.lean`). For a regular
sample `x` and a test measure `μ = g dz` (`g` continuous, compactly supported in `ℍ`), the
smoothed pairing `G(s) = ∫ evalReg x (fc(u,s)) dμ(u)` is integrable and continuous on `(0,∞)`
(`integrable_evalReg_fc_tmeas`, `continuousOn_pairSm`). Hence it has a limit as `s → 0⁺` iff it is
Cauchy along the positive rationals (`CauchyQ`, `exists_tendsto_of_cauchyQ`,
`cauchyQ_of_tendsto`), which is a measurable event of the field (`measurable_cauchyQ`) that only
reads the regularization (`cauchyQ_reconstruct`), so it can be transported along a law identity
of the data (`WedgeBdry.ae_of_fieldLawFull_eq`).

**Own elementary argument.**
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZipReg

/-- The circle-smoothed pairing `s ↦ ∫ evalReg x (fc(u,s)) g⁺(u) du`. -/
def pairSm (x : FieldSample) (g : ℂ → ℝ) (s : ℝ) : ℝ :=
  ∫ u, evalReg x (foldedCircle u s) ∂G1.tmeas g

/-- Cauchy condition along the positive rationals. -/
def CauchyQ (G : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, ∃ m : ℕ, ∀ q q' : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 / ((m : ℝ) + 1) → 0 < (q' : ℝ) →
    (q' : ℝ) < 1 / ((m : ℝ) + 1) → |G q - G q'| ≤ 1 / ((n : ℝ) + 1)

theorem le_of_forall_rat {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContinuousOn f U)
    {c : ℝ} (h : ∀ q : ℚ, (q : ℝ) ∈ U → f q ≤ c) {y : ℝ} (hy : y ∈ U) : f y ≤ c := by
  by_contra hlt
  rw [not_le] at hlt
  have hev : ∀ᶠ z in 𝓝 y, c < f z ∧ z ∈ U :=
    ((hf.continuousAt (hU.mem_nhds hy)).eventually (lt_mem_nhds hlt)).and (hU.mem_nhds hy)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y - ε < y + ε by linarith)
  have hq := hball (y := (q : ℝ)) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  exact absurd (h q hq.2) (not_le.2 hq.1)

theorem exists_tendsto_of_cauchyQ {G : ℝ → ℝ} (hG : ContinuousOn G (Ioi 0)) (hC : CauchyQ G) :
    ∃ L, Tendsto G (𝓝[>] 0) (𝓝 L) := by
  have hreal : ∀ n : ℕ, ∃ m : ℕ, ∀ s s' : ℝ, s ∈ Ioo 0 (1 / ((m : ℝ) + 1)) →
      s' ∈ Ioo 0 (1 / ((m : ℝ) + 1)) → |G s - G s'| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨m, hm⟩ := hC n
    refine ⟨m, ?_⟩
    have hsub : Ioo 0 (1 / ((m : ℝ) + 1)) ⊆ Ioi 0 := Ioo_subset_Ioi_self
    have hGU : ContinuousOn G (Ioo 0 (1 / ((m : ℝ) + 1))) := hG.mono hsub
    have step1 : ∀ q : ℚ, (q : ℝ) ∈ Ioo 0 (1 / ((m : ℝ) + 1)) →
        ∀ s' ∈ Ioo 0 (1 / ((m : ℝ) + 1)), |G q - G s'| ≤ 1 / ((n : ℝ) + 1) := by
      intro q hq s' hs'
      refine le_of_forall_rat (f := fun s' => |G q - G s'|) isOpen_Ioo
        (continuousOn_const.sub hGU).abs (fun q' hq' => hm q q' hq.1 hq.2 hq'.1 hq'.2) hs'
    intro s s' hs hs'
    exact le_of_forall_rat (f := fun s => |G s - G s'|) isOpen_Ioo
      (hGU.sub continuousOn_const).abs (fun q hq => step1 q hq s' hs') hs
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := hreal n
  refine ⟨G '' Ioo 0 (1 / ((m : ℝ) + 1)), image_mem_map (Ioo_mem_nhdsGT (by positivity)), ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
  rw [Real.dist_eq]
  exact (hm s s' hs hs').trans_lt hn

theorem cauchyQ_of_tendsto {G : ℝ → ℝ} {L : ℝ} (h : Tendsto G (𝓝[>] 0) (𝓝 L)) : CauchyQ G := by
  intro n
  have hε : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨δ, hδ, hδG⟩ := Metric.tendsto_nhdsWithin_nhds.1 h _ hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun q q' hq hqm hq' hqm' => ?_⟩
  have h1 := hδG (x := (q : ℝ)) hq (by rw [Real.dist_eq, sub_zero, abs_of_pos hq]; linarith)
  have h2 := hδG (x := (q' : ℝ)) hq' (by rw [Real.dist_eq, sub_zero, abs_of_pos hq']; linarith)
  rw [Real.dist_eq] at h1 h2
  have e : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
    field_simp; ring
  calc |G q - G q'| = |(G q - L) - (G q' - L)| := by ring_nf
    _ ≤ |G q - L| + |G q' - L| := abs_sub _ _
    _ ≤ 1 / ((n : ℝ) + 1) := by linarith

/-- `CauchyQ (pairSm x g)` is a measurable event of the field. -/
theorem measurable_cauchyQ (g : ℂ → ℝ) : Measurable fun x : FieldSample => CauchyQ (pairSm x g) := by
  unfold CauchyQ
  refine Measurable.forall fun n => Measurable.exists fun m => Measurable.forall fun q =>
    Measurable.forall fun q' => ?_
  refine measurable_const.imp (measurable_const.imp (measurable_const.imp
    (measurable_const.imp ?_)))
  exact GoodMeas.mprop_abs_le (GoodMeas.measurable_integral_evalReg_fc _ _)
    (GoodMeas.measurable_integral_evalReg_fc _ _) _

/-- `pairSm` reads only the regularization. -/
theorem pairSm_reconstruct (x : FieldSample) (g : ℂ → ℝ) :
    pairSm (Factorization.reconstruct (Factorization.coords x)) g = pairSm x g := by
  have h : RegEq (Factorization.reconstruct (Factorization.coords x)) x := fun k z => by
    rw [Factorization.avgReg_reconstruct_coords]
  funext s
  unfold pairSm
  simp only [Cor15Group.evalReg_congr_regEq h]

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {g : ℂ → ℝ}

theorem integrable_evalReg_fc_tmeas (hF : IsRegularWith x F) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgH : tsupport g ⊆ H) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => evalReg x (foldedCircle u s)) (G1.tmeas g) := by
  obtain ⟨M, R, δ, hS⟩ := PairLim.exists_setup_withDensity hg hgc hgH
  have := hS.good.isFiniteMeasure
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R ∩ Hbar) :=
    (isCompact_closedBall _ _).inter_right isClosed_Hbar
  have hcF : ContinuousOn (fun u => F (u, s)) Hbar :=
    hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun u hu => ⟨hu, hs⟩
  exact (FrostmanReg.integrable_of_continuousOn_frostman hK inter_subset_right hS.good.2
    hcF).congr (hS.good.ae_mem.mono fun u hu => (hF.evalReg_fc_of_mem hu.2 hs).symm)

theorem continuousOn_pairSm (hF : IsRegularWith x F) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgH : tsupport g ⊆ H) : ContinuousOn (pairSm x g) (Ioi 0) := by
  obtain ⟨M, R, δ, hS⟩ := PairLim.exists_setup_withDensity hg hgc hgH
  have e : ∀ s : ℝ, 0 < s → pairSm x g s = ∫ u, F (u, s) ∂G1.tmeas g := fun s hs =>
    integral_congr_ae (hS.good.ae_mem.mono fun u hu => hF.evalReg_fc_of_mem hu.2 hs)
  intro s hs
  have hs : 0 < s := hs
  have hc := PairLim.continuousOn_integral_witness hS hF.1 (half_pos hs) (b := 2 * s)
  have hmem : Icc (s / 2) (2 * s) ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
  have hca := (hc.continuousAt hmem).congr (f := fun s => ∫ u, F (u, s) ∂G1.tmeas g)
    (g := pairSm x g) ?_
  · exact hca.continuousWithinAt
  · filter_upwards [Ioi_mem_nhds hs] with s' hs'
    exact (e s' hs').symm

end ZipReg
end Thm18Asm
end QuantumZipper
