import QuantumZipper.Proofs.Thm18.R18G3TArea
import QuantumZipper.Proofs.Thm18.G3GeoHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T: honest boundary lengths of scheme `C` (F2 and the Palm mass)

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71 (the scheme), p. 28 (the Palm weighting
adds `−γ log|·|` to `𝔥₀`). For scheme `C` (field `g3pField γ (g3wProf γ)`, which on folded
circles is `zField X 1 + Lf (γ − 2/γ)`, `R18G3TArea.g3pField_fc_eq_Lf`) this file ports the
honest-length facts of the free scheme (`G3Fid.g3Fid2`, `G3GeoHonest.ae_g3Fid_sets`,
`G3FidMass.g3Z_eq_lintegral_g3Mass`, `G3FidHonest`):

* `ae_g3pField_good`: a.s. the shifted field has a boundary measure, finite approximations,
  no atoms, and `ν_C = |t|^{−(γ−2/γ)γ/2} ν_Z` on `ℝ ∖ {0}` (`LogSing.ae_logSingularity` with
  `α = γ − 2/γ < Q`, `AtomlessUncond.ae_noAtoms_zField'`);
* `ae_g3pFid_sets` (F2-C): the scheme's measures agree with `ν_C` on their windows
  (`G3Fid.regionCut`, `G3Fid.gapCut`);
* `g3pZ_eq_honest`: `g3pZ = E ν_C[−δ, 0]`.

Own bookkeeping on top of the cited lemmas (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The log-singularity exponent of scheme `C`. -/
abbrev αC (γ : ℝ) : ℝ := γ - 2 / γ

theorem logPot_zero_eq_Lf (α : ℝ) : LogSing.logPot α 0 = LogSingGood.Lf α := by
  funext v
  simp [LogSing.logPot, LogSingGood.Lf]

theorem αC_lt_Qc {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : αC γ < Qc γ := by
  unfold αC Qc
  have h : 1 < 2 / γ := (one_lt_div hγ).2 hγ2
  linarith

theorem bdryApprox_g3pField {γ : ℝ} (hγ : 0 < γ) (ω : Ω₀) :
    bdryApprox γ (g3pField γ (g3wProf γ) ω) = bdryApprox γ (BdryExist.zField X₀ 1 ω +
      ofFun (LogSing.logPot (αC γ) 0)) := by
  funext k
  have e : ∀ z, avgReg (g3pField γ (g3wProf γ) ω) k z = avgReg (BdryExist.zField X₀ 1 ω +
      ofFun (LogSing.logPot (αC γ) 0)) k z := fun z => by
    unfold avgReg
    simp_rw [g3pField_fc_eq_Lf hγ ω, logPot_zero_eq_Lf]
  simp only [bdryApprox, e]

/-- **A.s. input for scheme `C`.** -/
theorem ae_g3pField_good {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, IsVagueLimitR (bdryApprox γ (g3pField γ (g3wProf γ) ω))
        (qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω)) ∧
      (∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ (g3wProf γ) ω) k)) ∧
      (∀ s, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) {s} = 0) ∧
      qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) =
        ((qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω)).restrict {0}ᶜ).withDensity
          (fun t => ENNReal.ofReal (|t - 0| ^ (-(αC γ * γ / 2)))) := by
  filter_upwards [LogSing.ae_logSingularity gffBase.gff hγ hγ2 1 (αC_lt_Qc hγ hγ2) 0
      (LogSing.p3bBound gffBase.gff hγ hγ2 one_pos (by simp)),
    RegSample.ae_isRegularSample gffBase.gff,
    AtomlessUncond.ae_noAtoms_zField' gffBase.gff hγ hγ2 1] with ω hω hreg hat
  obtain ⟨hglob, hform, -⟩ := hω
  have hY : IsRegularSample (BdryExist.zField X₀ 1 ω + ofFun (LogSing.logPot (αC γ) 0)) :=
    (hreg.addConst' _).add_ofFun_log' _ 0
  have hb := bdryApprox_g3pField hγ ω
  have hv : IsVagueLimitR (bdryApprox γ (g3pField γ (g3wProf γ) ω)) (qBoundaryMeasure γ
      (BdryExist.zField X₀ 1 ω + ofFun (LogSing.logPot (αC γ) 0))) := by
    rw [hb]; exact hglob
  have hq := qBoundaryMeasure_eq hv
  refine ⟨hq ▸ hv, fun k => ?_, fun s => ?_, ?_⟩
  · rw [hb]; exact LogSing.isFiniteMeasureOnCompacts_bdryApprox hY γ k
  · rw [hq, hform]
    exact withDensity_absolutelyContinuous _ _
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self (hat.measure_singleton s))
  · rw [hq, hform]

/-- **F2 for a profiled scheme, deterministic form**: if the shifted field has a boundary
measure, finite approximations and no atoms, the scheme's measures agree with it on the
windows. -/
theorem g3pFid2_of {γ : ℝ} (hγ : 0 < γ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀)
    (hv : IsVagueLimitR (bdryApprox γ (g3pField γ g ω)) (qBoundaryMeasure γ (g3pField γ g ω)))
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ g ω) k))
    (hat : ∀ s, qBoundaryMeasure γ (g3pField γ g ω) {s} = 0) :
      (g3pν₁ γ g i ω + g3pν₀ γ g i ω).restrict
          (Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) =
        (qBoundaryMeasure γ (g3pField γ g ω)).restrict
          (Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) ∧
      (g3pν₀ γ g i ω + g3pν₂ γ g i ω).restrict
          (Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) =
        (qBoundaryMeasure γ (g3pField γ g ω)).restrict
          (Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) := by
  obtain ⟨hB1, e1⟩ := G3Fid.regionCut hγ hv hfin hat (t := i.t₁) i.r₁_pos
  obtain ⟨hB2, e2⟩ := G3Fid.regionCut hγ hv hfin hat (t := i.t₂) i.r₂_pos
  obtain ⟨hB0, e0⟩ := G3Fid.gapCut hγ hv hfin hat (t₁ := i.t₁) (t₂ := i.t₂) i.r₁_pos i.r₂_pos
  have ha : i.t₁ - i.r₁ = -i.δ - i.η / 4 := by unfold G3Idx.t₁ G3Idx.r₁; ring
  have hb : i.t₁ + i.r₁ = -(3 * i.η / 4) := by unfold G3Idx.t₁ G3Idx.r₁; ring
  have hc : i.t₂ - i.r₂ = 3 * i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
  have hd : i.t₂ + i.r₂ = 1 / 2 + i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
  have n1 : g3pν₁ γ g i ω = (qBoundaryMeasure γ (g3pField γ g ω)).restrict
      (Ioo (-i.δ - i.η / 4) (-(3 * i.η / 4))) := by
    rw [g3pν₁, bdryM, if_pos hB1, ← ha, ← hb]; exact e1
  have n2 : g3pν₂ γ g i ω = (qBoundaryMeasure γ (g3pField γ g ω)).restrict
      (Ioo (3 * i.η / 4) (1 / 2 + i.η / 4)) := by
    rw [g3pν₂, bdryM, if_pos hB2, ← hc, ← hd]; exact e2
  have n0 : g3pν₀ γ g i ω = (qBoundaryMeasure γ (g3pField γ g ω)).restrict
      (Icc (-i.δ - i.η / 4) (-(3 * i.η / 4)) ∪ Icc (3 * i.η / 4) (1 / 2 + i.η / 4))ᶜ := by
    rw [g3pν₀, bdryM, if_pos hB0, ← ha, ← hb, ← hc, ← hd]; exact e0
  have := i.hη; have := i.hηδ; have := i.hδ
  have h1 : -i.δ - i.η / 4 < -(3 * i.η / 4) := by linarith
  have h2 : -(3 * i.η / 4) < 3 * i.η / 4 := by linarith
  have h3 : 3 * i.η / 4 < 1 / 2 + i.η / 4 := by linarith
  refine ⟨?_, ?_⟩
  · rw [n1, n0]
    exact G3Fid.restrict_add_restrict_eq hat h1 h2 (G3Fid.Ioo_inter_Ioo_left h2.le)
      (G3Fid.Ioo_inter_gap h1.le h2 h3.le le_rfl h1.le le_rfl h3.le)
  · rw [n0, n2]
    exact G3Fid.restrict_add_restrict_eq hat h2 h3
      (G3Fid.Ioo_inter_gap h1.le h2 h3.le h1.le le_rfl h3.le le_rfl)
      (G3Fid.Ioo_inter_Ioo_right h2.le)

/-- **F2 for scheme `C`, restricted-measure form.** -/
theorem g3pFid2 {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      (g3pν₁ γ (g3wProf γ) i ω + g3pν₀ γ (g3wProf γ) i ω).restrict
          (Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) =
        (qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω)).restrict
          (Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) ∧
      (g3pν₀ γ (g3wProf γ) i ω + g3pν₂ γ (g3wProf γ) i ω).restrict
          (Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) =
        (qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω)).restrict
          (Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) := by
  filter_upwards [ae_g3pField_good hγ hγ2] with ω hω i
  exact g3pFid2_of hγ _ i ω hω.1 hω.2.1 hω.2.2.1

/-- **F2-C (sets).** -/
theorem ae_g3pFid_sets {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      (∀ s ⊆ Ioo (-i.δ - i.η / 4) (3 * i.η / 4),
        (g3pν₁ γ (g3wProf γ) i ω + g3pν₀ γ (g3wProf γ) i ω) s =
          qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) s) ∧
      (∀ s ⊆ Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4),
        (g3pν₀ γ (g3wProf γ) i ω + g3pν₂ γ (g3wProf γ) i ω) s =
          qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) s) := by
  filter_upwards [g3pFid2 hγ hγ2] with ω hω i
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [← Measure.restrict_eq_self _ hs, (hω i).1, Measure.restrict_eq_self _ hs]
  · rw [← Measure.restrict_eq_self _ hs, (hω i).2, Measure.restrict_eq_self _ hs]

/-! ## The Palm mass -/

theorem lintegral_g3pW0_fst (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀) :
    ∫⁻ ℓ : ℝ, g3pW0 γ g i (ω, ℓ) ∂L₀ = g3pMass γ g i ω := by
  refine (lintegral_congr fun ℓ => ?_).trans (lintegral_expMeasure_palmKernel (g3pMass γ g i ω))
  by_cases h : 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ g3pMass γ g i ω
  · rw [if_pos h]; unfold g3pW0; rw [if_pos h]
  · rw [if_neg h]; unfold g3pW0; rw [if_neg h]

theorem g3pZ_eq_lintegral_g3pMass (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) :
    g3pZ γ g i = ∫⁻ ω, g3pMass γ g i ω ∂gffBase.P := by
  have hW0 : Measurable (g3pW0 γ g i) := (measurable_g3pW0 γ g i).mono (sig_le_g3 i _ _) le_rfl
  unfold g3pZ
  rw [lintegral_prod _ hW0.aemeasurable]
  exact lintegral_congr fun ω => lintegral_g3pW0_fst γ g i ω

/-- `g3pZ = E ν_C[−δ, 0]`. -/
theorem g3pZ_eq_honest {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) :
    g3pZ γ (g3wProf γ) i =
      ∫⁻ ω, qBoundaryMeasure γ (g3pField γ (g3wProf γ) ω) (Icc (-i.δ) 0) ∂gffBase.P := by
  rw [g3pZ_eq_lintegral_g3pMass]
  exact lintegral_congr_ae ((ae_g3pFid_sets hγ hγ2).mono fun ω hω =>
    (hω i).1 _ (Icc_neg_subset_win i (by linarith [i.hη])))

end R18
end QuantumZipper
