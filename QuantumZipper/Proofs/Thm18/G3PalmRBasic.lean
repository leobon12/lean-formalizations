import QuantumZipper.Proofs.Thm18.G3GeoStmt
import QuantumZipper.Proofs.Section5.Prop17PalmABId
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg

/-!
# G3-PALMR, part 1: pathwise facts for the Palm form of "`R(x) ∈ B₁(0)` w.h.p."

For `G3GeoPalmRStmt γ` (`G3GeoStmt.lean`; Sheffield, arXiv:1012.4797, proof of Theorem 1.8,
§5.4, p. 71) we pass from the honest boundary measure `ν_h = g3Hν γ ω` of Theorem 1.2's field
`h = 𝔥₀ + X₀ − X₀(S)` to the boundary measure `ν_Z` of the unit-normalized free field
`Z = N_S(X₀) = zField X₀ 1` (`freeFieldN refS X₀`), for which the Palm (rooted-measure) formula
`S5.FieldLaw.Raw.palm_free_Ioo` is available. Since `𝔥₀ = (2/γ) log|·|`, `ν_h = |t| · ν_Z` off `0`
(`G3FidHonest.qBoundaryMeasure_normField_restrict`, the log-singularity theorem).

* `freeFieldN_refS_eq_zField`: `N_S(0 + X) = zField X 1` (both normalize at the unit semicircle).
* `bdryMc`: the boundary measure read from the raw dyadic coordinates (`bdryM ∘ reconstruct`,
  measurable); `bdryMc_coords_of_good`: it is the honest boundary measure on good samples;
  `bdryMc_coords_eq`: in general it is the honest one or `0`.
* `g3PalmEv δ`: the coordinate event `ν[¼, ½] < 4δ · ν[−¼, 0]`, measurable.
* `ae_hν_Icc_eq_Ioo`: a.s. `ν_h[−δ, 0] = ∫_{(−δ,0)} |t| dν_Z`;
* `ae_hν_bad_imp`: a.s. `ν_h[0,½] < ν_h[−δ,0]` forces the coordinates of `Z` into `g3PalmEv δ`
  (`|t| ≥ ¼` on `[¼, ½]`, `|t| ≤ δ` on `[−δ, 0]`).

Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw (freeFieldN palmFreeField)
open Factorization (coords reconstruct)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The unit-normalized free field `N_S(0 + X)` is `zField X 1`. -/
theorem freeFieldN_refS_eq_zField {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample) (ω : Ω) :
    freeFieldN refS X ω = BdryExist.zField X 1 ω := by
  unfold freeFieldN
  rw [PalmNorm.normAt_zField (ϖ := refS) measure_univ 1 0 ω]
  funext μ
  simp [PalmNorm.normAt, addConst, BdryExist.zField, ofFun, refS]

/-- The boundary measure read from raw dyadic coordinates (measurable). -/
def bdryMc (γ : ℝ) (c : ℕ → ℝ) : Measure ℝ := bdryM γ (reconstruct c)

theorem measurable_bdryMc (γ : ℝ) : Measurable (bdryMc γ) :=
  (measurable_bdryM γ).comp Factorization.measurable_reconstruct

theorem bdryApprox_reconstruct_coords (γ : ℝ) (y : FieldSample) :
    bdryApprox γ (reconstruct (coords y)) = bdryApprox γ y := by
  funext k
  unfold bdryApprox
  rw [Factorization.avgReg_reconstruct_coords]

theorem bCert_reconstruct_coords_iff (γ : ℝ) (y : FieldSample) :
    E1.M4.BCert γ (reconstruct (coords y)) ↔ E1.M4.BCert γ y := by
  unfold E1.M4.BCert
  rw [bdryApprox_reconstruct_coords]

open Classical in
/-- On raw coordinates of `y`, `bdryMc` is the honest boundary measure of `y` or junk `0`. -/
theorem bdryMc_coords_eq (γ : ℝ) (y : FieldSample) :
    bdryMc γ (coords y) = if E1.M4.BCert γ y then qBoundaryMeasure γ y else 0 := by
  unfold bdryMc bdryM
  rw [bCert_reconstruct_coords_iff, WedgeBdry.qBoundaryMeasure_reconstruct]

theorem bdryMc_coords_of_good {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) :
    bdryMc γ (coords y) = qBoundaryMeasure γ y := by
  have hc : E1.M4.BCert γ y :=
    E1.M4.bCert_of_isVagueLimitR
      (fun k N => (LogSing.isFiniteMeasureOnCompacts_bdryApprox hy.1 γ k).lt_top_of_isCompact
        isCompact_Icc)
      (ν := qBoundaryMeasure γ y)
      ⟨hy.qBoundaryMeasure_spec.1, fun f hf hfc => LQGMeas.tendsto_bdryApprox_of_good hy hf hfc⟩
  rw [bdryMc_coords_eq, if_pos hc]

/-- The coordinate event `ν[¼, ½] < 4δ · ν[−¼, 0]`. -/
def g3PalmEv (γ δ : ℝ) : Set (ℕ → ℝ) :=
  {c | bdryMc γ c (Icc (1 / 4) (1 / 2)) < ENNReal.ofReal (4 * δ) * bdryMc γ c (Icc (-(1 / 4)) 0)}

theorem measurableSet_g3PalmEv (γ δ : ℝ) : MeasurableSet (g3PalmEv γ δ) :=
  measurableSet_lt ((Measure.measurable_coe measurableSet_Icc).comp (measurable_bdryMc γ))
    (((Measure.measurable_coe measurableSet_Icc).comp (measurable_bdryMc γ)).const_mul _)

/-- The coordinate event is contained in the same event for the honest boundary measure (the
junk value `0` never satisfies a strict inequality `0 < c · 0`). -/
theorem coords_mem_g3PalmEv_imp (γ δ : ℝ) (y : FieldSample) (h : coords y ∈ g3PalmEv γ δ) :
    qBoundaryMeasure γ y (Icc (1 / 4) (1 / 2)) <
      ENNReal.ofReal (4 * δ) * qBoundaryMeasure γ y (Icc (-(1 / 4)) 0) := by
  have h' := h
  simp only [g3PalmEv, mem_setOf_eq, bdryMc_coords_eq] at h'
  split_ifs at h' with hc
  · exact h'
  · simp at h'

/-- The unit-normalized free field's boundary measure. -/
abbrev g3Zν (γ : ℝ) (ω : Ω₀) : Measure ℝ := qBoundaryMeasure γ (freeFieldN refS X₀ ω)

/-- **`ν_h = |t| ν_Z` off `0`** (log-singularity theorem, `G3FidHonest`). -/
theorem ae_g3Hν_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, g3Hν γ ω =
      ((g3Zν γ ω).restrict {0}ᶜ).withDensity (fun t => ENNReal.ofReal |t|) := by
  filter_upwards [qBoundaryMeasure_normField_restrict (X := X₀) gffBase.gff hγ hγ2] with ω hω
  rw [g3Zν, freeFieldN_refS_eq_zField]
  exact hω

/-- A.s. `ν_h[−δ, 0] = ∫_{(−δ,0)} |t| dν_Z`. -/
theorem ae_hν_Icc_eq_Ioo {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (δ : ℝ) :
    ∀ᵐ ω ∂gffBase.P, g3Hν γ ω (Icc (-δ) 0) =
      ∫⁻ t in Ioo (-δ) 0, ENNReal.ofReal |t| ∂(g3Zν γ ω) := by
  filter_upwards [ae_g3Hν_eq hγ hγ2, G3Fid.ae_normField_good gffBase.gff hγ hγ2] with ω hω hg
  have hs : Ioo (-δ) (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun t ht h0 => by
    rw [mem_singleton_iff] at h0; linarith [ht.2]
  rw [← measure_congr (Ioo_ae_eq_Icc' (hg.2.2 (-δ)) (hg.2.2 0))]
  show g3Hν γ ω (Ioo (-δ) 0) = _
  rw [hω, withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 hs]

/-- **The bad event forces the coordinate event.** A.s., for `δ ≥ 0`,
`ν_h[0,½] < ν_h[−δ,0]` implies `coords Z ∈ g3PalmEv γ δ`. -/
theorem ae_hν_bad_imp {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ4 : δ ≤ 1 / 4) :
    ∀ᵐ ω ∂gffBase.P, g3Hν γ ω (Icc 0 (1 / 2)) < g3Hν γ ω (Icc (-δ) 0) →
      coords (freeFieldN refS X₀ ω) ∈ g3PalmEv γ δ := by
  filter_upwards [ae_g3Hν_eq hγ hγ2, S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS]
    with ω hω hgood hbad
  set ν := g3Zν γ ω with hν
  have hupper : g3Hν γ ω (Icc (-δ) 0) ≤ ENNReal.ofReal δ * ν (Icc (-(1 / 4)) 0) := by
    rw [hω, withDensity_apply _ measurableSet_Icc]
    calc ∫⁻ t in Icc (-δ) 0, ENNReal.ofReal |t| ∂(ν.restrict {0}ᶜ)
        ≤ ∫⁻ _ in Icc (-δ) 0, ENNReal.ofReal δ ∂(ν.restrict {0}ᶜ) := by
          refine setLIntegral_mono measurable_const fun t ht => ENNReal.ofReal_le_ofReal ?_
          rw [abs_of_nonpos ht.2]
          linarith [ht.1]
      _ = ENNReal.ofReal δ * (ν.restrict {0}ᶜ) (Icc (-δ) 0) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal δ * ν (Icc (-(1 / 4)) 0) := by
          refine mul_le_mul' le_rfl ?_
          rw [Measure.restrict_apply measurableSet_Icc]
          exact (measure_mono Set.inter_subset_left).trans
            (measure_mono (Icc_subset_Icc_left (by linarith)))
  have hlower : ENNReal.ofReal (1 / 4) * ν (Icc (1 / 4) (1 / 2)) ≤ g3Hν γ ω (Icc 0 (1 / 2)) := by
    have hsub : Icc (1 / 4 : ℝ) (1 / 2) ⊆ Icc 0 (1 / 2) := Icc_subset_Icc_left (by norm_num)
    refine le_trans ?_ (measure_mono hsub)
    have hs : Icc (1 / 4 : ℝ) (1 / 2) ⊆ ({0}ᶜ : Set ℝ) := fun t ht h0 => by
      rw [mem_singleton_iff] at h0; linarith [ht.1]
    rw [hω, withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.2 hs]
    calc ENNReal.ofReal (1 / 4) * ν (Icc (1 / 4) (1 / 2))
        = ∫⁻ _ in Icc (1 / 4 : ℝ) (1 / 2), ENNReal.ofReal (1 / 4) ∂ν :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ t in Icc (1 / 4 : ℝ) (1 / 2), ENNReal.ofReal |t| ∂ν := by
          refine setLIntegral_mono (by fun_prop) fun t ht => ENNReal.ofReal_le_ofReal ?_
          rw [abs_of_nonneg (by linarith [ht.1])]
          exact ht.1
  have hlt : ENNReal.ofReal (1 / 4) * ν (Icc (1 / 4) (1 / 2)) <
      ENNReal.ofReal δ * ν (Icc (-(1 / 4)) 0) := (hlower.trans_lt hbad).trans_le hupper
  have key : ν (Icc (1 / 4) (1 / 2)) < ENNReal.ofReal (4 * δ) * ν (Icc (-(1 / 4)) 0) := by
    have h4 : ENNReal.ofReal (1 / 4) * ENNReal.ofReal (4 * δ) = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    by_contra hle
    push_neg at hle
    have hm := mul_le_mul' (le_refl (ENNReal.ofReal (1 / 4))) hle
    rw [← mul_assoc, h4] at hm
    exact absurd hlt (not_lt.2 hm)
  show coords (freeFieldN refS X₀ ω) ∈ g3PalmEv γ δ
  simp only [g3PalmEv, mem_setOf_eq, bdryMc_coords_of_good hgood.1]
  exact key

end Thm18Asm
end QuantumZipper
