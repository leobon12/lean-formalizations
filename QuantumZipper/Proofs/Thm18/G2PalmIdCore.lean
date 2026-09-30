import QuantumZipper.Proofs.Thm18.G2PalmIdCoords

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2-PALMID, part 2: the Palm formula in the interleaved coordinates

* `pid_palm`: the Duplantier–Sheffield Palm (rooted-measure) formula (arXiv:0808.1560, §3.3,
  p. 22), in the normalized form `E1.palm_formula_Ioo` (indicator weight of `(a, b)`), for the
  unit-normalized free field `Y = N_S X₀` and a measurable functional of the coordinates
  `Y(pidMu A B n)`; the Palm field is `N_S(X₀ + ψ_x)` with `ψ_x = (γ/2)(neumannH x · − k_S)`
  (`xPalm`).
* `ae_pidFine_palm`: `P`-a.s. properties transfer to the Palm field for Lebesgue-a.e. `x`
  (the standard remark, as in `S5.FieldLaw.Raw.ae_palmFreeField_good`): the boundary measure of
  `𝔥₀ + X₀ + ψ_x − (X₀ + ψ_x)(S)` has a certificate and is finite on compact intervals.
* `lintegral_hν_eq`: `∫_{[a,b]} g dν_h = ∫_{(a,b)} |t| g dν_Z` (log-singularity theorem
  `ae_g3Hν_eq`).

Own bookkeeping around the cited Palm formula (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Factorization (coords reconstruct)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

theorem ofFun_zero' : ofFun (0 : ℂ → ℝ) = 0 := by
  funext μ; simp [ofFun]

theorem shiftFun_zero_refS (γ x : ℝ) : PalmNorm.shiftFun γ 0 refS x = g2PalmPsi γ x := by
  funext u; simp [PalmNorm.shiftFun, g2PalmPsi]

theorem palmField_eq_xPalm (γ x : ℝ) (ω : Ω₀) :
    ofFun (PalmNorm.shiftFun γ 0 refS x) + X₀ ω = xPalm γ x ω := by
  rw [shiftFun_zero_refS, xPalm, add_comm]

theorem freeField_eq (ω : Ω₀) : ofFun (0 : ℂ → ℝ) + X₀ ω = X₀ ω := by
  rw [ofFun_zero', zero_add]

theorem measurable_pidC_xPalm (γ : ℝ) (A B : ℕ → Measure ℂ) (x : ℝ) :
    Measurable fun ω => pidC A B (xPalm γ x ω) := by
  refine measurable_pi_iff.2 fun j => ?_
  have e : (fun ω => pidC A B (xPalm γ x ω) j) = fun ω =>
      (X₀ ω (pidMu A B j) + ofFun (g2PalmPsi γ x) (pidMu A B j)) +
        -(X₀ ω refS + ofFun (g2PalmPsi γ x) refS) * (pidMu A B j univ).toReal := rfl
  rw [e]
  exact ((gffBase.gff.measurable_coord _).add measurable_const).add
    (((gffBase.gff.measurable_coord _).add measurable_const).neg.mul measurable_const)

theorem measurable_pidC_free (A B : ℕ → Measure ℂ) :
    Measurable fun ω => pidC A B (X₀ ω) := by
  refine measurable_pi_iff.2 fun j => ?_
  have e : (fun ω => pidC A B (X₀ ω) j) = fun ω =>
      X₀ ω (pidMu A B j) + -(X₀ ω refS) * (pidMu A B j univ).toReal := rfl
  rw [e]
  exact (gffBase.gff.measurable_coord _).add
    ((gffBase.gff.measurable_coord _).neg.mul measurable_const)

/-- Measurability of the Palm side in `x` (as `S5.FieldLaw.Raw.measurable_palmK`). -/
theorem measurable_pidK (γ : ℝ) {A B : ℕ → Measure ℂ} (hA : ∀ n, IsAdmissibleH (A n))
    (hB : ∀ n, IsAdmissibleH (B n)) {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) :
    Measurable fun x => ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P := by
  have hc : Measurable fun p : Ω₀ × ℝ => pidC A B (xPalm γ p.2 p.1) := by
    refine measurable_pi_iff.2 fun j => ?_
    haveI : IsFiniteMeasure (pidMu A B j) := (pidMu_adm hA hB j).1
    set μ := pidMu A B j
    have e : (fun p : Ω₀ × ℝ => pidC A B (xPalm γ p.2 p.1) j) = fun p =>
        (ofFun (PalmNorm.shiftFun γ 0 refS p.2) μ + X₀ p.1 μ) +
          -(ofFun (PalmNorm.shiftFun γ 0 refS p.2) refS + X₀ p.1 refS) * (μ univ).toReal := by
      funext p
      simp only [pidC, ← palmField_eq_xPalm, PalmNorm.normAt, addConst]
      rfl
    rw [e]
    have hs : Measurable (Prod.snd : Ω₀ × ℝ → ℝ) := measurable_snd
    have h1 := (E1.measurable_ofFun_shiftFun (γ := γ) (h := (0 : ℂ → ℝ)) measurable_const refS
      μ).comp hs
    have h2 := (E1.measurable_ofFun_shiftFun (γ := γ) (h := (0 : ℂ → ℝ)) measurable_const refS
      refS).comp hs
    exact (h1.add ((gffBase.gff.measurable_coord μ).comp measurable_fst)).add
      ((h2.add ((gffBase.gff.measurable_coord refS).comp measurable_fst)).neg.mul
        measurable_const)
  exact Measurable.lintegral_prod_left'
    (f := fun p : Ω₀ × ℝ => φ (pidC A B (xPalm γ p.2 p.1)) p.2) (hφ.comp (hc.prodMk measurable_snd))

/-- **The Palm formula in the interleaved coordinates** (`E1.palm_formula_Ioo`, `h = 0`,
`ϖ = S`). -/
theorem pid_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {A B : ℕ → Measure ℂ}
    (hA : ∀ n, IsAdmissibleH (A n)) (hB : ∀ n, IsAdmissibleH (B n)) {a b : ℝ}
    (hab : Icc a b ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)) {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) :
    ∫⁻ ω, ∫⁻ x in Ioo a b, φ (pidC A B (X₀ ω)) x ∂(g3Zν γ ω) ∂gffBase.P =
      ∫⁻ x in Ioo a b, ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P := by
  have hex : ∀ᵐ ω ∂gffBase.P,
      ∃ ν, IsVagueLimitR (bdryApprox γ (PalmNorm.normAt refS (ofFun 0 + X₀ ω))) ν := by
    filter_upwards [S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS] with ω hω
    exact ⟨_, hω.1.qBoundaryMeasure_spec.1,
      fun f hf hfc => LQGMeas.tendsto_bdryApprox_of_good hω.1 hf hfc⟩
  have hK : Measurable fun x => ∫⁻ ω, φ (fun j => PalmNorm.normAt refS
      (ofFun (PalmNorm.shiftFun γ 0 refS x) + X₀ ω) (pidMu A B j)) x ∂gffBase.P := by
    simp only [palmField_eq_xPalm]
    exact measurable_pidK γ hA hB hφ
  have H := E1.palm_formula_Ioo (P := gffBase.P) (h := 0) (h' := 0) (ϖ := refS)
    (μ := pidMu A B) gffBase.gff hγ hγ2 hab continuous_const isOpen_univ
    (fun _ _ => mem_univ _) (fun _ _ => rfl) isAdmissibleH_refS measure_univ
    (pidMu_adm hA hB) (integrable_zero _ _ _) (fun _ => integrable_zero _ _ _) hex hφ
    (E1.measurable_rhoNorm measurable_const refS) hK
  have hc : ∀ ω, pidC A B (X₀ ω) =
      fun j => PalmNorm.normAt refS (ofFun 0 + X₀ ω) (pidMu A B j) := fun ω => by
    rw [freeField_eq]; rfl
  simp only [palmField_eq_xPalm] at H
  simp only [hc]
  exact H

/-! ## Fineness and its transfer to the Palm field -/

/-- Coordinates whose boundary measure has a certificate and is finite on rational intervals. -/
def pidFine (γ : ℝ) (d : ℕ → ℝ) : Prop :=
  E1.M4.BCert γ (reconstruct d) ∧ ∀ q₁ q₂ : ℚ, bdryMc γ d (Icc (q₁ : ℝ) q₂) ≠ ⊤

theorem measurableSet_pidFine (γ : ℝ) : MeasurableSet {c : ℕ → ℝ | pidFine γ (pidDN γ c)} := by
  have e : {c : ℕ → ℝ | pidFine γ (pidDN γ c)} =
      (fun c => reconstruct (pidDN γ c)) ⁻¹' {x | E1.M4.BCert γ x} ∩
        ⋂ q₁ : ℚ, ⋂ q₂ : ℚ, {c | bdryMc γ (pidDN γ c) (Icc (q₁ : ℝ) q₂) ≠ ⊤} := by
    ext c; simp only [pidFine, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_iInter]
  rw [e]
  refine ((E1.M4.measurableSet_bCert γ).preimage
    (Factorization.measurable_reconstruct.comp (measurable_pidDN γ))).inter
    (MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ => ?_)
  exact (measurableSet_eq_fun ((Measure.measurable_coe measurableSet_Icc).comp
    ((measurable_bdryMc γ).comp (measurable_pidDN γ))) measurable_const).compl

theorem pidFine_coords_iff (γ : ℝ) (y : FieldSample) :
    pidFine γ (coords y) ↔
      E1.M4.BCert γ y ∧ ∀ q₁ q₂ : ℚ, qBoundaryMeasure γ y (Icc (q₁ : ℝ) q₂) ≠ ⊤ := by
  unfold pidFine
  rw [bCert_reconstruct_coords_iff]
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨hc, fun q₁ q₂ => ?_⟩
    have := hf q₁ q₂
    rwa [bdryMc_coords_eq, if_pos hc] at this
  · rintro ⟨hc, hf⟩
    refine ⟨hc, fun q₁ q₂ => ?_⟩
    rw [bdryMc_coords_eq, if_pos hc]
    exact hf q₁ q₂

/-- Fineness gives finiteness on every compact interval. -/
theorem qBM_Icc_ne_top_of_fine {γ : ℝ} {y : FieldSample}
    (h : ∀ q₁ q₂ : ℚ, qBoundaryMeasure γ y (Icc (q₁ : ℝ) q₂) ≠ ⊤) (u v : ℝ) :
    qBoundaryMeasure γ y (Icc u v) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (h (⌊u⌋ : ℚ) (⌈v⌉ : ℚ)) (measure_mono (Icc_subset_Icc ?_ ?_))
  · push_cast; exact Int.floor_le u
  · push_cast; exact Int.le_ceil v

theorem ae_pidFine_free {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, pidFine γ (coords (pidNf γ (X₀ ω))) := by
  filter_upwards [G3Fid.ae_normField_good gffBase.gff hγ hγ2] with ω hg
  have hv := hg.1
  have : IsLocallyFiniteMeasure (qBoundaryMeasure γ (pidNf γ (X₀ ω))) := hv.1
  rw [pidFine_coords_iff]
  refine ⟨E1.M4.bCert_of_isVagueLimitR
    (fun k N => (hg.2.1 k).lt_top_of_isCompact isCompact_Icc) hv, fun q₁ q₂ => ?_⟩
  exact measure_Icc_lt_top.ne

/-- **Transfer to the Palm field.** For Lebesgue-a.e. `x ∈ (a, b)`, the Palm field is a.s. fine. -/
theorem ae_pidFine_palm {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {A B : ℕ → Measure ℂ}
    (hA : ∀ n, IsAdmissibleH (A n)) (hB : ∀ n, IsAdmissibleH (B n)) {a b : ℝ}
    (hab : Icc a b ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)) :
    ∀ᵐ x ∂(volume.restrict (Ioo a b)), ∀ᵐ ω ∂gffBase.P,
      pidFine γ (pidDN γ (pidC A B (xPalm γ x ω))) := by
  set bad : Set (ℕ → ℝ) := {c | pidFine γ (pidDN γ c)}ᶜ with hbad
  have hbm : MeasurableSet bad := (measurableSet_pidFine γ).compl
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c _ => bad.indicator 1 c with hφdef
  have hφ : Measurable (Function.uncurry φ) := (measurable_one.indicator hbm).comp measurable_fst
  have H := pid_palm hγ hγ2 hA hB hab hφ
  have hL : ∫⁻ ω, ∫⁻ x in Ioo a b, φ (pidC A B (X₀ ω)) x ∂(g3Zν γ ω) ∂gffBase.P = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_pidFine_free hγ hγ2] with ω hω
    have hn : pidC A B (X₀ ω) ∉ bad := by
      rw [hbad, mem_compl_iff, not_not, mem_setOf_eq, ← coords_pidNf]; exact hω
    simp only [hφdef, indicator_of_notMem hn, lintegral_zero]
  rw [hL, eq_comm] at H
  have hmR : Measurable fun x => ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
      ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P :=
    (E1.measurable_rhoNorm measurable_const refS).ennreal_ofReal.mul (measurable_pidK γ hA hB hφ)
  filter_upwards [(lintegral_eq_zero_iff hmR).1 H] with x hx
  have hρ : ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have h0 := (mul_eq_zero.1 hx).resolve_left hρ
  have hm : Measurable fun ω => φ (pidC A B (xPalm γ x ω)) x :=
    (measurable_one.indicator hbm).comp (measurable_pidC_xPalm γ A B x)
  filter_upwards [(lintegral_eq_zero_iff hm).1 h0] with ω hω
  by_contra hne
  have : pidC A B (xPalm γ x ω) ∈ bad := hne
  simp [hφdef, indicator_of_mem this] at hω

/-! ## From `ν_h` to `|t| ν_Z` -/

theorem lintegral_hν_eq {νZ νH : Measure ℝ}
    (hH : νH = (νZ.restrict {0}ᶜ).withDensity (fun t => ENNReal.ofReal |t|)) (hZ0 : νZ {0} = 0)
    {a b : ℝ} (ha : νH {a} = 0) (hb : νH {b} = 0) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in Icc a b, g x ∂νH = ∫⁻ x in Ioo a b, ENNReal.ofReal |x| * g x ∂νZ := by
  rw [← setLIntegral_congr (Ioo_ae_eq_Icc' ha hb), hH,
    setLIntegral_withDensity_eq_setLIntegral_mul _
      (continuous_abs.measurable.ennreal_ofReal) hg measurableSet_Ioo]
  have hr : νZ.restrict {0}ᶜ = νZ := by
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]; simpa using hZ0
  rw [hr]
  rfl

end Thm18Asm
end QuantumZipper
