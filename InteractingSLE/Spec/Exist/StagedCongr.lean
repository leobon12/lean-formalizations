/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedDet
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# Staged histories: the optional hull coupling is insensitive to null modifications of the driver

Packet PROVE-STAGED. A staged driver is one measurable map serving all conditional laws, so under the kernel at `ω₀`
it agrees with the realized driver of that kernel only almost surely. **`IsOptionalHullCoupling.congr_ae`**: if the
filtration contains the null sets, replacing the driver `W` and the lifetime `ζ` by measurable `W'`, `ζ'` that agree
with them almost surely before the lifetime (and at time `0`) keeps the optional hull coupling. The driving
filtration is unchanged (`Exist.drivingFiltration_congr_ae`), the hulls, coupling means and Green energies at a stop
`τ < ζ` only see the driver on `[0, τ]` (`fwdHull_eq_of_eqOn`, `Sec7.Lemma71B.couplingMean_congr`,
`Ito.fwdMap_congr_of_eqOn_of_le`), a local set is a property of the law (`IsLocalSet.congr_ae`), and a bounded harmonic
extension of the new boundary data is one of the old data off a null set (it is patched there with the extension given
by the sealed companion `existsUnique_isBoundedHarmonicExtension_forceBoundaryData`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace Staged

open LQGMetric

/-- **A local set is a property of the law**: an almost surely equal set-valued map is again local. -/
theorem IsLocalSet.congr_ae {Ω : Type*} [MeasurableSpace Ω] {A A' : Ω → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} {P : Measure Ω} (hA : IsLocalSet A h P) (hAA' : ∀ᵐ ω ∂P, A' ω = A ω) :
    IsLocalSet A' h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hsub, Ω', mΩ', P', hP', A₀, h₁, h₂, hA₀, hh₁, hh₂, hA₀H, hharm, hcond, hlaw⟩ := hA
  have hpair : (fun ω => (A' ω, h ω)) =ᵐ[P] fun ω => (A ω, h ω) := hAA'.mono fun ω hω => Prod.ext hω rfl
  refine ⟨hm.congr hpair.symm, ?_, Ω', mΩ', P', hP', A₀, h₁, h₂, hA₀, hh₁, hh₂, hA₀H, hharm, hcond, ?_⟩
  · filter_upwards [hsub, hAA'] with ω hω hωA
    rw [hωA]; exact hω
  · rw [hlaw]
    exact Measure.map_congr hpair.symm

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The hull at a time `τ < ζ` only sees the driver before `ζ`. -/
theorem fwdHull_eq_of_agree {ζ : ℝ≥0∞} {W W' : ℝ≥0 → ℝ} (hW : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → W' t = W t)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < ζ) :
    QuantumZipper.fwdHull (fun s : ℝ => W' s.toNNReal) τ = QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal) τ := by
  obtain ⟨u, hτu, huζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτ
  have hτu' : (τ : ℝ) < u := by exact_mod_cast hτu
  refine fwdHull_eq_of_eqOn τ.2 hτu' fun _ hr => hW _ ?_
  refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) huζ
  exact Real.toNNReal_le_iff_le_coe.2 hr.2

/-- The driver on `[0, τ]` for `τ < ζ`. -/
theorem eqOn_Icc_of_agree {ζ : ℝ≥0∞} {W W' : ℝ≥0 → ℝ} (hW : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → W' t = W t)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < ζ) :
    EqOn (fun s : ℝ => W s.toNNReal) (fun s : ℝ => W' s.toNNReal) (Icc 0 (τ : ℝ)) := fun _ hr =>
  (hW _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) hτ)).symm

/-- A finite extended time is the coercion of its `untopD`. -/
theorem coe_untopD_of_lt {a : WithTop ℝ≥0} {b : ℝ≥0∞} (h : (a : ℝ≥0∞) < b) :
    (((a.untopD 0 : ℝ≥0)) : ℝ≥0∞) = a := by
  cases a with
  | top => exact absurd h (not_lt.2 le_top)
  | coe s => rfl

/-- The Green energy at time `t` only sees the driver on `[0, t]`. -/
theorem loewnerGreenEnergy_congr {w w' : ℝ → ℝ} {t : ℝ} (h : EqOn w w' (Icc 0 t)) (φ : ℂ → ℝ) :
    loewnerGreenEnergy w t φ = loewnerGreenEnergy w' t φ := by
  unfold loewnerGreenEnergy
  simp only [Ito.fwdMap_congr_of_eqOn_of_le h le_rfl]

/-- **The optional hull coupling is insensitive to null modifications of the driver and the lifetime**, when the
filtration contains the null sets. -/
theorem IsOptionalHullCoupling.congr_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓕 t] N)
    (hX' : IsMeasurableKilledDriving W' VL VR ζ')
    (hagree : ∀ᵐ ω ∂P, ζ' ω = ζ ω ∧ W' 0 ω = W 0 ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω) :
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W' VL VR B ζ' h := by
  obtain ⟨hE, hhm, hgff, hX, hcl⟩ := hC
  have hBm : ∀ t, Measurable (B t) := fun t => (hE.1.2.1 t).mono (𝓕.le t) le_rfl
  -- the evolution
  have hE' : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W' VL VR B ζ' := by
    refine isIntegratedSLEEvolution_congr_ae hE hnull hX' hBm ?_ ?_
    · filter_upwards [hagree] with ω ⟨hζ, _h0, hW⟩
      exact ⟨hζ, fun t ht => ⟨hW t ht, fun _ => rfl, fun _ => rfl⟩, fun _ => rfl⟩
    · filter_upwards [hE.2.2.2.2, hagree] with ω hp ⟨hζ, h0, hW⟩
      rw [hζ]
      exact Sec2.Assembly.isIntegratedSLEPath_congr hp h0 (fun _ => rfl) (fun _ => rfl) hW
        (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun _ _ => rfl
  refine ⟨hE', hhm, hgff, hX', fun τ hτ hτζ => ?_⟩
  -- the driving filtrations agree
  have hAB : ∀ᵐ ω ∂P, AgreeBefore W W' VL VL VR VR ζ ζ' ω := by
    filter_upwards [hagree] with ω ⟨hζ, _h0, hW⟩
    exact ⟨hζ, fun t ht => ⟨hW t ht, fun _ => rfl, fun _ => rfl⟩⟩
  have hfilt : drivingFiltration P hX = drivingFiltration P hX' := drivingFiltration_congr_ae hX hX' hAB
  have hτ₀ : IsStoppingTime (drivingFiltration P hX) τ := by rw [hfilt]; exact hτ
  have hσ : hτ₀.measurableSpace = hτ.measurableSpace := measurableSpace_congr hfilt hτ₀ hτ
  have hτζ₀ : ∀ᵐ ω ∂P, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hτζ, hagree] with ω h1 ⟨hζ, _h0, _hW⟩
    rw [← hζ, coe_untopD_of_lt h1]; exact h1
  obtain ⟨hloc, hform⟩ := hcl τ hτ₀ (by
    filter_upwards [hτζ, hagree] with ω h1 ⟨hζ, _h0, _hW⟩
    rw [← hζ]; exact h1)
  -- agreement of the driver on `[0, τ]`
  have hgood : ∀ᵐ ω ∂P, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω := by
    filter_upwards [hτζ₀, hagree] with ω h1 ⟨_hζ, _h0, hW⟩
    exact ⟨h1, hW⟩
  refine ⟨IsLocalSet.congr_ae hloc (hgood.mono fun ω hω => fwdHull_eq_of_agree hω.2 hω.1), ?_⟩
  intro u' hu' φ
  -- patch `u'` to an extension of the old data
  classical
  set dL : Ω → Fin nL → ℝ := fun ω i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω
  set dR : Ω → Fin nR → ℝ := fun ω j => VR j ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω
  set dL' : Ω → Fin nL → ℝ := fun ω i => VL i ((τ ω).untopD 0) ω - W' ((τ ω).untopD 0) ω
  set dR' : Ω → Fin nR → ℝ := fun ω j => VR j ((τ ω).untopD 0) ω - W' ((τ ω).untopD 0) ω
  set u : Ω → ℂ → ℝ := fun ω => if W' ((τ ω).untopD 0) ω = W ((τ ω).untopD 0) ω then u' ω else
    (Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ) (ρL := ρL)
      (ρR := ρR) (vL := dL ω) (vR := dR ω)).choose with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (dL ω) (dR ω))
      (forceJumpSet (dL ω) (dR ω)) (u ω) := by
    intro ω
    by_cases hω : W' ((τ ω).untopD 0) ω = W ((τ ω).untopD 0) ω
    · have e1 : dL' ω = dL ω := funext fun i => by simp only [dL, dL', hω]
      have e2 : dR' ω = dR ω := funext fun j => by simp only [dR, dR', hω]
      have := hu' ω
      change IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (dL' ω) (dR' ω))
        (forceJumpSet (dL' ω) (dR' ω)) (u' ω) at this
      rw [e1, e2] at this
      simp only [hudef, hω, ↓reduceIte]
      exact this
    · simp only [hudef, hω, ↓reduceIte]
      exact (Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ) (ρL := ρL)
        (ρR := ρR) (vL := dL ω) (vR := dR ω)).choose_spec.1
  have hold := hform u hu φ
  rw [hσ] at hold
  filter_upwards [hold, hgood] with ω hω ⟨hτω, hW⟩ hdisj
  have hhull := fwdHull_eq_of_agree hW hτω
  have hEq := eqOn_Icc_of_agree hW hτω
  have hτlt : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := hτω
  have hWτ : W' ((τ ω).untopD 0) ω = W ((τ ω).untopD 0) ω := hW _ hτlt
  rw [hhull] at hdisj
  rw [hω hdisj]
  have huω : u ω = u' ω := by simp only [hudef, hWτ, ↓reduceIte]
  have hint : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u' ω) z * φ z) =
      ∫ z, couplingMean κ (fun s : ℝ => W' s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u' ω) z * φ z := by
    congr 1
    funext z
    congr 1
    exact Sec7.Lemma71B.couplingMean_congr ((τ ω).untopD 0).2 hEq κ (u' ω) z
  rw [huω, loewnerGreenEnergy_congr hEq, hint]

end Staged

end Exist

end InteractingSLE
