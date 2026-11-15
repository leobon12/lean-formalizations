/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Kernel
import InteractingSLE.Spec.Coupling.MartMeansPath

/-!
# The conditional means annihilate Laplacians off the range (harmonicity of the retained mean)

Packet PROVE-WHOLEFIELD9 (follow-up note C.3: "On a deterministic rational ball contained in a selected component, all
preceding means annihilate Laplacians of tests. Their distributional limit does also"; specification Aux. lemma 16,
p. 92: "Testing this stopped stochastic integral against `Δψ` supported in the ball shows that `M_t(Δψ) = 0`").

`lapH ψ = −(2π)⁻¹ Δψ` is the Laplacian test of a test function on `ℍ`.

* `actMean_lapH_eq_zero`: the explicit active mean `𝔥_σ` is harmonic on `ℍ \ K_σ`, so `∫ 𝔥_σ lapH ψ = 0` for `ψ` off
  the hull (clamped driver, `MartMeans.harmonicOnNhd_meanHarmonic_fwdMap`, LQGMetric's Green identity);
* `ae_condExp_lapH_eq_zero_of_active`, `ae_condExp_lapH_eq_zero_of_pocket` (the second conclusion of the birth step),
  **`ae_condExp_lapH_eq_zero_of_isLabel`**: `E[(h, lapH ψ) | 𝓕_σ] = 0` almost surely when `supp ψ` is a label at `σ`;
* **`ae_condExp_lapH_eq_zero_of_disjoint`**: the same for a test whose support avoids the label set `offLabels` (pieces
  of a partition of unity at a fine scale are labels).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

/-! ### The Laplacian test -/

/-- The Laplacian test `−(2π)⁻¹ Δψ` of a test function on `ℍ`. -/
def lapH (ψ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens :=
  lapTest upperHalfPlaneOpens (MarkovAsm.toZs ψ)

theorem coe_lapH (ψ : TestOn upperHalfPlaneOpens) :
    ⇑(lapH ψ) = cmTest (MarkovZB.zsTest (MarkovAsm.toZs ψ).2) :=
  coe_lapTest le_rfl _

theorem tsupport_lapH_subset (ψ : TestOn upperHalfPlaneOpens) : tsupport (lapH ψ) ⊆ tsupport ψ :=
  tsupport_lapTest_subset le_rfl _

open InnerProductSpace Laplacian in
theorem lapH_apply (ψ : TestOn upperHalfPlaneOpens) (z : ℂ) :
    lapH ψ z = -(2 * Real.pi)⁻¹ * Δ (⇑ψ) z := by
  rw [coe_lapH]; rfl

open InnerProductSpace Laplacian in
theorem lapH_add (ψ ψ' : TestOn upperHalfPlaneOpens) : lapH (ψ + ψ') = lapH ψ + lapH ψ' := by
  ext z
  rw [testOn_add_apply, lapH_apply, lapH_apply, lapH_apply]
  have h1 : ContDiffAt ℝ 2 (⇑ψ) z := (ψ.contDiff.of_le (by simp)).contDiffAt
  have h2 : ContDiffAt ℝ 2 (⇑ψ') z := (ψ'.contDiff.of_le (by simp)).contDiffAt
  rw [show (⇑(ψ + ψ') : ℂ → ℝ) = ⇑ψ + ⇑ψ' from rfl, h1.laplacian_add h2]
  ring

theorem lapH_zero : lapH 0 = 0 := by
  have := lapH_add 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem lapH_sum {ι : Type*} (s : Finset ι) (ψ : ι → TestOn upperHalfPlaneOpens) :
    lapH (∑ k ∈ s, ψ k) = ∑ k ∈ s, lapH (ψ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lapH_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lapH_add, ih]

theorem lapTest_eq_lapH {U : TopologicalSpace.Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) (f : MarkovZB.zsSub (U : Set ℂ))
    (ψ : TestOn upperHalfPlaneOpens) (hψ : ⇑ψ = f.1) : lapTest U f = lapH ψ :=
  lapTest_congr hU le_rfl f (MarkovAsm.toZs ψ) hψ.symm

/-! ### The explicit active mean annihilates Laplacians -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The explicit mean is harmonic off the hull**: `∫ 𝔥_σ lapH ψ = 0` for a test off `K_σ`. -/
theorem integral_couplingMean_lapH_eq_zero (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < ζ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} (hvL : ∀ i, vL i ≤ 0)
    (hvR : ∀ i, 0 ≤ vR i) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    {ψ : TestOn upperHalfPlaneOpens} (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath w) (σ : ℝ))) :
    ∫ z, couplingMean κ (Ito.rpath w) σ u z * lapH ψ z = 0 := by
  obtain ⟨T₂, hσT₂, hT₂ζ⟩ := exists_btwn_lt hσ
  set W' : ℝ → ℝ := Ito.rpath (clampAt w T₂) with hW'
  have hW'c : Continuous W' := (continuous_clampAt hw hT₂ζ).comp continuous_real_toNNReal
  have hσ0 : (0 : ℝ) ≤ σ := σ.coe_nonneg
  have heq : EqOn (Ito.rpath w) W' (Icc 0 (T₂ : ℝ)) := eqOn_rpath_clampAt T₂
  have hσle : (σ : ℝ) ≤ T₂ := by exact_mod_cast hσT₂.le
  have hK : fwdHull (Ito.rpath w) (σ : ℝ) = fwdHull W' σ := fwdHull_clampAt hσT₂
  set g : ℂ → ℝ := fun y => Ito.meanHarmonic κ ρL ρR vL vR (fwdMap W' σ y) - chiC κ * (logDerivFwd W' σ y).im
  have hg : InnerProductSpace.HarmonicOnNhd g (H \ fwdHull W' σ) :=
    MartMeans.harmonicOnNhd_meanHarmonic_fwdMap κ ρL ρR vL vR hW'c hσ0
  have hU : IsOpen (H \ fwdHull W' σ) := FwdHolo.isOpen_compl_fwdHull hW'c hσ0
  have hsupp : tsupport (MarkovZB.zsTest (MarkovAsm.toZs ψ).2 : ℂ → ℝ) ⊆ H \ fwdHull W' σ := by
    intro z hz
    refine ⟨ψ.tsupport_subset hz, fun hzK => ?_⟩
    rw [← hK] at hzK
    exact Set.disjoint_left.1 hψ hz hzK
  have hint := HarmLoc.integral_mul_cmTest_of_harmonic hU hg (MarkovZB.zsTest (MarkovAsm.toZs ψ).2) hsupp
  rw [← hint, coe_lapH]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport ψ
  · have hzU : z ∈ H \ fwdHull W' σ := hsupp hz
    have hfH : fwdMap W' σ z ∈ H := FwdHolo.mapsTo_fwdMap hW'c hσ0 hzU
    have e1 : fwdMap (Ito.rpath w) σ z = fwdMap W' σ z := Ito.fwdMap_congr_of_eqOn_of_le heq hσle
    have e2 : logDerivFwd (Ito.rpath w) σ z = logDerivFwd W' σ z :=
      Ito.logDerivFwd_congr_of_eqOn heq hσ0 hσle
    show couplingMean κ (Ito.rpath w) σ u z * _ = g z * _
    rw [Ito.couplingMean_eq_meanHarmonic hvL hvR hu (e1 ▸ hfH), e1, e2]
  · have h0 : cmTest (MarkovZB.zsTest (MarkovAsm.toZs ψ).2) z = 0 := by
      have hz' : z ∉ tsupport (lapH ψ) := fun h' => hz (tsupport_lapH_subset ψ h')
      rw [← coe_lapH]; exact image_eq_zero_of_notMem_tsupport hz'
    simp [h0]

end Path

/-! ### The conditional means of Laplacian tests vanish on labels -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Active labels**: almost surely on `{supp ψ ∩ K_σ = ∅}`, `E[(h, lapH ψ) | 𝓕_σ] = 0`. -/
theorem ae_condExp_lapH_eq_zero_of_active (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (σ ω)) →
      (P[fun ω' => h ω' (lapH ψ) | hσ.measurableSpace]) ω = 0 := by
  filter_upwards [ae_condExp_pairing_eq_actMean hC hX hσ hσζ (lapH ψ), hC.1.2.2.2.2, hσζ] with ω h1 hp hlt hd
  rw [h1 (hd.mono_left (tsupport_lapH_subset ψ)), actMean]
  exact integral_couplingMean_lapH_eq_zero (w := (W · ω)) hp.2.2.2.1 hlt
    (fun i => sub_nonpos.2 (hp.2.2.2.2.2.2.2.1 _ hlt i)) (fun i => sub_nonneg.2 (hp.2.2.2.2.2.2.2.2.1 _ hlt i))
    (bheAt_spec κ ρL ρR _ _ _) hd

/-- **Pocket labels** (the second conclusion of the birth step): almost surely, if `supp ψ` is swallowed at once by
`σ`, then `E[(h, lapH ψ) | 𝓕_σ] = 0`. -/
theorem ae_condExp_lapH_eq_zero_of_pocket (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, IsPocketLabel (W · ω) (tsupport ψ) (σ ω) →
      (P[fun ω' => h ω' (lapH ψ) | hσ.measurableSpace]) ω = 0 := by
  obtain ⟨u₀, hu₀⟩ := exists_bhe κ ρL ρR xL xR
  by_cases h0 : tsupport (lapH ψ) = ∅
  · have hz : lapH ψ = 0 := by
      ext z; exact image_eq_zero_of_notMem_tsupport (by rw [h0]; exact notMem_empty z)
    have e : (fun ω' => h ω' (lapH ψ)) = 0 := by funext ω'; rw [hz, map_zero]; rfl
    refine Eventually.of_forall fun ω _ => ?_
    rw [e, condExp_zero]; rfl
  have hne : (tsupport (lapH ψ)).Nonempty := nonempty_iff_ne_empty.2 h0
  set Q : ℝ≥0 → Ω → Prop := fun t ω => Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ))
  set Ev : Ω → ℝ≥0 → Prop := fun ω β => ∀ z ∈ tsupport ψ, swallowTime (Ito.rpath (W · ω)) z = β
  have hsupp : ∀ c : ℝ, tsupport ⇑(c • (lapH ψ + 0)) ⊆ tsupport ψ := fun c =>
    (tsupport_smul_subset_right (fun _ => c) _).trans (by rw [add_zero]; exact tsupport_lapH_subset ψ)
  have hb := (ae_condExp_exp_eq_cmKer_of_birth hC hκ hu₀ hX hσ hσζ hσN (lapH ψ) 0 Q Ev
    (fun c τ hτ hτζ _ => by
      filter_upwards [ae_condExp_exp_eq_cmKer_of_active hC hX hτ hτζ (c • (lapH ψ + 0))] with ω hω hQ
      exact hω (hQ.mono_left (hsupp c)))
    (fun ω β hβ hEv => ⟨0, hβ, fun t _ htβ =>
      isActiveLabel_of_lt_swallowTime (w := (W · ω)) fun z hz => by rw [hEv z hz]; exact_mod_cast htβ⟩)).2
    (fun τ hτ hτζ _ => by
      filter_upwards [ae_condExp_lapH_eq_zero_of_active hC hX hτ hτζ ψ] with ω hω hQ
      rw [add_zero]; exact hω hQ)
  filter_upwards [hb] with ω hω ⟨β, hβσ, hβ⟩
  have := hω β hβσ hβ ⟨hne, fun z hz => hβ z (tsupport_lapH_subset ψ hz), fun z hz => by
    have e0 : (⇑(0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 := rfl
    rw [e0, tsupport_zero] at hz
    exact absurd hz (notMem_empty z)⟩
  rwa [add_zero] at this

/-- **Labels**: almost surely, if `supp ψ` is a label at `σ`, then `E[(h, lapH ψ) | 𝓕_σ] = 0`. -/
theorem ae_condExp_lapH_eq_zero_of_isLabel (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, IsLabel (W · ω) (tsupport ψ) (σ ω) →
      (P[fun ω' => h ω' (lapH ψ) | hσ.measurableSpace]) ω = 0 := by
  filter_upwards [ae_condExp_lapH_eq_zero_of_active hC hX hσ hσζ ψ,
    ae_condExp_lapH_eq_zero_of_pocket hC hκ hX hσ hσζ hσN ψ] with ω h1 h2 hl
  rcases hl with ha | hp
  · exact h1 ha
  · exact h2 hp

/-- **Off the label set**: almost surely, if `supp ψ` avoids `offLabels G` (the complement of the labelled rational
balls), then `E[(h, lapH ψ) | 𝓕_σ] = 0` (pieces of a partition of unity at a fine scale are labels). -/
theorem ae_condExp_lapH_eq_zero_of_disjoint (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N) {G : ℚ × ℚ × ℚ → Set Ω}
    (hGgood : ∀ ω q, ω ∈ G q → IsGoodBall q)
    (hGall : ∀ᵐ ω ∂P, ∀ q, IsGoodBall q → (ω ∈ G q ↔ IsLabel (W · ω) (closedBall (qCentre q) (qRad q)) (σ ω)))
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Disjoint (tsupport ψ) (offLabels G ω) →
      (P[fun ω' => h ω' (lapH ψ) | hσ.measurableSpace]) ω = 0 := by
  obtain ⟨R, hR⟩ := ψ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  have hint := integrable_pairing hC
  have hpieces : ∀ n : ℕ, ∀ᵐ ω ∂P, (∀ k ∈ WangWu.pouIdx (WangWu.scaleIdx R n),
      IsLabel (W · ω) (tsupport (WangWu.pouTest ψ n k)) (σ ω)) →
      (P[fun ω' => h ω' (lapH ψ) | hσ.measurableSpace]) ω = 0 := by
    intro n
    set I := WangWu.pouIdx (WangWu.scaleIdx R n)
    have hsum : lapH ψ = ∑ k ∈ I, lapH (WangWu.pouTest ψ n k) := by
      rw [← lapH_sum, WangWu.sum_pouTest hR (WangWu.le_scaleIdx R n)]
    have e : (fun ω' => h ω' (lapH ψ)) = ∑ k ∈ I, fun ω' => h ω' (lapH (WangWu.pouTest ψ n k)) := by
      funext ω'; rw [hsum, map_sum, Finset.sum_apply]
    have hcs := condExp_finsetSum (m := hσ.measurableSpace) (μ := P)
      (fun k _ => hint (lapH (WangWu.pouTest ψ n k))) (s := I)
    filter_upwards [hcs, (eventually_all_finset I).2 fun k _ =>
      ae_condExp_lapH_eq_zero_of_isLabel hC hκ hX hσ hσζ hσN (WangWu.pouTest ψ n k)] with ω h1 h2 hl
    rw [e, h1, Finset.sum_apply]
    exact Finset.sum_eq_zero fun k hk => h2 k hk (hl k hk)
  filter_upwards [ae_all_iff.2 hpieces, hGall] with ω hω hgω hd
  obtain ⟨n₀, hn₀⟩ := exists_scale_isLabel (fun q hq => (hgω q (hGgood ω q hq)).1 hq) ψ hd
  exact hω n₀ fun k _ => hn₀ n₀ le_rfl k

end Coupling

end WholeField

end InteractingSLE
