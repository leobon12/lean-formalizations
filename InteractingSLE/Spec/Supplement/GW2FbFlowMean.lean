/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3ChainUnion

/-!
# The hull mean of a coupling at a stopping time, at its flowed marks

Packet PROVE-GW2-FABLE. GB9, p. 525 ("Their own exposed germs survive by the protected-collar comparison"): the input
`hind₂` of `Supp8.Q3Rel.ae_eqOn_unionMean_of_relConfigOff` for GW2, where the explored curve is the flow line. A flow
line of GW2 may reach a continuation threshold, so its lifetime is finite and its hull is a local set only at
stopping times before the lifetime; `Supp8.Q3Chain.ae_eqOn_cfMean` (GB6's explored counterflow) is stated at
deterministic times for an infinite lifetime and a counterflow word.

* **`ae_eqOn_explMean_stop`**: for an optional hull coupling of ANY force word (parameter `k > 0`), a stopping time
  `τ < ζ` of its driving filtration, a hitting-measurable version `K` of the hull `K_τ` and a local-set mean `g₂` of
  `K` for the centred field: almost surely, for every globally continuous driver `D` from `0` that agrees with the
  coupling's driver on `[0, t₂]` for some `t₂ > τ` (e.g. the driver frozen before the lifetime), every harmonic
  representative `w₂` of `g₂` off `K` satisfies `w₂ + 𝔥⁰ = G_E ∘ f_τ − χ arg f_τ′` off `K`, for every bounded harmonic
  extension `G_E` of the force data at the marks flowed by `D` to `τ` (`Supp8.Q3Chain.flowedData`).

Same proof as `ae_eqOn_cfMean`: `Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull` (already stated at stopping
times and for every word), `Supp8.Q3Chain.ae_gap_eq_markPos`, uniqueness of bounded harmonic extensions and of harmonic
functions with the same test integrals. Conditional helper with a distinct name; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Fb

open LocalSets Supp8.Q3Chain

/-- **The hull mean of a coupling at a stopping time, at its flowed marks.** -/
theorem ae_eqOn_explMean_stop {k : ℝ} (hk : 0 < k) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {X : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling k xL xR ρL ρR P 𝓕 W VL VR B ζ X) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData k ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField X u₀) P)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {K : Ω → Set ℂ}
    (hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hKm : Measurable[mΩ, hittingSigma] K) {g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg₂ : IsLocalSetMean K (WholeField.centredField X u₀) P g₂) :
    ∀ᵐ ω ∂P, ∀ (D : ℝ → ℝ) (t₂ : ℝ), Continuous D → D 0 = 0 → (((τ ω).untopD 0 : ℝ≥0) : ℝ) < t₂ →
      (∀ r ∈ Icc (0 : ℝ) t₂, D r = W r.toNNReal ω) →
      ∀ GE : ℂ → ℝ, IsBoundedHarmonicExtension (flowedData k ρL ρR xL xR D ((τ ω).untopD 0 : ℝ≥0))
          (flowedJumps xL xR D ((τ ω).untopD 0 : ℝ≥0)) GE →
        ∀ w₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₂ (H \ K ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ K ω → g₂ ω φ = ∫ z, w₂ z * φ z) →
          EqOn (fun z => w₂ z + u₀ z)
            (fun z => GE (fwdMap D ((τ ω).untopD 0 : ℝ≥0) z) -
              QuantumZipper.chiC k * (logDerivFwd D ((τ ω).untopD 0 : ℝ≥0) z).im) (H \ K ω) := by
  classical
  -- bounded harmonic extensions of the coupling's force data at `τ`
  set u : Ω → ℂ → ℝ := fun ω => (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData k ρL ρR
    (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
    (fun j => VR j ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)).choose with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData k ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω) := fun ω =>
    (Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData k ρL ρR
      (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
      (fun j => VR j ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)).choose_spec
  have htr : ∀ ω, IsTranslateAddConst 0 (0 * 0) (X ω) (X ω) := fun ω =>
    Sec7.StripSysField.isTranslateAddConst_zero_self (X ω) 0
  have hmean := Sec7.SideHeight.ae_apply_eq_of_isLocalSetMean_flowHull hC hk htr hh0 hu₀.1 hu₀
    (fun z _ => by simp) hX hτ hτζ hKm
    (by
      filter_upwards [hKeq] with ω hω
      simp only [hω, Complex.ofReal_zero, add_zero, image_id']) hg₂ hu
  filter_upwards [hmean, ae_gap_eq_markPos hC, hτζ, hKeq] with ω hmω hgap hlt hKω D t₂ hD hD0 ht₂ hDW GE hGE w₂
    hw₂ hrep
  -- the stopping time is finite at `ω`
  have hne : τ ω ≠ ⊤ := fun h => by
    rw [h] at hlt
    exact not_top_lt hlt
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 hne
  have hTu : (τ ω).untopD 0 = T := by rw [← hT, WithTop.untopD_coe]
  rw [hTu] at hKω hmω ht₂ hGE ⊢
  have hTlt : (T : ℝ≥0∞) < ζ ω := by
    rw [← hT] at hlt
    exact hlt
  have hDs : ∀ s : ℝ≥0, s ≤ T → D s = W s ω := fun s hs => by
    have h1 := hDW (s : ℝ) ⟨s.2, (NNReal.coe_le_coe.2 hs).trans ht₂.le⟩
    rwa [Real.toNNReal_coe] at h1
  obtain ⟨hL, hR⟩ := hgap D hD hD0 T hTlt hDs
  -- the coupling's extension is the flowed one
  have huω : IsBoundedHarmonicExtension (flowedData k ρL ρR xL xR D T) (flowedJumps xL xR D T) (u ω) := by
    have h1 := hu ω
    rw [hTu] at h1
    rw [flowedJumps, coe_initJumps]
    simp only [flowedData]
    simp only [hL, hR] at h1
    exact h1
  have hGEu : EqOn GE (u ω) H :=
    Impl.eqOn_of_isBoundedHarmonicExtension (Finset.finite_toSet _) huω hGE
  -- the frozen driver and the coupling's driver have the same hull and maps at `T`
  have hWD : ∀ r ∈ Icc (0 : ℝ) t₂, (fun r : ℝ => W r.toNNReal ω) r = D r := fun r hr => (hDW r hr).symm
  have hKD : K ω = fwdHull D T := by
    rw [hKω]
    exact fwdHull_eq_of_eqOn T.coe_nonneg ht₂ hWD
  have hfm : ∀ z, fwdMap (fun r : ℝ => W r.toNNReal ω) T z = fwdMap D T z := fun z =>
    fwdMap_eq_of_eqOn T.coe_nonneg fun r hr => hWD r ⟨hr.1, hr.2.trans ht₂.le⟩
  have hfl : ∀ z, logDerivFwd (fun r : ℝ => W r.toNNReal ω) T z = logDerivFwd D T z := fun z =>
    Ito.logDerivFwd_congr_of_eqOn (fun r hr => hWD r ⟨hr.1, hr.2.trans ht₂.le⟩) T.coe_nonneg le_rfl
  rw [hKD] at hmω hw₂ hrep ⊢
  -- the two harmonic representatives
  have hO : IsOpen (H \ fwdHull D T) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hD T.2
  have hcm := Sec7.SideHeight.harmonicOnNhd_couplingMean (κ := k) hD T.coe_nonneg huω.1
  have hm2 : InnerProductSpace.HarmonicOnNhd (fun z => couplingMean k D T (u ω) z - u₀ z)
      (H \ fwdHull D T) := fun z hz => (hcm z hz).sub (hu₀.1 z hz.1)
  have heq : EqOn w₂ (fun z => couplingMean k D T (u ω) z - u₀ z) (H \ fwdHull D T) := by
    refine Sec6.eqOn_of_integral_mul_eq hO sdiff_subset hw₂ hm2 fun φ hφ => ?_
    rw [← hrep φ hφ, hmω φ hφ]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [Complex.ofReal_zero, sub_zero, mul_zero, couplingMean, hfm, hfl]
  intro z hz
  have h1 := heq hz
  have h2 := hGEu (QuantumZipper.FwdHolo.mapsTo_fwdMap hD T.coe_nonneg hz)
  simp only [couplingMean] at h1
  show w₂ z + u₀ z = GE (fwdMap D T z) - QuantumZipper.chiC k * (logDerivFwd D T z).im
  rw [h1]
  linarith

end InteractingSLE.Theorem14.GW2Fb
