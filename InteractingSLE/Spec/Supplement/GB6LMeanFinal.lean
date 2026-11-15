/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LMeanDet
import InteractingSLE.Spec.Supplement.GB6LineL4
import InteractingSLE.Spec.Sec5.Aux61SlitVChart

/-!
# GB6's union mean, part 5: `GB6LineMeanStatement` from Theorems 1.2–1.3

Packet PROVE-GB6-LINEMEAN. **`gb6LineMeanStatement_of_thm12_thm13`**: Theorem 1.4's named input (L3)
`GB6LineL.GB6LineMeanStatement` (the union mean identification at GB6's physical lines) follows from Theorems 1.2–1.3
(R48: GB6 serves Theorem 1.4; Theorems 1.2–1.3 enter only through `Exist.Param12.hasFieldDeterminedHistories`). Hence
**`gb6HullDetStatement_of_thm12_thm13`**: Theorem 1.4's `GB6HullDetStatement` from Theorems 1.2–1.3 alone.

Steps (for a counterflow time `t`, a version `B` of the physical union and a local-set mean `g` of `B t`):

* the retained mean on `{s < ζα}` (`GB6LMean.ae_eqOn_retMean`);
* the union mean of `retSet ∪ K_t` with a relative chain `Wr` generating every relative hull up to `a(t)`
  (`GB6LMean.ae_eqOn_unionMean_gb6_hull`), transferred to `B t` (`ae_eqOn_mean_of_marked`; both sets are marked local
  for `𝓕^α_s ∨ 𝓕^cf_t`) — `ae_rep_unionMean`; at `t = 0` the retained mean transferred to `B 0` — `ae_rep_retMean`;
* on the live event before the stop: `Wr = R` on `[0, a(t)]` (`eqOn_of_hullsUpTo` with the version's hull clause), the
  relative chart's lift `Im relLog − 2π`, and the typed word (`eqOn_bheProc_of_cfFlowed`) — the transport identity
  `chartTransport_eq_couplingMean` (deterministic).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Supp8.GB6LMean

open LocalSets

/-! ### The transport identity (deterministic) -/

section Transport

open GB6 Exist.StagedLaw Theorem14.GW2JointKernel RelSafeS

/-- **The transport of a represented union mean through the relative chart is the canonical relative mean.** Let `r`
be a record of time `s` whose driver agrees with `U` on `[0, s]`, `S ⊆ ℍ` with `ℍ ∖ S` the inverse chart image of the
complement of the relative hull `K̃_u = fwdHull Rp u`, `g'` represented on `ℍ ∖ S` by `wU`, and `wU + 𝔥⁰` the candidate
`G ∘ g̃_u ∘ Ψ − χ(16/κ) (Im log g̃_u′ ∘ Ψ + Im relLog)` of a driver `Wr` equal to `Rp` on `[0, u]`, with `G = Gb` on
`ℍ`. Then for every test `ψ` off `K̃_u`,
`chartTransport (relChart r) 1 (2πχ) χ (g' + 𝔥⁰) ψ = ∫ couplingMean Rp u Gb ψ`. -/
theorem chartTransport_eq_couplingMean (κ : ℝ) {r : RecData} {s : ℝ≥0} (hr : rtime r = s) {U : ℝ → ℝ}
    (hU : ∀ x ∈ Icc (0 : ℝ) s, rdrv r x = U x) {S : Set ℂ} {Rp Wr : ℝ → ℝ} {u : ℝ≥0}
    (hO : H \ S = (relChart r).2.1 '' (H \ fwdHull Rp u)) {g' : DistOn upperHalfPlaneOpens} {wU u₀ : ℂ → ℝ}
    (hwU : InnerProductSpace.HarmonicOnNhd wU (H \ S)) (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hrep : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ S → g' φ = ∫ z, wU z * φ z) {G Gb : ℂ → ℝ}
    (hv : EqOn (fun z => wU z + u₀ z)
      (fun z => G (fwdMap Wr u (relMap U s z)) -
        chiC (16 / κ) * ((logDerivFwd Wr u (relMap U s z)).im + (Q3Rel.relLog U s z).im)) (H \ S))
    (hWR : EqOn Wr Rp (Icc 0 (u : ℝ))) (hRp : Continuous Rp) (hGG : EqOn G Gb H)
    {ψ : TestOn upperHalfPlaneOpens} (hψ : Disjoint (tsupport ψ) (fwdHull Rp u)) :
    Chart.chartTransport (isConformal_relChart r) 1 (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ))
        (g' + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
      ∫ y, couplingMean (16 / κ) Rp u Gb y * ψ y := by
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hc := isConformal_relChart r
  have hrel : relChart r = jointChart (rdrv r) s := relChart_eq_jointChart hr
  have hinv : ∀ y, (relChart r).2.1 y = (jointChart (rdrv r) s).2.1 y := fun y => by rw [hrel]
  have hlift : ∀ z, (relChart r).2.2 z = (jointChart (rdrv r) s).2.2 z := fun z => by rw [hrel]
  have hSH : H \ S ⊆ H := sdiff_subset
  have hψO : tsupport ψ ⊆ H \ fwdHull Rp u := fun y hy =>
    ⟨Coupling.tsupport_subset_H ψ hy, Set.disjoint_left.1 hψ hy⟩
  have hmc : ContinuousOn (fun z => wU z + u₀ z) ((relChart r).2.1 '' (H \ fwdHull Rp u)) := by
    rw [← hO]
    exact (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hwU).add
      ((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀).mono hSH)
  have hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (relChart r).2.1 '' (H \ fwdHull Rp u) →
      (g' + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, (wU z + u₀ z) * φ z := fun φ hφ => by
    rw [← hO] at hφ
    have hu₀c : ContinuousOn u₀ H := Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hu₀
    have hi₁ : Integrable fun z => wU z * φ z :=
      WholeField.integrable_mul_testOn (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd hwU) φ hφ
    have hi₂ : Integrable fun z => u₀ z * φ z := WholeField.integrable_mul_testOn hu₀c φ (hφ.trans hSH)
    rw [add_apply, hrep φ hφ, Coupling.smoothDist_apply_eq hu₀c φ, ← integral_add hi₁ hi₂]
    simp only [add_mul]
  rw [Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset hc (continuousOn_lift_relChart r) sdiff_subset hmc
    hT (2 * Real.pi * chiC (16 / κ)) (chiC (16 / κ)) hψO]
  refine congrArg _ (funext fun y => ?_)
  by_cases hy : y ∈ tsupport ψ
  · have hyO := hψO hy
    have hyH : y ∈ H := hyO.1
    set z := (relChart r).2.1 y with hz
    have hzS : z ∈ H \ S := by rw [hO]; exact mem_image_of_mem _ hyO
    have hrelM : relMap U s = relMap (rdrv r) s := (relMap_eq_of_eqOn s.coe_nonneg fun x hx => hU x hx).symm
    have hrelL : Q3Rel.relLog U s = Q3Rel.relLog (rdrv r) s :=
      (Q3Chain.relLog_eq_of_eqOn s.coe_nonneg fun x hx => hU x hx).symm
    have hΨ : relMap U s z = y := by
      rw [hrelM, hz, hinv]
      exact relMap_jointChart_inv hw hw0 s.coe_nonneg hyH
    have hℓ : (relChart r).2.2 z = (Q3Rel.relLog U s z).im - 2 * Real.pi := by
      rw [hz, hlift, hinv, hrelL]
      exact jointChart_lift_inv hw hw0 s.coe_nonneg hyH
    have hfM : fwdMap Wr u y = fwdMap Rp u y := fwdMap_eq_of_eqOn u.coe_nonneg fun x hx => hWR hx
    have hfL : logDerivFwd Wr u y = logDerivFwd Rp u y := Ito.logDerivFwd_congr_of_eqOn hWR u.coe_nonneg le_rfl
    have hfH : fwdMap Rp u y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hRp u.coe_nonneg hyO
    have hvz := hv hzS
    simp only at hvz
    rw [hvz, hℓ, hΨ, hfM, hfL, hGG hfH]
    simp only [couplingMean]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

end Transport

/-! ### The union mean for every version of the physical union -/

section Union

open GB6 Exist.StagedLaw GB6LineL Q3Chain RelSafeS WholeField

/-- **Local-set means of almost surely equal sets agree**, when one of them is marked local and recorded by its
marks. -/
theorem ae_mean_eq_of_ae_eq {Ω : Type u} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A B : Ω → Set ℂ}
    (hAm : Measurable[mΩ, hittingSigma] A) (hBm : Measurable[mΩ, hittingSigma] B)
    (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω)) (hAB : ∀ᵐ ω ∂P, A ω = B ω) (hℳ : ℳ ≤ mΩ)
    (hloc : IsHistoryAvoidanceLocal ℳ A h P) (hAℳ : Measurable[ℳ, hittingSigma] A)
    {gA gB : Ω → DistOn upperHalfPlaneOpens} (hgA : IsLocalSetMean A h P gA) (hgB : IsLocalSetMean B h P gB) :
    ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gB ω φ = gA ω φ := by
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [hAB, hBc] with ω h1 h2
    rw [h1]
    exact h2
  have hlocB : IsHistoryAvoidanceLocal ℳ B h P := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae hAB hloc
  have h := ae_eqOn_mean_of_marked hh hAm hBm hAc hBc le_rfl hℳ hloc hlocB hAℳ
    (by filter_upwards [hAB] with ω hω; rw [hω]) MeasurableSet.univ
    (by filter_upwards [hAB] with ω hω _ using hω) hgA hgB
  filter_upwards [h] with ω hω
  exact hω trivial

/-- **The union mean represented on the complement of every version `B` of the physical union** (counterflow time
`t > 0`). In GB6's setting, with the retained set marked local together with the counterflow hull (marks `ℳ`) and the
retained mean known (`hret`, from `ae_eqOn_retMean`): almost surely on `{s < ζα, α(s) ∈ ℍ, t < T_c}` there are a
relative chain `Wr` generating every relative hull up to `a(t)`, a bounded harmonic extension `G` of the relative word,
and a harmonic representative `wU` of the local-set mean of `B` with `wU + 𝔥⁰ = G ∘ g̃_u ∘ Ψ − χ (Im log g̃_u′ ∘ Ψ +
Im relLog)` off `B`. -/
theorem ae_rep_unionMean {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u}
    {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    {b' : ℝ → ℝ} {J' : Finset ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b' J' 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b' J' 0) → ℝ≥0 → Ω → ℝ}
    {Bc : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling (16 / κ) (flowLineXL b' J' 0) (flowLineXR b' J' 0) (flowLineRhoL (16 / κ) b' J' 0 0)
      (flowLineRhoR (16 / κ) b' J' 0 0) P 𝓕 W VL VR Bc ζ h')
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h' u₀) P)
    (c : Restart.BoundaryWord) (s t : ℝ≥0) (ht0 : 0 < t) (hℳ : ℳ ≤ mΩ)
    (hlocU : IsHistoryAvoidanceLocal ℳ
      (fun ω => retSet s Wα ζα ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω))
      (centredField h' u₀) P)
    (hUℳ : Measurable[ℳ, hittingSigma]
      (fun ω => retSet s Wα ζα ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω)))
    (hdA : MeasurableSpace.comap (retSet s Wα ζα) hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P)
    (hlA : IsLocalSet (retSet s Wα ζα) (centredField h' u₀) P)
    (hret : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (retSet s Wα ζα) (centredField h' u₀) P g₁ →
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω →
        ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
            (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
            (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ retSet s Wα ζα ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ retSet s Wα ζα ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
                chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
              (H \ retSet s Wα ζα ω))
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBeq : ∀ᵐ ω ∂P, B ω = retSet s Wα ζα ω ∪ fwdHull (fun r : ℝ => W r.toNNReal ω) t)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B (centredField h' u₀) P g) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
        ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
      ∃ (Wr : ℝ → ℝ) (G wU : ℂ → ℝ), Continuous Wr ∧ Wr 0 = 0 ∧
        HullsUpTo (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) Wr t ∧
        IsBoundedHarmonicExtension
          (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
            (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
            (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t))
          (cfFlowedJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
            (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps Wr
            (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)) G ∧
        InnerProductSpace.HarmonicOnNhd wU (H \ B ω) ∧
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → g ω φ = ∫ z, wU z * φ z) ∧
        EqOn (fun z => wU z + u₀ z)
          (fun z => G (fwdMap Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
              (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)) -
            chiC (16 / κ) *
              ((logDerivFwd Wr (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W r.toNNReal ω) t)
                (relMap (fun r : ℝ => Wα r.toNNReal ω) s z)).im +
                (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im))
          (H \ B ω) := by
  classical
  have hk : 0 < 16 / κ := by positivity
  have hX := hC.2.2.2.1
  set K : Ω → Set ℂ := fun ω => Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VL VR ζ ω) with hKdef
  have hKm : Measurable[mΩ, hittingSigma] K := measurable_cfHull hX t
  have hKeq : ∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) t := ae_cfHull_eq hC hζ t
  have hAm : Measurable[mΩ, hittingSigma] (retSet s Wα ζα) :=
    (measurable_retOfRec s).comp (measurable_recOf_cfE hF s).2
  have hUm : Measurable[mΩ, hittingSigma] (fun ω => retSet s Wα ζα ω ∪ K ω) := hUℳ.mono hℳ le_rfl
  have hUB : ∀ᵐ ω ∂P, retSet s Wα ζα ω ∪ K ω = B ω := by
    filter_upwards [hKeq, hBeq] with ω hK hB
    rw [hB, hK]
  have hUc : ∀ᵐ ω ∂P, retSet s Wα ζα ω ∪ K ω ⊆ H ∧ IsOpen (H \ (retSet s Wα ζα ω ∪ K ω)) := by
    filter_upwards [hUB, hBc] with ω h1 h2
    rw [h1]
    exact h2
  have hlU : IsLocalSet (fun ω => retSet s Wα ζα ω ∪ K ω) (centredField h' u₀) P :=
    ((isLocalSet_tfae hh0 hUm hUc).out 4 1).2 hlocU.isAvoidanceLocal
  -- the three local-set means
  obtain ⟨gU, hgU⟩ := isGermConditionalLaw_iff.1 (hlocU.isAvoidanceLocal.isGermConditionalLaw hh0 hUm hUc)
  have hAc : ∀ᵐ ω ∂P, retSet s Wα ζα ω ⊆ H ∧ IsOpen (H \ retSet s Wα ζα ω) :=
    Eventually.of_forall fun ω => ⟨retSet_subset_H s Wα ζα ω, isOpen_H_diff_retSet s Wα ζα ω⟩
  obtain ⟨g₁, hg₁⟩ := isGermConditionalLaw_iff.1
    (IsAvoidanceLocal.isGermConditionalLaw hh0 hAm hAc (((isLocalSet_tfae hh0 hAm hAc).out 4 1).1 hlA))
  have hlocK := isHistoryAvoidanceLocal_cfHull hC hk hζ hu₀ t
  have hKc : ∀ᵐ ω ∂P, K ω ⊆ H ∧ IsOpen (H \ K ω) := by
    filter_upwards [hKeq, hW] with ω hK hWω
    rw [hK]
    exact ⟨(QuantumZipper.fwdHull_mono.2 _),
      QuantumZipper.FwdHolo.isOpen_compl_fwdHull (hWω.1.comp continuous_real_toNNReal) t.coe_nonneg⟩
  obtain ⟨g₂, hg₂⟩ := isGermConditionalLaw_iff.1 (hlocK.isAvoidanceLocal.isGermConditionalLaw hh0 hKm hKc)
  -- the union mean with the earlier hull identities
  have hmain := ae_eqOn_unionMean_gb6_hull hκ hκ4 hF hα hC hζ hW hu₀ hh0 c s t ht0 univ (A := retSet s Wα ζα)
    (by
      filter_upwards [GB6.ae_driver_zero_continuousOn hF] with ω hω _ hs
      exact retSet_eq_invHull hs hω.1 hω.2)
    (Eventually.of_forall fun ω => not_isBounded_lowerUnion_retSet s Wα ζα ω) hKeq hAm hKm hdA hlA hlU hgU hg₁
    hg₂
    (by
      filter_upwards [hret g₁ hg₁] with ω hω _ hs _ G₀ hG₀ w₁ hw₁ hr₁
      exact hω hs G₀ hG₀ w₁ hw₁ hr₁)
  -- the transfer to `B`
  have htr := ae_mean_eq_of_ae_eq hh0 hUm hBm hBc hUB hℳ hlocU hUℳ hgU hg
  filter_upwards [hmain, htr, hUB, hgU.2.1] with ω hω htrω hUBω hharm hs hsH htc
  obtain ⟨Wr, ηr, G, hWr, hWr0, -, -, -, hHU, hG, hU⟩ := hω trivial hs hsH htc
  obtain ⟨wU, hwU, hrepU⟩ := hharm
  have hwU' : InnerProductSpace.HarmonicOnNhd wU (H \ B ω) := by rw [← hUBω]; exact hwU
  have hrepU' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → gU ω φ = ∫ z, wU z * φ z :=
    fun φ hφ => hrepU φ (by rw [hUBω]; exact hφ)
  refine ⟨Wr, G, wU, hWr, hWr0, hHU, hG, hwU', fun φ hφ => by rw [htrω φ hφ, hrepU' φ hφ], ?_⟩
  have h1 := hU wU hwU (fun φ hφ => hrepU φ hφ)
  rw [hUBω] at h1
  exact h1

/-- **The retained mean represented on the complement of every version `B` of the retained set** (counterflow time
`0`). -/
theorem ae_rep_retMean {κ θ : ℝ} {Ω : Type u} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h' : Ω → DistOn upperHalfPlaneOpens} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    {u₀ : ℂ → ℝ} (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h' u₀) P)
    (c : Restart.BoundaryWord) (s : ℝ≥0) (hℳ : ℳ ≤ mΩ)
    (hAm : Measurable[mΩ, hittingSigma] (retSet s Wα ζα))
    (hlocA : IsHistoryAvoidanceLocal ℳ (retSet s Wα ζα) (centredField h' u₀) P)
    (hAℳ : Measurable[ℳ, hittingSigma] (retSet s Wα ζα))
    (hret : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (retSet s Wα ζα) (centredField h' u₀) P g₁ →
      ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω →
        ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
            (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
            (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ retSet s Wα ζα ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ retSet s Wα ζα ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
                chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im)
              (H \ retSet s Wα ζα ω))
    {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B) (hBc : ∀ᵐ ω ∂P, B ω ⊆ H ∧ IsOpen (H \ B ω))
    (hBeq : ∀ᵐ ω ∂P, B ω = retSet s Wα ζα ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean B (centredField h' u₀) P g) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → ∃ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ B ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ B ω → g ω φ = ∫ z, w₁ z * φ z) ∧
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
          (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ →
        EqOn (fun z => w₁ z + u₀ z)
          (fun z => G₀ (relMap (fun r : ℝ => Wα r.toNNReal ω) s z) -
            chiC (16 / κ) * (Q3Rel.relLog (fun r : ℝ => Wα r.toNNReal ω) s z).im) (H \ B ω) := by
  have hAc : ∀ᵐ ω ∂P, retSet s Wα ζα ω ⊆ H ∧ IsOpen (H \ retSet s Wα ζα ω) :=
    Eventually.of_forall fun ω => ⟨retSet_subset_H s Wα ζα ω, isOpen_H_diff_retSet s Wα ζα ω⟩
  obtain ⟨g₁, hg₁⟩ := isGermConditionalLaw_iff.1 (hlocA.isAvoidanceLocal.isGermConditionalLaw hh0 hAm hAc)
  have hAB : ∀ᵐ ω ∂P, retSet s Wα ζα ω = B ω := by
    filter_upwards [hBeq] with ω hω using hω.symm
  have htr := ae_mean_eq_of_ae_eq hh0 hAm hBm hBc hAB hℳ hlocA hAℳ hg₁ hg
  filter_upwards [htr, hret g₁ hg₁, hBeq, hg₁.2.1] with ω htrω hretω hBω hharm hs
  obtain ⟨w₁, hw₁, hrep₁⟩ := hharm
  refine ⟨w₁, by rw [hBω]; exact hw₁, fun φ hφ => by rw [htrω φ hφ, hrep₁ φ (by rw [← hBω]; exact hφ)],
    fun G₀ hG₀ => ?_⟩
  rw [hBω]
  exact hretω hs G₀ hG₀ w₁ hw₁ hrep₁

end Union

/-! ### Flowed marks of drivers agreeing up to a time -/

section Marks

open Exist.StagedLaw Q3Chain

theorem markPos_congr_eqOn {w w' : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hw' : Continuous w')
    (hw0' : w' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn w w' (Icc 0 t)) {x : ℝ} (hx : 0 ≤ x) :
    markPos w t x = markPos w' t x := by
  rw [Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hw hw0 ht hx,
    Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hw' hw0' ht hx, GB6.rightImg_congr hw' ht fun r hr => h hr,
    h ⟨ht, le_rfl⟩]

theorem markPosL_congr_eqOn {w w' : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) (hw' : Continuous w')
    (hw0' : w' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn w w' (Icc 0 t)) {x : ℝ} (hx : x ≤ 0) :
    markPosL w t x = markPosL w' t x := by
  unfold markPosL
  rw [markPos_congr_eqOn (w := fun s => -w s) (w' := fun s => -w' s) hw.neg (by simp [hw0]) hw'.neg
    (by simp [hw0']) ht (fun r hr => by simp only [h hr])
    (neg_nonneg.2 hx)]

/-- Extensions of the flowed counterflow data of two drivers agreeing up to `u`. -/
theorem bhe_cfFlowed_congr {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {w w' : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hw' : Continuous w') (hw0' : w' 0 = 0) {u : ℝ} (hu : 0 ≤ u) (h : EqOn w w' (Icc 0 u)) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (cfFlowedData k b J w u) (cfFlowedJumps b J w u) G) :
    IsBoundedHarmonicExtension (cfFlowedData k b J w' u) (cfFlowedJumps b J w' u) G := by
  have hL : (fun i => markPosL w u (flowLineXL b J 0 i)) = fun i => markPosL w' u (flowLineXL b J 0 i) :=
    funext fun i => markPosL_congr_eqOn hw hw0 hw' hw0' hu h (Theorem14.GW3Word.flowLineXL_nonpos _ _ i)
  have hR : (fun j => markPos w u (flowLineXR b J 0 j)) = fun j => markPos w' u (flowLineXR b J 0 j) :=
    funext fun j => markPos_congr_eqOn hw hw0 hw' hw0' hu h (Theorem14.GW3Word.flowLineXR_nonneg _ _ j)
  have e1 : cfFlowedData k b J w u = cfFlowedData k b J w' u := by
    simp only [cfFlowedData, flowedData]
    rw [hL, hR]
  have e2 : cfFlowedJumps b J w u = cfFlowedJumps b J w' u := by
    simp only [cfFlowedJumps, flowedJumps]
    rw [hL, hR]
  rw [← e1, ← e2]
  exact hG

/-- At time `0` the flowed counterflow data are the initial data. -/
theorem bhe_cfFlowed_zero {k : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {G : ℂ → ℝ} (hG : IsBoundedHarmonicExtension (cfData k b J) (cfJumps b J) G) :
    IsBoundedHarmonicExtension (cfFlowedData k b J w 0) (cfFlowedJumps b J w 0) G := by
  have hL : (fun i => markPosL w 0 (flowLineXL b J 0 i)) = flowLineXL b J 0 := funext fun i => by
    unfold markPosL
    rw [markPos_time_zero (w := fun s => -w s) hw.neg (by simp [hw0])
      (neg_nonneg.2 (Theorem14.GW3Word.flowLineXL_nonpos _ _ i)),
      neg_neg]
  have hR : (fun j => markPos w 0 (flowLineXR b J 0 j)) = flowLineXR b J 0 :=
    funext fun j => markPos_time_zero hw hw0 (Theorem14.GW3Word.flowLineXR_nonneg _ _ j)
  have e1 : cfFlowedData k b J w 0 = cfData k b J := by
    simp only [cfFlowedData, flowedData, cfData]
    rw [hL, hR]
  have e2 : cfFlowedJumps b J w 0 = cfJumps b J := by
    simp only [cfFlowedJumps, flowedJumps, cfJumps]
    rw [hL, hR]
  rw [e1, e2]
  exact hG

end Marks

/-! ### The main theorem -/

section Main

open GB6 GB6.RelDrv Exist.StagedLaw GB6LineL Q3Chain RelSafeS RelSafe Restart WholeField

/-- **Theorem 1.4's named input (L3), GB6's union mean identification, from Theorems 1.2–1.3.** -/
theorem gb6LineMeanStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : GB6LineMeanStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver w u₀ hu₀ hh0 B hBm hBc hBeq hBloc t g hg ψ
  classical
  have hk : 0 < 16 / κ := by positivity
  -- the flow line with the data of the word
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα :=
    (Exist.StagedLaw.isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 hfl
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  obtain ⟨uc, huc, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c.isPiecewiseConstantBoundaryData
  have hucb : IsBoundedHarmonicExtension b J uc := by
    have h1 : IsBoundedHarmonicExtension c.fn J uc := by rw [← hcJ]; exact huc
    exact (Restart.isBoundedHarmonicExtension_congr (fun y hy => hcb y hy) uc).1 h1
  have hGc : IsGFFWithBoundaryData P h c.fn c.jumps := by
    rw [hcJ]
    exact WangWu.isGFFWithBoundaryData_congr (fun y hy => (hcb y hy).symm) hG
  have hcen := Q3Chain.centredField_eq_reflect hκ hb hG hb' hG' hT hucb hu₀
  -- the counterflow coupling
  have hcf' := hcf
  obtain ⟨hcfF, 𝓕c, VLc, VRc, Bc, htrc, hCc⟩ := hcf'
  have e3 : hcfF = h' := funext fun ω => Theorem14.GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htrc ω)
  rw [e3] at hCc
  have hXc := hCc.2.2.2.1
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hcomp.mono fun ω hω => hω.1
  have hh₀m : Measurable (centredField h' u₀) := hh0.measurable
  -- determination of both curves (Theorems 1.2–1.3)
  have hdetc := Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine b' J' 0)
    P 𝓕c W VLc VRc Bc ζ h' hCc
  have hcomap' : MeasurableSpace.comap h' inferInstance ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P :=
    KernelTower.comap_le_aeSigma_comap (measurable_add_dist _)
      (Eventually.of_forall fun ω => (sub_add_cancel (h' ω)
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)).symm)
  have h𝓕c : ∀ t, drivingFiltration P hXc t ≤
      aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P := fun t =>
    (Q3Chain.drivingFiltration_le_aeSigma hdetc hXc t).trans (Q3Chain.aeSigma_le_of_le hcomap')
  have hdetα : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
      (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ (Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0)
  -- the retained set: marked local, and its mean
  obtain ⟨ℋ₁, -, hrecℋ₁, hℋ₁d, hloc₁⟩ := exists_retained_marks hκ hflc hdetα huc hh₀m (fun ω => hcen ω) s
  have hrecm := (measurable_recOf_cfE hfl s).2
  have hAm : Measurable[mΩ, hittingSigma] (retSet s Wα ζα) := (measurable_retOfRec s).comp hrecm
  have hAℋ : Measurable[ℋ₁.1, hittingSigma] (retSet s Wα ζα) := (measurable_retOfRec s).comp hrecℋ₁
  have hAc : ∀ᵐ ω ∂P, retSet s Wα ζα ω ⊆ H ∧ IsOpen (H \ retSet s Wα ζα ω) :=
    Eventually.of_forall fun ω => ⟨retSet_subset_H s Wα ζα ω, isOpen_H_diff_retSet s Wα ζα ω⟩
  have hret := fun (g₁ : Ω → DistOn upperHalfPlaneOpens)
      (hg₁ : IsLocalSetMean (retSet s Wα ζα) (centredField h' u₀) P g₁) =>
    ae_eqOn_retMean (θ := θ) hκ hGc hb' hG' hT hflc hdetα hu₀ hh0 s hg₁
  -- the counterflow driver
  have hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hCc.1.2.2.2.2, hcomp] with ω hp hc
    have hcont : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hp.2.2.2.1
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} = univ := by
      ext t
      simp only [hc.1, mem_ofPred_eq, ENNReal.coe_lt_top, mem_univ]
    rw [e] at hcont
    exact ⟨continuousOn_univ.1 hcont, hp.1, hc.2.1⟩
  have hWpath : ∀ᵐ ω ∂P, (fun r : ℝ => W' r.toNNReal ω) = fun r : ℝ => W r.toNNReal ω := by
    filter_upwards [hWW] with ω hω
    exact funext fun r => hω _
  have hRc := hver.1.2.1
  have hR0 := hver.1.2.2.1
  by_cases ht0 : t = 0
  · -- the counterflow time `0`: the retained mean
    subst ht0
    have hBeq0 : ∀ᵐ ω ∂P, B 0 ω = retSet s Wα ζα ω := by
      filter_upwards [hBeq 0, hWpath, hW] with ω hB hWp hWω
      have hWc : Continuous fun r : ℝ => W r.toNNReal ω := hWω.1.comp continuous_real_toNNReal
      rw [hB, hWp, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc, union_empty]
      exact relClosureH_eq_self (retSet_subset_H s Wα ζα ω) (isOpen_H_diff_retSet s Wα ζα ω)
    have hrep0 := ae_rep_retMean (θ := θ) hh0 c s ℋ₁.2 hAm hloc₁ hAℋ hret (hBm 0) (Eventually.of_forall (hBc 0))
      hBeq0 hg
    filter_upwards [hrep0, hGTae, hBeq0, ae_compl_union_eq_relChart hGT hver 0] with ω hrepω hGTω hB0 hshape hlive
      hlt hψ
    have hrecTS : gb6Rec s Wα ζα ω ∈ gb6TS s := hlive.1
    have hωGT : ω ∈ GT := hGTω.2 hrecTS
    obtain ⟨⟨hWc', -, -⟩, ⟨h0, hcα, -⟩, hs, -, hgood, -⟩ := hGT ω hωGT
    obtain ⟨-, -, hr⟩ := hgood
    obtain ⟨w₁, hw₁, hrep₁, hv₁⟩ := hrepω hs
    obtain ⟨G₀, hG₀⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
      (flowLineRhoL (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
      (flowLineRhoR (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn
        (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0 0)
      (flowLineXL (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0)
      (flowLineXR (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps 0)
    have hG₀' : IsBoundedHarmonicExtension
        (cfData (16 / κ) (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps)
        (cfJumps (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).fn (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).jumps) G₀ := by
      rw [coe_cfJumps]
      exact hG₀
    have hQ : (min (physClock s W' Wα ζα GT 0 ω) (V ω)).toNNReal = 0 := by
      rw [min_physClock_zero hGT ω, ENNReal.toNNReal_zero]
    have hsh := hshape hωGT hlt
    rw [hQ] at hψ hsh ⊢
    have hRpc : Continuous fun r : ℝ => R r.toNNReal ω := (hRc ω).comp continuous_real_toNNReal
    have hRp0 : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hR0 ω]
    have hO : H \ B 0 ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) ((0 : ℝ≥0) : ℝ)) := by
      have hWc'' : Continuous fun r : ℝ => W' r.toNNReal ω := hWc'.comp continuous_real_toNNReal
      rw [← hsh, NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc'', union_empty, hB0, retSet_of_lt hs]
    have hGG := eqOn_bheProc_of_cfFlowed (Hc := Hc) (V := V) (rec := gb6Rec s Wα ζα) hlive.2 (hRc ω) (hR0 ω) 0
      (G := G₀) (by simpa only [NNReal.coe_zero] using bhe_cfFlowed_zero hRpc hRp0 hG₀')
    have hL0 : ∀ y, logDerivFwd (fun r : ℝ => R r.toNNReal ω) 0 y = 0 := fun y => by
      simp [QuantumZipper.logDerivFwd]
    refine chartTransport_eq_couplingMean κ hr (fun x hx => rdrv_recOf_cfE s h0 hcα hs hx.2) hO hw₁ hu₀.1 hrep₁
      (Wr := fun r : ℝ => R r.toNNReal ω) (G := G₀) ?_ (fun _ _ => rfl) hRpc hGG hψ
    intro z hz
    rw [hv₁ G₀ hG₀' hz]
    simp only [NNReal.coe_zero, fwdMap_zero_time (W := fun r : ℝ => R r.toNNReal ω) hRp0, hL0, Complex.zero_im,
      zero_add]
  · -- a positive counterflow time: the union mean
    have ht0' : 0 < t := pos_iff_ne_zero.2 ht0
    have hKℳ : Measurable[drivingFiltration P hXc t, hittingSigma]
        (fun ω => Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VLc VRc ζ ω)) :=
      ((Sec5.CrossCond.measurable_hullAt_stopSigma t).comp (comap_measurable _)).mono
        (WangWu.comap_stopSigma_le hXc t) le_rfl
    have hlocU : IsHistoryAvoidanceLocal (ℋ₁.1 ⊔ drivingFiltration P hXc t)
        (fun ω => retSet s Wα ζα ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VLc VRc ζ ω))
        (centredField h' u₀) P :=
      Theorem14.WalkLaw.isHistoryAvoidanceLocal_union_of_det hh₀m (A₁ := retSet s Wα ζα)
        (A₂ := fun ω => Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VLc VRc ζ ω))
        (fun U hUH => hrecℋ₁ (measurable_retOfRec s (measurableSet_avoid U.isOpen hUH)))
        (fun U hUH => measurableSet_avoid_cfHull hXc t U.isOpen hUH) hℋ₁d (h𝓕c t) hloc₁
        (isHistoryAvoidanceLocal_cfHull hCc hk hζ hu₀ t)
    have hUℳ : Measurable[ℋ₁.1 ⊔ drivingFiltration P hXc t, hittingSigma]
        (fun ω => retSet s Wα ζα ω ∪ Sec5.GlueCond.hullAt t (LawUnique.killedHistory W VLc VRc ζ ω)) :=
      @measurable_union_hitting Ω (ℋ₁.1 ⊔ drivingFiltration P hXc t) _ _ (hAℋ.mono le_sup_left le_rfl)
        (hKℳ.mono le_sup_right le_rfl)
    have hdA : MeasurableSpace.comap (retSet s Wα ζα) hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h' u₀) inferInstance) P := hAℋ.comap_le.trans hℋ₁d
    have hlA : IsLocalSet (retSet s Wα ζα) (centredField h' u₀) P :=
      ((isLocalSet_tfae hh0 hAm hAc).out 4 1).2 hloc₁.isAvoidanceLocal
    have hunion : ∀ {ω : Ω} {V' : ℝ → ℝ}, Continuous V' →
        retSet s Wα ζα ω ∪ fwdHull V' t ⊆ H ∧ IsOpen (H \ (retSet s Wα ζα ω ∪ fwdHull V' t)) := fun {ω V'} hV' => by
      refine ⟨union_subset (retSet_subset_H s Wα ζα ω) (QuantumZipper.fwdHull_mono.2 _), ?_⟩
      have e : H \ (retSet s Wα ζα ω ∪ fwdHull V' t) = (H \ retSet s Wα ζα ω) ∩ (H \ fwdHull V' t) := by
        ext z
        simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]
        tauto
      rw [e]
      exact (isOpen_H_diff_retSet s Wα ζα ω).inter (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hV' t.coe_nonneg)
    have hBeqW : ∀ᵐ ω ∂P, B t ω = retSet s Wα ζα ω ∪ fwdHull (fun r : ℝ => W r.toNNReal ω) t := by
      filter_upwards [hBeq t, hWpath, hW] with ω hB hWp hWω
      rw [hB, hWp]
      have hWc : Continuous fun r : ℝ => W r.toNNReal ω := hWω.1.comp continuous_real_toNNReal
      exact relClosureH_eq_self (hunion hWc).1 (hunion hWc).2
    have hrepU := ae_rep_unionMean (θ := θ) hκ hκ4 hfl hα hCc hζ hW hu₀ hh0 c s t ht0'
      (sup_le ℋ₁.2 ((drivingFiltration P hXc).le t)) hlocU hUℳ hdA hlA hret (hBm t) (Eventually.of_forall (hBc t))
      hBeqW hg
    filter_upwards [hrepU, hGTae, hWpath, hver.1.2.2.2.2.2.2, ae_compl_union_eq_relChart hGT hver t, hBeq t]
      with ω hrepω hGTω hWp hverω hshape hBt hlive hlt hψ
    have hrecTS : gb6Rec s Wα ζα ω ∈ gb6TS s := hlive.1
    have hωGT : ω ∈ GT := hGTω.2 hrecTS
    obtain ⟨⟨hWc', hW0', hγ'⟩, ⟨h0, hcα, hαω⟩, hs, hsH, hgood, -⟩ := hGT ω hωGT
    obtain ⟨-, hreachV, hhull⟩ := hverω hs hsH
    obtain ⟨-, -, hr⟩ := hgood
    -- `t` is before the first contact
    have htc : (t : ℝ≥0∞) < gb6Tc s γ α ω := by
      by_contra hcon
      have hle : gb6Tc s γ α ω ≤ t := le_of_not_gt hcon
      have hV : V ω ≤ physClock s W' Wα ζα GT t ω := by
        rw [physClock_eq_iSup hGT hωGT]
        refine ENNReal.le_of_forall_nnreal_lt fun u hu => ?_
        obtain ⟨t', ht', hut'⟩ := hreachV u hu
        have ht't : t' < t := by
          have := lt_of_lt_of_le ht' hle
          exact_mod_cast this
        refine le_trans ?_ (le_iSup₂ (f := fun (t' : ℝ≥0) (_ : t' < t ∧ (t' : ℝ≥0∞) < gb6Tc s γ α ω) =>
          ENNReal.ofReal (gb6Clock s W' Wα ω t')) t' ⟨ht't, ht'⟩)
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hut'.le
      rw [min_eq_right hV] at hlt
      exact lt_irrefl _ hlt
    -- the clock at `t`
    have hphys := physClock_eq_gb6Clock hGT hωGT htc
    obtain ⟨ha0, hsm, hac⟩ := relClock_props_of_traces hαω hcα h0 hs hsH hγ' hWc' hW0'
    have hnn : 0 ≤ gb6Clock s W' Wα ω t := by
      have h0T : ((0 : ℝ≥0) : ℝ≥0∞) < gb6Tc s γ α ω := lt_of_le_of_lt bot_le htc
      have := hsm.monotoneOn h0T htc (bot_le : (0 : ℝ≥0) ≤ t)
      have e0 : relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W' r.toNNReal ω) ((0 : ℝ≥0) : ℝ) = 0 := by
        rw [NNReal.coe_zero]; exact ha0
      rw [e0] at this
      exact this
    have hlt' : ENNReal.ofReal (gb6Clock s W' Wα ω t) < V ω := by
      rw [hphys] at hlt
      exact lt_of_not_ge fun h => lt_irrefl _ (by rwa [min_eq_right h] at hlt)
    have hmin : min (physClock s W' Wα ζα GT t ω) (V ω) = ENNReal.ofReal (gb6Clock s W' Wα ω t) := by
      rw [hphys]
      exact min_eq_left hlt'.le
    have hreal : (((min (physClock s W' Wα ζα GT t ω) (V ω)).toNNReal : ℝ≥0) : ℝ) = gb6Clock s W' Wα ω t := by
      rw [hmin, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hnn]
    -- the union representation, read with the version's path
    obtain ⟨Wr, G, wU, hWr, hWr0, hHU, hGb, hwU, hrep, hv⟩ := hrepω hs hsH htc
    rw [← hWp] at hHU hGb hv
    -- `Wr = R` up to `a(t)`
    have hRpc : Continuous fun r : ℝ => R r.toNNReal ω := (hRc ω).comp continuous_real_toNNReal
    have hRp0 : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simp only [Real.toNNReal_zero, hR0 ω]
    have hHR : ∀ t' : ℝ≥0, t' ≤ t →
        relMap (fun r : ℝ => Wα r.toNNReal ω) s '' fwdHull (fun r : ℝ => W' r.toNNReal ω) t' =
        fwdHull (fun r : ℝ => R r.toNNReal ω)
          (relClock (fun r : ℝ => Wα r.toNNReal ω) s (fun r : ℝ => W' r.toNNReal ω) t') := fun t' ht' => by
      have ht'c : (t' : ℝ≥0∞) < gb6Tc s γ α ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht') htc
      have hle : ENNReal.ofReal (gb6Clock s W' Wα ω t') ≤ V ω :=
        le_trans (ENNReal.ofReal_le_ofReal (hsm.monotoneOn ht'c htc ht')) hlt'.le
      exact (hhull t' ht'c hle).symm
    have hWR := eqOn_of_hullsUpTo hWr hWr0 hRpc hRp0 ha0
      (hac.mono fun t' ht' => lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht'.2) htc) hHU hHR
    -- the typed word
    have hGR := bhe_cfFlowed_congr hWr hWr0 hRpc hRp0 hnn hWR hGb
    have hGG := eqOn_bheProc_of_cfFlowed (Hc := Hc) (V := V) (rec := gb6Rec s Wα ζα) hlive.2 (hRc ω) (hR0 ω)
      (min (physClock s W' Wα ζα GT t ω) (V ω)).toNNReal (G := G) (by rw [hreal]; exact hGR)
    -- the shape of the union
    have hO : H \ B t ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W' Wα ζα GT t ω) (V ω)).toNNReal) := by
      have hWc'' : Continuous fun r : ℝ => W' r.toNNReal ω := hWc'.comp continuous_real_toNNReal
      rw [← hshape hωGT hlt, hBt, relClosureH_eq_self (hunion hWc'').1 (hunion hWc'').2, retSet_of_lt hs]
    refine chartTransport_eq_couplingMean κ hr (fun x hx => rdrv_recOf_cfE s h0 hcα hs hx.2) hO hwU hu₀.1 hrep
      (Wr := Wr) (G := G) ?_ (by rw [hreal]; exact hWR) hRpc hGG hψ
    rw [hreal]
    exact hv

/-- **`RelSafeS.GB6LineLocalStatement` from Theorems 1.2–1.3.** -/
theorem gb6LineLocalStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : GB6LineLocalStatement.{u} :=
  gb6LineLocalStatement_of_mean h12 h13 (gb6LineMeanStatement_of_thm12_thm13 h12 h13)

/-- **Theorem 1.4's `GB6HullDetStatement` from Theorems 1.2–1.3.** -/
theorem gb6HullDetStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : Supp8.GB6.GB6HullDetStatement.{u} :=
  gb6HullDetStatement_of_mean h12 h13 (gb6LineMeanStatement_of_thm12_thm13 h12 h13)

end Main

end InteractingSLE.Supp8.GB6LMean
