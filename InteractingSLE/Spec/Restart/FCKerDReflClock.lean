/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerDReflWord

/-!
# Clocks, characteristic functionals and filtrations under the reflection

Packet PROVE-T15-FCKER4. The remaining objects of the corrected first-contact kernels under `σ(z) = −z̄`:

* the chart paths: forward chart limits pass to the reflected chart (`tendsto_fwd_reflPair`), so the first chart
  path of the reflected pair is the reflected second chart path (`cPath_reflPair`), with the same capacity clock
  (`chartClock_reflect`); the canonical clock of the reflected configuration (`reflGamma`, `reflLife`,
  **`isCanonClock_refl`**);
* the bounded harmonic extension of the reflected force word (`bheAt_reflect`, `bheProc_reflect`) and the
  characteristic functional of the reflected continuation (**`cfAt_reflect`**: at the test `−ψ ∘ σ` it is the
  original one);
* the retained driver filtration of the driver `−W` (**`fcRetainedDriverFiltration_reflPair`**) and the flowed chart
  field (`flowField_chartField_reflPair`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal ComplexConjugate
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb.FCKerD

open LP (reflectC)

section Clock

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω} (hd : d.IsMeasGood)
include hd

/-- Forward chart limits pass to the reflected chart. -/
theorem tendsto_fwd_reflPair {ω : Ω} (hω : ω ∈ d.E) {x w : ℂ}
    (ht : Tendsto (d.fwd ω) (𝓝[d.D ω] x) (𝓝 w)) :
    Tendsto ((reflPair d).fwd ω) (𝓝[(reflPair d).D ω] (reflectC x)) (𝓝 (reflectC w)) := by
  have hD : (reflPair d).D ω = reflectC '' d.D ω := reflPair_D hd ω
  have hσ : Tendsto reflectC (𝓝[(reflPair d).D ω] (reflectC x)) (𝓝[d.D ω] x) := by
    have h := (LP.continuous_reflectC.continuousWithinAt (s := (reflPair d).D ω)
      (x := reflectC x)).tendsto_nhdsWithin (t := d.D ω) (fun z hz => by
        rw [hD] at hz
        obtain ⟨v, hv, rfl⟩ := hz
        rwa [LP.reflectC_reflectC])
    rwa [LP.reflectC_reflectC] at h
  refine ((LP.continuous_reflectC.tendsto _).comp (ht.comp hσ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (reflPair_fwd hd hω hz).symm

/-- **The chart path of the reflected first continuation is the reflected chart path of the second
continuation.** -/
theorem cPath_reflPair {E₁ : Set Ω} (hs : IsContSpec d E₁ d.t₀ d.η₂ d.ζ₂) {ω : Ω} (hω : ω ∈ E₁) (r : ℝ≥0) :
    cPath (reflPair d) univ d.t₀ (reflPair d).η₁ (reflPair d).ζ₁ ω r =
      reflectC (cPath d univ d.t₀ d.η₂ d.ζ₂ ω r) := by
  have hωE := hs.subset hω
  obtain ⟨-, ht, -, -⟩ := hs.cPath_spec hω r
  have he : cPath d univ d.t₀ d.η₂ d.ζ₂ ω r = cPath d E₁ d.t₀ d.η₂ d.ζ₂ ω r := by
    rw [cPath_of_mem (mem_univ ω), cPath_of_mem hω]
  rw [he, cPath_of_mem (mem_univ ω)]
  have hx := hs.mem ω hω _ (le_contTime _ _ r) (contTime_le (hs.lt ω hω).le r)
  have hne : (𝓝[(reflPair d).D ω] (reflectC (d.η₂ ω (contTime (d.t₀ ω) (d.ζ₂ ω) r)))).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    rw [reflPair_D hd, LP.closure_image_reflectC]
    exact mem_image_of_mem _ hx
  exact (tendsto_fwd_reflPair hd hωE ht).limUnder_eq

end Clock

section Canon

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped Classical in
/-- The chart path of the reflected first continuation: the reflected second chart path on the meeting branch, a
given path elsewhere. -/
def reflGamma (d : PairData Ω) (γ₂ γ' : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ≥0 → ℂ :=
  if ω ∈ meetSet d then fun u => reflectC (γ₂ ω u) else γ' ω

open scoped Classical in
/-- Its lifetime: the second lifetime on the meeting branch, a given one elsewhere. -/
def reflLife (d : PairData Ω) (U₂ U' : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  if ω ∈ meetSet d then U₂ ω else U' ω

omit [MeasurableSpace Ω] in
theorem reflGamma_of_mem {d : PairData Ω} {γ₂ γ' : Ω → ℝ≥0 → ℂ} {ω : Ω} (hω : ω ∈ meetSet d) :
    reflGamma d γ₂ γ' ω = fun u => reflectC (γ₂ ω u) := by
  simp [reflGamma, hω]

omit [MeasurableSpace Ω] in
theorem reflLife_of_mem {d : PairData Ω} {U₂ U' : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ meetSet d) :
    reflLife d U₂ U' ω = U₂ ω := by
  simp [reflLife, hω]

variable {d : PairData Ω} (hd : d.IsMeasGood)
include hd

/-- **The canonical clock of the reflected configuration**: on the meeting branch the reflected first chart path is
the reflection of the second one, with the same capacity clock. -/
theorem isCanonClock_refl {P : Measure Ω} {γ₁ γ₂ : Ω → ℝ≥0 → ℂ} {U₁ U₂ : Ω → ℝ≥0∞}
    (hcanon : d.IsCanonClock P γ₁ γ₂ U₁ U₂) {E₁ : Set Ω} (hs : IsContSpec d E₁ d.t₀ d.η₂ d.ζ₂)
    (hME : ∀ᵐ ω ∂P, ω ∈ meetSet d → ω ∈ E₁) {γ' γ'' : Ω → ℝ≥0 → ℂ} {U' U'' : Ω → ℝ≥0∞}
    (hc' : (reflPair d).IsCanonClock P γ' γ'' U' U'') :
    (reflPair d).IsCanonClock P (reflGamma d γ₂ γ') γ'' (reflLife d U₂ U') U'' := by
  have hs₀ : (reflPair d).s₀ = d.t₀ := funext (reflPair_s₀ hd)
  filter_upwards [hcanon, hc', hME] with ω hc hcω hme hωE'
  refine ⟨fun hlt => ?_, (hcω hωE').2⟩
  by_cases hM : ω ∈ meetSet d
  · have hωE : ω ∈ d.E := by rwa [E_reflPair] at hωE'
    rw [hs₀] at hlt ⊢
    obtain ⟨h1, h2⟩ := (hc hωE).2 hlt
    have hcp : cPath (reflPair d) univ d.t₀ (reflPair d).η₁ (reflPair d).ζ₁ ω =
        fun r => reflectC (cPath d univ d.t₀ d.η₂ d.ζ₂ ω r) := funext (cPath_reflPair hd hs (hme hM))
    have hcl : chartClock (cPath (reflPair d) univ d.t₀ (reflPair d).η₁ (reflPair d).ζ₁ ω) =
        chartClock (cPath d univ d.t₀ d.η₂ d.ζ₂ ω) := by
      rw [hcp]
      funext r
      exact chartClock_reflect _ r
    rw [reflGamma_of_mem hM, reflLife_of_mem hM, hcl, hcp]
    exact ⟨fun u hu => by simp only; rw [h1 u hu]; rfl, h2⟩
  · simp only [reflGamma, reflLife, hM, ↓reduceIte]
    exact (hcω hωE').1 hlt

end Canon

section CF

open Sec7.FlowReflect (reflTest reflField)
open Sec7.PocketTraversal (geomLW geomRW)

variable {nL nR : ℕ}

/-- **The bounded harmonic extension of the reflected force word** is the reflected extension, on `ℍ`. -/
theorem bheAt_reflect (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    {z : ℂ} (hz : z ∈ H) :
    LocalExt.bheAt κ ρR ρL (fun i => -vR i) (fun j => -vL j) z =
      -LocalExt.bheAt κ ρL ρR vL vR (reflectC z) := by
  have hu := Sec7.FlowReflect.IsBoundedHarmonicExtension.reflect_force
    (LocalExt.isBoundedHarmonicExtension_bheAt κ ρR ρL (fun i => -vR i) (fun j => -vL j))
  have hv := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR vL vR
  have hfin : (forceJumpSet vL vR).Finite :=
    ((Set.finite_range vL).union (Set.finite_range vR)).insert 0
  have he := Impl.eqOn_of_isBoundedHarmonicExtension hfin hv hu (LP.reflectC_mem_H_iff.2 hz)
  simp only [LP.reflectC_reflectC] at he
  rw [← he, neg_neg]

variable {Ω : Type*}

/-- **The bounded harmonic extension process of the reflected geometric word** is the reflected one, on `ℍ`. -/
theorem bheProc_reflect (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ)
    (xR : Ω → Fin nR → ℝ) (ω : Ω) (s : ℝ≥0) {z : ℂ} (hz : z ∈ H) :
    DomainMarkov.bheProc κ ρR ρL (fun t ω => -W t ω) (geomLW (fun t ω => -W t ω) fun ω i => -xR ω i)
      (geomRW (fun t ω => -W t ω) fun ω j => -xL ω j) ω s z =
      -DomainMarkov.bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s (reflectC z) := by
  have eL : ∀ i, geomLW (fun t ω => -W t ω) (fun ω i => -xR ω i) i s ω - -W s ω = -(geomRW W xR i s ω - W s ω) :=
    fun i => by rw [show (fun t ω => -W t ω) = -W from rfl, Sec5.CfDown.geomLW_neg]; ring
  have eR : ∀ j, geomRW (fun t ω => -W t ω) (fun ω j => -xL ω j) j s ω - -W s ω = -(geomLW W xL j s ω - W s ω) :=
    fun j => by rw [show (fun t ω => -W t ω) = -W from rfl, Sec5.CfDown.geomRW_neg]; ring
  simp only [DomainMarkov.bheProc, eL, eR]
  exact bheAt_reflect κ ρL ρR _ _ hz

/-- **The characteristic functional of the reflected continuation** at the reflected negated test is the original
one, at a capacity time at which the test function avoids the hull. -/
theorem cfAt_reflect {κ : ℝ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) {u u' : Ω → ℝ≥0 → ℂ → ℝ}
    {q : ℝ≥0} {ω : Ω} (hu : ∀ z ∈ H, u' ω q z = -u ω q (reflectC z)) {ψ ψ' : ℂ → ℝ}
    (hψ : ∀ z, ψ' z = -ψ (reflectC z)) (hsupp : tsupport ψ ⊆ H)
    (hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) q)) :
    Coupling.cfAt κ (fun t ω => -W t ω) u' ψ' 1 (fun _ => q) ω =
      Coupling.cfAt κ W u ψ 1 (fun _ => q) ω := by
  set w : ℝ → ℝ := fun s => W s.toNNReal ω with hw
  have hwc : ContinuousOn w (Icc 0 (q : ℝ)) := ((hWc ω).comp continuous_real_toNNReal).continuousOn
  have e : (fun s : ℝ => -W s.toNNReal ω) = -w := rfl
  have hq : (0 : ℝ) ≤ q := q.2
  have hM : ∫ z, couplingMean κ (fun s : ℝ => -W s.toNNReal ω) q (u' ω q) z * ψ' z =
      ∫ z, couplingMean κ w q (u ω q) z * ψ z := by
    rw [e, ← Sec7.FlowReflect.integral_comp_reflectC]
    congr 1
    funext z
    rw [Sec7.FlowReflect.couplingMean_reflect κ w hq, hψ, LP.reflectC_reflectC]
    by_cases hz : z ∈ tsupport ψ
    · have hzH : z ∈ H := hsupp hz
      have hzK : z ∉ fwdHull w q := Set.disjoint_left.1 hdis hz
      have hf := WFS.fwdMap_mem_H_of_notMem hq hwc hzH hzK
      have hu' := hu _ (LP.reflectC_mem_H_iff.2 hf)
      rw [LP.reflectC_reflectC] at hu'
      simp only [couplingMean, hu', neg_neg]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hz, neg_zero, mul_zero, mul_zero]
  have hE : loewnerGreenEnergy (fun s : ℝ => -W s.toNNReal ω) q ψ' = loewnerGreenEnergy w q ψ := by
    rw [e, Sec7.FlowReflect.loewnerGreenEnergy_reflect w hq]
    have e2 : (fun z => ψ' (reflectC z)) = fun z => -ψ z := by
      funext z
      rw [hψ, LP.reflectC_reflectC]
    rw [e2, Sec7.FlowReflect.loewnerGreenEnergy_neg]
  simp only [Coupling.cfAt]
  rw [hM, hE]

end CF

section Out

open Sec7.FlowReflect (reflTest reflField)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : PairData Ω} (hd : d.IsMeasGood)
include hd

/-- **The retained driver filtration of the reflected configuration** (driver `−W`) is the original one. -/
theorem fcRetainedDriverFiltration_reflPair (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (W t))
    (hm' : ∀ t, Measurable fun ω => -W t ω) :
    fcRetainedDriverFiltration P (isMeasGood_reflPair hd) (fun t ω => -W t ω) hm' =
      fcRetainedDriverFiltration P hd W hm := by
  refine MeasureTheory.Filtration.ext (funext fun q => ?_)
  change mΩ ⊓ LocalSets.aeSigma (fcDriverFiltration (retHist (reflPair d)) (fun t ω => -W t ω) _ hm' q) P =
    mΩ ⊓ LocalSets.aeSigma (fcDriverFiltration (retHist d) W _ hm q) P
  congr 2
  change MeasurableSpace.comap (retHist (reflPair d)) inferInstance ⊔
      ⨆ r : ℝ≥0, ⨆ (_ : r ≤ q), MeasurableSpace.comap (fun ω => -W r ω) inferInstance =
    MeasurableSpace.comap (retHist d) inferInstance ⊔
      ⨆ r : ℝ≥0, ⨆ (_ : r ≤ q), MeasurableSpace.comap (W r) inferInstance
  have e1 : retHist (reflPair d) = fun ω => swapRefl (retHist d ω) := funext (reflPair_retHist hd)
  have e2 : ∀ r, MeasurableSpace.comap (fun ω => -W r ω) (inferInstance : MeasurableSpace ℝ) =
      MeasurableSpace.comap (W r) inferInstance := fun r => by
    change MeasurableSpace.comap (Neg.neg ∘ W r) _ = _
    rw [← MeasurableSpace.comap_comp, Sec7.FlowReflect.comap_eq_of_involutive' measurable_neg neg_involutive]
  rw [e1, comap_swapRefl]
  simp only [e2]

/-- **The flowed chart field of the reflected configuration** is the reflected flowed chart field. -/
theorem flowField_chartField_reflPair (κ a : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    Exist.flowField 0 (-a) ((isMeasGood_reflPair hd).chartField κ (fun ω => reflField (h ω)) ω) =
      reflField (Exist.flowField 0 a (hd.chartField κ h ω)) := by
  change Exist.flowField 0 (-a) (Chart.chartTransport _ 1 0 (chiC κ) (reflField (h ω))) =
    reflField (Exist.flowField 0 a (Chart.chartTransport _ 1 0 (chiC κ) (h ω)))
  rw [RetFin.flowField_chartTransport, RetFin.flowField_chartTransport]
  exact chartTransport_reflPair hd ω a (chiC κ) (h ω)

end Out

end InteractingSLE.Restart.FCPlumb.FCKerD
