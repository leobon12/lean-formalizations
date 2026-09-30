import QuantumZipper.Proofs.Thm14.GoodDriverSet
import QuantumZipper.Proofs.Loewner.ArcDeterminesDriver

/-!
# Theorem 1.4(b): the driver side

Sheffield, *Conformal weldings of random surfaces*, §1.4 (blueprint node C1).

Combining the Borel good set (`Thm14GoodDriverSet.exists_goodDriverSet`), the injectivity of the
welding data on good paths (welding uniqueness A3 and `ArcDriver.eqOn_of_revMap_eq`) and
Lusin–Souslin (`Thm14WeldingData.exists_weldingGraph_of_goodSet`):

* `injOn_weldingDataC_of_good`: the Borel welding data is injective on good paths;
* `exists_driverGraph`: a Borel partial graph in (welding data) × (driver at rational times)
  contains `(weldingData W T, W|ℚ)` almost surely, for `W = √κ B`;
* `exists_measurable_driver_of_weldingData`: the driver on `[0,T]` is almost surely a measurable
  function of the welding data.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14DriverSide

open Thm14Determination Thm14WeldingData Thm14GoodDriverSet

/-- **Injectivity of the welding data on good paths.** -/
theorem injOn_weldingDataC_of_good (hCar : Blueprint.RevMapCaratheodory) {T : ℝ} (hT : 0 < T)
    {G : Set C(Icc (0 : ℝ) T, ℝ)} (hgood : ∀ g ∈ G, GoodDriver T (extIccPath hT.le g)) :
    InjOn (weldingDataC hT.le) G := by
  refine injOn_weldingDataC hT.le hCar hT
    (fun f hf => ⟨(hgood f hf).1, (hgood f hf).2.1, (hgood f hf).2.2.1⟩) ?_
  intro f hf f' hf' h
  have hEq := ArcDriver.eqOn_of_revMap_eq hCar (continuous_extIccPath hT.le f)
    (continuous_extIccPath hT.le f') (hgood f hf).1 (hgood f' hf').1 hT (hgood f hf).2.2.2
    (hgood f' hf').2.2.2 h
  ext ⟨t, ht⟩
  have := hEq ht
  rwa [extIccPath_of_mem hT.le f ht, extIccPath_of_mem hT.le f' ht] at this

/-- **The welding data determines the driver (Borel partial graph).** -/
theorem exists_driverGraph (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) (hRSH : Blueprint.RohdeSchrammHolder)
    (hJS : Blueprint.JonesSmirnovRemovable) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ G' : Set ((ℝ × (ℚ → ℝ)) × (ℚ → ℝ)), MeasurableSet G' ∧ IsPartialGraph G' ∧
      ∀ᵐ ω ∂P, (weldingData (drive κ B ω) T, sampleDrive T (drive κ B ω)) ∈ G' := by
  obtain ⟨G, hGm, hgood, hae⟩ := exists_goodDriverSet hRSS hRSH hJS hκ0 hκ4 hT P B hB
  exact exists_weldingGraph_of_goodSet hCar hT hGm
    (fun f hf => ⟨(hgood f hf).1, (hgood f hf).2.1⟩) (injOn_weldingDataC_of_good hCar hT hgood)
    P (drive κ B) hae

/-- **The driver is a measurable function of the welding data**, almost surely. -/
theorem exists_measurable_driver_of_weldingData (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) (hRSH : Blueprint.RohdeSchrammHolder)
    (hJS : Blueprint.JonesSmirnovRemovable) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ F : ℝ × (ℚ → ℝ) → (ℝ → ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, F (weldingData (drive κ B ω) T) t = drive κ B ω t := by
  obtain ⟨G', hG'm, hG'g, hmem⟩ := exists_driverGraph hCar hRSS hRSH hJS hκ0 hκ4 hT P B hB
  obtain ⟨F₀, hF₀, hF₀ae⟩ := exists_measurable_ae_eq_of_partialGraph P hG'm hG'g
    (fun ω => weldingData (drive κ B ω) T) (fun ω => sampleDrive T (drive κ B ω)) hmem
  refine ⟨fun d => recoverDrive (F₀ d), measurable_recoverDrive.comp hF₀, ?_⟩
  filter_upwards [hF₀ae, hB.cont] with ω hω hc t ht
  change recoverDrive (F₀ (weldingData (drive κ B ω) T)) t = _
  rw [hω]
  exact recoverDrive_sampleDrive (Thm14FromThm13.continuous_drive hc) ht

end Thm14DriverSide

end QuantumZipper
