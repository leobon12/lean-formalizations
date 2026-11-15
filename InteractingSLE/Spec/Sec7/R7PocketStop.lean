/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7PocketWire
import InteractingSLE.Spec.Sec7.Lemma725RefWireStop

/-!
# Theorem R.7's two-seed pocket: the field-level statement from pocket-stop data

Packet PROVE-R7POCKET. Theorem R.7's proof (`source/spec/p433-480.md` L1058–L1068, pp. 477–478): "The traversal
argument above gives a complete continuous relative trace, and Lemma R.5 and its corollary give every stopped Gaussian
kernel. Lemma R.6 selects the zero phase for arbitrarily large weights … Aux. 124–125 give its full field–path joint
kernel and determining graph."

PROVE-LEMMA725REF4/REF5 reduced Lemma 7.25's `PocketChartFieldStatement` to the data of ONE pocket at its relative
capacity stops (`Lemma725RefChart.pocketChartFieldStatement_of_stop`,
`Lemma725RefRecovery.pocketChartFieldStatement_of_stop_exteriorDecomp`): the canonical pocket chart
`shiftChart (pChart A C ψ) n`, the marked union laws (`PocketStopUnionLaw`), the side limits with the canonical heights
(`PocketStopSideLimit`), and the determination. The same assembly for the constant two-seed word `SLE_κ(r_L; r_R)` (no
distant marks; marks `LP.twoSeedXL`, `LP.twoSeedXR`) with the pathwise property `Good` gives the named input of `hR7`:

* **`pocketChartTwoSeedStatement_of_stop`**: `PocketChartTwoSeedStatement κ r_L r_R Good` from one two-seed pocket's
  stop data, the determination `hdet`, and `Good`;
* **`pocketChartTwoSeedStatement_of_stop_exteriorDecomp`**: the same with `hdet` replaced by Aux. lemma 124's exterior
  decomposition, a standard Borel record, Proposition 5.13 and the measurable pocket erasure (REF5's route);
* `R7PocketStopStatement κ r_L r_R` (**named input**: Theorem R.7's mixed/outer two-seed pocket with these data) and
  **`r7ReferenceStatement_of_r7PocketStop`**: `hR7` from it on the whole range of Theorem R.7 (with
  `Lemma725RefSafe.r7ReferenceStatement_of_pocketChartTwoSeed_all`: no upper seed-weight bound; the zero phase for large
  weights is Lemma R.6's, inside the side limits `hside`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or a result taking them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7Pocket

open PocketTraversal Lemma71C LawUnique PocketStop PocketStopField Lemma725RefChart Lemma725RefSafe PocketCoupling
  Lemma725RefRecovery WholeField LocalSets

universe u

section Stop

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketChartTwoSeedStatement κ r_L r_R Good` from one two-seed pocket at its relative capacity stops**
(`Lemma725RefChart.pocketChartFieldStatement_of_stop` for the constant two-seed word): a walls-event `A` of positive
probability, the erased traversal `γ` (driven, measurable at fixed times, unbounded in `ℍ`), the open pocket `C ⊆ ℍ`
with a conformal bijection `ψ : C → ℍ` measurable for the walls, the hull sets `F q` (`ψ(C ∖ F q) = ℍ ∖ K_q`), the
zero-boundary GFF `h₀` and the bounded harmonic `u` (the field is `h₀ + u`), the branch `n`, the marked union laws
(`PocketStopUnionLaw`), the side limits with the two-seed word's canonical heights (`PocketStopSideLimit`), the
pathwise property `Good`, and the determination of the killed relative history by a walls record and the pocket
field. -/
theorem pocketChartTwoSeedStatement_of_stop [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    (hGood : ∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    {ε : Type u} [MeasurableSpace ε] {E : Ω → ε}
    {g : ε × DistOn upperHalfPlaneOpens → HistorySpace 1 1} (hEm : Measurable[𝓦] E) (hg : Measurable g)
    (hdet : ∀ᵐ ω ∂P, ω ∈ A → ∀ hc : (shiftChart (pChart A C ψ ω) (n ω)).IsConformal,
      killedHistory (fun t ω => segDriver (γ ω) t) (geomLW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXL)
        (geomRW (fun t ω => segDriver (γ ω) t) fun _ => LP.twoSeedXR) (fun ω => capLife (γ ω)) ω =
          g (E ω, Chart.chartTransport hc 1 a (chiC κ) (h₀ ω + smoothDist upperHalfPlaneOpens u))) :
    PocketChartTwoSeedStatement.{u} κ rL rR Good := by
  obtain ⟨hcc, hdom, hfwd, hliftm, hliftc, hlift, hKm, hKloc, 𝓜, M, hker, hmean⟩ :=
    pocketChartData_of_stop (ρL := fun _ : Fin 1 => rL) (ρR := fun _ : Fin 1 => rR) (xL := fun _ => LP.twoSeedXL)
      (xR := fun _ => LP.twoSeedXR) h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hFo hgeo hh₀ hu hub hn hU hside
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens
      (centredField (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) u) P := by
    rw [centredField_add_smoothDist]
    exact hh₀
  have hKloc' : ∀ s, IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ s)
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) s)
      (centredField (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) u) P := by
    rw [centredField_add_smoothDist]
    exact hKloc
  exact ⟨Ω, 𝓦, mΩ, inferInstance, P, inferInstance, A, γ, fun ω => shiftChart (pChart A C ψ ω) (n ω), hcc, a,
    chiC κ, fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u, u, 𝓜, M, ε, inferInstance, E, g, h𝓦, hA, hPA, hγ,
    hγm, hunb, hdom, hfwd, hliftm, hliftc, hlift, measurable_add_smoothDist hh₀.measurable u, hu, hh0, hker, hmean,
    hKm, hKloc', hGood, hEm, hg, by filter_upwards [hdet] with ω hω hωA using hω hωA (hcc ω)⟩

/-- **`PocketChartTwoSeedStatement` with the determination from Aux. lemma 124's exterior decomposition**
(`pocketChartTwoSeedStatement_of_stop` with `hdet` replaced as in
`Lemma725RefRecovery.pocketChartFieldStatement_of_stop_exteriorDecomp`): the decomposition `h − g` conditionally a
zero-boundary GFF in an open subset of `C` given `𝓦` (`PocketExteriorDecomp`), a standard Borel record `E₀`
generating `𝓦` up to null sets, Proposition 5.13 for the ambient counterflow `η`, and the measurable pocket erasure
(`PocketErasure`). -/
theorem pocketChartTwoSeedStatement_of_stop_exteriorDecomp [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    {κ rL rR : ℝ} {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    (hGood : ∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤)
    (hdec : PocketExteriorDecomp 𝓦 P A C (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) η) :
    PocketChartTwoSeedStatement.{u} κ rL rR Good := by
  have hdet := pocketHistDet_of_exteriorDecomp (κ := κ) (γ := γ) (xL := fun _ => LP.twoSeedXL)
    (xR := fun _ => LP.twoSeedXR) h𝓦 hA hCo hCH hψ hCm hψm (measurable_add_smoothDist hh₀.measurable u) hdec hE₀
    hgen h513 hers
  obtain ⟨ε, mε, -, E, g, hEm, hg, hdetω⟩ := hdet n hn a
  exact pocketChartTwoSeedStatement_of_stop h𝓦 hA hPA hγ hγm hunb hCo hCH hψ hCm hψm hFo hgeo hh₀ hu hub hn hU hside
    hGood hEm hg hdetω

end Stop

/-! ### The named input: Theorem R.7's two-seed pocket at its stops -/

/-- **Named input: Theorem R.7's mixed or outer two-seed pocket with its stop data** (Theorem R.7 and §5.1–5.6 of the
supplement, pp. 471–478; the exact hypotheses of `pocketChartTwoSeedStatement_of_stop_exteriorDecomp` for the constant
word `(r_L; r_R)` and the pathwise property `Good`). On a standard Borel probability space with a walls σ-algebra `𝓦`
(the intended incoming labels, R.7: "Its component is selected from the intended incoming labels alone"): the selected
pocket `C` on a walls-event `A` of positive probability with its Jordan coordinate `ψ`; the erased relative traversal
`γ` (§5.4); the active hull sets `F q`; the field `h₀ + u`; the marked union laws (the marked optional union law, Lemma
R.5); the side limits with the canonical two-seed heights (Lemma R.5's corollary and **Lemma R.6's zero phase**);
`Good`; Aux. lemma 124's exterior decomposition, a standard Borel record, Proposition 5.13 for the ambient counterflow
and the measurable pocket erasure. **Not proved in Lean**: none of §5.1's random objects (the outer arms, the certified
frontiers, the selected mixed/outer pocket and its traversal) exists as Lean data. -/
def R7PocketStopStatement (κ rL rR : ℝ) (Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop) : Prop :=
  ∃ (Ω : Type u) (𝓦 : MeasurableSpace Ω) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
    (_ : IsProbabilityMeasure P) (A : Set Ω) (γ : Ω → ℝ → ℂ) (C : Ω → Set ℂ) (ψ : Ω → ℂ → ℂ)
    (F : ℝ≥0 → Ω → Set ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (n : Ω → ℤ) (a : ℝ)
    (ε₀ : Type u) (_ : MeasurableSpace ε₀) (_ : StandardBorelSpace ε₀) (E₀ : Ω → ε₀) (η : Ω → ℝ → ℂ),
    𝓦 ≤ mΩ ∧ MeasurableSet[𝓦] A ∧ 0 < P A ∧ (∀ ω ∈ A, IsDrivenCurve (γ ω)) ∧
    (∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u) ∧
    (∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖) ∧
    (∀ ω ∈ A, IsOpen (C ω)) ∧ (∀ ω ∈ A, C ω ⊆ H) ∧ (∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) ∧
    (∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω}) ∧
    (∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) ∧
    (∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω)) ∧
    (∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) ∧
    IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P ∧ InnerProductSpace.HarmonicOnNhd u H ∧
    (∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) ∧ Measurable[𝓦] n ∧
    (∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q) ∧
    (∀ q : ℝ≥0, PocketStopSideLimit κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P A γ
      (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀ u
      (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q) ∧
    (∀ᵐ ω ∂P, ω ∈ A → capLife (γ ω) = ⊤ → Good (fun t => segDriver (γ ω) t) ⊤) ∧
    PocketExteriorDecomp 𝓦 P A C (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) ∧
    Measurable[𝓦] E₀ ∧ 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P ∧
    (∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t) ∧
    PocketErasure 𝓦 P A γ (fun _ => LP.twoSeedXL) (fun _ => LP.twoSeedXR) η

/-- `PocketChartTwoSeedStatement` from Theorem R.7's pocket stop data. -/
theorem pocketChartTwoSeedStatement_of_r7PocketStop {κ rL rR : ℝ} {Good : (ℝ≥0 → ℝ) → ℝ≥0∞ → Prop}
    (h : R7PocketStopStatement.{u} κ rL rR Good) : PocketChartTwoSeedStatement.{u} κ rL rR Good := by
  obtain ⟨Ω, 𝓦, mΩ, hSB, P, hP, A, γ, C, ψ, F, h₀, u, n, a, ε₀, mε₀, hSBε₀, E₀, η, h𝓦, hA, hPA, hγ, hγm, hunb,
    hCo, hCH, hψ, hCm, hψm, hFo, hgeo, hh₀, hu, hub, hn, hU, hside, hGood, hdec, hE₀, hgen, h513, hers⟩ := h
  exact pocketChartTwoSeedStatement_of_stop_exteriorDecomp h𝓦 hA hPA hγ hγm hunb hCo hCH hψ hCm hψm hFo hgeo hh₀ hu
    hub hn hU hside hGood hdec hE₀ hgen h513 hers

/-- **Theorem R.7's reference (`hR7`) from Theorem R.7's pockets at their stops, on the whole range**
(`r_L, r_R > −2`, `max(r_L, r_R) ≥ κ/2 − 4`; no upper seed-weight bound, `Good` the transient continuous trace). -/
theorem r7ReferenceStatement_of_r7PocketStop
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      R7PocketStopStatement.{u} κ rL rR fun w ζ => ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ζ η ∧
        (ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) :
    R7.R7ReferenceStatement.{u} :=
  r7ReferenceStatement_of_pocketChartTwoSeed_all fun κ hκ rL rR hL hR hmax =>
    pocketChartTwoSeedStatement_of_r7PocketStop (h κ hκ rL rR hL hR hmax)

end InteractingSLE.Sec7.R7Pocket
