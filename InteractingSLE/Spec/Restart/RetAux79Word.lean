/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetAux79
import InteractingSLE.Spec.Restart.RetAux79Chart
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# (III-b) from the boundary data, and the later-line mean identity for the retained charts

Packet PROVE-RETAUX79 (PROVE-DOMAINMARKOV8 §2, (III-b)). The word identity (III-b) says that the bounded harmonic
extension `u` of the continuation's force data at capacity time `Q` is `m + a` on `ℍ`, where `m = c.mean` is the word
mean of the later line and `a = θ₂χ`. Bounded harmonic extensions are unique off finite sets
(`PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension`), so (III-b) follows from the **boundary-data identity**

  `forceBoundaryData κ ρL ρR vL vR y = c.fn y + a` for all real `y` outside a finite set

(`eqOn_mean_add_of_forceBoundaryData`). Combined with (III-a) for the retained charts (`retChart_trans`) and the
pathwise (III) assembly (`chartTransport_eq_integral_couplingMean_of_trans`), this gives the later-line mean identity
of `Aux79.hasSafeLaw_of_lineKernel` for the retained charts of `Supp7.RetData`
(**`retLine_chartTransport_eq_integral_couplingMean`**), with the boundary-data identity and the chart-path facts as
its explicit inputs.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Restart.RetAux79

open Supp7 Chart

/-- **(III-b) from the boundary data.** If the force data agree with the boundary function of a sorted word plus `a`
off a finite set, then every bounded harmonic extension of the force data is the word mean plus `a` on `ℍ`. -/
theorem eqOn_mean_add_of_forceBoundaryData {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    {c : BoundaryWord} (hc : c.IsSorted) (a : ℝ) {S : Set ℝ} (hS : S.Finite)
    (hdata : ∀ y ∉ S, forceBoundaryData κ ρL ρR vL vR y = c.fn y + a) :
    ∀ z ∈ H, u z = c.mean z + a := by
  set S' : Set ℝ := S ∪ forceJumpSet vL vR ∪ (c.jumps : Set ℝ) with hS'def
  have hJ : (forceJumpSet vL vR).Finite :=
    ((Set.finite_range vL).union (Set.finite_range vR)).insert 0
  have hS' : S'.Finite := (hS.union hJ).union c.jumps.finite_toSet
  have h1 : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) S' u :=
    ⟨hu.1, hu.2.1, fun x hx => hu.2.2 x fun h => hx (Or.inl (Or.inr h))⟩
  obtain ⟨hharm, ⟨C, hC⟩, hlim⟩ := BoundaryWord.isBoundedHarmonicExtension_mean c hc
  have h2 : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) S' (fun z => c.mean z + a) := by
    refine ⟨fun z hz => (hharm z hz).add (InnerProductSpace.harmonicAt_const _), ⟨C + |a|, fun z hz => ?_⟩,
      fun x hx => ?_⟩
    · calc |c.mean z + a| ≤ |c.mean z| + |a| := abs_add_le _ _
        _ ≤ C + |a| := by linarith [hC z hz]
    · rw [hdata x fun h => hx (Or.inl (Or.inl h))]
      exact (hlim x fun h => hx (Or.inr h)).add tendsto_const_nhds
  exact fun z hz => (PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hS' h2 h1 hz)

/-- **The later-line mean identity for the retained charts** (`hmean` of `Aux79.hasSafeLaw_of_lineKernel` at one line
and one `ω`). Let `d`, `d'` be retained data at the stop line and at a later line, `ω` in both chart events, and let the
later union be the earlier one plus the `d.inv ω`-image of the continuation's chart path `γ`, a simple generating trace
of the continuous driver `W` up to capacity time `Q > 0` ending at the later tip (the hypotheses of `retChart_trans`).
Let `M` be the line mean, whose transport in the later chart is the mean of a sorted word `c` (the landed later-line
identification, LEMMA76G), and suppose the boundary-data identity: the force data of the continuation at `Q` (positions
`vL`, `vR`) are `c.fn + a` off a finite set. Then `M` read in the stop-line chart with height shift `a` is the coupling
mean `𝔥_Q` of the continuation against every test function supported off the hull `K̃_Q`. -/
theorem retLine_chartTransport_eq_integral_couplingMean (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E) (hω' : ω ∈ d'.E)
    {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} {ζc : ℝ≥0∞} {Q : ℝ≥0}
    (hg : IsGeneratingTrace W ζc γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn γ {s | (s : ℝ≥0∞) ≤ ζc}) (hQ : (Q : ℝ≥0∞) < ζc) (hQ0 : 0 < Q)
    (hKP : fillH (d.K ω) ⊆ fillH (d'.K ω)) (hPK : d'.K ω ⊆ d.K ω ∪ d.inv ω '' (γ '' Icc 0 Q))
    (hγP : ∀ s ∈ Icc 0 Q, d.inv ω (γ s) ∈ d'.K ω) (htip : d.inv ω (γ Q) = d'.η₂ ω d'.r)
    {M : DistOn upperHalfPlaneOpens} {c : BoundaryWord} (hc : c.IsSorted)
    (hid : ∀ φ : TestOn upperHalfPlaneOpens,
      chartTransport (hd'.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ) M φ = ∫ w, c.mean w * φ w)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR) (forceJumpSet vL vR) u)
    (a : ℝ) {S : Set ℝ} (hS : S.Finite) (hdata : ∀ y ∉ S, forceBoundaryData κ ρL ρR vL vR y = c.fn y + a)
    (ψ : TestOn upperHalfPlaneOpens) (hψ : tsupport ψ ⊆ H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) :
    chartTransport (hd.isConformal_chart ω) 1 a (QuantumZipper.chiC κ) M ψ =
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal) Q u z * ψ z := by
  obtain ⟨hinv, hlift⟩ := retChart_trans hd hd' hω hω' hg hWc hW0 hinj hQ hQ0 hKP hPK hγP htip
  exact chartTransport_eq_integral_couplingMean_of_trans κ (hd.isConformal_chart ω) (hd'.isConformal_chart ω)
    ((hd.isConformal_chart ω).continuousOn_lift_inv (hd.continuousOn_lift_chart ω))
    (hWc.comp continuous_real_toNNReal) (by simp [hW0]) Q.coe_nonneg hinv hlift (BoundaryWord.continuousOn_mean c)
    a hid (eqOn_mean_add_of_forceBoundaryData hu hc a hS hdata) ψ hψ

/-- **The mean identity at capacity time `0`** (the stop line itself, where the later-line chart is the stop-line
chart): from the stop-line identification and `u = m + a` on `ℍ`. -/
theorem chartTransport_eq_integral_couplingMean_zero (κ : ℝ) {c₀ : Chart} (h₀ : c₀.IsConformal)
    (hℓ₀ : ContinuousOn (fun w => c₀.2.2 (c₀.2.1 w)) H) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {M : DistOn upperHalfPlaneOpens} {m u : ℂ → ℝ} (hm : ContinuousOn m H) (a : ℝ)
    (hid : ∀ φ : TestOn upperHalfPlaneOpens,
      chartTransport h₀ 1 0 (QuantumZipper.chiC κ) M φ = ∫ w, m w * φ w)
    (hu : ∀ w ∈ H, u w = m w + a) (ψ : TestOn upperHalfPlaneOpens) :
    chartTransport h₀ 1 a (QuantumZipper.chiC κ) M ψ = ∫ z, couplingMean κ W 0 u z * ψ z := by
  have hinv : ∀ w ∈ H, c₀.2.1 w = c₀.2.1 (fwdMapInv W 0 w) := fun w hw => by
    rw [fwdMapInv_zero_time hW hW0 hw]
  have hlift : ∀ w ∈ H, c₀.2.2 (c₀.2.1 w) =
      (logDerivFwd W 0 (fwdMapInv W 0 w)).im + c₀.2.2 (c₀.2.1 (fwdMapInv W 0 w)) := fun w hw => by
    rw [fwdMapInv_zero_time hW hW0 hw, show logDerivFwd W 0 w = 0 by simp [QuantumZipper.logDerivFwd],
      Complex.zero_im, zero_add]
  refine chartTransport_eq_integral_couplingMean_of_trans κ h₀ h₀ hℓ₀ hW hW0 le_rfl hinv hlift hm a hid hu ψ ?_
  rw [QuantumZipper.RS.fwdHull_zero_eq_empty hW, sdiff_empty]
  exact ψ.tsupport_subset

end Restart.RetAux79

end InteractingSLE
