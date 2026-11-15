/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripEndpointLife

/-!
# Constant strip drift `|σ| < 1`: the strip-driver form of the endpoint theorem

Packet PROVE-ZHAN-A4. Astra, *Formalization proofs and dependency audit* (ruling R35), "Constant drift with
`|σ| < 1`: from the diffusion to the actual trace" (`source/external/AstraIG1/ig1_formalization_proofs.txt`
L1420–L1499): for the constant-drift strip chain `ξ_t = √κ B_t + σ t` with `|σ| < 1`, "this proves the actual
endpoint" — the trace converges to one finite point of the upper line `ℝ + iπ`.

In the R36 form (`Foundations/Strip/SLE.lean`) a strip chain is read through its chordal image: a chordal driver
`w` with the end mark `v` (the image of `−∞`, started at `−1`), the strip clock `t(s) = ∫₀ˢ (w − v)⁻²`, and the strip
driver `ξ_t = t + log(w − v)` at chordal time `s(t)`. On the strip life the path `(w, v)` is determined by `ξ`
(`w − v = e^{ξ − t}`, `dv/dt = −2(w − v)`, `ds/dt = (w − v)²`), so the theorem is a statement about the strip driver.

## Main definitions

* `IsStripPath w v ζ`: `w 0 = 0`, on the strip life `(w, v)` is a separated mark pair (`IsSepMark`: continuity,
  `v < w`, the end-mark equation), and the strip clock is unbounded on the strip life;
* `HasStripDriver w v ζ ξ`: a strip path whose strip driver is `ξ` at every strip time;
* `StripConv w v ζ`: clause (3) of `HasStripEndpoint` (every generating trace on the strip life converges along it
  to a point `x < −1`, the chordal image of a point of `ℝ + iπ`);
* `ConstDriftEndpointStatement κ`: **named input** (the source theorem of L1420–L1499, strip-driver form): for every
  `|σ| < 1` and every filtered Brownian motion `β`, almost surely every strip path whose strip driver is
  `√κ β + σ t` satisfies `HasStripEndpoint`.

## Main results

* `IsIntegratedSLEPath.isStripPath`: the chordal path of an R36 strip evolution with unbounded strip clock is a
  strip path;
* `ae_hasStripEndpoint_noMarks_of_constDrift`: from the named input, the strip endpoint theorem for a strip evolution
  with no lower marks (its strip driver is `√κ B̃ + σ t`, `σ = (q₋ − q₊)/2`, by `exists_stripBrownian_of_prefixSums`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

open Strip

/-! ### Strip paths and their strip drivers -/

/-- A strip path: `w 0 = 0`, the driver and the end mark form a separated mark pair on every strip-life interval,
and the strip clock is unbounded on the strip life (the strip chain lives for all strip times). -/
def IsStripPath (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  w 0 = 0 ∧ (∀ s : ℝ≥0, IsStripLife w v ζ s → IsSepMark (extPath w) (extPath v) s) ∧
    HasUnboundedStripClock w v ζ

/-- A strip path whose strip driver is `ξ` at every strip time. -/
def HasStripDriver (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (ξ : ℝ≥0 → ℝ) : Prop :=
  IsStripPath w v ζ ∧ ∀ t : ℝ≥0, stripDriver (extPath w) (extPath v) t = ξ t

/-- Clause (3) of `HasStripEndpoint`: every continuous generating chordal trace on the strip life converges, along
the strip life, to a point `x < −1` (the chordal image of a finite point of the upper line `ℝ + iπ`). -/
def StripConv (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ∀ η : ℝ≥0 → ℂ, (∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) →
    ∃ x : ℝ, x < -1 ∧ ∀ ε > 0, ∃ s₀ : ℝ≥0, IsStripLife w v ζ s₀ ∧
      ∀ s : ℝ≥0, s₀ ≤ s → IsStripLife w v ζ s → ‖η s - x‖ < ε

theorem HasStripEndpoint.stripConv {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : HasStripEndpoint w v ζ) :
    StripConv w v ζ :=
  h.2.2

theorem hasStripEndpoint_of_stripConv {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : IsStripPath w v ζ)
    (htr : ∃ η : ℝ≥0 → ℂ, ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η)
    (hc : StripConv w v ζ) : HasStripEndpoint w v ζ :=
  ⟨h.2.2, htr, hc⟩

/-- **Named input: Zhan's constant-drift endpoint theorem, `|σ| < 1`** (Astra L1420–L1499, "Constant drift with
`|σ| < 1`: from the diffusion to the actual trace"; [Zha10, Theorem 4.1]), in strip-driver form. For every
`|σ| < 1` and every Brownian motion `β` of a filtration, almost surely: every strip path whose strip driver is
`ξ_t = √κ β_t + σ t` has a continuous generating chordal trace on its strip life, and every such trace converges
along the strip life to a point `x < −1` (an actual endpoint on the upper line `ℝ + iπ`). -/
def ConstDriftEndpointStatement (κ : ℝ) : Prop :=
  ∀ σ : ℝ, |σ| < 1 → ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ)
    (β : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 β P →
      ∀ᵐ ω ∂P, ∀ (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞),
        HasStripDriver w v ζ (fun t => Real.sqrt κ * β t ω + σ * t) → HasStripEndpoint w v ζ

/-! ### The chordal path of a strip evolution is a strip path -/

variable {nL nR : ℕ}

/-- The chordal path of an R36 strip evolution (driver `w`, end mark `vL (Fin.last nL)`) with unbounded strip
clock is a strip path. -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.isStripPath {a : ℝ} {pL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a (wordXL pL) xR ρL ρR w vL vR b ζ)
    (hc : HasUnboundedStripClock w (vL (Fin.last nL)) ζ) : IsStripPath w (vL (Fin.last nL)) ζ :=
  ⟨hp.1, fun _ hs => isSepMark_of_isIntegratedSLEPath hp hs, hc⟩

/-! ### The strip endpoint theorem without lower marks, from the named input -/

theorem isSeparatedStripWord_elim0 {pL pR : Fin 0 → ℝ} : IsSeparatedStripWord pL pR :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem hasStripPrefixSums_elim0 {κ : ℝ} {ρL ρR : Fin 0 → ℝ} : HasStripPrefixSums κ ρL ρR :=
  ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- The drift of the constant-drift strip driver without lower marks: `σ = (q₋ − q₊)/2`, and `|q₊ − q₋| < 2`
is `|σ| < 1`. -/
theorem abs_sigma_lt_one_of_noMarks {κ τm : ℝ} {ρL ρR : Fin 0 → ℝ}
    (hq : |chargePlus κ ρL ρR τm - chargeMinus ρL τm| < 2) :
    |(τm - tauPlus κ ρL ρR τm) / 2| < 1 := by
  have e : chargePlus κ ρL ρR τm - chargeMinus ρL τm = -(2 * ((τm - tauPlus κ ρL ρR τm) / 2)) := by
    simp only [chargePlus, chargeMinus, Finset.univ_eq_empty, Finset.sum_empty]; ring
  rw [e, abs_neg, abs_mul, abs_two] at hq
  linarith

variable {κ τm : ℝ} {pL pR ρL ρR : Fin 0 → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (0 + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The strip endpoint theorem for a strip evolution without lower marks**, from the named constant-drift input:
the strip driver is `√κ B̃ + σ t` with `σ = (q₋ − q₊)/2`, `|σ| < 1`. -/
theorem ae_hasStripEndpoint_noMarks_of_constDrift (hκ : 0 < κ) (h : ConstDriftEndpointStatement.{u} κ)
    (hq : |chargePlus κ ρL ρR τm - chargeMinus ρL τm| < 2)
    (hE : IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, HasStripEndpoint (W · ω) (VL (Fin.last 0) · ω) (ζ ω) := by
  obtain ⟨𝓗, B', hB', hdr⟩ :=
    exists_stripBrownian_of_prefixSums hκ isSeparatedStripWord_elim0 hasStripPrefixSums_elim0 hE
  filter_upwards [h _ (abs_sigma_lt_one_of_noMarks hq) P 𝓗 B' hB', hdr, hE.ae_isIntegratedSLEPath,
    ae_hasUnboundedStripClock hκ isSeparatedStripWord_elim0 hasStripPrefixSums_elim0 hE]
    with ω hb hd hp hc
  refine hb _ _ _ ⟨hp.isStripPath hc, fun t => ?_⟩
  rw [(hd t).2]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]

end Zhan

end InteractingSLE
