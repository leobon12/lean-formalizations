import QuantumZipper.Proofs.Section5.Prop16LocalAssembly
import QuantumZipper.Proofs.Section5.Prop16GAssembly
import QuantumZipper.Proofs.Section5.Prop16WeakAssembly

/-!
# Proposition 1.6, wiring: the three elementary nodes from a local good-sample hypothesis

This file discharges the three "elementary" inputs of
`Prop16Asm.theorem1_6_of_nodes'` from a single hypothesis on the underlying mixed GFF
`X`: almost surely, `X ω` is locally good (`Prop16Area.G.IsLocallyGoodOn γ (D ∪ (a,b))`)
on the union of the domain `D` and the free boundary arc `(a,b)`. The hypothesis is packaged
as `Prop16LocGoodStmt`, quantified over the data `Prop16Data` of `theorem1_6` exactly like the
other node Props of `Prop16Assembly.lean`.

Concretely:

* `prop16NuMeasStmt_of_loc`: D4-MEAS, a.e.-measurability of `ω ↦ ν_{h(ω)}`. Route: `hloc`
  gives a.s. the local boundary measure of `𝔥₀ + X ω` on `(a,b)` (`Prop16Area.G.prop16_hexB`,
  from the deterministic core `local_limits_of_isLocallyGoodOn`), and
  `Prop16Area.G.aemeasurable_prop16Nu` converts that a.s. existence into measurability of the
  random measure;
* `prop16ZoomAreaStmt_of_loc`: the zoomed field `h(· + x) + C/γ` a.s. has a local area measure
  on `D − x`. Route: `Prop16Area.G.prop16_hA0` for every `ω` in the good event, transported to
  the weighted law `prop16Law` by `Prop16Area.G.hG_prop16`;
* `prop16CanonAreaStmt_of_loc`: the canonical description of the zoomed field a.s. has a local
  area measure. Route: `Prop16Area.G.prop16_hA1` (area limits of every rescaling `s > 0`)
  plus the deterministic step `Prop16Area.G.exists_vague_canonicalOn` (a canonical field is a
  rescaled zoomed field at scale `scaleParamOn`, and the zero-scale case has empty domain),
  transported by `hG_prop16`.

The transport `hG_prop16` needs the a.e.-measurability of `ω ↦ ν_{h(ω)}`, which is
`prop16NuMeasStmt_of_loc`, so the three lemmas share that first step; no node needs more than
`hloc`.

With these, `theorem1_6_of_loc_tvw (hloc) (hTVw)` produces `theorem1_6` from the weak TV-local
node D4⁺ʷ (decision D24, `Prop16TVWeakStmt`) alone: the scale node and the strong TV node are
no longer inputs.

Source: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Proposition 1.6
and its proof (pp. 24–25); the local/global good-sample decomposition underlying
`IsLocallyGoodOn` is the domain-Markov decomposition of Sheffield, *Gaussian free fields for
mathematicians*, PTRF 139 (2007), Thm. 2.17, as recorded in `Prop16LocalAssembly.lean`. The
arguments here are pure wiring (own elementary proof); no statement of `theorem1_6` is changed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Node `hloc` (local good-sample hypothesis).** Almost surely, `X ω` is locally good on
`D ∪ (a,b)`: on an open neighbourhood of `D ∪ (a,b)` it agrees on the dyadic folded circles
with a good sample plus a continuous function (`Prop16Area.G.IsLocallyGoodOn`). This is the
input from which the three elementary nodes of `theorem1_6_of_nodes'` are derived below. -/
def Prop16LocGoodStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ᵐ ω ∂P, Prop16Area.G.IsLocallyGoodOn γ (D ∪ realSet (Set.Ioo a b)) (X ω)

/-- **D4-MEAS from `hloc`.** The random boundary measure `ω ↦ ν_{h(ω)}` is a.e.-measurable:
`hloc` gives a.s. the local boundary limit of `𝔥₀ + X ω` on `(a,b)`, which is exactly the
hypothesis of `Prop16Area.G.aemeasurable_prop16Nu`. -/
theorem prop16NuMeasStmt_of_loc (hloc : Prop16LocGoodStmt) : Prop16NuMeasStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  have hlω := hloc γ D c d a b h0 P X hdat
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, hh0, hP, hX, hpos, hfin⟩ := hdat
  obtain ⟨hDo, hDc, hDb, hDH, hcd, hfr, hhd⟩ := hgeo
  exact Prop16Area.G.aemeasurable_prop16Nu hX.measurable_coord
    (Prop16Area.G.prop16_hexB hγ hDo hDH hh0 hlω)

/-- **The zoomed-field area node from `hloc`.** For every level `C`, under the weighted law
`prop16Q` the zoomed field `h(· + x) + C/γ` a.s. has a local area measure on `D − x`. -/
theorem prop16ZoomAreaStmt_of_loc (hloc : Prop16LocGoodStmt) : Prop16ZoomAreaStmt := by
  intro γ D c d a b h0 Ω _ P X hdat C
  have hlω := hloc γ D c d a b h0 P X hdat
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, hh0, hP, hX, hpos, hfin⟩ := hdat
  obtain ⟨hDo, hDc, hDb, hDH, hcd, hfr, hhd⟩ := hgeo
  refine Prop16Area.G.hG_prop16 hν hfin (G := fun C p => ∃ m, IsVagueLimitOn (zoomDomain D p.2)
      (areaApprox γ (zoomField γ C (ofFun h0 + X p.1) p.2)) m) (fun C => ?_) C
  exact (Prop16Area.G.prop16_hA0 hγ hDo hDH hh0 hlω C).mono
    fun ω hω t ht => hω t ht

/-- **The canonical-field area node from `hloc`.** For every level `C`, under the weighted law
`prop16Q` the canonical description of the zoomed field a.s. has a local area measure on
`canonicalDomainOn γ (h(· + x) + C/γ) (D − x)`. The canonical field is the rescaling of the
zoomed field at the canonical scale, so `prop16_hA1` (a.s. area limits of every rescaling
`s > 0`) plus the deterministic `exists_vague_canonicalOn` give it. -/
theorem prop16CanonAreaStmt_of_loc (hloc : Prop16LocGoodStmt) : Prop16CanonAreaStmt := by
  intro γ D c d a b h0 Ω _ P X hdat C
  have hlω := hloc γ D c d a b h0 P X hdat
  have hν := prop16NuMeasStmt_of_loc hloc γ D c d a b h0 P X hdat
  obtain ⟨hγ, hγ2, hgeo, hab, hca, hbd, hh0, hP, hX, hpos, hfin⟩ := hdat
  obtain ⟨hDo, hDc, hDb, hDH, hcd, hfr, hhd⟩ := hgeo
  refine Prop16Area.G.hG_prop16 hν hfin (G := fun C p => ∃ m, IsVagueLimitOn
      (canonicalDomainOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2))
      (areaApprox γ (canonicalOn γ (zoomField γ C (ofFun h0 + X p.1) p.2)
        (zoomDomain D p.2))) m) (fun C => ?_) C
  refine (Prop16Area.G.prop16_hA1 hγ hDo hDH hh0 hlω C).mono
    fun ω hω t ht => ?_
  exact Prop16Area.G.exists_vague_canonicalOn (Prop16Area.G.zero_notMem_zoomDomain hDH t)
    (fun s hs => hω t ht s hs)

/-- **Proposition 1.6 from the local good-sample hypothesis and the weak TV node.**

All three elementary nodes (`Prop16NuMeasStmt`, `Prop16ZoomAreaStmt`, `Prop16CanonAreaStmt`)
follow from `hloc`, so the only remaining input is D4⁺ʷ (`Prop16TVWeakStmt`, decision D24),
fed through D4-a′ `Prop16Area.areaConvergesInLawOn_of_tvLocal_close` by
`theorem1_6_of_nodes'`. -/
theorem theorem1_6_of_loc_tvw (hloc : Prop16LocGoodStmt) (hTVw : Prop16TVWeakStmt) :
    theorem1_6 :=
  theorem1_6_of_nodes' (prop16NuMeasStmt_of_loc hloc) (prop16ZoomAreaStmt_of_loc hloc)
    (prop16CanonAreaStmt_of_loc hloc) hTVw

end Prop16Asm

end QuantumZipper
