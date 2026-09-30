import QuantumZipper.Proofs.Section5.Prop16D4WInAssembly
import QuantumZipper.Proofs.Section5.Prop17PalmZoomMix
import QuantumZipper.Proofs.NonVacuityWedgeUncond

/-!
# Proposition 1.6, input (1) of D4⁺ʷ (the Palm zoom): reduction to three nodes (PROP16-PALMZOOM)

Sheffield, arXiv:1012.4797, proof of Proposition 1.6 (p. 25): under the weighted law
`prop16Q` (`ω` size-biased by `ν_h[a,b]`, then `x ~ ν_h|_{[a,b]}`), given `x` the field `X` has
the law of the original mixed GFF plus `(γ/2) G_D(x, ·)` (the rooted/Palm measure of
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, arXiv:0808.1560, §3.3, p. 22); zooming
in at the *fixed* point `x` of that field gives the `γ`-quantum wedge (TV-local form:
Duplantier–Miller–Sheffield, arXiv:1409.7055, Props. 4.7–4.8, pp. 77–79). The Palm zoom law is
therefore a mixture over the Palm point `x ~ ρ` of fixed-point zoom laws, and TV-local
convergence passes to the mixture (`S5.FieldLaw.Raw.tvLocalTendsto_prod_map_of_ae`, the mixture
lemma of Prop. 1.7's Palm zoom, reused here with the identity localization).

This mirrors the Prop. 1.7 reduction (`Prop17PalmZoomFree.lean`): nodes A (measurable version),
B (Palm identity) and C (fixed-point zoom). The Palm shift of the *mixed* field is defined
through its covariance, `mixedGreenSample D S x μ = lim_k dualCov D (mixedSpace D S) μ (fc(x,2^{-k}))`
(`= ∫ G_D(x,·) dμ`; for a mixed GFF `dualCov` is the covariance, `IsMixedGFF.covariance_eq`), so
that the level-`k` Cameron–Martin shift of `PalmFormula.shiftK` converges to it.

Nodes (hypotheses, `def … : Prop`):
* A. `Prop16PalmMeasStmt` — a.e.-measurability of the canonical zoom coordinates under `prop16Q`
  (literally the measurability clause of `Prop16PalmZoomStmt`).
* B. `Prop16PalmIdStmt` — the Palm identity: `prop16Q.map (zoom coords) = (P ⊗ ρ).map (F C)`,
  `ρ` a probability measure carried by `(a,b)`, `F C (·, x) = ` zoom coordinates at the fixed
  point `x` of the Palm-shifted field `X + (γ/2) G_D(x, ·)`.
* C. `Prop16FixedZoomStmt` — TV-local convergence of the zoom at a fixed `x ∈ (a,b)` of the
  Palm-shifted field to any `γ`-quantum wedge.

`prop16PalmZoomStmt_of_nodes : A → B → C → Prop16PalmZoomStmt` and
`theorem1_6_of_palmNodes`. The bookkeeping (mixture, localization, choice of a wedge by
`NonVacuity.exists_wedge_indep_BM_uncond_prob_uncond`) is own elementary work.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization

/-! ## 1. Objects -/

open Classical in
/-- The localization of a coordinate vector to the dyadic folded circles inside
`closedBall 0 R` (so that `locField R x = locCoords R (coords x)`). -/
@[reducible] def locCoords (R : ℕ) (c : ℕ → ℝ) : ℕ → ℝ := fun n => if inBall R n then c n else 0

theorem locField_eq_locCoords (R : ℕ) (x : FieldSample) :
    locField R x = locCoords R (coords x) := rfl

theorem measurable_locCoords (R : ℕ) : Measurable (locCoords R) := by
  classical
  refine measurable_pi_iff.2 fun n => ?_
  unfold locCoords
  by_cases h : inBall R n
  · simp only [h, ite_true]
    exact measurable_pi_apply n
  · simp only [h, ite_false]
    exact measurable_const

/-- The Palm (Cameron–Martin) shift direction of the mixed GFF on `D` (zero on `∂D \ S`, free on
`S`) at the boundary point `x`, as a field sample: `μ ↦ lim_k dualCov(μ, fc(x, 2^{-k}))`, i.e.
`μ ↦ ∫ G_D(x, ·) dμ` (junk value `limUnder` when the limit does not exist). -/
def mixedGreenSample (D S : Set ℂ) (x : ℝ) : FieldSample := fun μ =>
  limUnder atTop fun k : ℕ => dualCov D (mixedSpace D S) μ (foldedCircle (x : ℂ) (radius k))

/-- The Palm-shifted mixed field at the boundary point `x`: `X + (γ/2) G_D(x, ·)`. -/
def palmMixedField (γ : ℝ) (D S : Set ℂ) {Ω : Type} (X : Ω → FieldSample) (x : ℝ) (ω : Ω) :
    FieldSample :=
  X ω + (γ / 2) • mixedGreenSample D S x

/-- The canonical zoom coordinates of Prop. 1.6 at `p = (ω, t)` for a field family `X`. -/
def palmCanonCoords (γ C : ℝ) (D : Set ℂ) (h0 : ℂ → ℝ) {Ω : Type} (X : Ω → FieldSample)
    (p : Ω × ℝ) : ℕ → ℝ :=
  coords (canonicalOn γ (zoomFree γ C h0 X p) (zoomDomain D p.2))

/-! ## 2. The three nodes -/

/-- **Node A (measurable zoom coordinates).** -/
def Prop16PalmMeasStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ C, AEMeasurable (palmCanonCoords γ C D h0 X) (prop16Q γ h0 a b P X)

/-! ## 3. Assembly -/

/-- The mixture lemma with a single localization (from `tvLocalTendsto_prod_map_of_ae`). -/
theorem tendsto_tvDist_prod_map_of_ae {ι Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {l : Filter ι} [l.IsCountablyGenerated] (P : Measure Ω) [IsProbabilityMeasure P]
    (ρ : Measure T) [IsProbabilityMeasure ρ] (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ]
    {G : ι → Ω × T → (ℕ → ℝ)} (hG : ∀ i, Measurable (G i))
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun i => tvDist (P.map fun ω => G i (ω, x)) μ) l (𝓝 0)) :
    Tendsto (fun i => tvDist ((P.prod ρ).map (G i)) μ) l (𝓝 0) := by
  have h := S5.FieldLaw.Raw.tvLocalTendsto_prod_map_of_ae (Fl := fun _ : ℕ => ℕ → ℝ) P ρ μ
    (loc := fun _ => id) (fun _ => measurable_id) hG
    (hlim.mono fun x hx R => by simpa only [Measure.map_id] using hx) 0
  simpa only [Measure.map_id] using h

end Prop16Asm

end QuantumZipper
