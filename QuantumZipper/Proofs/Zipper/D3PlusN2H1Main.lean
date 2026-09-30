import QuantumZipper.Proofs.Zipper.D3PlusN2H1Reg
import QuantumZipper.Proofs.GFF.FrostmanReg

/-!
# N2-H1: independence of the lateral data of the local field from its radial Brownian motion

Task N2-H1 (`N2HLatIndepStmt`, `D3PlusN2HeartStmt.lean`), in the form restricted by
`DECISIONS.md` D36: the lateral data `n2LatY X r` read at any family `e : ι → Measure ℂ` of
measures at which the free field's dyadic regularization converges a.s. (in particular folded
circles and bounded compactly supported densities, `regAt_foldedCircle`, `regAt_of_le_smul_volume`)
are independent of the radial Brownian path `zRadB X r`.

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), p. 77
(independence of the projections onto `H₁(ℍ)` and `H₂(ℍ)`: rotation invariance of the Green
function); Sheffield, arXiv:1012.4797, p. 25. Route: `D3PlusN2H1Kernel` (Gaussian independence of
the free field's lateral family from its radial family), `D3PlusN2H1RadFam` (radial averages of
the local field; the balayage is radial), `D3PlusN2H1Reg` (regularized evaluation of the local
field), and the transfer of independence along coordinatewise a.e. equal representatives.

The unrestricted `N2HLatIndepStmt` follows from the same argument given a.s. regularization at
every local measure (`n2HLatIndep_of_regAll`); that hypothesis is the project gap
`F2.EvalRegRawStmt`/D17 and is not proved.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK

/-- A.s. convergence of the dyadic regularization of `X` at `ν`. -/
def RegAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample)
    (ν : Measure ℂ) : Prop :=
  ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν) atTop (𝓝 (X ω ν))

section Repr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- **Representation of the lateral data** at a measure where the regularization converges:
a.s. `n2LatY X r ν = L ν − L (bal ν)` with `L μ = X μ − X (radSmear μ)` (junk `0` off local
measures on both sides). -/
theorem ae_n2LatY_eq_latFamMap (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r)
    {ν : Measure ℂ} (hreg : K3.IsLocalH 0 r ν → RegAt P X ν) :
    ∀ᵐ ω ∂P, n2LatY X r ω ν = latFamMap r hr (fun μ => latFam X μ ω) ν := by
  classical
  by_cases hν : K3.IsLocalH 0 r ν
  · filter_upwards [ae_evalReg_locZField hX hr hν (hreg hν),
      ae_integral_radAvgReg_locZField hX hr hν, ae_X_radSmear_bal hX hr hν] with ω h1 h2 h3
    simp only [n2LatY, if_pos hν, lateralPart, latFamMap, dif_pos hν, latFam]
    rw [h1, h2, h3, locZField_apply_of_local X ω hν]
    simp only [K3.markovZ]
    ring
  · exact ae_of_all _ fun ω => by simp [n2LatY, latFamMap, hν]

/-- **N2-H1 (restricted index).** For any family of measures at each of which the free field's
regularization converges a.s. (when the measure is local), the lateral data of the local field
read at the family are independent of the radial Brownian path. -/
theorem indepFun_n2LatY_family (hX : IsFreeGFFModConstH X P) {r : ℝ} (hr : 0 < r)
    {ι : Type*} (e : ι → Measure ℂ) (hreg : ∀ i, K3.IsLocalH 0 r (e i) → RegAt P X (e i)) :
    IndepFun (fun ω i => n2LatY X r ω (e i)) (pathOf (zRadB X r)) P := by
  set Φ : (AdmIdx → ℝ) → ι → ℝ := fun ℓ i => latFamMap r hr ℓ (e i) with hΦ
  have hΦm : Measurable Φ :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply (e i)).comp (measurable_latFamMap r hr)
  set L : Ω → ι → ℝ := Φ ∘ fun ω (μ : AdmIdx) => latFam X μ ω with hL
  set R : Ω → (ℝ≥0 → ℝ) := radFamMap r ∘ fun ω (t : ℝ) => gaussFam X radPair t ω with hR
  have hind : IndepFun L R P := (indepFun_latFam_radPair hX).comp hΦm (measurable_radFamMap r)
  have hLm : AEMeasurable L P := (hΦm.comp (measurable_latFam hX)).aemeasurable
  have hRm : AEMeasurable R P :=
    ((measurable_radFamMap r).comp (measurable_gaussFam_pi hX radPair)).aemeasurable
  have hYm : Measurable fun ω i => n2LatY X r ω (e i) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply (e i)).comp (measurable_n2LatY hX hr)
  have hrep : ∀ i, ∀ᵐ ω ∂P, n2LatY X r ω (e i) = L ω i := fun i =>
    ae_n2LatY_eq_latFamMap hX hr (hreg i)
  have hprod : P.map (fun ω => (L ω, R ω)) = (P.map L).prod (P.map R) :=
    (indepFun_iff_map_prod_eq_prod_map_map hLm hRm).1 hind
  have hjoint : P.map (fun ω => ((fun i => n2LatY X r ω (e i)), pathOf (zRadB X r) ω)) =
      P.map (fun ω => (L ω, R ω)) := by
    set E := MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ℝ≥0 => ℝ with hE
    have hWt : Measurable fun ω (j : ι ⊕ ℝ≥0) =>
        Sum.elim (fun i => n2LatY X r ω (e i)) (fun t => zRadB X r t ω) j := by
      refine measurable_pi_iff.2 fun j => ?_
      rcases j with i | t
      · exact (measurable_pi_apply i).comp hYm
      · exact measurable_zRadB_coord hX hr t
    have hWr : Measurable fun ω (j : ι ⊕ ℝ≥0) => Sum.elim (fun i => L ω i) (fun t => R ω t) j := by
      refine measurable_pi_iff.2 fun j => ?_
      rcases j with i | t
      · exact (measurable_pi_apply i).comp (hΦm.comp (measurable_latFam hX))
      · exact (measurable_pi_apply t).comp
          ((measurable_radFamMap r).comp (measurable_gaussFam_pi hX radPair))
    have hcoord : ∀ j : ι ⊕ ℝ≥0, ∀ᵐ ω ∂P,
        (fun ω (j : ι ⊕ ℝ≥0) =>
          Sum.elim (fun i => n2LatY X r ω (e i)) (fun t => zRadB X r t ω) j) ω j =
        (fun ω (j : ι ⊕ ℝ≥0) => Sum.elim (fun i => L ω i) (fun t => R ω t) j) ω j := by
      rintro (i | t)
      · exact hrep i
      · exact ae_zRadB_eq_radFamMap hX hr t
    have hlaw := map_eq_of_coord_ae_eq hWt.aemeasurable hWr.aemeasurable hcoord
    have e1 : (fun ω => ((fun i => n2LatY X r ω (e i)), pathOf (zRadB X r) ω)) =
        E ∘ fun ω (j : ι ⊕ ℝ≥0) =>
          Sum.elim (fun i => n2LatY X r ω (e i)) (fun t => zRadB X r t ω) j := rfl
    have e2 : (fun ω => (L ω, R ω)) =
        E ∘ fun ω (j : ι ⊕ ℝ≥0) => Sum.elim (fun i => L ω i) (fun t => R ω t) j := rfl
    rw [e1, e2, ← Measure.map_map E.measurable hWt, ← Measure.map_map E.measurable hWr]
    exact congrArg (Measure.map E) hlaw
  have hm1 : P.map (fun ω i => n2LatY X r ω (e i)) = P.map L :=
    map_eq_of_coord_ae_eq hYm.aemeasurable hLm hrep
  have hm2 : P.map (pathOf (zRadB X r)) = P.map R :=
    map_eq_of_coord_ae_eq (measurable_pathOf_zRadB hX hr).aemeasurable hRm fun t =>
      ae_zRadB_eq_radFamMap hX hr t
  rw [indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable
    (measurable_pathOf_zRadB hX hr).aemeasurable, hjoint, hm1, hm2]
  exact hprod

end Repr

/-! ## The restricted class: folded circles and bounded densities -/

section Class

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- Regularization converges at every folded circle (clause 3 of `IsRegularWith` along the regular
version). -/
theorem regAt_foldedCircle (hX : IsFreeGFFModConstH X P) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    RegAt P X (foldedCircle d s) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  filter_upwards [hG.reg, hG.raw (foldH d) (CircleFubini.foldH_mem_Hbar' d) s hs] with ω hF hraw
  rw [← fc_foldH_eq d s, ← hraw]
  have hp : (foldH d, s) ∈ Hbar ×ˢ Ioi (0 : ℝ) := ⟨CircleFubini.foldH_mem_Hbar' d, hs⟩
  have hT := (hF.2.2.tendsto_at hp).comp RegClosure.tendsto_radius_nhdsGT
  refine hT.congr fun k => ?_
  simp only [Function.comp_apply]
  exact (integral_congr_ae ((RegClosure.fc_ae_mem_Hbar _ _).mono fun u hu =>
    hF.avgReg_eq k hu)).symm

end Class

end D3Plus
end QuantumZipper
