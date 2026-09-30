import QuantumZipper.Proofs.Section5.Prop17PalmZoomMix
import QuantumZipper.Proofs.LQG.PalmNorm

/-!
# Proposition 1.7, node D4⁺ (Palm zoom): the free-field instance, split into three nodes (PALMZOOM)

Instance: `h = N_ϖ X` (`PalmNorm.normAt`), the free boundary GFF on `ℍ` normalized by a fixed
admissible probability measure `ϖ` (e.g. `foldedCircle (3 I) 1`, `E1.isNormalizer_foldedCircle`),
on the probability space of the reference construction itself. Sources:

* Palm (rooted) measure: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
  185 (2011), arXiv:0808.1560, §3.3 (p. 22): under the rooted measure, given `x`, `h` is the GFF
  plus `γ ξ^x`; here in the normalized form `PalmNorm.palm_formula_norm`
  (Palm point law `∝ rhoNorm γ 0 ϖ x dx` on `[a,b]`, Palm field `N_ϖ(ofFun (shiftFun γ 0 ϖ x) + X)`).
* Zoom at a fixed boundary point of `GFF + γ(−log|x−·|) + smooth`: Sheffield, arXiv:1012.4797,
  proof of Prop. 1.6 (p. 25); TV-local form: Duplantier–Miller–Sheffield, arXiv:1409.7055,
  Prop. 4.7–4.8 (pp. 77–79). Near `x`, `(γ/2)(neumannH x · − kPot ϖ)` is `γ(−log|x−·|)` plus a
  function smooth near `x` (D24: TV-local is appropriate).

Nodes (hypotheses, `def … : Prop`):
1. `Prop17FreeRegStmt γ ϖ a b` — regularity of the normalized free field and its boundary measure
   (a modification `h` of `N_ϖ X`, an s-finite kernel `ν`, `0 < E ν[a,b] < ∞`, a.s. good,
   atomless, positive on intervals, infinite to the right, positive zoom scales, measurable zoom
   coordinates).
2. `Prop17FreePalmIdStmt γ ϖ a b` — the Palm identity for zoom coordinates
   (from `palm_formula_norm` + a countable-coordinate representation of `zoomCoords`).
3. `Prop17FreeFixedZoomStmt γ ϖ a b` — TV-local convergence of the zoom at a fixed point `x ∈ [a,b]` of the
   Palm-shifted field (D3⁺(i) at `x`, global canonical description).

`prop17PalmRepStmt_of_free` and `prop17PalmZoomStmt_of_free` assemble them (own elementary
bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-! ## 1. The objects -/

/-- The free field normalized by `ϖ`, written as in `palm_formula_norm` (mean `0`). -/
def freeFieldN (ϖ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : FieldSample :=
  normAt ϖ (ofFun (0 : ℂ → ℝ) + X ω)

/-- The Palm-shifted normalized free field at the boundary point `x`:
`N_ϖ(X + (γ/2)(neumannH x · − kPot ϖ))`. -/
def palmFreeField (γ : ℝ) (ϖ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (x : ℝ) (ω : Ω) :
    FieldSample :=
  normAt ϖ (ofFun (shiftFun γ (0 : ℂ → ℝ) ϖ x) + X ω)

/-- The zoom coordinates of the Palm-shifted field at its own Palm point. -/
def palmZoomCoords (γ C : ℝ) (ϖ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (p : Ω × ℝ) :
    ℕ → ℝ :=
  zoomCoords γ C (palmFreeField γ ϖ X p.2) p

/-- The law of the Palm point: `rhoNorm γ 0 ϖ x dx` on `[a, b]`, normalized. -/
def palmIntensity (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : Measure ℝ :=
  (∫⁻ x in Icc a b, ENNReal.ofReal (rhoNorm γ (0 : ℂ → ℝ) ϖ x))⁻¹ •
    (volume.restrict (Icc a b)).withDensity fun x => ENNReal.ofReal (rhoNorm γ (0 : ℂ → ℝ) ϖ x)

/-! ## 2. The three nodes -/

/-- **Node 1 (regularity of the normalized free field).** -/
def Prop17FreeRegStmt (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    ∃ (h : Ω → FieldSample) (ν : Kernel Ω ℝ), (∀ᵐ ω ∂P, h ω = freeFieldN ϖ X ω) ∧
      IsSFiniteKernel ν ∧ palmMass P ν a b ≠ 0 ∧ palmMass P ν a b ≠ ∞ ∧
      (∀ᵐ ω ∂P, ν ω = qBoundaryMeasure γ (h ω) ∧ IsLQGGood γ (h ω) ∧
        (∀ t : ℝ, ν ω {t} = 0) ∧ (∀ u v : ℝ, u < v → 0 < ν ω (Ioo u v)) ∧
        (∀ x : ℝ, ν ω (Ici x) = ⊤) ∧ ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C (h ω) x)) ∧
      ∀ C : ℝ, Measurable (zoomCoords γ C h)

/-- **Node 2 (Palm identity for the zoom coordinates).** For any modification `h` of `N_ϖ X`
with boundary-measure kernel `ν` and measurable zoom coordinates, the Palm law of the zoom
coordinates is the law of the zoom coordinates of the Palm-shifted field at an independent Palm
point `x ~ palmIntensity γ ϖ a b` (through a jointly measurable version `F C` of
`palmZoomCoords`, equal to it `P`-a.s. for `ρ`-a.e. `x` and every `C`). -/
def Prop17FreePalmIdStmt (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    ∀ (h : Ω → FieldSample) (ν : Kernel Ω ℝ), IsSFiniteKernel ν →
      (∀ᵐ ω ∂P, h ω = freeFieldN ϖ X ω ∧ ν ω = qBoundaryMeasure γ (h ω)) →
      (∀ C : ℝ, Measurable (zoomCoords γ C h)) →
      ∃ F : ℝ → Ω × ℝ → (ℕ → ℝ), (∀ C, Measurable (F C)) ∧
        (∀ᵐ x ∂palmIntensity γ ϖ a b, ∀ C, ∀ᵐ ω ∂P,
          F C (ω, x) = palmZoomCoords γ C ϖ X (ω, x)) ∧
        ∀ C, (palmLaw P ν a b).map (zoomCoords γ C h) =
          (P.prod (palmIntensity γ ϖ a b)).map (F C)

/-- **Node 3 (zoom at a fixed boundary point of the Palm-shifted field).** For every reference
construction and every `x ∈ [a, b]`, the laws of the canonical zoom coordinates at `x` of
`N_ϖ(X + (γ/2)(neumannH x · − kPot ϖ))` converge TV-locally to the reference wedge law. -/
def Prop17FreeFixedZoomStmt (γ : ℝ) (ϖ : Measure ℂ) (a b : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess γ (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ x ∈ Icc a b, TVLocalTendsto atTop
      (fun C : ℝ => P'.map fun ω => palmZoomCoords γ C ϖ X (ω, x))
      (P'.map fun ω => coordsFull (refField γ X A ω)) locFull

/-! ## 3. Assembly -/

/-- **D4⁺ in mixture form from the three free-field nodes.** -/
theorem prop17PalmRepStmt_of_free {γ : ℝ} {ϖ : Measure ℂ} {a b : ℝ}
    (hReg : Prop17FreeRegStmt γ ϖ a b) (hId : Prop17FreePalmIdStmt γ ϖ a b)
    (hFix : Prop17FreeFixedZoomStmt γ ϖ a b) : Prop17PalmRepStmt γ := by
  intro Ω' _ P' X A hP' hX hA hI
  obtain ⟨h, ν, hh, hν, h0, htop, hae, hmeas⟩ := hReg Ω' _ P' X hP' hX
  have hae2 : ∀ᵐ ω ∂P', h ω = freeFieldN ϖ X ω ∧ ν ω = qBoundaryMeasure γ (h ω) := by
    filter_upwards [hh, hae] with ω h1 h2 using ⟨h1, h2.1⟩
  obtain ⟨F, hF, hFae, hrepr⟩ := hId Ω' _ P' X hP' hX h ν hν hae2 hmeas
  have := hP'
  have := hν
  set ρ := palmIntensity γ ϖ a b with hρdef
  have : SFinite ρ := by rw [hρdef]; unfold palmIntensity; infer_instance
  have hρ : IsProbabilityMeasure ρ := by
    have hQ := isProbabilityMeasure_palmLaw P' ν a b h0 htop
    have h1 := congrArg (fun m : Measure (ℕ → ℝ) => m univ) (hrepr 0)
    rw [Measure.map_apply (hmeas 0) MeasurableSet.univ, Measure.map_apply (hF 0)
      MeasurableSet.univ, preimage_univ, preimage_univ, measure_univ, ← univ_prod_univ,
      Measure.prod_prod, measure_univ, one_mul] at h1
    exact ⟨h1.symm⟩
  refine ⟨Ω', _, P', h, ν, a, b, hP', hν, h0, htop, hae, hmeas, ρ, F, hρ, hF, hrepr, ?_⟩
  have hρI : ∀ᵐ x ∂ρ, x ∈ Icc a b := by
    rw [ae_iff]
    show palmIntensity γ ϖ a b (Icc a b)ᶜ = 0
    rw [palmIntensity, Measure.smul_apply, smul_eq_mul, withDensity_apply _ measurableSet_Icc.compl,
      Measure.restrict_restrict measurableSet_Icc.compl, compl_inter_self, Measure.restrict_empty,
      lintegral_zero_measure, mul_zero]
  filter_upwards [hFae, hρI] with x hx hxI
  have heq : (fun C : ℝ => P'.map fun ω => F C (ω, x)) =
      fun C : ℝ => P'.map fun ω => palmZoomCoords γ C ϖ X (ω, x) :=
    funext fun C => Measure.map_congr (hx C)
  rw [heq]
  exact hFix Ω' _ P' X A hP' hX hA hI x hxI

/-- **D4⁺ (Palm zoom, `Prop17PalmZoomStmt γ`) from the three free-field nodes.** -/
theorem prop17PalmZoomStmt_of_free {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ} {a b : ℝ}
    (hReg : Prop17FreeRegStmt γ ϖ a b) (hId : Prop17FreePalmIdStmt γ ϖ a b)
    (hFix : Prop17FreeFixedZoomStmt γ ϖ a b) : Prop17PalmZoomStmt γ :=
  prop17PalmZoomStmt_of_rep hγ hγ2 (prop17PalmRepStmt_of_free hReg hId hFix)

end Raw
end FieldLaw
end S5
end QuantumZipper
