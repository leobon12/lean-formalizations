import QuantumZipper.Proofs.Thm18.G1ZMeasTransl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-MEAS, part 2: node B1-MEAS (`G1SideTranslMeasStmt`) from two named inputs

* **First clause** (a.s. Borel dependence on the translation): proved from the a.s. regularity of
  the side field (`G1SideRegSampleStmt`, RC2 for the uniformizer chosen in `g1SideField`) by the
  deterministic `g1zMeas_locFieldFull_translate` (G1ZMeasTransl.lean).
* **Second clause** (joint a.e.-measurability of the rerooted data): proved for any field family
  `Z₀` whose dyadic coordinates and side boundary measure are a.e.-measurable and which is a.s.
  regular with an area limit (`g1zMeas_aemeasurable_reroot`: the rerooted data are then the
  measurable proxy `canonProxy` read through the coordinates, `canonProxy_eq_canonical`,
  G3FidProxy.lean, and the quantile points `lenLeft`/`lenRight` are jointly measurable,
  G3ConcreteMaps.lean). `G1SideRerootRepStmt` asks for such a `Z₀` whose rerooted data agree a.s.
  with those of `g1SideField`.

Why a representative `Z₀`: `g1SideField` uses `uniformizer D = Classical.epsilon
(IsNormalizedUniformizer D)`, and `IsNormalizedUniformizer` fixes `0` and `∞` only, so the chosen
map is determined up to a positive factor `c(D)` which is an arbitrary (choice) function of the
domain. The coordinates `coords (g1SideField ω)` therefore need not be measurable in `ω`; only
scale-invariant quantities (the canonical, rerooted data) are. The natural `Z₀` is the side field
for the measurable selection `Ψ` of `G1PsiSel` (G1RegRepMeas.lean); the a.s. equality of the
rerooted data is the scale invariance of `canonical` under `z ↦ c z` together with the scaling
covariance of the side boundary measure (so `g1SidePt` scales by `c`).

Own argument (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- The rerooted local canonical data of a field family `Z` (the integrand of `g1RerootInt`). -/
def g1zRerootData (γ : ℝ) {Ω : Type} (Z : Ω → FieldSample) (left : Bool) (R : ℕ)
    (p : Ω × ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  locFieldFull R (canonical γ (translate (Z p.1) (g1SidePt γ left (Z p.1) p.2 : ℂ)))

/-- A translate reads the field only through its dyadic circle coordinates. -/
theorem g1zMeas_translate_reconstruct (x : FieldSample) (b : ℂ) :
    translate (reconstruct (coords x)) b = translate x b := by
  funext μ
  simp only [translate]
  rw [evalReg_congr (avgReg_reconstruct_coords x)]

/-- The measurable canonical proxy of a translate, evaluated at an s-finite measure, is jointly
measurable in (field, translation). -/
theorem g1zMeas_measurable_canonProxy_translate_apply (γ : ℝ) (ν : Measure ℂ) [SFinite ν] :
    Measurable fun q : FieldSample × ℝ => canonProxy γ (translate q.1 (q.2 : ℂ)) ν := by
  have e : (fun q : FieldSample × ℝ => canonProxy γ (translate q.1 (q.2 : ℂ)) ν) = fun q =>
      rescale (reconstruct (coords (translate q.1 (q.2 : ℂ)))) (Qc γ)
        (scaleProxy γ (translate q.1 (q.2 : ℂ))) ν := by
    funext q
    rw [Prop16Area.rescale_reconstruct_coords]
    rfl
  rw [e]
  exact Measurable.comp (g := fun r : FieldSample × ℝ => rescale r.1 (Qc γ) r.2 ν)
    (f := fun q : FieldSample × ℝ => (reconstruct (coords (translate q.1 (q.2 : ℂ))),
      scaleProxy γ (translate q.1 (q.2 : ℂ))))
    (Prop16Area.measurable_rescale_apply_joint (Qc γ) ν)
    ((measurable_reconstruct.comp IndepParams.measurable_coords_translate).prodMk
      (g1zMeas_measurable_scaleProxy_translate γ))

/-- **B1-MEAS, second clause, for a measurable representative**: if the coordinates and the side
boundary measure of `Z` are a.e.-measurable and `Z` is a.s. regular with an area limit, the
rerooted local canonical data are a.e.-measurable jointly in `(ω, ℓ)`. -/
theorem g1zMeas_aemeasurable_reroot (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → FieldSample} (left : Bool) (R : ℕ)
    (hc : AEMeasurable (fun ω => coords (Z ω)) P)
    (hν : AEMeasurable (fun ω => g1SideNu γ left (Z ω)) P)
    (hreg : ∀ᵐ ω ∂P, IsRegularSample (Z ω) ∧ G1ZAreaEx γ (Z ω)) :
    AEMeasurable (g1zRerootData γ Z left R) (P.prod volume) := by
  have hm : AEMeasurable (fun p : Ω × ℝ => (g1SideNu γ left (Z p.1), p.2)) (P.prod volume) :=
    hν.comp_fst.prodMk measurable_snd.aemeasurable
  have hpt : AEMeasurable (fun p : Ω × ℝ => g1SidePt γ left (Z p.1) p.2) (P.prod volume) := by
    cases left
    · have e : (fun p : Ω × ℝ => g1SidePt γ false (Z p.1) p.2) =
          (fun m : Measure ℝ × ℝ => lenRight m.1 m.2) ∘
            (fun p : Ω × ℝ => (g1SideNu γ false (Z p.1), p.2)) := by
        funext p; simp [g1SidePt]
      rw [e]
      exact measurable_lenRight.comp_aemeasurable hm
    · have e : (fun p : Ω × ℝ => g1SidePt γ true (Z p.1) p.2) =
          (fun m : Measure ℝ × ℝ => lenLeft m.1 m.2) ∘
            (fun p : Ω × ℝ => (g1SideNu γ true (Z p.1), p.2)) := by
        funext p; simp [g1SidePt]
      rw [e]
      exact measurable_lenLeft.comp_aemeasurable hm
  have hΨ : Measurable fun q : (ℕ → ℝ) × ℝ =>
      locFieldFull R (canonProxy γ (translate (reconstruct q.1) (q.2 : ℂ))) :=
    g1zMeas_measurable_locFieldFull (fun ν _ =>
      Measurable.comp (g := fun r : FieldSample × ℝ => canonProxy γ (translate r.1 (r.2 : ℂ)) ν)
        (f := fun q : (ℕ → ℝ) × ℝ => (reconstruct q.1, q.2))
        (g1zMeas_measurable_canonProxy_translate_apply γ ν)
        ((measurable_reconstruct.comp measurable_fst).prodMk measurable_snd)) R
  have hJ := hΨ.comp_aemeasurable (hc.comp_fst.prodMk hpt)
  refine hJ.congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hreg] with p hp
  simp only [g1zRerootData, Function.comp_apply]
  rw [g1zMeas_translate_reconstruct,
    canonProxy_eq_canonical ((g1zAreaEx_translate_iff hp.1 _).2 hp.2)]

/-! ## The named inputs and the node -/

/-- **Input (RC2 for the chosen uniformizer)**: a.s. the side field is a regular sample. -/
def G1SideRegSampleStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ᵐ ω ∂P, IsRegularSample (g1SideField γ B Y left ω)

/-- **Input (measurable representative of the rerooted side data)**: a field family `Z₀` with
a.e.-measurable coordinates and side boundary measure, a.s. regular with an area limit, whose
rerooted local canonical data agree a.s. (for all `ℓ`) with those of the side field. -/
def G1SideRerootRepStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∃ Z₀ : Ω → FieldSample, AEMeasurable (fun ω => coords (Z₀ ω)) P ∧
      AEMeasurable (fun ω => g1SideNu γ left (Z₀ ω)) P ∧
      (∀ᵐ ω ∂P, IsRegularSample (Z₀ ω) ∧ G1ZAreaEx γ (Z₀ ω)) ∧
      ∀ R : ℕ, ∀ᵐ ω ∂P, ∀ ℓ : ℝ,
        g1zRerootData γ (g1SideField γ B Y left) left R (ω, ℓ) = g1zRerootData γ Z₀ left R (ω, ℓ)

/-- **Node B1-MEAS from its inputs.** -/
theorem g1SideTranslMeasStmt_of (hReg : G1SideRegSampleStmt) (hRep : G1SideRerootRepStmt) :
    G1SideTranslMeasStmt := by
  intro γ Ω _ P _ B Y hS hIn left R
  refine ⟨?_, ?_⟩
  · filter_upwards [hReg γ P B Y hS hIn left] with ω hω
    exact g1zMeas_locFieldFull_translate γ hω R
  · obtain ⟨Z₀, hc, hν, hr, heq⟩ := hRep γ P B Y hS hIn left
    have hJ := g1zMeas_aemeasurable_reroot γ left R hc hν hr
    refine hJ.congr ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (heq R)] with p hp
    exact (hp p.2).symm

end Thm18Asm
end QuantumZipper
