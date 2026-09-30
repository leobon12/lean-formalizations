import QuantumZipper.Proofs.Section5.Prop17PalmZoomScale
import QuantumZipper.Proofs.LQG.WedgeMeasurable
import QuantumZipper.Proofs.Thm18.G3ConcreteMaps
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.Proofs.Section5.Prop17Field

/-!
# Proposition 1.7, node D4⁺ (Palm zoom), node A: a measurable modification (PALM-AB)

`Prop17FreeModStmt γ ϖ` (node A of `handoff/PROP17-STAT.md`, PALMZOOM section) is proved here,
unconditionally for `0 < γ < 2` (`prop17FreeModStmt_holds`).

Route (countable-coordinate representation, as in `Thm18Asm.measurable_zoomLaw` and
`WedgeMeas.aemeasurable_dataFull_canonical`):

* `zoomRep γ C (c, x)`: a jointly measurable function of the raw dyadic coordinates `c` and the
  zoom point `x` (reconstruct, zoom, measurable scale `scaleG`, rescale, read `coordsFull`);
* `zoomCoords_eq_zoomRep`: on a good field `y`,
  `coordsFull (canonical γ (zoomField γ C y x)) = zoomRep γ C (coords y, x)` for all `C, x`;
* the modification: `h := N_ϖ X` on the measurable set where it is good, a fixed good sample
  elsewhere.

Own elementary arguments (measurability bookkeeping; AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull PalmNorm

/-- Raw dyadic coordinates of the zoomed field, as a function of the raw coordinates. -/
def zoomRaw (γ C : ℝ) (q : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  coords (zoomField γ C (reconstruct q.1) q.2)

/-- Measurable representation of the zoom coordinates through the raw coordinates. -/
def zoomRep (γ C : ℝ) (q : (ℕ → ℝ) × ℝ) : ℕ → ℝ :=
  coordsFull (resc (Qc γ) (zoomRaw γ C q, scaleG γ (zoomRaw γ C q)))

theorem measurable_zoomRaw (γ C : ℝ) : Measurable (zoomRaw γ C) :=
  Measurable.comp (g := fun q : FieldSample × ℝ => coords (zoomField γ C q.1 q.2))
    (f := fun q : (ℕ → ℝ) × ℝ => (reconstruct q.1, q.2))
    (Thm18Asm.measurable_coords_zoomField_joint γ C)
    ((measurable_reconstruct.comp measurable_fst).prodMk measurable_snd)

theorem measurable_zoomRep (γ C : ℝ) : Measurable (zoomRep γ C) := by
  have h := measurable_zoomRaw γ C
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_resc_apply (Qc γ) _).comp (h.prodMk ((measurable_scaleG γ).comp h))

theorem zoomField_reconstruct_coords (γ C : ℝ) (y : FieldSample) (x : ℝ) :
    zoomField γ C (reconstruct (coords y)) x = zoomField γ C y x := by
  have : translate (reconstruct (coords y)) (x : ℂ) = translate y (x : ℂ) := by
    funext μ
    simp only [translate]
    rw [evalReg_congr (avgReg_reconstruct_coords y)]
  simp only [zoomField, this]

/-- **Representation.** On a good field the zoom coordinates are `zoomRep` of the raw
coordinates. -/
theorem zoomCoords_eq_zoomRep {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) (C x : ℝ) :
    coordsFull (canonical γ (zoomField γ C y x)) = zoomRep γ C (coords y, x) := by
  have hz : zoomRaw γ C (coords y, x) = coords (zoomField γ C y x) := by
    simp only [zoomRaw, zoomField_reconstruct_coords]
  rw [zoomRep, hz, scaleG_coords (FieldShift.isLQGGood_zoomField hy C x), ← canonical_eq_resc]

/-- Zoom coordinates of an everywhere-good measurable field are measurable. -/
theorem measurable_zoomCoords_of_good {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ}
    {h : Ω → FieldSample} (hm : Measurable h) (hg : ∀ ω, IsLQGGood γ (h ω)) (C : ℝ) :
    Measurable (zoomCoords γ C h) := by
  have e : zoomCoords γ C h = fun p => zoomRep γ C (coords (h p.1), p.2) := by
    funext p
    exact zoomCoords_eq_zoomRep (hg p.1) C p.2
  rw [e]
  exact (measurable_zoomRep γ C).comp
    (((measurable_coords.comp hm).comp measurable_fst).prodMk measurable_snd)

theorem measurable_freeFieldN {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (ϖ : Measure ℂ) :
    Measurable (freeFieldN ϖ X) := by
  refine measurable_pi_iff.2 fun μ => ?_
  have e : (fun ω => freeFieldN ϖ X ω μ) = fun ω => X ω μ + -(X ω ϖ) * (μ univ).toReal := by
    funext ω
    rw [freeFieldN_eq_addConst]
    rfl
  rw [e]
  exact (hX.measurable_coord μ).add ((hX.measurable_coord ϖ).neg.mul measurable_const)

/-- **Node A (`Prop17FreeModStmt`), proved.** -/
theorem prop17FreeModStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (ϖ : Measure ℂ) :
    Prop17FreeModStmt γ ϖ := by
  intro Ω _ P X hP hX
  have hae : ∀ᵐ ω ∂P, IsLQGGood γ (freeFieldN ϖ X ω) :=
    (ae_freeFieldN_bdry hX hγ hγ2 ϖ).mono fun ω h => h.1
  obtain ⟨ω₀, hω₀⟩ := hae.exists
  have hmN := measurable_freeFieldN hX ϖ
  set G : Set Ω := {ω | IsLQGGood γ (freeFieldN ϖ X ω)} with hGdef
  have hG : MeasurableSet G := hmN (GoodMeas.measurableSet_isLQGGood γ)
  classical
  refine ⟨fun ω => if ω ∈ G then freeFieldN ϖ X ω else freeFieldN ϖ X ω₀, ?_, fun C => ?_⟩
  · filter_upwards [hae] with ω hω
    simp only [hGdef, Set.mem_ofPred_eq, hω, ite_true]
  · refine measurable_zoomCoords_of_good (Measurable.ite hG hmN measurable_const) (fun ω => ?_) C
    split_ifs with hω
    · exact hω
    · exact hω₀

end Raw
end FieldLaw
end S5
end QuantumZipper
