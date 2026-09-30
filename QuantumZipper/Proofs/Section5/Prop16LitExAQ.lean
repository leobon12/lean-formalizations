import QuantumZipper.Proofs.Section5.Prop16LitExAFix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: first half of `Prop16LitExStmt`, proved (COORD-CHANGE, D98)

`Prop16Lit.ExA.prop16LitExA_holds`: a.e. under the weighted law, for every level `C`, the local
area limit of the chart field `zoomFieldLit γ C (h0 + X ω) x (ψ x)` on `B(0, r₀ x) ∩ ℍ` exists.
Palm transfer (`Prop16Lit.ae_readings_of_palm`; Duplantier–Sheffield arXiv:0808.1560 §3.3) of the
Borel event `goodExA` on the local readings, from the fixed-point statement
`prop16LitExAFixStmt_proved`; the event only reads the field near the chart domain
(`goodA_congr`, `circAgree_litRep`). Split into small lemmas. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit
namespace ExA

open Prop16Asm

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

/-- A measurable model of the raw coordinates of the chart zoom of the rebuilt field. -/
def litPhi (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) : (ℕ → ℝ) × ℝ → ℕ → ℝ :=
  (exists_measurable_coords_litRep hfam γ C).choose

/-- The rebuilt chart zoom as a measurable family of field samples. -/
def litZr (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) (q : (ℕ → ℝ) × ℝ) : FieldSample :=
  Factorization.reconstruct (litPhi hfam γ C q)

theorem measurable_litZr (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) :
    Measurable (litZr hfam γ C) :=
  Factorization.measurable_reconstruct.comp (exists_measurable_coords_litRep hfam γ C).choose_spec.1

theorem areaApprox_litZr (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) {q : (ℕ → ℝ) × ℝ}
    (hq : q.2 ∈ Ioo a b) : areaApprox γ (litZr hfam γ C q) =
      areaApprox γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2)) := by
  have h := (exists_measurable_coords_litRep hfam γ C).choose_spec.2 q hq
  rw [← Prop16Area.areaApprox_recon γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2))]
  simp only [litZr, litPhi, Prop16Area.recon, h]

/-- The Borel event on the readings. -/
def litExSet (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) : Set ((ℕ → ℝ) × ℝ) :=
  {q | q.2 ∈ Ioo a b} ∩ goodExA γ (litZr hfam γ C) (fun q => r₀ q.2)

theorem measurableSet_litExSet (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) :
    MeasurableSet (litExSet hfam γ C) :=
  (measurableSet_Ioo.preimage measurable_snd).inter
    (measurableSet_goodExA (measurable_litZr hfam γ C) (hfam.2.1.comp measurable_snd))

theorem mem_litExSet_iff (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) {q : (ℕ → ℝ) × ℝ}
    (hq : q.2 ∈ Ioo a b) : q ∈ litExSet hfam γ C ↔
      GoodA γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2)) (r₀ q.2) := by
  have e := areaApprox_litZr hfam γ C hq
  constructor
  · rintro ⟨-, h⟩
    have h' : GoodA γ (litZr hfam γ C q) (r₀ q.2) := h
    unfold GoodA at h' ⊢
    rwa [e] at h'
  · intro h
    refine ⟨hq, ?_⟩
    show GoodA γ (litZr hfam γ C q) (r₀ q.2)
    unfold GoodA at h ⊢
    rwa [e]

/-- The Palm-side membership. -/
theorem palm_mem_litExSet {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hfam : LitFamily D a b ψ r₀) (C x : ℝ) (hx : x ∈ Ioo a b) :
    ∀ᵐ ω ∂P, (palmRawCoords γ D c d h0 X (repMeas D a b) (ω, x), x) ∈ litExSet hfam γ C := by
  obtain ⟨-, -, hgeo, -, hca, hbd, -⟩ := id hdat
  filter_upwards [prop16LitExAFixStmt_proved γ D c d a b h0 P X hdat ψ r₀ hfam C x hx] with ω hω
  refine (mem_litExSet_iff hfam γ C hx).2 (goodA_congr ?_ hω)
  exact circAgree_litRep hgeo hca hbd hfam _ _ (fun i => rfl) x hx

theorem ae_mem_Ioo_prop16Q {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X) :
    ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hfin⟩ := id hdat
  have hν := prop16NuMeasStmt_of_loc
    (prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm) γ D c d a b h0 P X hdat
  exact Prop16Area.G.ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b)
    (Prop16Area.G.aemeasurable_prop16Kernel' hν hfin)
    (fun ω => Prop16Area.G.sFinite_prop16Nu γ h0 a b (X ω))
    (fun ω => Prop16Area.G.prop16Nu_compl_Ioo γ h0 a b (X ω)) (ae_of_all _ fun _ _ ht => ht)

/-- **First half of `Prop16LitExStmt`**, proved. -/
theorem prop16LitExA_holds {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hfam : LitFamily D a b ψ r₀) (C : ℝ) :
    ∀ᵐ p ∂(prop16Q γ h0 a b P X), ∃ m, IsVagueLimitOn (ball 0 (r₀ p.2) ∩ H)
      (areaApprox γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))) m := by
  obtain ⟨-, -, hgeo, -, hca, hbd, -⟩ := id hdat
  have hgood := ae_readings_of_palm hdat (measurableSet_litExSet hfam γ C)
    (fun x hx => palm_mem_litExSet hdat hfam C x hx)
  filter_upwards [ae_mem_Ioo_prop16Q hdat, hgood] with p hp1 hp2
  have h2 := (mem_litExSet_iff hfam γ C hp1).1 (hp2 hp1)
  have hloc := circAgree_litRep (γ := γ) (C := C) hgeo hca hbd hfam (ofFun h0 + X p.1)
    (rawCoords h0 X (repMeas D a b) p.1) (fun i => rfl) p.2 hp1
  exact exists_vague_of_goodA (goodA_congr (fun n k z hz hs => (hloc n k z hz hs).symm) h2)

end ExA
end Prop16Lit
end QuantumZipper
