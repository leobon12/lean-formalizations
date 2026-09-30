import QuantumZipper.Proofs.Thm18.G2PalmIdCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2-PALMID, part 3: the Palm node on the `x` side, `G2RootXPalmIdStmt γ`, PROVED

`g2RootXPalmIdStmt_holds : 0 < γ → γ < 2 → G2RootXPalmIdStmt γ`.

Source: the rooted-measure (Palm) formula of Duplantier–Sheffield, *Liouville quantum gravity
and KPZ*, Invent. Math. 185 (2011), arXiv:0808.1560, §3.3 (p. 22), in the normalized form
`E1.palm_formula_Ioo` (via `pid_palm`), as used in Sheffield, arXiv:1012.4797, proof of
Prop. 5.5 (p. 65). Route (own bookkeeping):
1. the outside event `G'` depends on countably many pairs `J` (`exists_countable_dep`), which are
   appended to the dyadic coordinates (`pidMu`);
2. pathwise, the rooted event is a measurable set `pidSetX` of the coordinates of `Z = N_S X₀`
   (zoom law through `reconstruct`, cut length through `cutL`), exact on fine samples;
3. `ν_h = |t| ν_Z` (`lintegral_hν_eq`), the Palm formula for `ν_Z` with weight `|t|`, fineness of
   the Palm field for a.e. `x` (`ae_pidFine_palm`), and `ρ_h(x) = |x| ρ_0(x)` (`rhoX_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Factorization (coords reconstruct)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

theorem indicator_one_eq_of_iff {α β : Type*} {S : Set α} {T : Set β} {a : α} {b : β}
    (h : a ∈ S ↔ b ∈ T) : S.indicator (1 : α → ℝ≥0∞) a = T.indicator 1 b := by
  by_cases hb : b ∈ T
  · rw [indicator_of_mem (h.2 hb), indicator_of_mem hb]; rfl
  · rw [indicator_of_notMem (mt h.1 hb), indicator_of_notMem hb]

section XSide

variable (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ)
  (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ))

/-- The rooted event read at a sample `V` and a point `x`. -/
def pidEvX (x : ℝ) (V : FieldSample) : Prop :=
  zoomLaw γ i.C (pidNf γ V) x ∈ s ∧ |x - i.t₁| + m < i.r₁ ∧
    (outMap i V, (qBoundaryMeasure γ (pidNf γ V) (Icc (x + κ) 0)).toReal) ∈ G'

/-- The same event in the coordinates. -/
def pidSetX (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) : Set ((ℕ → ℝ) × ℝ) :=
  {p | zoomLaw γ i.C (reconstruct (pidDN γ p.1)) p.2 ∈ s ∧ |p.2 - i.t₁| + m < i.r₁ ∧
    (pidR J e (pidD p.1), (cutL (bdryMc γ (pidDN γ p.1)) (p.2 + κ)).toReal) ∈ G'}

end XSide

theorem measurableSet_pidSetX (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m κ : ℝ) {G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)} (hG' : MeasurableSet G')
    (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) :
    MeasurableSet (pidSetX γ i s m κ G' J e) := by
  have hdn : Measurable fun p : (ℕ → ℝ) × ℝ => pidDN γ p.1 := (measurable_pidDN γ).comp measurable_fst
  refine (((measurable_zoomLaw γ i.C).comp
    ((Factorization.measurable_reconstruct.comp hdn).prodMk measurable_snd)) hs).inter
    ((measurableSet_lt (Measurable.add_const (continuous_abs.measurable.comp
      (measurable_snd.sub_const i.t₁)) m) measurable_const).inter ?_)
  exact (((measurable_pidR J e).comp (measurable_pidD.comp measurable_fst)).prodMk
    (measurable_cutL ((measurable_bdryMc γ).comp hdn) (measurable_snd.add_const κ)).ennreal_toReal)
    hG'

theorem mem_pidSetX_iff (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ)
    {G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)} {J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)}
    {e : J → ℕ} (he : Function.Injective e)
    (hdep : ∀ f g : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ, (∀ j ∈ J, f j = g j) → ∀ b : ℝ,
      ((f, b) ∈ G' ↔ (g, b) ∈ G'))
    {V : FieldSample} (hV : pidFine γ (coords (pidNf γ V))) (x : ℝ) :
    (pidC (pidA J e (outPr i)) (pidB J e (outPr i)) V, x) ∈ pidSetX γ i s m κ G' J e ↔
      pidEvX γ i s m κ G' x V := by
  obtain ⟨hc, hf⟩ := (pidFine_coords_iff γ _).1 hV
  have hfin := qBM_Icc_ne_top_of_fine hf
  simp only [pidSetX, pidEvX, mem_setOf_eq]
  rw [← coords_pidNf, zoomLaw_reconstruct_coords, bdryMc_coords_eq, if_pos hc,
    cutL_eq (fun u => hfin u 0)]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact hdep _ _ (fun p hp => (outMap_eq_pidR i he V p hp).symm) _

/-- **Node P, `x` side (`G2RootXPalmIdStmt γ`), proved for `0 < γ < 2`.** -/
theorem g2RootXPalmIdStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootXPalmIdStmt γ := by
  intro i s hs m κ _hm _hκ G' hG'
  obtain ⟨J, hJ, hdep⟩ := exists_countable_dep hG'
  have : Countable J := hJ
  obtain ⟨e, he⟩ := Countable.exists_injective_nat J
  set A := pidA J e (outPr i) with hAdef
  set B := pidB J e (outPr i) with hBdef
  have hA : ∀ n, IsAdmissibleH (A n) := pidA_adm (fun p => p.2.1)
  have hB : ∀ n, IsAdmissibleH (B n) := pidB_adm (fun p => p.2.2.1)
  set E := pidSetX γ i s m κ G' J e with hEdef
  have hE : MeasurableSet E := measurableSet_pidSetX γ i hs m κ hG' J e
  have hEi : Measurable (E.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞)) := measurable_one.indicator hE
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c x => ENNReal.ofReal |x| * E.indicator 1 (c, x) with hφdef
  have hφ : Measurable (Function.uncurry φ) :=
    ((continuous_abs.measurable.comp measurable_snd).ennreal_ofReal).mul hEi
  have hδ : 0 < i.δ := i.hη.trans i.hηδ
  have hab : Icc (-i.δ) 0 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by
    intro t ht
    simp only [Nat.cast_one, mem_Icc] at ht ⊢
    constructor <;> linarith [i.hδ, ht.1, ht.2]
  -- the left side, pathwise
  have hL : ∀ᵐ ω ∂gffBase.P,
      ∫⁻ x in Icc (-i.δ) 0, (g3RootEvXc γ i s m κ (outEv i G')).indicator 1
        (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∂(g3Hν γ ω) =
      ∫⁻ x in Ioo (-i.δ) 0, φ (pidC A B (X₀ ω)) x ∂(g3Zν γ ω) := by
    filter_upwards [ae_pidFine_free hγ hγ2, ae_g3Hν_eq hγ hγ2,
      G3Fid.ae_normField_good gffBase.gff hγ hγ2,
      S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS] with ω hfine hH hg hZ
    have hpt : ∀ x, (g3RootEvXc γ i s m κ (outEv i G')).indicator 1
        (ω, (g3Hν γ ω (Icc x 0)).toReal, x) = E.indicator 1 (pidC A B (X₀ ω), x) := fun x =>
      indicator_one_eq_of_iff ((mem_pidSetX_iff γ i s m κ he hdep hfine x).symm)
    simp only [hpt]
    exact lintegral_hν_eq hH (hZ.2.1 0) (hg.2.2 _) (hg.2.2 _)
      (hEi.comp (measurable_const.prodMk measurable_id))
  -- the right side, for a.e. `x`
  have hkey : ∀ᵐ x ∂(volume.restrict (Ioo (-i.δ) 0)),
      ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P =
      ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEv γ i s m κ G' x) := by
    filter_upwards [ae_pidFine_palm hγ hγ2 hA hB hab, ae_restrict_mem measurableSet_Ioo]
      with x hx hxI
    have hmx : Measurable fun ω => pidC A B (xPalm γ x ω) := measurable_pidC_xPalm γ A B x
    have hpre : MeasurableSet ((fun ω => (pidC A B (xPalm γ x ω), x)) ⁻¹' E) :=
      (hmx.prodMk measurable_const) hE
    have hint : ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P =
        ENNReal.ofReal |x| * gffBase.P (g3RootXPalmEv γ i s m κ G' x) := by
      simp only [hφdef]
      rw [lintegral_const_mul (ENNReal.ofReal |x|)
        (f := fun ω => E.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞) (pidC A B (xPalm γ x ω), x))
        (hEi.comp (hmx.prodMk measurable_const))]
      congr 1
      have e1 : (fun ω => E.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞) (pidC A B (xPalm γ x ω), x)) =
          ((fun ω => (pidC A B (xPalm γ x ω), x)) ⁻¹' E).indicator 1 := by
        funext ω
        exact indicator_one_eq_of_iff Iff.rfl
      rw [e1, lintegral_indicator_one hpre]
      refine measure_congr ?_
      filter_upwards [hx] with ω hω
      exact propext (mem_pidSetX_iff γ i s m κ he hdep (by rw [coords_pidNf]; exact hω) x)
    have hx0 : x ≠ 0 := hxI.2.ne
    rw [hint, rhoX_eq hγ hx0, ENNReal.ofReal_mul (abs_nonneg x)]
    ring
  have hmR : Measurable fun x => ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
      ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P :=
    (E1.measurable_rhoNorm measurable_const refS).ennreal_ofReal.mul (measurable_pidK γ hA hB hφ)
  refine ⟨?_, ?_⟩
  · unfold g3RootInt
    rw [lintegral_congr_ae hL, pid_palm hγ hγ2 hA hB hab hφ, lintegral_congr_ae hkey,
      Measure.restrict_congr_set Ioo_ae_eq_Icc]
  · rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hmR.aemeasurable.congr hkey

end Thm18Asm
end QuantumZipper
