import QuantumZipper.Proofs.Thm18.G3ZqG2Palm
import QuantumZipper.Proofs.Thm18.G2PalmIdR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 engine with an abstract zoom: the Palm identities (node P, both sides)

Generalized copy (D92) of `G2PalmIdX.lean` and `G2PalmIdR.lean`: the Palm identities
`G2RootXPalmIdStmtZ Z γ`, `G2RootRPalmIdStmtZ Z γ` for an abstract zoom `Z`. The original proofs
use exactly two properties of the zoom `zoomLaw γ C`:

* joint measurability `Measurable fun q : FieldSample × ℝ => Z C q.1 q.2` (`measurable_zoomLaw`),
  for the measurability of the coordinate event `pidSetXZ`/`pidSetRZ`;
* factorization through the dyadic coordinates,
  `Z C (reconstruct (coords y)) x = Z C y x` (`zoomLaw_reconstruct_coords`), to read the rooted
  event pathwise from the coordinates.

They are the hypotheses `hZm`, `hZc` below; everything else (countable dependence, coordinate
Palm formula `pid_palm`, fineness, `rhoX_eq`, `lintegral_hν_eq`) is reused.

Sources: Duplantier–Sheffield, arXiv:0808.1560, §3.3 (p. 22), as used in Sheffield,
arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66. Own bookkeeping copied from the originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Factorization (coords reconstruct)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

variable {Z : ℝ → FieldSample → ℝ → LawD}

section XSide

variable (Z) (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ)
  (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ))

/-- The rooted event read at a sample `V` and a point `x`. -/
def pidEvXZ (x : ℝ) (V : FieldSample) : Prop :=
  Z i.C (pidNf γ V) x ∈ s ∧ |x - i.t₁| + m < i.r₁ ∧
    (outMap i V, (qBoundaryMeasure γ (pidNf γ V) (Icc (x + κ) 0)).toReal) ∈ G'

/-- The same event in the coordinates. -/
def pidSetXZ (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) : Set ((ℕ → ℝ) × ℝ) :=
  {p | Z i.C (reconstruct (pidDN γ p.1)) p.2 ∈ s ∧ |p.2 - i.t₁| + m < i.r₁ ∧
    (pidR J e (pidD p.1), (cutL (bdryMc γ (pidDN γ p.1)) (p.2 + κ)).toReal) ∈ G'}

end XSide

theorem measurableSet_pidSetXZ
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {s : Set LawD} (hs : MeasurableSet s)
    (m κ : ℝ) {G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)} (hG' : MeasurableSet G')
    (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) :
    MeasurableSet (pidSetXZ Z γ i s m κ G' J e) := by
  have hdn : Measurable fun p : (ℕ → ℝ) × ℝ => pidDN γ p.1 := (measurable_pidDN γ).comp measurable_fst
  refine (((hZm i.C).comp
    ((Factorization.measurable_reconstruct.comp hdn).prodMk measurable_snd)) hs).inter
    ((measurableSet_lt (Measurable.add_const (continuous_abs.measurable.comp
      (measurable_snd.sub_const i.t₁)) m) measurable_const).inter ?_)
  exact (((measurable_pidR J e).comp (measurable_pidD.comp measurable_fst)).prodMk
    (measurable_cutL ((measurable_bdryMc γ).comp hdn) (measurable_snd.add_const κ)).ennreal_toReal)
    hG'

theorem mem_pidSetXZ_iff
    (hZc : ∀ (C : ℝ) (y : FieldSample) (x : ℝ), Z C (reconstruct (coords y)) x = Z C y x)
    (γ : ℝ) (i : G3Idx) (s : Set LawD) (m κ : ℝ)
    {G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)} {J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)}
    {e : J → ℕ} (he : Function.Injective e)
    (hdep : ∀ f g : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ, (∀ j ∈ J, f j = g j) → ∀ b : ℝ,
      ((f, b) ∈ G' ↔ (g, b) ∈ G'))
    {V : FieldSample} (hV : pidFine γ (coords (pidNf γ V))) (x : ℝ) :
    (pidC (pidA J e (outPr i)) (pidB J e (outPr i)) V, x) ∈ pidSetXZ Z γ i s m κ G' J e ↔
      pidEvXZ Z γ i s m κ G' x V := by
  obtain ⟨hc, hf⟩ := (pidFine_coords_iff γ _).1 hV
  have hfin := qBM_Icc_ne_top_of_fine hf
  simp only [pidSetXZ, pidEvXZ, mem_setOf_eq]
  rw [← coords_pidNf, hZc, bdryMc_coords_eq, if_pos hc,
    cutL_eq (fun u => hfin u 0)]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact hdep _ _ (fun p hp => (outMap_eq_pidR i he V p hp).symm) _

/-- **Node P, `x` side (`G2RootXPalmIdStmtZ Z γ`), proved for `0 < γ < 2`.** -/
theorem g2RootXPalmIdStmtZ_holds
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZc : ∀ (C : ℝ) (y : FieldSample) (x : ℝ),
      Z C (reconstruct (coords y)) x = Z C y x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootXPalmIdStmtZ Z γ := by
  intro i s hs m κ _hm _hκ G' hG'
  obtain ⟨J, hJ, hdep⟩ := exists_countable_dep hG'
  have : Countable J := hJ
  obtain ⟨e, he⟩ := Countable.exists_injective_nat J
  set A := pidA J e (outPr i) with hAdef
  set B := pidB J e (outPr i) with hBdef
  have hA : ∀ n, IsAdmissibleH (A n) := pidA_adm (fun p => p.2.1)
  have hB : ∀ n, IsAdmissibleH (B n) := pidB_adm (fun p => p.2.2.1)
  set E := pidSetXZ Z γ i s m κ G' J e with hEdef
  have hE : MeasurableSet E := measurableSet_pidSetXZ hZm γ i hs m κ hG' J e
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
      ∫⁻ x in Icc (-i.δ) 0, (g3RootEvXcZ Z γ i s m κ (outEv i G')).indicator 1
        (ω, (g3Hν γ ω (Icc x 0)).toReal, x) ∂(g3Hν γ ω) =
      ∫⁻ x in Ioo (-i.δ) 0, φ (pidC A B (X₀ ω)) x ∂(g3Zν γ ω) := by
    filter_upwards [ae_pidFine_free hγ hγ2, ae_g3Hν_eq hγ hγ2,
      G3Fid.ae_normField_good gffBase.gff hγ hγ2,
      S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS] with ω hfine hH hg hZ
    have hpt : ∀ x, (g3RootEvXcZ Z γ i s m κ (outEv i G')).indicator 1
        (ω, (g3Hν γ ω (Icc x 0)).toReal, x) = E.indicator 1 (pidC A B (X₀ ω), x) := fun x =>
      indicator_one_eq_of_iff ((mem_pidSetXZ_iff hZc γ i s m κ he hdep hfine x).symm)
    simp only [hpt]
    exact lintegral_hν_eq hH (hZ.2.1 0) (hg.2.2 _) (hg.2.2 _)
      (hEi.comp (measurable_const.prodMk measurable_id))
  -- the right side, for a.e. `x`
  have hkey : ∀ᵐ x ∂(volume.restrict (Ioo (-i.δ) 0)),
      ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS x) *
        ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P =
      ENNReal.ofReal (rhoX γ x) * gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x) := by
    filter_upwards [ae_pidFine_palm hγ hγ2 hA hB hab, ae_restrict_mem measurableSet_Ioo]
      with x hx hxI
    have hmx : Measurable fun ω => pidC A B (xPalm γ x ω) := measurable_pidC_xPalm γ A B x
    have hpre : MeasurableSet ((fun ω => (pidC A B (xPalm γ x ω), x)) ⁻¹' E) :=
      (hmx.prodMk measurable_const) hE
    have hint : ∫⁻ ω, φ (pidC A B (xPalm γ x ω)) x ∂gffBase.P =
        ENNReal.ofReal |x| * gffBase.P (g3RootXPalmEvZ Z γ i s m κ G' x) := by
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
      exact propext (mem_pidSetXZ_iff hZc γ i s m κ he hdep (by rw [coords_pidNf]; exact hω) x)
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

section RSide

variable (Z) (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G'' : Set (CondR i))

/-- The rooted event at `R` read at a sample `V` and a point `y`. -/
def pidEvRZ (y : ℝ) (V : FieldSample) : Prop :=
  Z i.C (pidNf γ V) y ∈ t ∧ |y - i.t₂| + m < i.r₂ ∧
    (outMap i V, (qBoundaryMeasure γ (pidNf γ V) (Icc 0 (y - κ))).toReal, pidMassV γ i V) ∈ G''

/-- The same event in the coordinates. -/
def pidSetRZ (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) : Set ((ℕ → ℝ) × ℝ) :=
  {p | Z i.C (reconstruct (pidDN γ p.1)) p.2 ∈ t ∧ |p.2 - i.t₂| + m < i.r₂ ∧
    (pidR J e (pidD p.1), (cutR (bdryMc γ (pidDN γ p.1)) (p.2 - κ)).toReal, pidMassC γ i p.1)
      ∈ G''}

end RSide

theorem measurableSet_pidSetRZ
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m κ : ℝ) {G'' : Set (CondR i)} (hG'' : MeasurableSet G'')
    (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) :
    MeasurableSet (pidSetRZ Z γ i t m κ G'' J e) := by
  have hdn : Measurable fun p : (ℕ → ℝ) × ℝ => pidDN γ p.1 := (measurable_pidDN γ).comp measurable_fst
  refine (((hZm i.C).comp
    ((Factorization.measurable_reconstruct.comp hdn).prodMk measurable_snd)) ht).inter
    ((measurableSet_lt (Measurable.add_const (continuous_abs.measurable.comp
      (measurable_snd.sub_const i.t₂)) m) measurable_const).inter ?_)
  exact (((measurable_pidR J e).comp (measurable_pidD.comp measurable_fst)).prodMk
    ((measurable_cutR ((measurable_bdryMc γ).comp hdn) (measurable_snd.sub_const κ)).ennreal_toReal.prodMk
      ((measurable_pidMassC γ i).comp measurable_fst))) hG''

theorem mem_pidSetRZ_iff
    (hZc : ∀ (C : ℝ) (y : FieldSample) (x : ℝ), Z C (reconstruct (coords y)) x = Z C y x)
    (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) {G'' : Set (CondR i)}
    {J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)} {e : J → ℕ} (he : Function.Injective e)
    (hdep : ∀ f g : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ, (∀ j ∈ J, f j = g j) → ∀ b : ℝ × ℝ≥0∞,
      ((f, b) ∈ G'' ↔ (g, b) ∈ G''))
    {V : FieldSample} (hV : pidFine γ (coords (pidNf γ V))) (y : ℝ) :
    (pidC (pidA J e (outPr i)) (pidB J e (outPr i)) V, y) ∈ pidSetRZ Z γ i t m κ G'' J e ↔
      pidEvRZ Z γ i t m κ G'' y V := by
  obtain ⟨hc, hf⟩ := (pidFine_coords_iff γ _).1 hV
  have hfin := qBM_Icc_ne_top_of_fine hf
  simp only [pidSetRZ, pidEvRZ, mem_setOf_eq]
  rw [pidMassV_eq γ i (pidA J e (outPr i)) (pidB J e (outPr i)) V, ← coords_pidNf,
    hZc, bdryMc_coords_eq, if_pos hc, cutR_eq (fun u => hfin 0 u)]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact hdep _ _ (fun p hp => (outMap_eq_pidR i he V p hp).symm) _

/-- **Node P, `R` side (`G2RootRPalmIdStmtZ Z γ`), proved for `0 < γ < 2`.** -/
theorem g2RootRPalmIdStmtZ_holds
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZc : ∀ (C : ℝ) (y : FieldSample) (x : ℝ),
      Z C (reconstruct (coords y)) x = Z C y x)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootRPalmIdStmtZ Z γ := by
  intro i t ht m κ _hm _hκ G'' hG''
  obtain ⟨J, hJ, hdep⟩ := exists_countable_dep (ι := OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)
    (β := ℝ × ℝ≥0∞) hG''
  have : Countable J := hJ
  obtain ⟨e, he⟩ := Countable.exists_injective_nat J
  set A := pidA J e (outPr i) with hAdef
  set B := pidB J e (outPr i) with hBdef
  have hA : ∀ n, IsAdmissibleH (A n) := pidA_adm (fun p => p.2.1)
  have hB : ∀ n, IsAdmissibleH (B n) := pidB_adm (fun p => p.2.2.1)
  set E := pidSetRZ Z γ i t m κ G'' J e with hEdef
  have hE : MeasurableSet E := measurableSet_pidSetRZ hZm γ i ht m κ hG'' J e
  have hEi : Measurable (E.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞)) := measurable_one.indicator hE
  set φ : (ℕ → ℝ) → ℝ → ℝ≥0∞ := fun c x => ENNReal.ofReal |x| * E.indicator 1 (c, x) with hφdef
  have hφ : Measurable (Function.uncurry φ) :=
    ((continuous_abs.measurable.comp measurable_snd).ennreal_ofReal).mul hEi
  have hb1 : i.t₂ + i.r₂ ≤ 1 := by
    have h := G3Idx.inUnit₂ i
    have ht2 : 0 < i.t₂ := by unfold G3Idx.t₂; linarith [i.hη]
    rwa [abs_of_pos ht2] at h
  have hab : Icc 0 (i.t₂ + i.r₂) ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by
    intro u hu
    simp only [Nat.cast_one, mem_Icc] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hL : ∀ᵐ ω ∂gffBase.P,
      ∫⁻ y in Icc 0 (i.t₂ + i.r₂), (g3RootEvRccZ Z γ i t m κ G'').indicator 1
        (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∂(g3Hν γ ω) =
      ∫⁻ y in Ioo 0 (i.t₂ + i.r₂), φ (pidC A B (X₀ ω)) y ∂(g3Zν γ ω) := by
    filter_upwards [ae_pidFine_free hγ hγ2, ae_g3Hν_eq hγ hγ2,
      G3Fid.ae_normField_good gffBase.gff hγ hγ2,
      S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS] with ω hfine hH hg hZ
    have hpt : ∀ y, (g3RootEvRccZ Z γ i t m κ G'').indicator 1
        (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) = E.indicator 1 (pidC A B (X₀ ω), y) := fun y =>
      indicator_one_eq_of_iff ((mem_pidSetRZ_iff hZc γ i t m κ he hdep hfine y).symm)
    simp only [hpt]
    exact lintegral_hν_eq hH (hZ.2.1 0) (hg.2.2 _) (hg.2.2 _)
      (hEi.comp (measurable_const.prodMk measurable_id))
  have hkey : ∀ᵐ y ∂(volume.restrict (Ioo 0 (i.t₂ + i.r₂))),
      ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS y) *
        ∫⁻ ω, φ (pidC A B (xPalm γ y ω)) y ∂gffBase.P =
      ENNReal.ofReal (rhoX γ y) * gffBase.P (g3PalmEvRZ Z γ i t m κ G'' y) := by
    filter_upwards [ae_pidFine_palm hγ hγ2 hA hB hab, ae_restrict_mem measurableSet_Ioo]
      with y hy hyI
    have hmy : Measurable fun ω => pidC A B (xPalm γ y ω) := measurable_pidC_xPalm γ A B y
    have hpre : MeasurableSet ((fun ω => (pidC A B (xPalm γ y ω), y)) ⁻¹' E) :=
      (hmy.prodMk measurable_const) hE
    have hint : ∫⁻ ω, φ (pidC A B (xPalm γ y ω)) y ∂gffBase.P =
        ENNReal.ofReal |y| * gffBase.P (g3PalmEvRZ Z γ i t m κ G'' y) := by
      simp only [hφdef]
      rw [lintegral_const_mul (ENNReal.ofReal |y|)
        (f := fun ω => E.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞) (pidC A B (xPalm γ y ω), y))
        (hEi.comp (hmy.prodMk measurable_const))]
      congr 1
      have e1 : (fun ω => E.indicator (1 : (ℕ → ℝ) × ℝ → ℝ≥0∞) (pidC A B (xPalm γ y ω), y)) =
          ((fun ω => (pidC A B (xPalm γ y ω), y)) ⁻¹' E).indicator 1 := by
        funext ω
        exact indicator_one_eq_of_iff Iff.rfl
      rw [e1, lintegral_indicator_one hpre]
      refine measure_congr ?_
      filter_upwards [hy] with ω hω
      exact propext (mem_pidSetRZ_iff hZc γ i t m κ he hdep (by rw [coords_pidNf]; exact hω) y)
    have hy0 : y ≠ 0 := hyI.1.ne'
    rw [hint, rhoX_eq hγ hy0, ENNReal.ofReal_mul (abs_nonneg y)]
    ring
  have hmR : Measurable fun y => ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS y) *
      ∫⁻ ω, φ (pidC A B (xPalm γ y ω)) y ∂gffBase.P :=
    (E1.measurable_rhoNorm measurable_const refS).ennreal_ofReal.mul (measurable_pidK γ hA hB hφ)
  refine ⟨?_, ?_⟩
  · unfold g3RootIntR
    rw [lintegral_congr_ae hL, pid_palm hγ hγ2 hA hB hab hφ, lintegral_congr_ae hkey,
      Measure.restrict_congr_set Ioo_ae_eq_Icc]
  · rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
    exact hmR.aemeasurable.congr hkey

