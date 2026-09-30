import QuantumZipper.Proofs.Thm18.G2PalmIdX

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2-PALMID, part 4: the Palm node on the `R` side, `G2RootRPalmIdStmt γ`, PROVED

`g2RootRPalmIdStmt_holds : 0 < γ → γ < 2 → G2RootRPalmIdStmt γ`.

The twin of `G2PalmIdX.lean` (same source: Duplantier–Sheffield, arXiv:0808.1560, §3.3, p. 22,
normalized form `E1.palm_formula_Ioo`) on the window `[0, t₂ + r₂] ⊆ [0, 1]`, with the extra
conditioning coordinate `M = g3Mass` (the boundary masses of `[−δ, 0]` read from the region-1 and
gap fields). These are functions of the raw dyadic coordinates of `h` (`bdryM = bdryMc ∘ coords`,
and the coordinates of a restricted field are masked coordinates, `coords_restrictField`), so the
same coordinate route applies. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Factorization (coords reconstruct)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

open Classical in
/-- Masked dyadic coordinates (the coordinates of `restrictField S`). -/
def maskC (S : Set (Measure ℂ)) (d : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if WedgeGood.fcC k ∈ S then d k else 0

theorem coords_restrictField (S : Set (Measure ℂ)) (y : FieldSample) :
    coords (restrictField S y) = maskC S (coords y) := by
  funext k
  simp only [coords, restrictField, maskC]
  rfl

theorem measurable_maskC (S : Set (Measure ℂ)) : Measurable (maskC S) := by
  refine measurable_pi_iff.2 fun k => ?_
  by_cases hk : WedgeGood.fcC k ∈ S
  · simp only [maskC, if_pos hk]; exact measurable_pi_apply _
  · simp only [maskC, if_neg hk]; exact measurable_const

/-- The truncation mass read at a sample `V`. -/
def pidMassV (γ : ℝ) (i : G3Idx) (V : FieldSample) : ℝ≥0∞ :=
  (bdryM γ (restrictField (circIn i.t₁ i.r₁) (pidNf γ V)) +
    bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (pidNf γ V))) (Icc (-i.δ) 0)

/-- The truncation mass in the coordinates. -/
def pidMassC (γ : ℝ) (i : G3Idx) (c : ℕ → ℝ) : ℝ≥0∞ :=
  (bdryMc γ (maskC (circIn i.t₁ i.r₁) (pidDN γ c)) +
    bdryMc γ (maskC (circOut i.t₁ i.r₁ i.t₂ i.r₂) (pidDN γ c))) (Icc (-i.δ) 0)

theorem pidMassV_eq (γ : ℝ) (i : G3Idx) (A B : ℕ → Measure ℂ) (V : FieldSample) :
    pidMassV γ i V = pidMassC γ i (pidC A B V) := by
  unfold pidMassV pidMassC
  rw [bdryM_eq_bdryMc, bdryM_eq_bdryMc, coords_restrictField, coords_restrictField,
    coords_pidNf γ A B]

theorem measurable_pidMassC (γ : ℝ) (i : G3Idx) : Measurable (pidMassC γ i) :=
  (Measure.measurable_coe measurableSet_Icc).comp (measurable_measure_add
    ((measurable_bdryMc γ).comp ((measurable_maskC _).comp (measurable_pidDN γ)))
    ((measurable_bdryMc γ).comp ((measurable_maskC _).comp (measurable_pidDN γ))))

section RSide

variable (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G'' : Set (CondR i))

/-- The rooted event at `R` read at a sample `V` and a point `y`. -/
def pidEvR (y : ℝ) (V : FieldSample) : Prop :=
  zoomLaw γ i.C (pidNf γ V) y ∈ t ∧ |y - i.t₂| + m < i.r₂ ∧
    (outMap i V, (qBoundaryMeasure γ (pidNf γ V) (Icc 0 (y - κ))).toReal, pidMassV γ i V) ∈ G''

/-- The same event in the coordinates. -/
def pidSetR (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) : Set ((ℕ → ℝ) × ℝ) :=
  {p | zoomLaw γ i.C (reconstruct (pidDN γ p.1)) p.2 ∈ t ∧ |p.2 - i.t₂| + m < i.r₂ ∧
    (pidR J e (pidD p.1), (cutR (bdryMc γ (pidDN γ p.1)) (p.2 - κ)).toReal, pidMassC γ i p.1)
      ∈ G''}

end RSide

theorem measurableSet_pidSetR (γ : ℝ) (i : G3Idx) {t : Set LawD} (ht : MeasurableSet t)
    (m κ : ℝ) {G'' : Set (CondR i)} (hG'' : MeasurableSet G'')
    (J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)) (e : J → ℕ) :
    MeasurableSet (pidSetR γ i t m κ G'' J e) := by
  have hdn : Measurable fun p : (ℕ → ℝ) × ℝ => pidDN γ p.1 := (measurable_pidDN γ).comp measurable_fst
  refine (((measurable_zoomLaw γ i.C).comp
    ((Factorization.measurable_reconstruct.comp hdn).prodMk measurable_snd)) ht).inter
    ((measurableSet_lt (Measurable.add_const (continuous_abs.measurable.comp
      (measurable_snd.sub_const i.t₂)) m) measurable_const).inter ?_)
  exact (((measurable_pidR J e).comp (measurable_pidD.comp measurable_fst)).prodMk
    ((measurable_cutR ((measurable_bdryMc γ).comp hdn) (measurable_snd.sub_const κ)).ennreal_toReal.prodMk
      ((measurable_pidMassC γ i).comp measurable_fst))) hG''

theorem mem_pidSetR_iff (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) {G'' : Set (CondR i)}
    {J : Set (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)} {e : J → ℕ} (he : Function.Injective e)
    (hdep : ∀ f g : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ, (∀ j ∈ J, f j = g j) → ∀ b : ℝ × ℝ≥0∞,
      ((f, b) ∈ G'' ↔ (g, b) ∈ G''))
    {V : FieldSample} (hV : pidFine γ (coords (pidNf γ V))) (y : ℝ) :
    (pidC (pidA J e (outPr i)) (pidB J e (outPr i)) V, y) ∈ pidSetR γ i t m κ G'' J e ↔
      pidEvR γ i t m κ G'' y V := by
  obtain ⟨hc, hf⟩ := (pidFine_coords_iff γ _).1 hV
  have hfin := qBM_Icc_ne_top_of_fine hf
  simp only [pidSetR, pidEvR, mem_setOf_eq]
  rw [pidMassV_eq γ i (pidA J e (outPr i)) (pidB J e (outPr i)) V, ← coords_pidNf,
    zoomLaw_reconstruct_coords, bdryMc_coords_eq, if_pos hc, cutR_eq (fun u => hfin 0 u)]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  exact hdep _ _ (fun p hp => (outMap_eq_pidR i he V p hp).symm) _

/-- **Node P, `R` side (`G2RootRPalmIdStmt γ`), proved for `0 < γ < 2`.** -/
theorem g2RootRPalmIdStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootRPalmIdStmt γ := by
  intro i t ht m κ _hm _hκ G'' hG''
  obtain ⟨J, hJ, hdep⟩ := exists_countable_dep (ι := OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂)
    (β := ℝ × ℝ≥0∞) hG''
  have : Countable J := hJ
  obtain ⟨e, he⟩ := Countable.exists_injective_nat J
  set A := pidA J e (outPr i) with hAdef
  set B := pidB J e (outPr i) with hBdef
  have hA : ∀ n, IsAdmissibleH (A n) := pidA_adm (fun p => p.2.1)
  have hB : ∀ n, IsAdmissibleH (B n) := pidB_adm (fun p => p.2.2.1)
  set E := pidSetR γ i t m κ G'' J e with hEdef
  have hE : MeasurableSet E := measurableSet_pidSetR γ i ht m κ hG'' J e
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
      ∫⁻ y in Icc 0 (i.t₂ + i.r₂), (g3RootEvRcc γ i t m κ G'').indicator 1
        (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) ∂(g3Hν γ ω) =
      ∫⁻ y in Ioo 0 (i.t₂ + i.r₂), φ (pidC A B (X₀ ω)) y ∂(g3Zν γ ω) := by
    filter_upwards [ae_pidFine_free hγ hγ2, ae_g3Hν_eq hγ hγ2,
      G3Fid.ae_normField_good gffBase.gff hγ hγ2,
      S5.FieldLaw.Raw.ae_freeFieldN_bdry gffBase.gff hγ hγ2 refS] with ω hfine hH hg hZ
    have hpt : ∀ y, (g3RootEvRcc γ i t m κ G'').indicator 1
        (ω, (g3Hν γ ω (Icc 0 y)).toReal, y) = E.indicator 1 (pidC A B (X₀ ω), y) := fun y =>
      indicator_one_eq_of_iff ((mem_pidSetR_iff γ i t m κ he hdep hfine y).symm)
    simp only [hpt]
    exact lintegral_hν_eq hH (hZ.2.1 0) (hg.2.2 _) (hg.2.2 _)
      (hEi.comp (measurable_const.prodMk measurable_id))
  have hkey : ∀ᵐ y ∂(volume.restrict (Ioo 0 (i.t₂ + i.r₂))),
      ENNReal.ofReal (PalmNorm.rhoNorm γ 0 refS y) *
        ∫⁻ ω, φ (pidC A B (xPalm γ y ω)) y ∂gffBase.P =
      ENNReal.ofReal (rhoX γ y) * gffBase.P (g3PalmEvR γ i t m κ G'' y) := by
    filter_upwards [ae_pidFine_palm hγ hγ2 hA hB hab, ae_restrict_mem measurableSet_Ioo]
      with y hy hyI
    have hmy : Measurable fun ω => pidC A B (xPalm γ y ω) := measurable_pidC_xPalm γ A B y
    have hpre : MeasurableSet ((fun ω => (pidC A B (xPalm γ y ω), y)) ⁻¹' E) :=
      (hmy.prodMk measurable_const) hE
    have hint : ∫⁻ ω, φ (pidC A B (xPalm γ y ω)) y ∂gffBase.P =
        ENNReal.ofReal |y| * gffBase.P (g3PalmEvR γ i t m κ G'' y) := by
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
      exact propext (mem_pidSetR_iff γ i t m κ he hdep (by rw [coords_pidNf]; exact hω) y)
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

end Thm18Asm
end QuantumZipper
