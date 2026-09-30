import QuantumZipper.Proofs.Thm18.G3ZqWire
import QuantumZipper.Proofs.Thm18.G3ZqResc
import QuantumZipper.Proofs.Thm18.G3ZqGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (4): step 5T from the fixed-path limit of the **unscaled** wedge (rescaling route)

G1-ZOOM found that the fixed-path Palm limit cannot be proved path by path for the canonical
wedge `wedgeRep = canonical (wedgeU)`: in the coordinates of the unscaled field `wedgeU` (where
the field is a free field plus the radial part, the setting of Sheffield's Proposition 5.5), the
local maps of a fixed path become `b · φ(·/b)` with the random, global scale
`b = scaleParam γ wedgeU`. The fix is to average over the path first: by
`lintegral_path_rescale` (G3ZqResc) the path average of the canonical two-point functional equals
the path average of the unscaled one, given the pointwise rescaling identity
`g3PhiM2 (canonical W, S_b a) = g3PhiM2 (W, a)` for a.e. `ω'` and a.e. path (`G3ZqResclIdStmt`;
the one-point identity is `G1Zm.g1PhiM_canonical_scalePath`).

* `measurable_g3PhiM2_wedgeU`, `aemeasurable_g3PhiM2_wedgeRep_prod`, `aemeasurable_g3PhiM2_wedgeU_prod`;
* **`g3WedgeFreeTransferStmt_of_pathU : G3ZqResclIdStmt → G3ZqPathSmallUStmt →
  R18.G3WedgeFreeTransferStmt`**.

Sheffield, arXiv:1012.4797, pp. 70–71 (independent curve, SLE scale invariance). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 G3Zp G1Zm Factorization

/-- **The pointwise two-point rescaling identity, a.s.** (two-point analog of
`G1Zm.g1PhiM_canonical_scalePath`): for the wedge representative and an independent Brownian
path, for a.e. `ω'` the scale `b` of the unscaled field is positive and for a.e. path `a` the
two-point functional of the canonical field along `S_b a` equals that of the unscaled field
along `a`. -/
def G3ZqResclIdStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
    IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    (∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) →
  ∀ (U L : ℝ) (s t : Set LawD), s ∈ lawCyl → t ∈ lawCyl →
    ∀ᵐ ω' ∂P', 0 < scaleParam γ (wedgeU γ X A ω') ∧ ∀ᵐ a ∂(P.map (pathOf B)),
      g3PhiM2 γ L Ψ U s t (wedgeRep γ X A ω', scalePath (scaleParam γ (wedgeU γ X A ω')) a) =
        g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a)

/-- **The fixed-path Palm limit of the unscaled wedge at small windows** (`G3ZqPathSmallStmt`
with the unscaled field `wedgeU` in place of `wedgeRep`; the form in which the local maps of the
path are fixed maps in the coordinates of Sheffield's Proposition 5.5). -/
def G3ZqPathSmallUStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
    ∀ s ∈ lawCyl, ∀ t ∈ lawCyl, ∀ c : ℝ,
      Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter
        (𝓝 c) →
      ∀ ε : ℝ, 0 < ε → ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ U : ℝ, 0 < U → U ≤ U₀ →
        ∀ᵐ a ∂(P.map (pathOf B)), G3ZqGoodPathF γ a → ∀ᶠ L in (atTop : Filter ℝ),
          |(∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P').toReal / U - c| ≤ ε

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The two-point functional read through the coordinates. -/
theorem g3PhiM2_reconstruct_coords {γ L U : ℝ} {s t : Set LawD} (y : FieldSample)
    (a : ℝ≥0 → ℝ) :
    g3PhiM2 γ L Ψ U s t (reconstruct (coords y), a) = g3PhiM2 γ L Ψ U s t (y, a) :=
  g3PhiM2_congr (Factorization.avgReg_reconstruct_coords y) a

theorem measurable_g3PhiM2_coords {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ) {s t : Set LawD}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Measurable fun q : (ℝ≥0 → ℝ) × (ℕ → ℝ) => g3PhiM2 γ L Ψ U s t (reconstruct q.2, q.1) :=
  (measurable_g3PhiM2 hsel L U hs ht).comp
    ((Factorization.measurable_reconstruct.comp measurable_snd).prodMk measurable_fst)

/-- The unscaled path-functional is measurable in the path. -/
theorem measurable_g3PhiM2_wedgeU {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ) {s t : Set LawD}
    (hs : MeasurableSet s) (ht : MeasurableSet t) {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hc : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P') :
    Measurable fun a => ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P' := by
  have e : (fun a => ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P') =
      fun a => ∫⁻ c, g3PhiM2 γ L Ψ U s t (reconstruct c, a)
        ∂(P'.map fun ω' => coords (wedgeU γ X A ω')) := by
    funext a
    rw [lintegral_map' _ hc]
    · exact lintegral_congr fun ω' => (g3PhiM2_reconstruct_coords _ _).symm
    · exact ((measurable_g3PhiM2_coords hsel L U hs ht).comp
        (measurable_const.prodMk measurable_id)).aemeasurable
  rw [e]
  exact (measurable_g3PhiM2_coords hsel L U hs ht).lintegral_prod_right'

theorem aemeasurable_g3PhiM2_wedgeU_prod {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ)
    {s t : Set LawD} (hs : MeasurableSet s) (ht : MeasurableSet t) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hc : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P')
    (ν : Measure (ℝ≥0 → ℝ)) [SFinite ν] :
    AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => g3PhiM2 γ L Ψ U s t (wedgeU γ X A q.2, q.1))
      (ν.prod P') := by
  have h1 : AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => coords (wedgeU γ X A q.2)) (ν.prod P') :=
    hc.comp_snd
  have h2 : AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => (q.1, coords (wedgeU γ X A q.2)))
      (ν.prod P') := measurable_fst.aemeasurable.prodMk h1
  refine ((measurable_g3PhiM2_coords hsel L U hs ht).comp_aemeasurable h2).congr
    (ae_of_all _ fun q => ?_)
  exact g3PhiM2_reconstruct_coords (wedgeU γ X A q.2) q.1

theorem aemeasurable_g3PhiM2_wedgeRep_prod {γ : ℝ} (hsel : G1PsiSel γ Ψ) (L U : ℝ)
    {s t : Set LawD} (hs : MeasurableSet s) (ht : MeasurableSet t) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hm : AEMeasurable (fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω')) P')
    (ν : Measure (ℝ≥0 → ℝ)) [SFinite ν] :
    AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => g3PhiM2 γ L Ψ U s t (wedgeRep γ X A q.2, q.1))
      (ν.prod P') := by
  have h1 : AEMeasurable (fun q : (ℝ≥0 → ℝ) × Ω' => WedgeMeas.dataFull H (wedgeRep γ X A q.2))
      (ν.prod P') := hm.comp_snd
  have h2 : AEMeasurable
      (fun q : (ℝ≥0 → ℝ) × Ω' => (q.1, WedgeMeas.dataFull H (wedgeRep γ X A q.2)))
      (ν.prod P') := measurable_fst.aemeasurable.prodMk h1
  refine ((measurable_g3PhiData2 hsel L U hs ht).comp_aemeasurable h2).congr
    (ae_of_all _ fun q => ?_)
  exact g3PhiM2_fromC (wedgeRep γ X A q.2) q.1

/-- **Step 5T from the unscaled fixed-path limit and the rescaling identity.** -/
theorem g3WedgeFreeTransferStmt_of_pathU (hI : G3ZqResclIdStmt) (hP : G3ZqPathSmallUStmt) :
    R18.G3WedgeFreeTransferStmt := by
  intro γ Ω _ P _ B Y hS hIn s hs t ht c hc ε hε
  have hγ := hS.1
  have hγ2 := hS.2.1
  have hB : IsBrownianReal B P := hS.2.2.1
  obtain ⟨Ψ, hsel⟩ := g1PsiSelStmt γ hγ hγ2
  have hZ2 : G1Z2SideGoodStmt := g1Z2SideGoodStmt_of_area
    (g1Z2SideAreaStmt_of_sel (g1Z2SideAreaSelStmt_of_top G1Top.g1Z2SideTopSelStmt_holds))
  obtain ⟨Ω', _, P', hP', X, A, hX, hA, hXA, hfub⟩ :=
    G3Zr.g3zWedgePalmCyl_fubini_side hZ2 γ P B Y hS hIn hsel
  have hsm := measurableSet_lawCyl hs
  have htm := measurableSet_lawCyl ht
  have hc0 : 0 ≤ c := ge_of_tendsto hc (Eventually.of_forall fun i => measureReal_nonneg)
  obtain ⟨e, he0, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal (2 * e) ≤ ε := by
    obtain ⟨r, hr0, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hrpos : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · rw [← h, ENNReal.ofReal_zero] at hr; exact absurd hr (lt_irrefl 0)
    exact ⟨r / 2, by positivity, by rw [show 2 * (r / 2) = r by ring]; exact hrε.le⟩
  obtain ⟨U₀, hU₀, HP⟩ := hP γ P B Y hS hIn Ψ hsel P' X A hX hA hXA s hs t ht c hc e he0
  refine ⟨U₀, hU₀, fun U hU hUU₀ => ?_⟩
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff hgm).2 inferInstance
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hS.2.2.2.1.1, Ω', inferInstance, P', X, A, hP', hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  have hcu : AEMeasurable (fun ω' => coords (wedgeU γ X A ω')) P' :=
    WedgeMeas.aemeasurable_coords_wedgeField hX.measurable_coord hA
  have hpos : ∀ U' : ℝ, ∀ᵐ ω ∂P, ∀ᵐ x ∂(qBoundaryMeasure γ (Y ω)),
      x ∈ g1zWedgeWin γ true (Y ω) U' → 0 < R18.g3zPartner γ (Y ω) x := by
    intro U'
    filter_upwards [ae_g3zPartner_pos hS hIn] with ω hω
    exact Eventually.of_forall fun x hx => hω x hx.1
  set Fu : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun L a =>
    ∫⁻ ω', g3PhiM2 γ L Ψ U s t (wedgeU γ X A ω', a) ∂P' with hFudef
  have hFm : ∀ L, Measurable (Fu L) := fun L => measurable_g3PhiM2_wedgeU hsel L U hsm htm hcu
  have hFle : ∀ L a, Fu L a ≤ ENNReal.ofReal U := by
    intro L a
    calc Fu L a ≤ ∫⁻ _ω', ENNReal.ofReal U ∂P' := lintegral_mono fun ω' => g3PhiM2_le _
      _ = ENNReal.ofReal U := by simp
  have hJ : ∀ L, R18.g3zWedgePalmCyl γ P B Y U L s t = ∫⁻ a, Fu L a ∂(P.map (pathOf B)) := by
    intro L
    rw [hfub U L s t hsm htm (hpos U)]
    exact lintegral_path_rescale hB (measurable_g3PhiM2 hsel L U hsm htm)
      (aemeasurable_g3PhiM2_wedgeRep_prod hsel L U hsm htm hm _)
      (aemeasurable_g3PhiM2_wedgeU_prod hsel L U hsm htm hcu _)
      (hI γ hγ hγ2 Ψ hsel P' X A hX hA hXA P B hB
        (by filter_upwards [hIn.2.2] with ω h; exact h.1) U L s t hs ht)
  set f : ℝ → (ℝ≥0 → ℝ) → ℝ := fun L a => (Fu L a).toReal / U with hfdef
  have hf01 : ∀ L a, 0 ≤ f L a ∧ f L a ≤ 1 := by
    intro L a
    refine ⟨div_nonneg ENNReal.toReal_nonneg hU.le, (div_le_one hU).2 ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal hU.le (hFle L a)
  have hsc : ∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := by
    filter_upwards [hIn.2.2] with ω h; exact h.1
  have hω : ∀ᵐ ω ∂P, ∀ᶠ L in (atTop : Filter ℝ), |f L (pathOf B ω) - c| ≤ e := by
    filter_upwards [ae_of_ae_map hgm (HP U hU hUU₀), ae_goodPathF hγ hγ2 hB hsc] with ω h1 h2
    exact h1 h2
  have hfm : ∀ L, AEStronglyMeasurable (f L) (P.map (pathOf B)) := fun L =>
    ((hFm L).ennreal_toReal.div_const U).aestronglyMeasurable
  have hev := eventually_abs_integral_sub_le (μ := P) (f := fun L ω => f L (pathOf B ω))
    (fun L => ((hFm L).ennreal_toReal.div_const U).comp_aemeasurable hgm |>.aestronglyMeasurable)
    (K := 1)
    (fun L ω => by rw [abs_of_nonneg (hf01 L _).1]; exact (hf01 L _).2) he0 hω
  filter_upwards [hev] with L hL
  rw [← integral_map hgm (hfm L)] at hL
  have hint : (ENNReal.ofReal U)⁻¹ * R18.g3zWedgePalmCyl γ P B Y U L s t =
      ENNReal.ofReal (∫ a, f L a ∂(P.map (pathOf B))) := by
    have hfin : ∀ a, Fu L a ≠ ⊤ := fun a => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hFle L a)
    have h1 : ∫⁻ a, Fu L a ∂(P.map (pathOf B)) =
        ENNReal.ofReal (∫ a, (Fu L a).toReal ∂(P.map (pathOf B))) := by
      rw [ofReal_integral_eq_lintegral_ofReal]
      · exact lintegral_congr fun a => (ENNReal.ofReal_toReal (hfin a)).symm
      · refine Integrable.of_bound (hFm L).ennreal_toReal.aestronglyMeasurable U
          (ae_of_all _ fun a => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal hU.le (hFle L a)
      · exact ae_of_all _ fun a => ENNReal.toReal_nonneg
    rw [hJ L, h1, hfdef]
    simp only
    rw [integral_div, ← ENNReal.ofReal_inv_of_pos hU, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_eq_div]
  rw [hint]
  rw [abs_le] at hL
  constructor
  · calc ENNReal.ofReal (∫ a, f L a ∂(P.map (pathOf B))) ≤ ENNReal.ofReal (c + 2 * e) :=
          ENNReal.ofReal_le_ofReal (by linarith [hL.2])
      _ ≤ ENNReal.ofReal c + ENNReal.ofReal (2 * e) := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal c + ε := by gcongr
  · calc ENNReal.ofReal c ≤ ENNReal.ofReal (∫ a, f L a ∂(P.map (pathOf B)) + 2 * e) :=
          ENNReal.ofReal_le_ofReal (by linarith [hL.1])
      _ ≤ ENNReal.ofReal (∫ a, f L a ∂(P.map (pathOf B))) + ENNReal.ofReal (2 * e) :=
          ENNReal.ofReal_add_le
      _ ≤ _ := by gcongr

end G3Zq
end Thm18Asm
end QuantumZipper
