import QuantumZipper.Proofs.Thm18.G3ZqL15Cap
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (16): the uniform unscaled comparison from goodness at typical points

Copy of G3ZqG3LUnsc (`g3pl4_expect_cap_leGZ`, `g3pl4_unscaled_atGZ`, `g3PlPhiUnscaledZ_unifG`) with
the every-point goodness of the unscaled wedge `g3plUW γ X A` and of `V + logSing` replaced by
goodness at `ν`-a.e. point and its length partner (`G3ZqL.G3PlCapLocAE`, G3ZqL15Cap). Own
bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

namespace G3ZqL

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

theorem g3pl4_expect_cap_leAE {γ : ℝ} {Gd Gd' : FieldSample → ℝ → Prop}
    (hLoc : G3ZqL.G3PlCapLocAE Z Z' γ Gd Gd') {δ U : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    {s t : Set LawD} (hs : s ∈ lawCyl) (ht : t ∈ lawCyl)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y₁ Y₂ : Ω → FieldSample}
    (hg₁ : ∀ᵐ ω ∂P, IsLQGGood γ (Y₁ ω)) (hg₂ : ∀ᵐ ω ∂P, IsLQGGood γ (Y₂ ω))
    (hΦ₁ : ∀ L, AEMeasurable (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (Y₁ ω)) P)
    (hΦ₂ : ∀ L, AEMeasurable (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (Y₂ ω)) P)
    (hag : ∀ᵐ ω ∂P, FcAgree (ball (0 : ℂ) 1) (Y₁ ω) (Y₂ ω))
    (hG₂ : ∀ᵐ ω ∂P, ∀ᵐ x ∂(qBoundaryMeasure γ (Y₂ ω)), Gd (Y₂ ω) x ∧ Gd' (Y₂ ω) (g3zPartner γ (Y₂ ω) x))
    {E : Set Ω} (hE : MeasurableSet E) (hEsep : ∀ ω ∈ E, g3pl4Sep γ δ (Y₁ ω))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ L in atTop, ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₁ ω) ∂P ≤
      ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₂ ω) ∂P + ENNReal.ofReal U * P Eᶜ + ε := by
  have hsm := measurableSet_lawCyl hs
  have htm := measurableSet_lawCyl ht
  set F : ℝ → Ω → ℝ≥0∞ := fun L => E.indicator (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (Y₁ ω))
  set G : ℝ → Ω → ℝ≥0∞ := fun L ω => g3pl4PhiCapZ Z Z' γ δ U L s t (Y₂ ω)
  have hF : ∀ L, AEMeasurable (F L) P := fun L => (hΦ₁ L).indicator hE
  have hG : ∀ L, AEMeasurable (G L) P := hΦ₂
  have hbd : ∀ L, ∀ᵐ ω ∂P, F L ω ≤ ENNReal.ofReal U := fun L => ae_of_all _ fun ω =>
    (indicator_le_self _ _ ω).trans (g3pl4_phiCapZ_le_U _ _ _ _ _ _ _)
  have hlim : ∀ᵐ ω ∂P, ∀ e : ℝ≥0∞, 0 < e → ∀ᶠ L in atTop, F L ω ≤ G L ω + e := by
    filter_upwards [hg₁, hg₂, hag, hG₂] with ω h1 h2 ha hp e he
    by_cases hω : ω ∈ E
    · filter_upwards [hLoc δ U hδ hδ4 s hs t ht (Y₁ ω) (Y₂ ω) h1 h2 ha hp (hEsep ω hω) e he]
        with L hL
      simp only [F, G, indicator_of_mem hω]
      exact hL
    · refine Eventually.of_forall fun L => ?_
      simp only [F, indicator_of_notMem hω]
      exact bot_le
  have hmain := g3pl4_expect_le hF hG ENNReal.ofReal_ne_top hbd hlim hε
  filter_upwards [hmain] with L hL
  have hsplit : ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₁ ω) ∂P ≤
      ∫⁻ ω, F L ω ∂P + ENNReal.ofReal U * P Eᶜ := by
    calc ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₁ ω) ∂P
        ≤ ∫⁻ ω, (F L ω + Eᶜ.indicator (fun _ => ENNReal.ofReal U) ω) ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ E
          · simp only [F, indicator_of_mem hω]
            exact le_self_add
          · simp only [F, indicator_of_notMem hω, zero_add,
              indicator_of_mem (show ω ∈ Eᶜ from hω)]
            exact g3pl4_phiCapZ_le_U _ _ _ _ _ _ _
      _ = ∫⁻ ω, F L ω ∂P + ENNReal.ofReal U * P Eᶜ := by
          rw [lintegral_add_right _ (measurable_const.indicator hE.compl),
            lintegral_indicator_const hE.compl]
  calc ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₁ ω) ∂P
      ≤ ∫⁻ ω, F L ω ∂P + ENNReal.ofReal U * P Eᶜ := hsplit
    _ ≤ (∫⁻ ω, G L ω ∂P + ε) + ENNReal.ofReal U * P Eᶜ := add_le_add hL le_rfl
    _ = _ := by simp only [G]; ring

theorem g3pl4_unscaled_atAE
    (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    (hZa : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x)
    (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    (hZa' : ∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x)
    {γ : ℝ} {Gd Gd' : FieldSample → ℝ → Prop} (hLoc : G3ZqL.G3PlCapLocAE Z Z' γ Gd Gd')
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : Ω' → FieldSample}
    {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess (γ - 2 / γ) (Qc γ) A P')
    (hXA : IndepFun X (fun ω t => A t ω) P')
    (hGW : ∀ᵐ ω ∂P', ∀ᵐ x ∂(qBoundaryMeasure γ (g3plUW γ X A ω)), Gd (g3plUW γ X A ω) x ∧ Gd' (g3plUW γ X A ω) (g3zPartner γ (g3plUW γ X A ω) x))
    (hGV : ∀ V : Ω' → FieldSample, IsFreeGFFModConstH V P' →
      (∀ᵐ ω ∂P', V ω (foldedCircle 0 1) = 0) →
      ∀ᵐ ω ∂P', ∀ᵐ x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))), Gd (V ω + F2.logSingField (γ ^ 2)) x ∧ Gd' (V ω + F2.logSingField (γ ^ 2)) (g3zPartner γ (V ω + F2.logSingField (γ ^ 2)) x))
    {s t : Set LawD}
    (hM : ∀ δ U L : ℝ, AEMeasurable (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (g3plUW γ X A ω)) P')
    (hAG : ∀ᵐ ω ∂P', IsAreaGood γ (g3plUW γ X A ω))
    (hs : s ∈ lawCyl) (ht : t ∈ lawCyl) {ε : ℝ} (hε : 0 < ε)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) {U₀ : ℝ} (hU₀ : 0 < U₀)
    (hSepδ : ∃ E : Set Ω', MeasurableSet E ∧
      (∀ ω ∈ E, g3pl4Sep γ δ (g3plUW γ X A ω)) ∧ P' Eᶜ ≤ ENNReal.ofReal (ε / 4))
    (hSmallU : ∀ U : ℝ, 0 < U → U ≤ U₀ →
      ∃ E : Set Ω', MeasurableSet E ∧
        (∀ ω ∈ E, ENNReal.ofReal U ≤ qBoundaryMeasure γ (g3plUW γ X A ω) (Icc (-δ) 0)) ∧
        P' Eᶜ ≤ ENNReal.ofReal (ε / 4)) :
    ∀ U : ℝ, 0 < U → U ≤ U₀ →
      ∀ᶠ L in (atTop : Filter ℝ),
        (ENNReal.ofReal U)⁻¹ * ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (g3plUW γ X A ω) ∂P' ≤
            (ENNReal.ofReal U)⁻¹ * g3plHonXZ Z Z' γ δ U L s t + ENNReal.ofReal ε ∧
          (ENNReal.ofReal U)⁻¹ * g3plHonXZ Z Z' γ δ U L s t ≤
            (ENNReal.ofReal U)⁻¹ * ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (g3plUW γ X A ω) ∂P' +
              ENNReal.ofReal ε := by
  set W := g3plUW γ X A with hW
  have hsm := measurableSet_lawCyl hs
  have htm := measurableSet_lawCyl ht
  obtain ⟨V, hV, hVn, hag⟩ := g3pl4_wedge_fcAgree_norm hγ hX hA hXA
  set Y₂ : Ω' → FieldSample := fun ω => V ω + F2.logSingField (γ ^ 2) with hY₂
  have hg₂ := g3pl4_ae_isAreaGood_logSing hγ hγ2 hV
  have hm₂' : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y₂ ω)) P' :=
    (g3pl4_measurable_data fun μ => (hV.measurable_coord μ).add measurable_const).aemeasurable
  have hm₂ : ∀ δ U L : ℝ, AEMeasurable (fun ω => g3pl4PhiCapZ Z Z' γ δ U L s t (Y₂ ω)) P' :=
    fun δ U L => aemeasurable_phiCapZ hZm hZa hZm' hZa' hsm htm (hg₂.mono fun ω h => h.1) hm₂'
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨E₁, hE₁m, hE₁, hE₁P⟩ := hSepδ
  -- the a.s. event of the coupling
  obtain ⟨S, hSm, hS, hS0⟩ := g3pl4_exists_measurable_ae (P := P')
    (Q := fun ω => IsAreaGood γ (W ω) ∧ IsAreaGood γ (Y₂ ω) ∧
      FcAgree (ball (0 : ℂ) 1) (W ω) (Y₂ ω)) (by
        filter_upwards [hAG, hg₂, hag] with ω h1 h2 h3
        exact ⟨h1, h2, h3⟩)
  set E := E₁ ∩ S with hE
  have hEm : MeasurableSet E := hE₁m.inter hSm
  have hEP : P' Eᶜ ≤ ENNReal.ofReal (ε / 4) := by
    rw [hE, compl_inter]
    refine (measure_union_le _ _).trans ?_
    rw [hS0, add_zero]
    exact hE₁P
  have hsepW : ∀ ω ∈ E, g3pl4Sep γ δ (W ω) := fun ω hω => hE₁ ω hω.1
  have hsepY : ∀ ω ∈ E, g3pl4Sep γ δ (Y₂ ω) := by
    intro ω hω
    obtain ⟨h1, h2, h3⟩ := hS ω hω.2
    have hνr := g3pl4_restrict_eq_of_agree h1.1 h2.1 h3
    obtain ⟨hsep, hR⟩ := hsepW ω hω
    have hδ' : -(1 / 2 : ℝ) ≤ -δ := by linarith
    rw [g3pl4Sep, ← g3pl4_Icc_eq hνr hδ' (by norm_num),
      ← g3pl4_Icc_eq hνr (le_refl _) (by norm_num), ← g3pl4_Icc_eq hνr (by norm_num) (by norm_num)]
    exact ⟨hsep, hR⟩
  have hposW : ∀ᵐ ω ∂P', ∀ (x : ℝ) (q : ℝ), 0 < q →
      0 < areaProxy γ (translate (W ω) (x : ℂ)) q :=
    hAG.mono fun ω h x q hq => pos_areaProxy_of_isAreaGood (h.translate x) hq
  have hposY : ∀ᵐ ω ∂P', ∀ (x : ℝ) (q : ℝ), 0 < q →
      0 < areaProxy γ (translate (Y₂ ω) (x : ℂ)) q :=
    hg₂.mono fun ω h x q hq => pos_areaProxy_of_isAreaGood (h.translate x) hq
  intro U hU0 hUU
  obtain ⟨E₂, hE₂m, hE₂, hE₂P⟩ := hSmallU U hU0 hUU
  set u := ENNReal.ofReal U with hu
  have hu0 : u ≠ 0 := (ENNReal.ofReal_pos.2 hU0).ne'
  have hut : u ≠ ⊤ := ENNReal.ofReal_ne_top
  have hε' : 0 < u * ENNReal.ofReal (ε / 4) :=
    ENNReal.mul_pos hu0 (ENNReal.ofReal_pos.2 hε4).ne'
  have up := g3pl4_expect_cap_leAE hLoc (U := U) hδ hδ4 hs ht (Y₁ := W) (Y₂ := Y₂)
    (hAG.mono fun ω h => h.1) (hg₂.mono fun ω h => h.1) (hM δ U) (hm₂ δ U) hag (hGV V hV hVn) hEm hsepW hε'
  have down := g3pl4_expect_cap_leAE hLoc (U := U) hδ hδ4 hs ht (Y₁ := Y₂) (Y₂ := W)
    (hg₂.mono fun ω h => h.1) (hAG.mono fun ω h => h.1) (hm₂ δ U) (hM δ U)
    (hag.mono fun ω h => g3pl4_fcAgree_symm h) hGW hEm hsepY hε'
  filter_upwards [up, down] with L hup hdown
  have hHon : ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₂ ω) ∂P' = g3plHonXZ Z Z' γ δ U L s t :=
    g3pl4_lintegral_phiCapZ_V_eq hZm hZa hZm' hZa' hγ hγ2 hV hVn hsm htm
  -- window vs capped window
  have hW2 : ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P' ≤
      ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (W ω) ∂P' + u * P' E₂ᶜ := by
    calc ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P'
        ≤ ∫⁻ ω, (g3pl4PhiCapZ Z Z' γ δ U L s t (W ω) + E₂ᶜ.indicator (fun _ => u) ω) ∂P' := by
          refine lintegral_mono fun ω => (g3pl4_phiZ_le_phiCapZ γ δ U L s t (W ω)).trans ?_
          refine add_le_add le_rfl ?_
          by_cases hω : ω ∈ E₂
          · have hn : W ω ∉ {y : FieldSample | qBoundaryMeasure γ y (Icc (-δ) 0) <
                ENNReal.ofReal U} := fun h => absurd (hE₂ ω hω) (not_le.2 h)
            rw [indicator_of_notMem hn]
            exact bot_le
          · rw [indicator_of_mem (show ω ∈ E₂ᶜ from hω)]
            exact Set.indicator_le (fun _ _ => le_rfl) _
      _ = ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (W ω) ∂P' + u * P' E₂ᶜ := by
          rw [lintegral_add_right _ (measurable_const.indicator hE₂m.compl),
            lintegral_indicator_const hE₂m.compl]
  have hcap : ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (W ω) ∂P' ≤ ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P' :=
    lintegral_mono fun ω => g3pl4_phiCapZ_le_phiZ γ δ U L s t (W ω)
  have e4 : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) ≤
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add (by linarith) hε4.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  constructor
  · refine g3pl4_inv_mul_le hu0 hut ?_
    calc ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P'
        ≤ ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (W ω) ∂P' + u * P' E₂ᶜ := hW2
      _ ≤ (g3plHonXZ Z Z' γ δ U L s t + u * P' Eᶜ + u * ENNReal.ofReal (ε / 4)) + u * P' E₂ᶜ := by
          rw [← hHon]; exact add_le_add hup le_rfl
      _ ≤ (g3plHonXZ Z Z' γ δ U L s t + u * ENNReal.ofReal (ε / 4) + u * ENNReal.ofReal (ε / 4)) +
            u * ENNReal.ofReal (ε / 4) := by gcongr
      _ = g3plHonXZ Z Z' γ δ U L s t + u * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) +
            ENNReal.ofReal (ε / 4)) := by ring
      _ ≤ g3plHonXZ Z Z' γ δ U L s t + u * ENNReal.ofReal ε := by gcongr
  · refine g3pl4_inv_mul_le hu0 hut ?_
    calc g3plHonXZ Z Z' γ δ U L s t = ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (Y₂ ω) ∂P' := hHon.symm
      _ ≤ ∫⁻ ω, g3pl4PhiCapZ Z Z' γ δ U L s t (W ω) ∂P' + u * P' Eᶜ +
            u * ENNReal.ofReal (ε / 4) := hdown
      _ ≤ ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P' + u * ENNReal.ofReal (ε / 4) +
            u * ENNReal.ofReal (ε / 4) := by gcongr
      _ = ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P' + u * (ENNReal.ofReal (ε / 4) +
            ENNReal.ofReal (ε / 4)) := by ring
      _ ≤ ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (W ω) ∂P' + u * ENNReal.ofReal ε := by
          gcongr
          exact le_trans (le_add_right le_rfl) e4

/-- **Uniform unscaled wedge comparison**: the window `δ` and the bound `U₀` depend only on `γ`
and `ε`, not on the zooms, the wedge sample or the cylinders. -/
theorem g3PlPhiUnscaledZ_unifAE {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ U : ℝ, 0 < U → U ≤ U₀ →
    ∀ (Z Z' : ℝ → FieldSample → ℝ → LawD),
    (∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2) →
    (∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x) →
    (∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2) →
    (∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x) →
    ∀ Gd Gd' : FieldSample → ℝ → Prop, G3ZqL.G3PlCapLocAE Z Z' γ Gd Gd' →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P', ∀ᵐ x ∂(qBoundaryMeasure γ (g3plUW γ X A ω)), Gd (g3plUW γ X A ω) x ∧ Gd' (g3plUW γ X A ω) (g3zPartner γ (g3plUW γ X A ω) x)) →
      (∀ V : Ω' → FieldSample, IsFreeGFFModConstH V P' →
        (∀ᵐ ω ∂P', V ω (foldedCircle 0 1) = 0) →
        ∀ᵐ ω ∂P', ∀ᵐ x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))), Gd (V ω + F2.logSingField (γ ^ 2)) x ∧ Gd' (V ω + F2.logSingField (γ ^ 2)) (g3zPartner γ (V ω + F2.logSingField (γ ^ 2)) x)) →
    ∀ s ∈ lawCyl, ∀ t ∈ lawCyl,
      ∀ᶠ L in (atTop : Filter ℝ),
        (ENNReal.ofReal U)⁻¹ * ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (g3plUW γ X A ω) ∂P' ≤
            (ENNReal.ofReal U)⁻¹ * g3plHonXZ Z Z' γ δ U L s t + ENNReal.ofReal ε ∧
          (ENNReal.ofReal U)⁻¹ * g3plHonXZ Z Z' γ δ U L s t ≤
            (ENNReal.ofReal U)⁻¹ * ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (g3plUW γ X A ω) ∂P' +
              ENNReal.ofReal ε := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨δ, hδ, hδ4, hint⟩ := g3pl4_hC_sepBad_small hγ hγ2 hε4
  obtain ⟨U₀, hU₀, hbad⟩ := g3pl_exists_U₀ hγ hγ2 (δ := 2 * δ) (by positivity) hε4
  refine ⟨δ, hδ, hδ4, U₀, hU₀, fun U hU hUU Z Z' hZm hZa hZm' hZa' Gd Gd' hLoc Ω' _ P' _ X A hX hA
    hXA hGW hGV s hs t ht => ?_⟩
  have hP := gffBase.prob
  obtain ⟨V, hV, hVn, hag⟩ := g3pl4_wedge_fcAgree_norm hγ hX hA hXA
  set Y₂ : Ω' → FieldSample := fun ω => V ω + F2.logSingField (γ ^ 2) with hY₂
  have hg₂ : ∀ᵐ ω ∂P', IsLQGGood γ (Y₂ ω) :=
    (g3pl4_ae_isAreaGood_logSing hγ hγ2 hV).mono fun ω h => h.1
  have hm₂ : Measurable fun ω => CoordsFull.coordsFull (Y₂ ω) :=
    measurable_pi_iff.2 fun n => (hV.measurable_coord _).add measurable_const
  have hgZ : ∀ᵐ ω ∂P', IsLQGGood γ (g3plUW γ X A ω) :=
    (g3pl4_ae_isAreaGood_Z hγ hγ2 hX hA hXA).mono fun ω h => h.1
  have hνr : ∀ᵐ ω ∂P', (qBoundaryMeasure γ (g3plUW γ X A ω)).restrict (Icc (-(1 / 2)) (1 / 2)) =
      (qBoundaryMeasure γ (Y₂ ω)).restrict (Icc (-(1 / 2)) (1 / 2)) := by
    filter_upwards [hgZ, hg₂, hag] with ω h1 h2 h3
    exact g3pl4_restrict_eq_of_agree h1 h2 h3
  have hgC : ∀ᵐ ω ∂gffBase.P, IsLQGGood γ (g3pField γ (g3wProf γ) ω) :=
    (ae_isAreaGood_g3pField hγ hγ2).mono fun ω h => h.1
  have hmC : Measurable fun ω => CoordsFull.coordsFull (g3pField γ (g3wProf γ) ω) := by
    refine measurable_pi_iff.2 fun n => ?_
    simp only [CoordsFull.coordsFull, g3pField, normField, Pi.add_apply]
    exact (measurable_const.add ((gffBase.gff.measurable_coord _).sub
      (gffBase.gff.measurable_coord _))).add measurable_const
  have hlaw := g3pl4_coordsLaw_eq hγ hV hVn
  have hSepδ : ∃ E : Set Ω', MeasurableSet E ∧
      (∀ ω ∈ E, g3pl4Sep γ δ (g3plUW γ X A ω)) ∧ P' Eᶜ ≤ ENNReal.ofReal (ε / 4) := by
    have htr := g3pl4_lintegral_bdry_eq (γ := γ) (measurable_g3pl4SepBad δ) hg₂ hgC
      hm₂.aemeasurable hmC.aemeasurable hlaw
    obtain ⟨E, hEm, hE, hEP⟩ := g3pl4_event_of_bad (measurable_g3pl4SepBad δ)
      (g3pl4SepBad_01 δ) hg₂ hm₂ (Q := fun ω => g3pl4Sep γ δ (g3plUW γ X A ω)) (by
        filter_upwards [hνr] with ω hr h0
        have hδ' : -(1 / 2 : ℝ) ≤ -δ := by linarith
        unfold g3pl4SepBad at h0
        split_ifs at h0 with hc
        · rw [g3pl4Sep, g3pl4_Icc_eq hr hδ' (by norm_num), g3pl4_Icc_eq hr (le_refl _) (by norm_num),
            g3pl4_Icc_eq hr (by norm_num) (by norm_num)]
          exact hc
        · exact absurd h0 one_ne_zero)
    exact ⟨E, hEm, hE, hEP.trans (htr.le.trans hint)⟩
  have hSmallU : ∀ U : ℝ, 0 < U → U ≤ U₀ →
      ∃ E : Set Ω', MeasurableSet E ∧
        (∀ ω ∈ E, ENNReal.ofReal U ≤ qBoundaryMeasure γ (g3plUW γ X A ω) (Icc (-δ) 0)) ∧
        P' Eᶜ ≤ ENNReal.ofReal (ε / 4) := by
    intro U hU hUU
    have htr := g3pl4_lintegral_bdry_eq (γ := γ) (measurable_g3plBadE (2 * δ) U) hg₂ hgC
      hm₂.aemeasurable hmC.aemeasurable hlaw
    have e2 : 2 * δ / 2 = δ := by ring
    obtain ⟨E, hEm, hE, hEP⟩ := g3pl4_event_of_bad (measurable_g3plBadE (2 * δ) U)
      (g3pl4BadE_01 (2 * δ) U) hg₂ hm₂
      (Q := fun ω => ENNReal.ofReal U ≤ qBoundaryMeasure γ (g3plUW γ X A ω) (Icc (-δ) 0)) (by
        filter_upwards [hνr] with ω hr h0
        have hδ' : -(1 / 2 : ℝ) ≤ -δ := by linarith
        unfold g3plBadE at h0
        rw [e2] at h0
        split_ifs at h0 with hc
        · exact absurd h0 one_ne_zero
        · push Not at hc
          rw [g3pl4_Icc_eq hr hδ' (by norm_num)]
          exact hc.1)
    exact ⟨E, hEm, hE, hEP.trans (htr.le.trans (hbad U hUU))⟩

  exact g3pl4_unscaled_atAE hZm hZa hZm' hZa' hLoc hγ hγ2 hX hA hXA hGW hGV
    (g3pl4_aemeasurable_phiCapZ_UW hZm hZa hZm' hZa' hγ hγ2 hX hA hXA (measurableSet_lawCyl hs)
      (measurableSet_lawCyl ht))
    (g3pl4_ae_isAreaGood_Z hγ hγ2 hX hA hXA) hs ht hε hδ hδ4 hU₀ hSepδ hSmallU U hU hUU

end G3ZqL
end R18
end QuantumZipper
