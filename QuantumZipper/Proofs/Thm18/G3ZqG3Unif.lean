import QuantumZipper.Proofs.Thm18.G3ZqG3XSide
import QuantumZipper.Proofs.Thm18.G3ZqG3Unsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: the headline with a zoom-independent window

The same chain as `g3UnscaledTransferZ_final` (D92), with the quantifiers ordered so that the
window `δ` and the bound `U₀` are chosen **before** the zooms: `U₀` depends only on `γ`, `ε`
(and not on the zoom pair, the limit laws, the wedge sample or the cylinders). This is possible
because in the originals `δ` and `U₀` come only from zoom-free inputs
(`g3pl4_hC_sepBad_small`, `g3pl_exists_U₀`, `g3pl_exists_m`).

* `g3pl4_unscaled_atZ`: `g3pl4_unscaled_of_inputsZ` at a given window `δ` and bound `U₀`;
* `g3PlPhiUnscaledZ_unif`, `g3plHonX_schemeC_Z_unif`: the two comparisons with `δ, U₀` chosen
  before the zooms;
* `g3UnscaledTransferZ_unif`: `∀ s t ε, ∃ U₀ > 0, ∀ U ∈ (0, U₀], ∀ Z Z'` (with hypotheses)
  `∀ μ ν` (with the G2 body), `∀` wedge sample, eventually in `L`, `U⁻¹ E Φ ≈ μ(s) ν(t)`.

Sheffield, arXiv:1012.4797, proof of Thm. 1.8, §5.4, pp. 70–72. Own bookkeeping copied from the
originals.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- **Uniform honest comparison**: `U₀` depends only on `γ, δ, ε`. -/
theorem g3plHonX_schemeC_Z_unif {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ} (hδ : 0 < δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ U : ℝ, 0 < U → U ≤ U₀ →
    ∀ (Z Z' : ℝ → FieldSample → ℝ → LawD),
    (∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2) →
    (∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2) →
    ∀ s ∈ lawCyl, ∀ t ∈ lawCyl,
      ∃ m : ℝ, 0 < m ∧ ∀ᶠ η in 𝓝[>] (0 : ℝ), ∃ M : ℝ, ∀ L : ℝ,
        ∀ i : G3Idx, i.1 = (δ, η, L) →
        ∃ w : gffBase.Ω × ℝ → ℝ,
          Measurable[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] w ∧
          (∀ p, 0 ≤ w p ∧ w p ≤ M) ∧
          (ENNReal.ofReal U)⁻¹ * g3plHonXZ Z Z' γ δ U L s t ≤
            ENNReal.ofReal (∫ p, (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩
              g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
              g3pMarg γ (g3wProf γ) i m).indicator w p ∂(g3pPalmLaw γ (g3wProf γ) i)) +
              ENNReal.ofReal ε ∧
          ENNReal.ofReal (∫ p, (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩
              g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
              g3pMarg γ (g3wProf γ) i m).indicator w p ∂(g3pPalmLaw γ (g3wProf γ) i)) ≤
            (ENNReal.ofReal U)⁻¹ * g3plHonXZ Z Z' γ δ U L s t + ENNReal.ofReal ε ∧
          |∫ p, (g3pMarg γ (g3wProf γ) i m).indicator w p ∂(g3pPalmLaw γ (g3wProf γ) i) - 1|
            ≤ ε := by
  obtain ⟨U₂, hU₂, hφ⟩ := g3pl_exists_U₀ hγ hγ2 hδ (e := ε / 8) (by positivity)
  refine ⟨U₂, hU₂, fun U hU hUle Z Z' hZm hZm' s hs t ht => ?_⟩
  obtain ⟨m, hm0, hmδ, hm16, hψ⟩ := g3pl_exists_m hγ hγ2 hδ hU (e := ε / 8) (by positivity)
  refine ⟨m, hm0, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hm0] with η hη
  refine ⟨(g3plZ γ δ).toReal / U, fun L i hi => ?_⟩
  have hiδ : i.δ = δ := by
    show i.1.1 = δ; rw [hi]
  have hiη : i.η = η := by
    show i.1.2.1 = η; rw [hi]
  have hiC : i.C = L := by
    show i.1.2.2 = L; rw [hi]
  subst hiδ hiη hiC
  set u := ENNReal.ofReal U with hu
  have hu0 : u ≠ 0 := (ENNReal.ofReal_pos.2 hU).ne'
  have hut : u ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨-, -, hM1, hM2⟩ := g3pl_core hγ hγ2 i hU hm0 hmδ hm16 hη.2.le s t
  obtain ⟨hK, hHK⟩ := g3pl_coreZ (Z := Z) (Z' := Z') hγ hγ2 i (U := U) hm0 hmδ hm16 hη.2.le s t
  have hBd : ∫⁻ ω, g3plBd i.δ U m (g3plV γ ω) ∂gffBase.P ≤ u * ENNReal.ofReal (ε / 4) := by
    have hV := aemeasurable_g3plV hγ hγ2
    have hm1 : AEMeasurable (fun ω => u * g3plBadE i.δ U (g3plV γ ω)) gffBase.P :=
      (measurable_const.mul (measurable_g3plBadE _ _)).comp_aemeasurable hV
    unfold g3plBd
    rw [lintegral_add_left' hm1, lintegral_const_mul' _ _ hut]
    have h8 : ENNReal.ofReal (ε / 4) = ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    rw [h8, mul_add]
    exact add_le_add (by gcongr; exact hφ U hUle) hψ
  set Bd := ∫⁻ ω, g3plBd i.δ U m (g3plV γ ω) ∂gffBase.P with hBdd
  have hsm := measurableSet_lawCyl hs
  have htm := measurableSet_lawCyl ht
  have hA : MeasurableSet (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩ g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
      g3pMarg γ (g3wProf γ) i m) :=
    (((measurable_g3pUfZ hZm γ _ i) hsm).inter
      ((measurable_g3pVfZ hZm' γ _ i) htm)).inter (measurableSet_g3pMarg γ _ i m)
  have hI1 := g3pl_integral_eq hγ hγ2 i hU hA
  have hI2 := g3pl_integral_eq hγ hγ2 i hU (measurableSet_g3pMarg γ (g3wProf γ) i m)
  rw [← hu] at hI1 hI2
  set K := ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩
      g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩ g3pMarg γ (g3wProf γ) i m) ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P with hKdef
  set Km := ∫⁻ ω, volume ({ℓ | (ω, ℓ) ∈ g3pMarg γ (g3wProf γ) i m ∩ g3plWin U} ∩
      Ioc 0 (g3pMass γ (g3wProf γ) i ω).toReal) ∂gffBase.P with hKmdef
  have hKKm : K ≤ Km := lintegral_mono fun ω => measure_mono fun ℓ hℓ =>
    ⟨⟨hℓ.1.1.2, hℓ.1.2⟩, hℓ.2⟩
  have hone : u⁻¹ * u = 1 := ENNReal.inv_mul_cancel hu0 hut
  have hKf : u⁻¹ * K ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hone ▸ (by gcongr; exact hKKm.trans hM2))
  have hKmf : u⁻¹ * Km ≤ 1 := hone ▸ (by gcongr)
  have hee : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hHX := g3plHonZ_eq_honXZ hZm hZm' (L := i.C) hγ hγ2 hδ hU hsm htm (Z := Z) (Z' := Z')
  rw [← hHX]
  refine ⟨g3plW γ i.δ U, measurable_g3plW _ _ _ i, fun p => ?_, ?_, ?_, ?_⟩
  · unfold g3plW
    have h0 : 0 ≤ (g3plZ γ i.δ).toReal / U := div_nonneg ENNReal.toReal_nonneg hU.le
    split_ifs
    · exact ⟨h0, le_rfl⟩
    · exact ⟨le_rfl, h0⟩
  · rw [hI1, ENNReal.ofReal_toReal hKf]
    calc u⁻¹ * g3plHonZ Z Z' γ i.δ U i.C s t
        ≤ u⁻¹ * K + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
          g3pl_arith hu0 hut hBd hHK le_self_add
      _ ≤ u⁻¹ * K + ENNReal.ofReal ε := by rw [add_assoc]; gcongr
  · rw [hI1, ENNReal.ofReal_toReal hKf]
    calc u⁻¹ * K ≤ u⁻¹ * g3plHonZ Z Z' γ i.δ U i.C s t + ENNReal.ofReal (ε / 4) :=
          g3pl_arith2 hu0 hut hBd hK
      _ ≤ u⁻¹ * g3plHonZ Z Z' γ i.δ U i.C s t + ENNReal.ofReal ε := by
          gcongr; linarith
  · have h1 : 1 ≤ u⁻¹ * Km + ENNReal.ofReal (ε / 4) := by
      calc (1 : ℝ≥0∞) = u⁻¹ * u := hone.symm
        _ ≤ u⁻¹ * (Km + Bd) := by gcongr
        _ = u⁻¹ * Km + u⁻¹ * Bd := mul_add _ _ _
        _ ≤ u⁻¹ * Km + ENNReal.ofReal (ε / 4) := by
          refine add_le_add le_rfl ?_
          calc u⁻¹ * Bd ≤ u⁻¹ * (u * ENNReal.ofReal (ε / 4)) := by gcongr
            _ = ENNReal.ofReal (ε / 4) := by rw [← mul_assoc, hone, one_mul]
    have hKmt : u⁻¹ * Km ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hKmf
    have r1 : (u⁻¹ * Km).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hKmf
    have r2 : 1 ≤ (u⁻¹ * Km).toReal + ε / 4 := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hKmt, ENNReal.ofReal_ne_top⟩) h1
      rwa [ENNReal.toReal_add hKmt ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_one] at this
    rw [hI2, abs_le]
    constructor <;> linarith

end R18
end QuantumZipper
