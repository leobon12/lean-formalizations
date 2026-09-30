import QuantumZipper.Proofs.Thm18.G2RootRPalmAsm
import QuantumZipper.Proofs.Thm18.G2RootXModel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `R(x)` side: the fixed-point zoom from D3⁺(i), and the headline

The twin of `G2RootXModel.lean`: `G2RootRModelStmt γ ν` (D3⁺ data at a fixed point `y` of
region 2, with the conditioning variables `g3PalmCondR` = outside coordinates, cut length
`ν_h[0, y − κ]` and truncation level `M`, all a.s. equal to a `condSigma`-measurable map),
`g2RootRFixStmt_of_model` (the conditioning layer: D3⁺(i) with `Φ(ω, y) = 1_{G''}(V ω) 1_S(y)`),
and `g2FixMixRootRStmt_of_nodes`. Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **Model node at a fixed point, `R` side** (D3⁺ data for the Palm field at `x ∈` region 2; Sheffield,
arXiv:1012.4797, proof of Prop. 1.6, p. 25, and Prop. 5.5, p. 65; pattern of
`Prop17PalmCModelStmt`). -/
def G2RootRModelStmt (γ : ℝ) (μ : Measure LawD) : Prop :=
  ∀ s ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ x : ℝ,
    (∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η ∧ |x - i₀.t₂| + m < i₀.r₂) →
    ∃ (r : ℝ) (ρ₀ : Measure ℂ) (X' : Ω₀ → FieldSample) (g : Ω₀ → ℂ → ℝ) (R : ℕ)
      (S : Set ((ℕ → ℝ) × (TestFun H → ℝ))) (Ω' : Type) (_ : MeasurableSpace Ω')
      (P' : Measure Ω') (Y' : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ Y' P' ∧
      D3Plus.Setup γ γ r ρ₀ gffBase.P X' (fun _ : Ω₀ => ()) g ∧ MeasurableSet S ∧
      ∫⁻ ω', S.indicator 1 (D3Plus.locFieldFull R (Y' ω')) ∂P' = ENNReal.ofReal (μ.real s) ∧
      (∀ i : G3Idx, i.1.1 = δ → i.1.2.1 = η → ∃ V : Ω₀ → CondR i,
        Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) X' r] V ∧
        ∀ᵐ ω ∂gffBase.P, V ω = g3PalmCondR γ i κ x ω) ∧
      (∀ C : ℝ, AEMeasurable (g3ModelData γ r C ρ₀ R X' g) gffBase.P) ∧
      Tendsto (fun C : ℝ => gffBase.P {ω | ¬ (zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ↔
        g3ModelData γ r C ρ₀ R X' g ω ∈ S)}) atTop (𝓝 0)

/-- **The fixed-point zoom from D3⁺(i) and the model node, `R` side.** -/
theorem g2RootRFixStmt_of_model {γ : ℝ} {μ : Measure LawD} (hI : D3Plus.D3PlusIStmtRich)
    (hM : G2RootRModelStmt γ μ) : G2RootRFixStmt γ μ := by
  classical
  intro s hs δ η m κ hκ hκm x ε hε
  by_cases hx : ∃ i₀ : G3Idx, i₀.1.1 = δ ∧ i₀.1.2.1 = η ∧ |x - i₀.t₂| + m < i₀.r₂
  swap
  · refine Eventually.of_forall fun C i hi G' hG' => ?_
    have hmi : ¬ |x - i.t₂| + m < i.r₂ := fun h => hx ⟨i, by rw [hi], by rw [hi], h⟩
    have he : ∀ s', g3PalmEvR γ i s' m κ G' x = ∅ := fun s' =>
      eq_empty_of_forall_notMem fun ω hω => hmi hω.2.1
    rw [he, he, measure_empty]
    simpa using hε.le
  obtain ⟨i₀, hδ₀, hη₀, hx₀⟩ := hx
  obtain ⟨r, ρ₀, X', g, R, S, Ω', _, P', Y', hP', hW, hSet, hS, hμ, hV, hMdl, hlim⟩ :=
    hM s hs δ η m κ hκ hκm x ⟨i₀, hδ₀, hη₀, hx₀⟩
  have := hP'
  set c : ℝ := μ.real s with hc
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by positivity)
  filter_upwards [hI γ γ r ρ₀ gffBase.P X' (fun _ : Ω₀ => ()) g P' Y' hSet hW R _ hη2,
    hlim.eventually (gt_mem_nhds hη2)] with C hC hCl i hi G' hG'
  obtain ⟨ht, hr⟩ := G3Idx.t₂_r₂_congr (i := i) (i' := i₀) (by rw [hi, hη₀])
  have hmi : |x - i.t₂| + m < i.r₂ := by rw [ht, hr]; exact hx₀
  have hiC : i.C = C := by rw [G3Idx.C, hi]
  obtain ⟨V, hVm, hVae⟩ := hV i (by rw [hi]) (by rw [hi])
  set W := g3PalmCondR γ i κ x with hWdef
  set Mdl := g3ModelData γ r C ρ₀ R X' g with hMdef
  set Δ : Set Ω₀ := {ω | ¬ (zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ↔ Mdl ω ∈ S)} with hΔ
  have hA : g3PalmEvR γ i s m κ G' x =
      {ω | zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ∧ W ω ∈ G'} := by
    ext ω; simp only [g3PalmEvR, mem_setOf_eq, hiC, hmi, true_and, hWdef, g3PalmCondR]
  have hB : g3PalmEvR γ i univ m κ G' x = {ω | W ω ∈ G'} := by
    ext ω; simp only [g3PalmEvR, mem_setOf_eq, mem_univ, hmi, true_and, hWdef, g3PalmCondR]
  set A' : Set Ω₀ := {ω | V ω ∈ G'} ∩ {ω | Mdl ω ∈ S} with hA'
  set B' : Set Ω₀ := {ω | V ω ∈ G'} with hB'
  have hVmeas : Measurable V := hVm.mono (D3Plus.condSigma_le hSet) le_rfl
  have hB'm : MeasurableSet B' := hVmeas hG'
  have hPB : gffBase.P {ω | W ω ∈ G'} = gffBase.P B' :=
    measure_congr (hVae.mono fun ω h => by
      change (W ω ∈ G') = (V ω ∈ G'); rw [h])
  have hAle : gffBase.P {ω | zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ∧ W ω ∈ G'} ≤
      gffBase.P A' + gffBase.P Δ := by
    refine (measure_mono_ae (hVae.mono fun ω h hω => ?_)).trans (measure_union_le _ _)
    obtain ⟨h1, h2⟩ := hω
    by_cases hm : Mdl ω ∈ S
    · exact Or.inl ⟨show V ω ∈ G' by rw [h]; exact h2, hm⟩
    · exact Or.inr fun hiff => hm (hiff.1 h1)
  have hA'le : gffBase.P A' ≤
      gffBase.P {ω | zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ∧ W ω ∈ G'} +
        gffBase.P Δ := by
    refine (measure_mono_ae (hVae.mono fun ω h hω => ?_)).trans (measure_union_le _ _)
    obtain ⟨h1, h2⟩ := hω
    by_cases hz : zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s
    · exact Or.inl ⟨hz, show W ω ∈ G' by rw [← h]; exact h1⟩
    · exact Or.inr fun hiff => hz (hiff.2 h2)
  -- D3⁺(i) with `Φ(ω, y) = 1_{G'}(V ω) 1_S(y)`
  set Φ : Ω₀ × ((ℕ → ℝ) × (TestFun H → ℝ)) → ℝ≥0∞ :=
    fun p => G'.indicator 1 (V p.1) * S.indicator 1 p.2 with hΦ
  have hΦm : Measurable[(D3Plus.condSigma (fun _ : Ω₀ => ()) X' r).prod inferInstance] Φ := by
    letI : MeasurableSpace Ω₀ := D3Plus.condSigma (fun _ : Ω₀ => ()) X' r
    exact ((measurable_one.indicator hG').comp (hVm.comp measurable_fst)).mul
      ((measurable_one.indicator hS).comp measurable_snd)
  have hΦ1 : ∀ p, Φ p ≤ 1 := fun p => by
    simp only [hΦ]
    exact mul_le_one' (indicator_le (fun _ _ => le_rfl) _) (indicator_le (fun _ _ => le_rfl) _)
  have hD := hC Φ hΦm hΦ1
  simp only at hD
  have hL : ∫⁻ ω, Φ (ω, Mdl ω) ∂gffBase.P = gffBase.P A' := by
    have e : (fun ω => Φ (ω, Mdl ω)) = A'.indicator 1 := by
      funext ω
      simp only [hΦ, hA', indicator, mem_inter_iff, mem_ofPred_eq, Pi.one_apply]
      split_ifs <;> simp_all
    rw [e]
    exact lintegral_indicator_one₀ (hB'm.nullMeasurableSet.inter ((hMdl C).nullMeasurable hS))
  have hind : ∀ ω, G'.indicator (1 : CondR i → ℝ≥0∞) (V ω) =
      B'.indicator 1 ω := fun ω => by
    simp only [indicator, hB', mem_ofPred_eq, Pi.one_apply]
  have hR : ∫⁻ ω, ∫⁻ ω', Φ (ω, D3Plus.locFieldFull R (Y' ω')) ∂P' ∂gffBase.P =
      ENNReal.ofReal c * gffBase.P B' := by
    have e : ∀ ω, ∫⁻ ω', Φ (ω, D3Plus.locFieldFull R (Y' ω')) ∂P' =
        B'.indicator 1 ω * ENNReal.ofReal c := fun ω => by
      simp only [hΦ]
      rw [lintegral_const_mul' _ _ (by unfold indicator; split_ifs <;> simp), hμ, hind]
    simp_rw [e]
    rw [lintegral_mul_const _ (measurable_one.indicator hB'm), lintegral_indicator_one hB'm,
      mul_comm]
  have hD1 : gffBase.P A' ≤ ENNReal.ofReal c * gffBase.P B' + ENNReal.ofReal (ε / 2) := by
    rw [← hL, ← hR]; exact hD.1
  have hD2 : ENNReal.ofReal c * gffBase.P B' ≤ gffBase.P A' + ENNReal.ofReal (ε / 2) := by
    rw [← hL, ← hR]; exact hD.2
  rw [hA, hB, hPB]
  set E : ℝ≥0∞ := ENNReal.ofReal (ε / 2) + gffBase.P Δ with hE
  have hΔfin : gffBase.P Δ ≠ ⊤ := (hCl.trans ENNReal.ofReal_lt_top).ne
  have hEfin : E ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hΔfin⟩
  have h1 : gffBase.P {ω | zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ∧ W ω ∈ G'} ≤
      ENNReal.ofReal c * gffBase.P B' + E :=
    calc _ ≤ gffBase.P A' + gffBase.P Δ := hAle
      _ ≤ (ENNReal.ofReal c * gffBase.P B' + ENNReal.ofReal (ε / 2)) + gffBase.P Δ := by gcongr
      _ = _ := by rw [hE, add_assoc]
  have h2 : ENNReal.ofReal c * gffBase.P B' ≤
      gffBase.P {ω | zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ∧ W ω ∈ G'} + E :=
    calc _ ≤ gffBase.P A' + ENNReal.ofReal (ε / 2) := hD2
      _ ≤ (gffBase.P {ω | zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ∧ W ω ∈ G'} +
          gffBase.P Δ) + ENNReal.ofReal (ε / 2) := by gcongr
      _ = _ := by rw [hE]; ring
  have hEle : E.toReal ≤ ε := by
    rw [hE, ENNReal.toReal_add ENNReal.ofReal_ne_top hΔfin, ENNReal.toReal_ofReal (by positivity)]
    have : (gffBase.P Δ).toReal ≤ ε / 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hCl.le
    linarith
  exact (abs_toReal_sub_le_of_two_sided hc0 (measure_ne_top _ _) (measure_ne_top _ _) hEfin
    h1 h2).trans hEle

/-- **`G2FixMixRootRStmt` from D3⁺(i) (N2 form) and the named `R`-side nodes.** -/
theorem g2FixMixRootRStmt_of_nodes {γ : ℝ} (hγ : 0 < γ) {ν : Measure LawD}
    [IsProbabilityMeasure ν] (hN2 : D3Plus.D3PlusIN2RichStmt) (hP : G2RootRPalmIdStmt γ)
    (hM : G2RootRModelStmt γ ν) (hS : G2RootRLenSmoothStmt γ) : G2FixMixRootRStmt γ ν :=
  g2FixMixRootRStmt_of_cut hS
    (g2RootRCutStmt_of_palm hγ hP (g2RootRFixStmt_of_model (D3Plus.d3PlusIRich_of_N2 hN2) hM))

/-- **`G2FixMixStmt` (both sides) from D3⁺(i) (N2 form) and the named nodes.** -/
theorem g2FixMixStmt_of_rootNodes {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ ν : Measure LawD}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hMX : G2RootXModelStmt γ μ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hMR : G2RootRModelStmt γ ν) (hSR : G2RootRLenSmoothStmt γ) :
    G2FixMixStmt γ :=
  g2FixMixStmt_of_root hγ hγ2 (g2FixMixRootXStmt_of_nodes hγ hγ2 hN2 hPX hMX hSX)
    (g2FixMixRootRStmt_of_nodes hγ hN2 hPR hMR hSR)

end Thm18Asm
end QuantumZipper
