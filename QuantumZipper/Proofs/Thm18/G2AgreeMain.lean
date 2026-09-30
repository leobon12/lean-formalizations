import QuantumZipper.Proofs.Thm18.G2AgreeBasic
import QuantumZipper.Proofs.NonVacuityWedgeUncond

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: reduction to regularity/goodness and the conditioning maps

`g2RootXAgreeStmt_of_nodes`, `g2RootRAgreeStmt_of_nodes`: for every `γ`-wedge `Y'` (law of
`lawOf Y'`: `μ = g2WedgeLaw P' Y'`) the identification nodes of `G2RootSetup.lean` hold, given

* `G2PalmRegGoodStmt γ`: for `0 < |x| < 1`, a.s. the Palm field `h_x = normField γ (X₀ + ψ_x)`
  is `γ`-good (`IsLQGGood`) and regular (`evalReg = raw value`) at every folded dyadic circle
  inside `B(x, |x|)`;
* `G2RootXCondStmt γ` / `G2RootRCondStmt γ`: the conditioning variables (`g3PalmCond`,
  `g3PalmCondR`) are a.s. equal to maps measurable for the D3⁺ conditioning σ-algebra of the
  free field outside `B(x, κ/2)` (clause (b) of the Agree nodes, verbatim, per index `i`).

Clause (a) is `g2Agree_wedge_mass`, clause (c) `aemeasurable_g3ModelData_g2` (`G2AgreeBasic`);
clause (d) is `g2Agree_tendsto` below: on the regularity event the zoomed Palm field agrees with
the D3⁺ model field inside `B(0, κ/2)` (`g2_zoomField_eq_zoomModel`: the correction constant of
`g2Corr` is exact); on the goodness event the zoomed field has a global area limit and
`canonProxy = canonical`; when the model's local scale lies in `(0, (κ/2)/(R+1))`,
`E5.locFieldFull_canonical_eq_canonicalOn` identifies the global canonical data of the zoom with
the local canonical model data; the bad-scale probability tends to `0` by D3⁺(iii)
(`D3Plus.d3PlusIII_tendsto_prob`, proved). This is the route of `Prop17PalmCAgree.lean`.

`g2FixMixStmt_of_agreeLeaves`: `G2FixMixStmt γ` from D3⁺(i) (N2 form), the Palm identities, the
length smoothing, and the three nodes above (the wedge is supplied by
`NonVacuity.exists_wedge_indep_BM_uncond_prob_uncond`).

Sources: Sheffield, arXiv:1012.4797, Prop. 5.5 (p. 65) and proof of Thm. 1.8 (p. 71);
Duplantier–Sheffield, arXiv:0808.1560, §3.3 (Palm description `h + γ(−log|x − ·|)`). The formal
arguments are own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw

local notation "Ω₀" => gffBase.Ω

/-! ## The remaining nodes -/

/-- **Regularity and goodness of the Palm field** (Duplantier–Sheffield, arXiv:0808.1560, §3.3:
under the rooted measure at `x`, `h` is a free-boundary GFF plus `γ(−log|x − ·|)` plus a function
harmonic near `x`; such fields are a.s. `γ`-good, `LogSingGood`, and regular at fixed circles). -/
def G2PalmRegGoodStmt (γ : ℝ) : Prop :=
  ∀ x : ℝ, x ≠ 0 → |x| < 1 → ∀ᵐ ω ∂gffBase.P, IsLQGGood γ (normField γ (xPalm γ x) ω) ∧
    ∀ (n k : ℕ) (z : ℂ), ‖dyadicRoundC n z‖ + radius k < |x| →
      evalReg (normField γ (xPalm γ x) ω)
          ((foldedCircle (dyadicRoundC n z) (radius k)).map (· + (x : ℂ))) =
        normField γ (xPalm γ x) ω ((foldedCircle (dyadicRoundC n z) (radius k)).map (· + (x : ℂ)))

/-- **Conditioning map, `x` side** (clause (b) of `G2RootXAgreeStmt`): the outside coordinates and
the cut length `ν_h[x + κ, 0]` of the Palm field only read the field outside `B(x, κ/2)`
(Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 65). -/
def G2RootXCondStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (m κ x : ℝ), 0 < κ → κ < m → |x - i.t₁| + m < i.r₁ →
    ∃ V : Ω₀ → (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ,
      Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X x) (κ / 2)] V ∧
      ∀ᵐ ω ∂gffBase.P, V ω = g3PalmCond γ i κ x ω

/-- **Conditioning map, `R` side** (clause (b) of `G2RootRAgreeStmt`: outside coordinates, cut
length `ν_h[0, y − κ]`, truncation mass). -/
def G2RootRCondStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (m κ y : ℝ), 0 < κ → κ < m → |y - i.t₂| + m < i.r₂ →
    ∃ V : Ω₀ → CondR i,
      Measurable[D3Plus.condSigma (fun _ : Ω₀ => ()) (palmCField gffBase.X y) (κ / 2)] V ∧
      ∀ᵐ ω ∂gffBase.P, V ω = g3PalmCondR γ i κ y ω

/-! ## Clause (d) -/

/-- **Clause (d).** -/
theorem g2Agree_tendsto {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hRG : G2PalmRegGoodStmt γ)
    {x r : ℝ} (hr : 0 < r) (hxr : r < |x|) (hx1 : |x| + r < 1) {s : Set LawD} {R : ℕ}
    (hR : ∀ Z : FieldSample, D3Plus.locFieldFull R Z ∈ s ↔ lawOf Z ∈ s) :
    Tendsto (fun C : ℝ => gffBase.P {ω | ¬ (zoomLaw γ C (normField γ (xPalm γ x) ω) x ∈ s ↔
      g3ModelData γ r C (palmCRho refS x) R (palmCField gffBase.X x)
        (fun _ => g2Corr γ x) ω ∈ s)}) atTop (𝓝 0) := by
  have hS := g2Root_setup hγ hγ2 hr hxr hx1
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hxr; linarith
  set sc : ℝ → Ω₀ → ℝ := fun C ω => scaleParamOn γ (D3Plus.zoomModel γ γ C (palmCRho refS x)
    (palmCField gffBase.X x ω) (g2Corr γ x)) (D3Plus.halfDisc r) with hsc
  have hε : (0 : ℝ) < r / ((R : ℝ) + 1) := by positivity
  have hbad : Tendsto (fun C => gffBase.P {ω | ¬ (0 < sc C ω ∧ sc C ω < r / ((R : ℝ) + 1))})
      atTop (𝓝 0) := by
    refine tendsto_of_seq_tendsto fun Cs hCs => ?_
    exact D3Plus.d3PlusIII_tendsto_prob hS hCs hε fun n =>
      (Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm hS (Cs n)).nullMeasurable
        measurableSet_Ioo.compl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad
    (fun _ => bot_le) fun C => measure_mono_ae ?_
  filter_upwards [hRG x hx0 (by linarith)] with ω hω hE
  obtain ⟨hg, hreg⟩ := hω
  by_contra hb
  obtain ⟨hpos, hlt⟩ := hb
  apply hE
  set y := zoomField γ C (normField γ (xPalm γ x) ω) x with hy
  set y' := D3Plus.zoomModel γ γ C (palmCRho refS x) (palmCField gffBase.X x ω) (g2Corr γ x)
    with hy'
  have hag : D3Plus.AgreeNear y y' r := fun n k z hz =>
    g2_zoomField_eq_zoomModel γ C x ω _ (radius_pos k) (hreg n k z (hz.trans hxr))
  have hyg : IsLQGGood γ y := (hg.translate x).addConst (C / γ)
  have hvag := Prop16Area.G.isVagueLimitOn_H_of_good hyg
  have hlt' : scaleParamOn γ y' (D3Plus.halfDisc r) * ((R : ℝ) + 1) < r := by
    have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
    exact (lt_div_iff₀ hR1).1 hlt
  obtain ⟨-, hloc⟩ := E5.locFieldFull_canonical_eq_canonicalOn hag hvag hpos hlt'
  show lawOf (canonProxy γ y) ∈ s ↔
    D3Plus.locFieldFull R (canonicalOn γ y' (D3Plus.halfDisc r)) ∈ s
  rw [canonProxy_eq_canonical_of_good hyg, ← hR, hloc]

/-! ## The identification nodes -/

/-- **`G2RootXAgreeStmt` from the regularity/goodness node and the conditioning node.** -/
theorem g2RootXAgreeStmt_of_nodes {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y' : Ω' → FieldSample}
    (hW : IsQuantumWedge γ γ Y' P') (hRG : G2PalmRegGoodStmt γ) (hC : G2RootXCondStmt γ) :
    G2RootXAgreeStmt γ (g2WedgeLaw P' Y') := by
  intro s hs δ η m κ hκ hκm x hx
  obtain ⟨R, hR⟩ := exists_nat_locFieldFull_lawCyl hs
  have hsm := measurableSet_lawCyl hs
  obtain ⟨i₀, hδ₀, hη₀, hx₀⟩ := hx
  have h1 := i₀.hη; have h2 := i₀.hηδ; have h3 := i₀.hδ
  have hlt : |x - i₀.t₁| < i₀.r₁ - m := by linarith
  rw [abs_lt] at hlt
  unfold G3Idx.t₁ G3Idx.r₁ at hlt
  have hxneg : x < 0 := by linarith
  have hxa : |x| = -x := abs_of_neg hxneg
  have hxr : κ / 2 < |x| := by rw [hxa]; linarith
  have hx1 : |x| + κ / 2 < 1 := by rw [hxa]; linarith
  refine ⟨R, s, Ω', _, P', Y', inferInstance, hW, hsm, g2Agree_wedge_mass hγ hγ2 hW hsm hR,
    fun i hi1 hi2 => ?_, fun C => aemeasurable_g3ModelData_g2 hγ hγ2 (by positivity) hxr hx1 C R,
    g2Agree_tendsto hγ hγ2 hRG (by positivity) hxr hx1 hR⟩
  obtain ⟨ht, hr⟩ := G3Idx.t₁_r₁_congr (i := i) (i' := i₀) (by rw [hi1, hδ₀]) (by rw [hi2, hη₀])
  exact hC i m κ x hκ hκm (by rw [ht, hr]; exact hx₀)

/-- **`G2RootRAgreeStmt` from the regularity/goodness node and the conditioning node.** -/
theorem g2RootRAgreeStmt_of_nodes {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y' : Ω' → FieldSample}
    (hW : IsQuantumWedge γ γ Y' P') (hRG : G2PalmRegGoodStmt γ) (hC : G2RootRCondStmt γ) :
    G2RootRAgreeStmt γ (g2WedgeLaw P' Y') := by
  intro s hs δ η m κ hκ hκm x hx
  obtain ⟨R, hR⟩ := exists_nat_locFieldFull_lawCyl hs
  have hsm := measurableSet_lawCyl hs
  obtain ⟨i₀, hδ₀, hη₀, hx₀⟩ := hx
  have h1 := i₀.hη; have h2 := i₀.hηδ; have h3 := i₀.hδ
  have hlt : |x - i₀.t₂| < i₀.r₂ - m := by linarith
  rw [abs_lt] at hlt
  unfold G3Idx.t₂ G3Idx.r₂ at hlt
  have hxpos : 0 < x := by linarith
  have hxa : |x| = x := abs_of_pos hxpos
  have hxr : κ / 2 < |x| := by rw [hxa]; linarith
  have hx1 : |x| + κ / 2 < 1 := by rw [hxa]; linarith
  refine ⟨R, s, Ω', _, P', Y', inferInstance, hW, hsm, g2Agree_wedge_mass hγ hγ2 hW hsm hR,
    fun i _ hi2 => ?_, fun C => aemeasurable_g3ModelData_g2 hγ hγ2 (by positivity) hxr hx1 C R,
    g2Agree_tendsto hγ hγ2 hRG (by positivity) hxr hx1 hR⟩
  obtain ⟨ht, hr⟩ := G3Idx.t₂_r₂_congr (i := i) (i' := i₀) (by rw [hi2, hη₀])
  exact hC i m κ x hκ hκm (by rw [ht, hr]; exact hx₀)

/-- **`G2FixMixStmt` from D3⁺(i) (N2 form), the Palm identities, the length smoothing, the
regularity/goodness node and the two conditioning nodes.** -/
theorem g2FixMixStmt_of_agreeLeaves {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hSR : G2RootRLenSmoothStmt γ)
    (hRG : G2PalmRegGoodStmt γ) (hCX : G2RootXCondStmt γ) (hCR : G2RootRCondStmt γ) :
    G2FixMixStmt γ := by
  obtain ⟨Ω', _, P', Y', -, hP', hW, -, -, -⟩ :=
    NonVacuity.exists_wedge_indep_BM_uncond_prob_uncond hγ hγ2 (gamma_lt_Qc' hγ hγ2)
  have := hP'
  exact g2FixMixStmt_of_agreeNodes hγ hγ2 hN2 hPX (g2RootXAgreeStmt_of_nodes hγ hγ2 hW hRG hCX)
    hSX hPR (g2RootRAgreeStmt_of_nodes hγ hγ2 hW hRG hCR) hSR

end Thm18Asm
end QuantumZipper
