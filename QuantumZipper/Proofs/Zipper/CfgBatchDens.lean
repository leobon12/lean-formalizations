import QuantumZipper.Proofs.Zipper.E6FlowPair
import QuantumZipper.Proofs.Thm18.G1PairQuantLim
import QuantumZipper.Proofs.Thm18.G1PairLipRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-BATCH: the smoothed-pairing node `E6.CfgDensStmt` from a Lipschitz pairing modulus

Theorem 1.3, node E6 (Sheffield, arXiv:1012.4797, §5.4, pp. 70–72; the paper works with the
unzipped field as a distribution and never discusses the convergence of smoothed pairings).
`CfgDensStmt` asks, a.s. and for all `t ∈ [0,T]`, all dilations `b > 0` and all test functions `ρ`
at once, that the continuous-radius smoothed pairings of the unzipped `Γ⁰` field `x_t` with
`(b·)_* (ρ^±)` converge. At fixed `t` and fixed `ρ` this is PAIR-LIM (Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1 and Prop. 3.1). The quantifiers
over uncountably many `ρ` and `b` are removed by the deterministic theorem of G1-PAIR-QUANT
(`Thm18Asm.G1Rest.pairLimAll_of_count`, own elementary argument there): a regular sample with the
Lipschitz modulus `PairLipMod` (`|∫ (h_t − h_s) f| ≤ C L √(max t s)` for `L`-Lipschitz `f`
supported in a compact `K ⊆ ℍ`, the quantitative form of `h ∈ H^{-1/2}_loc`) has convergent
smoothed pairings with every dilated test function (`PairLimAll`).

* `densPair_of_pairLimAll`, `densPair_of_pairLipMod` (deterministic);
* `CfgPairLipStmt` (the new, quantitative, form of the node: a.s., for all `t ∈ [0,T]`,
  `PairLipMod x_t`; same shape as the G1 node `Thm18Asm.G1RestPairLipStmt` for wedge fields);
* `cfgDensStmt_of_pairLip`: `CfgPairLipStmt → CfgDensStmt` (regularity of `x_t` at all times is
  `RegUnif.ae_forall_isRegularSample`, proved);
* `CfgFirstModeStmt` and `cfgPairLip_of_firstMode`: the modulus from a first-circle-mode bound
  `O(τ^{-1/2})`, uniform in `t ∈ [0,T]`, by the deterministic `D3Plus.n2Lip_det1` (as
  `Thm18Asm.g1RestPairLip_of_firstMode` for G1 and `D3Plus.N2ZFirstModeStmt` for D3⁺; expected
  source of the bound: Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab.
  38 (2010), Prop. 2.1, for the pulled-back field);
* `cfgDensStmt_of_firstMode`: `CfgFirstModeStmt → CfgDensStmt`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

/-- `PairLimAll` (G1) contains `DensPair` at every positive dilation. -/
theorem densPair_of_pairLimAll {x : FieldSample} (h : Thm18Asm.G1Rest.PairLimAll x) {b : ℝ}
    (hb : 0 < b) : DensPair x b := fun ρ =>
  ⟨(h b hb ρ ρ.1 (Or.inl rfl)).2, (h b hb ρ (fun z => -ρ.1 z) (Or.inr rfl)).2⟩

/-- **Deterministic:** a regular sample with the Lipschitz pairing modulus has convergent
smoothed pairings with every dilated test function. -/
theorem densPair_of_pairLipMod {x : FieldSample} (hreg : IsRegularSample x)
    (h : Thm18Asm.G1Rest.PairLipMod x) {b : ℝ} (hb : 0 < b) : DensPair x b :=
  densPair_of_pairLimAll
    (Thm18Asm.G1Rest.pairLimAll_of_count hreg (Thm18Asm.G1Rest.countCond_of_pairLipMod h)) hb

variable {Ω : Type} [MeasurableSpace Ω]

/-- **Lipschitz pairing modulus of the unzipped `Γ⁰` field** (open; quantitative form of
`CfgDensStmt`): a.s., for every `t ∈ [0,T]`, the unzipped field `x_t` satisfies `PairLipMod`:
for each compact `K ⊆ ℍ` there are `C, δ > 0` with
`|∫ (evalReg x_t (fc(u,s)) − evalReg x_t (fc(u,s'))) f(u) du| ≤ C L √(max s s')` for all
`L`-Lipschitz `f` vanishing off `K` and `s, s' ∈ (0, δ)`. -/
def CfgPairLipStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → t ≤ T →
    Thm18Asm.G1Rest.PairLipMod (zipCapDown (Real.sqrt κ) t (cfg κ B X ω)).1

/-- **`CfgDensStmt` from the Lipschitz pairing modulus `CfgPairLipStmt`.** -/
theorem cfgDensStmt_of_pairLip {κ T : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (h : CfgPairLipStmt κ T P B X) : CfgDensStmt κ T P B X := by
  filter_upwards [h, RegUnif.ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind]
    with ω hω hRg t ht htT b hb
  exact densPair_of_pairLipMod (hRg t ht).1 (hω t ht htT) hb

/-- **First-circle-mode bound for the unzipped `Γ⁰` field** (open; probabilistic half of
`CfgPairLipStmt`): a.s., for every `t ∈ [0,T]` and compact `K ⊆ ℍ` there are `C`, `τ₀ > 0` with
`‖∫_0^{2π} ⟨x_t, σ_s(w + τ e^{iθ})⟩ e^{iθ} dθ‖ ≤ C / √τ` for `w ∈ K`, `τ ∈ (0, τ₀)`,
`s ∈ (0, τ)` (`σ_s(v)` the folded circle). -/
def CfgFirstModeStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → t ≤ T → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
    ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
      ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
          ((evalReg (zipCapDown (Real.sqrt κ) t (cfg κ B X ω)).1
              (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) : ℝ) : ℂ) *
            Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C / Real.sqrt τ

/-- **Deterministic:** a regular sample with the first-mode bound has the Lipschitz pairing
modulus (`D3Plus.n2Lip_det1`, as in `Thm18Asm.g1RestPairLip_of_firstMode`). -/
theorem pairLipMod_of_firstMode {x : FieldSample} (hreg : IsRegularSample x)
    (hmode : ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ w ∈ K, ∀ τ ∈ Ioo 0 τ₀, ∀ s ∈ Ioo 0 τ,
        ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
            ((evalReg x (foldedCircle (w + (τ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) s) :
              ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ C / Real.sqrt τ) :
    Thm18Asm.G1Rest.PairLipMod x := by
  obtain ⟨F, hFx⟩ := hreg
  intro K hK hKH
  obtain ⟨C, δ, hδ, hb⟩ := D3Plus.n2Lip_det1 hFx.1 hFx.2.2
    (Thm18Asm.G1PairLip.modeHyp_of_evalReg hFx hmode) hK hKH
  refine ⟨C, δ, hδ, fun L f hf hf0 t ht s hs => ?_⟩
  have e : (∫ u, (evalReg x (foldedCircle u t) - evalReg x (foldedCircle u s)) * f u) =
      ∫ u, (F (u, t) - F (u, s)) * f u := by
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    by_cases hu : u ∈ K
    · have hu' : u ∈ Hbar := show (0 : ℝ) ≤ u.im from le_of_lt (hKH hu)
      simp only
      rw [hFx.evalReg_fc_of_mem hu' ht.1, hFx.evalReg_fc_of_mem hu' hs.1]
    · simp [hf0 u hu]
  show |∫ u, (evalReg x (foldedCircle u t) - evalReg x (foldedCircle u s)) * f u| ≤ _
  rw [e]
  exact hb L f hf hf0 t ht s hs

/-- **`CfgPairLipStmt` from the first-mode node.** -/
theorem cfgPairLip_of_firstMode {κ T : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (h : CfgFirstModeStmt κ T P B X) : CfgPairLipStmt κ T P B X := by
  filter_upwards [h, RegUnif.ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind]
    with ω hω hRg t ht htT
  exact pairLipMod_of_firstMode (hRg t ht).1 (hω t ht htT)

/-- **`CfgDensStmt` from the first-mode node.** -/
theorem cfgDensStmt_of_firstMode {κ T : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (h : CfgFirstModeStmt κ T P B X) : CfgDensStmt κ T P B X :=
  cfgDensStmt_of_pairLip hB hX hind (cfgPairLip_of_firstMode hB hX hind h)

end QuantumZipper.E6
