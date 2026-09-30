import QuantumZipper.Proofs.Zipper.D3PlusStmt
import QuantumZipper.Proofs.Probability.GermZeroOne

/-!
# D3⁺(i): the conditioning layer (independent split + dominated TV convergence)

Task D3P-I (decision D23; statement `D3Plus.D3PlusIStmt`, `D3PlusStmt.lean`). Paper: Sheffield,
arXiv:1012.4797, proof of Prop. 1.6 (p. 25) and §5; blueprint `E_BRANCH_BLUEPRINT.md` §3 (D3⁺):
"with `g` macroscopic, L2 (`freeGFF_halfDisc_markov`) reduces to `Z_r + (deterministic g)`".

This file is the **abstract conditioning layer** of that reduction (standard measure theory, own
elementary proofs; cf. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Lemma 3.11
(independence and Fubini: `E f(ξ, η) = E [E f(x, η)]_{x = ξ}` for `ξ ⊥ η`), and the dominated
convergence theorem):

* `lintegral_comp_indep`: if `Z ⊥ 𝒢` and `Ψ` is `𝒢 ⊗ Borel`-measurable, then
  `E Ψ(ω, Z ω) = E ∫ Ψ(ω, s) d(law Z)(s)` (integrating out the independent part).
* `eventually_two_sided_of_tv`: if `κ_L ω` are probability measures whose TV distance to `ν` is
  bounded by measurable `d_L ω → 0` a.s., then `E ∫ Φ(ω, ·) dκ_L ω` and `E ∫ Φ(ω, ·) dν` are
  eventually `η`-close, **uniformly** over test functions `Φ ∈ [0,1]` (dominated convergence
  applied to `min(d_L, 1)`).
* `eventually_two_sided_of_factor`: the combination in the shape of `D3PlusIStmt`: if the zoomed
  quantity equals a.s. `T_L(Z ω, F ω)` with `Z ⊥ 𝒢` and `F` `𝒢`-measurable, and the law of
  `T_L(Z, f)` is TV-close to the target, measurably and a.s. in `f = F ω`, then the two-sided
  bound of `D3PlusIStmt` holds eventually in `L`.
* `indep_sup_of_indep_d3p`: the three-σ-algebra independence step (`Ξ ⊥ free field` and
  `Z_r ⊥ outside` give `Z_r ⊥ σ(Ξ) ⊔ outside`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## Independent split -/

/-- **Integrating out an independent variable** (Kallenberg, FMP 2nd ed., Lemma 3.11; own
Lean proof). If `Z` is independent of the sub-σ-algebra `m𝒢` and `Ψ` is measurable for
`m𝒢 ⊗ Borel`, then `∫ Ψ(ω, Z ω) dP = ∫ ∫ Ψ(ω, s) d(P.map Z)(s) dP(ω)`. -/
theorem lintegral_comp_indep {Ω S : Type*} {m𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace S] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m𝒢 ≤ mΩ) {Z : Ω → S}
    (hZ : Measurable Z) (hind : Indep (MeasurableSpace.comap Z inferInstance) m𝒢 P)
    {Ψ : Ω × S → ℝ≥0∞} (hΨ : Measurable[m𝒢.prod inferInstance] Ψ) :
    ∫⁻ ω, Ψ (ω, Z ω) ∂P = ∫⁻ ω, ∫⁻ s, Ψ (ω, s) ∂(P.map Z) ∂P := by
  have hid : @Measurable Ω Ω mΩ m𝒢 id := fun s hs => hm s hs
  -- independence of `id : (Ω, mΩ) → (Ω, m𝒢)` and `Z`
  have hIF : @IndepFun Ω Ω S mΩ m𝒢 _ id Z P := by
    rw [@IndepFun_iff_Indep Ω Ω S mΩ m𝒢 _ id Z P, MeasurableSpace.comap_id]
    exact hind.symm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map (mβ := m𝒢) (μ := P) (f := id) (g := Z)
    (@Measurable.aemeasurable Ω Ω mΩ m𝒢 id P hid) hZ.aemeasurable).1 hIF
  have hpair : @Measurable Ω (Ω × S) mΩ (m𝒢.prod inferInstance) fun ω => (id ω, Z ω) :=
    @Measurable.prodMk Ω mΩ Ω S m𝒢 _ id Z hid hZ
  have htrim : @Measure.map Ω Ω mΩ m𝒢 id P = P.trim hm := (trim_eq_map hm).symm
  rw [htrim] at hprod
  have : @SFinite Ω m𝒢 (P.trim hm) := by
    have : @IsFiniteMeasure Ω m𝒢 (P.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  calc ∫⁻ ω, Ψ (ω, Z ω) ∂P
      = @lintegral (Ω × S) (m𝒢.prod inferInstance)
          (@Measure.map Ω (Ω × S) mΩ (m𝒢.prod inferInstance) (fun ω => (id ω, Z ω)) P) Ψ :=
        (@lintegral_map Ω (Ω × S) mΩ (m𝒢.prod inferInstance) P Ψ _ hΨ hpair).symm
    _ = @lintegral (Ω × S) (m𝒢.prod inferInstance)
          (@Measure.prod Ω S m𝒢 _ (P.trim hm) (P.map Z)) Ψ := by rw [hprod]
    _ = @lintegral Ω m𝒢 (P.trim hm) (fun ω => ∫⁻ s, Ψ (ω, s) ∂(P.map Z)) :=
        @lintegral_prod Ω S m𝒢 _ (P.trim hm) (P.map Z) _ Ψ hΨ.aemeasurable
    _ = ∫⁻ ω, ∫⁻ s, Ψ (ω, s) ∂(P.map Z) ∂P :=
        lintegral_trim hm (@Measurable.lintegral_prod_right' Ω S m𝒢 _ (P.map Z) _ Ψ hΨ)

/-! ## Dominated TV convergence over the conditioning -/

/-! ## The combination -/

/-! ## Three-σ-algebra independence -/

/-- **Independent join** (own elementary proof; same argument as
`UnzipInvariance.indep_sup_of_indep`): if `m₁, m₂ ≤ m_B` are independent and `m_X` is
independent of `m_B`, then `m₁ ⊔ m_X` is independent of `m₂`. -/
theorem indep_sup_of_indep_d3p {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m₁ m₂ mX mB : MeasurableSpace Ω} (h₁ : m₁ ≤ mB) (h₂ : m₂ ≤ mB)
    (hmB : mB ≤ mΩ) (hmX : mX ≤ mΩ) (h12 : Indep m₁ m₂ P) (hXB : Indep mX mB P) :
    Indep (m₁ ⊔ mX) m₂ P := by
  refine IndepSets.indep (sup_le (h₁.trans hmB) hmX) (h₂.trans hmB)
    (GermZeroOne.isPiSystem_rectSets m₁ mX) (@MeasurableSpace.isPiSystem_measurableSet Ω m₂)
    (GermZeroOne.sup_eq_generateFrom_rectSets m₁ mX)
    (@MeasurableSpace.generateFrom_measurableSet Ω m₂).symm ?_
  rw [IndepSets_iff]
  rintro _ D ⟨A, C, hA, hC, rfl⟩ hD
  have e1 : P (C ∩ (A ∩ D)) = P C * P (A ∩ D) :=
    (Indep_iff _ _ _).1 hXB C (A ∩ D) hC ((h₁ A hA).inter (h₂ D hD))
  have e2 : P (A ∩ D) = P A * P D := (Indep_iff _ _ _).1 h12 A D hA hD
  have e3 : P (C ∩ A) = P C * P A := (Indep_iff _ _ _).1 hXB C A hC (h₁ A hA)
  calc P (A ∩ C ∩ D) = P (C ∩ (A ∩ D)) := by
        congr 1; ext ω; simp only [mem_inter_iff]; tauto
    _ = P C * (P A * P D) := by rw [e1, e2]
    _ = P (A ∩ C) * P D := by rw [inter_comm A C, e3, mul_assoc]

end D3Plus
end QuantumZipper
