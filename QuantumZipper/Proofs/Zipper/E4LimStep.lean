import QuantumZipper.Proofs.Zipper.E4GridMain
import QuantumZipper.Proofs.Zipper.E4LimDCT
import QuantumZipper.Proofs.Zipper.EWire

/-!
# E4-LIM: the double limit of one side of E4-GRID

`handoff/E4.md`, item E4-LIM. `e4_lim_side`: for a generic "value" `Z ω x s ∈ [0,1]` (the field
factor of either side of E4-GRID), right-continuous in `s` at live times `s < T₀` and with a limit
`Zc ω x` as `s ↑ τ_x` (when `τ_x ≤ T₀`), the grid integral of `e4_grid_cap` converges as `n → ∞`
to the integral at the entrance time `σ_ε`, and these converge as `ε = ε_j ↓ 0` to the integral
of `1{τ_x ≤ T₀} Ψ(x, V^{τ_x}, W⁰) Zc ω x`. Iterated dominated convergence
(`tendsto_iter_lintegral`), with bound `ν(Icc(−δ,0))` (Z-FIN, `EWire.zfin`); the a.e.-measurability
of the grid integrands comes from the grid decomposition (`decomp_pt`) as in `e4_grid_cap`.

Own argument filling in the limiting step of Sheffield, arXiv:1012.4797, proof of Lemma 5.6
(pp. 66–68).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E4Grid

open B2 E1 CoordsFull PalmNorm

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

omit [IsProbabilityMeasure P] in
/-- The grid integrands are a.e.-measurable in `x` and their inner integrals in `ω`. -/
theorem grid_aemeas (hT : 0 ≤ T) {T₀ : ℝ} (hT₀ : 0 < T₀) (hB : IsBrownianReal B P) (δ ε : ℝ)
    (n : ℕ) {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (Z : Ω → ℝ → ℝ → ℝ≥0∞)
    (hmeas : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k))
    (haem : ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x
        ∂nuPalm κ T B X ϖ ω) P) :
    (∀ᵐ ω ∂P, AEMeasurable (fun x =>
      {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
        (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
          Z ω x (sG κ T T₀ B ε n ω x)) x) ((nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0))) ∧
    AEMeasurable (fun ω => ∫⁻ x in Icc (-δ) 0,
      {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
        (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
          Z ω x (sG κ T T₀ B ε n ω x)) x ∂nuPalm κ T B X ϖ ω) P := by
  have hm' : ∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x := by
    filter_upwards [hB.cont, hmeas] with ω hc hm k hk
    simp_rw [liveInd_eq hc hT hT₀.le k (fun x => Z ω x (tk n k))]
    exact hm k hk
  have hdec : ∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0),
      {x | sG κ T T₀ B ε n ω x < T₀ ∧ IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
        (fun x => Ψ x (Vstop κ T (sG κ T T₀ B ε n ω x) B ω, W0p κ T B ω) *
          Z ω x (sG κ T T₀ B ε n ω x)) x =
      ∑ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator
        (fun x => PsiK T₀ ε n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x := by
    filter_upwards [hB.cont] with ω hc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact decomp_pt hc hT hT₀ (Z ω) hx.2
  refine ⟨?_, ?_⟩
  · filter_upwards [hm', hdec] with ω hm hd
    exact (Finset.aemeasurable_fun_sum _ fun k hk => (hm k hk).aemeasurable).congr
      (hd.mono fun x hx => hx.symm)
  · refine (Finset.aemeasurable_fun_sum _ fun k hk => haem k hk).congr ?_
    filter_upwards [hm', hdec] with ω hm hd
    rw [← lintegral_finsetSum _ hm]
    exact (lintegral_congr_ae hd).symm

/-- `ℝ≥0∞`-product of two finite limits. -/
theorem tendsto_mul_ennreal {α : Type*} {l : Filter α} {a b : α → ℝ≥0∞} {a₀ b₀ : ℝ≥0∞}
    (ha : Tendsto a l (𝓝 a₀)) (hb : Tendsto b l (𝓝 b₀)) (ha₀ : a₀ ≠ ⊤) (hb₀ : b₀ ≠ ⊤) :
    Tendsto (fun t => a t * b t) l (𝓝 (a₀ * b₀)) :=
  ENNReal.Tendsto.mul ha (Or.inr hb₀) hb (Or.inr ha₀)

theorem ne_top_of_le_one' {a : ℝ≥0∞} (h : a ≤ 1) : a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top h

omit [MeasurableSpace Ω] in
/-- `tendsto_grid_ind` in the notation `sG` of E4-GRID. -/
theorem tendsto_grid_pt {ω : Ω} {x T₀ ε : ℝ} (hV : Continuous (Vr κ T B ω))
    (hx : x < Vr κ T B ω 0) (hT₀ : 0 < T₀) (hε : 0 < ε) {K : ℝ → ℝ → ℝ≥0∞}
    (hK : sigEps (Vr κ T B ω) T₀ ε x < T₀ → ContinuousWithinAt (K x)
      (Ici (sigEps (Vr κ T B ω) T₀ ε x)) (sigEps (Vr κ T B ω) T₀ ε x)) :
    Tendsto (fun n => {x | sG κ T T₀ B ε n ω x < T₀ ∧
        IsLive (Vr κ T B ω) (sG κ T T₀ B ε n ω x) x}.indicator
          (fun x => K x (sG κ T T₀ B ε n ω x)) x) atTop
      (𝓝 ({x | sigEps (Vr κ T B ω) T₀ ε x < T₀}.indicator
        (fun x => K x (sigEps (Vr κ T B ω) T₀ ε x)) x)) :=
  tendsto_grid_ind hV hx hT₀ hε hK

/-- **One side of E4-LIM.** -/
theorem e4_lim_side (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hϖ : IsNormalizer ϖ)
    {T₀ : ℝ} (hT₀ : 0 < T₀) {δ : ℝ} (hδ : 0 < δ) {ε : ℕ → ℝ} (hε0 : ∀ j, 0 < ε j)
    (hεt : Tendsto ε atTop (𝓝[>] 0))
    {Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞} (hΨ1 : ∀ x d, Ψ x d ≤ 1)
    (hΨc : ∀ᵐ ω ∂P, ∀ x, Continuous fun s => Ψ x (Vstop κ T s B ω, W0p κ T B ω))
    {Z : Ω → ℝ → ℝ → ℝ≥0∞} {Zc : Ω → ℝ → ℝ≥0∞} (hZ1 : ∀ ω x s, Z ω x s ≤ 1)
    (hZc1 : ∀ ω x, Zc ω x ≤ 1)
    (hmeas : ∀ j n, ∀ᵐ ω ∂P, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, Measurable fun x =>
      PsiK T₀ (ε j) n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k))
    (haem : ∀ j n, ∀ k ∈ Finset.range ⌈(2 : ℝ) ^ n * T₀⌉₊, AEMeasurable (fun ω =>
      ∫⁻ x in Icc (-δ) 0, {x | IsLive (Vr κ T B ω) (tk n k) x}.indicator (fun x =>
        PsiK T₀ (ε j) n k Ψ x (Vstop κ T (tk n k) B ω, W0p κ T B ω) * Z ω x (tk n k)) x
        ∂nuPalm κ T B X ϖ ω) P)
    (hcont : ∀ᵐ ω ∂P, ∀ x < 0, ∀ s, 0 ≤ s → s < T₀ → IsLive (Vr κ T B ω) s x →
      ContinuousWithinAt (Z ω x) (Ici s) s)
    (hcoll : ∀ᵐ ω ∂P, ∀ x < 0, ∀ τ, realHitTime (Vr κ T B ω) x = ENNReal.ofReal τ → τ ≤ T₀ →
      Tendsto (Z ω x) (𝓝[<] τ) (𝓝 (Zc ω x))) :
    (∀ j, Tendsto (fun n => ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
      {x | sG κ T T₀ B (ε j) n ω x < T₀ ∧
        IsLive (Vr κ T B ω) (sG κ T T₀ B (ε j) n ω x) x}.indicator
        (fun x => Ψ x (Vstop κ T (sG κ T T₀ B (ε j) n ω x) B ω, W0p κ T B ω) *
          Z ω x (sG κ T T₀ B (ε j) n ω x)) x ∂nuPalm κ T B X ϖ ω ∂P) atTop
      (𝓝 (∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | sigEps (Vr κ T B ω) T₀ (ε j) x < T₀}.indicator
          (fun x => Ψ x (Vstop κ T (sigEps (Vr κ T B ω) T₀ (ε j) x) B ω, W0p κ T B ω) *
            Z ω x (sigEps (Vr κ T B ω) T₀ (ε j) x)) x ∂nuPalm κ T B X ϖ ω ∂P))) ∧
    Tendsto (fun j => ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | sigEps (Vr κ T B ω) T₀ (ε j) x < T₀}.indicator
          (fun x => Ψ x (Vstop κ T (sigEps (Vr κ T B ω) T₀ (ε j) x) B ω, W0p κ T B ω) *
            Z ω x (sigEps (Vr κ T B ω) T₀ (ε j) x)) x ∂nuPalm κ T B X ϖ ω ∂P) atTop
      (𝓝 (∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
        {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}.indicator
          (fun x => Ψ x (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω) *
            Zc ω x) x ∂nuPalm κ T B X ϖ ω ∂P)) ∧
    AEMeasurable (fun ω => ∫⁻ x in Icc (-δ) 0,
        {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}.indicator
          (fun x => Ψ x (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω) *
            Zc ω x) x ∂nuPalm κ T B X ϖ ω) P ∧
    ∀ᵐ ω ∂P, AEMeasurable (fun x =>
        {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}.indicator
          (fun x => Ψ x (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω) *
            Zc ω x) x) ((nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0)) := by
  have hfin : ∀ ω, nuPalm κ T B X ϖ ω (Icc (-δ) 0) < ⊤ := fun ω =>
    qBoundaryMeasure_Icc_lt_top _ _ _ _
  have hint := (EWire.zfin hκ hκ4 hT hδ hB hX hind hϖ (ϖ := ϖ)).2.2.ne
  have hν0 := E1.ae_nuPalm_singleton_zero RevCouplingReg.revCouplingBoundaryMeasureRegular
    hκ hκ4 hT hB hX hind ϖ
  -- good points: `x ∈ [−δ, 0)`
  have hgood : ∀ᵐ ω ∂P, ∀ᵐ x ∂(nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0), x < 0 := by
    filter_upwards [hν0] with ω h0
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with x hx hx0
    exact lt_of_le_of_ne hx.2 hx0
  have hV : ∀ᵐ ω ∂P, Continuous (Vr κ T B ω) ∧ Vr κ T B ω 0 = 0 := by
    filter_upwards [hB.cont] with ω hc
    exact ⟨continuous_vrev (drive_continuous hc) T, vrev_zero hT.le⟩
  have step1 := fun j => tendsto_iter_lintegral (P := P) hfin hint
    (a := fun n ω x => {x | sG κ T T₀ B (ε j) n ω x < T₀ ∧
        IsLive (Vr κ T B ω) (sG κ T T₀ B (ε j) n ω x) x}.indicator
        (fun x => Ψ x (Vstop κ T (sG κ T T₀ B (ε j) n ω x) B ω, W0p κ T B ω) *
          Z ω x (sG κ T T₀ B (ε j) n ω x)) x)
    (b := fun ω x => {x | sigEps (Vr κ T B ω) T₀ (ε j) x < T₀}.indicator
          (fun x => Ψ x (Vstop κ T (sigEps (Vr κ T B ω) T₀ (ε j) x) B ω, W0p κ T B ω) *
            Z ω x (sigEps (Vr κ T B ω) T₀ (ε j) x)) x)
    (fun n ω x => indicator_apply_le' (fun _ => mul_le_one' (hΨ1 _ _) (hZ1 _ _ _))
      fun _ => zero_le)
    (ae_all_iff.2 fun n => (grid_aemeas hT.le hT₀ hB δ (ε j) n Z (hmeas j n) (haem j n)).1)
    (fun n => (grid_aemeas hT.le hT₀ hB δ (ε j) n Z (hmeas j n) (haem j n)).2) (by
      filter_upwards [hV, hΨc, hcont, hgood] with ω hVω hΨω hco hg
      filter_upwards [hg] with x hx
      have hx' : x < Vr κ T B ω 0 := by rw [hVω.2]; exact hx
      refine tendsto_grid_pt hVω.1 hx' hT₀ (hε0 j)
        (K := fun y s => Ψ y (Vstop κ T s B ω, W0p κ T B ω) * Z ω y s) fun hσ => ?_
      exact tendsto_mul_ennreal ((hΨω x).continuousWithinAt) (hco x hx _ (sigEps_nonneg hT₀.le)
        hσ (isLive_sigEps hVω.1 hx' hT₀.le (hε0 j))) (ne_top_of_le_one' (hΨ1 _ _))
        (ne_top_of_le_one' (hZ1 _ _ _)))
  refine ⟨fun j => (step1 j).1, ?_⟩
  refine tendsto_iter_lintegral (P := P) hfin hint
    (a := fun j ω x => {x | sigEps (Vr κ T B ω) T₀ (ε j) x < T₀}.indicator
          (fun x => Ψ x (Vstop κ T (sigEps (Vr κ T B ω) T₀ (ε j) x) B ω, W0p κ T B ω) *
            Z ω x (sigEps (Vr κ T B ω) T₀ (ε j) x)) x)
    (b := fun ω x => {x | realHitTime (Vr κ T B ω) x ≤ ENNReal.ofReal T₀}.indicator
          (fun x => Ψ x (Vstop κ T (realHitTime (Vr κ T B ω) x).toReal B ω, W0p κ T B ω) *
            Zc ω x) x)
    (fun j ω x => indicator_apply_le' (fun _ => mul_le_one' (hΨ1 _ _) (hZ1 _ _ _))
      fun _ => zero_le)
    (ae_all_iff.2 fun j => (step1 j).2.2) (fun j => (step1 j).2.1) ?_
  filter_upwards [hV, hΨc, hcoll, hgood] with ω hVω hΨω hco hg
  filter_upwards [hg] with x hx
  have hx' : x < Vr κ T B ω 0 := by rw [hVω.2]; exact hx
  refine (tendsto_sigEps_ind hVω.1 hx' hT₀
    (K := fun y s => Ψ y (Vstop κ T s B ω, W0p κ T B ω) * Z ω y s)
    (C := fun y => Ψ y (Vstop κ T (realHitTime (Vr κ T B ω) y).toReal B ω, W0p κ T B ω) *
      Zc ω y) fun τ hτ hτT => ?_).comp hεt
  have hτpos : 0 < τ := by
    have := RealLine.realHitTime_pos hVω.1 hx'.ne
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  simp only [hτ, ENNReal.toReal_ofReal hτpos.le]
  exact tendsto_mul_ennreal (((hΨω x).tendsto τ).mono_left nhdsWithin_le_nhds)
    (hco x hx τ hτ hτT) (ne_top_of_le_one' (hΨ1 _ _)) (ne_top_of_le_one' (hZc1 _ _))

end E4Grid
end QuantumZipper
