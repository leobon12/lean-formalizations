import QuantumZipper.Proofs.Zipper.T13Hard3Heart
import QuantumZipper.Proofs.Zipper.D3PlusN2Bridge
import QuantumZipper.Proofs.Zipper.D3PlusLSCCInd

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3-PATH, part 1: the total-variation bookkeeping of the strong Markov route

Abstract measure-theoretic core of `D3Plus.hitPathInd_of_trans`. If a pair `(ρ, T)` agrees,
off an event `D`, with `(R, σ + G)` where `σ` is independent of `(R, G)` and `G ≥ 0`, then

`d_TV(law (ρ, T), law ρ ⊗ law T) ≤ 3 P(D) + ∫∫ d_TV(μ_σ * δ_g, μ_σ * δ_{g'}) dν(g) dν(g')`

(`D3Plus.tv_pair_indep_le`), where `μ_σ = law σ` and `ν = law G`. This is the coupling
inequality plus the convexity of total variation under mixtures (`TV.tvDist_bind_le`,
Levin–Peres–Wilmer §4.1); own elementary bookkeeping (standard).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- TV of two images of a product measure `μ₀ ⊗ μs` is at most the `μ₀`-average of the TV of
the sections. -/
theorem tv_map_prod_le_path {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ0 : Measure α) [IsProbabilityMeasure μ0] (μs : Measure ℝ) [IsProbabilityMeasure μs]
    {f1 f2 : α × ℝ → β} (h1 : Measurable f1) (h2 : Measurable f2) :
    TV.tvDist ((μ0.prod μs).map f1) ((μ0.prod μs).map f2) ≤
      ∫⁻ a, TV.tvDist (μs.map fun x => f1 (a, x)) (μs.map fun x => f2 (a, x)) ∂μ0 := by
  have key : ∀ f : α × ℝ → β, Measurable f → (μ0.prod μs).map f =
      μ0.bind (Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f) := by
    intro f hf
    rw [← Measure.compProd_const, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hf]
  have kap : ∀ f : α × ℝ → β, Measurable f → ∀ a,
      Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f a = μs.map fun x => f (a, x) := by
    intro f hf a
    rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
    rfl
  haveI : IsMarkovKernel (Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f1) :=
    Kernel.IsMarkovKernel.map _ h1
  haveI : IsMarkovKernel (Kernel.map (Kernel.id ×ₖ Kernel.const α μs) f2) :=
    Kernel.IsMarkovKernel.map _ h2
  rw [key f1 h1, key f2 h2]
  refine (TV.tvDist_bind_le _ _).trans (le_of_eq ?_)
  simp only [kap f1 h1, kap f2 h2]

/-- Translation TV kernel integrand (with the shifts clamped at `0`). -/
def transTV (μs : Measure ℝ) (g g' : ℝ) : ℝ≥0∞ :=
  TV.tvDist (μs.map fun x => x + max g 0) (μs.map fun x => x + max g' 0)

/-- **The TV bookkeeping.** -/
theorem tv_pair_indep_le {Ω B : Type*} [MeasurableSpace Ω] [MeasurableSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P] {ρ : Ω → B} {T σ G : Ω → ℝ} {R : Ω → B}
    (hρ : AEMeasurable ρ P) (hT : AEMeasurable T P) (hσ : Measurable σ) (hR : Measurable R)
    (hG : Measurable G) (hG0 : ∀ ω, 0 ≤ G ω) (hind : IndepFun σ (fun ω => (R ω, G ω)) P)
    (D : Set Ω) (hD : ∀ᵐ ω ∂P, ω ∉ D → ρ ω = R ω ∧ T ω = σ ω + G ω) :
    TV.tvDist (P.map fun ω => (ρ ω, T ω)) ((P.map ρ).prod (P.map T)) ≤
      3 * P D + ∫⁻ q, transTV (P.map σ) q.1.2 q.2.2
        ∂((P.map fun ω => (R ω, G ω)).prod (P.map fun ω => (R ω, G ω))) := by
  set U : Ω → B × ℝ := fun ω => (R ω, G ω) with hUdef
  have hU : Measurable U := hR.prodMk hG
  set ν := P.map U
  set μs := P.map σ
  have hTs : Measurable fun ω => σ ω + G ω := hσ.add hG
  -- step 1: coupling
  have e1 : TV.tvDist (P.map fun ω => (ρ ω, T ω)) (P.map fun ω => (R ω, σ ω + G ω)) ≤ P D :=
    tvDist_map_le_of_ae_eq_off (hρ.prodMk hT) (hR.prodMk hTs).aemeasurable D
      (hD.mono fun ω h hω => by rw [(h hω).1, (h hω).2])
  have e3a : TV.tvDist (P.map ρ) (P.map R) ≤ P D :=
    tvDist_map_le_of_ae_eq_off hρ hR.aemeasurable D (hD.mono fun ω h hω => (h hω).1)
  have e3b : TV.tvDist (P.map T) (P.map fun ω => σ ω + G ω) ≤ P D :=
    tvDist_map_le_of_ae_eq_off hT hTs.aemeasurable D (hD.mono fun ω h hω => (h hω).2)
  have e3 : TV.tvDist ((P.map R).prod (P.map fun ω => σ ω + G ω)) ((P.map ρ).prod (P.map T))
      ≤ 2 * P D := by
    rw [TV.tvDist_comm]
    refine (lscc_tvDist_prod_le).trans ?_
    rw [two_mul]; exact add_le_add e3a e3b
  -- step 2: the mixture identities
  have hjoint : P.map (fun ω => (U ω, σ ω)) = ν.prod μs := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hσ.aemeasurable).1 hind.symm]
  set f1 : ((B × ℝ) × (B × ℝ)) × ℝ → B × ℝ := fun p => (p.1.1.1, p.2 + max p.1.1.2 0)
  set f2 : ((B × ℝ) × (B × ℝ)) × ℝ → B × ℝ := fun p => (p.1.1.1, p.2 + max p.1.2.2 0)
  have hf1 : Measurable f1 :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.add ((measurable_snd.comp (measurable_fst.comp measurable_fst)).max
        measurable_const))
  have hf2 : Measurable f2 :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.add ((measurable_snd.comp (measurable_snd.comp measurable_fst)).max
        measurable_const))
  have hGm : ∀ ω, max (G ω) 0 = G ω := fun ω => max_eq_left (hG0 ω)
  have id1 : ((ν.prod ν).prod μs).map f1 = P.map fun ω => (R ω, σ ω + G ω) := by
    have hfac : f1 = (fun p : (B × ℝ) × ℝ => (p.1.1, p.2 + max p.1.2 0)) ∘
        (fun p : ((B × ℝ) × (B × ℝ)) × ℝ => (p.1.1, p.2)) := rfl
    have hg : Measurable (fun p : (B × ℝ) × ℝ => (p.1.1, p.2 + max p.1.2 0)) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.add ((measurable_snd.comp measurable_fst).max measurable_const))
    have hh : Measurable (fun p : ((B × ℝ) × (B × ℝ)) × ℝ => (p.1.1, p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    rw [hfac, ← Measure.map_map hg hh]
    have : ((ν.prod ν).prod μs).map (fun p : ((B × ℝ) × (B × ℝ)) × ℝ => (p.1.1, p.2)) =
        ν.prod μs := by
      rw [show (fun p : ((B × ℝ) × (B × ℝ)) × ℝ => (p.1.1, p.2)) = Prod.map Prod.fst id
        from rfl, ← Measure.map_prod_map _ _ measurable_fst measurable_id,
        Measure.map_fst_prod, measure_univ, one_smul, Measure.map_id]
    rw [this, ← hjoint, Measure.map_map hg (hU.prodMk hσ)]
    congr 1
    funext ω
    simp only [Function.comp_apply, U, hGm, add_comm]
  have id2 : ((ν.prod ν).prod μs).map f2 = (P.map R).prod (P.map fun ω => σ ω + G ω) := by
    have hg2 : Measurable (fun p : (B × ℝ) × ℝ => p.2 + max p.1.2 0) :=
      measurable_snd.add ((measurable_snd.comp measurable_fst).max measurable_const)
    have hR' : P.map R = ν.map Prod.fst := by
      rw [Measure.map_map measurable_fst hU]; rfl
    have hT' : (P.map fun ω => σ ω + G ω) = (ν.prod μs).map
        (fun p : (B × ℝ) × ℝ => p.2 + max p.1.2 0) := by
      rw [← hjoint, Measure.map_map hg2 (hU.prodMk hσ)]
      congr 1
      funext ω
      simp only [Function.comp_apply, U, hGm, add_comm]
    rw [hR', hT', Measure.map_prod_map _ _ measurable_fst hg2, ← Measure.prodAssoc_prod,
      Measure.map_map (measurable_fst.prodMap hg2) MeasurableEquiv.prodAssoc.measurable]
    rfl
  have e2 : TV.tvDist (P.map fun ω => (R ω, σ ω + G ω))
      ((P.map R).prod (P.map fun ω => σ ω + G ω)) ≤
      ∫⁻ q, transTV μs q.1.2 q.2.2 ∂(ν.prod ν) := by
    rw [← id1, ← id2]
    refine (tv_map_prod_le_path _ _ hf1 hf2).trans (lintegral_mono fun q => ?_)
    have hmk : Measurable (Prod.mk q.1.1 : ℝ → B × ℝ) := measurable_prodMk_left
    have h1 : (μs.map fun x => f1 (q, x)) = (μs.map fun x => x + max q.1.2 0).map
        (Prod.mk q.1.1) := by
      rw [Measure.map_map hmk (measurable_add_const _)]; rfl
    have h2 : (μs.map fun x => f2 (q, x)) = (μs.map fun x => x + max q.2.2 0).map
        (Prod.mk q.1.1) := by
      rw [Measure.map_map hmk (measurable_add_const _)]; rfl
    rw [h1, h2]
    exact TV.tvDist_map_le hmk
  calc TV.tvDist (P.map fun ω => (ρ ω, T ω)) ((P.map ρ).prod (P.map T))
      ≤ TV.tvDist (P.map fun ω => (ρ ω, T ω)) (P.map fun ω => (R ω, σ ω + G ω)) +
        (TV.tvDist (P.map fun ω => (R ω, σ ω + G ω))
          ((P.map R).prod (P.map fun ω => σ ω + G ω)) +
         TV.tvDist ((P.map R).prod (P.map fun ω => σ ω + G ω)) ((P.map ρ).prod (P.map T))) := by
        exact TV.tvDist_triangle.trans (add_le_add le_rfl TV.tvDist_triangle)
    _ ≤ P D + (∫⁻ q, transTV μs q.1.2 q.2.2 ∂(ν.prod ν) + 2 * P D) :=
        add_le_add e1 (add_le_add e2 e3)
    _ = 3 * P D + ∫⁻ q, transTV μs q.1.2 q.2.2 ∂(ν.prod ν) := by ring

end D3Plus
end QuantumZipper
