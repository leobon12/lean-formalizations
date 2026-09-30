import QuantumZipper.Proofs.Section5.Prop16DomCoupleGlue
import QuantumZipper.Proofs.Section5.Prop16PalmMask

/-!
# Proposition 1.6, DOM-a in a general Hilbert space (decision D34)

`DomMarkovCurveStmt` (`Prop16DomCoupleNodes.lean`) asks for the mixed vectors `e μ` and the
harmonic curve `H` inside the free feature space `HkE` itself. The localised construction chosen
in D34 (the remainder of the mixed Riesz vector orthogonal to the closed span of the *local*
annulus features, `K3.remVec`, `MixedProj.lean`, glued with the free annulus features) naturally
lives in a product `HkE × GradSpace D`. This file states DOM-a with an arbitrary separable
Hilbert space `E` containing an isometric copy `ι : HkE →ₗᵢ E` of the free space:

* `DomMarkovCurveEStmt D c d` — `DomMarkovCurveStmt` with `E`, `ι` (the old statement is the case
  `E = HkE`, `ι = id`: `domMarkovCurveEStmt_of_domMarkovCurve`);
* `prop16MixedFreeLocCoupling_of_domMarkovE` — the whole-domain coupling
  `Prop16MixedFreeLocCouplingStmt` from it (with DOM-b `gaussContFubini_holds`, proved);
* `theorem1_6_of_domMarkovE_palmMask` — Proposition 1.6 from it and the masked Palm nodes.

Construction (own argument, as `prop16MixedFreeLocCoupling_of_nodes`): one isonormal process `W`
on `E`; the free field is `μ ↦ W(ι v̂_μ)` (an isonormal process on `HkE` after composing with the
isometry), the mixed field `μ ↦ W(e μ)`, and on a dyadic circle `σ` inside `D ∪ (a,b)`,
`Y σ = X σ − X ρ₀ − W(k_σ)` with `k_σ = ι(v̂_σ − v̂_{ρ₀}) − e σ = ∫ H dσ` weakly.
Source for the mathematics: Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007),
Thm 2.17 (domain Markov property), mixed form.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace NNReal

namespace QuantumZipper

namespace Prop16Asm

open GFFExist LQGDimension.ExistAsm

/-- **DOM-a, general Hilbert form.** A separable Hilbert space `E` with an isometric copy
`ι : HkE →ₗᵢ E` of the free space, vectors `e μ ∈ E` with Gram matrix `dualCov D V` on
`V`-admissible measures (`V = mixedSpace D (realSet (Icc c d))`), a unit admissible reference
`ρ₀`, and a curve `H : ℂ → E`, Lipschitz on the compact subsets of `D ∪ (c,d)`, with
`ι(v̂_μ − v̂_{ρ₀}) − e μ = ∫ H dμ` weakly for every unit measure `μ`, admissible for both fields,
carried by a compact subset of `D ∪ (c,d)`. -/
def DomMarkovCurveEStmt (D : Set ℂ) (c d : ℝ) : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℝ E) (_ : CompleteSpace E)
    (_ : TopologicalSpace.SeparableSpace E) (ι : HkE →ₗᵢ[ℝ] E) (e : Measure ℂ → E)
    (ρ₀ : AdmT) (H : ℂ → E),
    ρ₀.1 Set.univ = 1 ∧
    (∀ μ ν : Measure ℂ, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ →
      IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) ν →
      ⟪e μ, e ν⟫ = dualCov D (mixedSpace D (realSet (Icc c d))) μ ν) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ D ∪ realSet (Ioo c d) →
      ∃ C : ℝ≥0, LipschitzOnWith C H K) ∧
    ∀ μ : AdmT, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ.1 →
      μ.1 Set.univ = 1 →
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ D ∪ realSet (Ioo c d) ∧ μ.1 Kᶜ = 0) →
      ∀ x : E, ⟪ι (freeVec μ - freeVec ρ₀) - e μ.1, x⟫ = ∫ z, ⟪H z, x⟫ ∂μ.1

/-! ### The mixed field realized in a general Hilbert space -/

open Classical in
/-- The mixed field realized from an isonormal process on `E` and vectors `e`. -/
def domYE {E : Type*} (D : Set ℂ) (c d : ℝ) (e : Measure ℂ → E) (W : E → (ℕ → ℝ) → ℝ) :
    (ℕ → ℝ) → FieldSample := fun ω μ =>
  if IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ then W (e μ) ω else 0

theorem domYE_apply {E : Type*} {D : Set ℂ} {c d : ℝ} {e : Measure ℂ → E}
    {W : E → (ℕ → ℝ) → ℝ} (μ : Measure ℂ)
    (h : IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ) (ω : ℕ → ℝ) :
    domYE D c d e W ω μ = W (e μ) ω := by
  simp [domYE, h]

section RealE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {W : E → (ℕ → ℝ) → ℝ} (hWm : ∀ x, Measurable (W x))
  (hW : ∀ {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * W (τ i) ω) (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) stdP)

include hW in
/-- A combination with zero vector vanishes a.s. -/
theorem domE_ae_eq_zero {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ)
    (h0 : ∑ i, a i • τ i = 0) : ∀ᵐ ω ∂stdP, ∑ i, a i * W (τ i) ω = 0 := by
  have hlaw := hW τ a
  rw [h0] at hlaw
  have h0' : (‖(0 : E)‖ ^ 2).toNNReal = 0 := by simp
  refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
  rw [hlaw.map_eq, h0', gaussianReal_zero_var, ae_dirac_eq]
  exact Filter.eventually_pure.2 rfl

include hWm hW in
/-- The realized mixed field is a mixed GFF when the Gram matrix of `e` is `dualCov`. -/
theorem domYE_isMixedGFF {D : Set ℂ} {c d : ℝ} {e : Measure ℂ → E}
    (he : ∀ μ ν : Measure ℂ, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ →
      IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) ν →
      ⟪e μ, e ν⟫ = dualCov D (mixedSpace D (realSet (Icc c d))) μ ν) :
    IsMixedGFF D (realSet (Icc c d)) (domYE D c d e W) stdP := by
  have hYe : ∀ (μ : Measure ℂ) (h : IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ),
      (fun ω => domYE D c d e W ω μ) = W (e μ) := fun μ h => funext (domYE_apply μ h)
  have hlaw1 : ∀ x : E, HasLaw (W x) (gaussianReal 0 (‖x‖ ^ 2).toNNReal) stdP := fun x =>
    gs_comb4 (v := id) hW ![x, x, x, x] ![1, 0, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]) _ (by simp [Fin.sum_univ_four])
  refine ⟨fun μ => ?_, ?_, fun μ hμ => ?_, fun μ ν hμ hν => ?_⟩
  · by_cases h : IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ
    · rw [hYe μ h]; exact hWm _
    · have : (fun ω => domYE D c d e W ω μ) = fun _ => 0 := by funext ω; simp [domYE, h]
      rw [this]; exact measurable_const
  · refine gs_isGaussianProcess (fun μ => ?_) fun I a => ?_
    · rw [hYe μ.1 μ.2]; exact (hWm _).aemeasurable
    · have ee : (fun ω => ∑ i : I, a i * domYE D c d e W ω i.1.1) =
          fun ω => ∑ i : I, a i * W (e i.1.1) ω := by
        funext ω
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [domYE_apply _ i.1.2]
      exact ⟨_, ee ▸ hW (fun i : I => e i.1.1) a⟩
  · rw [hYe μ hμ]; exact gs_integral_eq_zero (hlaw1 _)
  · rw [hYe μ hμ, hYe ν hν, ← he μ ν hμ hν]
    refine gs_cov_eq (hlaw1 _) (hlaw1 _) ?_
    exact gs_comb4 (v := id) hW ![e μ, e ν, e μ, e μ] ![1, 1, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]) _ (by simp [Fin.sum_univ_four])

end RealE

/-- The isonormal process on `E`, composed with a linear isometry `ι : F →ₗᵢ E`, is isonormal on
`F`. -/
theorem hasLaw_comp_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (ι : F →ₗᵢ[ℝ] E) {W : E → (ℕ → ℝ) → ℝ}
    (hW : ∀ {ι' : Type} [Fintype ι'] (τ : ι' → E) (a : ι' → ℝ),
      HasLaw (fun ω => ∑ i, a i * W (τ i) ω) (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal)
        stdP)
    {ι' : Type} [Fintype ι'] (τ : ι' → F) (a : ι' → ℝ) :
    HasLaw (fun ω => ∑ i, a i * W (ι (τ i)) ω)
      (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) stdP := by
  have h := hW (fun i => ι (τ i)) a
  have hn : ‖∑ i, a i • ι (τ i)‖ = ‖∑ i, a i • τ i‖ := by
    rw [← ι.norm_map (∑ i, a i • τ i), map_sum]
    simp only [map_smul]
  rwa [hn] at h

/-- **The domain Markov coupling of Proposition 1.6 from the general DOM-a.** -/
theorem prop16MixedFreeLocCoupling_of_domMarkovE
    (hA : ∀ (D : Set ℂ) (c d : ℝ), K3.Prop16Geometry D c d → DomMarkovCurveEStmt D c d) :
    Prop16MixedFreeLocCouplingStmt := by
  intro D c d a b hgeo hab hca hbd
  obtain ⟨E, _, _, _, _, ι, e, ρ₀, Hc, -, hGram, hLip, hcurve⟩ := hA D c d hgeo
  obtain ⟨O, hOo, hOV⟩ := locGood_exists_open hgeo le_rfl le_rfl
  obtain ⟨W', hW'o, hW'V⟩ := locGood_exists_open hgeo hca hbd
  obtain ⟨Wv, hWm, hW⟩ := gs_process_hilbert E id
  have hW2 : ∀ {ι' : Type} [Fintype ι'] (τ : ι' → E) (a : ι' → ℝ),
      HasLaw (fun ω => ∑ i, a i * Wv (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) stdP := fun τ a => hW τ a
  set Wf : HkE → (ℕ → ℝ) → ℝ := fun x => Wv (ι x) with hWfdef
  have hWfm : ∀ x, Measurable (Wf x) := fun x => hWm _
  have hWf : ∀ {ι' : Type} [Fintype ι'] (τ : ι' → HkE) (a : ι' → ℝ),
      HasLaw (fun ω => ∑ i, a i * Wf (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) stdP := fun τ a =>
    hasLaw_comp_isometry ι hW2 τ a
  obtain ⟨G, hGc, hGF⟩ := gaussContFubini_holds stdP Wv O Hc hOo hWm hW2
    (fun K hK hKs => hLip K hK (hOV ▸ hKs))
  set V := D ∪ realSet (Ioo a b) with hVdef
  have hVsub : V ⊆ D ∪ realSet (Ioo c d) :=
    union_subset_union_right _ (realSet_mono_dom (Ioo_subset_Ioo hca hbd))
  let I := {m : Measure ℂ // m ∈ locCircSet V}
  have : Countable I := (locCircSet_countable V).to_subtype
  have hper : ∀ i : I, ∀ᵐ ω ∂stdP, domYE D c d e Wv ω i.1 =
      domX Wf ω i.1 + ∫ z, (-(G ω z) - domX Wf ω ρ₀.1) ∂i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    have hw := CircleCont.dyadicRoundC_mem_Hbar hz n
    have hr := radius_pos k
    set σ := foldedCircle (dyadicRoundC n z) (radius k) with hσ
    have hσH : IsAdmissibleH σ := isAdmissibleH_foldedCircle hw hr
    have hsubW : closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ W' := fun u hu => by
      have hu' := hsub hu
      rw [← hW'V] at hu'
      exact hu'.1
    have hσD : IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) σ :=
      locGood_isAdmissible_circle hgeo hca hbd hW'o hW'V hw hr hsubW
    have hKc := Prop16Area.G.isCompact_closedBall_inter_Hbar (dyadicRoundC n z) (radius k)
    have hσK := K3.foldedCircle_compl_eq_zero hw hr.le
    have hKV : closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ D ∪ realSet (Ioo c d) :=
      hsub.trans hVsub
    have hKO : closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ O ∩ Hbar := hOV ▸ hKV
    have hk := hcurve ⟨σ, hσH⟩ hσD measure_univ ⟨_, hKc, hKV, hσK⟩
    have h1 := domE_ae_eq_zero hW2
      ![e σ, ι (freeVec ⟨σ, hσH⟩), ι (freeVec ρ₀), ι (freeVec ⟨σ, hσH⟩ - freeVec ρ₀) - e σ]
      ![1, -1, 1, 1] (by simp [Fin.sum_univ_four, map_sub]; abel)
    have h2 := hGF σ inferInstance ⟨_, hKc, hKO, hσK⟩ _ hk
    filter_upwards [h1, h2] with ω h1 h2
    have hInt : Integrable (G ω) σ :=
      integrable_of_continuousOn_carrier hKc ((hGc ω).mono hKO) hσK
    have hn : Integrable (fun z => -(G ω z)) σ := hInt.neg
    have hI : ∫ z, (-(G ω z) - domX Wf ω ρ₀.1) ∂σ =
        -(Wv (ι (freeVec ⟨σ, hσH⟩ - freeVec ρ₀) - e σ) ω) - domX Wf ω ρ₀.1 := by
      rw [integral_sub hn (integrable_const _), integral_neg, integral_const, probReal_univ,
        one_smul, h2]
    show domYE D c d e Wv ω σ = domX Wf ω σ + ∫ z, (-(G ω z) - domX Wf ω ρ₀.1) ∂σ
    rw [hI, domYE_apply _ hσD, domX_apply _ hσH, domX_apply _ ρ₀.2]
    simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h1
    simp only [hWfdef]
    linarith
  have hall : ∀ᵐ ω ∂stdP, ∀ i : I, domYE D c d e Wv ω i.1 =
      domX Wf ω i.1 + ∫ z, (-(G ω z) - domX Wf ω ρ₀.1) ∂i.1 := ae_all_iff.2 hper
  refine ⟨ℕ → ℝ, inferInstance, inferInstance, stdP, domYE D c d e Wv, domX Wf, inferInstance,
    domYE_isMixedGFF hWm hW2 hGram, domX_isFree hWfm hWf, ?_⟩
  filter_upwards [hall] with ω hω
  refine ⟨fun z => -(G ω z) - domX Wf ω ρ₀.1, ?_, fun n k z hz hsub => ?_⟩
  · exact ((hGc ω).mono (hOV ▸ hVsub)).neg.sub continuousOn_const
  · exact hω ⟨_, n, k, z, hz, hsub, rfl⟩

/-- **Proposition 1.6 from the general DOM-a and the masked Palm-zoom nodes B′, C′.** -/
theorem theorem1_6_of_domMarkovE_palmMask
    (hA : ∀ (D : Set ℂ) (c d : ℝ), K3.Prop16Geometry D c d → DomMarkovCurveEStmt D c d)
    (hId : Prop16PalmIdMaskStmt) (hFix : Prop16FixedZoomMaskStmt) : theorem1_6 :=
  theorem1_6_of_palmMask (prop16MixedFreeLocCoupling_of_domMarkovE hA) hId hFix

end Prop16Asm

end QuantumZipper
