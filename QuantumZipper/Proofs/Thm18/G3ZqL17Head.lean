import QuantumZipper.Proofs.Thm18.G3ZqL16Unsc
import QuantumZipper.Proofs.Thm18.G3ZqG3LRegG
import QuantumZipper.Proofs.Thm18.G3ZqG3Unif

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (17): the unscaled transfer with pulled-back goodness at typical points only

Copies of G3ZqG3LRegG (`g3pRegLocXZ_of_ballG`, `g3pRegLocRZ_of_ballG`) and G3ZqG3LHeadG
(`g3UnscaledTransferZ_ballG`, `g3UnscaledTransfer_map`) in which the goodness of the scheme `B`/`C`
fields is asked only at their Palm points (a.e. for the Palm laws `g3pPalmLaw`, which is all the
region locality uses), and that of the unscaled wedge and of `V + logSing` only at `ν`-a.e. point
and its length partner (`G3ZqL16Unsc`). Headline `g3UnscaledTransfer_mapAE`. Own bookkeeping
(Sheffield, arXiv:1012.4797, §5.4, pp. 70–72).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

local notation "Ω₀" => gffBase.Ω

namespace G3ZqL

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

/-- **Region locality at `x` from ball locality.** -/
theorem g3pRegLocXZ_of_ballAE (hZm : ∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2)
    {γ : ℝ} {Gd : FieldSample → ℝ → Prop} (hB : G3ZqZoomBallLocGZ Z Gd)
    (gf : ℝ → ℂ → ℝ)
    (hgood : ∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (gf i.η) i),
      Gd (g3pField γ (gf i.η) p.1) (g3pX γ (gf i.η) i p)) :
    G3pRegLocXZ Z γ gf := by
  intro s hs δ η m hm ε hε
  by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
  · set i₀ : G3Idx := ⟨(δ, η, 0), hcon⟩ with hi₀
    have : IsProbabilityMeasure (g3pPalmLaw γ (gf η) i₀) := isProbabilityMeasure_g3p γ _ i₀
    have key := eventually_real_symmDiff_le_of_ballG hZm hB hs (P := g3pPalmLaw γ (gf η) i₀)
      (Y := fun p => restrictField (circIn i₀.t₁ i₀.r₁) (g3pField γ (gf η) p.1))
      (Y' := fun p => g3pField γ (gf η) p.1)
      ((measurable_restrictField_y _).comp ((measurable_g3pField γ _).comp measurable_fst))
      ((measurable_g3pField γ _).comp measurable_fst)
      ((measurable_g3pX γ (gf η) i₀).mono (sig_le_g3 i₀ _ _) le_rfl)
      (E := {p | |g3pX γ (gf η) i₀ p - i₀.t₁| + m < i₀.r₁})
      (measurableSet_lt ((continuous_abs.measurable.comp
        (((measurable_g3pX γ (gf η) i₀).mono (sig_le_g3 i₀ _ _) le_rfl).sub_const _)).add_const _)
        measurable_const)
      isOpen_ball (fun p hp => abs_lt_ball hm hp)
      (fun p => fcAgree_restrictField_circIn _ _ _)
      (hgood i₀) hε
    filter_upwards [key] with C hC i hi
    obtain ⟨⟨a, b, c⟩, hp⟩ := i
    simp only [Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl⟩ := hi
    exact hC
  · filter_upwards with C
    intro i hi
    have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
      have := i.2
      rwa [hi] at this
    exact absurd h2 hcon

/-- **Region locality at `R(x)` from ball locality.** -/
theorem g3pRegLocRZ_of_ballAE (hZm' : ∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2)
    {γ : ℝ} {Gd : FieldSample → ℝ → Prop} (hB' : G3ZqZoomBallLocGZ Z' Gd)
    (gf : ℝ → ℂ → ℝ)
    (hgood : ∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (gf i.η) i),
      Gd (g3pField γ (gf i.η) p.1) (g3pR γ (gf i.η) i p)) :
    G3pRegLocRZ Z' γ gf := by
  intro t ht δ η m hm ε hε
  by_cases hcon : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4
  · set i₀ : G3Idx := ⟨(δ, η, 0), hcon⟩ with hi₀
    have : IsProbabilityMeasure (g3pPalmLaw γ (gf η) i₀) := isProbabilityMeasure_g3p γ _ i₀
    have key := eventually_real_symmDiff_le_of_ballG hZm' hB' ht (P := g3pPalmLaw γ (gf η) i₀)
      (Y := fun p => restrictField (circIn i₀.t₂ i₀.r₂) (g3pField γ (gf η) p.1))
      (Y' := fun p => g3pField γ (gf η) p.1)
      ((measurable_restrictField_y _).comp ((measurable_g3pField γ _).comp measurable_fst))
      ((measurable_g3pField γ _).comp measurable_fst)
      ((measurable_g3pR γ (gf η) i₀).mono (sig_le_g3 i₀ _ _) le_rfl)
      (E := {p | |g3pR γ (gf η) i₀ p - i₀.t₂| + m < i₀.r₂})
      (measurableSet_lt ((continuous_abs.measurable.comp
        (((measurable_g3pR γ (gf η) i₀).mono (sig_le_g3 i₀ _ _) le_rfl).sub_const _)).add_const _)
        measurable_const)
      isOpen_ball (fun p hp => abs_lt_ball hm hp)
      (fun p => fcAgree_restrictField_circIn _ _ _)
      (hgood i₀) hε
    filter_upwards [key] with C hC i hi
    obtain ⟨⟨a, b, c⟩, hp⟩ := i
    simp only [Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl, rfl⟩ := hi
    exact hC
  · filter_upwards with C
    intro i hi
    have h2 : 0 < η ∧ η < δ ∧ δ ≤ 1 / 4 := by
      have := i.2
      rwa [hi] at this
    exact absurd h2 hcon

theorem g3UnscaledTransferZ_ballAE {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {s t : Set LawD}
    (hs : s ∈ lawCyl) (ht : t ∈ lawCyl) {ε : ℝ} (hε : 0 < ε) :
    ∃ U₀ : ℝ, 0 < U₀ ∧ ∀ U : ℝ, 0 < U → U ≤ U₀ →
    ∀ (Z Z' : ℝ → FieldSample → ℝ → LawD),
    (∀ C, Measurable fun q : FieldSample × ℝ => Z C q.1 q.2) →
    (∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z C y x = Z C y' x) →
    (∀ C, Measurable fun q : FieldSample × ℝ => Z' C q.1 q.2) →
    (∀ (C : ℝ) (y y' : FieldSample) (x : ℝ), avgReg y = avgReg y' → Z' C y x = Z' C y' x) →
    ∀ Gd Gd' : FieldSample → ℝ → Prop, G3ZqZoomBallLocGZ Z Gd → G3ZqZoomBallLocGZ Z' Gd' →
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wCut γ i.η) i),
      Gd (g3pField γ (g3wCut γ i.η) p.1) (g3pX γ (g3wCut γ i.η) i p)) →
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wProf γ) i),
      Gd (g3pField γ (g3wProf γ) p.1) (g3pX γ (g3wProf γ) i p)) →
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wCut γ i.η) i),
      Gd' (g3pField γ (g3wCut γ i.η) p.1) (g3pR γ (g3wCut γ i.η) i p)) →
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wProf γ) i),
      Gd' (g3pField γ (g3wProf γ) p.1) (g3pR γ (g3wProf γ) i p)) →
    ∀ μ ν : Measure LawD, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    G3FixMixBody μ ν (g3PalmLaw γ) (g3X γ) (g3R γ) (g3UfZ Z γ) (g3VfZ Z' γ) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      (∀ᵐ ω ∂P', ∀ᵐ x ∂(qBoundaryMeasure γ (g3plUW γ X A ω)),
        Gd (g3plUW γ X A ω) x ∧ Gd' (g3plUW γ X A ω) (g3zPartner γ (g3plUW γ X A ω) x)) →
      (∀ V : Ω' → FieldSample, IsFreeGFFModConstH V P' →
        (∀ᵐ ω ∂P', V ω (foldedCircle 0 1) = 0) →
        ∀ᵐ ω ∂P', ∀ᵐ x ∂(qBoundaryMeasure γ (V ω + F2.logSingField (γ ^ 2))),
          Gd (V ω + F2.logSingField (γ ^ 2)) x ∧ Gd' (V ω + F2.logSingField (γ ^ 2))
            (g3zPartner γ (V ω + F2.logSingField (γ ^ 2)) x)) →
      ∀ᶠ L in (atTop : Filter ℝ),
        (ENNReal.ofReal U)⁻¹ * ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (g3plUW γ X A ω) ∂P' ≤
            ENNReal.ofReal (μ.real s * ν.real t) + ENNReal.ofReal ε ∧
          ENNReal.ofReal (μ.real s * ν.real t) ≤
            (ENNReal.ofReal U)⁻¹ * ∫⁻ ω, g3plPhiZ Z Z' γ L U s t (g3plUW γ X A ω) ∂P' +
              ENNReal.ofReal ε := by
  set e : ℝ := ε / 4 with he
  have he0 : 0 < e := by positivity
  have h4e : 4 * e = ε := by rw [he]; ring
  obtain ⟨δ, hδ, hδ4, U₁, hU₁, H1⟩ := G3ZqL.g3PlPhiUnscaledZ_unifAE hγ hγ2 he0
  obtain ⟨U₂, hU₂, H2⟩ := g3plHonX_schemeC_Z_unif hγ hγ2 hδ he0
  refine ⟨min U₁ U₂, lt_min hU₁ hU₂, fun U hU hUle Z Z' hZm hZa hZm' hZa' Gd Gd' hB hB'
    hGB hGC hGB' hGC' μ ν hμ hν hbody Ω' _ P' _ X A hX hA hXA hGW hGV => ?_⟩
  have hLB := g3pRegLocXZ_of_ballAE hZm hB (g3wCut γ) hGB
  have hLC := g3pRegLocXZ_of_ballAE hZm hB (fun _ => g3wProf γ) hGC
  have hRB := g3pRegLocRZ_of_ballAE hZm' hB' (g3wCut γ) hGB'
  have hRC := g3pRegLocRZ_of_ballAE hZm' hB' (fun _ => g3wProf γ) hGC'
  have hloc : G3pRegionLocStmtZ Z Z' γ := fun s hs t ht δ η m hm ε hε => by
    filter_upwards [hLC s hs δ η m hm ε hε, hRC t ht δ η m hm ε hε] with C h1 h2 i hi
    exact ⟨h1 i hi, h2 i hi⟩
  have hRc := g3TCutToProfRZ (Z := Z) hZm' hγ hγ2 hRB hRC
  have hJ : G3TJointMixZ Z Z' γ μ ν := g3TJointMixZ_of_bodyC hZm hZm' hloc
    (g3TProfMixTransferStmtZ_of hZm hZa hZm' hZa' hγ hγ2
      (g3TCutToProfStmtZ_of hZm hγ hγ2 hLB hLC hRc) μ ν hμ hν hbody)
  obtain ⟨m, hm, Hη⟩ := H2 U hU (hUle.trans (min_le_right _ _)) Z Z' hZm hZm' s hs t ht
  obtain ⟨η, ⟨M, HL⟩, hη⟩ := (Hη.and (Ioo_mem_nhdsGT hδ)).exists
  filter_upwards [H1 U hU (hUle.trans (min_le_left _ _)) Z Z' hZm hZa hZm' hZa' Gd Gd'
    (G3ZqL.g3PlCapLocAE_of_ball hZm hZm' hB hB') P' X A hX hA hXA hGW hGV s hs t ht, hJ s hs t ht δ η m hm M e he0] with L h1 h2
  let i : G3Idx := ⟨(δ, η, L), hη.1, hη.2, hδ4⟩
  obtain ⟨w, hwm, hwb, hJ1, hJ2, hE⟩ := HL L i rfl
  have hI := h2 i rfl w hwm hwb
  have hc0 : 0 ≤ μ.real s * ν.real t := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hc1 : μ.real s * ν.real t ≤ 1 :=
    mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  obtain ⟨hA', hB'⟩ := g3t_arith hc0 hc1 hI hE
  have hI0 : 0 ≤ ∫ p, (g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩ g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
      g3pMarg γ (g3wProf γ) i m).indicator w p ∂(g3pPalmLaw γ (g3wProf γ) i) :=
    integral_nonneg fun p => by
      by_cases hp : p ∈ g3pUfZ Z γ (g3wProf γ) i ⁻¹' s ∩ g3pVfZ Z' γ (g3wProf γ) i ⁻¹' t ∩
          g3pMarg γ (g3wProf γ) i m
      · rw [indicator_of_mem hp]; exact (hwb p).1
      · rw [indicator_of_notMem hp]; rfl
  rw [← h4e]
  exact ⟨g3zq_arith_le hI0 hc0 he0.le h1.1 hJ1 hA', g3zq_arith_ge hI0 he0.le h1.2 hJ2 hB'⟩

end G3ZqL
end R18
end QuantumZipper
