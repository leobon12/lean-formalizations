import SupercriticalLQGUniqueness.B2.LscTop.Limits
import SupercriticalLQGUniqueness.Frozen.LSCTendstoInProbability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

 


















set_option autoImplicit false

noncomputable section

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.LscTop

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

 

 
theorem lscTendstoInProbability_iff_subseq {F : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal}
    {L : Ω → ℂ × ℂ → EReal} :
    LSCTendstoInProbability P F L ↔
      ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, LSCTendsto (fun k => F (ε (φ k)) ω) (L ω) :=
  Iff.rfl

 


theorem lscTendstoInProbability_iff_subseq_tendsto {G : Set.Ioi (0 : ℝ) → Ω → LSCFun}
    {L : Ω → LSCFun} :
    LSCTendstoInProbability P (fun ε ω => (G ε ω).1) (fun ω => (L ω).1) ↔
      ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ᵐ ω ∂P, Tendsto (fun k => G (ε (φ k)) ω) atTop (𝓝 (L ω)) := by
  simp only [LSCTendstoInProbability, LSCFun.tendsto_iff_lscTendsto]

 
theorem LSCTendstoInProbability.congr_limit {F : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal}
    {L L' : Ω → ℂ × ℂ → EReal} (h : LSCTendstoInProbability P F L) (hL : L =ᵐ[P] L') :
    LSCTendstoInProbability P F L' := by
  intro ε hε
  obtain ⟨φ, hφ, hae⟩ := h ε hε
  exact ⟨φ, hφ, by filter_upwards [hae, hL] with ω hω hLω; rwa [← hLω]⟩

 
theorem LSCTendstoInProbability.congr_seq {F F' : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal}
    {L : Ω → ℂ × ℂ → EReal} (h : LSCTendstoInProbability P F L)
    (hF : ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
      ∀ᵐ ω ∂P, ∀ n, F (ε n) ω = F' (ε n) ω) :
    LSCTendstoInProbability P F' L := by
  intro ε hε
  obtain ⟨φ, hφ, hae⟩ := h ε hε
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hae, hF ε hε] with ω hω hFω
  have e : (fun k => F' (ε (φ k)) ω) = fun k => F (ε (φ k)) ω :=
    funext fun k => (hFω (φ k)).symm
  rwa [e]

 

theorem LSCTendstoInProbability.congr {F F' : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal}
    {L : Ω → ℂ × ℂ → EReal} (h : LSCTendstoInProbability P F L) (hF : ∀ ε, F ε =ᵐ[P] F' ε) :
    LSCTendstoInProbability P F' L :=
  LSCTendstoInProbability.congr_seq h fun ε _ => ae_all_iff.2 fun n => hF (ε n)

 
theorem lscTendstoInProbability_congr {F F' : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal}
    {L L' : Ω → ℂ × ℂ → EReal} (hF : ∀ ε, F ε =ᵐ[P] F' ε) (hL : L =ᵐ[P] L') :
    LSCTendstoInProbability P F L ↔ LSCTendstoInProbability P F' L' :=
  ⟨fun h => LSCTendstoInProbability.congr_limit (LSCTendstoInProbability.congr h hF) hL,
    fun h => LSCTendstoInProbability.congr_limit
      (LSCTendstoInProbability.congr h fun ε => (hF ε).symm) hL.symm⟩

 
def invSucc (n : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨1 / ((n : ℝ) + 1), mem_Ioi.2 Nat.one_div_pos_of_nat⟩

theorem tendsto_invSucc : Tendsto (fun n => (invSucc n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

 
theorem LSCTendstoInProbability.ae_eq_limit {F : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal}
    {L L' : Ω → ℂ × ℂ → EReal} (h : LSCTendstoInProbability P F L)
    (h' : LSCTendstoInProbability P F L') : L =ᵐ[P] L' := by
  obtain ⟨φ, hφ, hae⟩ := h invSucc tendsto_invSucc
  obtain ⟨ψ, hψ, hae'⟩ := h' (invSucc ∘ φ) (tendsto_invSucc.comp hφ.tendsto_atTop)
  filter_upwards [hae, hae'] with ω hω hω'
  exact (hω.comp_strictMono hψ).unique hω'

 

 
theorem exists_compatible_metric :
    ∃ d : MetricSpace LSCFun, d.toUniformSpace.toTopologicalSpace = LSCFun.instTopologicalSpace :=
  ⟨metrizableSpaceMetric LSCFun, rfl⟩

 



theorem lscTendstoInProbability_iff_tendstoInMeasure (d : PseudoEMetricSpace LSCFun)
    (hd : d.toUniformSpace.toTopologicalSpace = LSCFun.instTopologicalSpace) [IsFiniteMeasure P]
    {G : Set.Ioi (0 : ℝ) → Ω → LSCFun} {L : Ω → LSCFun}
    (hG : ∀ ε, AEStronglyMeasurable (G ε) P) :
    LSCTendstoInProbability P (fun ε ω => (G ε ω).1) (fun ω => (L ω).1) ↔
      @TendstoInMeasure _ _ _ d.toEDist _ P G (comap Subtype.val (𝓝 (0 : ℝ))) L := by
  
  have hseq : @TendstoInMeasure _ _ _ d.toEDist _ P G (comap Subtype.val (𝓝 (0 : ℝ))) L ↔
      ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        @TendstoInMeasure _ _ _ d.toEDist _ P (fun n => G (ε n)) atTop L := by
    constructor
    · intro h ε hε δ hδ
      exact (h δ hδ).comp (tendsto_comap_iff.2 hε)
    · intro h δ hδ
      refine tendsto_iff_seq_tendsto.2 fun ε hε => ?_
      exact h ε (tendsto_comap_iff.1 hε) δ hδ
  
  have hsub : ∀ ε : ℕ → Set.Ioi (0 : ℝ),
      @TendstoInMeasure _ _ _ d.toEDist _ P (fun n => G (ε n)) atTop L ↔
        ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
          ∀ᵐ ω ∂P, LSCTendsto (fun i => (G (ε (ns (ns' i))) ω).1) (L ω).1 := by
    intro ε
    have hf : ∀ n, @AEStronglyMeasurable _ _ d.toUniformSpace.toTopologicalSpace _ _
        (G (ε n)) P := by
      intro n
      have h := hG (ε n)
      rw [← hd] at h
      exact h
    refine (@exists_seq_tendstoInMeasure_atTop_iff _ _ _ P d _ _ hf L).trans ?_
    refine forall₂_congr fun ns _ => exists_congr fun ns' => and_congr_right fun _ => ?_
    refine Filter.eventually_congr (Eventually.of_forall fun ω => ?_)
    rw [hd]
    exact LSCFun.tendsto_iff_lscTendsto
  rw [hseq, LSCTendstoInProbability]
  constructor
  · intro h ε hε
    rw [hsub]
    intro ns hns
    exact h (ε ∘ ns) (hε.comp hns.tendsto_atTop)
  · intro h ε hε
    obtain ⟨ns', hns', hae⟩ := (hsub ε).1 (h ε hε) id strictMono_id
    exact ⟨ns', hns', hae⟩

end SupercriticalLQGUniqueness.B2.LscTop
