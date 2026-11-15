/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawSample

/-!
# Zhan's A.1 under R83: the clock facts of a mixed source column

Packet PROVE-A1-G3LAW2. A1-FAMILY's identification lemmas (`seedCapacityTime_spec`, `seedCapacityDriver_eq_…`) need
the capacity clock of a seeded column to be continuous, strictly increasing and bounded below linearly. For a mixed
source column (A1-G3CALC's `IsSourceColumnG`) these facts are produced inside PROVE-A1-G3LAW's
`isSeedSampleLaw_of_column`; **`clock_facts_of_column`** exposes them (same derivation: A22's
`seedMap_alive_derivative_facts`, A1-G3CALC's (D9) for the lower bound, A1-FAMILY's `clock_props`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open A2X A1SeedField A1EightSeed A1G3Calc Girsanov A1Family A1MultiMark A1G3Law

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The clock facts of a mixed source column**: the capacity clock is continuous and strictly increasing at every
sample and bounded below by `c · r` for some `c > 0`; every record is `OwnData` against the frozen hull. -/
theorem clock_facts_of_column {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : Ω → SeedData n}
    {T : Ω → ℝ≥0} (hpp : IsProtectedPairG H₁ H₂ δ p q dd)
    (hcol : IsSourceColumnG H₁ H₂ p q Tm κ rr 𝓕 P t₂ sdata T) :
    (∀ ω, Continuous (seedQuadClock (seedCapacityCoeff sdata T) ω)) ∧
      (∀ ω, StrictMono (seedQuadClock (seedCapacityCoeff sdata T) ω)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ ω r, c * r ≤ seedQuadClock (seedCapacityCoeff sdata T) ω r := by
  obtain ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hB, hBc, hDm, hDc, hdW, -, hVm, -, -⟩ := hcol
  obtain ⟨x₀⟩ : Nonempty Ω := by
    by_contra hX
    have hE : IsEmpty Ω := not_nonempty_iff.1 hX
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact zero_ne_one h1
  have r₀ := hrec x₀
  have hH₁ := hpp.pair.hull₁
  have hH₂ := hpp.pair.hull₂
  have hδ := hpp.pair.sep_pos
  have hsep := hpp.pair.sep
  have hq := hpp.pair.prot_pos
  have hqp := hpp.pair.prot_lt
  have hpH₂ := hpp.pair.src
  have hd := hpp.pair.rad_pos
  have hqH := hpp.pair.prot
  have hseg := hpp.seg
  have hW₂ := r₀.contW₂
  have hW₂0 := r₀.zeroW₂
  have ht₂ := r₀.pos₂
  have ht₂m := r₀.le₂
  have hK₂ := r₀.sub₂
  have hTm : ∀ ω, (T ω : ℝ) ≤ Tm := fun ω => (hrec ω).le₁
  have hdsource := fun ω => (hrec ω).source
  have hK₁ := fun ω => (hrec ω).sub₁
  have hVI := fun ω => (hrec ω).marks
  have hdκ : ∀ ω, (sdata ω).κ = κ := fun ω => congrArg SeedData.κ (hdsource ω)
  have hdr : ∀ ω, (sdata ω).r = rr := fun ω => congrArg SeedData.r (hdsource ω)
  have hdφ : ∀ ω, (sdata ω).φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) :=
    fun ω => congrArg SeedData.φ (hdsource ω)
  have hdζ : ∀ ω, (sdata ω).ζ₀ = W₂ t₂ := fun ω => congrArg SeedData.ζ₀ (hdsource ω)
  have h : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂) (sdata ω).φ (T ω) (sdata ω).a (sdata ω).W' :=
    fun ω => (hrec ω).own
  have hown : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (sdata ω).a (sdata ω).W' := by
    intro ω
    rw [← hdφ ω]
    exact h ω
  have hW0H : ∀ ω, ((sdata ω).W 0 : ℂ) ∈ closure H₁ := fun ω =>
    closure_mono (hK₁ ω) (start_mem_closure_fwdHull (h ω).cont (h ω).pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rwa [hW₂0]
  obtain ⟨r, L₀, hr, -, hinterval⟩ :=
    exists_ext_interval_own_bounds_right hH₁ hH₂ hδ hsep hq hd hqH hseg Tm
  have hint : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) →
      ∀ x ∈ uIcc (Vlo ω u) ((fwdMap (sdata ω).W u q).re + (sdata ω).W u),
      Disjoint (ball (x : ℂ) r)
        ((fun z => fwdMap (sdata ω).W u z + (sdata ω).W u) '' fwdHull W₂ t₂) := by
    intro ω u hu x hx
    exact (hinterval (sdata ω).W W₂ (Vlo ω) (Vhi ω) (T ω) t₂
      (sdata ω).a (sdata ω).W' (hown ω) hW₂ ht₂ (hW0H ω) hW₂H
      (by rwa [hW₂0]) ht₂m (hK₁ ω) hK₂ ((hrec ω).lo) ((hrec ω).hi) u hu x hx).1
  obtain ⟨r₀', a₀, γ, Γ, lam, hr₀, ha₀, -, hd9⟩ :=
    exists_twoCurveD9 hH₁ hH₂ hδ hsep hd hq hqH
      (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m) Tm
  have hd9ω := fun ω => hd9 (sdata ω).W W₂ t₂ (T ω) (sdata ω).a (sdata ω).W'
    0 Fin.elim0 (hown ω) hW₂ hW₂H (by rwa [hW₂0]) ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
  have hv₀ : ∀ ω, ∃ v, IsForwardSol (sdata ω).W' (sdata ω).ζ₀ ((sdata ω).a (T ω)) v := by
    intro ω
    rw [hdζ ω]
    exact (hd9ω ω).alive₀
  let X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u => ((hB.2.1 u).const_mul _).add (hDm u)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω => ((hBc ω).const_mul _).add (hDc ω)
  have hdX : ∀ ω, (sdata ω).W = Ito.rpath (X · ω) := by
    intro ω
    rw [hdW ω, driftDriver_eq_rpath]
  have hmclr : ∀ ω m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((sdata ω).V m t : ℂ) r) ((fun z => fwdMap (sdata ω).W t z + (sdata ω).W t) '' fwdHull W₂ t₂) :=
    fun ω m u hu => hint ω u hu _ (hVI ω u hu m)
  obtain ⟨hmA, hcA, hbA⟩ := seedMap_alive_derivative_facts hXm hXc hdX hdφ hdζ hdκ hdr hT hr₀ hr h hv₀
    (fun ω t ht => (hd9ω ω).d9.clr t ht) (fun ω m t ht => hmclr ω m t ht) hVm
  have hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).A 1 u - 1) := fun u => by
    have hg : MeasurableSet[𝓕 u] {ω | u ≤ T ω} := measurableSet_ge_of_isStoppingTime hT u
    have e' : ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).A 1 u - 1) =
        ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).A 1 u) - {ω | u ≤ T ω}.indicator fun _ => (1 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ {ω | u ≤ T ω}
      · simp only [indicator_of_mem hω, Pi.sub_apply]
      · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_zero]
    rw [e']
    exact (hmA u).sub (measurable_const.indicator hg)
  have hA1 : ∀ ω u, 0 < u → u ≤ T ω → a₀ ≤ (sdata ω).A 1 u := fun ω u hu huT => by
    change a₀ ≤ frzA (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ 1 u
    rw [hdφ ω]
    exact (hd9ω ω).d9.A1 u ⟨u.coe_nonneg, NNReal.coe_le_coe.2 huT⟩
  obtain ⟨hCc, hCs, -, c, hc, hClb⟩ := clock_props hm hcA ha₀ (C := 1) (fun ω u hu huT => hbA u ω hu huT) hA1
  exact ⟨hCc, hCs, c, hc, hClb⟩

end InteractingSLE.ZhanGT4.A1G3L2
