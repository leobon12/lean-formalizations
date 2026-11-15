/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawD10
import InteractingSLE.Spec.ZhanGT4.A1ForcesLaw
import InteractingSLE.Spec.ZhanGT4.A1FamilyCanon
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalData

/-!
# Zhan's A.1 under R83, (G3): the one-sample image law of a mixed-mark source column

Packet PROVE-A1-G3LAW (R83). From the seeded (D10) of a mixed source column (`exists_seedCapacityBrownian_of_column`)
and A1-FORCES's transfer `isSeedSampleLaw_of_capacityBrownian`:

* **`isSeedSampleLaw_of_column`**: A1-FAMILY's one-sample law `IsSeedSampleLaw` under the seeded measure of a mixed
  source column, for any image data equal to the seeded capacity coordinates up to the cap (driver, forces in the
  order of the charge enumeration, the residual as the noise, the cap the capacity horizon, the other caps image
  capacities at own-time stopping times). The clock, its lower bound and the progressive own-time image coordinates are
  discharged from the column.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open A2X A1SeedField A1EightSeed A1G3Calc Girsanov A1Family A1MultiMark

section Column

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The one-sample image law of a mixed-mark source column** (the per-sample frozen law with the compensated
residual as the noise, in seeded coordinates): under the seeded measure `seedMeasure P sdata T`, image data that agree
with the seeded capacity coordinates up to the cap satisfy `IsSeedSampleLaw`. -/
theorem isSeedSampleLaw_of_column {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : Ω → SeedData n}
    {T : Ω → ℝ≥0} (hpp : IsProtectedPairG H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (hcol : IsSourceColumnG H₁ H₂ p q Tm κ rr 𝓕 P t₂ sdata T)
    (hrate : ∀ ω m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      IntervalIntegrable (fun u => 2 / ((sdata ω).V m u - (sdata ω).W u)) volume 0 t)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hρL : ∀ ω i, (sdata ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (sdata ω).imageCharge (e (.inr j)) = ρR j)
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {N : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0} {m : ℕ}
    (hSm : ∀ ω, Scap m ω = seedCapacityHorizon sdata T ω)
    (hW : ∀ ω t, t ≤ Scap m ω → W t ω = seedCapacityDriver sdata T t ω)
    (hVL : ∀ ω i t, t ≤ Scap m ω → VL i t ω = seedCapacityForce sdata T (e (.inl i)) t ω)
    (hVR : ∀ ω j t, t ≤ Scap m ω → VR j t ω = seedCapacityForce sdata T (e (.inr j)) t ω)
    (hN : ∀ ω t, t ≤ Scap m ω → N t ω = seedCapacityNoise κ ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) t)
    (hζ : ∀ ω, (Scap m ω : ℝ≥0∞) ≤ ζ ω)
    (Tk : ℕ → Ω → ℝ≥0) (hTk : ∀ k, IsStoppingTime 𝓕 fun ω => (Tk k ω : WithTop ℝ≥0))
    (hcap₁ : ∀ k ω, Tk k ω ≤ T ω → (Scap k ω : ℝ) = (sdata ω).a (Tk k ω))
    (hcap₂ : ∀ k ω, T ω ≤ Tk k ω → Scap m ω ≤ Scap k ω) :
    IsSeedSampleLaw (seedMeasure P sdata T) W ζ VL VR N Scap m := by
  obtain ⟨B₀, hCc, hCm, hcm, hBh, hBhc⟩ := exists_seedCapacityBrownian_of_column hpp hκ hcol hrate e hρL hρR
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
  obtain ⟨-, hCs, -, c, hc, hClb⟩ := clock_props hm hcA ha₀ (C := 1) (fun ω u hu huT => hbA u ω hu huT) hA1
  have hparts := fun q : ℝ≥0 => measurable_seed_parts hXm hXc hdX hdφ hdζ q
    (measurableSet_ge_of_isStoppingTime hT q) (fun ω hω => NNReal.coe_le_coe.2 hω) (fun ω _ => h ω)
    (fun ω _ => hv₀ ω) (fun ω hω m => ⟨r, hr, hmclr ω m q ⟨q.coe_nonneg, NNReal.coe_le_coe.2 hω⟩⟩) (hVm q)
  have hcA0 : ∀ ω, ContinuousOn ((sdata ω).A 0) (Icc 0 (T ω)) := fun ω => (h ω).continuousOn_frzA 0
  have hWp := isStronglyProgressive_seedDriver (𝓕 := 𝓕) (fun ω => h ω)
    (fun u => measurable_stopped_of_indicator hT (f := fun ω t => (sdata ω).A 0 t) (fun q => (hparts q).1 0) hcA0 u)
  have hWI := fun ω => (hrec ω).drv
  have hcB0 : ∀ ω m, ContinuousOn (fun t => (sdata ω).B0 t m) (Icc 0 (T ω)) := by
    intro ω m
    have hds : ContinuousOn (fun u => dslope ((sdata ω).F 0 u) ((sdata ω).W u) ((sdata ω).V m u))
        (Icc 0 (T ω)) :=
      (h ω).continuousOn_dslope_moving hr (h ω).cont.continuousOn ((hrec ω).mark m).cont
        (fun u hu => hint ω u hu _ (hWI ω u hu)) (fun u hu => hint ω u hu _ (hVI ω u hu m))
    refine ((hcA0 ω).add ((((hrec ω).mark m).cont.sub (h ω).cont.continuousOn).mul hds)).congr fun u _ => ?_
    have he := sub_smul_dslope ((sdata ω).F 0 u) ((sdata ω).W u) ((sdata ω).V m u)
    simp only [smul_eq_mul] at he
    show (sdata ω).F 0 u ((sdata ω).V m u) = (sdata ω).F 0 u ((sdata ω).W u) +
      ((sdata ω).V m u - (sdata ω).W u) * dslope ((sdata ω).F 0 u) ((sdata ω).W u) ((sdata ω).V m u)
    linarith only [he]
  have hcF : ∀ k, ∀ ω, ContinuousOn (fun t => (sdata ω).imageForce t k) (Icc 0 (T ω)) := by
    intro k ω
    cases k using Fin.cases with
    | zero => exact fun u hu => ((h ω).hasDerivWithinAt_frzImg (hv₀ ω).choose_spec hu).continuousWithinAt
    | succ m => exact hcB0 ω m
  have hmF : ∀ k (q : ℝ≥0), Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (sdata ω).imageForce q k) := by
    intro k q
    cases k using Fin.cases with
    | zero => exact (hparts q).2.1
    | succ m => exact (hparts q).2.2.2.2.1 m
  have h0 : Measurable[𝓕 0] fun ω => (sdata ω).A 0 0 := by
    have hm0 := (hparts 0).1 0
    have he : ({ω | (0 : ℝ≥0) ≤ T ω}.indicator fun ω => (sdata ω).A 0 ((0 : ℝ≥0) : ℝ)) =
        fun ω => (sdata ω).A 0 0 := by
      funext ω
      have hmem : ω ∈ {ω' | (0 : ℝ≥0) ≤ T ω'} := (T ω).zero_le_coe
      rw [indicator_of_mem hmem, NNReal.coe_zero]
    rwa [he] at hm0
  have hVp : ∀ k, IsStronglyProgressive 𝓕 fun u ω =>
      (sdata ω).imageForce ((min u (T ω) : ℝ≥0) : ℝ) k - (sdata ω).A 0 0 := fun k =>
    isStronglyProgressive_seedForce k (hcF k)
      (fun u => measurable_stopped_of_indicator hT (f := fun ω t => (sdata ω).imageForce t k) (hmF k) (hcF k) u) h0
  exact A1Forces.isSeedSampleLaw_of_capacityBrownian (fun ω => h ω) hCc hCm hcm hCs hc hClb
    (XL := fun i ω t => (sdata ω).imageForce t (e (.inl i))) (XR := fun j ω t => (sdata ω).imageForce t (e (.inr j)))
    hBh hBhc hT hWp (fun i => hVp _) (fun j => hVp _) hSm hW hVL hVR hN hζ Tk hTk hcap₁ hcap₂

/-- **A Brownian motion under the seeded measure of a mixed source column** (the column's Girsanov process,
`seeded_source_calculus_ext`), with continuous paths. -/
theorem exists_brownian_seedMeasure_of_column {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : Ω → SeedData n}
    {T : Ω → ℝ≥0} (hpp : IsProtectedPairG H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (hcol : IsSourceColumnG H₁ H₂ p q Tm κ rr 𝓕 P t₂ sdata T) :
    ∃ B : ℝ≥0 → Ω → ℝ, IsFilteredBrownianReal 𝓕 B (seedMeasure P sdata T) ∧ ∀ ω, Continuous (B · ω) := by
  obtain ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hB, hBc, hDm, hDc, hdW, hD, hVm, hV₀m, hG₀m⟩ := hcol
  obtain ⟨x₀⟩ : Nonempty Ω := by
    by_contra hX
    have hE : IsEmpty Ω := not_nonempty_iff.1 hX
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact zero_ne_one h1
  have r₀ := hrec x₀
  have hsrc := seeded_source_calculus_ext hpp.pair.hull₁ hpp.pair.hull₂ hpp.pair.sep_pos hpp.pair.sep
    hpp.pair.src hpp.pair.prot_pos hpp.pair.prot_lt hpp.pair.rad_pos hpp.pair.prot hpp.seg 𝓕 hκ rr
    r₀.contW₂ r₀.zeroW₂ r₀.pos₂ r₀.le₂ r₀.sub₂ hB hBc hDm hDc (sdata := sdata) (Vlo := Vlo) (Vhi := Vhi) (T := T)
    (fun x => (hrec x).source) hdW hT (fun x => (hrec x).le₁) (fun x => (hrec x).own) (fun x => (hrec x).sub₁)
    (fun x => (hrec x).lo) (fun x => (hrec x).hi) (fun x => (hrec x).drv) (fun x => (hrec x).marks)
    (fun x => (hrec x).mark) (fun x => (hrec x).inj) hD hVm hV₀m hG₀m
  obtain ⟨-, -, -, -, hBh, -⟩ := hsrc
  have hXm : ∀ u, Measurable[𝓕 u] (fun ω => Real.sqrt κ * B u ω + D u ω) := fun u =>
    ((hB.2.1 u).const_mul _).add (hDm u)
  have hXc : ∀ ω, Continuous ((fun u ω => Real.sqrt κ * B u ω + D u ω) · ω) := fun ω =>
    ((hBc ω).const_mul _).add (hDc ω)
  have hdX : ∀ ω, (sdata ω).W = Ito.rpath ((fun u ω => Real.sqrt κ * B u ω + D u ω) · ω) := by
    intro ω
    rw [hdW ω, driftDriver_eq_rpath]
  obtain ⟨C, -, -, hpred, -, hb⟩ := exists_seedNoise_prepared_ext hpp.pair.hull₁ hpp.pair.hull₂ hpp.pair.sep_pos
    hpp.pair.sep hpp.pair.src hpp.pair.prot_pos hpp.pair.prot_lt hpp.pair.rad_pos hpp.pair.prot hpp.seg 𝓕 P rr
    r₀.contW₂ r₀.zeroW₂ r₀.pos₂ r₀.le₂ r₀.sub₂ hXm hXc (fun x => (hrec x).source) hdX hT (fun x => (hrec x).le₁)
    (fun x => (hrec x).own) (fun x => (hrec x).sub₁) (fun x => (hrec x).lo) (fun x => (hrec x).hi)
    (fun x => (hrec x).drv) (fun x => (hrec x).marks) (fun x => (hrec x).mark) hVm hV₀m
  exact ⟨_, hBh, fun ω => (hBc ω).add (Girsanov.continuous_drift hpred.isStronglyProgressive hb ω)⟩

end Column

end InteractingSLE.ZhanGT4.A1G3Law
