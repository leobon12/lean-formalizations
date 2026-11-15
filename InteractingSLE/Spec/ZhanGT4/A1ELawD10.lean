/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawD10
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldCol
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Protected
import InteractingSLE.Spec.ZhanGT4.DualSeedImagePrepare
import InteractingSLE.Spec.ZhanGT4.DualSeedImageRegularity
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteBounds
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformBound

/-!
# Zhan's A.1 under R83, (Eight): the seeded (D10) of a seed source column

Packet PROVE-A1-EIGHTLAW (R83). A1-SEEDFIELD's source columns `IsSourceColumn` (seeds only: the Eight records
`eightRec`, whose marks are the two seeds of the small curve) satisfy the hypotheses of A22's seeded source calculus
`seeded_source_calculus_right`. This file supplies every source premise of A22's
`exists_seedCapacityBrownian_actual_source` from such a column, exactly as PROVE-A1-G3LAW's
`exists_seedCapacityBrownian_of_column` does for the mixed (G3) columns, with A22's seed-interval lemmas
(`exists_seed_interval_own_bounds_right`, `exists_seed_remoteScale_right`, `exists_seedNoise_prepared_right`,
`SeedData.continuousOn_ellX_driver`, `SeedData.imageEntranceIntegrable_of_seed`) in place of the extended-interval ones:

* **`exists_seedCapacityBrownian_of_seedColumn`**: for a protected pair and a seed source column, the seeded image
  driver is a `SeedCapacityBrownian` of A1-FAMILY's `seedFilt` under `seedMeasure`, for any enumeration of the image
  charges. No segment condition on the pair and no integrability premise on the marks are needed (seeds have their
  entrance integrability).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ELaw

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open A2X A1SeedField A1EightSeed A1G3Calc Girsanov

section Column

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The seeded (D10) of a seed source column** (§A.1.3–A.1.4): for a protected pair, a source column whose marks are
seed coordinates (`IsSourceColumn`, e.g. the Eight records) and any enumeration `e` of the image charges, the seeded
image driver is a capacity Brownian motion of A1-FAMILY's `seedFilt` under the seeded measure (A22's
`exists_seedCapacityBrownian_actual_source` with every source premise discharged from the column). -/
theorem exists_seedCapacityBrownian_of_seedColumn {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm κ : ℝ} {rr : Fin n → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} [IsProbabilityMeasure P] {t₂ : ℝ} {sdata : Ω → SeedData n}
    {T : Ω → ℝ≥0} (hpp : IsProtectedPair H₁ H₂ δ p q dd) (hκ : 0 < κ)
    (hcol : IsSourceColumn H₁ H₂ p Tm κ rr 𝓕 P t₂ sdata T)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (e : Fin nL ⊕ Fin nR ≃ Fin (n + 1))
    (hρL : ∀ ω i, (sdata ω).imageCharge (e (.inl i)) = ρL i)
    (hρR : ∀ ω j, (sdata ω).imageCharge (e (.inr j)) = ρR j) :
    ∃ B : ℝ≥0 → Ω → ℝ, ∃ (hCc : ∀ ω, Continuous (seedQuadClock (seedCapacityCoeff sdata T) ω))
      (hCm : ∀ ω, Monotone (seedQuadClock (seedCapacityCoeff sdata T) ω))
      (hcm : ∀ u : ℝ≥0, Measurable[𝓕 u] fun ω => seedQuadClock (seedCapacityCoeff sdata T) ω u),
      SeedCapacityBrownian κ ρL ρR (seedMeasure P sdata T) (A1Family.seedFilt 𝓕 sdata T hCc hCm hcm)
        (seedCapacityDriver sdata T) (fun i => seedCapacityForce sdata T (e (.inl i)))
        (fun j => seedCapacityForce sdata T (e (.inr j))) (seedCapacityHorizon sdata T)
        (A1Family.seedBh κ sdata T (girsanovProcess B (seedNoise κ sdata T))) ∧
      ∀ ω, Continuous (A1Family.seedBh κ sdata T (girsanovProcess B (seedNoise κ sdata T)) · ω) := by
  obtain ⟨W₂, Vlo, Vhi, B, D, hrec, hT, hB, hBc, hDm, hDc, hdW, hD, hVm, hV₀m, hG₀m⟩ := hcol
  obtain ⟨x₀⟩ : Nonempty Ω := by
    by_contra hX
    have hE : IsEmpty Ω := not_nonempty_iff.1 hX
    have h1 := measure_univ (μ := P)
    rw [Set.univ_eq_empty_iff.2 hE, measure_empty] at h1
    exact zero_ne_one h1
  have r₀ := hrec x₀
  have hH₁ := hpp.hull₁
  have hH₂ := hpp.hull₂
  have hδ := hpp.sep_pos
  have hsep := hpp.sep
  have hpH₂ := hpp.src
  have hq := hpp.prot_pos
  have hqp := hpp.prot_lt
  have hd := hpp.rad_pos
  have hqH := hpp.prot
  have hW₂ := r₀.contW₂
  have hW₂0 := r₀.zeroW₂
  have ht₂ := r₀.pos₂
  have ht₂m := r₀.le₂
  have hK₂ := r₀.sub₂
  have hTm : ∀ ω, (T ω : ℝ) ≤ Tm := fun ω => (hrec ω).le₁
  have hdsource := fun ω => (hrec ω).source
  have hK₁ := fun ω => (hrec ω).sub₁
  have hlo := fun ω => (hrec ω).lo
  have hhi := fun ω => (hrec ω).hi
  have hWI := fun ω => (hrec ω).drv
  have hVI := fun ω => (hrec ω).marks
  have hseed := fun ω => (hrec ω).seed
  have hVV := fun ω => (hrec ω).inj
  have hsrc := seeded_source_calculus_right hH₁ hH₂ hδ hsep hpH₂ hq hqp hd hqH 𝓕 hκ rr hW₂ hW₂0 ht₂ ht₂m hK₂
    hB hBc hDm hDc (sdata := sdata) (Vlo := Vlo) (Vhi := Vhi) (T := T) hdsource hdW hT hTm
    (fun ω => (hrec ω).own) hK₁ hlo hhi hWI hVI hseed hVV hD hVm hV₀m hG₀m
  obtain ⟨-, -, -, -, hBh, -⟩ := hsrc
  have hdκ : ∀ ω, (sdata ω).κ = κ := fun ω => congrArg SeedData.κ (hdsource ω)
  have hdr : ∀ ω, (sdata ω).r = rr := fun ω => congrArg SeedData.r (hdsource ω)
  have hdφ : ∀ ω, (sdata ω).φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) :=
    fun ω => congrArg SeedData.φ (hdsource ω)
  have hdζ : ∀ ω, (sdata ω).ζ₀ = W₂ t₂ := fun ω => congrArg SeedData.ζ₀ (hdsource ω)
  have hdV₀ : ∀ ω, (sdata ω).V₀ = fun u => (fwdMap (sdata ω).W u p).re + (sdata ω).W u :=
    fun ω => congrArg SeedData.V₀ (hdsource ω)
  have hdG₀ : ∀ ω, (sdata ω).G₀ = fun u => (deriv (fwdMap (sdata ω).W u) p).re :=
    fun ω => congrArg SeedData.G₀ (hdsource ω)
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
  have hWq : ∀ ω, (sdata ω).W 0 < q := fun ω => by rw [(h ω).zero]; exact hq
  obtain ⟨r, L₀, hr, -, hinterval⟩ := exists_seed_interval_own_bounds_right hH₁ hH₂ hδ hsep hd hqH Tm
  have hint : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → ∀ x ∈ uIcc (Vlo ω u) (Vhi ω u),
      Disjoint (ball (x : ℂ) r)
        ((fun z => fwdMap (sdata ω).W u z + (sdata ω).W u) '' fwdHull W₂ t₂) ∧
      deriv ((sdata ω).F 0 u) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) := by
    intro ω u hu x hx
    have hb := hinterval (sdata ω).W W₂ (Vlo ω) (Vhi ω) (T ω) t₂
      (sdata ω).a (sdata ω).W' (hown ω) hW₂ ht₂ (hW0H ω) hW₂H (hWq ω)
      (by rw [hW₂0]; exact hqp) ht₂m (hK₁ ω) hK₂ (hlo ω) (hhi ω) u hu x hx
    refine ⟨hb.1, ?_⟩
    change deriv (fun y : ℝ => (ownExt (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ u y).re) x ∈ _
    rw [hdφ ω]
    exact hb.2
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right hH₁ hH₂ hδ hsep hpH₂ hq hqp hd hqH Tm
  have hremote : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → (sdata ω).RemoteScale u Lrem := by
    intro ω u hu
    have hb := hrem κ rr (sdata ω).W W₂ (sdata ω).a (sdata ω).W' (Vlo ω) (Vhi ω)
      (sdata ω).V (T ω) t₂ (hown ω) hW₂ hW₂0 ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
      (hlo ω) (hhi ω) (hWI ω) (hVI ω) u hu
    simpa only [← hdsource ω] using hb
  obtain ⟨r₀', a₀, γ, Γ, lam, hr₀, ha₀, -, hd9⟩ :=
    exists_twoCurveD9 hH₁ hH₂ hδ hsep hd hq hqH
      (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m) Tm
  have hd9ω := fun ω => hd9 (sdata ω).W W₂ t₂ (T ω) (sdata ω).a (sdata ω).W'
    0 Fin.elim0 (hown ω) hW₂ hW₂H (by rwa [hW₂0]) ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
  have hv₀ : ∀ ω, ∃ v, IsForwardSol (sdata ω).W' (sdata ω).ζ₀ ((sdata ω).a (T ω)) v := by
    intro ω
    rw [hdζ ω]
    exact (hd9ω ω).alive₀
  have hsrcf : ∀ ω, ∃ v, IsForwardSol (sdata ω).W (p : ℂ) (T ω) v := by
    intro ω
    obtain ⟨a₂, W₂', h₂⟩ := exists_imgData hW₂ ht₂
      (isHPHull_fwdHull (h ω).cont (h ω).pos.le) (isMapOut_fwdMap_gen (h ω).cont (h ω).pos.le)
      (h ω).disj.symm
    obtain ⟨v, hv, -⟩ := h₂.exists_start_alive (h ω).cont (h ω).pos.le
      (by rw [hW₂0, (h ω).zero]; exact (hq.trans hqp).ne')
    rw [hW₂0] at hv
    exact ⟨v, hv⟩
  have hrates : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) →
      HasDerivWithinAt (sdata ω).V₀ (2 / ((sdata ω).V₀ u - (sdata ω).W u)) (Icc 0 (T ω)) u ∧
      HasDerivWithinAt (sdata ω).G₀ (-2 * (sdata ω).G₀ u / ((sdata ω).V₀ u - (sdata ω).W u) ^ 2)
        (Icc 0 (T ω)) u := by
    intro ω u hu
    obtain ⟨v, hv⟩ := hsrcf ω
    simpa only [hdV₀ ω, hdG₀ ω] using source_gmap_rates (h ω).cont hv hu
  have hreg := fun ω => (sdata ω).continuousOn_normEll_gapVal_of_remoteScale (h ω) (hv₀ ω).choose_spec
    hr (fun _ _ => convex_uIcc _ _) (hWI ω) (hVI ω)
    (fun u hu x hx => (hint ω u hu x hx).1) (fun u hu x hx => (hint ω u hu x hx).2)
    (hremote ω) (fun m => (hseed ω m).cont)
    (fun u hu => (hrates ω u hu).1.continuousWithinAt)
    (fun u hu => (hrates ω u hu).2.continuousWithinAt)
  have hgn : ∀ ω i u, u ∈ Ioc (0 : ℝ) (T ω) → (sdata ω).gapVal i u ≠ 0 := by
    intro ω i u hu
    have huc := Ioc_subset_Icc_self hu
    have hdiff : ∀ x ∈ uIcc (Vlo ω u) (Vhi ω u),
        DifferentiableAt ℂ (ownExt (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ u) x := by
      intro x hx
      have hd' := ((h ω).ownExt_props huc (hint ω u huc x hx).1).1
      exact hd'.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    apply (sdata ω).gapVal_ne_zero_of_remoteScale (hremote ω u huc) (convex_uIcc _ _)
      (fun x hx => (hdiff x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt)
      (fun x hx => (Real.exp_pos _).trans_le (hint ω u huc x hx).2.1)
      (fun x hx => ((sdata ω).deriv_F_zero (hdiff x hx)).symm) (hWI ω u huc) (hVI ω u huc)
      (fun m => (hseed ω m).ne u hu) (hVV ω u hu) i
  let X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u => ((hB.2.1 u).const_mul _).add (hDm u)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω => ((hBc ω).const_mul _).add (hDc ω)
  have hdX : ∀ ω, (sdata ω).W = Ito.rpath (X · ω) := by
    intro ω
    rw [hdW ω, driftDriver_eq_rpath]
  obtain ⟨C, hC, hcoord, hpred, -, hb⟩ := exists_seedNoise_prepared_right hH₁ hH₂ hδ hsep hpH₂ hq hqp
    hd hqH 𝓕 P rr hW₂ hW₂0 ht₂ ht₂m hK₂ hXm hXc hdsource hdX hT hTm h hK₁
    hlo hhi hWI hVI hseed hVm hV₀m
  have hV₀c : ∀ ω, ContinuousOn (sdata ω).V₀ (Icc 0 (T ω)) := fun ω u hu =>
    (hrates ω u hu).1.continuousWithinAt
  have hnc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ sdata T u.toNNReal ω) (Ioc 0 (T ω)) := by
    intro ω
    have hc' := (sdata ω).continuousOn_ellX_driver (h ω) (hv₀ ω).choose_spec hr
      (fun _ _ => convex_uIcc _ _) (hWI ω) (hVI ω)
      (fun u hu x hx => (hint ω u hu x hx).1) (fun u hu x hx => (hint ω u hu x hx).2)
      (hremote ω) (hseed ω) (hV₀c ω)
    have hc2 : ContinuousOn (fun u : ℝ => -Real.sqrt κ * (sdata ω).ellX u ((sdata ω).W u)) (Ioc 0 (T ω)) :=
      continuousOn_const.mul hc'
    refine hc2.congr fun u hu => ?_
    have hu0 : (0 : ℝ) ≤ u := hu.1.le
    have hpos : 0 < u.toNNReal := Real.toNNReal_pos.2 hu.1
    have hle : u.toNNReal ≤ T ω := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0]; exact hu.2
    rw [hcoord.1 ω _ hpos hle, Real.coe_toNNReal _ hu0]
  set Y : SeedGap n → ℝ≥0 → Ω → ℝ := fun i u ω => (sdata ω).gapVal i ((min u (T ω) : ℝ≥0) : ℝ) with hYdef
  have hYc : ∀ i ω, Continuous (Y i · ω) := by
    intro i ω
    have hm : Continuous fun u : ℝ≥0 => ((min u (T ω) : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_id.min continuous_const)
    exact ((hreg ω).2 i).comp_continuous hm
      (fun u => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩)
  have hYm : ∀ i u, Measurable[𝓕 u] (Y i u) := by
    intro i u
    have hgm : ∀ q : ℝ≥0, Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (sdata ω).gapVal i q) := fun q =>
      (measurable_seed_norm_and_gaps hXm hXc hdX hdφ hdζ q
        (measurableSet_ge_of_isStoppingTime hT q) (fun ω hq => hq)
        (fun ω _ => h ω) (fun ω _ => hv₀ ω)
        (fun ω hq m => ⟨r, hr, (hint ω q ⟨q.coe_nonneg, hq⟩ _ (hVI ω q ⟨q.coe_nonneg, hq⟩ m)).1⟩)
        (hVm q) hdκ hdr (hV₀m q) (hG₀m q)).1 i
    have hNc : ∀ ω, ContinuousOn (fun q : ℝ≥0 => {ω | q ≤ T ω}.indicator (fun ω => (sdata ω).gapVal i q) ω)
        (Icc 0 (T ω)) := by
      intro ω
      refine (((hreg ω).2 i).comp NNReal.continuous_coe.continuousOn
        (fun q hq => ⟨q.coe_nonneg, NNReal.coe_le_coe.2 hq.2⟩)).congr fun q hq => ?_
      simp only [Function.comp_apply]
      exact indicator_of_mem (show ω ∈ {ω | q ≤ T ω} from hq.2) _
    have hst := A1RectLaw.measurable_stopped_of_continuousOn hgm hT hNc u
    have heq : (fun ω => {ω | min u (T ω) ≤ T ω}.indicator
        (fun ω => (sdata ω).gapVal i (min u (T ω) : ℝ≥0)) ω) = Y i u := by
      funext ω
      have hmem : ω ∈ {ω' | min u (T ω) ≤ T ω'} := min_le_right u (T ω)
      exact indicator_of_mem hmem (fun ω' => (sdata ω').gapVal i (min u (T ω) : ℝ≥0))
    rw [← heq]
    exact hst
  have hYv : ∀ ω i (u : ℝ≥0), 0 < u → u ≤ T ω → Y i u ω = (sdata ω).gapVal i u := by
    intro ω i u _ hu
    simp only [hYdef, min_eq_left hu]
  have hne : ∀ ω i (u : ℝ≥0), 0 < u → u ≤ T ω → Y i u ω ≠ 0 := by
    intro ω i u hu0 hu
    rw [hYv ω i u hu0 hu]
    exact hgn ω i u ⟨NNReal.coe_pos.2 hu0, NNReal.coe_le_coe.2 hu⟩
  have hc20 : ∀ ω, ContinuousOn (sdata ω).A20 (Icc 0 (T ω)) := fun ω u hu =>
    ((h ω).hasDerivWithinAt_frzImg (hv₀ ω).choose_spec hu).continuousWithinAt
  have hne20 : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → (sdata ω).A 0 t ≠ (sdata ω).A20 t := fun ω t ht he =>
    ((h ω).frzImg_sub_ne_zero (hv₀ ω).choose_spec ht) (sub_eq_zero.2 he.symm)
  have hi : ∀ ω, (sdata ω).ImageEntranceIntegrable (T ω) := fun ω =>
    (sdata ω).imageEntranceIntegrable_of_seed (h ω) hr (fun _ _ => convex_uIcc _ _) (hWI ω) (hVI ω)
      (fun u hu x hx => (hint ω u hu x hx).1) (fun u hu x hx => (hint ω u hu x hx).2) (hseed ω)
  have hTU : ∀ ω, T ω ≤ Tm.toNNReal := fun ω => by
    rw [← NNReal.coe_le_coe]
    exact (hTm ω).trans (Real.le_coe_toNNReal Tm)
  have hA0 : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω), |(sdata ω).A 0 t| ≤ max Γ 0 := by
    intro ω t ht
    show |frzA (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ 0 t| ≤ _
    rw [(h ω).frzA_zero ht]
    exact ((hd9ω ω).drv t ht).trans (le_max_left _ _)
  have hA1 : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (T ω), a₀ ≤ (sdata ω).A 1 t := fun ω u hu => by
    change a₀ ≤ frzA (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ 1 u
    rw [hdφ ω]
    exact (hd9ω ω).d9.A1 u hu
  obtain ⟨hCc, hCm, hcm, hcap, hcont⟩ := exists_seedCapacityBrownian_actual_source hκ rr hdW hdκ hdr hXm hXc hdX
    hdφ hdζ hTU hT (le_max_right Γ 0) hC hr₀ ha₀ hr h hv₀ (fun ω => (hd9ω ω).d9.clr) hA1
    (fun ω m u hu => (hint ω u hu _ (hVI ω u hu m)).1) hA0
    (fun ω u hu => (hrates ω u (Ioc_subset_Icc_self hu)).1.mono Ioc_subset_Icc_self)
    (fun ω m u hu => (hseed ω m).hasDerivWithinAt_pos (h ω).cont hu) hD hpred.isStronglyProgressive hb hnc hVm
    hBh hBc hYc hYm hYv hne (fun ω m => (hseed ω m).cont) hc20 hne20 hi e hρL hρR
  exact ⟨B, hCc, hCm, hcm, hcap, hcont⟩

end Column

end InteractingSLE.ZhanGT4.A1ELaw
