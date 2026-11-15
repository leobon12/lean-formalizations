/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField7Label

/-!
# C.4 at `κ = 4`: the pocket step at a birth

Packet PROVE-WHOLEFIELD7 (follow-up note C.4, `source/external/AstraIG1/ig1_followup_proofs.txt` L1651–1704; C.3,
L1546–1650; ruling R38).

**The birth step** (`ae_condExp_exp_eq_kerCF_of_birth`). Let `ψ = ψI + ψJ` where every point of `supp ψI` is
swallowed at one time `β` (the labels born last) and every point of `supp ψJ` earlier. Suppose the kernel identity
`E[e^{i(h,ψ)} | 𝓕_τ] = kerCF_τ(ψ)` is known at every bounded driving stop `τ < ζ` on an event `Q τ` (the induction
hypothesis: then `ψI` is active and `ψJ` consists of earlier pockets), and that `Q t` holds for all `t` in a left
neighbourhood of `β`. Then the identity holds at every bounded driving stop `σ ≥ β`.

Proof: the birth sequence `ρₙ ↑ β` of the compact set `supp ψI` (`exists_birthSeq_kernel`), capped; the first positive
term `U` of the capped sequence makes the birth stop `T = max(min(sup ρₙ, σ), U)` positive (the restart law behind
quasi-left continuity is landed only at positive stops); the birth transfer `ae_condExp_eq_of_birth` with
`ρ̌ₙ = max(min(ρₙ, σ), U) ↑ T` and `σ' = max(σ, U)`; the left limit of the kernel value (`tendsto_kerCF_of_tendsto`,
the pocket mean as a left limit for almost every point, `ae_ae_tendsto_meanAt_frozenMean`); and on the event,
`T = β`, `σ' = σ` and the kernel is frozen after `β` (`kerCF_eq_of_swallowTime_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

/-! ### Real-valued stops -/

section Stops

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ}

theorem isStoppingTime_coe_min {σ τ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓖 fun ω => ((min (σ ω) (τ ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have e : (fun ω => ((min (σ ω) (τ ω) : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min (σ ω : WithTop ℝ≥0) (τ ω : WithTop ℝ≥0) := funext fun ω => WithTop.coe_min _ _
  rw [e]; exact hσ.min hτ

theorem isStoppingTime_coe_max {σ τ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓖 fun ω => (σ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime 𝓖 fun ω => (τ ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓖 fun ω => ((max (σ ω) (τ ω) : ℝ≥0) : WithTop ℝ≥0) := by
  have e : (fun ω => ((max (σ ω) (τ ω) : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => max (σ ω : WithTop ℝ≥0) (τ ω : WithTop ℝ≥0) := funext fun ω => WithTop.coe_max _ _
  rw [e]; exact hσ.max hτ

theorem IsStoppingTime.mono_filtration {𝓖' : Filtration ℝ≥0 mΩ} (h : 𝓖 ≤ 𝓖') {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) : IsStoppingTime 𝓖' τ := fun i => h i _ (hτ i)

end Stops

/-- A compact subset of `ℍ` has a positive lower bound on its imaginary parts. -/
theorem exists_pos_le_im_of_isCompact' {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ y₀ > 0, ∀ z ∈ K, y₀ ≤ z.im := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun z hz => hz.elim⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  exact ⟨z₀.im, hKH hz₀, fun z hz => hmin hz⟩

/-- **A compact subset of `ℍ` is not reached by the hull at small positive times** (every point of `ℍ` is swallowed
at a positive time, and `ℍ \ K_t` is open). -/
theorem exists_pos_disjoint_fwdHull {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) (hζ : 0 < ζ) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ t : ℝ≥0, 0 < t ∧ (t : ℝ≥0∞) < ζ ∧ Disjoint K (fwdHull (Ito.rpath w) (t : ℝ)) := by
  obtain ⟨t₀, ht₀, ht₀ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hζ
  have ht₀' : 0 < t₀ := by exact_mod_cast ht₀
  set s : ℕ → ℝ≥0 := fun n => t₀ / ((n : ℝ≥0) + 1) with hsdef
  have hs : ∀ n, 0 < s n := fun n => div_pos ht₀' (by positivity)
  have hsle : ∀ n, s n ≤ t₀ := fun n => div_le_self (zero_le) (le_add_of_nonneg_left zero_le)
  have hsζ : ∀ n, (s n : ℝ≥0∞) < ζ := fun n => lt_of_le_of_lt (by exact_mod_cast hsle n) ht₀ζ
  have hanti : Antitone s := fun m n hmn => by
    simp only [hsdef]
    exact div_le_div_of_nonneg_left zero_le (by positivity) (by gcongr)
  set O : ℕ → Set ℂ := fun n => H \ fwdHull (Ito.rpath w) (s n : ℝ) with hOdef
  have hO : ∀ n, IsOpen (O n) := fun n => MartMeans2.isOpen_H_diff_fwdHull_rpath hP.2.2.2.1 (hsζ n)
  have hmono : Monotone O := fun m n hmn z hz =>
    ⟨hz.1, fun hzK => hz.2 ((QuantumZipper.fwdHull_mono).1 (by exact_mod_cast hanti hmn) hzK)⟩
  have hcov : K ⊆ ⋃ n, O n := by
    intro z hz
    have hpos := WangWu.swallowTime_pos_of_path hP hζ (hKH hz)
    obtain ⟨r, hr, hrs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    obtain ⟨n, hn⟩ := exists_nat_gt ((t₀ : ℝ) / r)
    have hsn : (s n : ℝ) < r := by
      simp only [hsdef, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hr'] at hn
      nlinarith
    refine mem_iUnion.2 ⟨n, hKH hz, fun hzK => ?_⟩
    have h1 := hzK.2
    rw [ENNReal.ofReal_coe_nnreal] at h1
    have h2 : (s n : ℝ≥0∞) < r := by exact_mod_cast hsn
    exact absurd (h1.trans_lt (h2.trans hrs)) (lt_irrefl _)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover O hO hcov hmono.directed_le
  exact ⟨s n, hs n, hsζ n, Set.disjoint_left.2 fun z hz hzK => (hn hz).2 hzK⟩

/-! ### The birth step -/

section Birth

universe v

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A birth at `β`**: `CI` is nonempty and swallowed at once at time `β`, every point of `CJ` earlier. -/
def IsBirthAt (w : ℝ≥0 → ℝ) (CI CJ : Set ℂ) (β : ℝ≥0) : Prop :=
  CI.Nonempty ∧ (∀ z ∈ CI, swallowTime (Ito.rpath w) z = β) ∧ ∀ z ∈ CJ, swallowTime (Ito.rpath w) z < β

omit mΩ [IsProbabilityMeasure P] in
/-- A pocket observable `1_F e^{i(h,ψ)}` is a germ observable when `supp ψ` lies in every germ neighbourhood of
`A` on `F`. -/
theorem stronglyMeasurable_indicator_exp_histGerm {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    {ℋ : MeasurableSpace Ω} {A : Ω → Set ℂ} {ψ : TestOn upperHalfPlaneOpens} {F : Set Ω}
    (hF : MeasurableSet[ℋ] F) (hFsub : ∀ ω ∈ F, ∀ δ : ℝ, 0 < δ → tsupport ψ ⊆ germNbhd δ (A ω)) :
    StronglyMeasurable[histGerm ℋ A (centredField h u₀)]
      (F.indicator fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) := by
  set c : ℝ := ∫ z, u₀ z * ψ z with hc
  have e : (F.indicator fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ))) =
      F.indicator fun ω => (fun x : ℝ => Complex.exp (Complex.I * ((x + c : ℝ) : ℂ)))
        (centredField h u₀ ω ψ) := by
    congr 1; funext ω
    simp only [centredField_apply h hu₀ ω ψ, hc, sub_add_cancel]
  rw [e]
  exact stronglyMeasurable_indicator_histGerm hF hFsub
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_id.add_const c))))

omit [IsProbabilityMeasure P] in
/-- **The frozen mean is almost everywhere a bounded measurable function at a bounded stop**, almost surely (the
jointly measurable version of Lemma 3.5, `WangWu.exists_frozenMean_version`). -/
theorem ae_isMeanGood [IsProbabilityMeasure P] (hE : WangWu.IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {σ₀ : Ω → ℝ≥0} (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N) :
    ∀ᵐ ω ∂P, IsMeanGood ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) := by
  obtain ⟨Yv, hYm, hYb, -, hYae⟩ := WangWu.exists_frozenMean_version hE hσ₀ hσ₀ζ hσ₀N
  filter_upwards [hYae] with ω hω
  refine ⟨fun z => Yv (σ₀ ω) z ω, (hYm (σ₀ ω)).comp measurable_prodMk_right, fun z => hYb _ _ _, ?_⟩
  filter_upwards [hω] with z hz hzH
  rw [hz hzH (σ₀ ω), min_self]

/-- **C.4, the pocket step at a birth.** Let `ψ = ψI + ψJ`. Suppose the kernel identity
`E[e^{i(h,ψ)} | 𝓕_τ] = kerCF_τ(ψ)` holds at every bounded driving stop `τ < ζ` almost surely on `{Q τ}` (`hIH`), and
that `Q t` holds on a left neighbourhood of `β` whenever `Ev β` (`hQ`). Then at every bounded driving stop `σ < ζ`,
almost surely, for every birth time `β ≤ σ` of `supp ψI` (with `supp ψJ` swallowed earlier) with `Ev β`, the identity
holds at `σ`. -/
theorem ae_condExp_exp_eq_kerCF_of_birth (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσN : ∀ ω, σ ω ≤ N)
    (ψI ψJ : TestOn upperHalfPlaneOpens) (Q : ℝ≥0 → Ω → Prop) (Ev : Ω → ℝ≥0 → Prop)
    (hIH : ∀ (τ : Ω → ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) fun ω => (τ ω : WithTop ℝ≥0)),
      (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) → (∀ ω, τ ω ≤ N + 1) →
      ∀ᵐ ω ∂P, Q (τ ω) ω →
        (P[fun ω' => Complex.exp (Complex.I * (h ω' (ψI + ψJ) : ℂ)) | hτ.measurableSpace]) ω =
          kerCF ρL ρR W VL VR (τ ω) (⇑(ψI + ψJ)) ω)
    (hQ : ∀ ω β, 0 < β → Ev ω β → ∃ t₀ < β, ∀ t, t₀ ≤ t → t < β → Q t ω) :
    ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω → Ev ω β → IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (ψI + ψJ) : ℂ)) | hσ.measurableSpace]) ω =
        kerCF ρL ρR W VL VR (σ ω) (⇑(ψI + ψJ)) ω := by
  have hE := hC.1
  have hh := hC.2.1
  set K : Set ℂ := tsupport ψI with hKdef
  have hK : IsCompact K := ψI.hasCompactSupport.isCompact
  have hKH : K ⊆ H := ψI.tsupport_subset
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact' hK hKH
  obtain ⟨ρ, hρ, A, -, hρm, hρζ, hdA, hexh, -, hAK, -, -⟩ :=
    exists_birthSeq_kernel hC (by norm_num) hu₀ hX (not_threshold_seed_of_ae_lt hE hσζ) hK hKH hm hKm
  have hζpos : ∀ᵐ ω ∂P, 0 < ζ ω := hσζ.mono fun ω hω => lt_of_le_of_lt bot_le hω
  -- capped birth sequence and its first positive term
  obtain ⟨ρc, hρcdef⟩ : ∃ ρc : ℕ → Ω → ℝ≥0, ρc = fun n ω => min (ρ n ω) (N + 1) := ⟨_, rfl⟩
  have hρc : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρc n ω : WithTop ℝ≥0) := fun n => by
    have e : (fun ω => (ρc n ω : WithTop ℝ≥0)) = fun ω => min (ρ n ω : WithTop ℝ≥0) ((N + 1 : ℝ≥0) : WithTop ℝ≥0) :=
      funext fun ω => by rw [hρcdef]; exact WithTop.coe_min _ _
    rw [e]; exact (hρ n).min_const _
  have hρcm : ∀ ω, Monotone fun n => ρc n ω := fun ω _ _ hmn => by
    rw [hρcdef]; exact min_le_min_right _ (hρm ω hmn)
  have hρcN : ∀ n ω, ρc n ω ≤ N + 1 := fun n ω => by rw [hρcdef]; exact min_le_right _ _
  have hρcle : ∀ n ω, ρc n ω ≤ ρ n ω := fun n ω => by rw [hρcdef]; exact min_le_left _ _
  have hbdd : ∀ ω, BddAbove (range fun n => ρc n ω) := fun ω => ⟨N + 1, by rintro _ ⟨n, rfl⟩; exact hρcN n ω⟩
  obtain ⟨U, hUdef⟩ : ∃ U : Ω → ℝ≥0, U = firstPos ρc := ⟨_, rfl⟩
  have hU : IsStoppingTime (drivingFiltration P hX) fun ω => (U ω : WithTop ℝ≥0) := by
    rw [hUdef]; exact isStoppingTime_firstPos hρc
  have hUN : ∀ ω, U ω ≤ N + 1 := fun ω => by
    rcases firstPos_eq_zero_or (ρ := ρc) ω with h0 | ⟨n, hn⟩
    · rw [hUdef, h0]; exact zero_le
    · rw [hUdef, hn]; exact hρcN n ω
  obtain ⟨ρi, hρidef⟩ : ∃ ρi : Ω → ℝ≥0, ρi = fun ω => ⨆ n, ρc n ω := ⟨_, rfl⟩
  have hρi : IsStoppingTime (drivingFiltration P hX) fun ω => (ρi ω : WithTop ℝ≥0) := by
    rw [hρidef]; exact WangWu.isStoppingTime_iSup_coe hρc hρcN
  -- the birth stop, the later stop, the announcing stops
  obtain ⟨T, hTdef⟩ : ∃ T : Ω → ℝ≥0, T = fun ω => max (min (ρi ω) (σ ω)) (U ω) := ⟨_, rfl⟩
  have hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0) := by
    rw [hTdef]; exact isStoppingTime_coe_max (isStoppingTime_coe_min hρi hσ) hU
  obtain ⟨σ', hσ'def⟩ : ∃ σ' : Ω → ℝ≥0, σ' = fun ω => max (σ ω) (U ω) := ⟨_, rfl⟩
  have hσ' : IsStoppingTime (drivingFiltration P hX) fun ω => (σ' ω : WithTop ℝ≥0) := by
    rw [hσ'def]; exact isStoppingTime_coe_max hσ hU
  obtain ⟨ρv, hρvdef⟩ : ∃ ρv : ℕ → Ω → ℝ≥0, ρv = fun n ω => max (min (ρc n ω) (σ ω)) (U ω) := ⟨_, rfl⟩
  have hρv : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρv n ω : WithTop ℝ≥0) := fun n => by
    rw [hρvdef]; exact isStoppingTime_coe_max (isStoppingTime_coe_min (hρc n) hσ) hU
  have hρvm : ∀ ω, Monotone fun n => ρv n ω := fun ω _ _ hmn => by
    rw [hρvdef]; exact max_le_max_right _ (min_le_min_right _ (hρcm ω hmn))
  have hρvT : ∀ n ω, ρv n ω ≤ T ω := fun n ω => by
    rw [hρvdef, hTdef, hρidef]; exact max_le_max_right _ (min_le_min_right _ (le_ciSup (hbdd ω) n))
  have hρvlim : ∀ ω, Tendsto (fun n => ρv n ω) atTop (𝓝 (T ω)) := fun ω => by
    rw [hρvdef, hTdef, hρidef]
    exact ((tendsto_atTop_ciSup (hρcm ω) (hbdd ω)).min tendsto_const_nhds).max tendsto_const_nhds
  have hTσ' : ∀ ω, T ω ≤ σ' ω := fun ω => by
    rw [hTdef, hσ'def]; exact max_le_max_right _ (min_le_right _ _)
  have hρvN : ∀ n ω, ρv n ω ≤ N + 1 := fun n ω => by
    rw [hρvdef]
    exact max_le ((min_le_right _ _).trans ((hσN ω).trans (le_add_of_nonneg_right zero_le))) (hUN ω)
  have hUζ : ∀ᵐ ω ∂P, (U ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [ae_all_iff.2 hρζ, hζpos] with ω h1 h0
    rcases firstPos_eq_zero_or (ρ := ρc) ω with hz | ⟨n, hn⟩
    · rw [hUdef, hz, ENNReal.coe_zero]; exact h0
    · rw [hUdef, hn]; exact lt_of_le_of_lt (by exact_mod_cast hρcle n ω) (h1 n)
  have hσ'ζ : ∀ᵐ ω ∂P, (σ' ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hσζ, hUζ] with ω h1 h2
    rw [hσ'def]; simp only [ENNReal.coe_max]
    exact max_lt h1 h2
  have hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω := hσ'ζ.mono fun ω hω =>
    lt_of_le_of_lt (by exact_mod_cast hTσ' ω) hω
  have hρvζ : ∀ n, ∀ᵐ ω ∂P, (ρv n ω : ℝ≥0∞) < ζ ω := fun n => hTζ.mono fun ω hω =>
    lt_of_le_of_lt (by exact_mod_cast hρvT n ω) hω
  have hU0 : ∀ᵐ ω ∂P, 0 < U ω := by
    filter_upwards [hexh, hE.2.2.2.2, hζpos] with ω hex hp h0
    obtain ⟨t, ht0, htζ, htd⟩ := exists_pos_disjoint_fwdHull hp h0 hK hKH
    obtain ⟨n, hn⟩ := (hex t htζ htd).exists
    rw [hUdef]
    exact firstPos_pos ⟨n, by rw [hρcdef]; exact lt_min (ht0.trans_le hn) (by positivity)⟩
  have hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j :=
    hU0.mono fun ω hω => Or.inl (hω.trans_le (by rw [hTdef]; exact le_max_right _ _))
  -- the facts on the event
  have hev : ∀ᵐ ω ∂P, ∀ β : ℝ≥0, β ≤ σ ω → IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
      T ω = β ∧ σ' ω = σ ω ∧ (∀ n, ρ n ω < β) ∧ (∀ᶠ n in atTop, ρv n ω = ρ n ω) ∧
        Tendsto (fun n => ρ n ω) atTop (𝓝 β) ∧ 0 < β := by
    filter_upwards [ae_all_iff.2 hdA, ae_all_iff.2 hAK, hexh, hσζ, hE.2.2.2.2] with ω hd hak hex hσω hp
      β hβσ hb
    obtain ⟨⟨z₀, hz₀⟩, hsI, -⟩ := hb
    have hlt : ∀ n, ρ n ω < β := fun n => by
      by_contra hle
      refine Set.disjoint_left.1 (hd n) hz₀ ?_
      rw [hak n]
      refine ⟨hKH hz₀, ?_⟩
      show swallowTime (Ito.rpath (W · ω)) z₀ ≤ ENNReal.ofReal ((ρ n ω : ℝ≥0) : ℝ)
      rw [hsI z₀ hz₀, ENNReal.ofReal_coe_nnreal]
      exact_mod_cast not_lt.1 hle
    have hβN : β < N + 1 := lt_of_le_of_lt (hβσ.trans (hσN ω)) (lt_add_one N)
    have hρc_eq : ∀ n, ρc n ω = ρ n ω := fun n => by
      rw [hρcdef]; exact min_eq_left ((hlt n).le.trans hβN.le)
    have hρi_eq : (⨆ n, ρc n ω) = β := by
      refine le_antisymm (ciSup_le fun n => (hρc_eq n ▸ hlt n).le) ?_
      refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
      have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_lt_of_le (by exact_mod_cast ht.trans_le hβσ) hσω.le
      have hdisj : Disjoint K (fwdHull (fun s : ℝ => W s.toNNReal ω) (t : ℝ)) :=
        isActiveLabel_of_lt_swallowTime (w := (W · ω)) (C := K) (t := t) fun z hz => by
          rw [hsI z hz]; exact_mod_cast ht
      obtain ⟨n, hn⟩ := (hex t htζ hdisj).exists
      exact hn.trans ((hρc_eq n).symm ▸ le_ciSup (hbdd ω) n)
    have hUβ : U ω ≤ β := by
      rcases firstPos_eq_zero_or (ρ := ρc) ω with hz | ⟨n, hn⟩
      · rw [hUdef, hz]; exact zero_le
      · rw [hUdef, hn, hρc_eq n]; exact (hlt n).le
    have hβpos : 0 < β := by
      have h1 := WangWu.swallowTime_pos_of_path hp (lt_of_le_of_lt bot_le hσω) (hKH hz₀)
      rw [hsI z₀ hz₀] at h1
      exact_mod_cast h1
    have hρlim : Tendsto (fun n => ρ n ω) atTop (𝓝 β) := by
      have := tendsto_atTop_ciSup (hρcm ω) (hbdd ω)
      rw [hρi_eq] at this
      exact this.congr fun n => hρc_eq n
    refine ⟨?_, by rw [hσ'def]; exact max_eq_left (hUβ.trans hβσ), hlt, ?_, hρlim, hβpos⟩
    · rw [hTdef, hρidef]; show max (min (⨆ n, ρc n ω) (σ ω)) (U ω) = β
      rw [hρi_eq, min_eq_left hβσ, max_eq_left hUβ]
    · filter_upwards [hρlim.eventually (lt_mem_nhds hβpos)] with n hn
      have hU : U ω ≤ ρc n ω := by rw [hUdef]; exact firstPos_le (hρcm ω) (by rw [hρc_eq n]; exact hn)
      rw [hρvdef]; show max (min (ρc n ω) (σ ω)) (U ω) = ρ n ω
      rw [min_eq_left ((hρc_eq n).symm ▸ (hlt n).le.trans hβσ), max_eq_left hU, hρc_eq n]
  -- hull version at the birth stop and the pocket event
  have hTN : ∀ ω, T ω ≤ N + 1 := fun ω => (hTσ' ω).trans (by
    rw [hσ'def]; exact max_le ((hσN ω).trans (le_add_of_nonneg_right zero_le)) (hUN ω))
  obtain ⟨AT, hATm, hATK, hAT𝓕⟩ := exists_hullVersion hC (by norm_num) hX hT hTζ
  obtain ⟨F, hFm, hFsub, hFmem⟩ := exists_pocketEvent hAT𝓕 (ψI + ψJ).tsupport_subset
  have hFZ := stronglyMeasurable_indicator_exp_histGerm (h := h) hu₀.1 hFm hFsub
  -- frozen means at the announcing stops; left limits at the birth stop
  have hdu : drivingFiltration P hX ≤ usualAugmentation 𝓕 P := Ito.drivingFiltration_le_usualAugmentation hE hX
  have hmg : ∀ᵐ ω ∂P, ∀ n, IsMeanGood ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (ρv n ω) :=
    ae_all_iff.2 fun n => ae_isMeanGood hE (IsStoppingTime.mono_filtration hdu (hρv n)) (hρvζ n) (hρvN n)
  have hLT := ae_ae_tendsto_meanAt_frozenMean (ρL := ρL) (ρR := ρR) hE (IsStoppingTime.mono_filtration hdu hT) hTζ hTN
  -- the supports
  have hsupp : ∀ z, z ∈ tsupport (ψI + ψJ) → z ∈ tsupport ψI ∪ tsupport ψJ := fun z hz =>
    tsupport_add (⇑ψI) (⇑ψJ) hz
  have hsle : ∀ ω β, IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β →
      ∀ z ∈ tsupport (ψI + ψJ), swallowTime (Ito.rpath (W · ω)) z ≤ β := fun ω β hb z hz => by
    rcases hsupp z hz with hz | hz
    · exact (hb.2.1 z hz).le
    · exact (hb.2.2 z hz).le
  -- the four hypotheses of the birth transfer
  set E : Set Ω := {ω | ∃ β : ℝ≥0, β ≤ σ ω ∧ Ev ω β ∧ IsBirthAt (W · ω) (tsupport ψI) (tsupport ψJ) β}
    with hEdef
  have h1 : ∀ n, ∀ᵐ ω ∂P, ω ∈ {ω | Q (ρv n ω) ω} →
      (P[fun ω' => Complex.exp (Complex.I * (h ω' (ψI + ψJ) : ℂ)) | (hρv n).measurableSpace]) ω =
        kerCF ρL ρR W VL VR (ρv n ω) (⇑(ψI + ψJ)) ω := fun n => hIH (ρv n) (hρv n) (hρvζ n) (hρvN n)
  have h2 : ∀ᵐ ω ∂P, ω ∈ E → ∀ᶠ n in atTop, ω ∈ {ω | Q (ρv n ω) ω} := by
    filter_upwards [hev] with ω hevω ⟨β, hβσ, hEv, hb⟩
    obtain ⟨-, -, hlt, hevρ, hρlim, hβpos⟩ := hevω β hβσ hb
    obtain ⟨t₀, ht₀, hQt⟩ := hQ ω β hβpos hEv
    filter_upwards [hevρ, hρlim.eventually (lt_mem_nhds ht₀)] with n hn1 hn2
    show Q (ρv n ω) ω
    rw [hn1]; exact hQt _ hn2.le (hlt n)
  have h3 : ∀ᵐ ω ∂P, ω ∈ E → Tendsto (fun n => kerCF ρL ρR W VL VR (ρv n ω) (⇑(ψI + ψJ)) ω) atTop
      (𝓝 (kerCF ρL ρR W VL VR (T ω) (⇑(ψI + ψJ)) ω)) := by
    filter_upwards [hev, hmg, hLT, hE.2.2.2.2, hTζ] with ω hevω hmω hLω hp hTω ⟨β, hβσ, hEv, hb⟩
    obtain ⟨hTβ, -, hlt, hevρ, -, -⟩ := hevω β hβσ hb
    rw [hTβ] at hTω hLω ⊢
    have hρvβ : Tendsto (fun n => ρv n ω) atTop (𝓝 β) := hTβ ▸ hρvlim ω
    have hρvle : ∀ n, ρv n ω ≤ β := fun n => hTβ ▸ hρvT n ω
    have hρvlt : ∀ᶠ n in atTop, ρv n ω < β := by
      filter_upwards [hevρ] with n hn
      rw [hn]; exact hlt n
    have hL : ∀ᵐ z ∂(volume : Measure ℂ), (ψI + ψJ) z ≠ 0 →
        swallowTime (Ito.rpath (W · ω)) z ≤ β ∧
        Tendsto (fun r => WangWu.meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
          (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
          (𝓝 (WangWu.frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) β z)) := by
      filter_upwards [hLω] with z hz hψz
      have hzs : z ∈ tsupport (ψI + ψJ) := subset_tsupport _ hψz
      have hzH : z ∈ H := (ψI + ψJ).tsupport_subset hzs
      have hs := hsle ω β hb z hzs
      exact ⟨hs, hz hzH hs⟩
    refine tendsto_kerCF_of_tendsto hp hTω hρvβ hρvle (ψI + ψJ) hmω ?_ ?_
    · filter_upwards [hL] with z hz hψz
      obtain ⟨hs, hlim⟩ := hz hψz
      have hzs : z ∈ tsupport (ψI + ψJ) := subset_tsupport _ hψz
      rcases hsupp z hzs with hzI | hzJ
      · have hsz : swallowTime (Ito.rpath (W · ω)) z = β := hb.2.1 z hzI
        rw [hsz, ENNReal.toNNReal_coe] at hlim
        have hρv' : Tendsto (fun n => ρv n ω) atTop (𝓝[<] β) :=
          tendsto_nhdsWithin_iff.2 ⟨hρvβ, hρvlt⟩
        refine (hlim.comp hρv').congr' ?_
        filter_upwards [hρvlt] with n hn
        have hlt' : ((ρv n ω : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z := by
          rw [hsz]; exact_mod_cast hn
        simp only [Function.comp_apply, WangWu.frozenMean, hlt', ↓reduceIte]
      · have hsz : swallowTime (Ito.rpath (W · ω)) z < β := hb.2.2 z hzJ
        have hne : swallowTime (Ito.rpath (W · ω)) z ≠ ⊤ := ne_top_of_lt hsz
        have hr : (swallowTime (Ito.rpath (W · ω)) z).toNNReal < β := by
          rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hne]; exact hsz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hρvβ.eventually (lt_mem_nhds hr)] with n hn
        have hle : swallowTime (Ito.rpath (W · ω)) z ≤ ρv n ω := by
          rw [← ENNReal.coe_toNNReal hne]; exact_mod_cast hn.le
        exact frozenMean_eq_of_swallowTime_le hle (hρvle n)
    · filter_upwards [hL] with z hz hψz n
      obtain ⟨hs, hlim⟩ := hz hψz
      have hzH : 0 < z.im := (ψI + ψJ).tsupport_subset (subset_tsupport _ hψz)
      by_cases hn : ((ρv n ω : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z
      · simp only [WangWu.frozenMean, hn, ↓reduceIte, WangWu.meanAt]
        exact WangWu.abs_condMean_le _ _ _ _ _
      · have hle : swallowTime (Ito.rpath (W · ω)) z ≤ ρv n ω := not_lt.1 hn
        rw [frozenMean_eq_of_swallowTime_le hle (hρvle n) |>.symm]
        have hb' := (WangWu.frozenMean_path_facts hp hTω hzH fun _ => hlim).2 β
        rwa [min_self] at hb'
  have h4 : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ T ω ≤ σ' ω := by
    filter_upwards [hev, hATK] with ω hevω hATω ⟨β, hβσ, hEv, hb⟩
    obtain ⟨hTβ, -⟩ := hevω β hβσ hb
    refine ⟨hFmem ω ?_, hTσ' ω⟩
    rw [hATω, hTβ]
    intro z hz
    refine ⟨(ψI + ψJ).tsupport_subset hz, ?_⟩
    show swallowTime (Ito.rpath (W · ω)) z ≤ ENNReal.ofReal ((β : ℝ≥0) : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
    exact hsle ω β hb z hz
  have hbirth := ae_condExp_eq_of_birth hC (by norm_num) hu₀ hX hT hσ' hTζ hT0 hρv hρvm hρvT
    (Eventually.of_forall hρvlim) hATm hATK (aestronglyMeasurable_exp_pairing hh (ψI + ψJ))
    (fun ω => norm_exp_I_mul_pairing (ψI + ψJ) ω) hFm hFZ h1 h2 h3 h4
  -- from `σ' = max(σ, U)` back to `σ`
  have hmin := condExp_min_stopping_time_ae_eq_restrict_le (μ := P)
    (f := fun ω' => Complex.exp (Complex.I * (h ω' (ψI + ψJ) : ℂ))) hσ' hσ
  have hcongr : (hσ'.min hσ).measurableSpace = hσ.measurableSpace :=
    IsStoppingTime.measurableSpace_congr _ _ (funext fun ω => min_eq_right
      (WithTop.coe_le_coe.2 (by rw [hσ'def]; exact le_max_left _ _)))
  rw [hcongr] at hmin
  have hmin' := ae_imp_of_ae_restrict hmin
  filter_upwards [hbirth, hmin', hev] with ω hb1 hb2 hevω β hβσ hEv hb
  obtain ⟨hTβ, hσ'σ, -⟩ := hevω β hβσ hb
  have hωE : ω ∈ E := ⟨β, hβσ, hEv, hb⟩
  rw [hb2 (show ((σ' ω : ℝ≥0) : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0) by rw [hσ'σ]), hb1 hωE, hTβ]
  exact (kerCF_eq_of_swallowTime_le (fun z hz => hsle ω β hb z (subset_tsupport _ hz)) hβσ).symm

end Birth

end WholeField

end InteractingSLE
