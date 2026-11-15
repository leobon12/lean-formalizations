/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofSol

/-!
# DS2 in reach form, X: pathwise uniqueness and the proof of `DS2ReachStatement`

Packet PROVE-T14-DS. The last steps of the proof of Lemma DS2 (spec p. 553) in the reach form
(`DSReach.DS2ReachStatement`, follow-up note A.3):

* `mem_reachSet_of_limitProps` (**pathwise uniqueness**): two pairs `(f, β)`, `(f', β)` with `LimitProps` for a
  separated DS1 word and the *same* Brownian path agree up to the exit of `f` from the outer open buffer
  (`Sec2.UpTo.agree_of_lt_min`), so one is in the reach set exactly when the other is;
* **`ds2ReachStatement`**: by contradiction along a subsequence with reach probabilities below `c`: tightness
  (`isTightMeasureSet_laws`) and Prokhorov give a weak limit `π`; `π` and the law of the limiting evolution both
  satisfy `LimitProps` (`ae_limitProps`, the latter for the constant sequence) and have the Wiener law as Brownian
  marginal; the conditionally independent gluing (`exists_glue`) and pathwise uniqueness give
  `π(reach) = P₀(reach)`; Portmanteau for the open reach set gives `π(reach) ≤ c`.

This replaces the source's limiting martingale problem and "integrated weak uniqueness" (Yamada–Watanabe instead of
the Brownian martingale identities in the limiting filtration), as recommended in
`planning/handoffs/PROVE-T14-TIP7.md` §5.2.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2
open scoped PathMeas

section Unique

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {T : ℝ≥0} {xL₀ : Fin nL → ℝ} {xR₀ : Fin nR → ℝ}
  {ρL₀ : Fin nL → ℝ} {ρR₀ : Fin nR → ℝ}

/-- Continuous paths agreeing before `t` agree at `t`, when they agree at `0`. -/
theorem eq_of_forall_lt {X : Type*} [TopologicalSpace X] [T2Space X] {φ ψ : ℝ≥0 → X} (hφ : Continuous φ)
    (hψ : Continuous ψ) (h0 : φ 0 = ψ 0) {t : ℝ≥0} (h : ∀ s < t, φ s = ψ s) : φ t = ψ t := by
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht]; exact h0
  · have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.2 ht⟩
    exact tendsto_nhds_unique ((hφ.tendsto t).mono_left (nhdsWithin_le_nhds (s := Iio t)))
      (((hψ.tendsto t).mono_left (nhdsWithin_le_nhds (s := Iio t))).congr'
        (eventually_nhdsWithin_of_forall (s := Iio t) fun s hs => (h s hs).symm))

/-- **Pathwise uniqueness for limits driven by one Brownian path.** -/
theorem mem_reachSet_of_limitProps (hε : 0 < ε) (hg : 0 < g) (hw0 : IsDS1Word mL mR Rw ε xL₀ xR₀ ρL₀ ρR₀)
    (hsep : ∀ i j, xL₀ i < xR₀ j) {f f' : C(Set.Icc (0 : ℝ≥0) T, SState nL nR)} {β : C(Set.Icc (0 : ℝ≥0) T, ℝ)}
    (h : LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ f β) (h' : LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ f' β)
    {O Bf : Set (SState nL nR)} (hBf : Bf ⊆ oBuf mL mR R g) (hf : f ∈ reachSet T O Bf) :
    f' ∈ reachSet T O Bf := by
  obtain ⟨t, htT, htO, htB⟩ := hf
  set t₀ : ℝ≥0 := (t : ℝ≥0) with ht₀
  -- `f` stays in the outer open buffer up to `t`
  have hU : ∀ s : ℝ≥0, s < t₀ → pathAt f s ∈ oBuf mL mR R g := fun s hs => by
    have hsT : s ≤ T := (hs.le.trans t.2.2)
    rw [pathAt_of_le f hsT]
    exact hBf (htB ⟨s, zero_le, hsT⟩ (Subtype.mk_le_mk.2 hs.le))
  have hup := h.isSLEPathUpTo hε hg hw0 t.2.2 hU
  -- the exit time of `f'`
  set S' : Set ℝ≥0 := {s | s ≤ T ∧ ∀ u < s, pathAt f' u ∈ oBuf mL mR R g} with hS'
  have hS'ne : S'.Nonempty := ⟨0, zero_le, fun u hu => absurd hu (not_lt.2 zero_le)⟩
  have hS'bdd : BddAbove S' := ⟨T, fun s hs => hs.1⟩
  set σ := sSup S' with hσ
  have hσT : σ ≤ T := csSup_le hS'ne fun s hs => hs.1
  have hU' : ∀ u : ℝ≥0, u < σ → pathAt f' u ∈ oBuf mL mR R g := fun u hu => by
    obtain ⟨s, hs, hus⟩ := exists_lt_of_lt_csSup hS'ne hu
    exact hs.2 u hus
  have hup' := h'.isSLEPathUpTo hε hg hw0 hσT hU'
  have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) < min (t₀ : ℝ≥0∞) σ → pathAt f u = pathAt f' u := fun u hu => by
    obtain ⟨h1, h2, h3⟩ := Sec2.UpTo.agree_of_lt_min hsep hup hup.driverEq hup' hup'.driverEq hu
    exact Prod.ext h1 (Prod.ext (funext h2) (funext h3))
  have h00 : pathAt f 0 = pathAt f' 0 := by rw [h.1, h'.1]
  -- the exit of `f'` is after `t`
  have hlt : t₀ < σ := by
    by_contra hcon
    push Not at hcon
    have hagσ : pathAt f σ = pathAt f' σ := eq_of_forall_lt (continuous_pathAt f) (continuous_pathAt f')
      h00 fun s hs => hag s (by rw [min_eq_right (by exact_mod_cast hcon)]; exact_mod_cast hs)
    have hmem : pathAt f' σ ∈ oBuf mL mR R g := by
      rw [← hagσ, pathAt_of_le f hσT]
      exact hBf (htB ⟨σ, zero_le, hσT⟩ (Subtype.mk_le_mk.2 hcon))
    have hσT' : σ < T := lt_of_le_of_lt hcon htT
    -- `f'` stays in the open buffer a little after `σ`
    have hev : ∀ᶠ u in 𝓝 σ, pathAt f' u ∈ oBuf mL mR R g :=
      (continuous_pathAt f').continuousAt.preimage_mem_nhds ((isOpen_oBuf mL mR R g).mem_nhds hmem)
    obtain ⟨v, hv, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (lt_add_one σ)).1
      (hev.filter_mono nhdsWithin_le_nhds)
    set s := min v T
    have hσs : σ < s := lt_min hv hσT'
    have hsS : s ∈ S' := by
      refine ⟨min_le_right _ _, fun u hu => ?_⟩
      rcases lt_or_ge u σ with h1 | h1
      · exact hU' u h1
      · exact hsub ⟨h1, lt_of_lt_of_le hu (min_le_left _ _)⟩
    exact absurd (le_csSup hS'bdd hsS) (not_le.2 hσs)
  have hag' : ∀ u : ℝ≥0, u ≤ t₀ → pathAt f u = pathAt f' u := by
    have hlt' : ∀ u : ℝ≥0, u < t₀ → pathAt f u = pathAt f' u := fun u hu =>
      hag u (by rw [min_eq_left (by exact_mod_cast hlt.le)]; exact_mod_cast hu)
    intro u hu
    rcases lt_or_eq_of_le hu with h1 | h1
    · exact hlt' u h1
    · rw [h1]; exact eq_of_forall_lt (continuous_pathAt f) (continuous_pathAt f') h00 hlt'
  refine ⟨t, htT, ?_, fun u hu => ?_⟩
  · have := hag' t₀ le_rfl
    rw [pathAt_coe, pathAt_coe] at this
    rw [← this]
    exact htO
  · have := hag' u (Subtype.coe_le_coe.2 hu)
    rw [pathAt_coe, pathAt_coe] at this
    rw [← this]
    exact htB u hu

end Unique

/-! ### The proof of `DS2ReachStatement` -/

/-- **Lemma DS2 in reach form** (spec p. 553; follow-up note A.3): `P₀(reach) ≤ liminf_m P_m(reach)` for every
horizon, open target and open inner buffer. -/
theorem ds2ReachStatement : DS2ReachStatement.{u} := by
  intro κ hκ nL nR hnL hnR mL mR Rw ε a g η hε ha hg _ xL xR ρL ρR xL₀ xR₀ ρL₀ ρR₀ hw hw₀ hcr hcr₀
    hxL hxR hρL hρR _ _ _ _ Ω mΩ P 𝓕 W VL VR B ζ hE Ω₀ mΩ₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hE₀ T R O Bf hO hBo hBR
  have hP : ∀ m, IsProbabilityMeasure (P m) := fun m => (hE m).1.isProbabilityMeasure'
  have hP₀ : IsProbabilityMeasure P₀ := hE₀.1.isProbabilityMeasure'
  have hRw : 0 ≤ Rw := (abs_nonneg _).trans (hw₀.2.2.1 ⟨0, hnR⟩)
  set s₀ : SState nL nR := ((0 : ℝ), xL₀, xR₀) with hs₀def
  -- if the limiting initial state is not in the buffer, the reach event is null
  by_cases hs₀ : s₀ ∈ Bf
  swap
  · have hnull : P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀) = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hE₀.2.2.2.2)
      rintro ω ⟨t, -, -, -, hB⟩ hpath
      apply hs₀
      have h0 := hB 0 zero_le
      have hup := hpath.isSLEPathUpTo le_rfl
      have e : Coupling.stateAt W₀ VL₀ VR₀ 0 ω = s₀ := by
        simp only [Coupling.stateAt, hs₀def]
        rw [hup.w_zero]
        congr 1
        exact Prod.ext (funext hup.vL_zero) (funext hup.vR_zero)
      rwa [e] at h0
    rw [hnull]
    exact zero_le
  have hs₀o : s₀ ∈ oBuf mL mR R g := inBuffer_subset_oBuf hg (hBR s₀ hs₀)
  have hBfo : Bf ⊆ oBuf mL mR R g := fun p hp => inBuffer_subset_oBuf hg (hBR p hp)
  have hsm : ∀ᶠ m in atTop, (((0 : ℝ), xL m, xR m) : SState nL nR) ∈ oBuf mL mR R g :=
    (tendsto_const_nhds.prodMk_nhds (hxL.prodMk_nhds hxR)).eventually
      ((isOpen_oBuf mL mR R g).mem_nhds hs₀o)
  obtain ⟨D₀⟩ := exists_evolData hE₀ hw₀ (InBuffer.inCBuffer hs₀o)
  have hreach₀ : P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀) = D₀.law T (reachSet T O Bf ×ˢ Set.univ) :=
    D₀.measure_reachEvent_eq hε hg T hO hBo hBfo
  -- by contradiction, along a subsequence with reach probabilities below `c`
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between hcon
  have hfreq : ∃ᶠ m in atTop, (((0 : ℝ), xL m, xR m) : SState nL nR) ∈ oBuf mL mR R g ∧
      P m (reachEvent T O Bf (W m) (VL m) (VR m) (ζ m)) < c :=
    ((frequently_lt_of_liminf_lt (by isBoundedDefault) hc1).and_eventually hsm).mono
      fun m h => ⟨h.2, h.1⟩
  obtain ⟨ψ, hψmono, hψ⟩ := extraction_of_frequently_atTop hfreq
  have hDψ : ∀ k, Nonempty (EvolData κ mL mR Rw ε R g (xL (ψ k)) (xR (ψ k)) (ρL (ψ k)) (ρR (ψ k)) (P (ψ k))
      (W (ψ k)) (VL (ψ k)) (VR (ψ k)) (ζ (ψ k))) := fun k =>
    exists_evolData (hE (ψ k)) (hw (ψ k)) (InBuffer.inCBuffer (hψ k).1)
  let D : ∀ k, EvolData κ mL mR Rw ε R g (xL (ψ k)) (xR (ψ k)) (ρL (ψ k)) (ρR (ψ k)) (P (ψ k))
      (W (ψ k)) (VL (ψ k)) (VR (ψ k)) (ζ (ψ k)) := fun k => (hDψ k).some
  -- tightness and Prokhorov
  have htight := isTightMeasureSet_laws (Ω := fun k => Ω (ψ k)) hκ hnL hnR hε ha hg hRw T
    (fun k => hE (ψ k)) (fun k => hw (ψ k)) (fun k => hcr (ψ k)) D 0
  obtain ⟨π, φ, hφ, hlim⟩ := Prokhorov.exists_subseq_tendsto_of_isTightMeasureSet
    (fun k => (D k).lawP hε hg T) htight
  -- identification of the limit and of the law of the limiting evolution
  have hmono := hψmono.comp hφ
  have hlimP := ae_limitProps (Ω := fun k => Ω (ψ (φ k))) hκ hnL hnR hε ha hg hRw T
    (fun k => hE (ψ (φ k))) (fun k => hw (ψ (φ k))) (fun k => hcr (ψ (φ k))) (fun k => D (φ k))
    (hxL.comp hmono.tendsto_atTop) (hxR.comp hmono.tendsto_atTop) (hρL.comp hmono.tendsto_atTop)
    (hρR.comp hmono.tendsto_atTop) hlim
  have hlimP₀ := ae_limitProps (Ω := fun _ : ℕ => Ω₀) hκ hnL hnR hε ha hg hRw T
    (fun _ => hE₀) (fun _ => hw₀) (fun _ => hcr₀) (fun _ => D₀) tendsto_const_nhds tendsto_const_nhds
    tendsto_const_nhds tendsto_const_nhds (tendsto_const_nhds (x := D₀.lawP hε hg T))
  -- the Brownian marginals agree
  have hmargP : π.map Prod.snd = (D₀.lawP hε hg T).map Prod.snd := by
    refine Prokhorov.map_eq_of_tendsto_of_map_eq hlim continuous_snd (Eventually.of_forall fun k => ?_)
    apply Subtype.ext
    change ((D (φ k)).law T).map Prod.snd = (D₀.law T).map Prod.snd
    rw [(D (φ k)).law_snd hε hg T, D₀.law_snd hε hg T, (D (φ k)).map_bP_eq D₀ T]
  have hmarg : (π : Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))).map
      Prod.snd = (D₀.law T).map Prod.snd := by
    have := congrArg (fun μ : ProbabilityMeasure C(Set.Icc (0 : ℝ≥0) T, ℝ) =>
      (μ : Measure C(Set.Icc (0 : ℝ≥0) T, ℝ))) hmargP
    simpa only [ProbabilityMeasure.toMeasure_map, EvolData.coe_lawP] using this
  -- the conditionally independent gluing over the Brownian path
  have hprob₀ : IsProbabilityMeasure (D₀.law T) := D₀.isProbabilityMeasure_law hε hg T
  obtain ⟨γ, -, hγ1, hγ2⟩ := exists_glue
    (π : Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ))) (D₀.law T) hmarg
  -- pathwise uniqueness
  have hsep : ∀ i j, xL₀ i < xR₀ j := fun i j => by
    have h1 : xL₀ i ≤ xL₀ ⟨0, hnL⟩ := hw₀.1.1 (Fin.le_def.2 (Nat.zero_le _))
    have h2 : xR₀ ⟨0, hnR⟩ ≤ xR₀ j := hw₀.1.2.2.1 (Fin.le_def.2 (Nat.zero_le _))
    linarith
  have hm1 : Measurable fun z : C(Set.Icc (0 : ℝ≥0) T, ℝ) × C(Set.Icc (0 : ℝ≥0) T, SState nL nR) ×
      C(Set.Icc (0 : ℝ≥0) T, SState nL nR) => (z.2.1, z.1) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have hm2 : Measurable fun z : C(Set.Icc (0 : ℝ≥0) T, ℝ) × C(Set.Icc (0 : ℝ≥0) T, SState nL nR) ×
      C(Set.Icc (0 : ℝ≥0) T, SState nL nR) => (z.2.2, z.1) :=
    (measurable_snd.comp measurable_snd).prodMk measurable_fst
  have h1 : ∀ᵐ z ∂γ, LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ z.2.1 z.1 :=
    ae_of_ae_map hm1.aemeasurable (p := fun q => LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ q.1 q.2)
      (by rw [hγ1]; exact hlimP)
  have h2 : ∀ᵐ z ∂γ, LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ z.2.2 z.1 :=
    ae_of_ae_map hm2.aemeasurable (p := fun q => LimitProps κ mL mR R g T xL₀ xR₀ ρL₀ ρR₀ q.1 q.2)
      (by rw [hγ2]; exact hlimP₀)
  have hiff : ∀ᵐ z ∂γ, (z.2.1 ∈ reachSet T O Bf ↔ z.2.2 ∈ reachSet T O Bf) := by
    filter_upwards [h1, h2] with z hz1 hz2
    exact ⟨mem_reachSet_of_limitProps hε hg hw₀ hsep hz1 hz2 hBfo,
      mem_reachSet_of_limitProps hε hg hw₀ hsep hz2 hz1 hBfo⟩
  have heq := measure_prod_univ_eq_of_glue hγ1 hγ2 (isOpen_reachSet T hO hBo).measurableSet
    (isOpen_reachSet T hO hBo).measurableSet hiff
  -- Portmanteau for the open reach set
  have hport : (π : Measure (C(Set.Icc (0 : ℝ≥0) T, SState nL nR) × C(Set.Icc (0 : ℝ≥0) T, ℝ)))
      (reachSet T O Bf ×ˢ Set.univ) ≤ c := by
    refine measure_le_of_tendsto_of_isOpen hlim ((isOpen_reachSet T hO hBo).prod isOpen_univ)
      (Eventually.of_forall fun k => ?_)
    change (D (φ k)).law T (reachSet T O Bf ×ˢ Set.univ) ≤ c
    rw [← (D (φ k)).measure_reachEvent_eq hε hg T hO hBo hBfo]
    exact (hψ (φ k)).2.le
  rw [hreach₀] at hc2
  rw [heq] at hport
  exact absurd (hc2.trans_le hport) (lt_irrefl c)


end DSReach

end Supp12

end InteractingSLE
