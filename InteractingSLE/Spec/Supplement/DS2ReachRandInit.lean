/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofMain

/-!
# DS2 with converging random initial states, I: DS2 without the grouping hypotheses, and a Fatou lemma

Packet PROVE-T14-DS3. Step (iii) of the proof of Lemma DS3 (spec p. 554, `source/spec/p529-576.md` L601–L611): "Apply
DS1's occupation bounds uniformly over these localized random initial states, and repeat DS2's joint tightness and limit-
identification argument … This argument permits a nearest gap to be zero in some initial states and positive in nearby
ones". The landed proof of DS2 (`DSReach.ds2ReachStatement`, PROVE-T14-DS) never uses its grouping hypotheses
(`SameGrouping`, the `η`-separation of groups): it holds for every converging sequence of DS1 words with cross gap at
least `a`. Random initial states are then handled by a Fatou lemma for weakly converging laws, with DS2 as the pointwise
input (no rerun of the tightness argument):

* **`ds2Reach_general`**: DS2 in reach form for any DS1 words `x_m → x₀` with cross gap `≥ a` (the proof of
  `ds2ReachStatement`, verbatim, without the unused hypotheses);
* **`lintegral_le_liminf_of_tendsto`** (Fatou lemma for weakly converging laws): if `ν_m → ν` weakly, all carried by a
  closed set `F`, and the measurable `K_m, K` satisfy `K x ≤ liminf_k K_{m_k}(y_k)` whenever `m_k → ∞` and
  `F ∋ y_k → x ∈ F`, then `∫ K dν ≤ liminf ∫ K_m dν_m`. Proof: layer cake, and for each level `t` the open sets
  `G_k = ⋃ {ball(p, 1/(2(k+1))) : every K_m, m ≥ k, exceeds t on F ∩ ball(p, 1/(k+1))}` with Portmanteau.
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

/-- **DS2 in reach form without the grouping hypotheses**: for DS1 words `x_m → x₀` with cross gap `≥ a` (and any
initial coincidence patterns). The proof is that of `ds2ReachStatement`, which does not use `SameGrouping` or the
`η`-separation of groups. -/
theorem ds2Reach_general (κ : ℝ) (hκ : 0 < κ) {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) (mL mR : ℕ)
    (Rw ε a g : ℝ) (hε : 0 < ε) (ha : 0 < a) (hg : 0 < g)
    (xL : ℕ → Fin nL → ℝ) (xR : ℕ → Fin nR → ℝ) (ρL : ℕ → Fin nL → ℝ) (ρR : ℕ → Fin nR → ℝ)
    (xL₀ : Fin nL → ℝ) (xR₀ : Fin nR → ℝ) (ρL₀ : Fin nL → ℝ) (ρR₀ : Fin nR → ℝ)
    (hw : ∀ m, IsDS1Word mL mR Rw ε (xL m) (xR m) (ρL m) (ρR m)) (hw₀ : IsDS1Word mL mR Rw ε xL₀ xR₀ ρL₀ ρR₀)
    (hcr : ∀ m, a ≤ xR m ⟨0, hnR⟩ - xL m ⟨0, hnL⟩) (hcr₀ : a ≤ xR₀ ⟨0, hnR⟩ - xL₀ ⟨0, hnL⟩)
    (hxL : Tendsto xL atTop (𝓝 xL₀)) (hxR : Tendsto xR atTop (𝓝 xR₀)) (hρL : Tendsto ρL atTop (𝓝 ρL₀))
    (hρR : Tendsto ρR atTop (𝓝 ρR₀))
    (Ω : ℕ → Type u) [mΩ : ∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m))
    (𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)) (W : ∀ m, ℝ≥0 → Ω m → ℝ) (VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ)
    (VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ) (B : ∀ m, ℝ≥0 → Ω m → ℝ) (ζ : ∀ m, Ω m → ℝ≥0∞)
    (hE : ∀ m, IsIntegratedSLEEvolution κ (xL m) (xR m) (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m)
      (ζ m))
    {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀)
    (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
    (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞)
    (hE₀ : IsIntegratedSLEEvolution κ xL₀ xR₀ ρL₀ ρR₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀)
    (T : ℝ≥0) (R : ℝ) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (hO : IsOpen O) (hBo : IsOpen Bf)
    (hBR : ∀ p ∈ Bf, InBuffer mL mR R g p) :
    P₀ (reachEvent T O Bf W₀ VL₀ VR₀ ζ₀) ≤
      liminf (fun m => P m (reachEvent T O Bf (W m) (VL m) (VR m) (ζ m))) atTop := by
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

/-! ### A Fatou lemma for weakly converging laws -/

section Fatou

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- One level of the Fatou lemma: `ν{t < K} ≤ liminf ν_m{t < K_m}`. -/
theorem measure_lt_le_liminf_of_tendsto {ν : ℕ → ProbabilityMeasure X} {ν₀ : ProbabilityMeasure X}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {F : Set X} (hFν : ∀ m, (ν m : Measure X) Fᶜ = 0)
    (hFν₀ : (ν₀ : Measure X) Fᶜ = 0) {K : ℕ → X → ℝ} {K₀ : X → ℝ}
    (hlsc : ∀ x ∈ F, ∀ (mk : ℕ → ℕ) (y : ℕ → X), Tendsto mk atTop atTop → (∀ k, y k ∈ F) →
      Tendsto y atTop (𝓝 x) → ENNReal.ofReal (K₀ x) ≤ liminf (fun k => ENNReal.ofReal (K (mk k) (y k))) atTop)
    {t : ℝ} (ht : 0 ≤ t) :
    (ν₀ : Measure X) {x | t < K₀ x} ≤ liminf (fun m => (ν m : Measure X) {x | t < K m x}) atTop := by
  classical
  set A : ℕ → Set X := fun k => {p | p ∈ F ∧ ∀ m ≥ k, ∀ q ∈ F, dist q p < 1 / ((k : ℝ) + 1) → t < K m q}
    with hA
  set G : ℕ → Set X := fun k => ⋃ p ∈ A k, Metric.ball p (1 / (2 * ((k : ℝ) + 1))) with hG
  set H : ℕ → Set X := fun k => ⋃ j ∈ Finset.range (k + 1), G j with hH
  have hGo : ∀ k, IsOpen (G k) := fun k => isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hHo : ∀ k, IsOpen (H k) := fun k => isOpen_biUnion fun j _ => hGo j
  have hHmono : Monotone H := fun k l hkl => biUnion_subset_biUnion_left fun j hj => by
    simp only [Finset.coe_range, Set.mem_Iio] at hj ⊢; omega
  -- (a) on `F`, `H k` is inside every superlevel set of `K m`, `m ≥ k`
  have ha : ∀ k m, k ≤ m → H k ∩ F ⊆ {q | t < K m q} := by
    rintro k m hkm q ⟨hq, hqF⟩
    simp only [hH, mem_iUnion, Finset.mem_range] at hq
    obtain ⟨j, hj, hqG⟩ := hq
    simp only [hG, mem_iUnion, Metric.mem_ball] at hqG
    obtain ⟨p, hpA, hqp⟩ := hqG
    refine hpA.2 m (by omega) q hqF (lt_of_lt_of_le hqp ?_)
    have : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ (by positivity) this]; linarith
  -- (b) the superlevel set of `K₀` on `F` is covered
  have hb : {x | t < K₀ x} ∩ F ⊆ ⋃ k, H k := by
    rintro x ⟨hx, hxF⟩
    by_contra hcon
    have hnot : ∀ k, x ∉ A k := fun k hk => hcon (mem_iUnion.2 ⟨k, by
      simp only [hH, mem_iUnion, Finset.mem_range]
      exact ⟨k, Nat.lt_succ_self k, mem_iUnion₂.2 ⟨x, hk, Metric.mem_ball_self (by positivity)⟩⟩⟩)
    have hex : ∀ k : ℕ, ∃ m : ℕ, k ≤ m ∧ ∃ q ∈ F, dist q x < 1 / ((k : ℝ) + 1) ∧ K m q ≤ t := fun k => by
      have := hnot k
      simp only [hA, mem_ofPred_eq, not_and, not_forall, not_lt, exists_prop] at this
      obtain ⟨m, hm, q, hqF, hq, hKq⟩ := this hxF
      exact ⟨m, hm, q, hqF, hq, hKq⟩
    choose mk hmk y hyF hy hKy using hex
    have hmk' : Tendsto mk atTop atTop := tendsto_atTop_mono hmk tendsto_id
    have hy' : Tendsto y atTop (𝓝 x) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k => dist_nonneg) (fun k => (hy k).le) ?_)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := hlsc x hxF mk y hmk' hyF hy'
    have h2 : liminf (fun k => ENNReal.ofReal (K (mk k) (y k))) atTop ≤ ENNReal.ofReal t :=
      liminf_le_of_le (by isBoundedDefault) fun b hb => by
        obtain ⟨k, hk⟩ := hb.exists
        exact hk.trans (ENNReal.ofReal_le_ofReal (hKy k))
    have h3 : ENNReal.ofReal t < ENNReal.ofReal (K₀ x) :=
      (ENNReal.ofReal_lt_ofReal_iff (ht.trans_lt hx)).2 hx
    exact absurd (h1.trans h2) (not_le.2 h3)
  -- conclusion
  calc (ν₀ : Measure X) {x | t < K₀ x} ≤ (ν₀ : Measure X) ({x | t < K₀ x} ∩ F) := by
        calc (ν₀ : Measure X) {x | t < K₀ x}
            ≤ (ν₀ : Measure X) ({x | t < K₀ x} ∩ F) + (ν₀ : Measure X) Fᶜ := by
              refine (measure_mono ?_).trans (measure_union_le _ _)
              intro x hx
              by_cases hxF : x ∈ F
              · exact Or.inl ⟨hx, hxF⟩
              · exact Or.inr hxF
          _ = _ := by rw [hFν₀, add_zero]
    _ ≤ (ν₀ : Measure X) (⋃ k, H k) := measure_mono hb
    _ = ⨆ k, (ν₀ : Measure X) (H k) := hHmono.measure_iUnion
    _ ≤ _ := by
        refine iSup_le fun k => ?_
        refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν (hHo k)).trans ?_
        refine liminf_le_liminf (eventually_atTop.2 ⟨k, fun m hm => ?_⟩) (by isBoundedDefault)
          (by isBoundedDefault)
        calc (ν m : Measure X) (H k) ≤ (ν m : Measure X) (H k ∩ F) + (ν m : Measure X) Fᶜ := by
              refine (measure_mono ?_).trans (measure_union_le _ _)
              intro x hx
              by_cases hxF : x ∈ F
              · exact Or.inl ⟨hx, hxF⟩
              · exact Or.inr hxF
          _ = (ν m : Measure X) (H k ∩ F) := by rw [hFν m, add_zero]
          _ ≤ _ := measure_mono (ha k m hm)

/-- **Fatou lemma for weakly converging laws.** If `ν_m → ν₀` weakly, all laws are carried by `F`, and the nonnegative
measurable `K_m`, `K₀` satisfy `K₀ x ≤ liminf_k K_{m_k}(y_k)` whenever `m_k → ∞` and `F ∋ y_k → x ∈ F`, then
`∫ K₀ dν₀ ≤ liminf_m ∫ K_m dν_m`. -/
theorem lintegral_le_liminf_of_tendsto {ν : ℕ → ProbabilityMeasure X} {ν₀ : ProbabilityMeasure X}
    (hν : Tendsto ν atTop (𝓝 ν₀)) {F : Set X} (hFν : ∀ m, (ν m : Measure X) Fᶜ = 0)
    (hFν₀ : (ν₀ : Measure X) Fᶜ = 0) {K : ℕ → X → ℝ} {K₀ : X → ℝ} (hKm : ∀ m, Measurable (K m))
    (hK0 : ∀ m x, 0 ≤ K m x) (hK₀m : Measurable K₀) (hK₀0 : ∀ x, 0 ≤ K₀ x)
    (hlsc : ∀ x ∈ F, ∀ (mk : ℕ → ℕ) (y : ℕ → X), Tendsto mk atTop atTop → (∀ k, y k ∈ F) →
      Tendsto y atTop (𝓝 x) → ENNReal.ofReal (K₀ x) ≤ liminf (fun k => ENNReal.ofReal (K (mk k) (y k))) atTop) :
    ∫⁻ x, ENNReal.ofReal (K₀ x) ∂(ν₀ : Measure X) ≤
      liminf (fun m => ∫⁻ x, ENNReal.ofReal (K m x) ∂(ν m : Measure X)) atTop := by
  rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hK₀0) hK₀m.aemeasurable]
  simp_rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall (hK0 _)) (hKm _).aemeasurable]
  calc ∫⁻ t in Ioi 0, (ν₀ : Measure X) {x | t < K₀ x}
      ≤ ∫⁻ t in Ioi 0, liminf (fun m => (ν m : Measure X) {x | t < K m x}) atTop := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        exact measure_lt_le_liminf_of_tendsto hν hFν hFν₀ hlsc (le_of_lt ht)
    _ ≤ _ := lintegral_liminf_le fun m => Antitone.measurable fun s t hst =>
        measure_mono fun x hx => lt_of_le_of_lt hst hx

end Fatou

end DSReach

end Supp12

end InteractingSLE
