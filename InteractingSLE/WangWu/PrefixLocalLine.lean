/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.PrefixLocalMean
import InteractingSLE.WangWu.Prop418Side

/-!
# The complete seed line of a full level-line coupling is a local set

Packet PROVE-WW-B8. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of
Proposition 4.19 (text dump L1660–1662): "The complete curve `β` is local by the terminal Gaussian-kernel limit."

For a full level-line coupling with infinite lifetime whose trace is a simple proper arc `γ`, the complete line
`γ((0, ∞)) = arcRange γ ∩ ℍ = ⋃ₙ K_n` is a local set of the centred field. The proof uses the avoidance criterion
(`isAvoidanceLocal_of_setIntegral_avoid`) for the σ-algebra `𝓕_∞ = ⨆ₙ 𝓕_n` of the whole driving history:

* on `𝓕_n`-events inside `{K_n ∩ V = ∅}` the Dirichlet-direction identity holds by the kernel at time `n`
  (`IsFullLevelLineCoupling.setIntegral_cexp_lapTest_add`);
* intersecting with the decreasing avoidance events `Gₙ ↓ G = {γ ∩ V = ∅}` and letting `n → ∞` gives the identity on
  `D ∩ G` for every `D ∈ ⋃ₙ 𝓕_n`; the class of such `D` is a Dynkin system, so it contains `𝓕_∞`
  (`setIntegral_inter_eq_mul_of_iSup`, π-λ).

No terminal kernel limit is needed. (The range itself, which contains the real point `γ 0 = 0`, is never a local set:
`not_isLocalSet_arcRange`.)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace QuantumZipper Metric
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE.WangWu

open LQGMetric LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm

/-! ### A π-λ extension of set-integral identities -/

section PiLambda

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **π-λ extension.** If `∫_{D ∩ G} X = c ∫_{D ∩ G} Y` for every `D` of each σ-algebra of a monotone sequence
`m n ≤ mΩ`, then it holds for every `D` of `⨆ n, m n`. -/
theorem setIntegral_inter_eq_mul_of_iSup {m : ℕ → MeasurableSpace Ω} (hm : ∀ n, m n ≤ mΩ)
    (hmono : Monotone m) {G : Set Ω} (hG : MeasurableSet G) {X Y : Ω → ℂ} (hX : Integrable X P)
    (hY : Integrable Y P) (c : ℂ)
    (hbasic : ∀ n D, MeasurableSet[m n] D → ∫ ω in D ∩ G, X ω ∂P = c * ∫ ω in D ∩ G, Y ω ∂P)
    (D : Set Ω) (hD : MeasurableSet[⨆ n, m n] D) :
    ∫ ω in D ∩ G, X ω ∂P = c * ∫ ω in D ∩ G, Y ω ∂P := by
  have hle : (⨆ n, m n) ≤ mΩ := iSup_le hm
  refine MeasurableSpace.induction_on_inter (m := ⨆ n, m n)
    (C := fun D _ => ∫ ω in D ∩ G, X ω ∂P = c * ∫ ω in D ∩ G, Y ω ∂P)
    (s := ⋃ n, {s | MeasurableSet[m n] s}) (MeasurableSpace.generateFrom_iUnion_measurableSet m).symm
    (isPiSystem_iUnion_of_monotone _ (fun n => @MeasurableSpace.isPiSystem_measurableSet Ω (m n))
      fun i j hij s hs => hmono hij s hs) ?_ ?_ ?_ ?_ D hD
  · simp
  · intro t ht
    obtain ⟨n, hn⟩ := mem_iUnion.1 ht
    exact hbasic n t hn
  · intro t htm ht
    have htm' : MeasurableSet t := hle t htm
    have huniv := hbasic 0 univ MeasurableSet.univ
    rw [univ_inter] at huniv
    have hsplit : ∀ Z : Ω → ℂ, Integrable Z P →
        ∫ ω in tᶜ ∩ G, Z ω ∂P = (∫ ω in G, Z ω ∂P) - ∫ ω in t ∩ G, Z ω ∂P := fun Z hZ => by
      have hdisj : Disjoint (t ∩ G) (tᶜ ∩ G) :=
        Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1.1
      have hU : (t ∩ G) ∪ (tᶜ ∩ G) = G := by
        rw [← union_inter_distrib_right, union_compl_self, univ_inter]
      have e := setIntegral_union hdisj (htm'.compl.inter hG) hZ.integrableOn hZ.integrableOn
      rw [hU] at e
      rw [e]
      ring
    rw [hsplit X hX, hsplit Y hY, huniv, ht]
    ring
  · intro f hdisj hfm hf
    have hfm' : ∀ i, MeasurableSet (f i ∩ G) := fun i => (hle _ (hfm i)).inter hG
    have hd : Pairwise (Function.onFun Disjoint fun i => f i ∩ G) := fun i j hij =>
      (hdisj hij).mono inter_subset_left inter_subset_left
    have e : (⋃ i, f i) ∩ G = ⋃ i, f i ∩ G := iUnion_inter G f
    rw [e, integral_iUnion hfm' hd hX.integrableOn, integral_iUnion hfm' hd hY.integrableOn,
      ← tsum_mul_left]
    exact tsum_congr hf

end PiLambda

/-! ### The complete line -/

section Line

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {F : Ω → DistOn upperHalfPlaneOpens}

omit mΩ in
/-- A countable union of hitting-measurable random sets is hitting-measurable. -/
theorem measurable_iUnion_hitting [mΩ : MeasurableSpace Ω] {A : ℕ → Ω → Set ℂ}
    (hA : ∀ n, Measurable[mΩ, hittingSigma] (A n)) :
    Measurable[mΩ, hittingSigma] fun ω => ⋃ n, A n ω := by
  unfold hittingSigma
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : (fun ω => ⋃ n, A n ω) ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      ⋃ n, A n ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, iUnion_inter, nonempty_iUnion, mem_iUnion]
  rw [e]
  exact MeasurableSet.iUnion fun n => hA n (measurableSet_hitting hU hUH)

/-- The positive-time part of a proper arc is the union of its prefixes `γ((0, n])`. -/
theorem IsProperArc.iUnion_image_Ioc {γ : ℝ → ℂ} (hγ : IsProperArc γ) :
    ⋃ n : ℕ, γ '' Ioc 0 (n : ℝ) = arcRange γ ∩ H := by
  ext z
  simp only [mem_iUnion, mem_image, mem_inter_iff, arcRange]
  constructor
  · rintro ⟨n, s, hs, rfl⟩
    exact ⟨⟨s, mem_Ici.2 hs.1.le, rfl⟩, hγ.mem_H s hs.1⟩
  · rintro ⟨⟨s, hs, rfl⟩, hsH⟩
    have hs0 : 0 < s := by
      rcases (mem_Ici.1 hs).lt_or_eq with h | h
      · exact h
      · rw [← h, hγ.zero] at hsH
        simp [H] at hsH
    obtain ⟨n, hn⟩ := exists_nat_gt s
    exact ⟨n, s, ⟨hs0, hn.le⟩, rfl⟩

/-- **The complete seed line is a local set** (proof of Wang–Wu Proposition 4.19, "The complete curve `β` is local").
For a full level-line coupling with an admissible seed and infinite lifetime, whose driver almost surely has a
continuous generating trace (`htr`) and whose Loewner trace `γ` is almost surely a simple proper arc, the complete line
`γ((0, ∞)) = arcRange γ ∩ ℍ` is a local set of the centred field `F − u₀`. -/
theorem IsFullLevelLineCoupling.isLocalSet_line [IsProbabilityMeasure P]
    (hF : IsFullLevelLineCoupling xL xR ρL ρR P 𝓕 W VL VR B ζ F)
    (htr : ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ᵐ ω ∂P, IsLoewnerTrace (Ito.rpath (W · ω)) (γ ω) ∧ IsProperArc (γ ω))
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR xL xR) (forceJumpSet xL xR) u₀) :
    IsLocalSet (fun ω => arcRange (γ ω) ∩ H) (WholeField.centredField F u₀) P := by
  classical
  have hE := hF.1
  obtain ⟨hX, -⟩ := hF.2.2
  have hh0 := hF.isZeroBoundaryGFF_centredField htr hseed hu₀
  set h0 := WholeField.centredField F u₀ with hh0def
  have hh0m := hh0.measurable
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  -- the deterministic times `n`
  set τ : ℕ → Ω → WithTop ℝ≥0 := fun n _ => ((n : ℝ≥0) : WithTop ℝ≥0) with hτdef
  have hτ : ∀ n, IsStoppingTime (drivingFiltration P hX) (τ n) := fun n => isStoppingTime_const _ _
  have hτζ : ∀ n, ∀ᵐ ω ∂P, (τ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hζ] with ω hω
    rw [hω]
    exact WithTop.coe_lt_top _
  have hτn : ∀ n (ω : Ω), (τ n ω).untopD 0 = (n : ℝ≥0) := fun n ω => WithTop.untopD_coe _ _
  choose A hAm hAK hAev using fun n => Coupling.exists_hittingVersion_hull hX hpath (hτ n) (hτζ n)
  set 𝓜 : ℕ → MeasurableSpace Ω := fun n => (hτ n).measurableSpace with h𝓜
  have h𝓜le : ∀ n, 𝓜 n ≤ mΩ := fun n => (hτ n).measurableSpace_le
  have h𝓜mono : Monotone 𝓜 := fun i j hij =>
    (hτ i).measurableSpace_mono (hτ j) fun ω => WithTop.coe_le_coe.2 (by exact_mod_cast hij)
  have h𝒢le : (⨆ n, 𝓜 n) ≤ mΩ := iSup_le h𝓜le
  set Aun : Ω → Set ℂ := fun ω => ⋃ n, A n ω with hAUdef
  have hAUm : Measurable[mΩ, hittingSigma] Aun := measurable_iUnion_hitting hAm
  -- the union of the hulls is the complete line
  have hAUK : ∀ᵐ ω ∂P, Aun ω = arcRange (γ ω) ∩ H := by
    filter_upwards [ae_all_iff.2 hAK, hγ] with ω hAω hγω
    simp only [hAUdef]
    rw [← hγω.2.iUnion_image_Ioc]
    refine iUnion_congr fun n => ?_
    rw [hAω n, hτn n ω]
    exact fwdHull_eq_image_Ioc hγω.1 hγω.2 (Nat.cast_nonneg n)
  -- the avoidance events of the union
  have hev : ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∃ E' : ℕ → Set Ω, (∀ n, MeasurableSet[𝓜 n] (E' n)) ∧
      Antitone E' ∧ ∀ n, ∀ᵐ ω ∂P, ω ∈ E' n ↔ ∀ k ≤ n, Disjoint (A k ω) V := by
    intro V hV hVH
    choose E hEm hEae using fun n => hAev n V hV hVH
    refine ⟨fun n => ⋂ (k : ℕ) (_ : k ≤ n), E k, fun n => ?_, fun i j hij => ?_, fun n => ?_⟩
    · refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk => ?_
      exact h𝓜mono hk _ (hEm k)
    · exact biInter_subset_biInter_left fun k hk => le_trans hk hij
    · have hall : ∀ᵐ ω ∂P, ∀ k, (Disjoint (A k ω) V ↔ ω ∈ E k) :=
        ae_all_iff.2 fun k => (hEae k).mono fun ω h => eq_iff_iff.1 h
      filter_upwards [hall] with ω hω
      simp only [mem_iInter]
      exact forall₂_congr fun k _ => (hω k).symm
  have hAevU : ∀ V : Set ℂ, IsOpen V → V ⊆ H → ∃ E' : Set Ω, MeasurableSet[⨆ n, 𝓜 n] E' ∧
      {ω | Disjoint (Aun ω) V} =ᵐ[P] E' := by
    intro V hV hVH
    obtain ⟨E', hE'm, -, hE'ae⟩ := hev V hV hVH
    refine ⟨⋂ n, E' n, MeasurableSet.iInter fun n => le_iSup 𝓜 n _ (hE'm n), ?_⟩
    filter_upwards [ae_all_iff.2 hE'ae] with ω hω
    show Disjoint (Aun ω) V = (ω ∈ ⋂ n, E' n)
    refine propext ⟨fun h => mem_iInter.2 fun n => (hω n).2 fun k _ => ?_, fun h => ?_⟩
    · exact h.mono_left (subset_iUnion (fun k => A k ω) k)
    · rw [disjoint_iUnion_left]
      exact fun k => (hω k).1 (mem_iInter.1 h k) k le_rfl
  have hAc : ∀ᵐ ω ∂P, Aun ω ⊆ H ∧ IsOpen (H \ Aun ω) := by
    filter_upwards [hAUK, hγ] with ω hω hγω
    rw [hω]
    refine ⟨inter_subset_right, ?_⟩
    have e : H \ (arcRange (γ ω) ∩ H) = H \ arcRange (γ ω) := by
      ext z; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [e]
    exact isOpen_H.sdiff hγω.2.isClosed_arcRange
  -- the Dirichlet-direction identity on the avoidance events of the union
  have hav : IsAvoidanceLocal Aun h0 P := by
    refine isAvoidanceLocal_of_setIntegral_avoid h𝒢le hh0 hAUm hAevU fun V hVH f Ξ D hD hDA => ?_
    obtain ⟨E', hE'm, hE'anti, hE'ae⟩ := hev V V.isOpen hVH
    set X : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h0 ω (lapTest V f + Ξ) : ℂ)) with hXdef
    set Y : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h0 ω Ξ : ℂ)) with hYdef
    set c : ℂ := Complex.exp (((-(1 / 2) * ‖gradFeat (V : Set ℂ) f.1‖ ^ 2 -
      ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ξ⟫ : ℝ) : ℂ)) with hc
    have hXi : Integrable X P :=
      Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hh0m)).aestronglyMeasurable
        1 (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
    have hYi : Integrable Y P :=
      Integrable.of_bound (GFF.measurable_exp_I_mul ((measurable_distOn_apply _).comp hh0m)).aestronglyMeasurable
        1 (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
    set G : Set Ω := ⋂ n, E' n with hGdef
    have hGm : MeasurableSet G := MeasurableSet.iInter fun n => h𝓜le n _ (hE'm n)
    -- the identity at each time `n` on `𝓜 n`-events inside `E' n`
    have hstep : ∀ n D', MeasurableSet[𝓜 n] D' →
        ∫ ω in D' ∩ E' n, X ω ∂P = c * ∫ ω in D' ∩ E' n, Y ω ∂P := by
      intro n D' hD'
      refine hF.setIntegral_cexp_lapTest_add htr hu₀.1 hX (hτ n) (hτζ n) hVH f Ξ (hD'.inter (hE'm n)) ?_
      filter_upwards [hE'ae n, hAK n] with ω h1 h2 hω
      rw [← h2]
      exact (h1.1 hω.2) n le_rfl
    -- the basic events
    have hbasic : ∀ m D', MeasurableSet[𝓜 m] D' →
        ∫ ω in D' ∩ G, X ω ∂P = c * ∫ ω in D' ∩ G, Y ω ∂P := by
      intro m D' hD'
      have hs : ∀ n, MeasurableSet (D' ∩ E' n) := fun n => (h𝓜le m _ hD').inter (h𝓜le n _ (hE'm n))
      have hanti : Antitone fun n => D' ∩ E' n := fun i j hij => inter_subset_inter_right _ (hE'anti hij)
      have hI : ⋂ n, D' ∩ E' n = D' ∩ G := by rw [← inter_iInter]
      have l1 := tendsto_setIntegral_of_antitone hs hanti ⟨0, hXi.integrableOn⟩
      have l2 := tendsto_setIntegral_of_antitone hs hanti ⟨0, hYi.integrableOn⟩
      rw [hI] at l1 l2
      have l3 := l2.const_mul c
      refine tendsto_nhds_unique_of_eventuallyEq l1 l3 ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      exact hstep n D' (h𝓜mono hn _ hD')
    have hall := setIntegral_inter_eq_mul_of_iSup h𝓜le h𝓜mono hGm hXi hYi c hbasic D hD
    have hDG : D ∩ G =ᵐ[P] D := by
      filter_upwards [ae_all_iff.2 hE'ae, hDA] with ω hω hωD
      show (ω ∈ D ∩ G) = (ω ∈ D)
      refine propext ⟨fun h => h.1, fun h => ⟨h, mem_iInter.2 fun n => (hω n).2 fun k _ => ?_⟩⟩
      exact (hωD h).mono_left (subset_iUnion (fun k => A k ω) k)
    rw [setIntegral_congr_set hDG, setIntegral_congr_set hDG] at hall
    exact hall
  have hloc := ((isLocalSet_tfae hh0 hAUm hAc).out 1 4).1 hav
  exact Coupling.IsLocalSet.congr_set hloc (hAUK.mono fun ω h => h.symm)

end Line

end InteractingSLE.WangWu
