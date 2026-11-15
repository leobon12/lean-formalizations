/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.Param12BorelTest
import InteractingSLE.Spec.Coupling.Assembly11BProvider

/-!
# Coupling constraints at stops from constraints at deterministic dyadic times (S4, first half)

Packet PROVE-PARAM12C (step S4 of `planning/handoffs/PROVE-PARAM12B.md` §5). Theorem 1.1's compactness step needs
a coupling that is sampled (`IsSampledCoupling`) and projection-independent (`IsProjIndepCoupling`) at a countable
family of stops of the usual augmentation. These stops are chosen per evolution. A Borel description of coupling laws
cannot refer to them. Instead it constrains the coupling at the deterministic dyadic times `q` on the events where a
compact `K` is still alive at `q` (`aliveEv`). This file shows that these constraints imply the constraints at every
stop `s` with `s < ζ` and `K ∩ K_s = ∅`:

* `exists_ae_eq_inter_lt`: for an event `A₀` of the stopped σ-algebra of the usual augmentation, `A₀ ∩ {s < q}` is
  almost surely an event of the raw filtration at time `q`;
* `setIntegral_eq_of_dyadic` (**the time approximation**): an identity `∫_{A × X} Φ dμ = ∫_A g_q dP₀` on the raw events
  at the dyadic times, with `g_{s_m} → G` along the dyadic times `s_m ↓ s` from above, gives `∫_{A₀ × X} Φ dμ =
  ∫_{A₀} G dP₀` for `A₀` in the stopped σ-algebra at `s`;
* `eventually_alive_of_disjoint` (deterministic): a compact set disjoint from `K_s`, `s < ζ`, stays alive on a right
  neighbourhood of `s` (lower semicontinuity of the swallowing time);
* `isSampledCoupling_of_dyadic`, `isProjIndepCoupling_of_dyadic`: the two constraints at a stop.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Coupling Ito

/-! ### Stopped events cut at a time -/

section Stopped

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}

/-- For an event `A₀` of the stopped σ-algebra of the usual augmentation at a finite stop `s`, `A₀ ∩ {s < q}` is
almost surely an event of the raw filtration at `q`. -/
theorem exists_ae_eq_inter_lt {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0)) {A₀ : Set Ω₀}
    (hA₀ : MeasurableSet[hs.measurableSpace] A₀) (q : ℝ≥0) :
    ∃ A', MeasurableSet[𝓕₀ q] A' ∧ A' =ᵐ[P₀] A₀ ∩ {ω | s ω < q} := by
  rcases eq_or_ne q 0 with rfl | hq
  · refine ⟨∅, @MeasurableSet.empty _ (𝓕₀ 0), ?_⟩
    have : A₀ ∩ {ω | s ω < 0} = ∅ := by ext ω; simp
    rw [this]
  have hq' : 0 < q := pos_iff_ne_zero.2 hq
  set r : ℕ → ℝ≥0 := fun j => q - q / (j + 2) with hr
  have hrq : ∀ j, r j < q := fun j => tsub_lt_self hq' (div_pos hq' (by positivity))
  have hpiece : ∀ j, ∃ A', MeasurableSet[𝓕₀ q] A' ∧
      A' =ᵐ[P₀] A₀ ∩ {ω | (s ω : WithTop ℝ≥0) ≤ (r j : WithTop ℝ≥0)} := fun j => by
    have h1 := ((hs.measurableSet A₀).1 hA₀).2 (r j)
    obtain ⟨A', hA', hae⟩ := exists_ae_eq_of_measurableSet_usualAugmentation (hrq j) h1
    exact ⟨A', hA', hae.symm⟩
  choose A' hA' hae using hpiece
  refine ⟨⋃ j, A' j, MeasurableSet.iUnion hA', ?_⟩
  have e : A₀ ∩ {ω | s ω < q} = ⋃ j, A₀ ∩ {ω | (s ω : WithTop ℝ≥0) ≤ (r j : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, WithTop.coe_le_coe]
    constructor
    · rintro ⟨h1, h2⟩
      have hpos : 0 < q - s ω := tsub_pos_of_lt h2
      obtain ⟨j, hj⟩ : ∃ j : ℕ, q / (j + 2) < q - s ω := by
        obtain ⟨j, hj⟩ := exists_nat_gt (q / (q - s ω))
        refine ⟨j, (div_lt_iff₀ (by positivity)).2 ?_⟩
        rw [div_lt_iff₀ hpos] at hj
        calc q < j * (q - s ω) := hj
          _ ≤ (j + 2) * (q - s ω) := by gcongr; norm_num
          _ = (q - s ω) * (j + 2) := mul_comm _ _
      refine ⟨j, h1, ?_⟩
      rw [hr]
      exact le_tsub_of_add_le_left (by
        calc q / (j + 2) + s ω ≤ (q - s ω) + s ω := add_le_add_left hj.le _
          _ = q := tsub_add_cancel_of_le h2.le)
    · rintro ⟨j, h1, h2⟩
      exact ⟨h1, lt_of_le_of_lt h2 (hrq j)⟩
  rw [e]
  exact EventuallyEqSet.countable_iUnion hae

end Stopped

/-! ### The time approximation -/

section Approx

variable {Ω₀ X : Type*} {mΩ₀ : MeasurableSpace Ω₀} [MeasurableSpace X] {P₀ : Measure Ω₀}
  {𝓕₀ : Filtration ℝ≥0 mΩ₀}

theorem measurable_of_isStoppingTime {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0)) : Measurable s := by
  refine measurable_of_Iic fun t => ?_
  have h := (usualAugmentation 𝓕₀ P₀).le t _ (hs t)
  convert h using 1
  ext ω
  simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
  rw [WithTop.coe_le_coe]

theorem flr_add_one_eq_iff {m k : ℕ} {t : ℝ≥0} (hk : 1 ≤ k) :
    flr m t + 1 = k ↔ dyad m (k - 1) ≤ t ∧ t < dyad m k := by
  have h2 : (0 : ℝ≥0) < 2 ^ m := by positivity
  have e0 : flr m t + 1 = k ↔ flr m t = k - 1 := by omega
  have e1 : dyad m (k - 1) ≤ t ↔ ((k - 1 : ℕ) : ℝ≥0) ≤ t * 2 ^ m := by
    unfold dyad; rw [div_le_iff₀ h2]
  have e2 : t < dyad m k ↔ t * 2 ^ m < ((k - 1 : ℕ) : ℝ≥0) + 1 := by
    unfold dyad
    rw [lt_div_iff₀ h2]
    have : ((k - 1 : ℕ) : ℝ≥0) + 1 = (k : ℝ≥0) := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hk]
    rw [this]
  rw [e0, e1, e2]
  unfold flr
  exact Nat.floor_eq_iff zero_le

/-- The pieces of the dyadic approximation from above: `A₀ ∩ {s_m = dyad m k}` is almost surely a raw event at
`dyad m k`. -/
theorem exists_ae_eq_inter_flr {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0)) {A₀ : Set Ω₀}
    (hA₀ : MeasurableSet[hs.measurableSpace] A₀) (m k : ℕ) :
    ∃ A', MeasurableSet[𝓕₀ (dyad m k)] A' ∧ A' =ᵐ[P₀] A₀ ∩ {ω | flr m (s ω) + 1 = k} := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨∅, @MeasurableSet.empty _ (𝓕₀ _), ?_⟩
    have : A₀ ∩ {ω | flr m (s ω) + 1 = 0} = ∅ := by ext ω; simp
    rw [this]
  obtain ⟨A1, hA1, h1⟩ := exists_ae_eq_inter_lt hs hA₀ (dyad m k)
  obtain ⟨A2, hA2, h2⟩ := exists_ae_eq_inter_lt hs (@MeasurableSet.univ _ hs.measurableSpace) (dyad m (k - 1))
  have hle : dyad m (k - 1) ≤ dyad m k := by unfold dyad; gcongr; omega
  refine ⟨A1 ∩ A2ᶜ, (hA1.inter (𝓕₀.mono hle _ hA2).compl), ?_⟩
  have e : A₀ ∩ {ω | flr m (s ω) + 1 = k} = (A₀ ∩ {ω | s ω < dyad m k}) ∩ (univ ∩ {ω | s ω < dyad m (k - 1)})ᶜ := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_univ, true_and, not_lt,
      flr_add_one_eq_iff hk]
    tauto
  rw [e]
  exact h1.inter h2.compl

variable [IsFiniteMeasure P₀]

/-- **The time approximation.** Let `μ` be a finite measure on `Ω₀ × X` with first marginal `P₀`. Suppose that at
every dyadic time `q`, for every raw event `A` of `𝓕₀ q`, `∫_{(A ∩ E q) × X} Φ dμ = ∫_{A ∩ E q} g_q dP₀`. If, almost
surely, along the dyadic times `s_m ↓ s` above a stop `s` of the usual augmentation one is eventually in `E (s_m)`
and `g_{s_m} → G`, then `∫_{A₀ × X} Φ dμ = ∫_{A₀} G dP₀` for every event `A₀` of the stopped σ-algebra at `s`. -/
theorem setIntegral_eq_of_dyadic {μ : Measure (Ω₀ × X)} [IsFiniteMeasure μ] (hμ : μ.map Prod.fst = P₀)
    {Φ : X → ℂ} (hΦ : Measurable Φ) {C : ℝ} (hC : 0 ≤ C) (hΦb : ∀ x, ‖Φ x‖ ≤ C)
    {E : ℝ≥0 → Set Ω₀} (hE : ∀ q, MeasurableSet (E q))
    {g : ℝ≥0 → Ω₀ → ℂ} (hg : ∀ q, Measurable ((E q).indicator (g q)))
    (hgb : ∀ᵐ ω ∂P₀, ∀ q, ω ∈ E q → ‖g q ω‖ ≤ C)
    (hDT : ∀ n k (A : Set Ω₀), MeasurableSet[𝓕₀ (dyad n k)] A →
      ∫ p in Prod.fst ⁻¹' (A ∩ E (dyad n k)), Φ p.2 ∂μ = ∫ ω in A ∩ E (dyad n k), g (dyad n k) ω ∂P₀)
    {s : Ω₀ → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    {G : Ω₀ → ℂ}
    (hlim : ∀ᵐ ω ∂P₀, (∀ᶠ m in atTop, ω ∈ E (dyadUp m (s ω))) ∧
        Tendsto (fun m => g (dyadUp m (s ω)) ω) atTop (𝓝 (G ω)))
    {A₀ : Set Ω₀} (hA₀ : MeasurableSet[hs.measurableSpace] A₀) :
    ∫ p in Prod.fst ⁻¹' A₀, Φ p.2 ∂μ = ∫ ω in A₀, G ω ∂P₀ := by
  have hsm : Measurable s := measurable_of_isStoppingTime hs
  have hA₀m : MeasurableSet A₀ := hs.measurableSpace_le _ hA₀
  set kf : ℕ → Ω₀ → ℕ := fun m ω => flr m (s ω) + 1 with hkf
  have hkfm : ∀ m, Measurable (kf m) := fun m => ((measurable_flr m).comp hsm).add_const 1
  have hup : ∀ m ω, dyadUp m (s ω) = dyad m (kf m ω) := fun _ _ => rfl
  set S : ℕ → Set Ω₀ := fun m => {ω | ω ∈ E (dyadUp m (s ω))} with hS
  set D : ℕ → ℕ → Set Ω₀ := fun m k => A₀ ∩ ({ω | kf m ω = k} ∩ E (dyad m k)) with hD
  have hDm : ∀ m k, MeasurableSet (D m k) := fun m k =>
    hA₀m.inter ((hkfm m (measurableSet_singleton k)).inter (hE _))
  have hDU : ∀ m, A₀ ∩ S m = ⋃ k, D m k := fun m => by
    ext ω
    simp only [hS, hD, mem_inter_iff, mem_ofPred_eq, mem_iUnion, hup]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨kf m ω, h1, rfl, h2⟩
    · rintro ⟨k, h1, rfl, h2⟩; exact ⟨h1, h2⟩
  have hDd : ∀ m, Pairwise (Function.onFun Disjoint (D m)) := fun m i j hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (hi.2.1.symm.trans hj.2.1)
  have hSm : ∀ m, MeasurableSet (A₀ ∩ S m) := fun m => by rw [hDU m]; exact MeasurableSet.iUnion (hDm m)
  obtain ⟨gs, hgs⟩ : ∃ gs : ℕ → Ω₀ → ℂ,
      gs = fun m ω => (E (dyadUp m (s ω))).indicator (g (dyadUp m (s ω))) ω := ⟨_, rfl⟩
  have hgs' : ∀ m ω, ω ∈ E (dyadUp m (s ω)) → gs m ω = g (dyadUp m (s ω)) ω := fun m ω h => by
    rw [hgs]; exact indicator_of_mem h _
  have hgsm : ∀ m, Measurable (gs m) := fun m => by
    obtain ⟨G, hG⟩ : ∃ G : ℕ → Ω₀ → ℂ, ∀ k, G k = (E (dyad m k)).indicator (g (dyad m k)) :=
      ⟨_, fun _ => rfl⟩
    have hGm : ∀ k, Measurable (G k) := fun k => by rw [hG]; exact hg _
    have h2 : Measurable fun p : Ω₀ × ℕ => G p.2 p.1 :=
      measurable_from_prod_countable_left fun k => hGm k
    have e : gs m = fun ω => G (kf m ω) ω := by
      funext ω
      rw [hgs]
      dsimp only
      rw [hup, hG]
    rw [e]
    exact h2.comp (measurable_id.prodMk (hkfm m))
  -- the identity at each level
  have hlev : ∀ m, ∫ p in Prod.fst ⁻¹' (A₀ ∩ S m), Φ p.2 ∂μ = ∫ ω in A₀ ∩ S m, gs m ω ∂P₀ := by
    intro m
    have hpk : ∀ k, ∫ p in Prod.fst ⁻¹' D m k, Φ p.2 ∂μ = ∫ ω in D m k, gs m ω ∂P₀ := by
      intro k
      obtain ⟨A', hA', hae⟩ := exists_ae_eq_inter_flr hs hA₀ m k
      have h := hDT m k A' hA'
      have hae' : A' ∩ E (dyad m k) =ᵐ[P₀] D m k := by
        have : D m k = (A₀ ∩ {ω | flr m (s ω) + 1 = k}) ∩ E (dyad m k) := by
          ext ω; simp only [hD, mem_inter_iff, mem_ofPred_eq, hkf]; tauto
        rw [this]
        exact hae.inter (EventuallyEq.refl _ _)
      rw [setIntegral_congr_set (preimage_fst_ae_eq hμ hae'), setIntegral_congr_set hae'] at h
      rw [h]
      refine setIntegral_congr_fun (hDm m k) fun ω hω => ?_
      have hk : kf m ω = k := hω.2.1
      have hω' : ω ∈ E (dyadUp m (s ω)) := by rw [hup, hk]; exact hω.2.2
      rw [hgs' m ω hω', hup, hk]
    have hint1 : IntegrableOn (fun p : Ω₀ × X => Φ p.2) (Prod.fst ⁻¹' (A₀ ∩ S m)) μ :=
      (Integrable.of_bound (hΦ.comp measurable_snd).aestronglyMeasurable C
        (Eventually.of_forall fun p => hΦb p.2)).integrableOn
    have hint2 : IntegrableOn (gs m) (A₀ ∩ S m) P₀ := by
      refine Integrable.of_bound (hgsm m).aestronglyMeasurable C ?_
      rw [ae_restrict_iff' (hSm m)]
      filter_upwards [hgb] with ω hω hωS
      rw [hgs' m ω hωS.2]
      exact hω _ hωS.2
    rw [hDU m, preimage_iUnion, integral_iUnion (fun k => measurable_fst (hDm m k))
      (fun i j hij => (hDd m hij).preimage _) (by rw [← preimage_iUnion, ← hDU m]; exact hint1),
      integral_iUnion (hDm m) (hDd m) (by rw [← hDU m]; exact hint2)]
    exact tsum_congr hpk
  -- the limit
  have hgood : ∀ᵐ ω ∂P₀, (∀ᶠ m in atTop, ω ∈ S m) ∧ Tendsto (fun m => gs m ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hlim] with ω hω
    refine ⟨hω.1, hω.2.congr' ?_⟩
    filter_upwards [hω.1] with m hm
    exact (hgs' m ω hm).symm
  have hL : Tendsto (fun m => ∫ p in Prod.fst ⁻¹' (A₀ ∩ S m), Φ p.2 ∂μ) atTop
      (𝓝 (∫ p in Prod.fst ⁻¹' A₀, Φ p.2 ∂μ)) := by
    simp_rw [← integral_indicator (measurable_fst (hSm _)), ← integral_indicator (measurable_fst hA₀m)]
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun m => ((hΦ.comp measurable_snd).indicator (measurable_fst (hSm m))).aestronglyMeasurable)
      (integrable_const C) (fun m => Eventually.of_forall fun p => ?_) ?_
    · by_cases hp : p ∈ Prod.fst ⁻¹' (A₀ ∩ S m)
      · rw [indicator_of_mem hp]; exact hΦb p.2
      · rw [indicator_of_notMem hp, norm_zero]; exact hC
    · have h' := preimage_fst_ae_eq hμ (show {ω | ∀ᶠ m in atTop, ω ∈ S m} =ᵐ[P₀] univ from
        (eventuallyEqSet_univ (s := {ω | ∀ᶠ m in atTop, ω ∈ S m})).2 (hgood.mono fun ω h => h.1))
      filter_upwards [(eventuallyEqSet_univ (s := Prod.fst ⁻¹' {ω | ∀ᶠ m in atTop, ω ∈ S m})).1 h'] with p hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hp] with m hm
      by_cases hpA : p.1 ∈ A₀
      · rw [indicator_of_mem (show p ∈ Prod.fst ⁻¹' A₀ from hpA),
          indicator_of_mem (show p ∈ Prod.fst ⁻¹' (A₀ ∩ S m) from ⟨hpA, hm⟩)]
      · rw [indicator_of_notMem (show p ∉ Prod.fst ⁻¹' A₀ from hpA),
          indicator_of_notMem (show p ∉ Prod.fst ⁻¹' (A₀ ∩ S m) from fun h => hpA h.1)]
  have hR : Tendsto (fun m => ∫ ω in A₀ ∩ S m, gs m ω ∂P₀) atTop (𝓝 (∫ ω in A₀, G ω ∂P₀)) := by
    simp_rw [← integral_indicator (hSm _), ← integral_indicator hA₀m]
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun m => ((hgsm m).indicator (hSm m)).aestronglyMeasurable)
      (integrable_const C) (fun m => ?_) ?_
    · filter_upwards [hgb] with ω hωb
      by_cases hω : ω ∈ A₀ ∩ S m
      · rw [indicator_of_mem hω, hgs' m ω hω.2]
        exact hωb _ hω.2
      · rw [indicator_of_notMem hω, norm_zero]; exact hC
    · filter_upwards [hgood] with ω hω
      obtain ⟨hev, hlimω⟩ := hω
      by_cases hωA : ω ∈ A₀
      · rw [indicator_of_mem hωA]
        refine hlimω.congr' ?_
        filter_upwards [hev] with m hm
        exact (indicator_of_mem (show ω ∈ A₀ ∩ S m from ⟨hωA, hm⟩) _).symm
      · rw [indicator_of_notMem hωA]
        exact tendsto_const_nhds.congr' (Eventually.of_forall fun m =>
          (indicator_of_notMem (fun h => hωA h.1) _).symm)
  exact tendsto_nhds_unique (hL.congr hlev) hR

end Approx

/-! ### Aliveness after a time (deterministic) -/

section Alive

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {K : Set ℂ}

/-- **A compact set outside the hull at `s < ζ` stays alive a little longer** (lower semicontinuity of the swallowing
time of the clamped driver). -/
theorem exists_gt_forall_alive (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hK : IsCompact K) (hKH : K ⊆ H)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ) (hdis : Disjoint K (fwdHull (rpath w) s)) :
    ∃ t₁ : ℝ≥0, s < t₁ ∧ (t₁ : ℝ≥0∞) < ζ ∧ ∀ z ∈ K, ∃ u, IsForwardSol (rpath w) z t₁ u := by
  obtain ⟨T, hsT, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hsT' : s < T := by exact_mod_cast hsT
  set A := clampDrv (rpath w) T with hA
  have hAc : Continuous A := continuous_clampDrv T.coe_nonneg (continuousOn_rpath hw hTζ)
  have hEq : ∀ t : ℝ≥0, t ≤ T → ∀ z u, IsForwardSol (rpath w) z t u ↔ IsForwardSol A z t u := by
    intro t ht z u
    refine isForwardSol_iff_of_eqOn (fun r hr => ?_) u
    exact (clampDrv_eqOn (W := rpath w) (T := T) ⟨hr.1, hr.2.trans (by exact_mod_cast ht)⟩).symm
  have hlt : ∀ z ∈ K, ENNReal.ofReal s < swallowTime A z := by
    intro z hz
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem s.coe_nonneg
      ⟨hKH hz, fun h => Set.disjoint_left.1 hdis hz h⟩
    have hu' := (hEq s hsT'.le z u).1 hu
    have hn := notMem_fwdHull_of_isForwardSol hAc (hKH hz) s.coe_nonneg hu'
    by_contra hle
    exact hn ⟨hKH hz, not_lt.1 hle⟩
  -- a common time below every swallowing time of `K`
  obtain ⟨m, hsm, hmK⟩ : ∃ m : ℝ≥0∞, ENNReal.ofReal s < m ∧ ∀ z ∈ K, m ≤ swallowTime A z := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊤, by simp, fun z hz => absurd hz (Set.notMem_empty z)⟩
    obtain ⟨z₀, hz₀, hmin⟩ :=
      (CoreArc.lowerSemicontinuousOn_swallowTime hAc hKH).exists_isMinOn hne hK
    exact ⟨swallowTime A z₀, hlt z₀ hz₀, fun z hz => hmin hz⟩
  obtain ⟨t₂, -, hst₂, ht₂m⟩ := ENNReal.lt_iff_exists_real_btwn.1 hsm
  have hs₂ : (s : ℝ) < t₂ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.coe_nonneg).1 hst₂
  set t₁ : ℝ≥0 := min (Real.toNNReal t₂) ((s + T) / 2) with ht₁
  have hst₁ : s < t₁ := by
    refine lt_min ?_ ?_
    · exact (Real.lt_toNNReal_iff_coe_lt).2 hs₂
    · rw [lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; linarith [hsT']
  have ht₁T : t₁ ≤ T := (min_le_right _ _).trans (by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]; linarith [hsT'.le])
  refine ⟨t₁, hst₁, lt_of_le_of_lt (by exact_mod_cast ht₁T) hTζ, fun z hz => ?_⟩
  have hzA : z ∈ H \ fwdHull A t₁ := by
    refine ⟨hKH hz, fun h => ?_⟩
    have h1 : swallowTime A z ≤ ENNReal.ofReal t₁ := h.2
    have h2 : ENNReal.ofReal t₁ ≤ ENNReal.ofReal t₂ :=
      ENNReal.ofReal_le_ofReal ((NNReal.coe_le_coe.2 (min_le_left _ _)).trans
        (Real.coe_toNNReal _ (s.coe_nonneg.trans hs₂.le)).le)
    exact (not_le.2 (ht₂m.trans_le (hmK z hz))) (h1.trans h2)
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem t₁.coe_nonneg hzA
  exact ⟨u, (hEq t₁ ht₁T z u).2 hu⟩

/-- A compact set alive at `t < ζ` is safe at `t` with some margin. -/
theorem exists_isSafeAt_of_alive (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hK : IsCompact K) (hKH : K ⊆ H)
    {t : ℝ≥0} (htζ : (t : ℝ≥0∞) < ζ) (halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath w) z t u) :
    ∃ δ > 0, IsSafeAt K δ t t ζ w t := by
  have hwt := continuousOn_rpath hw htζ
  have hW' := continuous_clampDrv t.coe_nonneg hwt
  have hKt : K ⊆ H \ fwdHull (clampDrv (rpath w) t) t := fun z hz =>
    mem_diff_fwdHull_clampDrv t.coe_nonneg hwt (hKH hz) (halive z hz)
  obtain ⟨δ₀, hδ₀, hprot⟩ := exists_isProtected_of_isCompact hW' t.coe_nonneg hK hKt
  refine ⟨δ₀, hδ₀, htζ, le_rfl, le_rfl, fun z hz => ⟨halive z hz, ?_⟩⟩
  have := (hprot z hz).2
  rwa [fwdMap_clampDrv_of_le le_rfl] at this

end Alive

/-! ### Right continuity of the protected characteristic function -/

section CfAt

variable {Ω : Type*} {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **`cfAt` is right continuous** at a time `s < ζ` at which a compact `K ⊇ supp ψ` is outside the hull: along the
dyadic times `s_m ↓ s` it converges to its value at `s`. -/
theorem tendsto_cfAt_dyadUp (u : Ω → ℝ≥0 → ℂ → ℝ) {ω : Ω}
    (hu : ∀ t, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
      (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t))
    (hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hvLc : ∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hvRc : ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hordL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i, VL i t ω ≤ W t ω)
    (hordR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ i, W t ω ≤ VR i t ω)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hψK : tsupport ψ ⊆ K) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) s)) :
    Tendsto (fun m => cfAt κ W u ψ 1 (fun _ => dyadUp m s) ω) atTop
      (𝓝 (cfAt κ W u ψ 1 (fun _ => s) ω)) := by
  obtain ⟨t₁, hst₁, ht₁ζ, halive⟩ := exists_gt_forall_alive hw hK hKH hs hdis
  obtain ⟨δ, hδ, hsafe⟩ := exists_isSafeAt_of_alive hw hK hKH ht₁ζ halive
  have hψH : tsupport (ψ : ℂ → ℝ) ⊆ H := hψK.trans hKH
  have hsafeψ := hsafe.subset hψK
  have hMeq : ∀ t ∈ Iic t₁,
      (∫ z, meanCan κ ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω) t z * ψ z) =
        ∫ z, couplingMean κ (rpath fun t => W t ω) t (u ω t) z * ψ z := by
    intro t ht
    have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast (mem_Iic.1 ht)) ht₁ζ
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    by_cases hz : z ∈ tsupport (ψ : ℂ → ℝ)
    · have h := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (vL := fun i t => VL i t ω)
        (vR := fun i t => VR i t ω) hw hψH hsafeψ hδ (mem_Iic.1 ht) hz (hordL t htζ) (hordR t htζ) (hu t)
      dsimp only
      rw [h]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hMc : ContinuousOn (fun t : ℝ≥0 => ∫ z, couplingMean κ (rpath fun t => W t ω) (t : ℝ) (u ω t) z * ψ z)
      (Iic t₁) :=
    (hsafeψ.continuousOn_meanInt ψ.continuous ψ.hasCompactSupport hw hvLc hvRc hψH hδ).congr
      fun t ht => (hMeq t ht).symm
  have hEc : ContinuousOn (fun t : ℝ≥0 => loewnerGreenEnergy (rpath fun t => W t ω) t ψ) (Iic t₁) :=
    hsafeψ.continuousOn_loewnerGreenEnergy ψ.continuous ψ.hasCompactSupport hw hψH hδ
  have hlim : Tendsto (fun m => dyadUp m s) atTop (𝓝[Iic t₁] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadUp s, ?_⟩
    exact (tendsto_dyadUp s).eventually (Iic_mem_nhds hst₁)
  have hMt := ((hMc s (mem_Iic.2 hst₁.le)).tendsto).comp hlim
  have hEt := ((hEc s (mem_Iic.2 hst₁.le)).tendsto).comp hlim
  have hcont : Continuous fun p : ℝ × ℝ => Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (p.1 : ℂ) -
      ((1 : ℝ) : ℂ) ^ 2 * (p.2 : ℂ) / 2) := by fun_prop
  exact (hcont.tendsto _).comp (hMt.prodMk_nhds hEt)

end CfAt


/-! ### The two constraints at a stop -/

section Constraints

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}
  {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ}
  {ζ : Ω₀ → ℝ≥0∞}

/-- The event that a set `K` is alive at time `q < ζ`. -/
def aliveEv (W : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞) (K : Set ℂ) (q : ℝ≥0) : Set Ω₀ :=
  {ω | (q : ℝ≥0∞) < ζ ω ∧ ∀ z ∈ K, ∃ v, IsForwardSol (rpath (W · ω)) z q v}

/-- Along the dyadic times above a protected stop one is eventually in the alive event. -/
theorem eventually_mem_aliveEv {ω : Ω₀} (hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) s)) :
    ∀ᶠ m in atTop, ω ∈ aliveEv W ζ K (dyadUp m s) := by
  obtain ⟨t₁, hst₁, ht₁ζ, halive⟩ := exists_gt_forall_alive hw hK hKH hs hdis
  filter_upwards [(tendsto_dyadUp s).eventually (Iic_mem_nhds hst₁)] with m hm
  refine ⟨lt_of_le_of_lt (by exact_mod_cast (mem_Iic.1 hm)) ht₁ζ, fun z hz => ?_⟩
  obtain ⟨v, hv⟩ := halive z hz
  exact ⟨v, isForwardSol_of_le hv (dyadUp m s).coe_nonneg (by exact_mod_cast (mem_Iic.1 hm))⟩

variable [IsProbabilityMeasure P₀]

/-- **The sampling identity at a stop for one test function, from the dyadic identities.** -/
theorem setIntegral_cexp_eq_cfAt_of_dyadic (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
    (u : Ω₀ → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)} [IsFiniteMeasure μ]
    (hμ : μ.map Prod.fst = P₀) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {E : ℝ≥0 → Set Ω₀} (hEm : ∀ q, MeasurableSet (E q))
    (hEae : ∀ᵐ ω ∂P₀, ∀ q, ω ∈ E q ↔ ω ∈ aliveEv W ζ K q)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψK : tsupport ψ ⊆ K)
    (hgm : ∀ q, Measurable ((E q).indicator fun ω => cfAt κ W u ψ 1 (fun _ => q) ω))
    (hDT : ∀ n k (A : Set Ω₀), MeasurableSet[𝓕₀ (dyad n k)] A →
        ∫ p in Prod.fst ⁻¹' (A ∩ E (dyad n k)), Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ =
          ∫ ω in A ∩ E (dyad n k), cfAt κ W u ψ 1 (fun _ => dyad n k) ω ∂P₀)
    {s : Ω₀ → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂P₀, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)))
    {A₀ : Set Ω₀} (hA₀ : MeasurableSet[hs.measurableSpace] A₀) :
    ∫ p in Prod.fst ⁻¹' A₀, Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ = ∫ ω in A₀, cfAt κ W u ψ 1 s ω ∂P₀ := by
  have hpath := hE.2.2.2.2
  refine setIntegral_eq_of_dyadic hμ (Φ := fun x => Complex.exp (Complex.I * (x ψ : ℂ)))
    (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)) zero_le_one
    (fun x => (Complex.norm_exp_I_mul_ofReal _).le) hEm (g := fun q ω => cfAt κ W u ψ 1 (fun _ => q) ω)
    hgm ?_ hDT hs ?_ hA₀
  · filter_upwards [hEae, hpath] with ω hω hp q hq
    obtain ⟨hqζ, hal⟩ := (hω q).1 hq
    exact norm_cfAt_le_one u 1 ψ (r := fun _ => q) (continuousOn_rpath hp.2.2.2.1 hqζ) hp.1
      fun z hz => hal z (hψK hz)
  · filter_upwards [hEae, hpath, hsafe] with ω hω hp hsω
    refine ⟨?_, ?_⟩
    · filter_upwards [eventually_mem_aliveEv hp.2.2.2.1 hK hKH hsω.1 hsω.2] with m hm
      exact (hω _).2 hm
    · exact tendsto_cfAt_dyadUp u (hu ω) hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1
        (fun t ht i => hp.2.2.2.2.2.2.2.1 t ht i) (fun t ht i => hp.2.2.2.2.2.2.2.2.1 t ht i)
        hK hKH ψ hψK hsω.1 hsω.2

/-- **The sampling constraint at a stop from the dyadic constraints.** -/
theorem isSampledCoupling_of_dyadic (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
    (u : Ω₀ → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    {μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)} [IsFiniteMeasure μ]
    (hμ : μ.map Prod.fst = P₀) {K U : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) (hUK : U ⊆ K)
    {E : ℝ≥0 → Set Ω₀} (hEm : ∀ q, MeasurableSet (E q))
    (hEae : ∀ᵐ ω ∂P₀, ∀ q, ω ∈ E q ↔ ω ∈ aliveEv W ζ K q)
    (hgm : ∀ (ψ : LQGMetric.TestOn upperHalfPlaneOpens) q,
      Measurable ((E q).indicator fun ω => cfAt κ W u ψ 1 (fun _ => q) ω))
    (hDT : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U → ∀ n k (A : Set Ω₀),
      MeasurableSet[𝓕₀ (dyad n k)] A →
        ∫ p in Prod.fst ⁻¹' (A ∩ E (dyad n k)), Complex.exp (Complex.I * (p.2 ψ : ℂ)) ∂μ =
          ∫ ω in A ∩ E (dyad n k), cfAt κ W u ψ 1 (fun _ => dyad n k) ω ∂P₀)
    {s : Ω₀ → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂P₀, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω))) :
    IsSampledCoupling κ W u P₀ U hs μ := fun ψ hψ _ hA₀ =>
  setIntegral_cexp_eq_cfAt_of_dyadic hE u hu hμ hK hKH hEm hEae ψ (hψ.trans hUK) (hgm ψ) (hDT ψ hψ) hs hsafe hA₀

/-- **The projection-independence constraint at a stop from the dyadic constraints.** -/
theorem isProjIndepCoupling_of_dyadic (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
    {μ : Measure (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens)} [IsFiniteMeasure μ]
    (hμ : μ.map Prod.fst = P₀) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (O : TopologicalSpace.Opens ℂ)
    {E : ℝ≥0 → Set Ω₀} (hEm : ∀ q, MeasurableSet (E q))
    (hEae : ∀ᵐ ω ∂P₀, ∀ q, ω ∈ E q ↔ ω ∈ aliveEv W ζ K q)
    (hDT : ∀ (f : LQGMetric.MarkovZB.zsSub (O : Set ℂ)) (Ξ : LQGMetric.TestOn upperHalfPlaneOpens) n k
      (A : Set Ω₀), MeasurableSet[𝓕₀ (dyad n k)] A →
        ∫ p in Prod.fst ⁻¹' (A ∩ E (dyad n k)), Complex.exp (Complex.I * (p.2 (LocalSets.lapTest O f + Ξ) : ℂ)) ∂μ =
          projFactor O f Ξ * ∫ p in Prod.fst ⁻¹' (A ∩ E (dyad n k)), Complex.exp (Complex.I * (p.2 Ξ : ℂ)) ∂μ)
    {s : Ω₀ → ℝ≥0} (hs : IsStoppingTime (usualAugmentation 𝓕₀ P₀) fun ω => (s ω : WithTop ℝ≥0))
    (hsafe : ∀ᵐ ω ∂P₀, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω))) :
    IsProjIndepCoupling O hs μ := by
  intro f Ξ A₀ hA₀
  set c : ℂ := projFactor O f Ξ with hc
  have hm1 : Measurable fun x : LQGMetric.DistOn upperHalfPlaneOpens =>
      Complex.exp (Complex.I * (x (LocalSets.lapTest O f + Ξ) : ℂ)) :=
    GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply _)
  have hm2 : Measurable fun x : LQGMetric.DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (x Ξ : ℂ)) :=
    GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply _)
  have hb : ∀ x : LQGMetric.DistOn upperHalfPlaneOpens, ‖Complex.exp (Complex.I * (x (LocalSets.lapTest O f + Ξ) : ℂ)) -
      c * Complex.exp (Complex.I * (x Ξ : ℂ))‖ ≤ 1 + ‖c‖ := fun x => by
    refine (norm_sub_le _ _).trans (add_le_add (Complex.norm_exp_I_mul_ofReal _).le ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Complex.norm_exp_I_mul_ofReal _).le
  have hint : ∀ S : Set (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens), ∀ F : LQGMetric.DistOn upperHalfPlaneOpens → ℂ,
      Measurable F → (∀ x, ‖F x‖ ≤ 1) → IntegrableOn (fun p => F p.2) S μ := fun S F hF hFb =>
    (Integrable.of_bound (hF.comp measurable_snd).aestronglyMeasurable 1
      (Eventually.of_forall fun p => hFb p.2)).integrableOn
  have hsplit : ∀ S : Set (Ω₀ × LQGMetric.DistOn upperHalfPlaneOpens),
      ∫ p in S, (Complex.exp (Complex.I * (p.2 (LocalSets.lapTest O f + Ξ) : ℂ)) -
        c * Complex.exp (Complex.I * (p.2 Ξ : ℂ))) ∂μ =
      (∫ p in S, Complex.exp (Complex.I * (p.2 (LocalSets.lapTest O f + Ξ) : ℂ)) ∂μ) -
        c * ∫ p in S, Complex.exp (Complex.I * (p.2 Ξ : ℂ)) ∂μ := fun S => by
    rw [integral_sub (hint S _ hm1 fun x => (Complex.norm_exp_I_mul_ofReal _).le)
      ((hint S _ hm2 fun x => (Complex.norm_exp_I_mul_ofReal _).le).const_mul c), integral_const_mul]
  have key := setIntegral_eq_of_dyadic hμ
    (Φ := fun x => Complex.exp (Complex.I * (x (LocalSets.lapTest O f + Ξ) : ℂ)) -
      c * Complex.exp (Complex.I * (x Ξ : ℂ))) (hm1.sub (hm2.const_mul c))
    (by positivity) hb hEm (g := fun _ _ => 0) (fun q => by
      rw [show (E q).indicator (fun _ : Ω₀ => (0 : ℂ)) = fun _ => 0 from indicator_zero' _]
      exact measurable_const)
    (ae_of_all _ fun ω q _ => by simp only [norm_zero]; positivity) (fun n k A hA => by
      rw [hsplit, hDT f Ξ n k A hA, sub_self, integral_zero]) hs (G := fun _ => 0) ?_ hA₀
  · rw [hsplit, integral_zero, sub_eq_zero] at key
    exact key
  · filter_upwards [hEae, hE.2.2.2.2, hsafe] with ω hω hp hsω
    refine ⟨?_, tendsto_const_nhds⟩
    filter_upwards [eventually_mem_aliveEv hp.2.2.2.1 hK hKH hsω.1 hsω.2] with m hm
    exact (hω _).2 hm

end Constraints

end Param12

end Exist

end InteractingSLE
