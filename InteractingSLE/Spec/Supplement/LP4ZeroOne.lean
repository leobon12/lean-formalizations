/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LP4Terminal
import InteractingSLE.Spec.Sec2.RestartMarkov
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Aux. lemma 128 for driver events: the dilation zero–one law of the two-seed law

Packet PROVE-LP14 (the zero–one input of Proposition LP4). Specification §7.4, Aux. lemma 128
(`source/spec/p385-432.md` L335–L353, pp. 403–404): "Fix `k > 0` and `r_L, r_R > −2`. Let `X = (W, V^L, V^R)` be the
canonical integrated two-seed driving evolution, with all three initial coordinates zero. Every measurable event of
its full path law that is invariant under all positive dilations has probability zero or one."

This file proves it for events of the driving path (`aux128DriverStatement : Aux128DriverStatement`), following the
source's proof:

* **The germ is trivial** (`map_killedPath_germ`): "Let `A ∈ ⋂_{t>0} 𝓕_t` with `ℙ(A) > 0`, and put `ℚ = ℙ(· | A)`.
  […] Thus `B` remains Brownian in the retained filtration under `ℚ`. The integrated equations […] remain valid under
  `ℚ`. The weak uniqueness proved in Theorem 2.2 therefore gives the same law for `X` under both measures. Since `A`
  is measurable from `X` up to completion, this implies `ℙ(A) = ℚ(A) = 1`." The event lies in the usual augmentation
  at time `0`; the conditioned Brownian motion is `Sec2.Restart.isFilteredBrownianReal_restart_cond` at the stopping
  time `0`; uniqueness is `Sec7.map_killedRestrict_eq`.
* **Dilation invariance of the path law** (`map_dilPath_map_killedPath`): "The same equations and uniqueness show that
  `Θ_c` preserves the path law" (`IsIntegratedSLEEvolution.dilate_zero`).
* **Approximation** (`exists_germ_ae_eq`): "For every `ε > 0` there are a finite `T` and a […] `𝓕_T`-measurable path
  function `f` such that `𝔼|1_E − f| < ε` […]. Then `f ∘ Θ_c` is `𝓕_t`-measurable […]. The closedness of `L¹(𝓕_t)`
  now gives `E ∈ 𝓕_t` up to completion. Apply this for `t = 1/n` and intersect." Here with sets: the past σ-algebras
  `pathPast n` of path space form a ring generating the product σ-algebra, so `G` is approximated in measure by a set of
  some `pathPast n` (`exists_measure_symmDiff_lt_of_generateFrom_isSetRing`); its preimage under a small dilation lies
  in `pathPast t`; a Borel–Cantelli `limsup` of such sets for `t = 1/(k+1)` is a germ set equal to `G` almost
  everywhere.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal symmDiff

universe u

namespace InteractingSLE.LP

namespace ZeroOne

open Sec7.Dilation

/-! ### The past σ-algebras of path space -/

/-- The σ-algebra of the coordinates `x s`, `s ≤ t`, of a real path. -/
@[instance_reducible] def pathPast (t : ℝ≥0) : MeasurableSpace (ℝ≥0 → ℝ) :=
  ⨆ s : {s : ℝ≥0 // s ≤ t}, MeasurableSpace.comap (fun x : ℝ≥0 → ℝ => x s.1) inferInstance

theorem pathPast_le (t : ℝ≥0) : pathPast t ≤ MeasurableSpace.pi :=
  iSup_le fun s => (measurable_pi_apply s.1).comap_le

theorem pathPast_mono : Monotone pathPast := fun _ _ h =>
  iSup_le fun s => le_iSup_of_le (⟨s.1, s.2.trans h⟩ : {s : ℝ≥0 // s ≤ _}) le_rfl

theorem measurable_coord_pathPast {s t : ℝ≥0} (h : s ≤ t) :
    Measurable[pathPast t] fun x : ℝ≥0 → ℝ => x s :=
  measurable_iff_comap_le.2 (le_iSup (fun s : {s : ℝ≥0 // s ≤ t} =>
    MeasurableSpace.comap (fun x : ℝ≥0 → ℝ => x s.1) inferInstance) ⟨s, h⟩)

/-- A map into paths whose coordinates up to `t` are `m`-measurable pulls `pathPast t` back into `m`. -/
theorem comap_pathPast_le {α : Type*} {m : MeasurableSpace α} {f : α → ℝ≥0 → ℝ} {t : ℝ≥0}
    (hf : ∀ s ≤ t, Measurable[m] fun a => f a s) : (pathPast t).comap f ≤ m := by
  rw [pathPast, MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 (hf s.1 s.2)

/-- The sets measurable for the past up to some integer time. -/
def pastRing : Set (Set (ℝ≥0 → ℝ)) := {S | ∃ n : ℕ, MeasurableSet[pathPast n] S}

theorem isSetRing_pastRing : IsSetRing pastRing where
  empty_mem := ⟨0, @MeasurableSet.empty _ (pathPast ((0 : ℕ) : ℝ≥0))⟩
  union_mem := by
    rintro S T ⟨m, hS⟩ ⟨n, hT⟩
    exact ⟨max m n, (pathPast_mono (Nat.cast_le.2 (le_max_left m n)) _ hS).union
      (pathPast_mono (Nat.cast_le.2 (le_max_right m n)) _ hT)⟩
  sdiff_mem := by
    rintro S T ⟨m, hS⟩ ⟨n, hT⟩
    exact ⟨max m n, (pathPast_mono (Nat.cast_le.2 (le_max_left m n)) _ hS).diff
      (pathPast_mono (Nat.cast_le.2 (le_max_right m n)) _ hT)⟩

theorem generateFrom_pastRing :
    MeasurableSpace.generateFrom pastRing = (MeasurableSpace.pi : MeasurableSpace (ℝ≥0 → ℝ)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun S ⟨n, hS⟩ => pathPast_le n S hS) ?_
  refine iSup_le fun t => measurable_iff_comap_le.1 fun A hA => ?_
  exact MeasurableSpace.measurableSet_generateFrom ⟨⌈t⌉₊, measurable_coord_pathPast (Nat.le_ceil t) hA⟩

/-- **Approximation by the past**: a measurable set of paths is approximated in measure by a set of some integer
past. -/
theorem exists_pathPast_symmDiff_lt (μ : Measure (ℝ≥0 → ℝ)) [IsFiniteMeasure μ] {G : Set (ℝ≥0 → ℝ)}
    (hG : MeasurableSet G) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ H, MeasurableSet[pathPast n] H ∧ μ (H ∆ G) < ε := by
  obtain ⟨H, ⟨n, hH⟩, hlt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ) isSetRing_pastRing
    ⟨{univ}, countable_singleton _, singleton_subset_iff.2 ⟨0, @MeasurableSet.univ _ (pathPast ((0 : ℕ) : ℝ≥0))⟩, by simp⟩
    generateFrom_pastRing.symm hG hε
  exact ⟨n, H, hH, hlt⟩

/-! ### Dilations of path space -/

theorem measurable_dilPath {c : ℝ≥0} : Measurable (dilPath c) :=
  measurable_pi_iff.2 fun _ => (measurable_pi_apply _).const_mul _

/-- The dilation by `c` reads the coordinates up to `c t` to produce those up to `t`. -/
theorem measurable_dilPath_pathPast {c : ℝ≥0} (t : ℝ≥0) :
    @Measurable _ _ (pathPast (c * t)) (pathPast t) (dilPath c) :=
  measurable_iff_comap_le.2 (comap_pathPast_le fun _ hs =>
    (measurable_coord_pathPast (mul_le_mul_of_nonneg_left hs c.2)).const_mul _)

/-- **A dilation-invariant event lies in the germ σ-algebra up to a null set** (Aux. lemma 128's proof, (EZ13.2)). -/
theorem exists_germ_ae_eq (μ : Measure (ℝ≥0 → ℝ)) [IsFiniteMeasure μ]
    (hμ : ∀ c : ℝ≥0, c ≠ 0 → μ.map (dilPath c) = μ) {G : Set (ℝ≥0 → ℝ)} (hG : MeasurableSet G)
    (hinv : ∀ c : ℝ≥0, c ≠ 0 → μ ((dilPath c ⁻¹' G) ∆ G) = 0) :
    ∃ A : Set (ℝ≥0 → ℝ), (∀ t : ℝ≥0, 0 < t → MeasurableSet[pathPast t] A) ∧ μ (A ∆ G) = 0 := by
  -- for each `k`, a set of the past up to `1/(k+1)` within `2^{-k}` of `G`
  have hstep : ∀ k : ℕ, ∃ H, MeasurableSet[pathPast ((k : ℝ≥0) + 1)⁻¹] H ∧ μ (H ∆ G) < (2⁻¹ : ℝ≥0∞) ^ k := by
    intro k
    obtain ⟨n, H, hH, hlt⟩ := exists_pathPast_symmDiff_lt μ hG (ε := (2⁻¹ : ℝ≥0∞) ^ k)
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) k)
    set c : ℝ≥0 := ((k : ℝ≥0) + 1)⁻¹ / ((n : ℝ≥0) + 1) with hc
    have hc0 : c ≠ 0 := by rw [hc]; positivity
    have hcn : c * n ≤ ((k : ℝ≥0) + 1)⁻¹ := by
      rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      gcongr
      exact le_self_add
    refine ⟨dilPath c ⁻¹' H, pathPast_mono hcn _ (measurable_dilPath_pathPast (c := c) (n : ℝ≥0) hH), ?_⟩
    calc μ ((dilPath c ⁻¹' H) ∆ G)
        ≤ μ ((dilPath c ⁻¹' H) ∆ (dilPath c ⁻¹' G)) + μ ((dilPath c ⁻¹' G) ∆ G) := measure_symmDiff_le _ _ _
      _ = μ (H ∆ G) := by
        rw [hinv c hc0, add_zero, ← preimage_symmDiff,
          ← Measure.map_apply measurable_dilPath ((pathPast_le n _ hH).symmDiff hG), hμ c hc0]
      _ < _ := hlt
  choose H hH hlt using hstep
  refine ⟨⋂ m, ⋃ k ≥ m, H k, fun t ht => ?_, ?_⟩
  · -- germ measurability
    obtain ⟨M, hM⟩ := exists_nat_one_div_lt ht
    have hset : (⋂ m, ⋃ k ≥ m, H k) = ⋂ m, ⋃ k ≥ max m M, H k := by
      ext x
      simp only [mem_iInter, mem_iUnion]
      constructor
      · intro h m; exact h (max m M)
      · intro h m
        obtain ⟨k, hk, hx⟩ := h m
        exact ⟨k, le_trans (le_max_left _ _) hk, hx⟩
    rw [hset]
    refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => ?_
    have hkM : ((k : ℝ≥0) + 1)⁻¹ ≤ t := by
      refine le_trans ?_ (le_of_lt (by simpa [one_div] using hM))
      refine (inv_le_inv₀ (by positivity) (by positivity)).2 ?_
      exact_mod_cast Nat.add_le_add_right ((le_max_right m M).trans hk) 1
    exact pathPast_mono hkM _ (hH k)
  · -- Borel–Cantelli
    have hsum : ∑' k, μ (H k ∆ G) ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∑' k, (2⁻¹ : ℝ≥0∞) ^ k) ?_
        (ENNReal.tsum_le_tsum fun k => (hlt k).le)
      rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    refine measure_mono_null (fun x hx => ?_) (measure_limsup_atTop_eq_zero hsum)
    rw [limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, mem_iInter, mem_iUnion]
    intro m
    rcases mem_symmDiff.1 hx with ⟨hA, hGx⟩ | ⟨hGx, hA⟩
    · simp only [mem_iInter, mem_iUnion] at hA
      obtain ⟨k, hk, hxk⟩ := hA m
      exact ⟨k, hk, mem_symmDiff.2 (Or.inl ⟨hxk, hGx⟩)⟩
    · simp only [mem_iInter, mem_iUnion, not_forall, not_exists] at hA
      obtain ⟨m₀, hm₀⟩ := hA
      exact ⟨max m m₀, le_max_left _ _,
        mem_symmDiff.2 (Or.inr ⟨hGx, hm₀ (max m m₀) (le_max_right _ _)⟩)⟩

/-! ### The killed driving path and its law -/

section Law

variable {κ rL rR : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The driving path killed at the lifetime (value `0` from `ζ` on). -/
def killedPath (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℝ := fun t => Sec7.killedProc W ζ t ω

/-- The killed driver at time `t` is `𝓕_t`-measurable. -/
theorem measurable_killedProc_filtration (hW : AdaptedBefore 𝓕 ζ W) (t : ℝ≥0) :
    Measurable[𝓕 t] (Sec7.killedProc W ζ t) := by
  intro s hs
  have h1 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ s} := hW t s hs
  have h2 : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    have h := hW t univ MeasurableSet.univ
    simpa using h
  have hset : Sec7.killedProc W ζ t ⁻¹' s =
      {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ s} ∪ ({ω | (t : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ s}) := by
    ext ω
    by_cases h : (t : ℝ≥0∞) < ζ ω <;> simp [Sec7.killedProc, h]
  rw [hset]
  exact h1.union (h2.compl.inter (MeasurableSet.const _))

theorem measurable_killedPath (hW : AdaptedBefore 𝓕 ζ W) : Measurable (killedPath W ζ) :=
  measurable_pi_iff.2 fun t => Sec7.measurable_killedProc hW t

/-- The past of the killed driving path up to `t` is in `𝓕_t`. -/
theorem comap_killedPath_le (hW : AdaptedBefore 𝓕 ζ W) (t : ℝ≥0) :
    (pathPast t).comap (killedPath W ζ) ≤ 𝓕 t :=
  comap_pathPast_le fun s hs => (measurable_killedProc_filtration hW s).mono (𝓕.mono hs) le_rfl

/-- On infinite lifetime with a continuous driver, the law of the killed path is the extension of the law of its
rational-time values. -/
theorem map_killedPath_eq_of_ae (hW : AdaptedBefore 𝓕 ζ W)
    (hgood : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous fun t => W t ω) :
    P.map (killedPath W ζ) = (P.map (Sec7.killedRestrict W ζ)).map Sec7.extendRat := by
  rw [Measure.map_map Sec7.measurable_extendRat (Sec7.measurable_killedRestrict hW)]
  refine Measure.map_congr ?_
  filter_upwards [hgood] with ω ⟨hζ, hw⟩
  show killedPath W ζ ω = Sec7.extendRat (Sec7.killedRestrict W ζ ω)
  rw [Sec7.killedRestrict_eq_of_top hζ, Sec7.extendRat_eq hw]
  funext t
  simp [killedPath, Sec7.killedProc, hζ]

/-- **The dilation preserves the two-seed path law** (Aux. lemma 128's proof: "The same equations and uniqueness show
that `Θ_c` preserves the path law"). -/
theorem map_dilPath_map_killedPath (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {c : ℝ≥0} (hc : c ≠ 0) :
    (P.map (killedPath W ζ)).map (dilPath c) = P.map (killedPath W ζ) := by
  have hE' := hE.dilate_zero hc
  have hlaw := Sec7.map_killedRestrict_eq (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR
    Sec7.jacobiDiffusionExistsStatement hE' hE
  have hK := measurable_killedPath hE.2.1
  have hgood := ae_good hκ hL hR hE
  rw [Measure.map_map measurable_dilPath hK]
  have h1 : P.map (dilPath c ∘ killedPath W ζ) = P.map (killedPath (dilProc c W) fun ω => ζ ω / c) := by
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω ⟨hζ, _, _⟩
    funext t
    simp [killedPath, Sec7.killedProc, dilPath, dilProc, hζ, ENNReal.top_div_coe, ENNReal.mul_eq_top]
  have hgood' : ∀ᵐ ω ∂P, ζ ω / c = ⊤ ∧ Continuous fun t => dilProc c W t ω := by
    filter_upwards [hgood] with ω ⟨hζ, hw, _⟩
    exact ⟨by rw [hζ]; exact ENNReal.top_div_coe, continuous_dilPath (c := c) _ hw⟩
  rw [h1, map_killedPath_eq_of_ae hE'.2.1 hgood',
    map_killedPath_eq_of_ae hE.2.1 (hgood.mono fun ω h => ⟨h.1, h.2.1⟩), hlaw]

/-- The Brownian motion of a two-seed evolution vanishes at time `0` on the good event (the driving equation at
`t = 0`). -/
theorem brownian_zero_of_path {ω : Ω} (hκ : 0 < κ) (hζ : ζ ω = ⊤)
    (hp : IsIntegratedSLEPath κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) (fun t => W t ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) : B 0 ω = 0 := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hweq := hp.2.2.2.2.2.2.2.2.2.2.2.2.1 0 h0
  have hw0 : W 0 ω = 0 := hp.1
  simp only [NNReal.coe_zero, intervalIntegral.integral_same, Finset.sum_const_zero, add_zero] at hweq
  rw [hw0] at hweq
  rcases mul_eq_zero.1 hweq.symm with h | h
  · exact absurd h (Real.sqrt_pos.2 hκ).ne'
  · exact h

/-- **The germ of the two-seed path law is trivial** (Aux. lemma 128's proof, first paragraph). A set of paths that
is measurable for the past up to every positive time has probability `0` or `1` under the law of the killed driving
path. -/
theorem map_killedPath_germ (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ)
    {A : Set (ℝ≥0 → ℝ)} (hA : ∀ t : ℝ≥0, 0 < t → MeasurableSet[pathPast t] A) :
    P.map (killedPath W ζ) A = 0 ∨ P.map (killedPath W ζ) A = 1 := by
  have hK := measurable_killedPath hE.2.1
  have hAm : MeasurableSet A := pathPast_le 1 A (hA 1 one_pos)
  rw [Measure.map_apply hK hAm]
  set A₀ := killedPath W ζ ⁻¹' A with hA₀
  have hA₀t : ∀ t : ℝ≥0, 0 < t → MeasurableSet[𝓕 t] A₀ := fun t ht =>
    comap_killedPath_le hE.2.1 t _ ⟨A, hA t ht, rfl⟩
  have hA₀0 : MeasurableSet[usualAugmentation 𝓕 P 0] A₀ := by
    rw [Ito.usualAugmentation_apply]
    refine MeasurableSpace.measurableSet_iInf.2 fun u => MeasurableSpace.measurableSet_iInf.2 fun hu => ?_
    exact Ito.le_nullAugmented 𝓕 P u _ (hA₀t u hu)
  rcases eq_or_ne (P A₀) 0 with h0 | h0
  · exact Or.inl h0
  right
  -- the conditioned measure
  obtain ⟨B', -, hB'c, hB', hBB'⟩ := Sec2.Restart.exists_continuous_version hE.1
  have hT := isStoppingTime_const (usualAugmentation 𝓕 P) (0 : ℝ≥0)
  have hA₀T : MeasurableSet[hT.measurableSpace] A₀ := by
    rw [IsStoppingTime.measurableSpace_const]; exact hA₀0
  have hBQ := Sec2.Restart.isFilteredBrownianReal_restart_cond (T := fun _ => (0 : ℝ≥0)) hB' hB'c hT hA₀T h0
  have : IsProbabilityMeasure (P[|A₀]) := cond_isProbabilityMeasure h0
  have hQP : P[|A₀] ≪ P := cond_absolutelyContinuous
  have hle : 𝓕 ≤ Sec2.Restart.restartFiltration (usualAugmentation 𝓕 P) (fun _ => (0 : ℝ≥0)) hT := by
    intro s
    rw [Sec2.Restart.restartFiltration_apply]
    show 𝓕 s ≤ (isStoppingTime_const (usualAugmentation 𝓕 P) ((0 : ℝ≥0) + s)).measurableSpace
    rw [IsStoppingTime.measurableSpace_const, zero_add]
    exact Ito.le_usualAugmentation 𝓕 P s
  have hgood := ae_good hκ hL hR hE
  -- the processes are a two-seed evolution under the conditioned measure (Brownian motion `B' − B'_0`)
  have hEQ : IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) (P[|A₀])
      (Sec2.Restart.restartFiltration (usualAugmentation 𝓕 P) (fun _ => (0 : ℝ≥0)) hT) W VL VR
      (QuantumZipper.StrongMarkov.smShift B' fun _ => (0 : ℝ≥0)) ζ := by
    refine ⟨hBQ, Ito.adaptedBefore_mono hle hE.2.1, fun i => Ito.adaptedBefore_mono hle (hE.2.2.1 i),
      fun i => Ito.adaptedBefore_mono hle (hE.2.2.2.1 i), hQP.ae_le ?_⟩
    filter_upwards [hE.2.2.2.2, hBB', hgood] with ω hp hb ⟨hζ, _, _⟩
    have hb0 : B 0 ω = 0 := brownian_zero_of_path hκ hζ hp
    have heq : (fun t => QuantumZipper.StrongMarkov.smShift B' (fun _ => (0 : ℝ≥0)) t ω) = fun t => B t ω := by
      funext t
      simp only [QuantumZipper.StrongMarkov.smShift, zero_add, hb t, hb 0, hb0, sub_zero]
    rw [heq]
    exact hp
  -- Theorem 2.2's uniqueness: the same path law under both measures
  have hlaw := Sec7.map_killedRestrict_eq (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR
    Sec7.jacobiDiffusionExistsStatement hEQ hE
  have hgoodP : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous fun t => W t ω := hgood.mono fun ω h => ⟨h.1, h.2.1⟩
  have hmap : (P[|A₀]).map (killedPath W ζ) = P.map (killedPath W ζ) := by
    rw [map_killedPath_eq_of_ae hE.2.1 (hQP.ae_le hgoodP), map_killedPath_eq_of_ae hE.2.1 hgoodP, hlaw]
  have h1 : (P[|A₀]) A₀ = 1 := cond_apply_self h0 (measure_ne_top P A₀)
  have h2 : (P[|A₀]) A₀ = P A₀ := by
    rw [hA₀, ← Measure.map_apply hK hAm, ← Measure.map_apply hK hAm, hmap]
  rw [← h2, h1]

end Law

/-! ### Aux. lemma 128 -/

/-- **Aux. lemma 128 for events of the driver** (Specification pp. 403–404): for `k > 0` and `r_L, r_R > −2`, every
measurable dilation-invariant event of the two-seed driving path has probability `0` or `1`. This discharges the named
input `Aux128DriverStatement` of Proposition LP4. -/
theorem aux128DriverStatement : Aux128DriverStatement.{u} := by
  intro κ hκ rL rR hL hR G hG hinv Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hK := measurable_killedPath hE.2.1
  set μ := P.map (killedPath W ζ) with hμdef
  have hgood := ae_good hκ hL hR hE
  have hKW : ∀ᵐ ω ∂P, killedPath W ζ ω = fun t => W t ω := hgood.mono fun ω h => funext fun t => by
    simp [killedPath, Sec7.killedProc, h.1]
  have hinvμ : ∀ c : ℝ≥0, c ≠ 0 → μ ((dilPath c ⁻¹' G) ∆ G) = 0 := by
    intro c hc
    rw [hμdef, Measure.map_apply hK ((measurable_dilPath hG).symmDiff hG)]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hgood, hKW] with ω ⟨_, hw, hw0⟩ hk
    simp only [mem_preimage, hk, mem_symmDiff, hinv c hc _ hw hw0]
    tauto
  obtain ⟨A, hA, hAG⟩ := exists_germ_ae_eq μ (fun c hc => map_dilPath_map_killedPath hκ hL hR hE hc) hG hinvμ
  have hμG : μ G = μ A := (measure_congr (measure_symmDiff_eq_zero_iff.1 hAG)).symm
  rcases map_killedPath_germ hκ hL hR hE hA with h | h
  · right
    have h' : μ G = 0 := hμG.trans h
    rw [hμdef, Measure.map_apply hK hG] at h'
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h', hKW] with ω h1 h2
    rw [← h2]
    exact h1
  · left
    have h' : μ Gᶜ = 0 := by
      rw [measure_compl hG (measure_ne_top _ _), hμG, h, measure_univ, tsub_self]
    rw [hμdef, Measure.map_apply hK hG.compl] at h'
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h', hKW] with ω h1 h2
    rw [← h2]
    simpa using h1

end ZeroOne

/-- **Proposition LP4 from its positive-probability step alone**: `lp4Statement_of_inputs` with Aux. lemma 128 now
proved (`ZeroOne.aux128DriverStatement`). Conditional helper. -/
theorem lp4Statement_of_avoid (hpos : LP4AvoidStatement.{u}) : LP4Statement.{u} :=
  lp4Statement_of_inputs ZeroOne.aux128DriverStatement hpos

end InteractingSLE.LP
