import InteractingSLE.Spec.Sec2.MartingaleSingularCover
import InteractingSLE.Spec.Sec2.MartingaleCharacterization
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# Theorem 2.4, converse implication: assembly into an integrated `SLE_κ(ρ)` evolution

Packet PROVE-SEC2-MART2 (step R2 of `planning/handoffs/PROVE-SEC2-MART.md`). Specification, Theorem
2.4 (`source/spec/p001-048.md`, anchors `thm-2.4`, `thm-2.4-proof`, L819–L898): from the martingale
hypothesis and the deterministic properties of the force-point coordinates,

  `W_t = √κ B_t + ∫₀ᵗ ∑ⱼ ρⱼ/(W_s − Vʲ_s) ds`,  `Vʲ_t = xʲ + ∫₀ᵗ 2/(Vʲ_s − W_s) ds`

up to the continuation threshold, with `B = M/√κ` the Brownian motion of
`MartChar.isFilteredBrownianReal_of_couplingMean`, i.e. the coordinates form an integrated
`SLE_κ(ρ)` evolution in the frozen sense `IsIntegratedSLEEvolution`, with lifetime the first time
`thresholdTime` at which the threshold condition holds.

## Main results

* `thresholdTime`, `thresholdTime_mem_thresholdSet` (the threshold is attained, by the permanence
  of merging), `thresholdTime_le_iff`;
* `measurableSet_thresholdTime_le`, `adaptedBefore_thresholdTime`;
* `isIntegratedSLEPath_of_forceDefect_eq_zero` (pathwise assembly);
* `isIntegratedSLEEvolution_of_couplingMean` (the converse implication for force-point
  coordinates with the deterministic properties of geometric images).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

/-! ### The continuation threshold -/

section Threshold

variable {nL nR : ℕ}

/-- The times at which one side of the threshold condition holds. -/
def sideThreshold {n : ℕ} (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) : Set ℝ≥0 :=
  {t | (∑ i ∈ Finset.univ.filter (fun i => v i t = w t), ρ i) ≤ -2}

/-- The times at which the threshold condition holds. -/
def thresholdSet (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) : Set ℝ≥0 :=
  {t | ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)}

lemma thresholdSet_eq_union (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) :
    thresholdSet ρL ρR w vL vR = sideThreshold ρL w vL ∪ sideThreshold ρR w vR := rfl

open scoped Classical in
/-- The continuation threshold `T_*`: the first time at which the threshold condition holds
(`∞` if it never does). -/
def thresholdTime (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if (thresholdSet ρL ρR w vL vR).Nonempty then
    ((sInf (thresholdSet ρL ρR w vL vR) : ℝ≥0) : ℝ≥0∞) else ⊤

/-- **Merged points stay merged, so a side threshold is attained at the infimum.** -/
lemma mem_sideThreshold_of_mem_closure {n : ℕ} {ρ : Fin n → ℝ} {w : ℝ≥0 → ℝ}
    {v : Fin n → ℝ≥0 → ℝ} (hwc : Continuous w) (hvc : ∀ i, Continuous (v i))
    (hmerge : ∀ i j s t, s ≤ t → v i s = v j s → v i t = v j t) {T : ℝ≥0}
    (hT : T ∈ closure (sideThreshold ρ w v)) (hle : ∀ t ∈ sideThreshold ρ w v, T ≤ t) :
    T ∈ sideThreshold ρ w v := by
  have hU : sideThreshold ρ w v = ⋃ S : Finset (Fin n),
      {t | Finset.univ.filter (fun i => v i t = w t) = S ∧ (∑ i ∈ S, ρ i) ≤ -2} := by
    ext t
    simp only [sideThreshold, mem_ofPred_eq, mem_iUnion]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨S, hS, h⟩ => hS ▸ h⟩
  rw [hU, closure_iUnion_of_finite] at hT
  obtain ⟨S, hS⟩ := mem_iUnion.1 hT
  obtain ⟨t₁, ht₁S, ht₁⟩ := closure_nonempty_iff.1 ⟨T, hS⟩
  have hT1 : T ≤ t₁ := hle t₁ (by
    show (∑ i ∈ Finset.univ.filter (fun i => v i t₁ = w t₁), ρ i) ≤ -2
    rw [ht₁S]; exact ht₁)
  have hC : IsClosed {t | ∀ i ∈ S, v i t = w t} := by
    have : {t | ∀ i ∈ S, v i t = w t} = ⋂ i ∈ S, {t | v i t = w t} := by ext t; simp
    rw [this]
    exact isClosed_biInter fun i _ => isClosed_eq (hvc i) hwc
  have hsub : {t | Finset.univ.filter (fun i => v i t = w t) = S ∧ (∑ i ∈ S, ρ i) ≤ -2}
      ⊆ {t | ∀ i ∈ S, v i t = w t} := fun t ht i hi => by
    rw [← ht.1] at hi
    exact (Finset.mem_filter.1 hi).2
  have hTS : ∀ i ∈ S, v i T = w T := closure_minimal hsub hC hS
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at ht₁
    linarith
  obtain ⟨j, hj⟩ := hSne
  have hj1 : v j t₁ = w t₁ := by
    rw [← ht₁S] at hj
    exact (Finset.mem_filter.1 hj).2
  have hfil : Finset.univ.filter (fun i => v i T = w T) = S := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hi => ?_, hTS i⟩
    have hm := hmerge i j T t₁ hT1 (hi.trans (hTS j hj).symm)
    rw [← ht₁S]
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hm.trans hj1⟩
  show (∑ i ∈ Finset.univ.filter (fun i => v i T = w T), ρ i) ≤ -2
  rw [hfil]
  exact ht₁

variable {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
  {vR : Fin nR → ℝ≥0 → ℝ}

/-- Before the threshold time, the threshold condition fails. -/
lemma notMem_thresholdSet_of_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < thresholdTime ρL ρR w vL vR) :
    t ∉ thresholdSet ρL ρR w vL vR := by
  classical
  intro hmem
  have hne : (thresholdSet ρL ρR w vL vR).Nonempty := ⟨t, hmem⟩
  simp only [thresholdTime, hne, ite_true, ENNReal.coe_lt_coe] at ht
  exact notMem_of_lt_csInf ht (OrderBot.bddBelow _) hmem

/-- **The threshold is attained.** -/
lemma thresholdTime_mem_thresholdSet (hwc : Continuous w) (hvLc : ∀ i, Continuous (vL i))
    (hvRc : ∀ j, Continuous (vR j))
    (hmergeL : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t)
    (hmergeR : ∀ i j s t, s ≤ t → vR i s = vR j s → vR i t = vR j t) {T : ℝ≥0}
    (hT : thresholdTime ρL ρR w vL vR = T) : T ∈ thresholdSet ρL ρR w vL vR := by
  classical
  by_cases hne : (thresholdSet ρL ρR w vL vR).Nonempty
  · simp only [thresholdTime, hne, ite_true, ENNReal.coe_inj] at hT
    subst hT
    have hcl := csInf_mem_closure hne (OrderBot.bddBelow _)
    have hle : ∀ t ∈ thresholdSet ρL ρR w vL vR, sInf (thresholdSet ρL ρR w vL vR) ≤ t :=
      fun t ht => csInf_le (OrderBot.bddBelow _) ht
    rw [thresholdSet_eq_union, closure_union] at hcl
    rw [thresholdSet_eq_union] at hle ⊢
    rcases hcl with h | h
    · exact Or.inl (mem_sideThreshold_of_mem_closure hwc hvLc hmergeL h
        fun t ht => hle t (Or.inl ht))
    · exact Or.inr (mem_sideThreshold_of_mem_closure hwc hvRc hmergeR h
        fun t ht => hle t (Or.inr ht))
  · simp only [thresholdTime, hne, ite_false] at hT
    exact absurd hT ENNReal.top_ne_coe

lemma thresholdTime_le_iff (hwc : Continuous w) (hvLc : ∀ i, Continuous (vL i))
    (hvRc : ∀ j, Continuous (vR j))
    (hmergeL : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t)
    (hmergeR : ∀ i j s t, s ≤ t → vR i s = vR j s → vR i t = vR j t) (t : ℝ≥0) :
    thresholdTime ρL ρR w vL vR ≤ t ↔ ∃ u ≤ t, u ∈ thresholdSet ρL ρR w vL vR := by
  classical
  constructor
  · intro h
    have hne : thresholdTime ρL ρR w vL vR ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1 hne
    exact ⟨T, by rw [← hT] at h; exact ENNReal.coe_le_coe.1 h,
      thresholdTime_mem_thresholdSet hwc hvLc hvRc hmergeL hmergeR hT.symm⟩
  · rintro ⟨u, hut, hu⟩
    have hne : (thresholdSet ρL ρR w vL vR).Nonempty := ⟨u, hu⟩
    simp only [thresholdTime, hne, ite_true, ENNReal.coe_le_coe]
    exact (csInf_le (OrderBot.bddBelow _) hu).trans hut

end Threshold

/-! ### The threshold time is a stopping time -/

section Measurability

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- `{∃ u ≤ t, φ_u = 0 ≠ ψ_u}` is an `𝓕_t`-event for continuous adapted `φ`, `ψ` (a countable
union of `{first zero of |φ| + (1/(m+1) − |ψ|)⁺ ≤ t}`). -/
lemma measurableSet_exists_le_eq_zero_ne_zero {φ ψ : ℝ≥0 → Ω → ℝ}
    (hφc : ∀ ω, Continuous fun u => φ u ω) (hψc : ∀ ω, Continuous fun u => ψ u ω)
    (hφa : ∀ u, Measurable[𝓕 u] (φ u)) (hψa : ∀ u, Measurable[𝓕 u] (ψ u)) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | ∃ u ≤ t, φ u ω = 0 ∧ ψ u ω ≠ 0} := by
  set g : ℕ → ℝ≥0 → Ω → ℝ := fun m u ω => |φ u ω| + max 0 (1 / ((m : ℝ) + 1) - |ψ u ω|)
    with hg
  have hgc : ∀ m ω, Continuous fun u => g m u ω := fun m ω => by
    have h1 := hφc ω
    have h2 := hψc ω
    simp only [hg]
    fun_prop
  have hga : ∀ m u, Measurable[𝓕 u] (g m u) := fun m u => by
    have hF : Continuous fun p : ℝ × ℝ => |p.1| + max 0 (1 / ((m : ℝ) + 1) - |p.2|) := by
      fun_prop
    exact hF.measurable.comp ((hφa u).prodMk (hψa u))
  have hset : {ω | ∃ u ≤ t, φ u ω = 0 ∧ ψ u ω ≠ 0}
      = ⋃ m : ℕ, {ω | zeroHit (g m) 0 ω ≤ (t : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨u, hut, hφ, hψ⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 hψ)
      refine ⟨m, (zeroHit_le_iff (hgc m) 0 t ω).2 ⟨u, zero_le, hut, ?_⟩⟩
      simp only [hg, hφ, abs_zero, zero_add]
      exact max_eq_left (by linarith)
    · rintro ⟨m, hm⟩
      obtain ⟨u, -, hut, hu⟩ := (zeroHit_le_iff (hgc m) 0 t ω).1 hm
      simp only [hg] at hu
      have h1 := abs_nonneg (φ u ω)
      have h2 := le_max_left 0 (1 / ((m : ℝ) + 1) - |ψ u ω|)
      have h3 := le_max_right 0 (1 / ((m : ℝ) + 1) - |ψ u ω|)
      have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      refine ⟨u, hut, abs_eq_zero.1 (by linarith), fun h0 => ?_⟩
      have h4 : |ψ u ω| = 0 := by rw [h0, abs_zero]
      linarith
  rw [hset]
  exact MeasurableSet.iUnion fun m => (isStoppingTime_zeroHit (hgc m) (hga m) 0).measurableSet_le t

/-- One side of the threshold condition is met by time `t`: an `𝓕_t`-event. -/
lemma measurableSet_exists_le_mem_sideThreshold {n : ℕ} {ρ : Fin n → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {V : Fin n → ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVc : ∀ i ω, Continuous fun t => V i t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVa : ∀ i, StronglyAdapted 𝓕 (V i)) (t : ℝ≥0) :
    MeasurableSet[𝓕 t]
      {ω | ∃ u ≤ t, u ∈ sideThreshold ρ (fun s => W s ω) (fun i s => V i s ω)} := by
  have hset : {ω | ∃ u ≤ t, u ∈ sideThreshold ρ (fun s => W s ω) (fun i s => V i s ω)}
      = ⋃ S : Finset (Fin n), {_ω : Ω | (∑ i ∈ S, ρ i) ≤ -2} ∩
        {ω | ∃ u ≤ t, (∑ i ∈ S, |V i u ω - W u ω|) = 0 ∧ (∏ i ∈ Sᶜ, (V i u ω - W u ω)) ≠ 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, sideThreshold]
    have hiff : ∀ (S : Finset (Fin n)) (u : ℝ≥0),
        ((∑ i ∈ S, |V i u ω - W u ω|) = 0 ∧ (∏ i ∈ Sᶜ, (V i u ω - W u ω)) ≠ 0) ↔
          Finset.univ.filter (fun i => V i u ω = W u ω) = S := fun S u => by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg _), Finset.prod_ne_zero_iff,
        Finset.ext_iff]
      simp only [abs_eq_zero, sub_eq_zero, Finset.mem_compl, sub_ne_zero, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩ i
        exact ⟨fun h => by by_contra hi; exact h2 i hi h, h1 i⟩
      · intro h
        exact ⟨fun i hi => (h i).2 hi, fun i hi h' => hi ((h i).1 h')⟩
    constructor
    · rintro ⟨u, hut, hu⟩
      exact ⟨_, hu, u, hut, (hiff _ u).2 rfl⟩
    · rintro ⟨S, hS, u, hut, hu⟩
      exact ⟨u, hut, by rw [(hiff S u).1 hu]; exact hS⟩
  rw [hset]
  refine MeasurableSet.iUnion fun S => (@MeasurableSet.const Ω (𝓕 t) _).inter ?_
  refine measurableSet_exists_le_eq_zero_ne_zero (fun ω => ?_) (fun ω => ?_) (fun u => ?_)
    (fun u => ?_) t
  · exact continuous_finsetSum _ fun i _ => ((hVc i ω).sub (hWc ω)).abs
  · exact continuous_finsetProd _ fun i _ => (hVc i ω).sub (hWc ω)
  · exact Finset.measurable_sum _ fun i _ =>
      continuous_abs.measurable.comp ((hVa i u).measurable.sub (hWa u).measurable)
  · exact Finset.measurable_prod _ fun i _ => (hVa i u).measurable.sub (hWa u).measurable

variable {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **The threshold time is a stopping time.** -/
lemma measurableSet_thresholdTime_le (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ j ω, Continuous fun t => VR j t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω) (t : ℝ≥0) :
    MeasurableSet[𝓕 t] {ω | thresholdTime ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
      (fun j s => VR j s ω) ≤ t} := by
  have hset : {ω | thresholdTime ρL ρR (fun s => W s ω) (fun i s => VL i s ω)
      (fun j s => VR j s ω) ≤ t}
      = {ω | ∃ u ≤ t, u ∈ sideThreshold ρL (fun s => W s ω) (fun i s => VL i s ω)} ∪
        {ω | ∃ u ≤ t, u ∈ sideThreshold ρR (fun s => W s ω) (fun j s => VR j s ω)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union]
    rw [thresholdTime_le_iff (hWc ω) (fun i => hVLc i ω) (fun j => hVRc j ω) (hmergeL ω)
      (hmergeR ω), thresholdSet_eq_union]
    constructor
    · rintro ⟨u, hut, hu | hu⟩
      · exact Or.inl ⟨u, hut, hu⟩
      · exact Or.inr ⟨u, hut, hu⟩
    · rintro (⟨u, hut, hu⟩ | ⟨u, hut, hu⟩)
      · exact ⟨u, hut, Or.inl hu⟩
      · exact ⟨u, hut, Or.inr hu⟩
  rw [hset]
  exact (measurableSet_exists_le_mem_sideThreshold hWc hVLc hWa hVLa t).union
    (measurableSet_exists_le_mem_sideThreshold hWc hVRc hWa hVRa t)

/-- An adapted process is adapted before a stopping time (frozen `AdaptedBefore`). -/
lemma adaptedBefore_of_stronglyAdapted {ζ : Ω → ℝ≥0∞}
    (hζ : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | ζ ω ≤ t}) {X : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted 𝓕 X) : AdaptedBefore 𝓕 ζ X := fun t A hA => by
  have : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} = {ω | ζ ω ≤ t}ᶜ ∩ (X t) ⁻¹' A := by
    ext ω
    simp [not_le]
  rw [this]
  exact (hζ t).compl.inter ((hX t).measurable hA)

end Measurability

/-! ### Assembly -/

section Assembly

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {w b : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}

/-- The drift integral of one force point once its defect vanishes:
`∫₀ᵗ ρ/(W − V) = −½ ρ (V_t − x)`. -/
lemma integral_weight_div_eq {v : ℝ≥0 → ℝ} (ρ x : ℝ) (hv0 : v 0 = x) {t : ℝ≥0}
    (hd : forceDefect w v t = 0) :
    ∫ s in (0 : ℝ)..t, ρ / (w s.toNNReal - v s.toNNReal) = -(1 / 2) * (ρ * (v t - x)) := by
  have hpt : ∀ s : ℝ, ρ / (w s.toNNReal - v s.toNNReal)
      = (-(ρ / 2)) * (2 / (v s.toNNReal - w s.toNNReal)) := fun s => by
    rw [show w s.toNNReal - v s.toNNReal = -(v s.toNNReal - w s.toNNReal) by ring, div_neg]
    ring
  simp only [hpt, intervalIntegral.integral_const_mul]
  have h : ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal) = v t - x := by
    simp only [forceDefect] at hd
    rw [hv0] at hd
    linarith
  rw [h]
  ring

/-- **Pathwise assembly.** Force paths with the deterministic properties of geometric images,
whose driver is `√κ b − ½ ∑ⱼ ρⱼ (Vʲ − xʲ)` and whose defects vanish before the threshold time,
form an integrated `SLE_κ(ρ)` path (frozen `IsIntegratedSLEPath`) with lifetime the threshold
time. -/
theorem isIntegratedSLEPath_of_forceDefect_eq_zero {κ : ℝ}
    (hw0 : w 0 = 0) (hvL0 : ∀ i, vL i 0 = xL i) (hvR0 : ∀ j, vR j 0 = xR j)
    (hwc : Continuous w) (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (hordL : ∀ t i, vL i t ≤ w t) (hordR : ∀ t j, w t ≤ vR j t)
    (hidxL : ∀ t, Antitone fun i => vL i t) (hidxR : ∀ t, Monotone fun j => vR j t)
    (hmergeL : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t)
    (hmergeR : ∀ i j s t, s ≤ t → vR i s = vR j s → vR i t = vR j t)
    (hw : ∀ t, w t = Real.sqrt κ * b t
      - (1 / 2) * ((∑ i, ρL i * (vL i t - xL i)) + ∑ j, ρR j * (vR j t - xR j)))
    (hdefL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR w vL vR →
      ∀ i, forceDefect w (vL i) t = 0)
    (hdefR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR w vL vR →
      ∀ j, forceDefect w (vR j) t = 0) :
    IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b (thresholdTime ρL ρR w vL vR) := by
  have hvLc : ∀ i, Continuous (vL i) := fun i => (hpL i).1
  have hvRc : ∀ j, Continuous (vR j) := fun j => (hpR j).1
  refine ⟨hw0, hvL0, hvR0, hwc.continuousOn, fun i => (hvLc i).continuousOn,
    fun j => (hvRc j).continuousOn, fun t _ => hidxL t, fun t _ i => hordL t i,
    fun t _ j => hordR t j, fun t _ => hidxR t,
    fun t _ i => (hpL i).intervalIntegrable_inv_sub t,
    fun t _ j => (hpR j).intervalIntegrable_inv_sub t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [Finset.sum_congr rfl fun i _ =>
        integral_weight_div_eq (ρL i) (xL i) (hvL0 i) (hdefL t ht i),
      Finset.sum_congr rfl fun j _ =>
        integral_weight_div_eq (ρR j) (xR j) (hvR0 j) (hdefR t ht j),
      ← Finset.mul_sum, ← Finset.mul_sum, hw t]
    ring
  · intro t ht i
    have h := hdefL t ht i
    simp only [forceDefect, hvL0] at h
    linarith
  · intro t ht j
    have h := hdefR t ht j
    simp only [forceDefect, hvR0] at h
    linarith
  · intro i
    refine measure_mono_null ?_ (hpL i).2.2.2
    intro s hs
    exact ⟨hs.1, hs.2.2.symm⟩
  · intro j
    refine measure_mono_null ?_ (hpR j).2.2.2
    intro s hs
    exact ⟨hs.1, hs.2.2.symm⟩
  · intro t ht
    exact notMem_thresholdSet_of_lt ht
  · intro h0
    have h := thresholdTime_mem_thresholdSet hwc hvLc hvRc hmergeL hmergeR (T := 0)
      (by rw [h0, ENNReal.coe_zero])
    have h' : ForceWord.ThresholdCondition ρL ρR (w 0) (fun i => vL i 0) (fun j => vR j 0) := h
    have e1 : (fun i => vL i 0) = xL := funext hvL0
    have e2 : (fun j => vR j 0) = xR := funext hvR0
    rwa [hw0, e1, e2] at h'
  · intro T hT hTζ w₀ vL₀ vR₀ hlim
    have hmem := thresholdTime_mem_thresholdSet hwc hvLc hvRc hmergeL hmergeR hTζ.symm
    have hcont : Continuous fun t => (w t, fun i => vL i t, fun j => vR j t) :=
      hwc.prodMk ((continuous_pi hvLc).prodMk (continuous_pi hvRc))
    have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
    have heq := tendsto_nhds_unique hlim ((hcont.tendsto T).mono_left nhdsWithin_le_nhds)
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2, h3⟩ := heq
    rw [h1, h2, h3]
    exact hmem

end Assembly

/-! ### The converse implication of Theorem 2.4 -/

section Converse

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Theorem 2.4, converse implication, for force-point coordinates with the deterministic
properties of geometric images.** Let the driver `W` and the force-point coordinates `V^{i,q}` be
continuous adapted processes started at `(0; xL; xR)`, with the properties that geometric
force-point images have: side ordering `V^{i,L} ≤ W ≤ V^{j,R}`, index ordering, monotonicity in
time (left non-increasing, right non-decreasing), force paths (`IsForcePath`: `dV = 2/(V − W) dt`
away from a null collision set), merged points stay merged, and a left and a right point never meet
the driver at the same positive time. If every coupling mean `𝔥_t(z)`, `z ∈ ℍ`, is a local
martingale before `z` is swallowed, then `(W, V)` with the Brownian motion `B = M/√κ` is an
integrated `SLE_κ(ρ)` evolution whose lifetime is the continuation threshold. -/
theorem isIntegratedSLEEvolution_of_couplingMean [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hVL0 : ∀ i ω, VL i 0 ω = xL i) (hVR0 : ∀ i ω, VR i 0 ω = xR i)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    (hmart : ∀ u : Ω → ℝ≥0 → ℂ → ℝ,
      (∀ ω t, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)) (u ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
        (fun ω => (QuantumZipper.swallowTime (fun s : ℝ => W s.toNNReal ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (fun s : ℝ => W s.toNNReal ω) t (u ω t) z)) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR
      (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ)
      (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω)) := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hVc : ∀ j ω, Continuous fun t => jointV VL VR j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hB := isFilteredBrownianReal_of_couplingMean hκ hW0 hVL0 hVR0 hWc hWa hVLa hVRa hordL
    hordR hpathL hpathR hmart
  have hBpre := LocalTime.isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hBc : ∀ ω, Continuous fun t =>
      martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ := fun ω =>
    (continuous_martProc hWc hVc ω).div_const _
  have hdec := fun t ω => driver_eq_sqrt_mul_sub (ρL := ρL) (ρR := ρR) hκ hW0 hVL0 hVR0 t ω
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hL := ae_forceDefect_left_eq_zero hsk hBpre hBc hdec hWc hWa hVLa hVRa hpathL hpathR
    hordL hantiL hmonoR hmergeL hidxL hsep
  have hR := ae_forceDefect_right_eq_zero hsk hBpre hBc hdec hWc hWa hVLa hVRa hpathL hpathR
    hordR hantiL hmonoR hmergeR hidxR hsep
  have hζ := measurableSet_thresholdTime_le (ρL := ρL) (ρR := ρR) hWc hVLc hVRc hWa hVLa hVRa
    hmergeL hmergeR
  refine ⟨hB, adaptedBefore_of_stronglyAdapted hζ hWa,
    fun i => adaptedBefore_of_stronglyAdapted hζ (hVLa i),
    fun j => adaptedBefore_of_stronglyAdapted hζ (hVRa j), ?_⟩
  filter_upwards [hL, hR] with ω hLω hRω
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < thresholdTime ρL ρR (fun t => W t ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) → ∀ u ≤ t,
      ¬ ForceWord.ThresholdCondition ρL ρR (W u ω) (fun i => VL i u ω) (fun j => VR j u ω) :=
    fun t ht u hu => notMem_thresholdSet_of_lt ((ENNReal.coe_le_coe.2 hu).trans_lt ht)
  exact isIntegratedSLEPath_of_forceDefect_eq_zero (hW0 ω) (fun i => hVL0 i ω)
    (fun j => hVR0 j ω) (hWc ω) (hpathL ω) (hpathR ω) (hordL ω) (hordR ω) (hidxL ω) (hidxR ω)
    (hmergeL ω) (hmergeR ω) (fun t => hdec t ω) (fun t ht i => hLω t (hnot t ht) i)
    (fun t ht j => hRω t (hnot t ht) j)

end Converse

end MartChar

end InteractingSLE
