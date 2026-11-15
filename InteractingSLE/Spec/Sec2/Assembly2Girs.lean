/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Life
import InteractingSLE.Spec.Sec2.AddMarksMerge
import InteractingSLE.Spec.Sec2.OneForceLaw

/-!
# Theorem 2.2, existence: positive local horizons by Girsanov

Packet PROVE-SEC2-PATCH3. For a separated, ordered, non-threshold word `s`, along almost every
Brownian path there is a local solution from `s` with a positive horizon (`hasPosLife`), the input
`HasPosLife` of `Assembly2Life`. Proof (the source's local construction, Specification L486–L488):

* the marks of `s` at the driver form one group on one side (`s` is separated), of total weight
  `> −2`; the one-force-point evolution (PROVE-SEC2-ONE) with that weight, split into the coincident
  marks of the group (`IsSLEPathUpTo.splitR`, `splitL`), is a reference local evolution;
* it is modified on a null set to have every path continuous, in the usual augmentation
  (`IsSLEEvolutionUpTo.exists_continuous_modification`);
* the other marks are added by Girsanov (PROVE-SEC2-GIR2's `IsSLEEvolutionUpTo.exists_addMarks`)
  up to the first time `τ ≤ 1` one of them comes within `δ` of the driver (`hitTime`, an exact
  stopping time since every path is continuous), and `τ > 0` everywhere;
* under the new measure the driving process is a Brownian motion, so its path law is the Wiener
  law (`map_path_eq_map_path`), and almost every path drives a local solution up to `τ > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### Splitting a mark into coincident marks -/

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {w : ℝ≥0 → ℝ} {v : ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **Splitting a right mark** of weight `∑ ρ` at `0` into `m` coincident marks of weights `ρ`. -/
theorem splitR {xL : Fin nL → ℝ} {ρL : Fin nL → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {ρ1 : Fin 1 → ℝ}
    {m : ℕ} {ρm : Fin m → ℝ} (hsum : ρ1 0 = ∑ j, ρm j)
    (h : IsSLEPathUpTo a xL (fun _ : Fin 1 => 0) ρL ρ1 w vL (fun _ => v) b τ) :
    IsSLEPathUpTo a xL (fun _ : Fin m => 0) ρL ρm w vL (fun _ => v) b τ :=
  { w_zero := h.w_zero
    vL_zero := h.vL_zero
    vR_zero := fun _ => h.vR_zero 0
    continuousOn_w := h.continuousOn_w
    continuousOn_vL := h.continuousOn_vL
    continuousOn_vR := fun _ => h.continuousOn_vR 0
    antitone_vL := h.antitone_vL
    vL_le_w := h.vL_le_w
    w_le_vR := fun ht _ => h.w_le_vR ht 0
    monotone_vR := fun _ _ _ _ => le_rfl
    integrable_gapL := h.integrable_gapL
    integrable_gapR := fun ht _ => h.integrable_gapR ht 0
    w_eq := fun {t} ht => by
      rw [h.w_eq ht]
      congr 1
      have hint : ∀ j, IntervalIntegrable (fun s : ℝ => ρm j / (w s.toNNReal - v s.toNNReal))
          volume 0 t := fun j => by
        simpa only [div_eq_mul_inv] using (h.integrable_gapR ht 0).const_mul (ρm j)
      rw [← intervalIntegral.integral_finsetSum fun j _ => hint j, Fin.sum_univ_one, hsum]
      exact intervalIntegral.integral_congr fun s _ => by simp only [Finset.sum_div]
    vL_eq := h.vL_eq
    vR_eq := fun ht _ => h.vR_eq ht 0
    volume_collisionL := h.volume_collisionL
    volume_collisionR := fun _ => h.volume_collisionR 0
    not_threshold := fun {t} ht hthr => h.not_threshold ht (by
      unfold ForceWord.ThresholdCondition at hthr ⊢
      rcases hthr with hthr | hthr
      · exact Or.inl hthr
      · refine Or.inr ?_
        simp only [Finset.filter_const] at hthr ⊢
        split_ifs at hthr ⊢ with hv
        · rw [Fin.sum_univ_one, hsum]; exact hthr
        · simpa using hthr) }

/-- **Splitting a left mark** of weight `∑ ρ` at `0` into `m` coincident marks of weights `ρ`. -/
theorem splitL {xR : Fin nR → ℝ} {ρR : Fin nR → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ρ1 : Fin 1 → ℝ}
    {m : ℕ} {ρm : Fin m → ℝ} (hsum : ρ1 0 = ∑ j, ρm j)
    (h : IsSLEPathUpTo a (fun _ : Fin 1 => 0) xR ρ1 ρR w (fun _ => v) vR b τ) :
    IsSLEPathUpTo a (fun _ : Fin m => 0) xR ρm ρR w (fun _ => v) vR b τ :=
  { w_zero := h.w_zero
    vL_zero := fun _ => h.vL_zero 0
    vR_zero := h.vR_zero
    continuousOn_w := h.continuousOn_w
    continuousOn_vL := fun _ => h.continuousOn_vL 0
    continuousOn_vR := h.continuousOn_vR
    antitone_vL := fun _ _ _ _ => le_rfl
    vL_le_w := fun ht _ => h.vL_le_w ht 0
    w_le_vR := h.w_le_vR
    monotone_vR := h.monotone_vR
    integrable_gapL := fun ht _ => h.integrable_gapL ht 0
    integrable_gapR := h.integrable_gapR
    w_eq := fun {t} ht => by
      rw [h.w_eq ht]
      congr 2
      have hint : ∀ j, IntervalIntegrable (fun s : ℝ => ρm j / (w s.toNNReal - v s.toNNReal))
          volume 0 t := fun j => by
        simpa only [div_eq_mul_inv] using (h.integrable_gapL ht 0).const_mul (ρm j)
      rw [← intervalIntegral.integral_finsetSum fun j _ => hint j, Fin.sum_univ_one, hsum]
      exact intervalIntegral.integral_congr fun s _ => by simp only [Finset.sum_div]
    vL_eq := fun ht _ => h.vL_eq ht 0
    vR_eq := h.vR_eq
    volume_collisionL := fun _ => h.volume_collisionL 0
    volume_collisionR := h.volume_collisionR
    not_threshold := fun {t} ht hthr => h.not_threshold ht (by
      unfold ForceWord.ThresholdCondition at hthr ⊢
      rcases hthr with hthr | hthr
      · refine Or.inl ?_
        simp only [Finset.filter_const] at hthr ⊢
        split_ifs at hthr ⊢ with hv
        · rw [Fin.sum_univ_one, hsum]; exact hthr
        · simpa using hthr
      · exact Or.inr hthr) }

end IsSLEPathUpTo

namespace IsSLEEvolutionUpTo

variable {a : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W V B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem splitR {nL : ℕ} {xL : Fin nL → ℝ} {ρL : Fin nL → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {ρ1 : Fin 1 → ℝ}
    {m : ℕ} {ρm : Fin m → ℝ} (hsum : ρ1 0 = ∑ j, ρm j)
    (hE : IsSLEEvolutionUpTo a xL (fun _ : Fin 1 => 0) ρL ρ1 P 𝓕 W VL (fun _ => V) B ζ) :
    IsSLEEvolutionUpTo a xL (fun _ : Fin m => 0) ρL ρm P 𝓕 W VL (fun _ => V) B ζ :=
  ⟨hE.brownian, hE.adapted_W, hE.adapted_VL, fun _ => hE.adapted_VR 0,
    hE.ae_path.mono fun _ h => IsSLEPathUpTo.splitR hsum h⟩

theorem splitL {nR : ℕ} {xR : Fin nR → ℝ} {ρR : Fin nR → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {ρ1 : Fin 1 → ℝ}
    {m : ℕ} {ρm : Fin m → ℝ} (hsum : ρ1 0 = ∑ j, ρm j)
    (hE : IsSLEEvolutionUpTo a (fun _ : Fin 1 => 0) xR ρ1 ρR P 𝓕 W (fun _ => V) VR B ζ) :
    IsSLEEvolutionUpTo a (fun _ : Fin m => 0) xR ρm ρR P 𝓕 W (fun _ => V) VR B ζ :=
  ⟨hE.brownian, hE.adapted_W, fun _ => hE.adapted_VL 0, hE.adapted_VR,
    hE.ae_path.mono fun _ h => IsSLEPathUpTo.splitL hsum h⟩

/-! ### A modification with every path continuous -/

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

open Classical in
/-- Changing a process on a measurable null set keeps it adapted in the usual augmentation. -/
theorem adaptedBefore_ite_null {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 ζ X) {N : Set Ω}
    (hNm : MeasurableSet N) (hN0 : P N = 0) (c : ℝ) :
    AdaptedBefore (usualAugmentation 𝓕 P) ζ (fun t ω => if ω ∈ N then c else X t ω) := by
  intro t A hA
  have hNt : MeasurableSet[usualAugmentation 𝓕 P t] N :=
    Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ (if ω ∈ N then c else X t ω) ∈ A} =
      ({ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∩ Nᶜ) ∪
        ({ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ univ} ∩ (N ∩ {_ω | c ∈ A})) := by
    ext ω
    by_cases hω : ω ∈ N <;> simp [hω]
  rw [e]
  exact (((Ito.le_usualAugmentation 𝓕 P t) _ (hX t A hA)).inter hNt.compl).union
    (((Ito.le_usualAugmentation 𝓕 P t) _ (hX t univ MeasurableSet.univ)).inter
      (hNt.inter (MeasurableSet.const _)))

/-- **A modification with every path continuous**: a local evolution can be changed on a null set
so that every driver path is continuous before the lifetime and starts at `0`, in the usual
augmentation of its filtration. -/
theorem exists_continuous_modification
    (hE : IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ),
      IsSLEEvolutionUpTo a xL xR ρL ρR P (usualAugmentation 𝓕 P) W' VL' VR' B ζ ∧
      (∀ ω, ContinuousOn (W' · ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ ∀ ω, W' 0 ω = 0 := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hE.ae_path)
  refine ⟨fun t ω => if ω ∈ N then 0 else W t ω, fun i t ω => if ω ∈ N then xL i else VL i t ω,
    fun j t ω => if ω ∈ N then xR j else VR j t ω, ⟨Ito.isFilteredBrownianReal_usualAugmentation
      hE.brownian, adaptedBefore_ite_null hE.adapted_W hNm hN0 0,
      fun i => adaptedBefore_ite_null (hE.adapted_VL i) hNm hN0 (xL i),
      fun j => adaptedBefore_ite_null (hE.adapted_VR j) hNm hN0 (xR j), ?_⟩, fun ω => ?_,
      fun ω => ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    have hp : IsSLEPathUpTo a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) := by
      by_contra hc
      exact hω (hNsub hc)
    simp only [hω, ↓reduceIte]
    exact hp
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · have hp : IsSLEPathUpTo a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) := by
        by_contra hc
        exact hω (hNsub hc)
      simp only [hω, ↓reduceIte]
      exact hp.continuousOn_w
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · have hp : IsSLEPathUpTo a xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) := by
        by_contra hc
        exact hω (hNsub hc)
      simp only [hω, ↓reduceIte]
      exact hp.w_zero

end IsSLEEvolutionUpTo

namespace Assembly2

open Assembly

/-! ### The first time a gap reaches `δ` -/

section Hit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {K : Type*}

/-- The first time one of the processes `Y k` is `≤ δ` (`⊤` if never). -/
def hitTime (Y : K → ℝ≥0 → Ω → ℝ) (δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ∃ k, Y k t ω ≤ δ), (t : ℝ≥0∞)

variable {Y : K → ℝ≥0 → Ω → ℝ} {δ : ℝ}

theorem lt_of_lt_hitTime {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < hitTime Y δ ω) (k : K) :
    δ < Y k t ω := by
  by_contra h
  rw [not_lt] at h
  exact absurd (iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, Y k t ω ≤ δ) => (t : ℝ≥0∞)) t ⟨k, h⟩)
    (not_le.2 ht)

/-- The infimum is attained (the paths are continuous). -/
theorem hitTime_le_iff [Finite K] {ω : Ω} (hc : ∀ k, Continuous (Y k · ω)) {s : ℝ≥0} :
    hitTime Y δ ω ≤ s ↔ ∃ t ≤ s, ∃ k, Y k t ω ≤ δ := by
  set S := {t : ℝ≥0 | ∃ k, Y k t ω ≤ δ} with hS
  constructor
  · intro h
    have hne : S.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      have htop : hitTime Y δ ω = ⊤ := by
        refine le_antisymm le_top (le_iInf₂ fun t ht => ?_)
        exact absurd (show t ∈ S from ht) (by rw [hne]; exact notMem_empty t)
      rw [htop] at h
      exact absurd h (not_le.2 ENNReal.coe_lt_top)
    have hcl : IsClosed S := by
      have e : S = ⋃ k, {t : ℝ≥0 | Y k t ω ≤ δ} := by ext t; simp [hS]
      rw [e]
      exact isClosed_iUnion_of_finite fun k => isClosed_le (hc k) continuous_const
    have hmem := hcl.csInf_mem hne (OrderBot.bddBelow S)
    have hle : ((sInf S : ℝ≥0) : ℝ≥0∞) ≤ hitTime Y δ ω :=
      le_iInf₂ fun t ht => ENNReal.coe_le_coe.2 (csInf_le (OrderBot.bddBelow S) ht)
    exact ⟨sInf S, by exact_mod_cast hle.trans h, hmem⟩
  · rintro ⟨t, hts, k, hk⟩
    exact (iInf₂_le (f := fun (t : ℝ≥0) (_ : ∃ k, Y k t ω ≤ δ) => (t : ℝ≥0∞)) t ⟨k, hk⟩).trans
      (by exact_mod_cast hts)

theorem hitTime_pos [Finite K] {ω : Ω} (hc : ∀ k, Continuous (Y k · ω)) (h0 : ∀ k, δ < Y k 0 ω) :
    0 < hitTime Y δ ω := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ hitTime Y δ ω) with h | h
  · obtain ⟨t, ht, k, hk⟩ := (hitTime_le_iff (s := 0) hc).1 (by rw [← h]; rfl)
    rw [nonpos_iff_eq_zero.1 ht] at hk
    exact absurd hk (not_le.2 (h0 k))
  · exact h

theorem measurableSet_hitTime_le [Finite K] {𝓕 : Filtration ℝ≥0 mΩ} (hY : ∀ k t, Measurable[𝓕 t] (Y k t))
    (hc : ∀ k ω, Continuous (Y k · ω)) (s : ℝ≥0) :
    MeasurableSet[𝓕 s] {ω | hitTime Y δ ω ≤ s} := by
  have e : {ω | hitTime Y δ ω ≤ s} =
      (⋂ k, {ω | ∀ r ∈ Icc (0 : ℝ) s, δ < Y k r.toNNReal ω})ᶜ := by
    ext ω
    rw [mem_ofPred_eq, hitTime_le_iff (hc · ω), mem_compl_iff, mem_iInter]
    constructor
    · rintro ⟨t, hts, k, hk⟩ h
      have := h k (t : ℝ) ⟨t.coe_nonneg, by exact_mod_cast hts⟩
      rw [Real.toNNReal_coe] at this
      exact absurd hk (not_le.2 this)
    · intro h
      simp only [mem_ofPred_eq, not_forall, not_lt] at h
      obtain ⟨k, r, hr, hk⟩ := h
      refine ⟨r.toNNReal, ?_, k, hk⟩
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
  rw [e]
  refine (MeasurableSet.iInter fun k => ?_).compl
  exact OneForce.measurableSet_forall_Icc_lt (mα := 𝓕 s) s.coe_nonneg
    (fun r hr => (hY k _).mono (𝓕.mono (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2)) le_rfl)
    (fun ω => ((hc k ω).comp continuous_real_toNNReal).continuousOn) δ

end Hit

/-! ### Positive local horizons from a reference evolution, by Girsanov -/

section Girsanov

variable {a : ℝ} {nL nR kL kR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {s : MWord nL nR}

theorem measurable_pos_lifeMax :
    MeasurableSet {g : ℝ≥0 → ℝ | 0 < lifeMax a ρL ρR s (enc g)} :=
  measurableSet_lt measurable_const (measurable_lifeMax_left.comp measurable_enc)

/-- From a local evolution of `s` up to a positive time, almost every path of every pre-Brownian
motion has a local solution from `s` with a positive horizon (the path law is the Wiener law). -/
theorem ae_pos_lifeMax_of_evolutionUpTo (hsep : ∀ i j, s.1 i < s.2 j) {Ω₀ : Type*}
    {m₀ : MeasurableSpace Ω₀} {Q : Measure Ω₀} [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 m₀}
    {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ}
    {B' : ℝ≥0 → Ω₀ → ℝ} {τ : Ω₀ → ℝ≥0∞}
    (hE : IsSLEEvolutionUpTo a s.1 s.2 ρL ρR Q 𝓖 W VL VR B' τ) (hτ : ∀ ω, 0 < τ ω)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B₁ : ℝ≥0 → Ω → ℝ} (hB₁ : IsPreBrownianReal B₁ P)
    (hm₁ : Measurable fun ω (t : ℝ≥0) => B₁ t ω) :
    ∀ᵐ ω ∂P, 0 < lifeMax a ρL ρR s (enc (B₁ · ω)) := by
  have hBM := hE.brownian
  have hpos : ∀ᵐ ω ∂Q, 0 < lifeMax a ρL ρR s (enc (B' · ω)) := by
    filter_upwards [hE.ae_path, hBM.1.cont] with ω hp hc
    exact lt_of_lt_of_le (hτ ω) (le_lifeMax (mem_lSet_of_isSLEPathUpTo hsep hc hp le_rfl))
  have hBm' : ∀ t, Measurable (B' t) := fun t => (hBM.2.1 t).mono (𝓖.le t) le_rfl
  have hm' : Measurable fun ω (t : ℝ≥0) => B' t ω := measurable_pi_iff.2 hBm'
  have hlaw := map_path_eq_map_path hB₁ hBM.1.toIsPreBrownianReal hm₁ hm'
  have hG := measurable_pos_lifeMax (a := a) (ρL := ρL) (ρR := ρR) (s := s)
  have h1 : ∀ᵐ g ∂(Q.map fun ω (t : ℝ≥0) => B' t ω), 0 < lifeMax a ρL ρR s (enc g) :=
    (ae_map_iff hm'.aemeasurable hG).2 hpos
  rw [← hlaw] at h1
  exact ae_of_ae_map hm₁.aemeasurable h1

/-- **Positive local horizons along almost every Brownian path, from a reference evolution.** Let
`eL`, `eR` enumerate the marks of the good word `s` at the driver, and let a local evolution of
this reference sub-word with lifetime `∞` be given on some filtered probability space. Then along
almost every path of every pre-Brownian motion there is a local solution from `s` with a positive
horizon. -/
theorem ae_pos_lifeMax_of_reference (ha : 0 < a) (hs : GoodWord ρL ρR s)
    {eL : Fin kL → Fin nL} {eR : Fin kR → Fin nR} (heL : Function.Injective eL)
    (heR : Function.Injective eR) (hcL : ∀ i, (∃ j, eL j = i) ↔ s.1 i = 0)
    (hcR : ∀ i, (∃ j, eR j = i) ↔ s.2 i = 0)
    {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 m₀} {W : ℝ≥0 → Ω₀ → ℝ} {VLr : Fin kL → ℝ≥0 → Ω₀ → ℝ}
    {VRr : Fin kR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ}
    (hE : IsSLEEvolutionUpTo a (fun j => s.1 (eL j)) (fun j => s.2 (eR j)) (fun j => ρL (eL j))
      (fun j => ρR (eR j)) P₀ 𝓕₀ W VLr VRr B (fun _ => ⊤))
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {B₁ : ℝ≥0 → Ω → ℝ} (hB₁ : IsPreBrownianReal B₁ P)
    (hm₁ : Measurable fun ω (t : ℝ≥0) => B₁ t ω) :
    ∀ᵐ ω ∂P, 0 < lifeMax a ρL ρR s (enc (B₁ · ω)) := by
  classical
  obtain ⟨W', VL', VR', hE', hW'c, hW'0⟩ := hE.exists_continuous_modification
  set 𝓤 := usualAugmentation 𝓕₀ P₀ with h𝓤
  have hWc : ∀ ω, Continuous (W' · ω) := fun ω => by
    have := hW'c ω
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top
    rw [e] at this
    exact continuousOn_univ.1 this
  have hWa : ∀ t, Measurable[𝓤 t] (W' t) := fun t A hA => by
    have := hE'.adapted_W t A hA
    simp only [ENNReal.coe_lt_top, true_and] at this
    exact this
  -- the gap level
  set f : Fin nL ⊕ Fin nR → ℝ := Sum.elim (fun i => if s.1 i = 0 then 1 else -s.1 i)
    (fun j => if s.2 j = 0 then 1 else s.2 j) with hf
  have hfpos : ∀ k, 0 < f k := by
    rintro (i | j)
    · simp only [hf, Sum.elim_inl]
      split_ifs with h
      · exact one_pos
      · exact neg_pos.2 (lt_of_le_of_ne (hs.2.1.2.1 i) h)
    · simp only [hf, Sum.elim_inr]
      split_ifs with h
      · exact one_pos
      · exact lt_of_le_of_ne (hs.2.1.2.2.2 j) (Ne.symm h)
  obtain ⟨δ, hδ, hδf⟩ := exists_pos_forall_lt f hfpos
  -- the gaps of the added marks
  set Y : Fin nL ⊕ Fin nR → ℝ≥0 → Ω₀ → ℝ := Sum.elim
    (fun i t ω => if s.1 i = 0 then δ + 1 else W' t ω - leftMark δ (s.1 i) (fun _ => ⊤) W' t ω)
    (fun j t ω => if s.2 j = 0 then δ + 1 else rightMark δ (s.2 j) (fun _ => ⊤) W' t ω - W' t ω)
    with hY
  have hWc' : ∀ ω, ContinuousOn (fun t => W' t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < (fun _ => ⊤) ω} :=
    fun ω => (hWc ω).continuousOn
  have hLc : ∀ (y : ℝ) ω, Continuous fun t => leftMark δ y (fun _ => ⊤) W' t ω := fun y ω => by
    have := (markFlow_eq_of_continuousOn (W := W') (ζ := fun _ => ⊤) (y := y)
      (lipschitzWith_leftMarkDrift hδ) (abs_leftMarkDrift_le hδ) (hWc' ω)).1
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) < (fun (_ : Ω₀) => (⊤ : ℝ≥0∞)) ω} = univ :=
      eq_univ_of_forall fun t => ENNReal.coe_lt_top
    rw [e] at this
    exact continuousOn_univ.1 this
  have hRc : ∀ (y : ℝ) ω, Continuous fun t => rightMark δ y (fun _ => ⊤) W' t ω := fun y ω => by
    have := (markFlow_eq_of_continuousOn (W := W') (ζ := fun _ => ⊤) (y := y)
      (lipschitzWith_rightMarkDrift hδ) (abs_rightMarkDrift_le hδ) (hWc' ω)).1
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) < (fun (_ : Ω₀) => (⊤ : ℝ≥0∞)) ω} = univ :=
      eq_univ_of_forall fun t => ENNReal.coe_lt_top
    rw [e] at this
    exact continuousOn_univ.1 this
  have hYc : ∀ k ω, Continuous (Y k · ω) := by
    rintro (i | j) ω
    · simp only [hY, Sum.elim_inl]
      split_ifs
      · exact continuous_const
      · exact (hWc ω).sub (hLc _ ω)
    · simp only [hY, Sum.elim_inr]
      split_ifs
      · exact continuous_const
      · exact (hRc _ ω).sub (hWc ω)
  have hWad : AdaptedBefore 𝓤 (fun _ => ⊤) W' := hE'.adapted_W
  have hmark : ∀ {X : ℝ≥0 → Ω₀ → ℝ}, AdaptedBefore 𝓤 (fun _ => ⊤) X → ∀ t,
      Measurable[𝓤 t] (X t) := fun {X} hX t A hA => by
    have := hX t A hA
    simp only [ENNReal.coe_lt_top, true_and] at this
    exact this
  have hYm : ∀ k t, Measurable[𝓤 t] (Y k t) := by
    rintro (i | j) t
    · simp only [hY, Sum.elim_inl]
      split_ifs
      · exact measurable_const
      · exact (hWa t).sub (hmark (adaptedBefore_leftMark hδ _ hWad) t)
    · simp only [hY, Sum.elim_inr]
      split_ifs
      · exact measurable_const
      · exact (hmark (adaptedBefore_rightMark hδ _ hWad) t).sub (hWa t)
  have hY0 : ∀ k ω, δ < Y k 0 ω := by
    rintro (i | j) ω
    · simp only [hY, Sum.elim_inl]
      split_ifs with h
      · linarith
      · rw [hW'0 ω, leftMark, markFlow_zero, zero_sub]
        have := hδf (Sum.inl i)
        simpa only [hf, Sum.elim_inl, h, ↓reduceIte] using this
    · simp only [hY, Sum.elim_inr]
      split_ifs with h
      · linarith
      · rw [hW'0 ω, rightMark, markFlow_zero, sub_zero]
        have := hδf (Sum.inr j)
        simpa only [hf, Sum.elim_inr, h, ↓reduceIte] using this
  -- the stopping time
  set τ : Ω₀ → ℝ≥0∞ := fun ω => min (hitTime Y δ ω) ((1 : ℝ≥0) : ℝ≥0∞) with hτdef
  have hτ : ∀ u : ℝ≥0, MeasurableSet[𝓤 u] {ω | τ ω ≤ u} := fun u => by
    have e : {ω | τ ω ≤ u} = {ω | hitTime Y δ ω ≤ u} ∪ {_ω | ((1 : ℝ≥0) : ℝ≥0∞) ≤ u} := by
      ext ω; simp only [hτdef, mem_ofPred_eq, mem_union, min_le_iff]
    rw [e]
    exact (measurableSet_hitTime_le hYm hYc u).union (MeasurableSet.const _)
  have hτpos : ∀ ω, 0 < τ ω := fun ω =>
    lt_min (hitTime_pos (hYc · ω) (hY0 · ω)) (by exact_mod_cast one_pos)
  have hgap : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < τ ω → ∀ k, δ < Y k t ω := fun ω t ht k =>
    lt_of_lt_hitTime (lt_of_lt_of_le ht (min_le_left _ _)) k
  have hgapL : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ i, (∀ j, eL j ≠ i) →
      δ ≤ W' t ω - leftMark δ (s.1 i) (fun _ => ⊤) W' t ω := ae_of_all _ fun ω t ht i hi => by
    have hne : s.1 i ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := (hcL i).2 h0
      exact hi j hj
    have := hgap ω t ht (Sum.inl i)
    simp only [hY, Sum.elim_inl, hne, ↓reduceIte] at this
    exact this.le
  have hgapR : ∀ᵐ ω ∂P₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ i, (∀ j, eR j ≠ i) →
      δ ≤ rightMark δ (s.2 i) (fun _ => ⊤) W' t ω - W' t ω := ae_of_all _ fun ω t ht i hi => by
    have hne : s.2 i ≠ 0 := fun h0 => by
      obtain ⟨j, hj⟩ := (hcR i).2 h0
      exact hi j hj
    have := hgap ω t ht (Sum.inr i)
    simp only [hY, Sum.elim_inr, hne, ↓reduceIte] at this
    exact this.le
  -- Girsanov
  obtain ⟨hQ, hEQ⟩ := hE'.exists_addMarks ha hs.2.1 heL heR hδ hτ (fun _ => le_top)
    (fun ω => min_le_right _ _) hgapL hgapR
  have hQp := hQ.isProb
  exact ae_pos_lifeMax_of_evolutionUpTo hs.1 hEQ hτpos hB₁ hm₁

end Girsanov

/-! ### The reference evolutions and positive horizons for every good word -/

section Reference

variable {a : ℝ}

/-- The one-force-point evolution (weight `ρ > −2` at `0⁺`), split into `m` coincident right
marks. -/
theorem exists_reference_right (ha : 0 < a) {ρ : ℝ} (hρ : -2 < ρ) {m : ℕ} {ρm : Fin m → ℝ}
    (hsum : ρ = ∑ j, ρm j) (xL0 ρL0 : Fin 0 → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ)
      (VR : Fin m → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsSLEEvolutionUpTo a xL0 (fun _ : Fin m => 0) ρL0 ρm P 𝓕 W VL VR B (fun _ => ⊤) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, hBc, hB0⟩ := OneForce.exists_filteredBrownian
  have h1 := OneForce.isIntegratedSLEEvolution_right ha (xL := xL0) (xR := fun _ : Fin 1 => 0)
    (ρL := ρL0) (ρR := fun _ : Fin 1 => ρ) le_rfl hB hBc hB0 (fun i => i.elim0)
  have hc : 0 < (ρ + 2) / a := div_pos (by linarith) ha
  have hζ : OneForce.rightζ a ((fun _ : Fin 1 => (0 : ℝ)) 0) ((fun _ : Fin 1 => ρ) 0) B =
      fun _ => ⊤ := funext fun ω => OneForce.oneζ_of_pos hc ω
  rw [hζ] at h1
  exact ⟨Ω, mΩ, P, hP, 𝓕, _, _, _, B,
    IsSLEEvolutionUpTo.splitR (ρ1 := fun _ => ρ) hsum h1.isSLEEvolutionUpTo⟩

/-- The one-force-point evolution (weight `ρ > −2` at `0⁻`), split into `m` coincident left
marks. -/
theorem exists_reference_left (ha : 0 < a) {ρ : ℝ} (hρ : -2 < ρ) {m : ℕ} {ρm : Fin m → ℝ}
    (hsum : ρ = ∑ j, ρm j) (xR0 ρR0 : Fin 0 → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin m → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
      IsSLEEvolutionUpTo a (fun _ : Fin m => 0) xR0 ρm ρR0 P 𝓕 W VL VR B (fun _ => ⊤) := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, B, hB, hBc, hB0⟩ := OneForce.exists_filteredBrownian
  have h1 := OneForce.isIntegratedSLEEvolution_left ha (xL := fun _ : Fin 1 => 0) (xR := xR0)
    (ρL := fun _ : Fin 1 => ρ) (ρR := ρR0) le_rfl hB hBc hB0 (fun i => i.elim0)
  have hc : 0 < (ρ + 2) / a := div_pos (by linarith) ha
  have hζ : OneForce.leftζ a ((fun _ : Fin 1 => (0 : ℝ)) 0) ((fun _ : Fin 1 => ρ) 0) B =
      fun _ => ⊤ := funext fun ω => OneForce.oneζ_of_pos hc ω
  rw [hζ] at h1
  exact ⟨Ω, mΩ, P, hP, 𝓕, _, _, _, B,
    IsSLEEvolutionUpTo.splitL (ρ1 := fun _ => ρ) hsum h1.isSLEEvolutionUpTo⟩

/-- The marks of a word at `0`, enumerated. -/
theorem exists_enum_zero {n : ℕ} (x : Fin n → ℝ) :
    ∃ (k : ℕ) (e : Fin k → Fin n), Function.Injective e ∧ (∀ i, (∃ j, e j = i) ↔ x i = 0) ∧
      ∀ ρ : Fin n → ℝ, ∑ j, ρ (e j) = ∑ i ∈ Finset.univ.filter (fun i => x i = 0), ρ i := by
  classical
  set F := Finset.univ.filter (fun i => x i = 0) with hF
  refine ⟨F.card, fun j => (F.orderIsoOfFin rfl j : Fin n), fun j j' h =>
    (F.orderIsoOfFin rfl).injective (Subtype.ext h), fun i => ⟨?_, fun hi => ?_⟩, fun ρ => ?_⟩
  · rintro ⟨j, rfl⟩
    exact (Finset.mem_filter.1 (F.orderIsoOfFin rfl j).2).2
  · refine ⟨(F.orderIsoOfFin rfl).symm ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩, ?_⟩
    simp only [OrderIso.apply_symm_apply]
  · rw [← Finset.sum_coe_sort F ρ]
    exact Fintype.sum_equiv (F.orderIsoOfFin rfl).toEquiv _ _ fun j => rfl

variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {s : MWord nL nR}

/-- **Positive local horizons for every good word** (Claim A): along almost every path of every
pre-Brownian motion there is a local solution from `s` with a positive horizon. -/
theorem ae_pos_lifeMax (ha : 0 < a) (hs : GoodWord ρL ρR s) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {B₁ : ℝ≥0 → Ω → ℝ} (hB₁ : IsPreBrownianReal B₁ P)
    (hm₁ : Measurable fun ω (t : ℝ≥0) => B₁ t ω) :
    ∀ᵐ ω ∂P, 0 < lifeMax a ρL ρR s (enc (B₁ · ω)) := by
  classical
  have hnt := hs.2.2
  unfold ForceWord.ThresholdCondition at hnt
  rw [not_or, not_le, not_le] at hnt
  obtain ⟨kL, eL, heL, hcL, hsL⟩ := exists_enum_zero s.1
  obtain ⟨kR, eR, heR, hcR, hsR⟩ := exists_enum_zero s.2
  by_cases hL : ∀ i, s.1 i ≠ 0
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W, VL, VR, B, hE⟩ := exists_reference_right ha
      (ρ := ∑ j, ρR (eR j)) (by rw [hsR]; exact hnt.2) (ρm := fun j => ρR (eR j)) rfl
      (fun j : Fin 0 => s.1 (Fin.elim0 j)) (fun j => ρL (Fin.elim0 j))
    have e : (fun j => s.2 (eR j)) = fun _ => (0 : ℝ) := funext fun j => (hcR (eR j)).1 ⟨j, rfl⟩
    rw [← e] at hE
    exact ae_pos_lifeMax_of_reference ha hs (eL := Fin.elim0) (eR := eR) (fun j => j.elim0) heR
      (fun i => ⟨fun ⟨j, _⟩ => j.elim0, fun h => absurd h (hL i)⟩) hcR hE hB₁ hm₁
  · simp only [ne_eq, not_forall, not_not] at hL
    obtain ⟨i₀, hi₀⟩ := hL
    have hR : ∀ j, s.2 j ≠ 0 := fun j h => by
      have := hs.1 i₀ j
      rw [hi₀, h] at this
      exact lt_irrefl 0 this
    obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W, VL, VR, B, hE⟩ := exists_reference_left ha
      (ρ := ∑ j, ρL (eL j)) (by rw [hsL]; exact hnt.1) (ρm := fun j => ρL (eL j)) rfl
      (fun j : Fin 0 => s.2 (Fin.elim0 j)) (fun j => ρR (Fin.elim0 j))
    have e : (fun j => s.1 (eL j)) = fun _ => (0 : ℝ) := funext fun j => (hcL (eL j)).1 ⟨j, rfl⟩
    rw [← e] at hE
    exact ae_pos_lifeMax_of_reference ha hs (eL := eL) (eR := Fin.elim0) heL (fun j => j.elim0)
      hcL (fun i => ⟨fun ⟨j, _⟩ => j.elim0, fun h => absurd h (hR i)⟩) hE hB₁ hm₁

/-- **`HasPosLife` holds for every pre-Brownian motion.** -/
theorem hasPosLife (ha : 0 < a) {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : Measurable fun ω (t : ℝ≥0) => B t ω) : HasPosLife a ρL ρR P B :=
  fun _ hs => ae_pos_lifeMax ha hs hB hm

end Reference

end Assembly2

end Sec2

end InteractingSLE
