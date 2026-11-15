/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OBranch
import InteractingSLE.Spec.ZhanGT4.FrozenMeas
import InteractingSLE.Spec.Sec7.Aux57

/-!
# Lemma 7.1's inherited branch is measurable: the named input (N)

Packet PROVE-LEMMA71O. Supplement §2.3: "For random configurations, normalized conformal maps and the selected logarithm
must be measurable functions of the retained labels." The integer of the inherited branch
(`Lemma71O.exists_isPocketBranch`) is pinned, for every chart point `ξ_j = −1/(j + 1)` and stopping time `j`, by the
canonical logarithm `Im log g′` of the left wall's prefix hull `fill β([0, j])` read at `σ(β, α)`-measurable points of
the pocket approaching `ξ_j` in the chart (`exists_measurable_chart_approach`). The prefix hulls are observed through
their dyadic hits (`isDyadicHitMeasurable_image_Icc`), so the pins are measurable
(`Restart.measurable_indicator_canonDerivLog`); for large `j` the landing time at `ξ_j` is below `j`, so the pins
converge to `2πn`.

* **`pocketBranchStatement`**: `Lemma71N.PocketBranchStatement` (named input (N) of PROVE-LEMMA71N) is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71O

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open Lemma71N (IsPocketFrame IsPocketBranch)

/-! ### Measurable prefixes and approaches -/

section Meas

variable {Ω : Type*} [m : MeasurableSpace Ω]

/-- **The prefix of a continuous random curve is observed through its dyadic hits.** -/
theorem isDyadicHitMeasurable_image_Icc {η : Ω → ℝ≥0 → ℂ} (hc : ∀ ω, Continuous (η ω))
    (hm : ∀ t, Measurable[m] fun ω => η ω t) (Q : ℝ≥0) :
    @Restart.IsDyadicHitMeasurable Ω m fun ω => η ω '' Icc 0 Q := by
  set A : Set ℂ := (fun t : ℝ≥0 => ((t : ℝ) : ℂ)) '' Icc 0 Q with hA
  set ψ : Ω → ℂ → ℂ := fun ω z => η ω z.re.toNNReal with hψ
  have himg : ∀ ω, ψ ω '' A = η ω '' Icc 0 Q := fun ω => by
    rw [hA, image_image]
    refine image_congr fun t _ => ?_
    simp [hψ]
  have h := ZhanGT4.isDyadicHitMeasurable_closure_image (G := (univ : Set Ω)) MeasurableSet.univ (A := A) (ψ := ψ)
    (fun z _ => by rw [indicator_univ]; exact hm _)
    (fun ω _ => ((hc ω).comp (continuous_real_toNNReal.comp continuous_re)).continuousOn)
  intro n k
  have h' := h n k
  convert h' using 4 with ω
  dsimp only
  split_ifs with hω
  · rw [himg, (isCompact_Icc.image (hc ω)).isClosed.closure_eq]
  · exact absurd (mem_univ ω) hω

/-- **A measurable approach to a real chart point**: through a dense sequence, points of the chart domains whose chart
values tend to `ξ` within `ℍ`, with measurable indices. -/
theorem exists_measurable_chart_approach {C : Ω → Set ℂ} {c : Ω → Chart} (hconf : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ ω, ((c ω).dom : Set ℂ) = C ω) (hCm : ∀ z, MeasurableSet[m] {ω | z ∈ C ω})
    (hfm : ∀ z, Measurable[m] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) {e : ℕ → ℂ}
    (he : DenseRange e) (ξ : ℝ) :
    ∃ N : ℕ → Ω → ℕ, (∀ k, Measurable[m] (N k)) ∧ (∀ k ω, e (N k ω) ∈ C ω) ∧
      ∀ ω, Tendsto (fun k => (c ω).1 (e (N k ω))) atTop (𝓝[H] (ξ : ℂ)) := by
  classical
  set y : ℕ → ℂ := fun k => (ξ : ℂ) + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I with hy
  have hyH : ∀ k, y k ∈ H := fun k => by
    show 0 < (y k).im
    simp only [hy, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
    positivity
  have hex : ∀ (k : ℕ) (ω : Ω), ∃ j, e j ∈ C ω ∧ dist ((c ω).1 (e j)) (y k) < 1 / ((k : ℝ) + 1) := by
    intro k ω
    have hw : (c ω).2.1 (y k) ∈ C ω := by rw [← hdom]; exact (hconf ω).inv_mem_dom (hyH k)
    have hco : ContinuousOn (c ω).1 (C ω) := by rw [← hdom]; exact (hconf ω).differentiableOn_fwd.continuousOn
    have hCo : IsOpen (C ω) := by rw [← hdom]; exact (c ω).dom.isOpen
    have hU := hco.isOpen_inter_preimage hCo (isOpen_ball (x := y k) (ε := 1 / ((k : ℝ) + 1)))
    obtain ⟨j, hj⟩ := he.exists_mem_open hU ⟨_, hw, by
      rw [mem_preimage, (hconf ω).2.2 _ (hyH k)]; exact mem_ball_self (by positivity)⟩
    exact ⟨j, hj.1, hj.2⟩
  refine ⟨fun k ω => Nat.find (hex k ω), fun k => ?_, fun k ω => (Nat.find_spec (hex k ω)).1, fun ω => ?_⟩
  · refine measurable_find (hex k) fun j => ?_
    have heq : {ω | e j ∈ C ω ∧ dist ((c ω).1 (e j)) (y k) < 1 / ((k : ℝ) + 1)} =
        {ω | e j ∈ C ω} ∩ {ω | dist (({ω | e j ∈ (c ω).dom}.indicator fun ω => (c ω).1 (e j)) ω) (y k) <
          1 / ((k : ℝ) + 1)} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rwa [indicator_of_mem (show ω ∈ {ω | e j ∈ (c ω).dom} by
          show e j ∈ ((c ω).dom : Set ℂ); rw [hdom]; exact h1)]
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rwa [indicator_of_mem (show ω ∈ {ω | e j ∈ (c ω).dom} by
          show e j ∈ ((c ω).dom : Set ℂ); rw [hdom]; exact h1)] at h2
    rw [heq]
    exact (hCm (e j)).inter (measurableSet_lt ((hfm (e j)).dist measurable_const) measurable_const)
  · have h0 : Tendsto (fun k : ℕ => 2 * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun k => dist_nonneg) (fun k => ?_) h0)
      · have h1 := (Nat.find_spec (hex k ω)).2
        have h2 : dist (y k) (ξ : ℂ) = 1 / ((k : ℝ) + 1) := by
          rw [hy, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc dist ((c ω).1 (e (Nat.find (hex k ω)))) (ξ : ℂ)
            ≤ dist ((c ω).1 (e (Nat.find (hex k ω)))) (y k) + dist (y k) (ξ : ℂ) := dist_triangle _ _ _
          _ ≤ 2 * (1 / ((k : ℝ) + 1)) := by rw [h2]; linarith
    · have hmem := (Nat.find_spec (hex k ω)).1
      exact (hconf ω).fwd_mem (by rw [← SetLike.mem_coe, hdom]; exact hmem)

/-- **The canonical logarithm of a prefix hull is the Loewner logarithm.** -/
theorem canonDerivLog_eqOn_logDerivFwd {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} (htr : IsGeneratingTrace W ⊤ η)
    (hW : Continuous W) (hW0 : W 0 = 0) (q : ℝ≥0) :
    EqOn (Restart.canonDerivLog (fillH (η '' Icc 0 q))) (logDerivFwd (fun r : ℝ => W r.toNNReal) q)
      (H \ fillH (η '' Icc 0 q)) := by
  have hg : IsGeneratingTrace W ⊤ (fun t => η t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  obtain ⟨κ, hA, hgA, hLA⟩ := ReverseArc.exists_physChart hg hW.continuousOn hW0 (WithTop.coe_lt_top q)
  simp only [Complex.ofReal_zero, sub_zero] at hgA hLA
  have h₁ := (Restart.isCanonicalDerivLog_canonDerivLog hA).congr hA
    (IsMapOut.eqOn hA (ConformalImage.isMapOut_mapOut hA) hgA)
  exact Restart.IsCanonicalDerivLog.eqOn h₁ hLA hA hgA

/-- A measurable index into a sequence of measurable functions. -/
theorem measurable_comp_index {β : Type*} [MeasurableSpace β] {F : ℕ → Ω → β} (hF : ∀ i, Measurable (F i))
    {N : Ω → ℕ} (hN : Measurable N) : Measurable fun ω => F (N ω) ω := by
  have h : Measurable fun p : Ω × ℕ => F p.2 p.1 := measurable_from_prod_countable_left fun i => hF i
  exact h.comp (measurable_id.prodMk hN)

/-- The floor of a double `limsup` of measurable functions is measurable. -/
theorem measurable_floor_limsup_limsup {X : ℕ → ℕ → Ω → ℝ} (hX : ∀ j k, Measurable (X j k)) (d : ℝ) :
    Measurable fun ω => ⌊limsup (fun j => limsup (fun k => X j k ω) atTop) atTop / d + 1 / 2⌋ :=
  Int.measurable_floor.comp (((Measurable.limsup fun j => Measurable.limsup fun k => hX j k).div_const _).add_const _)

end Meas

/-! ### The named input (N) -/

section Named

open MartChar Lemma71M Lemma71E Lemma71D Coupling Lemma71G PocketFrame

/-- **Named input (N) of PROVE-LEMMA71N, proved**: on every pocket construction over a three-curve space there is a
`σ(β, α)`-measurable branch shift that is almost surely the inherited branch (supplement §2.3, the deterministic
normalization lemma (2) and its measurability). -/
theorem pocketBranchStatement : Lemma71N.PocketBranchStatement.{u} := by
  intro κ _ _ θ₁ θ₂ a b _ _ _ _ Ω mΩ P _ h u₀ β α γ ζβ ζα ζγ hS C c γ' hpc
  set m₀ : MeasurableSpace Ω := MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance with hm₀
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, -, hL, -⟩ := hpc'
  have hβc : ∀ ω, Continuous (β ω) := hβ62.1
  have hβ0 : ∀ ω, β ω 0 = 0 := hβ62.2.1
  have hβm : ∀ t, Measurable[m₀] fun ω => β ω t := fun t =>
    (measurable_pi_apply t).comp (measurable_fst.comp (comap_measurable (fun ω => (β ω, α ω))))
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hCmem : ∀ z, MeasurableSet[m₀] {ω | z ∈ C ω} := fun z =>
    @Lemma71E.measurableSet_mem_of_closedBall Ω m₀ C hCo hCm z
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set ξ : ℕ → ℝ := fun j => -(1 / ((j : ℝ) + 1)) with hξdef
  have hN := fun j => @exists_measurable_chart_approach Ω m₀ C c hconf hdom hCmem hfm e he (ξ j)
  choose N hNm hNC hNt using hN
  set K : ℕ → Ω → Set ℂ := fun j ω => β ω '' Icc 0 (j : ℝ≥0) with hKdef
  have hKm : ∀ j, @Restart.IsDyadicHitMeasurable Ω m₀ (K j) := fun j =>
    @isDyadicHitMeasurable_image_Icc Ω m₀ β hβc hβm j
  have hKc : ∀ j ω, IsCompact (K j ω) := fun j ω => isCompact_Icc.image (hβc ω)
  have hKp : ∀ j ω, IsPreconnected (K j ω ∪ Restart.lowerHalf) := fun j ω =>
    Restart.isPreconnected_image_union_lowerHalf (hβc ω).continuousOn (by rw [hβ0 ω]; simp)
  set F : ℕ → ℕ → Ω → ℂ := fun j i => {ω | e i ∈ H \ fillH (K j ω)}.indicator fun ω =>
    Restart.canonDerivLog (fillH (K j ω)) (e i) with hFdef
  have hFm : ∀ j i, Measurable[m₀] (F j i) := fun j i =>
    @Restart.measurable_indicator_canonDerivLog Ω m₀ (K j) (hKm j) (hKc j) (hKp j) (e i)
  set X : ℕ → ℕ → Ω → ℝ := fun j k ω => (F j (N j k ω) ω).im - (c ω).2.2 (e (N j k ω)) with hXdef
  have hXm : ∀ j k, Measurable[m₀] (X j k) := by
    intro j k
    have h1 := @measurable_comp_index Ω m₀ ℂ _ (F j) (hFm j) (N j k) (hNm j k)
    have h2 := @Lemma71E.measurable_at_seq Ω ℝ m₀ _ _ (fun ω => ((c ω).dom : Set ℂ)) (fun ω z => (c ω).2.2 z) e
      (N j k) (hNm j k) (fun ω => by rw [hdom]; exact hNC j k ω) hlm
    exact (Complex.measurable_im.comp h1).sub h2
  set Y : ℕ → Ω → ℝ := fun j ω => limsup (fun k => X j k ω) atTop with hYdef
  set Z : Ω → ℝ := fun ω => limsup (fun j => Y j ω) atTop with hZdef
  refine ⟨fun ω => ⌊Z ω / (2 * π) + 1 / 2⌋, @measurable_floor_limsup_limsup Ω m₀ X hXm (2 * π), ?_⟩
  clear hXm hFm hKm hNm hCmem hβm hm₀
  clear m₀
  filter_upwards [Lemma71N.ae_exists_isPocketFrame hS hpc] with ω hω
  obtain ⟨Ψ, a', b', hF⟩ := hω
  obtain ⟨L, hLd, hLl⟩ := hL ω
  obtain ⟨n₀, hn₀⟩ := exists_isPocketBranch hF hLd hLl
  by_cases hex : ∃ Wβ Wα : ℝ≥0 → ℝ, IsGeneratingTrace Wβ ⊤ (β ω) ∧ IsGeneratingTrace Wα ⊤ (α ω)
  swap
  · exact fun Wβ Wα h₁ h₂ => absurd ⟨Wβ, Wα, h₁, h₂⟩ hex
  obtain ⟨Wβ, Wα, htrβ, htrα⟩ := hex
  have hWβ := continuous_of_isGeneratingTrace_top htrβ
  have hWβ0 : Wβ 0 = 0 := SideHeight.w_zero_of_isGeneratingTrace htrβ (by simp)
  obtain ⟨sa, hsa⟩ := exists_land_zero_eq hF
  set Q₀ : ℕ := ⌈(sa : ℝ)⌉₊ + 1 with hQ₀
  have hsaQ₀ : sa < (Q₀ : ℝ≥0) := by
    have h1 : (sa : ℝ) ≤ ⌈(sa : ℝ)⌉₊ := Nat.le_ceil _
    have h2 : (sa : ℝ) < (Q₀ : ℝ) := by rw [hQ₀]; push_cast; linarith
    exact_mod_cast h2
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hF.hβ hsaQ₀
  have hξt : Tendsto ξ atTop (𝓝 0) := by
    have : Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) atTop (𝓝 (-(0 : ℝ))) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
    rw [neg_zero] at this
    exact this
  have hlt : Tendsto (fun j => land (c ω) (ξ j)) atTop (𝓝 (land (c ω) 0)) := by
    have := ((continuous_land_ofReal hF).tendsto 0).comp hξt
    rw [Complex.ofReal_zero] at this
    exact this
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hlt (ball_mem_nhds _ hρ))
  have hY : ∀ j ≥ max J Q₀, Y j ω = 2 * π * n₀ := by
    intro j hj
    have hξj : ξ j < 0 := by simp only [hξdef, Left.neg_neg_iff]; positivity
    obtain ⟨s, -, -, hs⟩ := land_ofReal_neg hF hξj
    have hsQ : s < (j : ℝ≥0) := by
      have hsQ₀ : s < (Q₀ : ℝ≥0) := by
        by_contra hle
        refine hball s (not_lt.1 hle) ?_
        rw [← hs, ← hsa]
        exact hJ j (le_of_max_le_left hj)
      exact hsQ₀.trans_le (by exact_mod_cast le_of_max_le_right hj)
    have hland : Tendsto (c ω).2.1 (𝓝[H] (ξ j : ℂ)) (𝓝 (β ω s)) :=
      hs ▸ tendsto_land hF (mem_Hbar_of_im_eq_zero (by simp))
    have hbr := (hn₀ Wβ Wα htrβ htrα (ξ j) s j hsQ).1 hξj hland
    have hcomp := hbr.comp (hNt j ω)
    have hinv : ∀ k, (c ω).2.1 ((c ω).1 (e (N j k ω))) = e (N j k ω) := fun k =>
      (hconf ω).inv_fwd (by rw [← SetLike.mem_coe, hdom]; exact hNC j k ω)
    have hX : ∀ k, X j k ω = (logDerivFwd (fun r : ℝ => Wβ r.toNNReal) ((j : ℝ≥0) : ℝ) (e (N j k ω))).im -
        (c ω).2.2 (e (N j k ω)) := by
      intro k
      have hzK : e (N j k ω) ∈ H \ fillH (K j ω) :=
        dom_subset_H_diff_fillH htrβ (hdom ω) (subset_H_diff_fwdHull_left hF htrβ) j
          (by rw [hdom]; exact hNC j k ω)
      simp only [hXdef, hFdef]
      rw [indicator_of_mem (show ω ∈ {ω' | e (N j k ω) ∈ H \ fillH (K j ω')} from hzK),
        canonDerivLog_eqOn_logDerivFwd htrβ hWβ hWβ0 j hzK]
    have hXt : Tendsto (fun k => X j k ω) atTop (𝓝 (2 * π * n₀)) := by
      have h' := (tendsto_const_nhds (x := 2 * π * (n₀ : ℝ))).sub hcomp
      rw [sub_zero] at h'
      refine h'.congr fun k => ?_
      simp only [Function.comp_apply, hinv, hX]
      ring
    exact hXt.limsup_eq
  have hZ : Z ω = 2 * π * n₀ := by
    show limsup (fun j => Y j ω) atTop = _
    rw [limsup_congr (eventually_atTop.2 ⟨max J Q₀, hY⟩), limsup_const]
  have hfl : ⌊Z ω / (2 * π) + 1 / 2⌋ = n₀ := by
    rw [hZ, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0), Int.floor_eq_iff]
    constructor <;> linarith
  show IsPocketBranch (β ω) (α ω) (c ω) ⌊Z ω / (2 * π) + 1 / 2⌋
  rw [hfl]
  exact hn₀

end Named

end InteractingSLE.Sec7.Lemma71O
