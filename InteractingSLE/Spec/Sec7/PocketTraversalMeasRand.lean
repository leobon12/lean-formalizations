/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordAssembly
import InteractingSLE.Spec.Sec7.StripSysSel
import InteractingSLE.Spec.Sec7.Lemma71ICap

/-!
# The erased counterflow traversal of a random change pocket is measurable at each fixed own time

Packet PROVE-STRIPSYS23, item 2 (second half). Specification §7.4.1, proof of Lemma 7.25 (`source/spec/p385-432.md`
L489–L515, p. 414: the relative driver of the erased traversal is the process to which Aux. lemma 122's martingale
characterization is applied, so the traversal must be a random curve, measurable at each fixed own time) and Aux.
lemma 130 (p. 409: "The event and the selected component are measurable from their complete labeled incoming paths
alone").

PROVE-STRIPSYS20 assembled the pocket word evolution (hPW) from a random bounded change pocket with the named input
`PocketWordAssembly.TraversalMeasStatement`: for every Jordan coordinate family `ψ` of the pocket that is measurable
for the walls' σ-algebra `𝓦` at its `𝓦`-measurable points, the traversal `ψ ∘ γ̂` in that coordinate is measurable at
each fixed own time. This file proves it for every counterflow that is measurable at each fixed time.

* **Hitting times.** For a random path continuous on `[0, ∞)` and measurable at fixed times, the first hitting time
  of a measurable random point is measurable (`measurable_firstHit`): `{T ≤ t}` is "visited during `[0, t]`" or
  "never visited", both countable conditions at rational times (`StripSys.mem_image_Icc_iff`).
* **The erasure clock** `ℓ(t) = ∫_τ^t 1_I(s) e^{−s} ds`, `I = {s ∈ (τ, σ) : η s ∈ C}`, is measurable at measurable
  times (`measurable_pocketClock`): the integrand is jointly measurable, the primitive from `0` is measurable for each
  upper limit (Fubini's measurability, `StronglyMeasurable.integral_prod_right'`) and continuous in it, hence jointly
  measurable (Carathéodory).
* **The fibre's right end** `fR(v) = sup {t ∈ [τ, S] : ℓ t ≤ v ∨ ℓ τ}` of a continuous monotone clock is measurable
  (`measurable_fibreRight`): `a < fR(v)` iff `a < τ` or some rational `q ∈ (a, S]`, `q ≥ τ`, has `ℓ q ≤ v ∨ ℓ τ`.
* **The Jordan coordinate at measurable points.** A family `ψ` measurable for `𝓦` at `𝓦`-measurable points (only)
  is measurable at every measurable point of the closed pocket off `m(x₀)` (`measurable_comp_of_isPointMeasurable`):
  its values at the fixed points of a dense sequence lying in the pocket are `𝓦`-measurable, and every value is a
  limit of those along a measurable approach sequence (`Lemma71E.exists_measurable_approach`), by continuity of the
  Jordan coordinate on the closed pocket off `m(x₀)`.

## Main results

* `firstHit_le_iff`, `measurable_firstHit`, `measurable_uncurry_max`, `measurable_comp_time`,
  `measurable_erasureClock`, `measurable_pocketClock`, `lt_fibreRight_iff`, `measurable_fibreRight`;
* `measurable_cfPocket_sub`, `measurableSet_mem_cfPocket`, `measurable_comp_of_fixedPts`,
  `measurable_comp_of_isPointMeasurable`, `measurable_cfArcR_sub`;
* **`traversalMeasStatement_of_measurable`**: `TraversalMeasStatement 𝓦 R L r η G` for walls measurable for `𝓦`
  (`𝓦 ≤ mΩ`), a `𝓦`-measurable event `G` of bounded change pockets traversed by the counterflow
  (`IsCfPocketConfig`), and a counterflow measurable at each fixed time;
* **`pocketWordEvolution_of_cfPocketConfig_meas`**, `pocketWordEvolution_of_cfPocketConfig_meas'`: STRIPSYS20's
  assembly with `TraversalMeasStatement` replaced by the fixed-time measurability of the counterflow.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketTraversalMeasRand

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketMeas PocketWordAssembly

/-! ### Deterministic facts -/

/-- **The first hitting time is at most `t ≥ 0`** iff the point is visited during `[0, t]` or never visited (then the
hitting time is `sInf ∅ = 0`). -/
theorem firstHit_le_iff {η : ℝ → ℂ} (hη : ContinuousOn η (Ici 0)) {p : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    firstHit η p ≤ t ↔ p ∈ η '' Icc 0 t ∨ ∀ n : ℕ, p ∉ η '' Icc 0 (n : ℝ) := by
  constructor
  · intro h
    by_cases hv : ∃ n : ℕ, p ∈ η '' Icc 0 (n : ℝ)
    · obtain ⟨n, hn⟩ := hv
      obtain ⟨h0, hηp, -⟩ := firstHit_spec hη ⟨_, hn⟩
      exact Or.inl ⟨_, ⟨h0, h⟩, hηp⟩
    · push Not at hv
      exact Or.inr hv
  · rintro (⟨u, hu, rfl⟩ | hn)
    · have hb : BddBelow {x ∈ Ici (0 : ℝ) | η x = η u} := ⟨0, fun _ hx => hx.1⟩
      exact (csInf_le hb ⟨hu.1, rfl⟩).trans hu.2
    · have he : {u ∈ Ici (0 : ℝ) | η u = p} = ∅ := by
        refine eq_empty_iff_forall_notMem.2 fun u (hu : u ∈ {u ∈ Ici (0 : ℝ) | η u = p}) => ?_
        exact hn ⌈u⌉₊ ⟨u, ⟨hu.1, Nat.le_ceil u⟩, hu.2⟩
      rw [firstHit, he, Real.sInf_empty]
      exact ht

theorem firstHit_nonneg (η : ℝ → ℂ) (p : ℂ) : 0 ≤ firstHit η p :=
  Real.sInf_nonneg fun _ hx => hx.1

/-- **The right end of a fibre of a continuous monotone clock exceeds `a`** iff `a < τ` or some rational
`q ∈ (a, S]` with `q ≥ τ` has clock at most `v ∨ ℓ τ`. -/
theorem lt_fibreRight_iff {ℓ : ℝ → ℝ} (hℓ : Continuous ℓ) (hm : Monotone ℓ) {τ S v a : ℝ} (hτS : τ ≤ S) :
    a < Sec6.fibreRight ℓ τ S v ↔
      a < τ ∨ ∃ q : ℚ, a < q ∧ τ ≤ q ∧ (q : ℝ) ≤ S ∧ ℓ q ≤ max v (ℓ τ) := by
  constructor
  · intro h
    by_cases haτ : a < τ
    · exact Or.inl haτ
    · push Not at haτ
      have hmem := Sec6.fibreRight_mem_set hℓ hτS v
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h
      exact Or.inr ⟨q, hq1, haτ.trans hq1.le, hq2.le.trans hmem.1.2, (hm hq2.le).trans hmem.2⟩
  · rintro (haτ | ⟨q, hq1, hq2, hq3, hq4⟩)
    · exact haτ.trans_le (Sec6.le_fibreRight ⟨le_rfl, hτS⟩ (le_max_right _ _))
    · exact hq1.trans_le (Sec6.le_fibreRight ⟨hq2, hq3⟩ hq4)

/-! ### Measurability for random paths on an arbitrary measurable space -/

section Generic

variable {α : Type*} [MeasurableSpace α] {η : α → ℝ → ℂ}

/-- Visiting a random point during `[0, t]` is a measurable event. -/
theorem measurableSet_mem_image_Icc (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {p : α → ℂ} (hp : Measurable p) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet {ω | p ω ∈ η ω '' Icc 0 t} := by
  have hc : ∀ ω, Continuous (nnPath (η ω)) := fun ω =>
    (hη ω).comp_continuous NNReal.continuous_coe fun s => s.2
  have hq : ∀ q : ℚ, Measurable fun ω => nnPath (η ω) (StripSys.rt q) := fun q =>
    hηm _ (StripSys.rt q).2
  have heq : {ω | p ω ∈ η ω '' Icc 0 t} = {ω | ∀ n : ℕ, ∃ q : ℚ, 0 ≤ q ∧ (q : ℝ) ≤ t.toNNReal ∧
      dist (p ω) (nnPath (η ω) (StripSys.rt q)) < 1 / (n + 1)} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [← image_nnPath (η ω) ht, StripSys.mem_image_Icc_iff (hc ω)]
  rw [heq]
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => Measurable.exists fun q =>
    measurable_const.and (measurable_const.and (measurableSet_setOfPred.1 ?_)))
  exact measurableSet_lt (hp.dist (hq q)) measurable_const

/-- **The first hitting time of a measurable random point is measurable.** -/
theorem measurable_firstHit (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {p : α → ℂ} (hp : Measurable p) :
    Measurable fun ω => firstHit (η ω) (p ω) := by
  refine measurable_of_Iic fun t => ?_
  by_cases ht : 0 ≤ t
  · have heq : (fun ω => firstHit (η ω) (p ω)) ⁻¹' Iic t =
        {ω | p ω ∈ η ω '' Icc 0 t} ∪ ⋂ n : ℕ, {ω | p ω ∈ η ω '' Icc 0 (n : ℝ)}ᶜ := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_union, mem_iInter, mem_compl_iff, mem_ofPred_eq]
      exact firstHit_le_iff (hη ω) ht
    rw [heq]
    exact (measurableSet_mem_image_Icc hη hηm hp ht).union
      (MeasurableSet.iInter fun n => (measurableSet_mem_image_Icc hη hηm hp n.cast_nonneg).compl)
  · have heq : (fun ω => firstHit (η ω) (p ω)) ⁻¹' Iic t = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun ω hω => ht ?_
      exact (firstHit_nonneg _ _).trans hω
    rw [heq]
    exact MeasurableSet.empty

/-- The path read at `max s 0` is jointly measurable (Carathéodory). -/
theorem measurable_uncurry_max (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) : Measurable fun x : α × ℝ => η x.1 (max x.2 0) := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : α) => η ω (max s 0))
    (fun ω => (hη ω).comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0)
    (fun s => hηm _ (le_max_right s 0))
  exact h.comp measurable_swap

/-- A random path read at a measurable nonnegative random time is measurable. -/
theorem measurable_comp_time (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {T : α → ℝ} (hT : Measurable T) (hT0 : ∀ ω, 0 ≤ T ω) :
    Measurable fun ω => η ω (T ω) := by
  have h := (measurable_uncurry_max hη hηm).comp (measurable_id.prodMk hT)
  convert h using 1
  funext ω
  simp only [comp_apply, id_eq, max_eq_left (hT0 ω)]

/-- **The erasure clock of a random visit set with measurable graph is measurable at measurable times**:
`ℓ(T) = ∫_τ^T 1_I(s) e^{−s} ds`. The primitive from `0` is measurable for each upper limit (Fubini's measurability) and
continuous in it, hence jointly measurable (Carathéodory). -/
theorem measurable_erasureClock {I : α → Set ℝ} (hI : MeasurableSet {x : α × ℝ | x.2 ∈ I x.1}) {τ T : α → ℝ}
    (hτ : Measurable τ) (hT : Measurable T) : Measurable fun ω => Sec6.erasureClock (I ω) (τ ω) (T ω) := by
  set g : α × ℝ → ℝ := {x : α × ℝ | x.2 ∈ I x.1}.indicator fun x => Real.exp (-x.2) with hgdef
  have hgm : Measurable g := (Real.measurable_exp.comp measurable_snd.neg).indicator hI
  have hsec : ∀ ω, (I ω).indicator (fun s => Real.exp (-s)) = fun s => g (ω, s) := fun ω => rfl
  have hvm : ∀ ω, MeasurableSet (I ω) := fun ω => measurable_prodMk_left hI
  have hint : ∀ ω a b, IntervalIntegrable (fun s => g (ω, s)) volume a b := fun ω a b => by
    rw [← hsec ω]
    exact Sec6.intervalIntegrable_indicator_exp (hvm ω) a b
  set F : ℝ → α → ℝ := fun x ω => ∫ s in (0 : ℝ)..x, g (ω, s) with hFdef
  have hFm : ∀ x, Measurable (F x) := fun x => by
    have h1 := (hgm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 x))).measurable
    have h2 := (hgm.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc x 0))).measurable
    exact h1.sub h2
  have hFc : ∀ ω, Continuous fun x => F x ω := fun ω => intervalIntegral.continuous_primitive (hint ω) 0
  have hFj : Measurable (uncurry F) := measurable_uncurry_of_continuous_of_measurable hFc hFm
  have hcomp : ∀ {X : α → ℝ}, Measurable X → Measurable fun ω => F (X ω) ω := fun hX =>
    hFj.comp (hX.prodMk measurable_id)
  have heq : (fun ω => Sec6.erasureClock (I ω) (τ ω) (T ω)) = fun ω => F (T ω) ω - F (τ ω) ω := by
    funext ω
    simp only [Sec6.erasureClock, hsec ω, hFdef]
    exact (intervalIntegral.integral_interval_sub_left (hint ω 0 (T ω)) (hint ω 0 (τ ω))).symm
  rw [heq]
  exact (hcomp hT).sub (hcomp hτ)

/-- **The pocket clock is measurable at measurable times**: `I = {s ∈ (τ, σ) : η s ∈ C}` for a random open set `C`
with measurable graph. -/
theorem measurable_pocketClock (hη : ∀ ω, ContinuousOn (η ω) (Ici 0))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {C : α → Set ℂ}
    (hC : MeasurableSet {x : α × ℂ | x.2 ∈ C x.1}) {τ σ T : α → ℝ} (hτ : Measurable τ) (hσ : Measurable σ)
    (hτ0 : ∀ ω, 0 ≤ τ ω) (hT : Measurable T) :
    Measurable fun ω => Sec6.pocketClock (η ω) (C ω) (τ ω) (σ ω) (T ω) := by
  have h3 : MeasurableSet {x : α × ℝ | η x.1 (max x.2 0) ∈ C x.1} :=
    (measurable_fst.prodMk (measurable_uncurry_max hη hηm)) hC
  have hS : MeasurableSet {x : α × ℝ | x.2 ∈ Sec6.visitSet (η x.1) (C x.1) (τ x.1) (σ x.1)} := by
    have heq : {x : α × ℝ | x.2 ∈ Sec6.visitSet (η x.1) (C x.1) (τ x.1) (σ x.1)} =
        {x : α × ℝ | τ x.1 < x.2} ∩ ({x : α × ℝ | x.2 < σ x.1} ∩ {x : α × ℝ | η x.1 (max x.2 0) ∈ C x.1}) := by
      ext x
      simp only [Sec6.visitSet, mem_ofPred_eq, mem_Ioo, mem_inter_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, by rwa [max_eq_left ((hτ0 x.1).trans h1.le)]⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, by rwa [max_eq_left ((hτ0 x.1).trans h1.le)] at h3⟩
    rw [heq]
    exact (measurableSet_lt (hτ.comp measurable_fst) measurable_snd).inter
      ((measurableSet_lt measurable_snd (hσ.comp measurable_fst)).inter h3)
  exact measurable_erasureClock hS hτ hT

/-- **The right end of a fibre of a random continuous monotone clock is measurable.** -/
theorem measurable_fibreRight {ℓ : α → ℝ → ℝ} (hℓc : ∀ ω, Continuous (ℓ ω)) (hℓm : ∀ ω, Monotone (ℓ ω))
    (hℓq : ∀ q : ℚ, Measurable fun ω => ℓ ω q) {τ S v : α → ℝ} (hτ : Measurable τ) (hS : Measurable S)
    (hv : Measurable v) (hℓτ : Measurable fun ω => ℓ ω (τ ω)) (hτS : ∀ ω, τ ω ≤ S ω) :
    Measurable fun ω => Sec6.fibreRight (ℓ ω) (τ ω) (S ω) (v ω) := by
  refine measurable_of_Ioi fun a => ?_
  have heq : (fun ω => Sec6.fibreRight (ℓ ω) (τ ω) (S ω) (v ω)) ⁻¹' Ioi a =
      {ω | a < τ ω} ∪ ⋃ q : ℚ, {ω | a < q ∧ τ ω ≤ q ∧ (q : ℝ) ≤ S ω ∧ ℓ ω q ≤ max (v ω) (ℓ ω (τ ω))} := by
    ext ω
    simp only [mem_preimage, mem_Ioi, mem_union, mem_iUnion, mem_ofPred_eq]
    exact lt_fibreRight_iff (hℓc ω) (hℓm ω) (hτS ω)
  rw [heq]
  refine (measurableSet_lt measurable_const hτ).union (MeasurableSet.iUnion fun q => ?_)
  refine measurableSet_setOfPred.2 (measurable_const.and
    ((measurableSet_setOfPred.1 (measurableSet_le hτ measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_le measurable_const hS)).and
        (measurableSet_setOfPred.1 (measurableSet_le (hℓq q) (hv.max hℓτ))))))

end Generic

/-! ### The random change pocket -/

section Pocket

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
  {G : Set Ω}

/-- On a subset of `G`, the inverted pocket has measurable membership events and a measurable graph. -/
theorem measurable_cfPocket_sub (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hAG : A ⊆ G) :
    MeasurableSet {x : A × ℂ | x.2 ∈ cfPocket (R x.1) (L x.1) r} := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨C, -, -, hCp, hCm, -, hCG, -⟩ :=
    PocketCoord.exists_measurable_changePocketInc (mΩ := 𝓦) hRm hLm hGm hG he
  have hJ : MeasurableSet {x : A × ℂ | x.2 ∈ C x.1} :=
    measurableSet_setOf_mem (C := fun ω : A => C ω) (fun ω => (hCp ω).1)
      fun c ρ => measurable_subtype_coe (h𝓦 _ (hCm c ρ))
  have hHm : MeasurableSet {x : A × ℂ | x.2 ∈ H} :=
    measurable_snd (measurableSet_lt measurable_const Complex.measurable_im : MeasurableSet {z : ℂ | 0 < z.im})
  have heq : {x : A × ℂ | x.2 ∈ cfPocket (R x.1) (L x.1) r} =
      {x : A × ℂ | x.2 ∈ H} ∩ (fun x : A × ℂ => (x.1, negInv x.2)) ⁻¹' {x : A × ℂ | x.2 ∈ C x.1} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, cfPocket, ← hCG _ (hAG x.1.2)]
    constructor
    · rintro ⟨w, hw, hwx⟩
      rw [← hwx]
      exact ⟨WangWu.negInv_mem_H ((hCp x.1).2.2.2 hw), by rw [WangWu.negInv_negInv]; exact hw⟩
    · rintro ⟨-, hx⟩
      exact ⟨negInv x.2, hx, WangWu.negInv_negInv x.2⟩
  rw [heq]
  exact hHm.inter ((measurable_fst.prodMk (measurable_negInv.comp measurable_snd)) hJ)

omit mΩ in
/-- The pocket-membership events of a fixed point, on `G`, are measurable for the walls' σ-algebra. -/
theorem measurableSet_mem_cfPocket (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (z : ℂ) :
    MeasurableSet[𝓦] {ω | ω ∈ G ∧ z ∈ cfPocket (R ω) (L ω) r} := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨C, -, -, hCp, hCm, -, hCG, -⟩ :=
    PocketCoord.exists_measurable_changePocketInc (mΩ := 𝓦) hRm hLm hGm hG he
  have heq : {ω | ω ∈ G ∧ z ∈ cfPocket (R ω) (L ω) r} = G ∩ {ω | z ∈ negInv '' C ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    exact and_congr_right fun hω => by rw [cfPocket, hCG ω hω]
  rw [heq]
  exact hGm.inter
    (measurableSet_mem_image_negInv (mΩ := 𝓦) (fun ω => (hCp ω).1) (fun ω => (hCp ω).2.2.2) hCm z)

/-- **A random function on the pocket is measurable at measurable points of the closed pocket** (on `A ⊆ G`) as soon
as its values at fixed points are measurable for the walls' σ-algebra on the pocket-membership events and it is
continuous within the pocket at the given points: through the values at the points of a dense sequence and a
measurable approach sequence (`Lemma71E.exists_measurable_approach`). -/
theorem measurable_comp_of_fixedPts (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hfix : ∀ z : ℂ, Measurable[𝓦] ({ω | ω ∈ G ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z))
    {p : A → ℂ} (hp : Measurable p) (hpc : ∀ ω : A, p ω ∈ closure (cfPocket (R ω) (L ω) r))
    (hψc : ∀ ω : A, ContinuousWithinAt (ψ ω) (cfPocket (R ω) (L ω) r) (p ω)) :
    Measurable fun ω : A => ψ ω (p ω) := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set F : A × ℕ → ℂ := fun x =>
    {ω | ω ∈ G ∧ e x.2 ∈ cfPocket (R ω) (L ω) r}.indicator (fun ω => ψ ω (e x.2)) x.1 with hFdef
  have hF : Measurable F :=
    measurable_from_prod_countable_left fun j => ((hfix (e j)).mono h𝓦 le_rfl).comp measurable_subtype_coe
  have hJ := measurable_cfPocket_sub h𝓦 hRm hLm hGm hG hAG
  have hCA : ∀ z, MeasurableSet {ω : A | z ∈ cfPocket (R ω) (L ω) r} := fun z => measurable_prodMk_right hJ
  obtain ⟨N, hN, hNC, hNt⟩ := Lemma71E.exists_measurable_approach (C := fun ω : A => cfPocket (R ω) (L ω) r)
    (fun ω => isOpen_image_negInv' (hG ω (hAG ω.2)).isOpen_changePocket (hG ω (hAG ω.2)).changePocket_subset_H)
    hCA he hp hpc
  refine measurable_of_tendsto_metrizable (f := fun m (ω : A) => F (ω, N m ω))
    (fun m => hF.comp (measurable_id.prodMk (hN m))) (tendsto_pi_nhds.2 fun ω => ?_)
  have hval : ∀ m, F (ω, N m ω) = ψ ω (e (N m ω)) := fun m =>
    indicator_of_mem (show (ω : Ω) ∈ {ω' | ω' ∈ G ∧ e (N m ω) ∈ cfPocket (R ω') (L ω') r} from
      ⟨hAG ω.2, hNC m ω⟩) _
  simp only [hval]
  exact (hψc ω).tendsto.comp (hNt ω)

/-- **A Jordan coordinate family measurable for `𝓦` at `𝓦`-measurable points is measurable at every measurable point**
of the closed pocket off `m(x₀)` (on a subset `A ⊆ G` where the family is continuous there). -/
theorem measurable_comp_of_isPointMeasurable (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hAG : A ⊆ G) {ψ : Ω → ℂ → ℂ}
    (hψc : ∀ ω ∈ A, ContinuousOn (ψ ω) (closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}))
    (hψm : @IsPointMeasurable Ω 𝓦 R L r G ψ) {p : A → ℂ} (hp : Measurable p)
    (hpA : ∀ ω : A, p ω ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) :
    Measurable fun ω : A => ψ ω (p ω) := by
  have hsub : ∀ ω ∈ G, cfPocket (R ω) (L ω) r ⊆ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    fun ω hω z hz => ⟨subset_closure hz, fun h => (hG ω hω).cfPt_openPt_notMem (h ▸ hz)⟩
  refine measurable_comp_of_fixedPts h𝓦 hRm hLm hGm hG hAG (fun z => ?_) hp (fun ω => (hpA ω).1)
    fun ω => ((hψc ω ω.2) _ (hpA ω)).mono (hsub ω (hAG ω.2))
  exact hψm _ (measurableSet_mem_cfPocket hRm hLm hGm hG z) (fun ω hω => hω.1) (fun _ => z) measurable_const
    fun ω hω => hsub ω hω.1 hω.2

/-- The right arc's points at fixed parameters are measurable on a subset of `G`. -/
theorem measurable_cfArcR_sub (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω} (hAG : A ⊆ G) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : Measurable fun ω : A => cfArcR (R ω) (L ω) r s := by
  classical
  set y : Ω → ℝ := fun ω => gapLoα G R L r ω + s * (gapHiα G R L r ω - gapLoα G R L r ω) with hydef
  have hlo := measurable_gapLoα (mΩ := 𝓦) hRm hLm hGm hG
  have hhi := measurable_gapHiα (mΩ := 𝓦) hRm hLm hGm hG
  have hy : Measurable[𝓦] y := hlo.add (measurable_const.mul (hhi.sub hlo))
  have hf : Measurable[𝓦] fun ω => cfPt (discPath G R (y ω) ω) :=
    measurable_cfPt.comp (measurable_discPath_comp (mΩ := 𝓦) hGm (fun ω hω => (hG ω hω).right) hRm hy)
  have h := (hf.mono h𝓦 le_rfl).comp (measurable_subtype_coe (p := fun ω => ω ∈ A))
  convert h using 1
  funext ω
  have hω := hAG ω.2
  obtain ⟨hu, hv, huv, -⟩ := (hG ω hω).changeCorner_props
  have hmem := (IsChangeConfigInc.affine_mem huv).1 hs
  simp only [comp_apply, cfArcR, hydef, ← rightLo_eq_gapLoα hω, ← rightHi_eq_gapHiα hω]
  rw [discPath_of_mem ⟨hu.1.trans hmem.1, hmem.2.trans hv.2⟩ hω]

/-- **The erased counterflow traversal of a random bounded change pocket is measurable at each fixed own time**
(`TraversalMeasStatement`, PROVE-STRIPSYS20's named input): for walls measurable for `𝓦 ≤ mΩ` at each time, a
`𝓦`-measurable event `G` of bounded change pockets traversed by the counterflow, and a counterflow measurable at each
fixed time, every Jordan coordinate family measurable for `𝓦` at its `𝓦`-measurable points gives a traversal
measurable at each fixed own time on every measurable `A ⊆ G` on which it is a Jordan coordinate family. -/
theorem traversalMeasStatement_of_measurable (h𝓦 : 𝓦 ≤ mΩ) (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) :
    TraversalMeasStatement 𝓦 R L r η G := by
  intro A _ hAG ψ hψ hψm u hu
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hP : ∀ ω : A, Sec6.IsReversePocket (W ω) (η ω) (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r)
      (cfArcL (R ω) (L ω) r) (cfBeta (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := fun ω =>
    (hcfg ω (hAG ω.2)).conf.isReversePocket_of_counterflow
      (zero_notMem_closure_of_rightLo_pos (hcfg ω (hAG ω.2)).conf (hcfg ω (hAG ω.2)).bounded)
      (hcfg ω (hAG ω.2)).trace (hcfg ω (hAG ω.2)).continuous_W (hcfg ω (hAG ω.2)).W_zero
      (hcfg ω (hAG ω.2)).revR (hcfg ω (hAG ω.2)).revL (hcfg ω (hAG ω.2)).visR
  have hηc : ∀ ω : A, ContinuousOn (η ω) (Ici 0) := fun ω => (hcfg ω (hAG ω.2)).trace.2.1
  have hηmA : ∀ u, 0 ≤ u → Measurable fun ω : A => η ω u := fun u hu =>
    (hηm u hu).comp measurable_subtype_coe
  -- the first visits of `m(y₀)` and `m(x₀)`
  have hτ : Measurable fun ω : A => firstHit (η ω) (cfArcR (R ω) (L ω) r 1) :=
    measurable_firstHit hηc hηmA (measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG ⟨zero_le_one, le_rfl⟩)
  have hσ : Measurable fun ω : A => firstHit (η ω) (cfArcR (R ω) (L ω) r 0) :=
    measurable_firstHit hηc hηmA (measurable_cfArcR_sub h𝓦 hRm hLm hGm hG hAG ⟨le_rfl, zero_le_one⟩)
  -- the clock, the fibre and the erased point
  have hℓ : ∀ {T : A → ℝ}, Measurable T → Measurable fun ω : A =>
      Sec6.pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (T ω) := fun hT =>
    measurable_pocketClock hηc hηmA (measurable_cfPocket_sub h𝓦 hRm hLm hGm hG hAG) hτ hσ
      (fun ω => firstHit_nonneg _ _) hT
  have hv : Measurable fun ω : A => clockOf (Sec6.pocketClock (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) u :=
    (hℓ hσ).mul measurable_const
  have hfR := measurable_fibreRight (fun ω => (hP ω).continuous_clock) (fun ω => (hP ω).monotone_clock)
    (fun q => hℓ measurable_const) hτ hσ hv (hℓ hτ) (fun ω => (hP ω).τ_lt_σ.le)
  have hp := measurable_comp_time hηc hηmA hfR fun ω => (hP ω).nonneg.trans ((hP ω).fibre_mem _).1
  refine measurable_comp_of_isPointMeasurable h𝓦 hRm hLm hGm hG hAG (fun ω hω => (hψ ω hω).1) hψm hp
    fun ω => ?_
  have hm := (hP ω).erasedPath_mem (clockOf_mem_Ico ((hP ω).clock_σ_pos (hcfg ω (hAG ω.2)).attach) hu)
  exact ⟨hm.1, fun h => hm.2 (mem_singleton_iff.2
    ((mem_singleton_iff.1 h).trans IsChangeConfigInc.cfArcR_zero.symm))⟩

/-! ### The assembly of hPW without the named measurability input -/

/-- **hPW from a random bounded change pocket** (STRIPSYS20's `pocketWordEvolution_of_cfPocketConfig`) with the
named input `TraversalMeasStatement` replaced by the fixed-time measurability of the counterflow. -/
theorem pocketWordEvolution_of_cfPocketConfig_meas.{v} {κ rL rR : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hcpl : PocketCouplingInput κ rL rR 𝓦 P R L r η G) :
    Lemma725Ref.PocketWordEvolution.{v} (16 / κ) rL rR :=
  pocketWordEvolution_of_cfPocketConfig hκ hκ4 hL hR h𝓦 hRm hLm hGm hPG hcfg
    (traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm) hcpl

/-- **hPW in the form the Theorem 1.3 wiring consumes** (`κ′ > 4`, both-low seed weights), with the fixed-time
measurability of the counterflow in place of `TraversalMeasStatement`. -/
theorem pocketWordEvolution_of_cfPocketConfig_meas'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hcpl : PocketCouplingInput (16 / κ') rL rR 𝓦 P R L r η G) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR :=
  pocketWordEvolution_of_cfPocketConfig' hκ' hL hLd hR hRd h𝓦 hRm hLm hGm hPG hcfg
    (traversalMeasStatement_of_measurable h𝓦 hRm hLm hGm hcfg hηm) hcpl

end Pocket

end InteractingSLE.Sec7.PocketTraversalMeasRand
