/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeBoundField
import InteractingSLE.Spec.Restart.ChartMeasRandom
import InteractingSLE.Spec.Restart.ChartMeas
import InteractingSLE.Spec.Ito.Loewner
import InteractingSLE.Stochastic.ItoAdapted

/-!
# Measurability in `ω` of the frozen factors of `M̃`

Packet PROVE-ZHAN-GT4-A8. Source: Astra, *Follow-up proofs*, §A.1.1–A.1.4 (`ig1_followup_proofs.txt` L190–L380, R38):
the factors of `M̃` (D6) with the other curve frozen are adapted processes. The Itô field theorems
(`Ito.integral_mul_fieldStopped_sub_eq_zero`) need the conformal factors `A_{j,k}`, `A_{k,0}`, `A_{k,1}`, `B_{m,0}`,
`B_{m,1}` and `log F` to be measurable at each time. They are defined through choices (`OwnData`'s image driver
`W'` and clock `a`), but each one is a canonical function of the random image hull `E_t = g_t(A)`:

* `A_{j,k} = Re R_t^{(k)}(W_t)`, with `R_t` the mapping-out function of `E_t`, extended across `W_t`;
* `A_{k,0}, B_{m,0} = Re g̃_{a(t)}(ζ) + W'(a(t)) = lim_n Re R_t(g_t(φ⁻¹(ζ + i/(n+1))) + W_t)`;
* `A_{k,1}, B_{m,1}` (up to the constant `φ'(p_m)`) `= Re g̃'_{a(t)}(ζ)`, the limit of difference quotients at `ζ`.

The random compact set `closure E_t` is dyadic-hit measurable (countable dense subset of `A`, the adapted values
`g_t(z)`), so its mapping-out function is measurable at every fixed point (`Restart.measurable_indicator_mapOut`);
iterated derivatives at fixed points are limits of difference quotients, and values or derivatives at random points
are forward limits along the random domain (`Restart.measurable_of_tendsto_nhdsWithin`).

## Main results

* `measurable_indicator_of_tendsto'`: forward limits along a random open set, on a measurable event;
* `measurable_indicator_iterDeriv`: iterated derivatives of a random holomorphic function at fixed points;
* `inter_closure_nonempty_iff`, `isDyadicHitMeasurable_closure_image`: the closure of the image of a fixed set under
  a random continuous map is dyadic-hit measurable;
* `FrzMeas` (the measurability inputs at a time `t`) and `FrzMeas.measurable_frzA`,
  `FrzMeas.measurable_frzImg`, `FrzMeas.measurable_frzImgD`, `measurable_frzLogF`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull)

/-! ### Forward limits and derivatives of random holomorphic functions -/

section RandomHolo

variable {Ω : Type*} [MeasurableSpace Ω] {S : Set Ω} {D : Ω → Set ℂ} {f : Ω → ℂ → ℂ}

/-- **Forward limits along a random open set are measurable, on a measurable event `S`.** The version of
`Restart.measurable_of_tendsto_nhdsWithin` where the data are only given on `S`. -/
theorem measurable_indicator_of_tendsto' (hS : MeasurableSet S) (hDo : ∀ ω ∈ S, IsOpen (D ω))
    (hDm : ∀ z, MeasurableSet {ω | ω ∈ S ∧ z ∈ D ω})
    (hfm : ∀ z, Measurable ({ω | ω ∈ S ∧ z ∈ D ω}.indicator fun ω => f ω z)) {q w : Ω → ℂ}
    (hq : Measurable (S.indicator q)) (hqD : ∀ ω ∈ S, q ω ∈ closure (D ω))
    (hlim : ∀ ω ∈ S, Tendsto (f ω) (𝓝[D ω] (q ω)) (𝓝 (w ω))) : Measurable (S.indicator w) := by
  classical
  set D' : Ω → Set ℂ := fun ω => if ω ∈ S then D ω else univ
  set f' : Ω → ℂ → ℂ := fun ω => if ω ∈ S then f ω else 0
  have hD'o : ∀ ω, IsOpen (D' ω) := fun ω => by
    by_cases hω : ω ∈ S
    · simp only [D', hω, ↓reduceIte]; exact hDo ω hω
    · simp only [D', hω, ↓reduceIte]; exact isOpen_univ
  have hset : ∀ z, {ω | z ∈ D' ω} = {ω | ω ∈ S ∧ z ∈ D ω} ∪ Sᶜ := fun z => by
    ext ω
    by_cases hω : ω ∈ S <;> simp [D', hω]
  have hD'm : ∀ z, MeasurableSet {ω | z ∈ D' ω} := fun z => by
    rw [hset]; exact (hDm z).union hS.compl
  have hf'm : ∀ z, Measurable ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) := fun z => by
    have heq : ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) =
        {ω | ω ∈ S ∧ z ∈ D ω}.indicator fun ω => f ω z := by
      funext ω
      by_cases hω : ω ∈ S
      · by_cases hz : z ∈ D ω
        · simp [D', f', hω, hz]
        · simp [D', f', hω, hz]
      · simp [D', f', hω]
    rw [heq]; exact hfm z
  have hq'D : ∀ ω, S.indicator q ω ∈ closure (D' ω) := fun ω => by
    by_cases hω : ω ∈ S
    · simp only [D', hω, ↓reduceIte, indicator_of_mem hω]; exact hqD ω hω
    · simp only [D', hω, ↓reduceIte, closure_univ]; exact mem_univ _
  refine Restart.measurable_of_tendsto_nhdsWithin hD'o hD'm hf'm hq hq'D fun ω => ?_
  by_cases hω : ω ∈ S
  · simp only [D', f', hω, ↓reduceIte, indicator_of_mem hω]; exact hlim ω hω
  · simp only [f', hω, ↓reduceIte, indicator_of_notMem hω]; exact tendsto_const_nhds

/-- **Evaluation at a random point of a random open set**, on a measurable event `S`: if `f ω` is continuous on
`D ω` and measurable at fixed points (indicator form), then `ω ↦ f ω (q ω)` is measurable on `S`. -/
theorem measurable_indicator_eval (hS : MeasurableSet S) (hDo : ∀ ω ∈ S, IsOpen (D ω))
    (hDm : ∀ z, MeasurableSet {ω | ω ∈ S ∧ z ∈ D ω})
    (hfm : ∀ z, Measurable ({ω | ω ∈ S ∧ z ∈ D ω}.indicator fun ω => f ω z))
    (hfc : ∀ ω ∈ S, ContinuousOn (f ω) (D ω)) {q : Ω → ℂ} (hq : Measurable (S.indicator q))
    (hqD : ∀ ω ∈ S, q ω ∈ D ω) : Measurable (S.indicator fun ω => f ω (q ω)) :=
  measurable_indicator_of_tendsto' hS hDo hDm hfm hq (fun ω hω => subset_closure (hqD ω hω))
    fun ω hω => hfc ω hω (q ω) (hqD ω hω)

/-- Iterated complex derivatives of a holomorphic function on an open set are holomorphic there. -/
theorem differentiableOn_iterate_deriv {g : ℂ → ℂ} {U : Set ℂ} (hg : DifferentiableOn ℂ g U) (hU : IsOpen U)
    (k : ℕ) : DifferentiableOn ℂ (deriv^[k] g) U := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.deriv hU

/-- Functions that agree near `x` have the same iterated derivatives near `x`. -/
theorem eventuallyEq_iterate_deriv {g₁ g₂ : ℂ → ℂ} {x : ℂ} (h : g₁ =ᶠ[𝓝 x] g₂) (k : ℕ) :
    deriv^[k] g₁ =ᶠ[𝓝 x] deriv^[k] g₂ := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    exact ih.deriv

/-- The real step `1/(m+1)`, as a complex number. -/
def stepC (m : ℕ) : ℂ := ((1 / ((m : ℝ) + 1) : ℝ) : ℂ)

theorem stepC_ne_zero (m : ℕ) : stepC m ≠ 0 := by
  unfold stepC
  exact ofReal_ne_zero.2 (by positivity)

theorem tendsto_stepC : Tendsto stepC atTop (𝓝 0) := by
  have h := (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [ofReal_zero] at h
  exact h

theorem tendsto_stepC_punctured : Tendsto stepC atTop (𝓝[≠] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_stepC, Eventually.of_forall stepC_ne_zero⟩

/-- **Iterated derivatives of a random holomorphic function are measurable at fixed points** (indicator form, on a
measurable event `S`): difference quotients along `z + 1/(m+1)`. -/
theorem measurable_indicator_iterDeriv (hDo : ∀ ω ∈ S, IsOpen (D ω))
    (hDm : ∀ z, MeasurableSet {ω | ω ∈ S ∧ z ∈ D ω})
    (hf : ∀ ω ∈ S, DifferentiableOn ℂ (f ω) (D ω))
    (hf0 : ∀ z, Measurable ({ω | ω ∈ S ∧ z ∈ D ω}.indicator fun ω => f ω z)) (k : ℕ) (z : ℂ) :
    Measurable ({ω | ω ∈ S ∧ z ∈ D ω}.indicator fun ω => deriv^[k] (f ω) z) := by
  induction k generalizing z with
  | zero => simpa using hf0 z
  | succ k ih =>
    refine measurable_of_tendsto_metrizable (f := fun m => {ω | ω ∈ S ∧ z ∈ D ω}.indicator fun ω =>
      (stepC m)⁻¹ * ({ω | ω ∈ S ∧ z + stepC m ∈ D ω}.indicator (fun ω => deriv^[k] (f ω) (z + stepC m)) ω -
        {ω | ω ∈ S ∧ z ∈ D ω}.indicator (fun ω => deriv^[k] (f ω) z) ω)) (fun m => ?_) ?_
    · exact (measurable_const.mul ((ih (z + stepC m)).sub (ih z))).indicator (hDm z)
    · rw [tendsto_pi_nhds]
      intro ω
      by_cases hω : ω ∈ {ω | ω ∈ S ∧ z ∈ D ω}
      · simp only [indicator_of_mem hω]
        have hdk := differentiableOn_iterate_deriv (hf ω hω.1) (hDo ω hω.1) k
        have hda : HasDerivAt (deriv^[k] (f ω)) (deriv^[k + 1] (f ω) z) z := by
          rw [Function.iterate_succ_apply']
          exact ((hdk z hω.2).differentiableAt ((hDo ω hω.1).mem_nhds hω.2)).hasDerivAt
        have hev : ∀ᶠ m in atTop, z + stepC m ∈ D ω := by
          have ht : Tendsto (fun m => z + stepC m) atTop (𝓝 z) := by
            simpa using tendsto_const_nhds.add tendsto_stepC
          exact ht.eventually ((hDo ω hω.1).mem_nhds hω.2)
        refine (hda.tendsto_slope_zero.comp tendsto_stepC_punctured).congr' ?_
        filter_upwards [hev] with m hm
        have hm' : ω ∈ {ω | ω ∈ S ∧ z + stepC m ∈ D ω} := ⟨hω.1, hm⟩
        simp only [Function.comp_apply, indicator_of_mem hm', smul_eq_mul]
      · simp only [indicator_of_notMem hω]
        exact tendsto_const_nhds

end RandomHolo

/-! ### The closure of a random image of a fixed set is dyadic-hit measurable -/

section RandomHull

/-- The closure of `S` meets a nonempty compact `Q` iff points of `S` come arbitrarily close to `Q`. -/
theorem inter_closure_nonempty_iff {Q S : Set ℂ} (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    (Q ∩ closure S).Nonempty ↔ ∀ j : ℕ, ∃ s ∈ S, infDist s Q < 1 / ((j : ℝ) + 1) := by
  constructor
  · rintro ⟨q, hqQ, hqS⟩ j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    obtain ⟨s, hs, hd⟩ := Metric.mem_closure_iff.1 hqS _ hj
    exact ⟨s, hs, (infDist_le_dist_of_mem hqQ).trans_lt (by rwa [dist_comm])⟩
  · intro h
    have hS : S.Nonempty := let ⟨s, hs, _⟩ := h 0; ⟨s, hs⟩
    obtain ⟨q₀, hq₀, hmin⟩ := hQ.exists_isMinOn hQne (continuous_infDist_pt S).continuousOn
    refine ⟨q₀, hq₀, (mem_closure_iff_infDist_zero hS).2 (le_antisymm ?_ infDist_nonneg)⟩
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
    obtain ⟨s, hs, hsQ⟩ := h j
    obtain ⟨q, hqQ, hq⟩ := (infDist_lt_iff hQne).1 hsQ
    have h1 : infDist q S < 1 / ((j : ℝ) + 1) :=
      (infDist_le_dist_of_mem hs).trans_lt (by rwa [dist_comm])
    have h2 : infDist q₀ S ≤ infDist q S := isMinOn_iff.1 hmin q hqQ
    linarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Whether the closure of a random image of a countable set meets a nonempty compact set is measurable. -/
theorem measurableSet_inter_closure_image_nonempty {C : Set ℂ} (hC : C.Countable) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ c ∈ C, Measurable fun ω => ψ ω c) {Q : Set ℂ} (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    MeasurableSet {ω | (Q ∩ closure (ψ ω '' C)).Nonempty} := by
  have heq : {ω | (Q ∩ closure (ψ ω '' C)).Nonempty} =
      ⋂ j : ℕ, ⋃ c ∈ C, {ω | infDist (ψ ω c) Q < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [mem_ofPred_eq, inter_closure_nonempty_iff hQ hQne, mem_iInter, mem_iUnion, exists_prop,
      Set.exists_mem_image]
  rw [heq]
  exact MeasurableSet.iInter fun j => MeasurableSet.biUnion hC fun c hc =>
    measurableSet_lt ((continuous_infDist_pt Q).measurable.comp (hψ c hc)) measurable_const

open scoped Classical in
/-- **The closure of a random continuous image of a fixed set is dyadic-hit measurable** (`∅` off the event `G`):
it is the closure of the image of a countable dense subset. -/
theorem isDyadicHitMeasurable_closure_image {G : Set Ω} (hG : MeasurableSet G) {A : Set ℂ} {ψ : Ω → ℂ → ℂ}
    (hψm : ∀ z ∈ A, Measurable (G.indicator fun ω => ψ ω z)) (hψc : ∀ ω ∈ G, ContinuousOn (ψ ω) A) :
    Restart.IsDyadicHitMeasurable fun ω => if ω ∈ G then closure (ψ ω '' A) else ∅ := by
  obtain ⟨C, hCA, hCc, hAC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace A).exists_countable_dense_subset
  set ψ' : Ω → ℂ → ℂ := fun ω z => G.indicator (fun ω => ψ ω z) ω with hψ'def
  have hcl : ∀ ω ∈ G, closure (ψ ω '' A) = closure (ψ' ω '' C) := fun ω hω => by
    have hψ' : ψ' ω = ψ ω := funext fun z => by simp [ψ', hω]
    rw [hψ']
    refine Subset.antisymm (closure_minimal ?_ isClosed_closure) (closure_mono (image_mono hCA))
    rintro _ ⟨a, ha, rfl⟩
    exact ((hψc ω hω a ha).mono hCA).mem_closure_image (hAC ha)
  intro n k
  have heq : {ω | (Restart.dyadicSquare n k ∩ (if ω ∈ G then closure (ψ ω '' A) else ∅)).Nonempty} =
      G ∩ {ω | (Restart.dyadicSquare n k ∩ closure (ψ' ω '' C)).Nonempty} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, hω, ↓reduceIte, hcl ω hω, mem_inter_iff, true_and]
    · simp [hω]
  rw [heq]
  exact hG.inter (measurableSet_inter_closure_image_nonempty hCc (fun c hc => hψm c (hCA hc))
    (Restart.isCompact_dyadicSquare n k) (Restart.PairData.dyadicSquare_nonempty n k))

end RandomHull

/-! ### The frozen factors are measurable -/

section Own

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The (uncentred) image `E_t = g_t(A)` of the frozen hull. -/
def imgHull (W : ℝ → ℝ) (A : Set ℂ) (t : ℝ) : Set ℂ := (fun z => fwdMap W t z + W t) '' A

/-- **The measurability inputs at time `t`.** On a measurable event `G`, `OwnData` holds up to a time `T ω ≥ t`, the
driver value `W_t` is measurable, and the Loewner map `g_t(z)` is measurable at every fixed `z ∈ ℍ` on the event that
`z` is alive at `t` (for `W = √κ B` these come from `Ito.measurableSet_aliveSet` and `Ito.measurable_fwdMap_alive`). -/
structure FrzMeas (W W' a : Ω → ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ) (T : Ω → ℝ) (G : Set Ω) (t : ℝ) : Prop where
  meas : MeasurableSet G
  own : ∀ ω ∈ G, OwnData (W ω) A φ (T ω) (a ω) (W' ω)
  mem : ∀ ω ∈ G, t ∈ Icc 0 (T ω)
  drv : Measurable fun ω => W ω t
  alive : ∀ z ∈ H, MeasurableSet {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) z t u}
  fwd : ∀ z ∈ H,
    Measurable ({ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) z t u}.indicator fun ω => fwdMap (W ω) t z)

open scoped Classical in
/-- The random compact set `closure E_t` (`∅` off `G`). -/
def hullK (W : Ω → ℝ → ℝ) (A : Set ℂ) (G : Set Ω) (t : ℝ) (ω : Ω) : Set ℂ :=
  if ω ∈ G then closure (imgHull (W ω) A t) else ∅

/-- The points `z_n = φ⁻¹(ζ + i/(n+1))` of the original chart over a real mark `ζ` of the `φ`-chart. -/
def markPt (A : Set ℂ) (φ : ℂ → ℂ) (ζ : ℝ) (n : ℕ) : ℂ :=
  Function.invFunOn φ (H \ A) ((ζ : ℂ) + stepC n * I)

namespace FrzMeas

variable {W W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {t : ℝ}
  (hM : FrzMeas W W' a A φ T G t)
include hM

theorem isHPHull {ω : Ω} (hω : ω ∈ G) : IsHPHull (imgHull (W ω) A t) :=
  (hM.own ω hω).isHPHull_E (hM.mem ω hω)

theorem notMem_fwdHull {ω : Ω} (hω : ω ∈ G) {z : ℂ} (hz : z ∈ A) : z ∉ fwdHull (W ω) t :=
  fun hK => Set.disjoint_left.1 ((hM.own ω hω).disjoint_A_K (hM.mem ω hω)) hz hK

theorem alive_of_mem {ω : Ω} (hω : ω ∈ G) {z : ℂ} (hz : z ∈ A) : ∃ u, IsForwardSol (W ω) z t u :=
  QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull (hM.mem ω hω).1 ((hM.own ω hω).hull.1 hz)
    (hM.notMem_fwdHull hω hz)

theorem measurable_img {z : ℂ} (hz : z ∈ A) :
    Measurable (G.indicator fun ω => fwdMap (W ω) t z + (W ω t : ℂ)) := by
  by_cases hzH : z ∈ H
  · have heq : (G.indicator fun ω => fwdMap (W ω) t z + (W ω t : ℂ)) = G.indicator fun ω =>
        {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) z t u}.indicator (fun ω => fwdMap (W ω) t z) ω + (W ω t : ℂ) := by
      funext ω
      by_cases hω : ω ∈ G
      · have hal : ω ∈ {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) z t u} := ⟨hω, hM.alive_of_mem hω hz⟩
        simp only [indicator_of_mem hω, indicator_of_mem hal]
      · simp only [indicator_of_notMem hω]
    rw [heq]
    exact ((hM.fwd z hzH).add (Complex.measurable_ofReal.comp hM.drv)).indicator hM.meas
  · have heq : (G.indicator fun ω => fwdMap (W ω) t z + (W ω t : ℂ)) = fun _ => 0 :=
      funext fun ω => indicator_of_notMem (fun hω => hzH ((hM.own ω hω).hull.1 hz)) _
    rw [heq]
    exact measurable_const

theorem continuousOn_img {ω : Ω} (hω : ω ∈ G) :
    ContinuousOn (fun z => fwdMap (W ω) t z + (W ω t : ℂ)) A := by
  have hd := QuantumZipper.FwdHolo.differentiableOn_fwdMap (hM.own ω hω).cont (hM.mem ω hω).1
  exact (hd.continuousOn.mono fun z hz => ⟨(hM.own ω hω).hull.1 hz, hM.notMem_fwdHull hω hz⟩).add
    continuousOn_const

theorem isDyadicHitMeasurable_hullK : Restart.IsDyadicHitMeasurable (hullK W A G t) :=
  isDyadicHitMeasurable_closure_image (ψ := fun ω z => fwdMap (W ω) t z + (W ω t : ℂ)) hM.meas
    (fun _ hz => hM.measurable_img hz) fun _ hω => hM.continuousOn_img hω

omit hM in
theorem isCompact_hullK (hM : FrzMeas W W' a A φ T G t) (ω : Ω) : IsCompact (hullK W A G t ω) := by
  unfold hullK
  split_ifs with hω
  · exact (hM.isHPHull hω).2.1.isCompact_closure
  · exact isCompact_empty

omit hM in
theorem isPreconnected_hullK (hM : FrzMeas W W' a A φ T G t) (ω : Ω) :
    IsPreconnected (hullK W A G t ω ∪ Restart.lowerHalf) := by
  unfold hullK
  split_ifs with hω
  · have h := (hM.isHPHull hω).isPreconnected_union_lowerHalf.closure
    rw [closure_union, (_root_.InteractingSLE.isClosed_lowerHalf).closure_eq] at h
    exact h
  · rw [empty_union]
    exact _root_.InteractingSLE.isPreconnected_lowerHalf

theorem fillH_hullK {ω : Ω} (hω : ω ∈ G) : fillH (hullK W A G t ω) = imgHull (W ω) A t := by
  simp only [hullK, hω, ↓reduceIte]
  have h1 : fillH (closure (imgHull (W ω) A t)) = fillH (imgHull (W ω) A t) :=
    fillH_congr (by rw [closure_closure])
  rw [h1]
  exact (hM.isHPHull hω).fillH_eq

theorem measurableSet_mem_diff (z : ℂ) : MeasurableSet {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t} := by
  have heq : {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t} = G ∩ {ω | z ∈ H \ fillH (hullK W A G t ω)} := by
    ext ω
    constructor
    · rintro ⟨hω, hz⟩
      exact ⟨hω, by rwa [mem_ofPred_eq, hM.fillH_hullK hω]⟩
    · rintro ⟨hω, hz⟩
      rw [mem_ofPred_eq, hM.fillH_hullK hω] at hz
      exact ⟨hω, hz⟩
  rw [heq]
  exact hM.meas.inter (Restart.measurableSet_mem_H_diff_fillH hM.isDyadicHitMeasurable_hullK
    hM.isCompact_hullK z)

/-- The mapping-out function of `E_t` is measurable at fixed points of its domain. -/
theorem measurable_mapOut (z : ℂ) :
    Measurable ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t}.indicator fun ω =>
      ConformalImage.mapOut (imgHull (W ω) A t) z) := by
  have heq : ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t}.indicator fun ω =>
      ConformalImage.mapOut (imgHull (W ω) A t) z) = G.indicator ({ω | z ∈ H \ fillH (hullK W A G t ω)}.indicator
        fun ω => ConformalImage.mapOut (fillH (hullK W A G t ω)) z) := by
    funext ω
    by_cases hω : ω ∈ G
    · have hf := hM.fillH_hullK hω
      by_cases hz : z ∈ H \ imgHull (W ω) A t
      · have h1 : ω ∈ {ω | z ∈ H \ fillH (hullK W A G t ω)} := by rw [mem_ofPred_eq, hf]; exact hz
        rw [indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t} from ⟨hω, hz⟩),
          indicator_of_mem hω, indicator_of_mem h1, hf]
      · have h1 : ω ∉ {ω | z ∈ H \ fillH (hullK W A G t ω)} := by rw [mem_ofPred_eq, hf]; exact hz
        rw [indicator_of_notMem (fun h => hz h.2), indicator_of_mem hω, indicator_of_notMem h1]
    · rw [indicator_of_notMem (fun h => hω h.1), indicator_of_notMem hω]
  rw [heq]
  exact (Restart.measurable_indicator_mapOut hM.isDyadicHitMeasurable_hullK hM.isCompact_hullK
    hM.isPreconnected_hullK z).indicator hM.meas

/-- Iterated derivatives of the mapping-out function of `E_t` are measurable at fixed points. -/
theorem measurable_iterDeriv_mapOut (k : ℕ) (z : ℂ) :
    Measurable ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t}.indicator fun ω =>
      deriv^[k] (ConformalImage.mapOut (imgHull (W ω) A t)) z) :=
  measurable_indicator_iterDeriv (fun _ hω => (hM.isHPHull hω).2.2.1) hM.measurableSet_mem_diff
    (fun _ hω => (ConformalImage.isMapOut_mapOut (hM.isHPHull hω)).1.1) hM.measurable_mapOut k z

/-- **`F_t^{(k)}(W_t)` is measurable**, `F_t = ownExt … t`: a forward limit of `R_t^{(k)}` at `W_t` along
`ℍ \ E_t` (`R_t` the mapping-out function of `E_t`, equal to `F_t` near `W_t` in `ℍ`). -/
theorem measurable_iterDeriv_ownExt (k : ℕ) :
    Measurable (G.indicator fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t) (W ω t)) := by
  refine measurable_indicator_of_tendsto' hM.meas (D := fun ω => H \ imgHull (W ω) A t)
    (f := fun ω => deriv^[k] (ConformalImage.mapOut (imgHull (W ω) A t))) (q := fun ω => (W ω t : ℂ))
    (fun ω hω => (hM.isHPHull hω).2.2.1) hM.measurableSet_mem_diff (hM.measurable_iterDeriv_mapOut k)
    ((Complex.measurable_ofReal.comp hM.drv).indicator hM.meas) (fun ω hω => ?_) (fun ω hω => ?_)
  · obtain ⟨ρ, hρ, hcl⟩ := (hM.own ω hω).exists_clearance
    have hdisj := hcl t (hM.mem ω hω)
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hs : 0 < min ε ρ / 2 := by positivity
    have hlt : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have hlt' : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hd : dist (W ω t : ℂ) ((W ω t : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I) = min ε ρ / 2 := by
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    refine ⟨(W ω t : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I, ⟨?_, fun hE => ?_⟩, by rw [hd]; exact hlt'⟩
    · show 0 < ((W ω t : ℂ) + ((min ε ρ / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
      exact hs
    · refine Set.disjoint_left.1 hdisj ?_ hE
      rw [mem_ball, dist_comm, hd]
      exact hlt
  · obtain ⟨ρ, hρ, hcl⟩ := (hM.own ω hω).exists_clearance
    obtain ⟨hd, -, -, -, -, hR⟩ := (hM.own ω hω).ownExt_props (hM.mem ω hω) (hcl t (hM.mem ω hω))
    have hR' := hR _ (ConformalImage.isMapOut_mapOut (hM.isHPHull hω))
    have hc : ContinuousAt (deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t)) (W ω t) :=
      (differentiableOn_iterate_deriv hd isOpen_ball k).continuousOn.continuousAt
        (ball_mem_nhds _ (half_pos hρ))
    refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (W ω t : ℂ) (half_pos hρ)),
      self_mem_nhdsWithin] with z hz1 hz2
    have hU : IsOpen (ball (W ω t : ℂ) (ρ / 2) ∩ H) := isOpen_ball.inter QuantumZipper.isOpen_H
    exact (eventuallyEq_iterate_deriv (Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hz1, hz2.1⟩) hR') k).eq_of_nhds

/-- **`A_{j,k}(t) = frzA … k t` is measurable** (on `G`). -/
theorem measurable_frzA (k : ℕ) : Measurable (G.indicator fun ω => frzA (W ω) (W' ω) (a ω) φ k t) := by
  have heq : (G.indicator fun ω => frzA (W ω) (W' ω) (a ω) φ k t) = fun ω =>
      (G.indicator (fun ω => deriv^[k] (ownExt (W ω) (W' ω) (a ω) φ t) (W ω t)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzA]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_iterDeriv_ownExt k)

/-! #### The image chain at a real mark -/

omit hM in
theorem markArg_mem_H (ζ : ℝ) (n : ℕ) : (ζ : ℂ) + stepC n * I ∈ H := by
  show 0 < ((ζ : ℂ) + stepC n * I).im
  simp only [stepC, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
  positivity

omit hM in
theorem markPt_spec (hφ : IsMapOut A φ) (ζ : ℝ) (n : ℕ) :
    markPt A φ ζ n ∈ H \ A ∧ φ (markPt A φ ζ n) = (ζ : ℂ) + stepC n * I := by
  have hex : ∃ z ∈ H \ A, φ z = (ζ : ℂ) + stepC n * I := hφ.1.2.surjOn (markArg_mem_H ζ n)
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

theorem mem_Icc_clock {ω : Ω} (hω : ω ∈ G) : a ω t ∈ Icc 0 (a ω (T ω)) := by
  have h := hM.own ω hω
  have ht := hM.mem ω hω
  have hT : 0 ≤ T ω := ht.1.trans ht.2
  refine ⟨?_, h.mono.monotoneOn ht ⟨hT, le_rfl⟩ ht.2⟩
  rw [← h.a0]
  exact h.mono.monotoneOn ⟨le_rfl, hT⟩ ht ht.1

/-- At a real mark `ζ` alive for the image chain: the points `z_n = φ⁻¹(ζ + i/(n+1))` are eventually alive at `t`,
`g̃_{a(t)}(ζ + i/(n+1)) → g̃_{a(t)}(ζ)`, and `g̃_{a(t)}` is complex differentiable at `ζ`. -/
theorem mark_facts {ζ : ℝ} {ω : Ω} (hω : ω ∈ G) (hv : ∃ v, IsForwardSol (W' ω) (ζ : ℂ) (a ω (T ω)) v) :
    (∀ᶠ n in atTop, ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u) ∧
    Tendsto (fun n => fwdMap (W' ω) (a ω t) ((ζ : ℂ) + stepC n * I)) atTop
      (𝓝 (fwdMap (W' ω) (a ω t) ζ)) ∧
    HasDerivAt (fwdMap (W' ω) (a ω t)) (deriv (fwdMap (W' ω) (a ω t)) ζ) ζ := by
  obtain ⟨v, hv⟩ := hv
  have h := hM.own ω hω
  have ht := hM.mem ω hω
  have hat := hM.mem_Icc_clock hω
  have hS : 0 ≤ a ω (T ω) := hat.1.trans hat.2
  obtain ⟨δ, hδ, hlow, hmem⟩ := exists_aliveDisc_self hv hS
  have hder := hasDerivAt_fwdMap_aliveDisc h.contW' hv hδ hlow hmem hat
  have hconv : Tendsto (fun n => (ζ : ℂ) + stepC n * I) atTop (𝓝 (ζ : ℂ)) := by
    simpa using tendsto_const_nhds.add (tendsto_stepC.mul_const I)
  refine ⟨?_, hder.continuousAt.tendsto.comp hconv, hder.differentiableAt.hasDerivAt⟩
  filter_upwards [hconv.eventually (ball_mem_nhds (ζ : ℂ) (aliveRad_pos hδ))] with n hn
  obtain ⟨hzA, hφz⟩ := markPt_spec h.mapOut ζ n
  refine QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht.1 hzA.1 fun hK => ?_
  have h1 : φ (markPt A φ ζ n) ∈ fwdHull (W' ω) (a ω t) := by rw [h.img t ht]; exact ⟨_, hK, rfl⟩
  rw [hφz] at h1
  obtain ⟨v', hv', -⟩ := exists_sol_aliveDisc h.contW' hv hδ hlow hn
  exact Ito.notMem_fwdHull_of_isForwardSol h.contW' (markArg_mem_H ζ n) hS hv'
    (QuantumZipper.fwdHull_mono.1 hat.2 h1)

/-- On the event that `z_n` is alive at `t`: the point `g_t(z_n) + W_t` lies in `ℍ \ E_t`, and the mapping-out
function of `E_t` there is `g̃_{a(t)}(ζ + i/(n+1)) + W'(a(t))` (the rate identity of `OwnData`). -/
theorem mark_eval {ζ : ℝ} {n : ℕ} {ω : Ω} (hω : ω ∈ G) (hal : ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u) :
    fwdMap (W ω) t (markPt A φ ζ n) + (W ω t : ℂ) ∈ H \ imgHull (W ω) A t ∧
      ConformalImage.mapOut (imgHull (W ω) A t) (fwdMap (W ω) t (markPt A φ ζ n) + (W ω t : ℂ)) =
        fwdMap (W' ω) (a ω t) ((ζ : ℂ) + stepC n * I) + (W' ω (a ω t) : ℂ) := by
  have h := hM.own ω hω
  have ht := hM.mem ω hω
  obtain ⟨hzA, hφz⟩ := markPt_spec h.mapOut ζ n
  obtain ⟨u, hu⟩ := hal
  have hzK : markPt A φ ζ n ∉ fwdHull (W ω) t := Ito.notMem_fwdHull_of_isForwardSol h.cont hzA.1 ht.1 hu
  have hbij := (isMapOut_fwdMap h.cont h.zero ht.1).1.2
  refine ⟨⟨hbij.mapsTo ⟨hzA.1, hzK⟩, ?_⟩, ?_⟩
  · rintro ⟨b, hb, hbe⟩
    have := hbij.injOn ⟨h.hull.1 hb, hM.notMem_fwdHull hω hb⟩ ⟨hzA.1, hzK⟩ hbe
    exact hzA.2 (this ▸ hb)
  · have hr := (h.rate t ht _ (ConformalImage.isMapOut_mapOut (hM.isHPHull hω))).1 (markPt A φ ζ n)
      ⟨hzA.1, fun h' => h'.elim hzA.2 hzK⟩
    rw [hφz] at hr
    exact hr.symm

/-- The value of the mapping-out function of `E_t` at `g_t(z_n) + W_t`, on the event that `z_n` is alive. -/
theorem measurable_markVal (hφ : IsMapOut A φ) (ζ : ℝ) (n : ℕ) :
    Measurable ({ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u}.indicator fun ω =>
      ConformalImage.mapOut (imgHull (W ω) A t) (fwdMap (W ω) t (markPt A φ ζ n) + (W ω t : ℂ))) := by
  set Gn := {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u} with hGn
  have hzH : markPt A φ ζ n ∈ H := (markPt_spec hφ ζ n).1.1
  have hS : MeasurableSet Gn := hM.alive _ hzH
  refine measurable_indicator_eval (D := fun ω => H \ imgHull (W ω) A t)
    (f := fun ω => ConformalImage.mapOut (imgHull (W ω) A t)) hS (fun _ hω => (hM.isHPHull hω.1).2.2.1)
    (fun z => ?_) (fun z => ?_) (fun _ hω => (ConformalImage.isMapOut_mapOut (hM.isHPHull hω.1)).1.1.continuousOn)
    ?_ fun ω hω => (hM.mark_eval hω.1 hω.2).1
  · have heq : {ω | ω ∈ Gn ∧ z ∈ H \ imgHull (W ω) A t} = Gn ∩ {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t} := by
      ext ω
      exact ⟨fun h => ⟨h.1, h.1.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [heq]
    exact hS.inter (hM.measurableSet_mem_diff z)
  · have heq : ({ω | ω ∈ Gn ∧ z ∈ H \ imgHull (W ω) A t}.indicator fun ω =>
        ConformalImage.mapOut (imgHull (W ω) A t) z) = Gn.indicator ({ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t}.indicator
          fun ω => ConformalImage.mapOut (imgHull (W ω) A t) z) := by
      funext ω
      by_cases hω : ω ∈ Gn
      · by_cases hz : z ∈ H \ imgHull (W ω) A t
        · rw [indicator_of_mem (show ω ∈ {ω | ω ∈ Gn ∧ z ∈ H \ imgHull (W ω) A t} from ⟨hω, hz⟩),
            indicator_of_mem hω, indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ z ∈ H \ imgHull (W ω) A t} from ⟨hω.1, hz⟩)]
        · rw [indicator_of_notMem (fun h => hz h.2), indicator_of_mem hω, indicator_of_notMem (fun h => hz h.2)]
      · rw [indicator_of_notMem (fun h => hω h.1), indicator_of_notMem hω]
    rw [heq]
    exact (hM.measurable_mapOut z).indicator hS
  · have heq : (Gn.indicator fun ω => fwdMap (W ω) t (markPt A φ ζ n) + (W ω t : ℂ)) = Gn.indicator fun ω =>
        Gn.indicator (fun ω => fwdMap (W ω) t (markPt A φ ζ n)) ω + (W ω t : ℂ) := by
      funext ω
      by_cases hω : ω ∈ Gn
      · simp only [indicator_of_mem hω]
      · simp only [indicator_of_notMem hω]
    rw [heq]
    exact ((hM.fwd _ hzH).add (Complex.measurable_ofReal.comp hM.drv)).indicator hS

/-- **The image chain at a real mark is measurable**: `g̃_{a(t)}(ζ) + W'(a(t))`, on `G`, for a mark `ζ` alive for
the image chain up to `a(T)`. -/
theorem measurable_imgC {ζ : ℝ} (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => fwdMap (W' ω) (a ω t) ζ + (W' ω (a ω t) : ℂ)) := by
  rcases G.eq_empty_or_nonempty with hG | ⟨ω₀, hω₀⟩
  · rw [hG, indicator_empty]; exact measurable_const
  have hφ := (hM.own ω₀ hω₀).mapOut
  refine measurable_of_tendsto_metrizable (f := fun n =>
      {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u}.indicator fun ω =>
        ConformalImage.mapOut (imgHull (W ω) A t) (fwdMap (W ω) t (markPt A φ ζ n) + (W ω t : ℂ)))
    (fun n => hM.measurable_markVal hφ ζ n) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · obtain ⟨hev, hlim, -⟩ := hM.mark_facts hω (hv ω hω)
    rw [indicator_of_mem hω]
    refine (hlim.add_const (W' ω (a ω t) : ℂ)).congr' ?_
    filter_upwards [hev] with n hn
    rw [indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u} from ⟨hω, hn⟩),
      (hM.mark_eval hω hn).2]
  · rw [indicator_of_notMem hω]
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    beta_reduce
    rw [indicator_of_notMem (fun h : ω ∈ {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u} => hω h.1)]

/-- **`frzImg` is measurable** (`A_{k,0}`, `B_{m,0}`), on `G`. -/
theorem measurable_frzImg {ζ : ℝ} (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => frzImg (W' ω) (a ω) ζ t) := by
  have heq : (G.indicator fun ω => frzImg (W' ω) (a ω) ζ t) = fun ω =>
      (G.indicator (fun ω => fwdMap (W' ω) (a ω t) ζ + (W' ω (a ω t) : ℂ)) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzImg, add_re, ofReal_re]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_imgC hv)

/-- The derivative of the image chain at a real mark is measurable (on `G`): the limit of the difference quotients
along `ζ + i/(n+1)`. -/
theorem measurable_derivImg {ζ : ℝ} (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => deriv (fwdMap (W' ω) (a ω t)) ζ) := by
  rcases G.eq_empty_or_nonempty with hG | ⟨ω₀, hω₀⟩
  · rw [hG, indicator_empty]; exact measurable_const
  have hφ := (hM.own ω₀ hω₀).mapOut
  have hstep : Tendsto (fun n => stepC n * I) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_stepC.mul_const I,
      Eventually.of_forall fun n => mul_ne_zero (stepC_ne_zero n) I_ne_zero⟩
  refine measurable_of_tendsto_metrizable (f := fun n => G.indicator fun ω => (stepC n * I)⁻¹ *
      ({ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u}.indicator (fun ω =>
        ConformalImage.mapOut (imgHull (W ω) A t) (fwdMap (W ω) t (markPt A φ ζ n) + (W ω t : ℂ))) ω -
        G.indicator (fun ω => fwdMap (W' ω) (a ω t) ζ + (W' ω (a ω t) : ℂ)) ω))
    (fun n => (measurable_const.mul ((hM.measurable_markVal hφ ζ n).sub
      (hM.measurable_imgC hv))).indicator hM.meas) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ G
  · obtain ⟨hev, -, hder⟩ := hM.mark_facts hω (hv ω hω)
    simp only [indicator_of_mem hω]
    refine (hder.tendsto_slope_zero.comp hstep).congr' ?_
    filter_upwards [hev] with n hn
    rw [indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ ∃ u, IsForwardSol (W ω) (markPt A φ ζ n) t u} from ⟨hω, hn⟩),
      (hM.mark_eval hω hn).2, Function.comp_apply, smul_eq_mul]
    ring
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- **`frzImgD` is measurable** (`A_{k,1}`, `B_{m,1}/φ'(p_m)`), on `G`. -/
theorem measurable_frzImgD {ζ : ℝ} (hv : ∀ ω ∈ G, ∃ v, IsForwardSol (W' ω) (ζ : ℂ) (a ω (T ω)) v) :
    Measurable (G.indicator fun ω => frzImgD (W' ω) (a ω) ζ t) := by
  have heq : (G.indicator fun ω => frzImgD (W' ω) (a ω) ζ t) = fun ω =>
      (G.indicator (fun ω => deriv (fwdMap (W' ω) (a ω t)) ζ) ω).re := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzImgD]
    · simp only [indicator_of_notMem hω, zero_re]
  rw [heq]
  exact Complex.measurable_re.comp (hM.measurable_derivImg hv)

/-- **`frzRate` is measurable** (on `G`). -/
theorem measurable_frzRate : Measurable (G.indicator fun ω => frzRate (W ω) (W' ω) (a ω) φ t) := by
  have heq : (G.indicator fun ω => frzRate (W ω) (W' ω) (a ω) φ t) = fun ω =>
      1 / 4 * (G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) φ 2 t) ω /
        G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) φ 1 t) ω) ^ 2 -
      1 / 6 * (G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) φ 3 t) ω /
        G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) φ 1 t) ω) := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzRate]
    · simp only [indicator_of_notMem hω, div_zero]
      norm_num
  rw [heq]
  exact (measurable_const.mul (((hM.measurable_frzA 2).div (hM.measurable_frzA 1)).pow_const 2)).sub
    (measurable_const.mul ((hM.measurable_frzA 3).div (hM.measurable_frzA 1)))

end FrzMeas

/-- **`log F = frzLogF … t` is measurable** (on `G`), given the measurability inputs at every time `u ∈ [0, t]`:
the integral of the continuous measurable rate. -/
theorem measurable_frzLogF {W W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {t : ℝ}
    (ht : 0 ≤ t) (hM : ∀ u ∈ Icc (0 : ℝ) t, FrzMeas W W' a A φ T G u) :
    Measurable (G.indicator fun ω => frzLogF (W ω) (W' ω) (a ω) φ t) := by
  have heq : (G.indicator fun ω => frzLogF (W ω) (W' ω) (a ω) φ t) = fun ω =>
      ∫ r in (0 : ℝ)..t, G.indicator (fun ω => frzRate (W ω) (W' ω) (a ω) φ r) ω := by
    funext ω
    by_cases hω : ω ∈ G
    · simp only [indicator_of_mem hω, frzLogF]
    · simp only [indicator_of_notMem hω, intervalIntegral.integral_zero]
  rw [heq]
  refine Ito.measurable_intervalIntegral_of_continuousOn ht (fun r hr => (hM r hr).measurable_frzRate)
    fun ω => ?_
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω]
    have htT := (hM t ⟨ht, le_rfl⟩).mem ω hω
    exact ((hM t ⟨ht, le_rfl⟩).own ω hω).continuousOn_frzRate.mono (Icc_subset_Icc_right htT.2)
  · simp only [indicator_of_notMem hω]
    exact continuousOn_const

end Own

end InteractingSLE.ZhanGT4
