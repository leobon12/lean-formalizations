/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Factors
import InteractingSLE.Spec.ZhanGT4.A1MargImg
import InteractingSLE.Spec.Exist.StagedLaw2Flow
import InteractingSLE.Spec.ZhanGT4.A1EightSeedRecord

/-!
# Zhan's A.1: the seeded logarithm at a random frozen height is measurable

Packet PROVE-A1-RECTMEAS. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407).

A source record (`A1EightSeed.srcRec`) reads the frozen curve at a height `t`: its hull `K₂(t)`, its chart
`g^{(2)}_t` and its tip `W₂(t)`. A22's `measurable_srcRec_normEll_pair` proves measurability of the seeded logarithm
for a **deterministic** height. Here the height `τ` is a measurable random variable on the sample space `Ω`. The image
chain of the record is chosen (`imgChain`, a `Classical.choose`); no measurable selection is needed, because every
image observable is read from the unique mapping-out function of the random hull (`FrzMeasR`, A13), exactly as in A22.
The new inputs for a random height are:

* `measurableSet_hit_frzDrv`: the compact hits of the frozen hull at the random height (A1-MARG's
  `measurableSet_hit_stop`, jointly in the stop and the sample);
* `measurable_frzChart_frzDrv`: the frozen chart at a fixed point (the forward map at a random time,
  `Exist.StagedLaw.measurable_fwdMap_param`);
* `markSeq_frzDrv`: the frozen tip as a mark sequence of the chart (a measurable choice of points of a dense sequence,
  as A13's `markSeq_tip`).

## Main results

* `frzDrv`: the frozen driver `u ↦ F(min(max u 0) τ) + p` at the random height `τ`;
* **`frzMeasR_frzDrv`**: the inputs `FrzMeasR` of the growing curve against the frozen hull at the random height;
* **`measurable_srcRec_normEll_rand`**: the seeded logarithm of the source record at the random height, on a measurable
  event, at a fixed own time.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectMeas

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

variable {Ω : Type*}

/-! ### Continuous driver families -/

section Family

variable {F : Ω → ℝ → ℝ}

/-- A family of continuous drivers with measurable evaluations is jointly measurable. -/
theorem measurable_uncurry_drv [MeasurableSpace Ω] (hFc : ∀ ω, Continuous (F ω))
    (hFm : ∀ r, Measurable fun ω => F ω r) :
    Measurable fun q : Ω × ℝ => F q.1 q.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable (u := fun r ω => F ω r) (fun ω => hFc ω) hFm
  exact h.comp measurable_swap

/-- The frozen driver at the random height `τ`: the base driver stopped at `τ` and shifted by `p`. -/
def frzDrv (F : Ω → ℝ → ℝ) (p : ℝ) (τ : Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun u => A1Ref.stopDrv (F ω) (τ ω) u + p

variable {p : ℝ} {τ : Ω → ℝ}

theorem continuous_frzDrv (hFc : ∀ ω, Continuous (F ω)) (hτ0 : ∀ ω, 0 ≤ τ ω) (ω : Ω) :
    Continuous (frzDrv F p τ ω) :=
  (A1Ref.continuous_stopDrv (hFc ω).continuousOn (hτ0 ω)).add continuous_const

theorem frzDrv_tip (hτ0 : ∀ ω, 0 ≤ τ ω) (ω : Ω) : frzDrv F p τ ω (τ ω) = F ω (τ ω) + p := by
  simp only [frzDrv, A1Ref.stopDrv_eqOn (F ω) (τ ω) ⟨hτ0 ω, le_rfl⟩]

theorem frzDrv_zero (hτ0 : ∀ ω, 0 ≤ τ ω) (hF0 : ∀ ω, F ω 0 = 0) (ω : Ω) : frzDrv F p τ ω 0 = p := by
  simp only [frzDrv, A1Ref.stopDrv_eqOn (F ω) (τ ω) ⟨le_rfl, hτ0 ω⟩, hF0 ω, zero_add]

theorem measurable_frzDrv_tip [MeasurableSpace Ω] (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ r, Measurable fun ω => F ω r)
    (hτ : Measurable τ) (hτ0 : ∀ ω, 0 ≤ τ ω) : Measurable fun ω => frzDrv F p τ ω (τ ω) := by
  simp_rw [frzDrv_tip hτ0]
  exact ((measurable_uncurry_drv hFc hFm).comp (measurable_id.prodMk hτ)).add_const p

/-- The frozen hull at the random height is the translated hull of the base driver. -/
theorem fwdHull_frzDrv (hFc : ∀ ω, Continuous (F ω)) (hτ0 : ∀ ω, 0 ≤ τ ω) (ω : Ω) :
    fwdHull (frzDrv F p τ ω) (τ ω) = A2X.physHull p (F ω) (τ ω) := by
  unfold frzDrv
  rw [ConformalImageFull.fwdHull_add_const]
  rw [QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn (A1Ref.continuous_stopDrv (hFc ω).continuousOn (hτ0 ω))
    (hFc ω) (hτ0 ω) (A1Ref.stopDrv_eqOn (F ω) (τ ω))]
  rfl

/-- The frozen chart at the random height, at a fixed point. -/
theorem frzChart_frzDrv_eq (hτ0 : ∀ ω, 0 ≤ τ ω) (ω : Ω) (z : ℂ) :
    frzChart (frzDrv F p τ ω) (τ ω) z = fwdMap (F ω) (τ ω) (z - p) + ((F ω (τ ω) + p : ℝ) : ℂ) := by
  unfold frzChart
  rw [frzDrv_tip hτ0]
  unfold frzDrv
  rw [ConformalImageFull.fwdMap_add_const, Ito.fwdMap_congr_of_eqOn (A1Ref.stopDrv_eqOn (F ω) (τ ω))]

end Family

/-! ### The tip selection -/

section Select

variable {F : Ω → ℝ → ℝ} (hFc : ∀ ω, Continuous (F ω)) {p : ℝ} {τ : Ω → ℝ} (hτ0 : ∀ ω, 0 ≤ τ ω)

/-- The selection predicate for the tip at step `n`: the dense point `e j` lies in `ℍ` off the frozen hull and is
mapped within `1/(n+1)` of `tip + i/(n+1)`. -/
def TipSel (F : Ω → ℝ → ℝ) (p : ℝ) (τ : Ω → ℝ) (n : ℕ) (ω : Ω) (j : ℕ) : Prop :=
  TopologicalSpace.denseSeq ℂ j ∈ H ∧ TopologicalSpace.denseSeq ℂ j ∉ fwdHull (frzDrv F p τ ω) (τ ω) ∧
    dist (frzChart (frzDrv F p τ ω) (τ ω) (TopologicalSpace.denseSeq ℂ j))
      ((frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I) < 1 / ((n : ℝ) + 1)

include hFc hτ0 in
theorem exists_tipSel (n : ℕ) (ω : Ω) : ∃ j, TipSel F p τ n ω j := by
  have hc := continuous_frzDrv (p := p) hFc hτ0 ω
  have hφ := isMapOut_fwdMap_gen hc (hτ0 ω)
  have hy : (frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I ∈ H := FrzMeas.markArg_mem_H _ n
  obtain ⟨z, hz, hzy⟩ := hφ.1.2.surjOn hy
  have hDo : IsOpen (H \ fwdHull (frzDrv F p τ ω) (τ ω)) :=
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc (hτ0 ω)
  have hcont : ContinuousOn (frzChart (frzDrv F p τ ω) (τ ω)) (H \ fwdHull (frzDrv F p τ ω) (τ ω)) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hc (hτ0 ω)).continuousOn.add continuousOn_const
  have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hUo := hcont.isOpen_inter_preimage hDo
    (isOpen_ball (x := (frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I) (ε := 1 / ((n : ℝ) + 1)))
  have hzU : z ∈ (H \ fwdHull (frzDrv F p τ ω) (τ ω)) ∩ frzChart (frzDrv F p τ ω) (τ ω) ⁻¹'
      ball ((frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I) (1 / ((n : ℝ) + 1)) :=
    ⟨hz, by
      rw [mem_preimage, show frzChart (frzDrv F p τ ω) (τ ω) z = (frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I from hzy]
      exact mem_ball_self hr⟩
  obtain ⟨j, hj⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_mem_open hUo ⟨z, hzU⟩
  exact ⟨j, hj.1.1, hj.1.2, hj.2⟩

open scoped Classical in
/-- The `n`-th approximating point of the frozen tip in its chart: the first dense point selected by `TipSel`. -/
def tipQ (hFc : ∀ ω, Continuous (F ω)) (hτ0 : ∀ ω, 0 ≤ τ ω) (p : ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  TopologicalSpace.denseSeq ℂ (Nat.find (exists_tipSel (p := p) hFc hτ0 n ω))

theorem tipQ_spec (n : ℕ) (ω : Ω) :
    tipQ hFc hτ0 p n ω ∈ H ∧ tipQ hFc hτ0 p n ω ∉ fwdHull (frzDrv F p τ ω) (τ ω) ∧
      dist (frzChart (frzDrv F p τ ω) (τ ω) (tipQ hFc hτ0 p n ω)) ((frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I) <
        1 / ((n : ℝ) + 1) := by
  classical
  exact Nat.find_spec (exists_tipSel (p := p) hFc hτ0 n ω)

end Select

/-! ### Hits, chart and tip at the random height -/

section Random

variable [MeasurableSpace Ω] {F : Ω → ℝ → ℝ} (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ r, Measurable fun ω => F ω r)
  (hF0 : ∀ ω, F ω 0 = 0) {p : ℝ} {τ : Ω → ℝ} (hτ : Measurable τ) (hτ0 : ∀ ω, 0 ≤ τ ω)

include hFc hFm hτ hτ0 in
/-- **Compact hits of the base hull at the random height** (A1-MARG's `measurableSet_hit_stop`). -/
theorem measurableSet_hit_rand {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) :
    MeasurableSet {ω | (L ∩ fwdHull (F ω) (τ ω)).Nonempty} := by
  have hS := A1Marg.measurableSet_hit_stop (V := fun (t : ℝ≥0) ω => F ω t) (ζ := fun _ => ⊤)
    (fun ω => ((hFc ω).comp NNReal.continuous_coe).continuousOn) (fun t => hFm t) measurable_const hL hLH
  have hg : Measurable fun ω => ((τ ω).toNNReal, ω) := (measurable_real_toNNReal.comp hτ).prodMk measurable_id
  convert hg hS using 1
  ext ω
  simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
  have hτe : (((τ ω).toNNReal : ℝ≥0) : ℝ) = τ ω := Real.coe_toNNReal _ (hτ0 ω)
  rw [hτe]
  have hext : Continuous (Strip.extPath fun t : ℝ≥0 => F ω t) :=
    (hFc ω).comp (NNReal.continuous_coe.comp continuous_real_toNNReal)
  rw [QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hext (hFc ω) (hτ0 ω) fun u hu => by
    simp only [Strip.extPath, Real.coe_toNNReal _ hu.1]]

include hFc hFm hτ hτ0 in
/-- **Compact hits of the frozen hull at the random height.** -/
theorem measurableSet_hit_frzDrv {L : Set ℂ} (hL : IsCompact L) (hLH : L ⊆ H) :
    MeasurableSet {ω | (L ∩ fwdHull (frzDrv F p τ ω) (τ ω)).Nonempty} := by
  simp_rw [fwdHull_frzDrv hFc hτ0, A1Marg.hit_physHull_iff]
  exact measurableSet_hit_rand hFc hFm hτ hτ0 (A1Marg.isCompact_image_sub hL p) (A1Marg.image_sub_subset_H hLH p)

include hFc hFm hτ hτ0 in
/-- Membership of a fixed point of `ℍ` in the frozen hull at the random height is measurable. -/
theorem measurableSet_mem_frzDrv {z : ℂ} (hz : z ∈ H) :
    MeasurableSet {ω | z ∈ fwdHull (frzDrv F p τ ω) (τ ω)} := by
  have e : {ω | z ∈ fwdHull (frzDrv F p τ ω) (τ ω)} =
      {ω | ({z} ∩ fwdHull (frzDrv F p τ ω) (τ ω)).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, singleton_inter_nonempty]
  rw [e]
  exact measurableSet_hit_frzDrv hFc hFm hτ hτ0 isCompact_singleton (singleton_subset_iff.2 hz)

include hFc hFm hF0 hτ hτ0 in
/-- **The frozen chart at the random height is measurable at every fixed point.** -/
theorem measurable_frzChart_frzDrv (z : ℂ) : Measurable fun ω => frzChart (frzDrv F p τ ω) (τ ω) z := by
  simp_rw [frzChart_frzDrv_eq hτ0]
  have h := (Exist.StagedLaw.measurable_fwdMap_param (W := F) hFc hFm hF0 hτ hτ0
    (y := fun _ => z - p) measurable_const).1
  refine h.add (Complex.measurable_ofReal.comp ?_)
  exact ((measurable_uncurry_drv hFc hFm).comp (measurable_id.prodMk hτ)).add_const p

include hFm hF0 hτ in
/-- **The frozen tip at the random height is a mark sequence of the frozen chart.** -/
theorem markSeq_frzDrv (G : Set Ω) (hG : MeasurableSet G) :
    MarkSeq (fun ω => fwdHull (frzDrv F p τ ω) (τ ω)) (fun ω => frzChart (frzDrv F p τ ω) (τ ω)) G
      (fun ω => frzDrv F p τ ω (τ ω)) (tipQ hFc hτ0 p) := by
  classical
  have hφm := measurable_frzChart_frzDrv (p := p) hFc hFm hF0 hτ hτ0
  have htip := measurable_frzDrv_tip (p := p) hFc hFm hτ hτ0
  have hsel : ∀ n j, MeasurableSet {ω : Ω | TipSel F p τ n ω j} := by
    intro n j
    by_cases hj : TopologicalSpace.denseSeq ℂ j ∈ H
    · have e : {ω : Ω | TipSel F p τ n ω j} =
          {ω | TopologicalSpace.denseSeq ℂ j ∈ fwdHull (frzDrv F p τ ω) (τ ω)}ᶜ ∩
          {ω | dist (frzChart (frzDrv F p τ ω) (τ ω) (TopologicalSpace.denseSeq ℂ j))
            ((frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I) < 1 / ((n : ℝ) + 1)} := by
        ext ω; simp only [TipSel, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, hj, true_and]
      rw [e]
      exact (measurableSet_mem_frzDrv hFc hFm hτ hτ0 hj).compl.inter (measurableSet_lt
        ((hφm _).dist ((Complex.measurable_ofReal.comp htip).add measurable_const)) measurable_const)
    · have e : {ω : Ω | TipSel F p τ n ω j} = ∅ := by
        ext ω; simp only [TipSel, mem_ofPred_eq, hj, false_and, mem_empty_iff_false]
      rw [e]; exact MeasurableSet.empty
  have hN : ∀ n, Measurable fun ω => Nat.find (exists_tipSel (p := p) hFc hτ0 n ω) := fun n =>
    measurable_find (exists_tipSel hFc hτ0 n) (hsel n)
  have hconv : ∀ ω : Ω, Tendsto (fun n => (frzDrv F p τ ω (τ ω) : ℂ) + stepC n * I) atTop
      (𝓝 (frzDrv F p τ ω (τ ω) : ℂ)) := fun ω => by
    simpa using tendsto_const_nhds.add (tendsto_stepC.mul_const I)
  refine ⟨fun ω _ n => (tipQ_spec hFc hτ0 n ω).1, fun n => ?_, fun ω _ => Eventually.of_forall fun n =>
    (tipQ_spec hFc hτ0 n ω).2.1, fun n => measurable_from_nat.comp (hN n), fun n => ?_, fun ω _ => ?_⟩
  · have e : {ω : Ω | tipQ hFc hτ0 p n ω ∈ fwdHull (frzDrv F p τ ω) (τ ω)} = ∅ := by
      ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]; exact (tipQ_spec hFc hτ0 n ω).2.1
    rw [e]; exact MeasurableSet.empty
  · set Φ : Ω × ℕ → ℂ := fun q => frzChart (frzDrv F p τ q.1) (τ q.1) (TopologicalSpace.denseSeq ℂ q.2) with hΦ
    have hΦm : Measurable Φ := measurable_from_prod_countable_left fun j => hφm (TopologicalSpace.denseSeq ℂ j)
    have e : (fun ω => frzChart (frzDrv F p τ ω) (τ ω) (tipQ hFc hτ0 p n ω)) =
        Φ ∘ fun ω => (ω, Nat.find (exists_tipSel (p := p) hFc hτ0 n ω)) := rfl
    rw [e]
    exact (hΦm.comp (measurable_id.prodMk (hN n))).indicator hG
  · refine tendsto_of_tendsto_of_dist (hconv ω) (squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [dist_comm]
    exact (tipQ_spec hFc hτ0 n ω).2.2.le

end Random

/-! ### The seeded logarithm at the random height -/

section Record

variable [MeasurableSpace Ω] {D F : Ω → ℝ → ℝ} (hDc : ∀ ω, Continuous (D ω)) (hDm : ∀ r, Measurable fun ω => D ω r)
  (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ r, Measurable fun ω => F ω r) (hF0 : ∀ ω, F ω 0 = 0) {p : ℝ}
  {τ : Ω → ℝ} (hτ : Measurable τ) (hτ0 : ∀ ω, 0 ≤ τ ω)

include hDc hDm hFc hFm hτ hτ0 in
/-- **The inputs `FrzMeasR` against the frozen hull at the random height**: the growing curve (driver family `D`) at
the own time `u`, on a measurable event `G` where the image data satisfy `OwnData` up to `T ω ≥ u`. -/
theorem frzMeasR_frzDrv {W' a : Ω → ℝ → ℝ} {T : Ω → ℝ} {G : Set Ω} (hG : MeasurableSet G) {u : ℝ} (hu : 0 ≤ u)
    (hown : ∀ ω ∈ G, OwnData (D ω) (fwdHull (frzDrv F p τ ω) (τ ω)) (frzChart (frzDrv F p τ ω) (τ ω)) (T ω) (a ω)
      (W' ω))
    (hmem : ∀ ω ∈ G, u ∈ Icc 0 (T ω)) :
    FrzMeasR D W' a (fun ω => fwdHull (frzDrv F p τ ω) (τ ω)) (fun ω => frzChart (frzDrv F p τ ω) (τ ω)) T G u :=
  A1Marg.frzMeasR_family hDc hu (fun r _ => hDm r) hG
    (fun _ hL hLH => measurableSet_hit_frzDrv hFc hFm hτ hτ0 hL hLH)
    (fun ω _ z hz => ((QuantumZipper.LoewnerAlgebra.mem_fwdHull_iff (hτ0 ω) z).1 hz).1) hown hmem

include hDc hDm hFc hFm hF0 hτ hτ0 in
/-- **The seeded logarithm of the source record at the random height is measurable** on a measurable event `G`, at a
fixed own time `s`: the growing driver family `D` (horizon `T`), the frozen curve `F` stopped at the random height `τ`
and shifted by the other source `p`, the marks `Z`. The image chain is the record's chosen one; the inputs are the
existence of an image chain (`hex`), the aliveness of the frozen tip for every image chain (`hv`), the clearance of the
marks (`hcl`) and the measurability of the marks and of the other source's coordinate and derivative factor. -/
theorem measurable_srcRec_normEll_rand {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) {T : Ω → ℝ} {G : Set Ω}
    (hG : MeasurableSet G) {s : ℝ} (hs : 0 ≤ s) {Z : Ω → Fin n → ℝ → ℝ}
    (hex : ∀ ω ∈ G, ∃ a W', OwnData (D ω) (fwdHull (frzDrv F p τ ω) (τ ω)) (frzChart (frzDrv F p τ ω) (τ ω))
      (T ω) a W')
    (hmem : ∀ ω ∈ G, s ≤ T ω)
    (hv : ∀ ω ∈ G, ∀ a W', OwnData (D ω) (fwdHull (frzDrv F p τ ω) (τ ω)) (frzChart (frzDrv F p τ ω) (τ ω))
      (T ω) a W' → ∃ v, IsForwardSol W' (frzDrv F p τ ω (τ ω) : ℂ) (a (T ω)) v)
    (hcl : ∀ ω ∈ G, ∀ m, ∃ ρ > 0,
      Disjoint (ball (Z ω m s : ℂ) ρ) (imgHull (D ω) (fwdHull (frzDrv F p τ ω) (τ ω)) s))
    (hZ : ∀ m, Measurable (G.indicator fun ω => Z ω m s))
    (hV₀ : Measurable (G.indicator fun ω => (fwdMap (D ω) s p).re + D ω s))
    (hG₀ : Measurable (G.indicator fun ω => (deriv (fwdMap (D ω) s) p).re)) :
    Measurable (G.indicator fun ω =>
      (A1EightSeed.srcRec (D ω) (T ω) (frzDrv F p τ ω) (τ ω) κ rr p (Z ω)).normEll s) := by
  have hM : ∀ u ∈ Icc (0 : ℝ) s,
      FrzMeasR (fun ω => (A1EightSeed.srcRec (D ω) (T ω) (frzDrv F p τ ω) (τ ω) κ rr p (Z ω)).W)
        (fun ω => (A1EightSeed.srcRec (D ω) (T ω) (frzDrv F p τ ω) (τ ω) κ rr p (Z ω)).W')
        (fun ω => (A1EightSeed.srcRec (D ω) (T ω) (frzDrv F p τ ω) (τ ω) κ rr p (Z ω)).a)
        (fun ω => fwdHull (frzDrv F p τ ω) (τ ω))
        (fun ω => (A1EightSeed.srcRec (D ω) (T ω) (frzDrv F p τ ω) (τ ω) κ rr p (Z ω)).φ) T G u :=
    fun u hu => frzMeasR_frzDrv hDc hDm hFc hFm hτ hτ0 hG hu.1
      (fun ω hω => A1EightSeed.ownData_imgChain (hex ω hω)) fun ω hω => ⟨hu.1, hu.2.trans (hmem ω hω)⟩
  exact measurable_seed_normEll_random_hull hs hM (markSeq_frzDrv hFc hFm hF0 hτ hτ0 G hG)
    (fun ω hω => hv ω hω _ _ (A1EightSeed.ownData_imgChain (hex ω hω))) hcl (fun _ => rfl) (fun _ => rfl) hZ
    hV₀ hG₀

end Record

end InteractingSLE.ZhanGT4.A1RectMeas
