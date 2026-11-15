/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtHLaw
import InteractingSLE.Spec.Restart.FlowStopIdentGRule

/-!
# Aux. lemma 54 for general words, part 1: the record of a stopped coupling

Packet PROVE-AUX54. Aux. lemma 54 (specification p. 246) samples the future of a stopped coupling from one fixed
reference coupling conditionally on a **record**: "Record the entire stopped driving history, including `S`, … and map
its active field to `ℍ` … The pair has exactly the same joint law in the stopped coupling and in the fixed full
reference coupling: the first marginal is the common stopped driving law, and its conditional second marginal is the
specified Gaussian kernel". As in the seed case (PROVE-LOCEXT-H, `LocalExt.recOf`) the active field is recorded as the
field itself on every test function whose support avoids the hull (no conformal transport). This file generalizes the
seed's record law from two-seed histories to **any** history space `Γ` with a hull map `A : Γ → Set ℂ` whose avoidance
events are measurable, and fixes the records of a general word:

* `fieldRecA A x y`, `recOfA A x y`: the field `x` on the test functions avoiding `A y`, and the record `(y, ·)`;
* `HasHistKernelA`: the conditional characteristic functional at every test function avoiding the recorded hull is a
  Borel functional `G φ` of the recorded history;
* **`map_recOfA_eq_of_hasHistKernelA`**: two configurations with the same history law and the same kernel functional
  have the same record law (`LocalExt.map_recOf_eq_of_hasHistKernel` with `TwoSeedHist`, `tsHull` replaced by `Γ`, `A`);
* `lowerStrict`, `stopVal`, `recH`: the history **stopped** at its recorded lifetime, read from a killed history (the
  samples before the lifetime, and the left limit of the state from the lifetime on); on the killed history of a state
  continuous on `[0, T]` it is the history of the stopped state (`recH_killedHistory`), a continuous history
  (`isContHist_recH_killedHistory`);
* `recMask`: the histories with no future (infinite lifetime, or a threshold state at the lifetime); `recHull`: the
  hull read from `recH` (everything on masked histories), with measurable avoidance events (`isMeasHull_recHull`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace Aux54

open LQGMetric LawUnique Sec4

/-! ### Records over a general history space -/

section Generic

variable {Γ : Type*} [MeasurableSpace Γ]

open Classical in
/-- **The field off the hull**: the pairing `x(ψ)` of every test function whose support avoids `A y`, `0` on the
others. -/
def fieldRecA (A : Γ → Set ℂ) (x : DistOn upperHalfPlaneOpens) (y : Γ) : TestOn upperHalfPlaneOpens → ℝ :=
  fun ψ => if Disjoint (tsupport ψ) (A y) then x ψ else 0

/-- **The record** of a field and a history: the history and the field off its hull. -/
def recOfA (A : Γ → Set ℂ) (x : DistOn upperHalfPlaneOpens) (y : Γ) : Γ × (TestOn upperHalfPlaneOpens → ℝ) :=
  (y, fieldRecA A x y)

/-- **A measurable hull map**: the avoidance event of every compact set is measurable. -/
def IsMeasHull (A : Γ → Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → MeasurableSet {y | Disjoint K (A y)}

theorem measurable_fieldRecA_apply {A : Γ → Set ℂ} (hA : IsMeasHull A) (ψ : TestOn upperHalfPlaneOpens) :
    Measurable fun p : DistOn upperHalfPlaneOpens × Γ => fieldRecA A p.1 p.2 ψ := by
  classical
  have hs : MeasurableSet {p : DistOn upperHalfPlaneOpens × Γ | Disjoint (tsupport ψ) (A p.2)} :=
    measurable_snd (hA _ ψ.hasCompactSupport.isCompact)
  exact Measurable.ite hs ((measurable_distOn_apply ψ).comp measurable_fst) measurable_const

theorem measurable_recOfA {A : Γ → Set ℂ} (hA : IsMeasHull A) :
    Measurable fun p : DistOn upperHalfPlaneOpens × Γ => recOfA A p.1 p.2 :=
  measurable_snd.prodMk (Measurable.of_eval fun ψ => measurable_fieldRecA_apply hA ψ)

omit [MeasurableSpace Γ] in
theorem fieldRecA_of_disjoint {A : Γ → Set ℂ} {x : DistOn upperHalfPlaneOpens} {y : Γ}
    {ψ : TestOn upperHalfPlaneOpens} (h : Disjoint (tsupport ψ) (A y)) : fieldRecA A x y ψ = x ψ := by
  classical
  simp only [fieldRecA, h, ↓reduceIte]

/-- **The kernel at the stop read from the recorded history**: given `m`, at every test function `φ` whose support
avoids the recorded hull `A (Y ω)`, the conditional characteristic functional of `h` is `G φ (Y ω)`. -/
def HasHistKernelA {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (m : MeasurableSpace Ω) (Y : Ω → Γ)
    (A : Γ → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (G : TestOn upperHalfPlaneOpens → Γ → ℂ) : Prop :=
  ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A (Y ω)) →
    P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | m] ω = G φ (Y ω)

/-- **A record kernel in set-integral form**: on every measurable history event avoiding `supp φ`, the tested
integral of the field is the integral of `G φ` of the history. -/
def HasSetKernel {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (Y : Ω → Γ) (A : Γ → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (G : TestOn upperHalfPlaneOpens → Γ → ℂ) : Prop :=
  ∀ (φ : TestOn upperHalfPlaneOpens) (B : Set Γ), MeasurableSet B → (∀ y ∈ B, Disjoint (tsupport φ) (A y)) →
    ∫ ω in Y ⁻¹' B, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P = ∫ ω in Y ⁻¹' B, G φ (Y ω) ∂P

/-- **On a history event avoiding `supp φ`, the kernel computes the tested integral.** -/
theorem HasHistKernelA.hasSetKernel {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ mΩ) {Y : Ω → Γ} (hY : Measurable[m] Y) {A : Γ → Set ℂ}
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) {G : TestOn upperHalfPlaneOpens → Γ → ℂ}
    (hk : HasHistKernelA P m Y A h G) : HasSetKernel P Y A h G := by
  intro φ B hB hBd
  rw [← setIntegral_condExp hm (LocalExt.integrable_cexp_field hh φ) (hY hB)]
  refine setIntegral_congr_ae ((hY.mono hm le_rfl) hB) ?_
  filter_upwards [hk φ] with ω hω hωB using hω (hBd _ hωB)

open Classical in
/-- The test functions of `F` whose supports avoid the hull recorded in `y`. -/
def avoidSetA (A : Γ → Set ℂ) (F : Finset (TestOn upperHalfPlaneOpens)) (y : Γ) :
    Finset (TestOn upperHalfPlaneOpens) :=
  F.filter fun j => Disjoint (tsupport j) (A y)

theorem measurableSet_avoidSetA_eq {A : Γ → Set ℂ} (hA : IsMeasHull A) (F J : Finset (TestOn upperHalfPlaneOpens)) :
    MeasurableSet {y : Γ | avoidSetA A F y = J} := by
  classical
  have e : {y : Γ | avoidSetA A F y = J} =
      (if J ⊆ F then univ else ∅) ∩ ⋂ j ∈ F, {y : Γ | Disjoint (tsupport j) (A y) ↔ j ∈ J} := by
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro rfl
      refine ⟨by simp only [avoidSetA, Finset.filter_subset, ↓reduceIte, mem_univ], fun j hj => ?_⟩
      simp only [avoidSetA, Finset.mem_filter, hj, true_and]
    · rintro ⟨hJ, hall⟩
      have hJF : J ⊆ F := by
        by_contra hc
        simp only [hc, ↓reduceIte, mem_empty_iff_false] at hJ
      ext j
      simp only [avoidSetA, Finset.mem_filter]
      constructor
      · rintro ⟨hj, hd⟩
        exact (hall j hj).1 hd
      · intro hj
        exact ⟨hJF hj, (hall j (hJF hj)).2 hj⟩
  rw [e]
  refine MeasurableSet.inter (by split_ifs <;> simp) (MeasurableSet.biInter F.countable_toSet fun j _ => ?_)
  have hd := hA (tsupport j) j.hasCompactSupport.isCompact
  by_cases hj : j ∈ J
  · simpa only [hj, iff_true] using hd
  · simp only [hj, iff_false]
    exact hd.compl

omit [MeasurableSpace Γ] in
/-- On the event that exactly the test functions of `J` avoid the hull, the support of `Σ_{j ∈ J} c_j φ_j` avoids it. -/
theorem disjoint_tsupport_sum_of_avoidSetA (A : Γ → Set ℂ) (F : Finset (TestOn upperHalfPlaneOpens)) (y : Γ)
    (c : TestOn upperHalfPlaneOpens → ℝ) :
    Disjoint (tsupport ⇑(∑ j ∈ avoidSetA A F y, c j • j)) (A y) := by
  classical
  refine Finset.sum_induction _ (fun φ : TestOn upperHalfPlaneOpens => Disjoint (tsupport φ) (A y)) ?_ ?_ ?_
  · intro a b ha hb
    have h1 : tsupport ⇑(a + b) ⊆ tsupport ⇑a ∪ tsupport ⇑b := by
      rw [FunLike.coe_add]
      exact tsupport_add _ _
    exact Disjoint.mono_left h1 (disjoint_union_left.2 ⟨ha, hb⟩)
  · rw [FunLike.coe_zero, tsupport_zero]
    exact Set.empty_disjoint _
  · intro j hj
    have h1 : tsupport ⇑(c j • j) ⊆ tsupport ⇑j := by
      rw [FunLike.coe_smul]
      exact tsupport_smul_subset_right (fun _ => c j) _
    exact Disjoint.mono_left h1 (Finset.mem_filter.1 hj).2

/-- **The finite-dimensional characteristic functions of a record law** on a rectangle `B × (TestOn → ℝ)`: a sum over
the subsets `J ⊆ F` of history integrals of the kernel functional at `Σ_{j ∈ J} c_j φ_j`, on the events that exactly
the members of `J` avoid the hull. -/
theorem setIntegral_map_recOfA {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : Γ → Set ℂ} (hA : IsMeasHull A) {Y : Ω → Γ} (hYm : Measurable Y)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) {G : TestOn upperHalfPlaneOpens → Γ → ℂ}
    (hG : ∀ φ, Measurable (G φ)) (hk : HasSetKernel P Y A h G) (F : Finset (TestOn upperHalfPlaneOpens))
    (c : TestOn upperHalfPlaneOpens → ℝ) {B : Set Γ} (hB : MeasurableSet B) :
    ∫ p in B ×ˢ univ, Complex.exp (((∑ j ∈ F, c j * p.2 j : ℝ) : ℂ) * Complex.I)
        ∂(P.map fun ω => recOfA A (h ω) (Y ω)) =
      ∑ J ∈ F.powerset, ∫ y in B ∩ {y | avoidSetA A F y = J}, G (∑ j ∈ J, c j • j) y ∂(P.map Y) := by
  classical
  have hrec : Measurable fun ω => recOfA A (h ω) (Y ω) := (measurable_recOfA hA).comp (hh.prodMk hYm)
  have hcm : Measurable fun p : Γ × (TestOn upperHalfPlaneOpens → ℝ) =>
      Complex.exp (((∑ j ∈ F, c j * p.2 j : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.measurable.comp ((Complex.measurable_ofReal.comp
      (Finset.measurable_sum _ fun j _ => measurable_const.mul
        ((measurable_pi_apply j).comp measurable_snd))).mul_const _)
  have hpre : (fun ω => recOfA A (h ω) (Y ω)) ⁻¹' (B ×ˢ univ) = Y ⁻¹' B := by
    ext ω
    simp [recOfA]
  rw [setIntegral_map (hB.prod MeasurableSet.univ) hcm.aestronglyMeasurable hrec.aemeasurable, hpre]
  set f : TestOn upperHalfPlaneOpens → Ω → ℂ := fun φ ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hfdef
  have hfm : ∀ φ, Measurable (f φ) := fun φ => Complex.continuous_exp.measurable.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp ((measurable_distOn_apply φ).comp hh)))
  have hAJ : ∀ J : Finset (TestOn upperHalfPlaneOpens), MeasurableSet (Y ⁻¹' {y | avoidSetA A F y = J}) :=
    fun J => hYm (measurableSet_avoidSetA_eq hA F J)
  have hpt : ∀ ω, Complex.exp (((∑ j ∈ F, c j * (recOfA A (h ω) (Y ω)).2 j : ℝ) : ℂ) * Complex.I) =
      ∑ J ∈ F.powerset, (Y ⁻¹' {y | avoidSetA A F y = J}).indicator (f (∑ j ∈ J, c j • j)) ω := by
    intro ω
    rw [Finset.sum_eq_single (avoidSetA A F (Y ω))]
    · rw [indicator_of_mem (show ω ∈ Y ⁻¹' {y | avoidSetA A F y = avoidSetA A F (Y ω)} from rfl)]
      simp only [hfdef, recOfA, fieldRecA, map_sum, map_smul, smul_eq_mul]
      rw [mul_comm Complex.I]
      congr 3
      rw [avoidSetA, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    · intro J _ hJ
      exact indicator_of_notMem (fun h' => hJ h'.symm) _
    · intro h'
      exact absurd (Finset.mem_powerset.2 (Finset.filter_subset _ _)) h'
  simp_rw [hpt]
  rw [integral_finsetSum _ fun J _ => (Integrable.of_bound (hfm _).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)).indicator (hAJ J) |>.integrableOn]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [setIntegral_indicator (hAJ J), ← preimage_inter]
  have hΓ : MeasurableSet (B ∩ {y | avoidSetA A F y = J}) := hB.inter (measurableSet_avoidSetA_eq hA F J)
  rw [hk _ _ hΓ fun y hy => by
      rw [← hy.2]; exact disjoint_tsupport_sum_of_avoidSetA A F y c,
    ← setIntegral_map hΓ (hG _).aestronglyMeasurable hYm.aemeasurable]

/-- **Aux. lemma 54's record law** (specification p. 246, "the first marginal is the common stopped driving law, and
its conditional second marginal is the specified Gaussian kernel"): two configurations whose fields have the same
kernel functional `G` of their recorded histories, and whose histories have the same law, have the same record law. -/
theorem map_recOfA_eq_of_hasSetKernel {Ω₁ Ω₂ : Type*} [mΩ₁ : MeasurableSpace Ω₁] [mΩ₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsFiniteMeasure P₁] [IsFiniteMeasure P₂] {A : Γ → Set ℂ}
    (hA : IsMeasHull A) {Y₁ : Ω₁ → Γ} {Y₂ : Ω₂ → Γ} (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂)
    {h₁ : Ω₁ → DistOn upperHalfPlaneOpens} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) {G : TestOn upperHalfPlaneOpens → Γ → ℂ} (hG : ∀ φ, Measurable (G φ))
    (hk₁ : HasSetKernel P₁ Y₁ A h₁ G) (hk₂ : HasSetKernel P₂ Y₂ A h₂ G) (hlaw : P₁.map Y₁ = P₂.map Y₂) :
    P₁.map (fun ω => recOfA A (h₁ ω) (Y₁ ω)) = P₂.map (fun ω => recOfA A (h₂ ω) (Y₂ ω)) := by
  refine LocalExt.measure_eq_of_setIntegral_cexp_pi fun F c B hB => ?_
  rw [setIntegral_map_recOfA hA hY₁ hh₁ hG hk₁ F c hB, setIntegral_map_recOfA hA hY₂ hh₂ hG hk₂ F c hB, hlaw]

end Generic

/-! ### The history stopped at its recorded lifetime -/

section Hist

variable {nL nR : ℕ}

/-- Dyadic times strictly below `t > 0` at level `n`: the dyadic time at or below `t − 2⁻ⁿ`. -/
def lowerStrict (t : ℝ≥0) (n : ℕ) : ℕ × ℕ := lowerDyadic (t - 1 / 2 ^ n) n

theorem dyadicTime_lowerStrict_lt {t : ℝ≥0} (ht : 0 < t) (n : ℕ) : dyadicTime (lowerStrict t n) < t :=
  lt_of_le_of_lt (dyadicTime_lowerDyadic_le _ n) (tsub_lt_self ht (by positivity))

theorem tendsto_dyadicTime_lowerStrict (t : ℝ≥0) :
    Tendsto (fun n => dyadicTime (lowerStrict t n)) atTop (𝓝 t) := by
  have hlo : Tendsto (fun n : ℕ => t - 1 / 2 ^ n - 1 / 2 ^ n) atTop (𝓝 t) := by
    simpa only [tsub_zero] using (tendsto_const_nhds.sub tendsto_one_div_two_pow).sub tendsto_one_div_two_pow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds (fun n => ?_) (fun n => ?_)
  · exact tsub_le_iff_right.2 (le_dyadicTime_lowerDyadic_add _ n)
  · exact (dyadicTime_lowerDyadic_le _ n).trans tsub_le_self

/-- The initial state `(0, xL, xR)` of the word. -/
def initVal (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : DrivingValue nL nR := (0, xL, xR)

open Classical in
/-- **The state at the recorded lifetime**: the initial state at lifetime `0`, else the limit of the samples at the
dyadic times strictly below the lifetime. -/
def stopVal (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (γ : HistorySpace nL nR) : DrivingValue nL nR :=
  if γ.1 = 0 then initVal xL xR else limUnder atTop fun n => γ.2 (lowerStrict γ.1.toNNReal n)

theorem measurable_stopVal (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Measurable (stopVal xL xR) := by
  classical
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const ?_
  exact (StronglyMeasurable.limUnder fun n => (measurable_sample_comp (measurable_lowerDyadic_comp
    (measurable_histStop.sub measurable_const) n)).stronglyMeasurable).measurable

open Classical in
/-- **The history stopped at its recorded lifetime**: the samples before the lifetime and the state at the lifetime
(`stopVal`) from the lifetime on. -/
def recH (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (γ : HistorySpace nL nR) : HistorySpace nL nR :=
  (γ.1, fun p => if (dyadicTime p : ℝ≥0∞) < γ.1 then γ.2 p else stopVal xL xR γ)

theorem measurable_recH (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Measurable (recH xL xR) := by
  classical
  refine measurable_fst.prodMk (Measurable.of_eval fun p => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_pi_apply p).comp measurable_snd) (measurable_stopVal xL xR)

/-- **A history whose samples up to its finite stop come from a continuous state** reads that state: driver
`f (t ∧ T)`, force coordinates `f T`. -/
theorem histRead_of_eq {γ : HistorySpace nL nR} {T : ℝ≥0} (hT : γ.1 = T) {f : ℝ≥0 → DrivingValue nL nR}
    (hf : Continuous f) (hγ : ∀ p, dyadicTime p ≤ T → γ.2 p = f (dyadicTime p)) :
    IsContHist γ ∧ (∀ t, histPath γ t = (f (min t T)).1) ∧ (∀ i, histVL γ i = (f T).2.1 i) ∧
      ∀ i, histVR γ i = (f T).2.2 i := by
  have hS : γ.1.toNNReal = T := by rw [hT]; rfl
  have key : ∀ r : ℝ≥0, r ≤ T → Tendsto (fun n => γ.2 (lowerDyadic r n)) atTop (𝓝 (f r)) := by
    intro r hr
    have h1 : Tendsto (fun n => f (dyadicTime (lowerDyadic r n))) atTop (𝓝 (f r)) :=
      (hf.tendsto r).comp (tendsto_dyadicTime_lowerDyadic r)
    exact h1.congr fun n => (hγ _ ((dyadicTime_lowerDyadic_le r n).trans hr)).symm
  refine ⟨⟨by rw [hT]; exact ENNReal.coe_ne_top, f, hf, fun p hp => hγ p (hS ▸ hp)⟩, fun t => ?_, fun i => ?_,
    fun i => ?_⟩
  · show limUnder atTop (fun n => (γ.2 (lowerDyadic (min t γ.1.toNNReal) n)).1) = _
    rw [hS]
    exact Tendsto.limUnder_eq ((continuous_fst.tendsto _).comp (key _ (min_le_right _ _)))
  · show limUnder atTop (fun n => (γ.2 (lowerDyadic γ.1.toNNReal n)).2.1 i) = _
    rw [hS]
    exact Tendsto.limUnder_eq ((((continuous_apply i).comp continuous_fst).tendsto _).comp
      ((continuous_snd.tendsto _).comp (key _ le_rfl)))
  · show limUnder atTop (fun n => (γ.2 (lowerDyadic γ.1.toNNReal n)).2.2 i) = _
    rw [hS]
    exact Tendsto.limUnder_eq ((((continuous_apply i).comp continuous_snd).tendsto _).comp
      ((continuous_snd.tendsto _).comp (key _ le_rfl)))

section Killed

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {ω : Ω} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- The driving state of `(W, V^L, V^R)` at a time. -/
def dState (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) :
    DrivingValue nL nR :=
  (W t ω, fun i => VL i t ω, fun j => VR j t ω)

/-- **The state at the recorded lifetime of a killed history** of a state continuous on `[0, T]` started at the
initial state. -/
theorem stopVal_killedHistory {T : ℝ≥0} (hT : (T : ℝ≥0∞) = e ω) (hc : ContinuousOn (dState W VL VR ω) (Iic T))
    (h0 : dState W VL VR ω 0 = initVal xL xR) :
    stopVal xL xR (killedHistory W VL VR e ω) = dState W VL VR ω T := by
  classical
  by_cases hT0 : T = 0
  · subst hT0
    have : (killedHistory W VL VR e ω).1 = 0 := by simp only [killedHistory, ← hT, ENNReal.coe_zero]
    simp only [stopVal, this, ↓reduceIte, h0]
  have hTpos : 0 < T := pos_iff_ne_zero.2 hT0
  have hne : (killedHistory W VL VR e ω).1 ≠ 0 := by
    simp only [killedHistory, ← hT, ne_eq, ENNReal.coe_eq_zero]
    exact hT0
  have hS : (killedHistory W VL VR e ω).1.toNNReal = T := by simp only [killedHistory, ← hT, ENNReal.toNNReal_coe]
  simp only [stopVal, hne, ↓reduceIte, hS]
  refine Tendsto.limUnder_eq ?_
  have hlim : Tendsto (fun n => dyadicTime (lowerStrict T n)) atTop (𝓝[Iic T] T) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicTime_lowerStrict T,
      Eventually.of_forall fun n => (dyadicTime_lowerStrict_lt hTpos n).le⟩
  refine ((hc T self_mem_Iic).tendsto.comp hlim).congr fun n => ?_
  have hlt : (dyadicTime (lowerStrict T n) : ℝ≥0∞) < e ω := by
    rw [← hT]; exact ENNReal.coe_lt_coe.2 (dyadicTime_lowerStrict_lt hTpos n)
  simp only [Function.comp_apply, killedHistory, hlt, ↓reduceIte, dState]

/-- **The stopped history read from a killed history** of a state continuous on `[0, T]` started at the initial state:
the samples of the stopped state `t ↦ X(t ∧ T)`. -/
theorem recH_killedHistory_snd {T : ℝ≥0} (hT : (T : ℝ≥0∞) = e ω) (hc : ContinuousOn (dState W VL VR ω) (Iic T))
    (h0 : dState W VL VR ω 0 = initVal xL xR) (p : ℕ × ℕ) :
    (recH xL xR (killedHistory W VL VR e ω)).2 p = dState W VL VR ω (min (dyadicTime p) T) := by
  classical
  have h1 : (killedHistory W VL VR e ω).1 = e ω := rfl
  by_cases hp : (dyadicTime p : ℝ≥0∞) < e ω
  · have hpT : dyadicTime p ≤ T := by rw [← hT] at hp; exact (ENNReal.coe_lt_coe.1 hp).le
    simp only [recH, hp, ↓reduceIte, killedHistory, min_eq_left hpT, dState]
  · have hpT : T ≤ dyadicTime p := by rw [← hT, not_lt] at hp; exact ENNReal.coe_le_coe.1 hp
    simp only [recH, h1, hp, ↓reduceIte, min_eq_right hpT]
    exact stopVal_killedHistory hT hc h0

theorem recH_fst (γ : HistorySpace nL nR) : (recH xL xR γ).1 = γ.1 := rfl

/-- **The stopped history of a continuous state is a continuous history**, whose driver is `W(t ∧ T)` and whose force
coordinates are those at `T`. -/
theorem recH_killedHistory_read {T : ℝ≥0} (hT : (T : ℝ≥0∞) = e ω) (hc : ContinuousOn (dState W VL VR ω) (Iic T))
    (h0 : dState W VL VR ω 0 = initVal xL xR) :
    IsContHist (recH xL xR (killedHistory W VL VR e ω)) ∧
      (∀ t, histPath (recH xL xR (killedHistory W VL VR e ω)) t = W (min t T) ω) ∧
      (∀ i, histVL (recH xL xR (killedHistory W VL VR e ω)) i = VL i T ω) ∧
      ∀ i, histVR (recH xL xR (killedHistory W VL VR e ω)) i = VR i T ω := by
  have hf : Continuous fun t => dState W VL VR ω (min t T) :=
    hc.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t T
  obtain ⟨h1, h2, h3, h4⟩ := histRead_of_eq (γ := recH xL xR (killedHistory W VL VR e ω)) (T := T) hT.symm hf
    fun p _ => recH_killedHistory_snd hT hc h0 p
  refine ⟨h1, fun t => ?_, fun i => ?_, fun i => ?_⟩
  · rw [h2, min_assoc, min_self]; rfl
  · rw [h3, min_self]; rfl
  · rw [h4, min_self]; rfl

/-- **The hull read from the stopped history of a continuous state** is the closure in `ℍ` of the hull at `T` of the
driver, when the driver is continuous on `[0, T']` for some `T' > T`. -/
theorem regHull_recH_killedHistory {T T' : ℝ≥0} (hT : (T : ℝ≥0∞) = e ω)
    (hc : ContinuousOn (dState W VL VR ω) (Iic T)) (h0 : dState W VL VR ω 0 = initVal xL xR) (hTT' : T < T')
    (hw : ContinuousOn (fun t => W t ω) (Iic T')) :
    regHull (recH xL xR (killedHistory W VL VR e ω)) =
      closure (fwdHull (fun r : ℝ => W r.toNNReal ω) T) ∩ (upperHalfPlaneOpens : Set ℂ) := by
  obtain ⟨hC, hpath, -, -⟩ := recH_killedHistory_read hT hc h0
  have hS : (recH xL xR (killedHistory W VL VR e ω)).1.toNNReal = T := by
    simp only [recH, killedHistory, ← hT, ENNReal.toNNReal_coe]
  rw [hC.regHull_eq, histHull, hS]
  congr 2
  have hdr : histDrive (recH xL xR (killedHistory W VL VR e ω)) = fun r : ℝ => W (min r.toNNReal T) ω := by
    funext r
    exact hpath r.toNNReal
  rw [hdr]
  set V : ℝ → ℝ := fun r => W (min r.toNNReal T') ω with hVdef
  have hVc : Continuous V :=
    (hw.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t T').comp
      continuous_real_toNNReal
  have hWT : Continuous fun r : ℝ => W (min r.toNNReal T) ω := by
    have h1 : ContinuousOn (fun t => W t ω) (Iic T) := hw.mono (Iic_subset_Iic.2 hTT'.le)
    exact (h1.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t T).comp
      continuous_real_toNNReal
  have e1 : fwdHull (fun r : ℝ => W r.toNNReal ω) T = fwdHull V T := by
    refine InteractingSLE.fwdHull_eq_of_eqOn T.coe_nonneg (by exact_mod_cast hTT') fun r hr => ?_
    simp only [hVdef]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]
  rw [e1]
  refine (YuanCorollary13.fwdHull_eq_of_eqOn_Icc hVc hWT T.coe_nonneg fun r hr => ?_).symm
  have hrT : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hr.2
  simp only [hVdef]
  rw [min_eq_left (hrT.trans hTT'.le), min_eq_left hrT]

end Killed

/-! ### Histories with no future, and the recorded hull -/

/-- **Histories with no future**: an infinite lifetime, or a threshold state at the lifetime. -/
def recMask (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (γ : HistorySpace nL nR) :
    Prop :=
  γ.1 = ⊤ ∨ ForceWord.ThresholdCondition ρL ρR (stopVal xL xR γ).1 (stopVal xL xR γ).2.1 (stopVal xL xR γ).2.2

theorem measurableSet_threshold (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    MeasurableSet {s : DrivingValue nL nR | ForceWord.ThresholdCondition ρL ρR s.1 s.2.1 s.2.2} := by
  have e : {s : DrivingValue nL nR | ForceWord.ThresholdCondition ρL ρR s.1 s.2.1 s.2.2} =
      ⋃ m, FlowStopIdentG.thrSet ρL ρR m := by
    ext s
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun h => FlowStopIdentG.exists_mem_thrSet h, fun ⟨m, hm⟩ =>
      FlowStopIdentG.thresholdCondition_of_mem_thrSet hm⟩
  rw [e]
  exact MeasurableSet.iUnion fun m => (FlowStopIdentG.isClosed_thrSet ρL ρR m).measurableSet

theorem measurableSet_recMask (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    MeasurableSet {γ : HistorySpace nL nR | recMask ρL ρR xL xR γ} :=
  (measurableSet_eq_fun measurable_fst measurable_const).union
    ((measurable_stopVal xL xR) (measurableSet_threshold ρL ρR))

open Classical in
/-- **The recorded hull**: everything on a history with no future, else the hull read from the stopped history. -/
def recHull (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (γ : HistorySpace nL nR) :
    Set ℂ :=
  if recMask ρL ρR xL xR γ then univ else regHull (recH xL xR γ)

theorem isMeasHull_recHull (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    IsMeasHull (recHull ρL ρR xL xR) := by
  classical
  intro K hK
  have e : {γ : HistorySpace nL nR | Disjoint K (recHull ρL ρR xL xR γ)} =
      ({γ | recMask ρL ρR xL xR γ} ∩ {_γ | Disjoint K (univ : Set ℂ)}) ∪
        ({γ | recMask ρL ρR xL xR γ}ᶜ ∩ recH xL xR ⁻¹' {γ | Disjoint K (regHull γ)}) := by
    ext γ
    by_cases hm : recMask ρL ρR xL xR γ <;> simp [recHull, hm]
  rw [e]
  exact ((measurableSet_recMask ρL ρR xL xR).inter (MeasurableSet.const _)).union
    ((measurableSet_recMask ρL ρR xL xR).compl.inter
      ((measurable_recH xL xR) (measurableSet_disjoint_regHull hK)))

theorem recHull_of_not_mask {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {γ : HistorySpace nL nR} (h : ¬ recMask ρL ρR xL xR γ) : recHull ρL ρR xL xR γ = regHull (recH xL xR γ) := by
  classical
  simp only [recHull, h, ↓reduceIte]

end Hist

end Aux54

end Restart

end InteractingSLE
