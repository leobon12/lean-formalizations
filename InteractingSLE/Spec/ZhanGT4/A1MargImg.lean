/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MargHit
import InteractingSLE.Spec.ZhanGT4.A1MargClock
import InteractingSLE.Spec.ZhanGT4.A1RefCond
import InteractingSLE.Spec.Sec7.SideHeightRange

/-!
# (m3)–(m4): the canonical image of A.1 is measurable jointly in the stop and the sample

Packet PROVE-A1-MARG (R76). Clauses (m3)–(m4) of `A1Core.IsRectImageCore`: the masked canonical image driver (at each
image time) and the masked canonical image lifetime are measurable functions of the stop of the conditioning curve and
the sample. The canonical image (`A1Ref.imgClk`, `imgDrv`, `imgLife`) is choice-defined; it is reduced
(`A1MargClock.lean`) to countably many quantities of the frozen-hull calculus of A.1, whose measurability is A13's
`FrzMeasR` (for any continuous drivers, `A1MargHit.lean`):

* the pre-contact events `G d = {live, d < contactTime}` (`measurableSet_preContact`): two random compact sets meet iff
  some dyadic square meets both at every level (`inter_nonempty_iff_dyadic`), and the closures of the two hulls are
  dyadic-hit measurable (`isDyadicHitMeasurable_closure_of_hits`);
* on `G d`: the clock `imgClk d` (through `hcap(g^{(j)}_d(K_k(τ)))`, `measurable_clock`) and `F d = imgDrv (imgClk d)`
  (through `frzA … 0 d`, `measurable_drvAtClock`);
* **`measurable_canonImgLife`**: the lifetime is a countable supremum of clocks;
* **`measurable_canonImgDrv`**: the driver at image time `σ` is the limit of `F` along the dyadic search inverting the
  clock (`A1MargClock.tendsto_dySearch`).

The setting is a general measurable space `Ω` carrying the two drivers, the stop `τ` and a measurable live event on
which the stop precedes the conditioning curve's lifetime; the inputs are the measurability of the evaluations and of
the compact hits of the two hulls (supplied on path spaces by `A1MargHit.measurableSet_hit_stop`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Marg

open QuantumZipper (H fwdHull)
open A2X A1Ref ConformalImage

/-! ### Random compact sets -/

section RandomSet

variable {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ}

/-- **Open hits from compact hits**: if the hits of a random set by compact subsets of `ℍ` are events, so are its hits
by open subsets of `ℍ` (countably many rational closed balls). -/
theorem measurableSet_open_hit
    (hA : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ A ω).Nonempty}) {U : Set ℂ} (hU : IsOpen U)
    (hUH : U ⊆ H) : MeasurableSet {ω | (A ω ∩ U).Nonempty} := by
  set e := TopologicalSpace.denseSeq ℂ with he
  have heq : {ω | (A ω ∩ U).Nonempty} = ⋃ j : ℕ, ⋃ k : ℕ, ⋃ (_ : closedBall (e j) (1 / ((k : ℝ) + 1)) ⊆ U),
      {ω | (closedBall (e j) (1 / ((k : ℝ) + 1)) ∩ A ω).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨z, hzA, hzU⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨j, hj⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z _
        (Nat.one_div_pos_of_nat (n := k))
      refine ⟨j, k, fun w hw => hball ?_, z, ?_, hzA⟩
      · rw [mem_ball]
        rw [mem_closedBall] at hw
        calc dist w z ≤ dist w (e j) + dist (e j) z := dist_triangle _ _ _
          _ < ε := by rw [dist_comm (e j) z]; linarith
      · rw [mem_closedBall]; exact hj.le
    · rintro ⟨j, k, hsub, z, hzB, hzA⟩
      exact ⟨z, hzA, hsub hzB⟩
  rw [heq]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hsub =>
    hA _ (isCompact_closedBall _ _) (hsub.trans hUH)

/-- **The closure of a random subset of `ℍ` with measurable compact hits is dyadic-hit measurable.** -/
theorem isDyadicHitMeasurable_closure_of_hits
    (hA : ∀ L : Set ℂ, IsCompact L → L ⊆ H → MeasurableSet {ω | (L ∩ A ω).Nonempty}) (hAH : ∀ ω, A ω ⊆ H) :
    Restart.IsDyadicHitMeasurable fun ω => closure (A ω) := by
  intro n k
  have e : {ω | (Restart.dyadicSquare n k ∩ closure (A ω)).Nonempty} =
      ⋂ m : ℕ, {ω | (A ω ∩ (thickening (1 / ((m : ℝ) + 1)) (Restart.dyadicSquare n k) ∩ H)).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter,
      Sec7.SideHeight.nonempty_inter_closure_iff (Restart.isCompact_dyadicSquare n k)]
    exact forall_congr' fun m => ⟨fun ⟨z, hz, hzQ⟩ => ⟨z, hz, hzQ, hAH ω hz⟩, fun ⟨z, hz, hzQ, _⟩ => ⟨z, hz, hzQ⟩⟩
  rw [e]
  exact MeasurableSet.iInter fun m =>
    measurableSet_open_hit hA (isOpen_thickening.inter QuantumZipper.isOpen_H) inter_subset_right

/-- **Two compact sets meet iff at every level some dyadic square meets both.** -/
theorem inter_nonempty_iff_dyadic {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁) (h₂ : IsClosed K₂) :
    (K₁ ∩ K₂).Nonempty ↔ ∀ n : ℕ, ∃ k : ℤ × ℤ,
      (Restart.dyadicSquare n k ∩ K₁).Nonempty ∧ (Restart.dyadicSquare n k ∩ K₂).Nonempty := by
  constructor
  · rintro ⟨z, hz1, hz2⟩ n
    exact ⟨_, ⟨z, Restart.mem_dyadicSquare_indexOf n z, hz1⟩, ⟨z, Restart.mem_dyadicSquare_indexOf n z, hz2⟩⟩
  · intro h
    obtain ⟨k₀, ⟨a₀, -, ha₀⟩, ⟨b₀, -, hb₀⟩⟩ := h 0
    obtain ⟨a, ha, hmin⟩ := h₁.exists_isMinOn ⟨a₀, ha₀⟩ (continuous_infDist_pt K₂).continuousOn
    have hle : ∀ n : ℕ, infDist a K₂ ≤ 2 / 2 ^ n := fun n => by
      obtain ⟨k, ⟨a', ha'Q, ha'⟩, ⟨b', hb'Q, hb'⟩⟩ := h n
      calc infDist a K₂ ≤ infDist a' K₂ := isMinOn_iff.1 hmin a' ha'
        _ ≤ dist a' b' := infDist_le_dist_of_mem hb'
        _ = ‖a' - b'‖ := dist_eq_norm _ _
        _ ≤ 2 / 2 ^ n := Restart.norm_sub_le_of_mem_dyadicSquare ha'Q hb'Q
    have h0 : infDist a K₂ = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) infDist_nonneg
      obtain ⟨n, hn⟩ := Restart.exists_lt_two_div_pow hε
      linarith [hle n]
    refine ⟨a, ha, ?_⟩
    rw [← h₂.closure_eq]
    exact (mem_closure_iff_infDist_zero ⟨b₀, hb₀⟩).2 h0

/-- The event that two random compact sets with dyadic hits meet. -/
theorem measurableSet_inter_nonempty {K₁ K₂ : Ω → Set ℂ} (h₁ : Restart.IsDyadicHitMeasurable K₁)
    (h₂ : Restart.IsDyadicHitMeasurable K₂) (hc₁ : ∀ ω, IsCompact (K₁ ω)) (hc₂ : ∀ ω, IsClosed (K₂ ω)) :
    MeasurableSet {ω | (K₁ ω ∩ K₂ ω).Nonempty} := by
  have e : {ω | (K₁ ω ∩ K₂ ω).Nonempty} = ⋂ n : ℕ, ⋃ k : ℤ × ℤ,
      {ω | (Restart.dyadicSquare n k ∩ K₁ ω).Nonempty} ∩ {ω | (Restart.dyadicSquare n k ∩ K₂ ω).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    exact inter_nonempty_iff_dyadic (hc₁ ω) (hc₂ ω)
  rw [e]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun k => (h₁ n k).inter (h₂ n k)

end RandomSet

/-! ### Hulls of curves started off `0` -/

section Phys

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Hits of the hull of a curve started at `x` are hits of the centred hull by the translated compact set. -/
theorem hit_physHull_iff (x : ℝ) (w : ℝ → ℝ) (s : ℝ) (K : Set ℂ) :
    (K ∩ physHull x w s).Nonempty ↔ ((fun z : ℂ => z - x) '' K ∩ fwdHull w s).Nonempty := by
  constructor
  · rintro ⟨_, hzK, z, hz, rfl⟩
    exact ⟨z, ⟨z + x, hzK, by ring⟩, hz⟩
  · rintro ⟨_, ⟨z, hzK, rfl⟩, hz⟩
    exact ⟨z, hzK, z - x, hz, by ring⟩

theorem isCompact_image_sub {K : Set ℂ} (hK : IsCompact K) (x : ℝ) :
    IsCompact ((fun z : ℂ => z - x) '' K) :=
  hK.image (continuous_id.sub continuous_const)

theorem image_sub_subset_H {K : Set ℂ} (hKH : K ⊆ H) (x : ℝ) : (fun z : ℂ => z - x) '' K ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  show 0 < (z - (x : ℂ)).im
  have h' : 0 < z.im := hKH hz
  simpa using h'

/-- A random set masked by an event: `B ω` on `E`, empty off it. -/
def maskSet (E : Set Ω) (B : Ω → Set ℂ) (ω : Ω) : Set ℂ := {z | ω ∈ E ∧ z ∈ B ω}

omit [MeasurableSpace Ω] in
theorem maskSet_of_mem {E : Set Ω} {B : Ω → Set ℂ} {ω : Ω} (hω : ω ∈ E) : maskSet E B ω = B ω := by
  ext z; simp [maskSet, hω]

omit [MeasurableSpace Ω] in
theorem maskSet_of_notMem {E : Set Ω} {B : Ω → Set ℂ} {ω : Ω} (hω : ω ∉ E) : maskSet E B ω = ∅ := by
  ext z; simp [maskSet, hω]

omit [MeasurableSpace Ω] in
theorem maskSet_subset {E : Set Ω} {B : Ω → Set ℂ} (ω : Ω) : maskSet E B ω ⊆ B ω := fun _ hz => hz.2

/-- Compact hits of the (masked) hull of a curve started at `x`. -/
theorem measurableSet_hit_physHull_mask {E : Set Ω} {w : Ω → ℝ → ℝ} {s : Ω → ℝ} (x : ℝ)
    (h : ∀ K : Set ℂ, IsCompact K → K ⊆ H → MeasurableSet {ω | ω ∈ E ∧ (K ∩ fwdHull (w ω) (s ω)).Nonempty})
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    MeasurableSet {ω | (K ∩ maskSet E (fun ω => physHull x (w ω) (s ω)) ω).Nonempty} := by
  have e : {ω | (K ∩ maskSet E (fun ω => physHull x (w ω) (s ω)) ω).Nonempty} =
      {ω | ω ∈ E ∧ ((fun z : ℂ => z - x) '' K ∩ fwdHull (w ω) (s ω)).Nonempty} := by
    ext ω
    by_cases hω : ω ∈ E
    · simp only [maskSet_of_mem hω, hω, mem_ofPred_eq, true_and, hit_physHull_iff]
    · simp only [maskSet_of_notMem hω, hω, inter_empty, Set.not_nonempty_empty, mem_ofPred_eq, false_and]
  rw [e]
  exact h _ (isCompact_image_sub hK x) (image_sub_subset_H hKH x)

end Phys

/-! ### The standing hypotheses on the two drivers -/

section Canon

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The standing hypotheses** for the canonical image of curve `j` (driver `wj`, lifetime `ζj`) at the stop `τ` of
curve `k` (driver `wk`, lifetime `ζk`) on the live event `L`: continuity before the lifetimes and zero start at every
sample, the stop before `ζk` on `L`, measurable evaluations of `wj`, measurable `ζj`, `τ`, and measurable compact hits
of the hull of curve `j` at deterministic times and of curve `k` at the stop (on `L`). -/
structure CanonHyp (L : Set Ω) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (ζk : Ω → ℝ≥0∞)
    (τ : Ω → ℝ≥0) : Prop where
  meas : MeasurableSet L
  life : ∀ ω ∈ L, (τ ω : ℝ≥0∞) < ζk ω
  contj : ∀ ω, ContinuousOn (wj ω) {t | (t : ℝ≥0∞) < ζj ω}
  zeroj : ∀ ω, wj ω 0 = 0
  contk : ∀ ω, ContinuousOn (wk ω) {t | (t : ℝ≥0∞) < ζk ω}
  zerok : ∀ ω, wk ω 0 = 0
  measj : ∀ t, Measurable fun ω => wj ω t
  measζj : Measurable ζj
  measτ : Measurable τ
  hitj : ∀ (q : ℝ≥0) (K : Set ℂ), IsCompact K → K ⊆ H →
    MeasurableSet {ω | (q : ℝ≥0∞) < ζj ω ∧ (K ∩ fwdHull (Strip.extPath (wj ω)) q).Nonempty}
  hitk : ∀ K : Set ℂ, IsCompact K → K ⊆ H →
    MeasurableSet {ω | ω ∈ L ∧ (K ∩ fwdHull (Strip.extPath (wk ω)) (τ ω)).Nonempty}

variable {L : Set Ω} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ} {ζk : Ω → ℝ≥0∞}
  {τ : Ω → ℝ≥0}

namespace CanonHyp

variable (hC : CanonHyp L wj ζj wk ζk τ)
include hC

theorem regj (ω : Ω) : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T) :=
  fun _ hT => continuousOn_extPath_Icc (hC.contj ω) hT

theorem regj0 (ω : Ω) : Strip.extPath (wj ω) 0 = 0 := by
  simp only [Strip.extPath, Real.toNNReal_zero, hC.zeroj ω]

theorem regk {ω : Ω} (hω : ω ∈ L) :
    ∃ τ' : ℝ, (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ') :=
  exists_continuousOn_extPath_beyond (hC.contk ω) (hC.life ω hω)

theorem regk0 (ω : Ω) : Strip.extPath (wk ω) 0 = 0 := by
  simp only [Strip.extPath, Real.toNNReal_zero, hC.zerok ω]

/-- The clock is continuous and strictly increasing before the contact time, `0` at `0` (live samples). -/
theorem clock_props {xj xk : ℝ} {ω : Ω} (hω : ω ∈ L) :
    imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) 0 = 0 ∧
    ContinuousOn (imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω))
      {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)} ∧
    StrictMonoOn (imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω))
      {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)} :=
  have h := isImageChainUpTo_canonical (hC.regj ω) (hC.regj0 ω) (hC.regk hω) (hC.regk0 ω) (τ ω).coe_nonneg 0
  ⟨h.1, h.2.1, h.2.2.1⟩

/-- Compact hits of the hull of curve `j` (started at `x`) at a deterministic time `q`, masked by `q < ζj`. -/
theorem measurableSet_hit_j (x : ℝ) (q : ℝ≥0) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    MeasurableSet {ω | (K ∩ maskSet {ω | (q : ℝ≥0∞) < ζj ω}
      (fun ω => physHull x (Strip.extPath (wj ω)) (q : ℝ)) ω).Nonempty} :=
  measurableSet_hit_physHull_mask (E := {ω | (q : ℝ≥0∞) < ζj ω}) (w := fun ω => Strip.extPath (wj ω))
    (s := fun _ => (q : ℝ)) x (fun K hK hKH => hC.hitj q K hK hKH) hK hKH

/-- Compact hits of the hull of curve `k` (started at `x`) at the stop, masked by the live event. -/
theorem measurableSet_hit_k (x : ℝ) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    MeasurableSet {ω | (K ∩ maskSet L (fun ω => physHull x (Strip.extPath (wk ω)) (τ ω)) ω).Nonempty} :=
  measurableSet_hit_physHull_mask (E := L) (w := fun ω => Strip.extPath (wk ω)) (s := fun ω => (τ ω : ℝ)) x
    (fun K hK hKH => hC.hitk K hK hKH) hK hKH

end CanonHyp

end Canon

/-! ### The pre-contact events and the frozen-hull data on them -/

section PreContact

variable {Ω : Type*} [MeasurableSpace Ω] {L : Set Ω} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞}
  {wk : Ω → ℝ≥0 → ℝ} {ζk : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0}

/-- The contact time of curve `j` with the hull of curve `k` at the stop. -/
def cT (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)

/-- **The pre-contact event** at the own time `d` of curve `j`: live, and `d` before the contact time. -/
def preC (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0)
    (d : ℝ) : Set Ω :=
  {ω | ω ∈ L ∧ ENNReal.ofReal d < cT xj xk wj ζj wk τ ω}

omit [MeasurableSpace Ω] in
theorem preC_subset (xj xk : ℝ) (d : ℝ) : preC L xj xk wj ζj wk τ d ⊆ L := fun _ h => h.1

theorem physHull_subset_H (x : ℝ) (w : ℝ → ℝ) (s : ℝ) : physHull x w s ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  show 0 < (z + (x : ℂ)).im
  have h' : 0 < z.im := QuantumZipper.fwdHull_mono.2 s hz
  simpa using h'

namespace CanonHyp

variable (hC : CanonHyp L wj ζj wk ζk τ)
include hC

/-- **The pre-contact events are measurable.** -/
theorem measurableSet_preC (xj xk : ℝ) {d : ℝ} (hd : 0 ≤ d) : MeasurableSet (preC L xj xk wj ζj wk τ d) := by
  set K₁ : ℚ → Ω → Set ℂ := fun q ω => closure (maskSet {ω | ((q : ℝ).toNNReal : ℝ≥0∞) < ζj ω}
    (fun ω => physHull xj (Strip.extPath (wj ω)) (((q : ℝ).toNNReal : ℝ≥0) : ℝ)) ω) with hK₁
  set K₂ : Ω → Set ℂ := fun ω => closure (maskSet L (fun ω => physHull xk (Strip.extPath (wk ω)) (τ ω)) ω)
    with hK₂
  have heq : preC L xj xk wj ζj wk τ d = L ∩ ⋃ q : ℚ, ⋃ (_ : d < q),
      {ω | ENNReal.ofReal q < ζj ω} ∩ {ω | (K₁ q ω ∩ K₂ ω).Nonempty}ᶜ := by
    ext ω
    simp only [preC, cT, mem_ofPred_eq, mem_inter_iff, mem_iUnion, ofReal_lt_contactTime_iff hd, exists_prop,
      mem_compl_iff]
    refine and_congr_right fun hω => exists_congr fun q => and_congr_right fun hdq =>
      and_congr_right fun hqζ => ?_
    have hq0 : (0 : ℝ) ≤ q := hd.trans hdq.le
    have h1 : ω ∈ {ω | ((q : ℝ).toNNReal : ℝ≥0∞) < ζj ω} := hqζ
    simp only [hK₁, hK₂, maskSet_of_mem h1, maskSet_of_mem hω, Real.coe_toNNReal _ hq0]
  rw [heq]
  refine hC.meas.inter (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    (measurableSet_lt measurable_const hC.measζj).inter (MeasurableSet.compl ?_))
  refine measurableSet_inter_nonempty
    (isDyadicHitMeasurable_closure_of_hits (fun K hK hKH => hC.measurableSet_hit_j xj _ hK hKH)
      fun ω => (maskSet_subset ω).trans (physHull_subset_H _ _ _))
    (isDyadicHitMeasurable_closure_of_hits (fun K hK hKH => hC.measurableSet_hit_k xk hK hKH)
      fun ω => (maskSet_subset ω).trans (physHull_subset_H _ _ _)) (fun ω => ?_) fun ω => isClosed_closure
  by_cases hω : ω ∈ {ω | ((q : ℝ).toNNReal : ℝ≥0∞) < ζj ω}
  · simp only [hK₁, maskSet_of_mem hω]
    obtain ⟨τ', h1, h2⟩ := exists_continuousOn_extPath_beyond (hC.contj ω) hω
    exact (isHPHull_physHull_loc (x := xj) (NNReal.coe_nonneg _) ⟨τ', h1, h2⟩).2.1.isCompact_closure
  · simp only [hK₁, maskSet_of_notMem hω, closure_empty]
    exact isCompact_empty

end CanonHyp

end PreContact

/-! ### The clock and the driver at the clock, on the pre-contact events -/

section Frozen

variable {Ω : Type*} [MeasurableSpace Ω] {L : Set Ω} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞}
  {wk : Ω → ℝ≥0 → ℝ} {ζk : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0}

/-- The canonical clock at the own time `d` (frame of curve `j` started at `xj`). -/
def clkAt (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (d : ℝ) (ω : Ω) : ℝ :=
  imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) d

/-- The canonical driver at the clock of the own time `d`. -/
def drvAt (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (d : ℝ) (ω : Ω) : ℝ :=
  imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) (clkAt xj xk wj wk τ d ω)

namespace CanonHyp

variable (hC : CanonHyp L wj ζj wk ζk τ)
include hC

/-- **The frozen-hull data on a pre-contact event**: A.1's own-time data (`OwnData`) of curve `j` (frame `0`,
driver stopped beyond a good horizon `T > d`) against the hull of curve `k`, chosen samplewise, satisfy the
measurability inputs `FrzMeasR`. -/
theorem exists_frozenData (xj xk : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    ∃ (W W' a : Ω → ℝ → ℝ) (T : Ω → ℝ),
      FrzMeasR W W' a (maskSet L fun ω => physHull (xk - xj) (Strip.extPath (wk ω)) (τ ω))
        (fun ω => physMap (xk - xj) (Strip.extPath (wk ω)) (τ ω)) T (preC L xj xk wj ζj wk τ d) d ∧
      ∀ ω ∈ preC L xj xk wj ζj wk τ d, ∃ T₂ : ℝ, T ω < T₂ ∧ d < T ω ∧
        IsGoodTime 0 (Strip.extPath (wj ω)) (ζj ω) (xk - xj) (Strip.extPath (wk ω)) (τ ω) (T ω) ∧
        W ω = stopDrv (Strip.extPath (wj ω)) T₂ ∧
        OwnData (stopDrv (Strip.extPath (wj ω)) T₂) (physHull (xk - xj) (Strip.extPath (wk ω)) (τ ω))
          (physMap (xk - xj) (Strip.extPath (wk ω)) (τ ω)) (T ω) (a ω) (W' ω) := by
  classical
  set G := preC L xj xk wj ζj wk τ d with hGdef
  have hex : ∀ ω ∈ G, ∃ p : ℝ × ℝ × (ℝ → ℝ) × (ℝ → ℝ), p.1 < p.2.1 ∧ d < p.1 ∧
      IsGoodTime 0 (Strip.extPath (wj ω)) (ζj ω) (xk - xj) (Strip.extPath (wk ω)) (τ ω) p.1 ∧
      ContinuousOn (Strip.extPath (wj ω)) (Icc 0 p.2.1) ∧ 0 ≤ p.2.1 ∧
      OwnData (stopDrv (Strip.extPath (wj ω)) p.2.1) (physHull (xk - xj) (Strip.extPath (wk ω)) (τ ω))
        (physMap (xk - xj) (Strip.extPath (wk ω)) (τ ω)) p.1 p.2.2.1 p.2.2.2 := by
    intro ω hω
    have hc : ENNReal.ofReal d < contactTime 0 (Strip.extPath (wj ω)) (ζj ω) (xk - xj)
        (Strip.extPath (wk ω)) (τ ω) := by
      rw [← contactTime_sub]; exact hω.2
    obtain ⟨T, hT, hdT⟩ := exists_isGoodTime hd hc
    obtain ⟨T₂, hT₂, hTT⟩ := exists_isGoodTime hT.1.le hT.2
    have hT₂ζ : ENNReal.ofReal T₂ < ζj ω := hT₂.2.trans_le contactTime_le
    have hcon := hC.regj ω T₂ hT₂ζ
    have hWc := continuous_stopDrv hcon hT₂.1.le
    have hW0 : stopDrv (Strip.extPath (wj ω)) T₂ 0 = 0 := by
      rw [stopDrv_eqOn _ _ ⟨le_rfl, hT₂.1.le⟩, hC.regj0]
    have hk := hC.regk hω.1
    have hA := isHPHull_physHull_loc (x := xk - xj) (τ ω).coe_nonneg hk
    have hφ := isMapOut_physMap_loc (x := xk - xj) (τ ω).coe_nonneg hk (hC.regk0 ω)
    have hdisj : Disjoint (closure (physHull (xk - xj) (Strip.extPath (wk ω)) (τ ω)))
        (closure (QuantumZipper.fwdHull (stopDrv (Strip.extPath (wj ω)) T₂) T)) := by
      have h := disjoint_of_isGoodTime hT
      rwa [physHull_congr hT.1.le hTT (stopDrv_eqOn (Strip.extPath (wj ω)) T₂).symm, physHull_zero] at h
    obtain ⟨a, W', hown⟩ := exists_ownData hWc hW0 hT.1 hA hφ hdisj
    exact ⟨(T, T₂, a, W'), hTT, hdT, hT, hcon, hT₂.1.le, hown⟩
  choose P hP using hex
  set Q : Ω → ℝ × ℝ × (ℝ → ℝ) × (ℝ → ℝ) := fun ω => if h : ω ∈ G then P ω h else (1, 2, 0, 0) with hQ
  have hQG : ∀ ω (h : ω ∈ G), Q ω = P ω h := fun ω h => by simp only [hQ, h, ↓reduceDIte]
  set W : Ω → ℝ → ℝ := fun ω => if ω ∈ G then stopDrv (Strip.extPath (wj ω)) (Q ω).2.1 else fun _ => 0 with hW
  have hWG : ∀ ω ∈ G, W ω = stopDrv (Strip.extPath (wj ω)) (Q ω).2.1 := fun ω h => by simp only [hW, h, ↓reduceIte]
  have hWc : ∀ ω, Continuous (W ω) := fun ω => by
    by_cases h : ω ∈ G
    · rw [hWG ω h, hQG ω h]
      exact continuous_stopDrv (hP ω h).2.2.2.1 (hP ω h).2.2.2.2.1
    · simp only [hW, h, ↓reduceIte]; exact continuous_const
  have hGm := hC.measurableSet_preC xj xk hd
  have hWm : ∀ r ∈ Icc (0 : ℝ) d, Measurable fun ω => W ω r := fun r hr => by
    have e : (fun ω => W ω r) = G.indicator fun ω => wj ω r.toNNReal := by
      funext ω
      by_cases h : ω ∈ G
      · rw [indicator_of_mem h, hWG ω h, hQG ω h, stopDrv_eqOn _ _ ⟨hr.1, hr.2.trans
          ((hP ω h).2.1.trans (hP ω h).1).le⟩]
        rfl
      · simp only [hW, h, ↓reduceIte, indicator_of_notMem h]
    rw [e]
    exact (hC.measj _).indicator hGm
  refine ⟨W, fun ω => (Q ω).2.2.2, fun ω => (Q ω).2.2.1, fun ω => (Q ω).1, ?_, fun ω h =>
    ⟨(Q ω).2.1, by simp only [hQG ω h]; exact (hP ω h).1, by simp only [hQG ω h]; exact (hP ω h).2.1,
      by simp only [hQG ω h]; exact (hP ω h).2.2.1, hWG ω h,
      by simp only [hQG ω h]; exact (hP ω h).2.2.2.2.2⟩⟩
  refine frzMeasR_family hWc hd hWm hGm (fun K hK hKH => hC.measurableSet_hit_k (xk - xj) hK hKH)
    (fun ω _ => (maskSet_subset ω).trans (physHull_subset_H _ _ _)) (fun ω h => ?_) fun ω h => ?_
  · simp only [hWG ω h, maskSet_of_mem h.1, hQG ω h]
    exact (hP ω h).2.2.2.2.2
  · simp only [hQG ω h]
    exact ⟨hd, ((hP ω h).2.1).le⟩

/-- **The clock and the driver at the clock are measurable on the pre-contact events** (through `hcap` of the image of
the frozen hull and `frzA … 0`, A13's `FrzMeasR`). -/
theorem measurable_clkAt_drvAt (xj xk : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    Measurable ((preC L xj xk wj ζj wk τ d).indicator (clkAt xj xk wj wk τ d)) ∧
    Measurable ((preC L xj xk wj ζj wk τ d).indicator (drvAt xj xk wj ζj wk τ d)) := by
  obtain ⟨W, W', a, T, hM, hdat⟩ := hC.exists_frozenData xj xk hd
  set G := preC L xj xk wj ζj wk τ d with hGdef
  have hGm : MeasurableSet G := hC.measurableSet_preC xj xk hd
  set A := maskSet L fun ω => physHull (xk - xj) (Strip.extPath (wk ω)) (τ ω) with hA
  have key : ∀ ω ∈ G, clkAt xj xk wj wk τ d ω = a ω d ∧
      (0 < d → clkAt xj xk wj wk τ d ω = (hcapSet (imgHull (W ω) (A ω) d) + 2 * d - 2 * τ ω) / 2) ∧
      drvAt xj xk wj ζj wk τ d ω =
        frzA (W ω) (W' ω) (a ω) (physMap (xk - xj) (Strip.extPath (wk ω)) (τ ω)) 0 d + xj := by
    intro ω hω
    obtain ⟨T₂, hTT, hdT, hT, hWe, hown⟩ := hdat ω hω
    obtain ⟨hW', ha⟩ := ownData_bridge hTT hown
    have hdI : d ∈ Icc (0 : ℝ) (T ω) := ⟨hd, hdT.le⟩
    have hclk : clkAt xj xk wj wk τ d ω = a ω d := by
      rw [clkAt, imgClk_sub, ha d hdI]
    refine ⟨hclk, fun hd0 => ?_, ?_⟩
    · rw [clkAt, imgClk_sub, imgClk_eq_hcap (τ ω).coe_nonneg (hC.regk hω.1) hTT hown hdI hd0, hWe, hA,
        maskSet_of_mem hω.1]
    have hTg : IsGoodTime xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) (T ω) :=
      isGoodTime_sub.2 hT
    have heq := imgDrv_eqOn (hC.regj ω) (hC.regj0 ω) (hC.regk hω.1) (hC.regk0 ω) (τ ω).coe_nonneg hTg
      (isImgDrvOn_add hW')
    obtain ⟨h0, -, hmono⟩ := hC.clock_props (xj := xj) (xk := xk) hω.1
    have hdc : d ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk
        (Strip.extPath (wk ω)) (τ ω)} := ⟨hd, (ENNReal.ofReal_le_ofReal hdT.le).trans_lt hTg.2⟩
    have hTc : T ω ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk
        (Strip.extPath (wk ω)) (τ ω)} := ⟨hT.1.le, hTg.2⟩
    have h0c : (0 : ℝ) ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk
        (Strip.extPath (wk ω)) (τ ω)} := ⟨le_rfl, (ENNReal.ofReal_le_ofReal hd).trans_lt hdc.2⟩
    have hmem : imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) d ∈
        Icc 0 (imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) (T ω)) :=
      ⟨h0 ▸ hmono.monotoneOn h0c hdc hd, hmono.monotoneOn hdc hTc hdT.le⟩
    have h1 : drvAt xj xk wj ζj wk τ d ω = W' ω (clkAt xj xk wj wk τ d ω) + xj := heq hmem
    rw [h1, hclk, hWe, OwnData.frzA_zero hown hdI]
  refine ⟨?_, ?_⟩
  · rcases hd.eq_or_lt with hd0 | hd0
    · subst hd0
      have e : G.indicator (clkAt xj xk wj wk τ 0) = fun _ => 0 := by
        funext ω
        by_cases h : ω ∈ G
        · rw [indicator_of_mem h, clkAt, imgClk_zero]
        · rw [indicator_of_notMem h]
      rw [e]; exact measurable_const
    -- the capacity of the image of the frozen hull, as a limit
    set mv : ℕ → Ω → ℂ := fun n => {ω | ω ∈ G ∧ ((n : ℝ) : ℂ) * I ∈ H \ imgHull (W ω) (A ω) d}.indicator
      fun ω => ConformalImage.mapOut (imgHull (W ω) (A ω) d) (((n : ℝ) : ℂ) * I) with hmv
    have hmvm : ∀ n, Measurable (mv n) := fun n => hM.measurable_mapOut _
    have hcap : Measurable (G.indicator fun ω => hcapSet (imgHull (W ω) (A ω) d)) := by
      refine measurable_of_tendsto_metrizable (f := fun n : ℕ => G.indicator fun ω =>
        (n : ℝ) * ((n : ℝ) - (mv n ω).im)) (fun n => ?_) ?_
      · exact (measurable_const.mul (measurable_const.sub (Complex.measurable_im.comp (hmvm n)))).indicator hGm
      · rw [tendsto_pi_nhds]
        intro ω
        by_cases hω : ω ∈ G
        · simp only [indicator_of_mem hω]
          have hE := hM.isHPHull hω
          obtain ⟨R, hR⟩ := hE.2.1.subset_closedBall 0
          refine (tendsto_hcapSet hE).congr' ?_
          filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (max R 0)] with n hn
          have hn0 : (0 : ℝ) < n := (le_max_right R 0).trans_lt hn
          have hnI : ((n : ℝ) : ℂ) * I ∈ H \ imgHull (W ω) (A ω) d := by
            refine ⟨show 0 < (((n : ℝ) : ℂ) * I).im by simpa using hn0, fun hz => ?_⟩
            have := hR hz
            rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hn0] at this
            exact absurd ((le_max_left R 0).trans_lt hn) (not_lt.2 this)
          simp only [hmv, indicator_of_mem (show ω ∈ {ω | ω ∈ G ∧ ((n : ℝ) : ℂ) * I ∈
            H \ imgHull (W ω) (A ω) d} from ⟨hω, hnI⟩)]
        · simp only [indicator_of_notMem hω]
          exact tendsto_const_nhds
    have e : G.indicator (clkAt xj xk wj wk τ d) = G.indicator fun ω =>
        (G.indicator (fun ω => hcapSet (imgHull (W ω) (A ω) d)) ω + 2 * d - 2 * τ ω) / 2 := by
      funext ω
      by_cases h : ω ∈ G
      · rw [indicator_of_mem h, indicator_of_mem h, indicator_of_mem h, (key ω h).2.1 hd0]
      · rw [indicator_of_notMem h, indicator_of_notMem h]
    rw [e]
    exact (((hcap.add measurable_const).sub (measurable_const.mul
      (measurable_coe_nnreal_real.comp hC.measτ))).div_const 2).indicator hGm
  · have e : G.indicator (drvAt xj xk wj ζj wk τ d) = G.indicator fun ω =>
        G.indicator (fun ω => frzA (W ω) (W' ω) (a ω) (physMap (xk - xj) (Strip.extPath (wk ω)) (τ ω)) 0 d) ω
          + xj := by
      funext ω
      by_cases h : ω ∈ G
      · rw [indicator_of_mem h, indicator_of_mem h, indicator_of_mem h, (key ω h).2.2]
      · rw [indicator_of_notMem h, indicator_of_notMem h]
    rw [e]
    exact ((hM.measurable_frzA 0).add measurable_const).indicator hGm

end CanonHyp

end Frozen

/-! ### (m4) and (m3) -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {L : Set Ω} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞}
  {wk : Ω → ℝ≥0 → ℝ} {ζk : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0}

/-- Evaluation of a family of measurable functions at a measurable index. -/
theorem measurable_eval_nat {F : ℕ → Ω → ℝ} {k : Ω → ℕ} (hF : ∀ j, Measurable (F j)) (hk : Measurable k) :
    Measurable fun ω => F (k ω) ω := by
  have h2 : Measurable fun p : Ω × ℕ => F p.2 p.1 := measurable_from_prod_countable_left hF
  exact h2.comp (measurable_id.prodMk hk)

/-- The contact time, masked by the live event (`0` off it). -/
def cTL (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) :
    Ω → ℝ≥0∞ :=
  L.indicator (cT xj xk wj ζj wk τ)

/-- The canonical clock as a function of the own time. -/
def clkF (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : ℝ → ℝ :=
  fun s => imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) s

/-- The dyadic search inverting the clock at the image time `σ`, level `n`. (Irreducible: unfolding the underlying
`Nat.find` during unification is very slow.) -/
@[irreducible] def dS (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0)
    (σ : ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  dySearch (cTL L xj xk wj ζj wk τ ω) (clkF xj xk wj wk τ ω) σ n

/-- The driver at the clock of the dyadic time `k/2ⁿ`, masked by its pre-contact event. -/
def Fm (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0) (n k : ℕ) :
    Ω → ℝ :=
  (preC L xj xk wj ζj wk τ ((k : ℝ) / 2 ^ n)).indicator (drvAt xj xk wj ζj wk τ ((k : ℝ) / 2 ^ n))

omit [MeasurableSpace Ω] in
theorem dS_eq {xj xk : ℝ} {σ : ℝ} {ω : Ω} (hω : ω ∈ L) (n : ℕ) :
    dS L xj xk wj ζj wk τ σ n ω = dySearch (cT xj xk wj ζj wk τ ω) (clkF xj xk wj wk τ ω) σ n := by
  simp only [dS, cTL, indicator_of_mem hω]

/-- The dyadic search is measurable when its tests are events. -/
theorem measurable_dySearch {c : Ω → ℝ≥0∞} {clk : Ω → ℝ → ℝ} {σ : ℝ} {n : ℕ}
    (h : ∀ j, MeasurableSet {ω | DyGood (c ω) (clk ω) σ n j}) : Measurable fun ω => dySearch (c ω) (clk ω) σ n := by
  classical
  refine measurable_to_countable' fun k => ?_
  have hP : ∀ j, MeasurableSet {ω | DyGood (c ω) (clk ω) σ n j ∨ ∀ i, ¬ DyGood (c ω) (clk ω) σ n i} := fun j => by
    have e : {ω | DyGood (c ω) (clk ω) σ n j ∨ ∀ i, ¬ DyGood (c ω) (clk ω) σ n i} =
        {ω | DyGood (c ω) (clk ω) σ n j} ∪ ⋂ i, {ω | DyGood (c ω) (clk ω) σ n i}ᶜ := by
      ext ω; simp only [mem_ofPred_eq, mem_union, mem_iInter, mem_compl_iff]
    rw [e]
    exact (h j).union (MeasurableSet.iInter fun i => (h i).compl)
  have e : (fun ω => dySearch (c ω) (clk ω) σ n) ⁻¹' {k} =
      {ω | DyGood (c ω) (clk ω) σ n k ∨ ∀ i, ¬ DyGood (c ω) (clk ω) σ n i} ∩
        ⋂ j : ℕ, ⋂ (_ : j < k), {ω | DyGood (c ω) (clk ω) σ n j ∨ ∀ i, ¬ DyGood (c ω) (clk ω) σ n i}ᶜ := by
    ext ω
    simp only [dySearch, mem_preimage, mem_singleton_iff, Nat.find_eq_iff, mem_inter_iff, mem_iInter,
      mem_compl_iff, mem_ofPred_eq]
  rw [e]
  exact (hP k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hP j).compl)

namespace CanonHyp

variable (hC : CanonHyp L wj ζj wk ζk τ)
include hC

/-- Before the contact time the clock stays below the lifetime. -/
theorem ofReal_clk_lt_imgLife {xj xk : ℝ} {ω : Ω} (hω : ω ∈ L) {s : ℝ}
    (hs : s ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < cT xj xk wj ζj wk τ ω}) :
    0 ≤ clkAt xj xk wj wk τ s ω ∧
      ENNReal.ofReal (clkAt xj xk wj wk τ s ω) < imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk
        (Strip.extPath (wk ω)) (τ ω) := by
  obtain ⟨h0, -, hmono⟩ := hC.clock_props (xj := xj) (xk := xk) hω
  obtain ⟨s', -, hs's, hs'c⟩ := ENNReal.lt_iff_exists_real_btwn.1 hs.2
  have hss' : s < s' := ((ENNReal.ofReal_lt_ofReal_iff').1 hs's).1
  have hs'I : s' ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < cT xj xk wj ζj wk τ ω} := ⟨hs.1.trans hss'.le, hs'c⟩
  have h0I : (0 : ℝ) ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < cT xj xk wj ζj wk τ ω} :=
    ⟨le_rfl, (ENNReal.ofReal_le_ofReal hs.1).trans_lt hs.2⟩
  have hnn : 0 ≤ clkAt xj xk wj wk τ s ω := h0 ▸ hmono.monotoneOn h0I hs hs.1
  have hlt := hmono hs hs'I hss'
  have hle : ENNReal.ofReal (imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) s') ≤
      imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) :=
    le_iSup₂_of_le (f := fun (r : ℝ≥0) (_ : (r : ℝ≥0∞) < cT xj xk wj ζj wk τ ω) =>
      ENNReal.ofReal (imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) r)) (Real.toNNReal s')
      (by rw [← ENNReal.ofReal]; exact hs'c) (by rw [Real.coe_toNNReal _ hs'I.1])
  exact ⟨hnn, ((ENNReal.ofReal_lt_ofReal_iff (hnn.trans_lt hlt)).2 hlt).trans_le hle⟩

/-- **(m4) in general form: the masked canonical lifetime is measurable.** -/
theorem measurable_canonImgLife (xj xk : ℝ) :
    Measurable (L.indicator fun ω => imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)) := by
  set g : ℚ → Ω → ℝ≥0∞ := fun q ω => if 0 ≤ (q : ℝ) then
    ENNReal.ofReal ((preC L xj xk wj ζj wk τ q).indicator (clkAt xj xk wj wk τ q) ω) else 0 with hg
  have hgm : ∀ q, Measurable (g q) := fun q => by
    by_cases hq : 0 ≤ (q : ℝ)
    · simp only [hg, hq, ↓reduceIte]
      exact ENNReal.measurable_ofReal.comp (hC.measurable_clkAt_drvAt xj xk hq).1
    · simp only [hg, hq, ↓reduceIte]; exact measurable_const
  have e : (L.indicator fun ω => imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)) =
      fun ω => ⨆ q : ℚ, g q ω := by
    funext ω
    by_cases hω : ω ∈ L
    · rw [indicator_of_mem hω, imgLife_eq_iSup_rat (hC.clock_props hω).2.2]
      refine iSup_congr fun q => ?_
      by_cases hq : 0 ≤ (q : ℝ) ∧ ENNReal.ofReal q < contactTime xj (Strip.extPath (wj ω)) (ζj ω) xk
          (Strip.extPath (wk ω)) (τ ω)
      · rw [iSup_pos hq]
        simp only [hg, hq.1, ↓reduceIte, indicator_of_mem (show ω ∈ preC L xj xk wj ζj wk τ q from ⟨hω, hq.2⟩)]
        rfl
      · rw [iSup_neg hq]
        by_cases hq0 : 0 ≤ (q : ℝ)
        · have hn : ω ∉ preC L xj xk wj ζj wk τ q := fun h => hq ⟨hq0, h.2⟩
          simp only [hg, hq0, ↓reduceIte, indicator_of_notMem hn, ENNReal.ofReal_zero]
          rfl
        · simp only [hg, hq0, ↓reduceIte]
          rfl
    · rw [indicator_of_notMem hω]
      symm
      refine ENNReal.iSup_eq_zero.2 fun q => ?_
      by_cases hq0 : 0 ≤ (q : ℝ)
      · simp only [hg, hq0, ↓reduceIte, indicator_of_notMem (show ω ∉ preC L xj xk wj ζj wk τ q from
          fun h => hω h.1), ENNReal.ofReal_zero]
      · simp only [hg, hq0, ↓reduceIte]
  rw [e]
  exact Measurable.iSup hgm

/-- The dyadic tests of the clock inversion are events. -/
theorem measurableSet_dyGood (xj xk : ℝ) (σ : ℝ) (n j : ℕ) :
    MeasurableSet {ω | DyGood (cTL L xj xk wj ζj wk τ ω) (clkF xj xk wj wk τ ω) σ n j} := by
  have hr : (0 : ℝ) ≤ (j : ℝ) / 2 ^ n := by positivity
  have e : {ω | DyGood (cTL L xj xk wj ζj wk τ ω) (clkF xj xk wj wk τ ω) σ n j} =
      preC L xj xk wj ζj wk τ ((j : ℝ) / 2 ^ n) ∩
        {ω | σ ≤ (preC L xj xk wj ζj wk τ ((j : ℝ) / 2 ^ n)).indicator
          (clkAt xj xk wj wk τ ((j : ℝ) / 2 ^ n)) ω} := by
    ext ω
    simp only [DyGood, cTL, clkF, mem_ofPred_eq, mem_inter_iff]
    by_cases hω : ω ∈ L
    · rw [indicator_of_mem hω]
      constructor
      · rintro ⟨h1, h2⟩
        have hp : ω ∈ preC L xj xk wj ζj wk τ ((j : ℝ) / 2 ^ n) := ⟨hω, h1⟩
        exact ⟨hp, by rw [indicator_of_mem hp]; exact h2⟩
      · rintro ⟨hp, h2⟩
        rw [indicator_of_mem hp] at h2
        exact ⟨hp.2, h2⟩
    · rw [indicator_of_notMem hω]
      simp only [not_lt_zero, false_and, false_iff, not_and]
      exact fun h => absurd h.1 hω
  rw [e]
  exact (hC.measurableSet_preC xj xk hr).inter
    (measurableSet_le measurable_const (hC.measurable_clkAt_drvAt xj xk hr).1)

theorem measurable_dS (xj xk σ : ℝ) (n : ℕ) : Measurable (dS L xj xk wj ζj wk τ σ n) := by
  have h := measurable_dySearch (c := cTL L xj xk wj ζj wk τ) (clk := clkF xj xk wj wk τ) (σ := σ) (n := n)
    fun j => hC.measurableSet_dyGood xj xk σ n j
  unfold dS
  exact h

theorem measurable_Fm (xj xk : ℝ) (n k : ℕ) : Measurable (Fm L xj xk wj ζj wk τ n k) := by
  unfold Fm
  exact (hC.measurable_clkAt_drvAt xj xk (by positivity : (0 : ℝ) ≤ (k : ℝ) / 2 ^ n)).2

/-- **Pointwise convergence of the dyadic search**, on a live sample whose canonical lifetime exceeds `σ`. -/
theorem tendsto_Fm_dS {xj xk : ℝ} {ω : Ω} (hL : ω ∈ L) {σ : ℝ} (hσ : 0 ≤ σ)
    (hlt : ENNReal.ofReal σ < imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)) :
    Tendsto (fun n => Fm L xj xk wj ζj wk τ n (dS L xj xk wj ζj wk τ σ n ω) ω) atTop
      (𝓝 (imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) σ)) := by
  obtain ⟨h0, hcont, hmono⟩ := hC.clock_props (xj := xj) (xk := xk) hL
  obtain ⟨s, hs, hσs⟩ : ∃ s : ℝ≥0, (s : ℝ≥0∞) < cT xj xk wj ζj wk τ ω ∧
      ENNReal.ofReal σ < ENNReal.ofReal (imgClk xj (Strip.extPath (wj ω)) xk (Strip.extPath (wk ω)) (τ ω) s) := by
    simp only [imgLife, lt_iSup_iff] at hlt
    obtain ⟨s, hs, h⟩ := hlt
    exact ⟨s, hs, h⟩
  have hsI : (s : ℝ) ∈ {s | 0 ≤ s ∧ ENNReal.ofReal s < cT xj xk wj ζj wk τ ω} :=
    ⟨s.coe_nonneg, by rw [ENNReal.ofReal_coe_nnreal]; exact hs⟩
  have hFc : ContinuousOn (fun s => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)
      (clkF xj xk wj wk τ ω s)) {s | 0 ≤ s ∧ ENNReal.ofReal s < cT xj xk wj ζj wk τ ω} :=
    (continuousOn_imgDrv (hC.regj ω) (hC.regj0 ω) (hC.regk hL) (hC.regk0 ω) (τ ω).coe_nonneg).comp hcont
      fun s hs => hC.ofReal_clk_lt_imgLife hL hs
  obtain ⟨t₀, -, hct, hlim, hgood⟩ := tendsto_dySearch (c := cT xj xk wj ζj wk τ ω)
    (clk := clkF xj xk wj wk τ ω) hcont hmono h0 hσ hFc hsI ((ENNReal.ofReal_lt_ofReal_iff'.1 hσs).1)
  have hval : imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) (clkF xj xk wj wk τ ω t₀) =
      imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) σ := by rw [hct]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [hgood] with n hn
  rw [dS_eq hL]
  have hp : ω ∈ preC L xj xk wj ζj wk τ
      ((dySearch (cT xj xk wj ζj wk τ ω) (clkF xj xk wj wk τ ω) σ n : ℝ) / 2 ^ n) := ⟨hL, hn.1⟩
  simp only [Fm, indicator_of_mem hp, drvAt, clkAt, clkF]

/-- **The canonical driver at a deterministic image time, masked by the live event, is measurable.** -/
theorem measurable_imgDrv_at (xj xk : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    Measurable (L.indicator fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) σ) := by
  set E : Set Ω := L ∩ {ω | ENNReal.ofReal σ < L.indicator (fun ω => imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk
    (Strip.extPath (wk ω)) (τ ω)) ω} with hE
  have hEm : MeasurableSet E :=
    hC.meas.inter (measurableSet_lt measurable_const (hC.measurable_canonImgLife xj xk))
  have hseq : ∀ n, Measurable fun ω => Fm L xj xk wj ζj wk τ n (dS L xj xk wj ζj wk τ σ n ω) ω := fun n =>
    measurable_eval_nat (F := Fm L xj xk wj ζj wk τ n) (k := dS L xj xk wj ζj wk τ σ n)
      (fun k => hC.measurable_Fm xj xk n k) (hC.measurable_dS xj xk σ n)
  have e : (L.indicator fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) σ) =
      E.indicator fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) σ := by
    funext ω
    by_cases hω : ω ∈ L
    · by_cases hlt : ω ∈ E
      · rw [indicator_of_mem hω, indicator_of_mem hlt]
      · rw [indicator_of_mem hω, indicator_of_notMem hlt]
        refine imgDrv_eq_zero_of_le (hC.clock_props hω).2.2 ?_
        by_contra h
        exact hlt ⟨hω, by rw [mem_ofPred_eq, indicator_of_mem hω]; exact not_le.1 h⟩
    · rw [indicator_of_notMem hω, indicator_of_notMem fun h => hω h.1]
  rw [e]
  refine measurable_of_tendsto_metrizable
    (f := fun n => E.indicator fun ω => Fm L xj xk wj ζj wk τ n (dS L xj xk wj ζj wk τ σ n ω) ω)
    (fun n => (hseq n).indicator hEm) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ E
  · simp only [indicator_of_mem hω]
    exact hC.tendsto_Fm_dS hω.1 hσ (by have := hω.2; rwa [mem_ofPred_eq, indicator_of_mem hω.1] at this)
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- **(m3) in general form: the masked centred canonical driver at a deterministic image time is measurable.** -/
theorem measurable_canonImgDrv (xj xk : ℝ) (σ : ℝ≥0) :
    Measurable (L.indicator fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) σ -
      imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0) := by
  rw [indicator_sub]
  exact (hC.measurable_imgDrv_at xj xk σ.coe_nonneg).sub (hC.measurable_imgDrv_at xj xk le_rfl)

end CanonHyp

end Assembly

end InteractingSLE.ZhanGT4.A1Marg
