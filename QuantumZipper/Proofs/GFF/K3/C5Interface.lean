import QuantumZipper.Proofs.RS.TraceGenBubble
import QuantumZipper.Proofs.GFF.K3.Conformal

/-!
# GFF-K3, node C5 (via C5′): the deterministic hull interface

Blueprint `blueprint/EXT_PP_BLUEPRINT.md` §B, "Deterministic interface required from AD-1"
(i)–(iv), and `blueprint/GFF_K3_BLUEPRINT.md` §3.C node C5 (items 1, 2).

`GenTrace W η` bundles the ω-wise content of `Blueprint.RohdeSchrammTraceGen` (proved:
`RS.rohdeSchrammTraceGen_of_lt_eight`) together with `η(s) ∈ closure (ℍ \ K_s)` (the trace is the
radial limit `lim_{y↓0} f_s⁻¹(iy)`; from TR4 `RS.ae_sleTrace_good`).  For `τ ∈ [0,T]` the
**bubble set** `Ω_τ := {z ∈ ℍ \ η[0,T] : τ_z = τ}` (the union of the bounded components of
`ℍ \ η[0,T]` swallowed at `τ`, AD1-1(b)) satisfies:

* (ii) `isOpen_bubbleSet`, `bubbleSet_subset_compl_fwdHull` (`Ω_τ ⊆ ℍ \ K_t`, `t < τ`),
  `countable_bubbleIdx` (countably many nonempty `Ω_τ`);
* (iii) `compl_image_eq_union`: `ℍ \ η[0,T] = (ℍ \ K_T) ∪ ⋃_{τ ∈ [0,T]} Ω_τ`, with
  `disjoint_bubbleSet`, `disjoint_compl_fwdHull_bubbleSet`; `closure_image_eq` so that
  `sleComplement = ℍ \ η[0,T]`;
* the gate `frontier_bubbleSet_inter_subset`: `frontier Ω_τ ∩ (ℍ \ K_t) ⊆ η((t,τ])`, the radii
  `exists_gate_radius`, and the fatness `exists_fat` (intermediate value theorem along `η`);
* item 2: `isConformalOnto_fwdMap` (`f_T : ℍ \ K_T → ℍ` conformal onto).
* `ae_genTrace`: `GenTrace (drive κ B ω) (sleTrace κ B ω)` a.s. for `0 < κ < 8`.

Sources: Rohde–Schramm, *Basic properties of SLE* (2005), Thm 5.1 (p. 20) and proof of Thm 6.4
(p. 31); Lawler, *Conformally Invariant Processes in the Plane* (2005), Prop. 6.10 (p. 128).
The point-set deductions (openness of `Ω_τ`, the gate, fatness) are own elementary arguments
following the blueprint text of C5′.
-/

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.K3

/-- Deterministic hull hypotheses: continuous driver, curve generating the hulls, tip in the
closure of the unbounded complement. -/
structure GenTrace (W : ℝ → ℝ) (η : ℝ → ℂ) : Prop where
  contW : Continuous W
  zeroW : W 0 = 0
  zero : η 0 = 0
  cont : ContinuousOn η (Ici 0)
  gen : ∀ t : ℝ, 0 ≤ t → ∀ M : ℝ, (∀ s ∈ Icc 0 t, ‖η s‖ < M) →
    H \ fwdHull W t = connectedComponentIn (H \ η '' Icc 0 t) (M * I)
  tip : ∀ s : ℝ, 0 ≤ s → η s ∈ closure (H \ fwdHull W s)

/-- The bubble set `Ω_τ`: points of `ℍ \ η[0,T]` swallowed at time `τ`. -/
def bubbleSet (W : ℝ → ℝ) (η : ℝ → ℂ) (T τ : ℝ) : Set ℂ :=
  {z | z ∈ H \ η '' Icc 0 T ∧ swallowTime W z = ENNReal.ofReal τ}

/-- The times of nonempty bubble sets. -/
def bubbleIdx (W : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ) : Set ℝ :=
  {τ | τ ∈ Icc 0 T ∧ (bubbleSet W η T τ).Nonempty}

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

theorem GenTrace.isCompact_image (hg : GenTrace W η) (T : ℝ) : IsCompact (η '' Icc 0 T) :=
  isCompact_Icc.image_of_continuousOn (hg.cont.mono Icc_subset_Ici_self)

theorem GenTrace.closure_image_eq (hg : GenTrace W η) (T : ℝ) :
    closure (η '' Icc 0 T) = η '' Icc 0 T :=
  (hg.isCompact_image T).isClosed.closure_eq

theorem GenTrace.isOpen_compl_image (hg : GenTrace W η) (T : ℝ) : IsOpen (H \ η '' Icc 0 T) :=
  isOpen_H.sdiff (hg.isCompact_image T).isClosed

/-- (i) `ℍ \ K_t ⊆ ℍ \ η[0,t]`. -/
theorem GenTrace.compl_fwdHull_subset (hg : GenTrace W η) {t : ℝ} (ht : 0 ≤ t) :
    H \ fwdHull W t ⊆ H \ η '' Icc 0 t := by
  intro z hz
  have h := RS.compl_fwdHull_eq_cc_of_gen hg.cont hg.gen ht hz
  rw [h] at hz
  exact connectedComponentIn_subset _ _ hz

/-- (i) `η(s) ∉ ℍ \ K_t` for `0 ≤ s ≤ t`. -/
theorem GenTrace.not_mem_compl_fwdHull (hg : GenTrace W η) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    η s ∉ H \ fwdHull W t := fun h =>
  (hg.compl_fwdHull_subset (hs.trans hst) h).2 ⟨s, ⟨hs, hst⟩, rfl⟩

/-- Swallowing times are constant on a preconnected subset of `ℍ \ η[0,S]` containing a point
swallowed by time `S`. -/
theorem GenTrace.swallowTime_eq_of_preconnected (hg : GenTrace W η) {S : ℝ} (hS : 0 ≤ S)
    {C : Set ℂ} (hC : IsPreconnected C) (hCsub : C ⊆ H \ η '' Icc 0 S) {z w : ℂ} (hz : z ∈ C)
    (hw : w ∈ C) (hzS : swallowTime W z ≤ ENNReal.ofReal S) :
    swallowTime W w = swallowTime W z := by
  have htop : swallowTime W z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hzS
  set τ := (swallowTime W z).toReal with hτ
  have hτeq : ENNReal.ofReal τ = swallowTime W z := ENNReal.ofReal_toReal htop
  have hτS : τ ≤ S := by rwa [← ENNReal.ofReal_le_ofReal_iff hS, hτeq]
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  refine le_antisymm ?_ ?_
  · by_contra hlt
    rw [not_le] at hlt
    have hwD : w ∈ H \ fwdHull W τ :=
      RS.mem_compl_fwdHull_iff.2 ⟨(hCsub hw).1, by rwa [hτeq]⟩
    have := RS.subset_compl_fwdHull_of_gen hg.cont hg.gen hτ0 hτS hC hCsub hw hwD hz
    exact (RS.mem_compl_fwdHull_iff.1 this).2.ne' hτeq.symm
  · by_contra hlt
    rw [not_le] at hlt
    have hwtop : swallowTime W w ≠ ⊤ := ne_top_of_lt hlt
    set s := (swallowTime W w).toReal
    have hseq : ENNReal.ofReal s = swallowTime W w := ENNReal.ofReal_toReal hwtop
    have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
    have hsS : s ≤ S := by
      rw [← ENNReal.ofReal_le_ofReal_iff hS, hseq]; exact (hlt.le.trans hzS)
    have hzD : z ∈ H \ fwdHull W s :=
      RS.mem_compl_fwdHull_iff.2 ⟨(hCsub hz).1, by rwa [hseq]⟩
    have := RS.subset_compl_fwdHull_of_gen hg.cont hg.gen hs0 hsS hC hCsub hz hzD hw
    exact (RS.mem_compl_fwdHull_iff.1 this).2.ne' hseq.symm

/-- (ii) `Ω_τ` is open. -/
theorem GenTrace.isOpen_bubbleSet (hg : GenTrace W η) {T τ : ℝ} (hτT : τ ≤ T) :
    IsOpen (bubbleSet W η T τ) := by
  rw [Metric.isOpen_iff]
  rintro z ⟨hzU, hzτ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hg.isOpen_compl_image T) z hzU
  have hT : 0 ≤ T := by
    by_contra h; rw [not_le] at h
    have := swallowTime_pos hg.contW hzU.1
    rw [hzτ, ENNReal.ofReal_of_nonpos (hτT.trans h.le)] at this
    exact lt_irrefl _ this
  refine ⟨ε, hε, fun w hw => ⟨hball hw, ?_⟩⟩
  rw [← hzτ]
  exact hg.swallowTime_eq_of_preconnected hT (convex_ball z ε).isPreconnected hball
    (mem_ball_self hε) hw (hzτ ▸ ENNReal.ofReal_le_ofReal hτT)

/-- (ii) `Ω_τ ⊆ ℍ \ K_t` for `t < τ`. -/
theorem bubbleSet_subset_compl_fwdHull {T τ t : ℝ} (ht : 0 ≤ t) (htτ : t < τ) :
    bubbleSet W η T τ ⊆ H \ fwdHull W t := by
  rintro z ⟨hzU, hzτ⟩
  refine ⟨hzU.1, fun h => ?_⟩
  have := h.2
  rw [hzτ, ENNReal.ofReal_le_ofReal_iff'] at this
  rcases this with h' | h' <;> linarith

/-- (iii) Pairwise disjointness of the bubble sets. -/
theorem disjoint_bubbleSet {T τ τ' : ℝ} (hτ : 0 ≤ τ) (hτ' : 0 ≤ τ') (hne : τ ≠ τ') :
    Disjoint (bubbleSet W η T τ) (bubbleSet W η T τ') := by
  rw [Set.disjoint_left]
  rintro z ⟨-, h1⟩ ⟨-, h2⟩
  exact hne ((ENNReal.ofReal_eq_ofReal_iff hτ hτ').1 (h1.symm.trans h2))

/-- (iii) `ℍ \ η[0,T] = (ℍ \ K_T) ∪ ⋃_{τ ∈ [0,T]} Ω_τ`. -/
theorem GenTrace.compl_image_eq_union (hg : GenTrace W η) {T : ℝ} (hT : 0 ≤ T) :
    H \ η '' Icc 0 T = (H \ fwdHull W T) ∪ ⋃ τ ∈ bubbleIdx W η T, bubbleSet W η T τ := by
  apply Subset.antisymm
  · intro z hz
    by_cases hK : z ∈ fwdHull W T
    · right
      have htop : swallowTime W z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK.2
      have hmem : z ∈ bubbleSet W η T (swallowTime W z).toReal :=
        ⟨hz, (ENNReal.ofReal_toReal htop).symm⟩
      refine mem_biUnion ⟨⟨ENNReal.toReal_nonneg, ?_⟩, z, hmem⟩ hmem
      rw [← ENNReal.ofReal_le_ofReal_iff hT, ENNReal.ofReal_toReal htop]; exact hK.2
    · exact Or.inl ⟨hz.1, hK⟩
  · rintro z (hz | hz)
    · exact hg.compl_fwdHull_subset hT hz
    · obtain ⟨τ, -, hz⟩ := mem_iUnion₂.1 hz
      exact hz.1

/-- (ii) Countably many nonempty bubble sets. -/
theorem GenTrace.countable_bubbleIdx (hg : GenTrace W η) (T : ℝ) :
    (bubbleIdx W η T).Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := bubbleSet W η T) ?_
    (fun τ hτ => hg.isOpen_bubbleSet hτ.1.2) (fun τ hτ => hτ.2)
  intro τ hτ τ' hτ' hne
  exact disjoint_bubbleSet hτ.1.1 hτ'.1.1 hne

/-- **The gate.** For `0 ≤ t < τ ≤ T`, `frontier Ω_τ ∩ (ℍ \ K_t) ⊆ η((t,τ])`. -/
theorem GenTrace.frontier_bubbleSet_inter_subset (hg : GenTrace W η) {T τ t : ℝ} (hτT : τ ≤ T)
    (ht : 0 ≤ t) (htτ : t < τ) :
    frontier (bubbleSet W η T τ) ∩ (H \ fwdHull W t) ⊆ η '' Ioc t τ := by
  rintro z ⟨hzf, hzD⟩
  have hτ0 : 0 ≤ τ := ht.trans htτ.le
  by_cases hzη : z ∈ η '' Icc 0 τ
  · obtain ⟨s, hs, rfl⟩ := hzη
    refine ⟨s, ⟨?_, hs.2⟩, rfl⟩
    by_contra hst; rw [not_lt] at hst
    exact hg.not_mem_compl_fwdHull hs.1 hst hzD
  exfalso
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hg.isOpen_compl_image τ) z ⟨hzD.1, hzη⟩
  obtain ⟨w, hwb, hwΩ⟩ := (mem_closure_iff_nhds.1 (frontier_subset_closure hzf)) (ball z ε)
    (ball_mem_nhds z hε)
  have hconst : ∀ v ∈ ball z ε, swallowTime W v = ENNReal.ofReal τ := fun v hv => by
    rw [← hwΩ.2]
    exact hg.swallowTime_eq_of_preconnected hτ0 (convex_ball z ε).isPreconnected hball hwb hv
      hwΩ.2.le
  -- `z ∉ Ω_τ` since `Ω_τ` is open and `z` is a frontier point
  have hzΩ : z ∉ bubbleSet W η T τ := fun h => by
    have := (hg.isOpen_bubbleSet hτT).inter_frontier_eq
    exact (Set.eq_empty_iff_forall_notMem.1 this) z ⟨h, hzf⟩
  have hzU : z ∈ η '' Icc 0 T := by
    by_contra h
    exact hzΩ ⟨⟨hzD.1, h⟩, hconst z (mem_ball_self hε)⟩
  obtain ⟨s, hs, hsz⟩ := hzU
  have hsτ : τ < s := by
    by_contra h; rw [not_lt] at h
    exact hzη ⟨s, ⟨hs.1, h⟩, hsz⟩
  -- the tip `η s` is a limit of points of `ℍ \ K_s ⊆ ℍ \ K_τ`
  have htip := hg.tip s hs.1
  rw [hsz] at htip
  obtain ⟨v, hvb, hvD⟩ := (mem_closure_iff_nhds.1 htip) (ball z ε) (ball_mem_nhds z hε)
  have := hconst v hvb
  exact hvD.2 ⟨hvD.1, (this.le.trans (ENNReal.ofReal_le_ofReal hsτ.le))⟩

/-- **Gate radii.** For `t_n → τ` with `0 ≤ t_n ≤ τ` there are radii `r_n > 0`, `r_n → 0`, with
`‖η s − η τ‖ ≤ r_n` on `[t_n, τ]` (continuity of `η` at `τ`). -/
theorem GenTrace.exists_gate_radius (hg : GenTrace W η) {τ : ℝ} (hτ : 0 ≤ τ) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (htτ : ∀ n, t n ≤ τ) (hlim : Tendsto t atTop (𝓝 τ)) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
      ∀ n, ∀ s ∈ Icc (t n) τ, ‖η s - η τ‖ ≤ r n := by
  set F : ℝ → ℝ := fun s => ‖η s - η τ‖ with hF
  have hFc : ContinuousOn F (Ici 0) := (hg.cont.sub continuousOn_const).norm
  have hFτ : F τ = 0 := by simp [hF]
  set e : ℕ → ℝ := fun n => sSup (F '' Icc (t n) τ) with he
  have hbdd : ∀ n, BddAbove (F '' Icc (t n) τ) := fun n =>
    (isCompact_Icc.image_of_continuousOn
      (hFc.mono fun s hs => (ht0 n).trans hs.1)).bddAbove
  have hle : ∀ n, ∀ s ∈ Icc (t n) τ, F s ≤ e n := fun n s hs =>
    le_csSup (hbdd n) (mem_image_of_mem F hs)
  have he0 : ∀ n, 0 ≤ e n := fun n => (norm_nonneg _).trans (hle n τ ⟨htτ n, le_rfl⟩)
  have hlim_e : Tendsto e atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hFc τ hτ) (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have hen : e n ≤ ε / 2 := csSup_le ⟨F τ, mem_image_of_mem F ⟨htτ n, le_rfl⟩⟩ (by
      rintro _ ⟨s, hs, rfl⟩
      have hd := hN n hn
      rw [Real.dist_eq, abs_lt] at hd
      have h1 := hcont (x := s) ((ht0 n).trans hs.1) (by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
      rw [hFτ, Real.dist_eq, sub_zero, abs_lt] at h1
      exact h1.2.le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (he0 n)]
    linarith
  refine ⟨fun n => e n + 1 / ((n : ℝ) + 1), fun n => by have := he0 n; positivity, ?_,
    fun n s hs => (hle n s hs).trans (le_add_of_nonneg_right (by positivity))⟩
  simpa using hlim_e.add tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Fatness** (`hfat` of BUB-4): spheres around `η τ` of radius in `(2 r_n, d)` meet
`ℂ \ (ℍ \ K_{t_n})`.  If `η τ ∉ ℍ`, the real point `η τ + s`; otherwise `d = ‖η τ‖` and the
intermediate value theorem for `s ↦ ‖η s − η τ‖` on `[0, t_n]`. -/
theorem GenTrace.exists_fat (hg : GenTrace W η) {τ : ℝ} {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    {r : ℕ → ℝ} (hr0 : ∀ n, 0 < r n) (hrt : ∀ n, ‖η (t n) - η τ‖ ≤ r n) :
    ∃ d > 0, ∀ n, ∀ s ∈ Ioo (2 * r n) d, ∃ z, ‖z - η τ‖ = s ∧ z ∉ H \ fwdHull W (t n) := by
  by_cases hp : η τ ∈ H
  · refine ⟨‖η τ‖, norm_pos_iff.2 fun h => by
      have : (0 : ℝ) < (η τ).im := hp
      rw [h] at this; simp at this, fun n s hs => ?_⟩
    have hFc : ContinuousOn (fun s' => ‖η s' - η τ‖) (Icc 0 (t n)) :=
      ((hg.cont.mono Icc_subset_Ici_self).sub continuousOn_const).norm
    have hmem : s ∈ Icc ‖η (t n) - η τ‖ ‖η 0 - η τ‖ := by
      refine ⟨by linarith [hrt n, hr0 n, hs.1], ?_⟩
      rw [hg.zero, zero_sub, norm_neg]; exact hs.2.le
    obtain ⟨s', hs', hFs'⟩ := intermediate_value_Icc' (ht0 n) hFc hmem
    exact ⟨η s', hFs', hg.not_mem_compl_fwdHull hs'.1 hs'.2⟩
  · refine ⟨1, one_pos, fun n s hs => ⟨η τ + s, ?_, fun h => hp ?_⟩⟩
    · rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [hr0 n, hs.1])]
    · have h1 : (0 : ℝ) < (η τ + (s : ℂ)).im := h.1
      show (0 : ℝ) < (η τ).im
      simpa using h1

/-- **Item 2.** `f_T` maps `ℍ \ K_T` conformally onto `ℍ`. -/
theorem isConformalOnto_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T) :
    IsConformalOnto (fwdMap W T) (H \ fwdHull W T) H where
  isOpen := FwdHolo.isOpen_compl_fwdHull hW hT
  diffOn := fun z hz =>
    (FwdHolo.hasDerivAt_fwdMap hW hT hz).differentiableAt.differentiableWithinAt
  injOn := FwdHolo.injOn_fwdMap hW hT
  image_eq := by
    refine Subset.antisymm (image_subset_iff.2 (FwdHolo.mapsTo_fwdMap hW hT)) fun w hw => ?_
    exact ⟨fwdMapInv W T w, RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hw,
      RS.fwdMap_fwdMapInv hW hW0 hT hw⟩
  deriv_ne := fun z hz => by
    rw [(FwdHolo.hasDerivAt_fwdMap hW hT hz).deriv]; exact Complex.exp_ne_zero _

/-- `GenTrace` holds almost surely for SLE_κ, `0 < κ < 8` (AD1-0 and TR4). -/
theorem ae_genTrace {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∀ᵐ ω ∂P, GenTrace (drive κ B ω) (sleTrace κ B ω) := by
  obtain ⟨δ, hδ, h⟩ := RS.ae_sleTrace_good hB hκ hκ8
  filter_upwards [h, RS.rohdeSchrammTraceGen_of_lt_eight hκ hκ8 P B hB, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hω hgen hc h0
  obtain ⟨h0', hcont, hbd⟩ := hω
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  refine ⟨hW, hW0, h0', hcont, hgen.2.2, fun s hs => ?_⟩
  obtain ⟨C, hC⟩ := hbd ⌈s⌉₊
  have hr : Tendsto (fun y : ℝ => C * y ^ δ) (𝓝[>] 0) (𝓝 0) := by
    have hca : ContinuousAt (fun y : ℝ => C * y ^ δ) 0 :=
      continuousAt_const.mul (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le))
    have h2 := hca.tendsto
    rw [Real.zero_rpow hδ.ne', mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun y : ℝ => fwdMapInv (drive κ B ω) s (y * I)) (𝓝[>] 0)
      (𝓝 (sleTrace κ B ω s)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero_norm' ?_ hr)
    filter_upwards [Ioo_mem_nhdsGT one_pos] with y hy
    rw [norm_norm]
    exact hC s ⟨hs, Nat.le_ceil s⟩ y ⟨hy.1, hy.2.le⟩
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact RS.fwdMapInv_mem_compl_fwdHull hW hW0 hs (show 0 < ((y : ℂ) * I).im by simpa using hy)

end QuantumZipper.K3
