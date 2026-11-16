/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermK2Ends
import InteractingSLE.Spec.Supplement.AStopPathTerm

/-!
# The stopping rule of the chart path at a boundary seed (item 6 of `AStopSourceInputs`, pathwise)

Packet PROVE-RC-TERM, second run (ruling R124). `RLC.AStopPath.aStop_facts` needs an interior tip
(`Supp7.IsRetCont.tipH`); here the same five facts are proved for the chart path of the first path from its boundary
seed, in the chart of the completed second path:

* `kLife`, `kClock`, `kTrace`: the capacity lifetime, the inverse clock and the chart path in capacity time;
* `IsPathSample.mem_retSet_of_stop_lt`: a stop before the lifetime is a contact;
* **`IsKSample.stop_facts`**: for an untouched word of a fixed force type with an admissible seed, the live incident
  bounds and the jump avoidance of the first path, its terminal bad incident height, and any continuous driver `W`
  from `0` generating `kTrace` up to `kLife`:
  `0 < kLife`; the seed is not a threshold; no threshold at a positive capacity time before `kLife` (Lemma G7);
  `kTrace` avoids the stop set `aStopSet (kEnds U T d)` before `kLife`; at a finite `kLife` either the threshold
  condition holds (the first path ran to its own lifetime off the second path) or `kTrace kLife` is in the stop set.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.RealContact

namespace Term

open LP (reflectC)
open Restart Supp7 RLC.AStopPath PiecewiseConstantBoundaryData MartChar.RealFlow
open Exist.StagedLaw (markPos markPosL)

/-- **A stop before the lifetime is a contact** (builder frame). -/
theorem IsPathSample.mem_retSet_of_stop_lt {V : ℝ → ℝ} {T : ℝ≥0} {ξ : ℝ → ℂ} {p d : ℝ} {w : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} {β : ℝ≥0 → ℂ} (h : IsPathSample V T ξ p d w ζ β) (hL : physStop ξ T d β ζ < ζ) :
    β (physStop ξ T d β ζ).toNNReal ∈ retSet ξ T d := by
  by_contra hK
  have hfin : physStop ξ T d β ζ ≠ ⊤ := ne_top_of_lt hL
  set c := (physStop ξ T d β ζ).toNNReal with hc
  have hcL : (c : ℝ≥0∞) = physStop ξ T d β ζ := ENNReal.coe_toNNReal hfin
  obtain ⟨ζ', hζ'1, hζ'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hL
  have hcζ' : c < ζ' := by
    rw [← hcL] at hζ'1
    exact_mod_cast hζ'1
  have hnb : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} ∈ 𝓝 c :=
    mem_of_superset (Iio_mem_nhds hcζ') fun t ht => (ENNReal.coe_le_coe.2 (le_of_lt ht)).trans hζ'2.le
  have hcont : ContinuousAt β c := (h.gen.2.1 c (hcL.le.trans hL.le)).continuousAt hnb
  have hKc : IsClosed (retSet ξ T d) := by
    rw [retSet_eq h.tpos]
    exact h.entry.isCompact_path.isClosed
  have hev : ∀ᶠ t in 𝓝 c, β t ∉ retSet ξ T d ∧ t < ζ' :=
    (hcont.eventually (hKc.isOpen_compl.mem_nhds hK)).and (Iio_mem_nhds hcζ')
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set e : ℝ≥0 := ⟨ε / 2, by positivity⟩ with he
  have he0 : 0 < e := by
    show (0 : ℝ) < ε / 2
    positivity
  have hd : ∀ t : ℝ≥0, c ≤ t → t ≤ c + e → dist t c < ε := by
    intro t h1 h2
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 h1))]
    have h3 : (t : ℝ) ≤ (c : ℝ) + (e : ℝ) := by exact_mod_cast h2
    have he' : (e : ℝ) = ε / 2 := rfl
    linarith
  have hmem : c + e ∈ contSet β ζ 0 (retSet ξ T d) := by
    refine ⟨zero_le, ?_, fun t' ht'0 ht' => ?_⟩
    · exact (ENNReal.coe_le_coe.2 (hball (hd (c + e) le_self_add le_rfl)).2.le).trans hζ'2.le
    · rcases lt_or_ge t' c with hlt | hge
      · exact off_of_lt ht'0 (by rw [← hcL]; exact_mod_cast hlt)
      · exact (hball (hd t' hge ht'.le)).1
  have hle : ((c + e : ℝ≥0) : ℝ≥0∞) ≤ (c : ℝ≥0∞) := by
    rw [hcL]
    exact le_contStop hmem
  exact absurd (ENNReal.coe_le_coe.1 hle) (not_le.2 (lt_add_of_pos_right c he0))

/-! ### The chart path in capacity time -/

/-- The capacity lifetime of the chart path. -/
def kLife (U : ℝ → ℝ) (ρ₂ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (ρ₁ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  capLife (chartClock (kPath U ρ₂ T d ρ₁ ζ)) (kStop ρ₂ T d ρ₁ ζ)

/-- The inverse capacity clock: the physical time of a capacity time. -/
def kClock (U : ℝ → ℝ) (ρ₂ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (ρ₁ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (q' : ℝ≥0) : ℝ≥0 :=
  invClock (chartClock (kPath U ρ₂ T d ρ₁ ζ)) (kStop ρ₂ T d ρ₁ ζ) q'

/-- The chart path in capacity time. -/
def kTrace (U : ℝ → ℝ) (ρ₂ : ℝ → ℂ) (T : ℝ≥0) (d : ℝ) (ρ₁ : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (q' : ℝ≥0) : ℂ :=
  kPath U ρ₂ T d ρ₁ ζ (kClock U ρ₂ T d ρ₁ ζ q')

namespace IsKSample

variable {U : ℝ → ℝ} {T : ℝ≥0} {ρ₂ : ℝ → ℂ} {q d : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {ρ₁ : ℝ≥0 → ℂ}
  (h : IsKSample U T ρ₂ q d w ζ ρ₁)
include h

theorem rho_zero : ρ₁ 0 = 0 := by
  have h1 : reflectC (ρ₁ 0) = 0 := (IsPathSample.gen h).1
  have h2 := congrArg reflectC h1
  rw [LP.reflectC_reflectC] at h2
  rw [h2]
  simp [reflectC]

theorem rho_injOn : InjOn ρ₁ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := fun a ha b hb hab =>
  IsPathSample.inj h ha hb (by show reflectC (ρ₁ a) = reflectC (ρ₁ b); rw [hab])

omit h in
theorem kStop_le : kStop ρ₂ T d ρ₁ ζ ≤ ζ := physStop_le _ T d _ ζ

omit h in
theorem kTime_of_le {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ kStop ρ₂ T d ρ₁ ζ) : kTime ρ₂ T d ρ₁ ζ s = s :=
  stopT_of_le hs

theorem isClockOn : IsClockOn (chartClock (kPath U ρ₂ T d ρ₁ ζ)) (kStop ρ₂ T d ρ₁ ζ) :=
  (h.isAGood (Ω := Unit) ()).clock

/-- The boundary inverse of the chart path before the stop is the first path. -/
theorem kInv_kPath_of_le {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ kStop ρ₂ T d ρ₁ ζ) :
    kInv U (T : ℝ) d (kPath U ρ₂ T d ρ₁ ζ s) = ρ₁ s := by
  rw [h.kInv_kPath, kTime_of_le hs]

omit h in
theorem off_of_lt_kStop {s : ℝ≥0} (hs0 : 0 < s) (hs : (s : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ) :
    reflectC (ρ₁ s) ∉ retSet (fun s => reflectC (ρ₂ s)) T d :=
  off_of_lt hs0 hs

theorem mem_retSet_of_kStop_lt (hL : kStop ρ₂ T d ρ₁ ζ < ζ) :
    reflectC (ρ₁ (kStop ρ₂ T d ρ₁ ζ).toNNReal) ∈ retSet (fun s => reflectC (ρ₂ s)) T d :=
  IsPathSample.mem_retSet_of_stop_lt h hL

/-- An interior chart point is not over the second path, and its image is interior. -/
theorem of_im_pos {v : ℂ} (hv : 0 < v.im) :
    reflectC (kInv U (T : ℝ) d v) ∉ retSet (fun s => reflectC (ρ₂ s)) T d ∧ 0 < (kInv U (T : ℝ) d v).im := by
  have hE := IsPathSample.entry h
  have hvH : reflectC v ∈ H := by
    show 0 < (reflectC v).im
    rw [LP.im_reflectC]
    exact hv
  have hdom : entryInv (-U) (T : ℝ) d (reflectC v) ∈ entryDom (fun s => reflectC (ρ₂ s)) (T : ℝ) d := by
    rw [hE.entryInv_eq_inv hvH]
    exact hE.isDomainChart'.inv_mem hvH
  have e : reflectC (kInv U (T : ℝ) d v) = entryInv (-U) (T : ℝ) d (reflectC v) := by
    unfold kInv
    rw [LP.reflectC_reflectC]
  constructor
  · rw [e, retSet_eq (IsPathSample.tpos h)]
    intro hmem
    exact hdom.2 ⟨hdom.1, Or.inl (subset_closure hmem)⟩
  · have h1 : 0 < (entryInv (-U) (T : ℝ) d (reflectC v)).im := hdom.1
    rw [← e, LP.im_reflectC] at h1
    exact h1

theorem markPos_zero_pos (hq : q < 0) : 0 < markPos U (T : ℝ) 0 := by
  have hE := IsPathSample.entry h
  have h1 := hE.tip.reflect
  rw [neg_neg, neg_neg] at h1
  exact h1.markPos_pos hq le_rfl

theorem kLife_pos : 0 < kLife U ρ₂ T d ρ₁ ζ := by
  have hclk := h.isClockOn (U := U)
  unfold kLife capLife
  split_ifs with hLt
  · exact ENNReal.zero_lt_top
  · have hL'0 : 0 < (kStop ρ₂ T d ρ₁ ζ).toNNReal := ENNReal.toNNReal_pos h.stopPos.ne' hLt
    have h1 := hclk.strictMonoOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ kStop ρ₂ T d ρ₁ ζ from zero_le)
      (show (((kStop ρ₂ T d ρ₁ ζ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ kStop ρ₂ T d ρ₁ ζ from
        (ENNReal.coe_toNNReal hLt).le) hL'0
    rw [hclk.zero] at h1
    exact ENNReal.ofReal_pos.2 h1

omit h in
theorem kStop_ne_top_of_kLife (hfin : kLife U ρ₂ T d ρ₁ ζ ≠ ⊤) : kStop ρ₂ T d ρ₁ ζ ≠ ⊤ := fun hLt =>
  hfin (by unfold kLife capLife; rw [ite_eq_left hLt])

/-- Every positive capacity time before the lifetime is the capacity of a positive physical time before the stop. -/
theorem exists_time {q' : ℝ≥0} (hq0 : 0 < q') (hq' : (q' : ℝ≥0∞) < kLife U ρ₂ T d ρ₁ ζ) :
    ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ ∧
      kTrace U ρ₂ T d ρ₁ ζ q' = kPath U ρ₂ T d ρ₁ ζ s := by
  have hclk := h.isClockOn (U := U)
  obtain ⟨hsL, has⟩ := hclk.invClock_spec (show (q' : ℝ≥0∞) ≤ capLife _ _ from hq'.le)
  refine ⟨kClock U ρ₂ T d ρ₁ ζ q', ?_, ?_, rfl⟩
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ kClock U ρ₂ T d ρ₁ ζ q') with h0 | h0
    · exfalso
      have has' : chartClock (kPath U ρ₂ T d ρ₁ ζ) (kClock U ρ₂ T d ρ₁ ζ q') = q' := has
      rw [← h0, hclk.zero] at has'
      exact hq0.ne' (by exact_mod_cast has'.symm)
    · exact h0
  · rcases hsL.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hfin : kStop ρ₂ T d ρ₁ ζ ≠ ⊤ := by
        rw [← h1]
        exact ENNReal.coe_ne_top
      have hs' : invClock (chartClock (kPath U ρ₂ T d ρ₁ ζ)) (kStop ρ₂ T d ρ₁ ζ) q' =
          (kStop ρ₂ T d ρ₁ ζ).toNNReal := by
        have h2 := congrArg ENNReal.toNNReal h1
        rwa [ENNReal.toNNReal_coe] at h2
      have hV : kLife U ρ₂ T d ρ₁ ζ = ENNReal.ofReal
          (chartClock (kPath U ρ₂ T d ρ₁ ζ) (kStop ρ₂ T d ρ₁ ζ).toNNReal) := by
        unfold kLife capLife
        rw [ite_eq_right hfin]
      rw [hV, ← hs', has, ENNReal.ofReal_coe_nnreal] at hq'
      exact lt_irrefl _ hq'

/-- At a finite capacity lifetime the chart path ends at the physical stop. -/
theorem kTrace_end (hfin : kLife U ρ₂ T d ρ₁ ζ ≠ ⊤) :
    kTrace U ρ₂ T d ρ₁ ζ (kLife U ρ₂ T d ρ₁ ζ).toNNReal =
      kPath U ρ₂ T d ρ₁ ζ (kStop ρ₂ T d ρ₁ ζ).toNNReal := by
  have hclk := h.isClockOn (U := U)
  have hLfin := kStop_ne_top_of_kLife hfin
  have hV : (kLife U ρ₂ T d ρ₁ ζ).toNNReal =
      (chartClock (kPath U ρ₂ T d ρ₁ ζ) (kStop ρ₂ T d ρ₁ ζ).toNNReal).toNNReal := by
    unfold kLife capLife
    rw [ite_eq_right hLfin]
    exact ENNReal.toNNReal_coe _
  show kPath U ρ₂ T d ρ₁ ζ (invClock _ _ (kLife U ρ₂ T d ρ₁ ζ).toNNReal) = _
  rw [hV, hclk.invClock_apply (ENNReal.coe_toNNReal hLfin).le]

theorem injOn_kTrace :
    InjOn (kTrace U ρ₂ T d ρ₁ ζ) {s : ℝ≥0 | (s : ℝ≥0∞) ≤ kLife U ρ₂ T d ρ₁ ζ} := by
  have hclk := h.isClockOn (U := U)
  intro a ha b hb hab
  have h1 := h.injOn_kPath (hclk.invClock_spec ha).1 (hclk.invClock_spec hb).1 hab
  exact hclk.strictMonoOn_invClock.injOn ha hb h1

/-- **The stopping rule of the chart path** (see the module docstring). -/
theorem stop_facts (hq : q < 0) (x₁ : ℝ) {Kp : Set ℂ} (hKc : IsClosed Kp)
    (hK : ∀ z : ℂ, z ∈ Kp ↔
      reflectC (z - (x₁ : ℂ)) ∈ retSet (fun s => reflectC (ρ₂ s)) T d ∨ z = (x₁ : ℂ))
    {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {c : BoundaryWord} (hu : RLC.IsUntouchedWord b jumps Kp (fun v => kInv U (T : ℝ) d v + (x₁ : ℂ)) c)
    (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ y : ℝ, ρ₁ t + (x₁ : ℂ) = y →
      (y ≤ x₁ → leftLim b y + θ * chiC κ < sleLambda κ) ∧ (x₁ ≤ y → -sleLambda κ < rightLim b y + θ * chiC κ))
    (hj : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → ∀ y ∈ jumps, y ≠ x₁ → ρ₁ t + (x₁ : ℂ) ≠ y)
    (hseed : ExplState.IsAdmissibleSeed κ (leftLim c.fn 0) (rightLim c.fn 0) θ)
    (hbad : ζ ≠ ⊤ → (ρ₁ ζ.toNNReal + (x₁ : ℂ)).im = 0 ∧
      (((ρ₁ ζ.toNNReal + (x₁ : ℂ)).re ≤ x₁ ∧
          sleLambda κ ≤ leftLim b (ρ₁ ζ.toNNReal + (x₁ : ℂ)).re + θ * chiC κ) ∨
        (x₁ ≤ (ρ₁ ζ.toNNReal + (x₁ : ℂ)).re ∧
          rightLim b (ρ₁ ζ.toNNReal + (x₁ : ℂ)).re + θ * chiC κ ≤ -sleLambda κ)))
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (htype : c ∈ FCDet.typeSet κ θ nL nR ρL ρR)
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0)
    (hg : IsGeneratingTrace W (kLife U ρ₂ T d ρ₁ ζ) (kTrace U ρ₂ T d ρ₁ ζ)) :
    0 < kLife U ρ₂ T d ρ₁ ζ ∧
    ¬ ForceWord.ThresholdCondition ρL ρR 0 (FCDet.typeXL κ θ nL nR ρL ρR c) (FCDet.typeXR κ θ nL nR ρL ρR c) ∧
    (∀ q' : ℝ≥0, 0 < q' → (q' : ℝ≥0∞) < kLife U ρ₂ T d ρ₁ ζ →
      ¬ ForceWord.ThresholdCondition ρL ρR (W q')
        (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i) q')
        (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j) q')) ∧
    (∀ q' : ℝ≥0, 0 < q' → (q' : ℝ≥0∞) < kLife U ρ₂ T d ρ₁ ζ →
      kTrace U ρ₂ T d ρ₁ ζ q' ∉ RLC.OrdModel.aStopSet (kEnds U (T : ℝ) d)) ∧
    (kLife U ρ₂ T d ρ₁ ζ ≠ ⊤ →
      ForceWord.ThresholdCondition ρL ρR (W (kLife U ρ₂ T d ρ₁ ζ).toNNReal)
          (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-FCDet.typeXL κ θ nL nR ρL ρR c i)
            (kLife U ρ₂ T d ρ₁ ζ).toNNReal)
          (fun j => rightImg (fun s : ℝ => W s.toNNReal) (FCDet.typeXR κ θ nL nR ρL ρR c j)
            (kLife U ρ₂ T d ρ₁ ζ).toNNReal) ∨
        kTrace U ρ₂ T d ρ₁ ζ (kLife U ρ₂ T d ρ₁ ζ).toNNReal ∈ RLC.OrdModel.aStopSet (kEnds U (T : ℝ) d)) := by
  have hA := h.isAChart x₁ hKc hK
  have hM := h.isAMono x₁ hK
  have hρ0 := h.rho_zero
  have hxK : (x₁ : ℂ) ∈ Kp := (hK _).2 (Or.inr rfl)
  have h0K : kInv U (T : ℝ) d ((0 : ℝ) : ℂ) + (x₁ : ℂ) ∈ Kp := by
    rw [ofReal_zero, h.kInv_zero, zero_add]
    exact hxK
  have ha0 : 0 ≤ markPos U (T : ℝ) 0 := (h.markPos_zero_pos hq).le
  -- the first path is off `Kp` strictly between `0` and the stop
  have hoffK : ∀ s : ℝ≥0, 0 < s → (s : ℝ≥0∞) < kStop ρ₂ T d ρ₁ ζ → ρ₁ s + (x₁ : ℂ) ∉ Kp := by
    intro s hs0 hsL hmem
    rcases (hK _).1 hmem with h1 | h1
    · rw [add_sub_cancel_right] at h1
      exact off_of_lt_kStop hs0 hsL h1
    · have h2 : ρ₁ s = 0 := by
        have := congrArg (fun z : ℂ => z - (x₁ : ℂ)) h1
        simpa only [add_sub_cancel_right, sub_self] using this
      exact hs0.ne' (h.rho_injOn (hsL.le.trans kStop_le) (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ from zero_le)
        (h2.trans hρ0.symm))
  refine ⟨h.kLife_pos, FCPlumb.not_threshold_type_of_admissible hκ htype hseed, fun q' hq0 hq' => ?_,
    fun q' hq0 hq' hmem => ?_, fun hfin => ?_⟩
  · -- no threshold before the stop
    refine FCPlumb.not_threshold_type_geom_of_incident_bounds hκ htype hWc hW0 hg hq0 hq'.le fun him => ?_
    obtain ⟨s, hs0, hsL, hz⟩ := h.exists_time hq0 hq'
    rw [hz] at him ⊢
    have hzr : kPath U ρ₂ T d ρ₁ ζ s = (((kPath U ρ₂ T d ρ₁ ζ s).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    have hψ : kInv U (T : ℝ) d (((kPath U ρ₂ T d ρ₁ ζ s).re : ℝ) : ℂ) + (x₁ : ℂ) = ρ₁ s + (x₁ : ℂ) := by
      rw [← hzr, h.kInv_kPath_of_le hsL.le]
    have hw : kInv U (T : ℝ) d (((kPath U ρ₂ T d ρ₁ ζ s).re : ℝ) : ℂ) + (x₁ : ℂ) ∉ Kp := by
      rw [hψ]
      exact hoffK s hs0 hsL
    exact hA.incident_bounds hb hu (η := fun t => ρ₁ t + (x₁ : ℂ)) hxK h0K hv hj hw hs0
      (lt_of_lt_of_le hsL kStop_le) hψ.symm
  · -- the stop set is avoided
    obtain ⟨s, hs0, hsL, hz⟩ := h.exists_time hq0 hq'
    rw [hz] at hmem
    obtain ⟨him, h1, h2⟩ := (mem_aStopSet_kEnds ha0).1 hmem
    have hzr : kPath U ρ₂ T d ρ₁ ζ s = (((kPath U ρ₂ T d ρ₁ ζ s).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [him])
    have hp := (h.mem_path_iff (kPath U ρ₂ T d ρ₁ ζ s).re).2 ⟨h1, h2⟩
    rw [← hzr, h.kInv_kPath_of_le hsL.le] at hp
    exact off_of_lt_kStop hs0 hsL hp
  · -- a finite capacity lifetime
    have hLfin := kStop_ne_top_of_kLife hfin
    have hend := h.kTrace_end hfin
    set L' := (kStop ρ₂ T d ρ₁ ζ).toNNReal with hL'
    have hL'L : (L' : ℝ≥0∞) = kStop ρ₂ T d ρ₁ ζ := ENNReal.coe_toNNReal hLfin
    have hL'0 : 0 < L' := ENNReal.toNNReal_pos h.stopPos.ne' hLfin
    have hinv := h.kInv_kPath_of_le (U := U) hL'L.le
    by_cases hcontact : reflectC (ρ₁ L') ∈ retSet (fun s => reflectC (ρ₂ s)) T d
    · right
      rw [hend]
      have him : (kPath U ρ₂ T d ρ₁ ζ L').im = 0 := by
        by_contra hne
        have hpos : 0 < (kPath U ρ₂ T d ρ₁ ζ L').im :=
          lt_of_le_of_ne (h.kPath_mem_Hbar L') (Ne.symm hne)
        have h1 := (h.of_im_pos hpos).1
        rw [hinv] at h1
        exact h1 hcontact
      have hzr : kPath U ρ₂ T d ρ₁ ζ L' = (((kPath U ρ₂ T d ρ₁ ζ L').re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [him])
      refine (mem_aStopSet_kEnds ha0).2 ⟨him, (h.mem_path_iff _).1 ?_⟩
      rw [← hzr, hinv]
      exact hcontact
    · left
      have hLζ : kStop ρ₂ T d ρ₁ ζ = ζ := by
        by_contra hne
        exact hcontact (h.mem_retSet_of_kStop_lt (lt_of_le_of_ne kStop_le hne))
      have hζfin : ζ ≠ ⊤ := hLζ ▸ hLfin
      have hζL' : ζ.toNNReal = L' := by rw [hL', hLζ]
      obtain ⟨hbim, hbside⟩ := hbad hζfin
      rw [hζL'] at hbim hbside
      have him : (kPath U ρ₂ T d ρ₁ ζ L').im = 0 := by
        by_contra hne
        have hpos : 0 < (kPath U ρ₂ T d ρ₁ ζ L').im :=
          lt_of_le_of_ne (h.kPath_mem_Hbar L') (Ne.symm hne)
        have h1 := (h.of_im_pos hpos).2
        rw [hinv] at h1
        have h2 : (ρ₁ L' + (x₁ : ℂ)).im = (ρ₁ L').im := by simp
        rw [h2] at hbim
        linarith
      have hzr : kPath U ρ₂ T d ρ₁ ζ L' = (((kPath U ρ₂ T d ρ₁ ζ L').re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [him])
      have hψw : kInv U (T : ℝ) d (((kPath U ρ₂ T d ρ₁ ζ L').re : ℝ) : ℂ) + (x₁ : ℂ) =
          ρ₁ L' + (x₁ : ℂ) := by
        rw [← hzr, hinv]
      have hw : kInv U (T : ℝ) d (((kPath U ρ₂ T d ρ₁ ζ L').re : ℝ) : ℂ) + (x₁ : ℂ) ∉ Kp := by
        rw [hψw]
        intro hmem
        rcases (hK _).1 hmem with h1 | h1
        · rw [add_sub_cancel_right] at h1
          exact hcontact h1
        · have h2 : ρ₁ L' = 0 := by
            have := congrArg (fun z : ℂ => z - (x₁ : ℂ)) h1
            simpa only [add_sub_cancel_right, sub_self] using this
          exact hL'0.ne' (h.rho_injOn (hL'L.le.trans kStop_le) (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ from zero_le)
            (h2.trans hρ0.symm))
      obtain ⟨hlL, hlR⟩ := hA.limits_of_mono hM hb hu hw
      rw [hψw] at hlL hlR
      have hVpos : 0 < (kLife U ρ₂ T d ρ₁ ζ).toNNReal := ENNReal.toNNReal_pos h.kLife_pos.ne' hfin
      have hTU : (((kLife U ρ₂ T d ρ₁ ζ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ kLife U ρ₂ T d ρ₁ ζ :=
        ENNReal.coe_toNNReal_le_self
      have him' : (kTrace U ρ₂ T d ρ₁ ζ (kLife U ρ₂ T d ρ₁ ζ).toNNReal).im = 0 := by
        rw [hend]
        exact him
      have hacc := FCPlumb.zero_side_collisions_of_simple_real_endpoint hg hWc hW0 h.injOn_kTrace hVpos hTU
        him'
      have hw0 : (kPath U ρ₂ T d ρ₁ ζ L').re ≠ 0 := fun h0 => hw (by rw [h0]; exact h0K)
      refine (FCPlumb.threshold_type_geom_iff_accessed_incident_height hκ htype hWc hW0 hg hTU).2 ?_
      rw [hend] at hacc ⊢
      rcases lt_or_gt_of_ne hw0 with hneg | hposw
      · have hlt := hA.neg _ hw hneg
        rw [hψw] at hlt
        rcases hbside with hL₁ | hR₁
        · exact Or.inl ⟨hacc.1 hneg.le, by rw [hlL]; exact hL₁.2⟩
        · exact absurd hR₁.1 (not_le.2 hlt)
      · have hlt := hA.pos _ hw hposw
        rw [hψw] at hlt
        rcases hbside with hL₁ | hR₁
        · exact absurd hL₁.1 (not_le.2 hlt)
        · exact Or.inr ⟨hacc.2 hposw.le, by rw [hlR]; exact hR₁.2⟩

end IsKSample

end Term

end InteractingSLE.RealContact
