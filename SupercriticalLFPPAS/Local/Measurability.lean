import SupercriticalLFPPAS.Local.Basic
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.FellBase
import SupercriticalLQGUniqueness.B2.LscTop.Limits
import LQGMetric.Meas.UM
import LQGMetric.Field.StandardBorelRange

/-!
# Measurability of the event of Lemma 3.2 (packet P32; replacement of Remark 3.3)

Planning audit `planning/audits/SB1-sections-1-3.md` A13 (1)–(4), replacing the sketch of Remark 3.3
(l. 280–301; SB1 item 28):

* on a compact set `K`, the internal metric extended by `⊤` off `K × K` (`internalExt`) is jointly
  lower semicontinuous on `LSCMetric × ℂ × ℂ` (from the host's
  `internal_compact_joint_lsc`, through a closed embedding);
* an infimum of a jointly lower semicontinuous function over a compact set is lower semicontinuous
  (`lowerSemicontinuous_iInf_compact`), so the internal set distance between moving open balls
  (`ballSetDist`), a countable infimum over a compact exhaustion of the balls, is jointly Borel;
* the event of Lemma 3.2 (with lengths in arbitrary measurable units) for two measurable
  field-to-metric maps is universally measurable on the standard Borel field space: its complement
  is the projection of a Borel set (`umeasurableSet_lemma32EventU`, via
  `LQGMetric.UMeasurableSet.setOf_forall`).

No Hölder bound, path-space projection or separability of the metric is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

/-- An infimum of a jointly lower semicontinuous function over a compact set is lower
semicontinuous in the remaining variable. -/
theorem lowerSemicontinuous_iInf_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set Y} (hC : IsCompact C) {Ψ : X × Y → ℝ≥0∞} (hΨ : LowerSemicontinuous Ψ) :
    LowerSemicontinuous fun x => ⨅ y ∈ C, Ψ (x, y) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  rcases C.eq_empty_or_nonempty with hC0 | hCne
  · have hf : (fun x => ⨅ y ∈ C, Ψ (x, y)) = fun _ => ⊤ := by
      funext x
      simp [hC0]
    rw [hf]
    by_cases hc : (⊤ : ℝ≥0∞) ≤ c
    · convert isClosed_univ
      ext x
      simp [hc]
    · convert isClosed_empty
      ext x
      simp [hc]
  · have : CompactSpace C := isCompact_iff_compactSpace.1 hC
    have heq : (fun x => ⨅ y ∈ C, Ψ (x, y)) ⁻¹' Iic c =
        Prod.fst '' {p : X × C | Ψ (p.1, (p.2 : Y)) ≤ c} := by
      ext x
      constructor
      · intro hx
        have hcont : Continuous fun y : Y => (x, y) := continuous_const.prodMk continuous_id
        have hlsc : LowerSemicontinuousOn (fun y => Ψ (x, y)) C :=
          (hΨ.comp hcont).lowerSemicontinuousOn C
        obtain ⟨y, hy, hmin⟩ := hlsc.exists_isMinOn hCne hC
        refine ⟨(x, ⟨y, hy⟩), ?_, rfl⟩
        show Ψ (x, y) ≤ c
        calc Ψ (x, y) ≤ ⨅ y' ∈ C, Ψ (x, y') := le_iInf₂ fun y' hy' => hmin hy'
          _ ≤ c := hx
      · rintro ⟨⟨x', y⟩, hle, rfl⟩
        exact (biInf_le (fun y' => Ψ (x', y')) y.2).trans (show Ψ (x', (y : Y)) ≤ c from hle)
    rw [heq]
    refine isClosedMap_fst_of_compactSpace _ ?_
    have hc : Continuous fun p : X × C => (p.1, (p.2 : Y)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (hΨ.comp hc).isClosed_preimage c

open Classical in
/-- The internal metric of `K`, extended by `⊤` off `K × K`. -/
def internalExt (K : Set ℂ) (T : LSCMetric) (x y : ℂ) : ℝ≥0∞ :=
  if h : x ∈ K ∧ y ∈ K then T.internal K (⟨x, h.1⟩, ⟨y, h.2⟩) else ⊤

theorem internalExt_of_mem {K : Set ℂ} (T : LSCMetric) (x y : K) :
    internalExt K T x y = T.internal K (x, y) := by
  rw [internalExt, dite_eq_left ⟨x.2, y.2⟩]

/-- **Joint lower semicontinuity of compact internal metrics** (A13 (2)), extended by `⊤`. -/
theorem lowerSemicontinuous_internalExt {K : Set ℂ} (hK : IsCompact K) :
    LowerSemicontinuous fun q : LSCMetric × (ℂ × ℂ) => internalExt K q.1 q.2.1 q.2.2 := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c = ⊤
  · subst hc
    convert isClosed_univ
    ext q
    simp
  · let ι : LSCMetric × (K × K) → LSCMetric × (ℂ × ℂ) := fun q => (q.1, ((q.2.1 : ℂ), (q.2.2 : ℂ)))
    have hι : Topology.IsClosedEmbedding ι :=
      Topology.IsClosedEmbedding.id.prodMap
        (hK.isClosed.isClosedEmbedding_subtypeVal.prodMap hK.isClosed.isClosedEmbedding_subtypeVal)
    have heq : (fun q : LSCMetric × (ℂ × ℂ) => internalExt K q.1 q.2.1 q.2.2) ⁻¹' Iic c =
        ι '' {q : LSCMetric × (K × K) | q.1.internal K (q.2.1, q.2.2) ≤ c} := by
      ext ⟨T, x, y⟩
      simp only [mem_preimage, mem_Iic, mem_image]
      constructor
      · intro hq
        by_cases hxy : x ∈ K ∧ y ∈ K
        · refine ⟨(T, (⟨x, hxy.1⟩, ⟨y, hxy.2⟩)), ?_, rfl⟩
          show T.internal K (⟨x, hxy.1⟩, ⟨y, hxy.2⟩) ≤ c
          simpa only [internalExt, dite_eq_left hxy] using hq
        · simp only [internalExt, dite_eq_right hxy, top_le_iff] at hq
          exact absurd hq hc
      · rintro ⟨⟨T', x', y'⟩, hle, heq⟩
        simp only [ι, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        rw [internalExt_of_mem]
        exact hle
    rw [heq]
    exact hι.isClosedMap _
      ((Uniqueness.Toolkit.MovingEndpoints.internal_compact_joint_lsc hK).isClosed_preimage c)

/-- The internal set distance `T(B_η(u), B_η(v); K)` between two open Euclidean balls. -/
def ballSetDist (K : Set ℂ) (η : ℝ) (T : LSCMetric) (u v : ℂ) : ℝ≥0∞ :=
  T.internalSetDist K {x | (x : ℂ) ∈ ball u η} {x | (x : ℂ) ∈ ball v η}

theorem ballSetDist_eq_iInf (K : Set ℂ) (η : ℝ) (T : LSCMetric) (u v : ℂ) :
    ballSetDist K η T u v =
      ⨅ a ∈ ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η, internalExt K T (u + a.1) (v + a.2) := by
  unfold ballSetDist LSCMetric.internalSetDist
  apply le_antisymm
  · refine le_iInf₂ fun a ha => ?_
    by_cases hxy : u + a.1 ∈ K ∧ v + a.2 ∈ K
    · have e : internalExt K T (u + a.1) (v + a.2) =
          T.internal K (⟨u + a.1, hxy.1⟩, ⟨v + a.2, hxy.2⟩) := internalExt_of_mem T ⟨_, hxy.1⟩ ⟨_, hxy.2⟩
      rw [e]
      have hx : ((⟨u + a.1, hxy.1⟩ : K) : ℂ) ∈ ball u η := by
        show u + a.1 ∈ ball u η
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        have := ha.1
        rwa [mem_ball, dist_zero_right] at this
      have hy : ((⟨v + a.2, hxy.2⟩ : K) : ℂ) ∈ ball v η := by
        show v + a.2 ∈ ball v η
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
        have := ha.2
        rwa [mem_ball, dist_zero_right] at this
      exact iInf_le_of_le ⟨u + a.1, hxy.1⟩ (iInf_le_of_le hx
        (iInf_le_of_le ⟨v + a.2, hxy.2⟩ (iInf_le_of_le hy le_rfl)))
    · have e : internalExt K T (u + a.1) (v + a.2) = ⊤ := by
        unfold internalExt
        rw [dite_eq_right hxy]
      rw [e]
      exact le_top
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    have ha : ((x : ℂ) - u, (y : ℂ) - v) ∈ ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, ← dist_eq_norm]
        exact hx
      · rw [mem_ball, dist_zero_right, ← dist_eq_norm]
        exact hy
    refine (biInf_le (fun a : ℂ × ℂ => internalExt K T (u + a.1) (v + a.2)) ha).trans
      (le_of_eq ?_)
    simp only [add_sub_cancel]
    exact internalExt_of_mem T x y

private theorem secondCountable_lscMetric' : SecondCountableTopology LSCMetric :=
  LSCMetric.isInducing_toLSCFun.secondCountableTopology

attribute [local instance] secondCountable_lscMetric' B2.LscTop.borelSpace_LSCMetric

/-- **Joint measurability of `internalExt`.** -/
theorem measurable_internalExt {K : Set ℂ} (hK : IsCompact K) :
    Measurable fun q : LSCMetric × (ℂ × ℂ) => internalExt K q.1 q.2.1 q.2.2 :=
  (lowerSemicontinuous_internalExt hK).measurable

/-- **Joint measurability of the internal set distance between moving open balls** (A13 (3)). -/
theorem measurable_ballSetDist {K : Set ℂ} (hK : IsCompact K) (η : ℝ) :
    Measurable fun q : LSCMetric × (ℂ × ℂ) => ballSetDist K η q.1 q.2.1 q.2.2 := by
  set C : ℕ → Set (ℂ × ℂ) := fun n =>
    closedBall (0 : ℂ) (η - 1 / ((n : ℝ) + 1)) ×ˢ closedBall (0 : ℂ) (η - 1 / ((n : ℝ) + 1))
  have hCc : ∀ n, IsCompact (C n) := fun n =>
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hunion : ball (0 : ℂ) η ×ˢ ball (0 : ℂ) η = ⋃ n, C n := by
    ext a
    simp only [mem_prod, mem_ball, dist_zero_right, mem_iUnion, mem_closedBall, C]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (max_lt h1 h2))
      refine ⟨n, ?_, ?_⟩
      · linarith [le_max_left ‖a.1‖ ‖a.2‖]
      · linarith [le_max_right ‖a.1‖ ‖a.2‖]
    · rintro ⟨n, h1, h2⟩
      have : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      exact ⟨by linarith, by linarith⟩
  have heq : (fun q : LSCMetric × (ℂ × ℂ) => ballSetDist K η q.1 q.2.1 q.2.2) =
      fun q => ⨅ n : ℕ, ⨅ a ∈ C n, internalExt K q.1 (q.2.1 + a.1) (q.2.2 + a.2) := by
    funext q
    rw [ballSetDist_eq_iInf, hunion, iInf_iUnion]
  rw [heq]
  refine Measurable.iInf fun n => ?_
  have hΨ : LowerSemicontinuous fun p : (LSCMetric × (ℂ × ℂ)) × (ℂ × ℂ) =>
      internalExt K p.1.1 (p.1.2.1 + p.2.1) (p.1.2.2 + p.2.2) := by
    have hc : Continuous fun p : (LSCMetric × (ℂ × ℂ)) × (ℂ × ℂ) =>
        (p.1.1, (p.1.2.1 + p.2.1, p.1.2.2 + p.2.2)) := by
      fun_prop
    exact (lowerSemicontinuous_internalExt hK).comp hc
  exact (lowerSemicontinuous_iInf_compact (hCc n) hΨ).measurable

/-- The pointwise relation behind one direction of Lemma 3.2, at a pair `(u, v)` of points. -/
def OneWayAt (S T : LSCMetric) (η ν M : ℝ) (u v : ℂ) : Prop :=
  ‖u‖ = 1 → ‖v‖ = 2 → internalExt srcV S u v ≤ ENNReal.ofReal M →
    ballSetDist tgtU η T u v ≤ internalExt srcV S u v + ENNReal.ofReal ν

theorem oneWayCompare_iff_forall (S T : LSCMetric) (η ν M : ℝ) :
    OneWayCompare S T η ν M ↔ ∀ p : ℂ × ℂ, OneWayAt S T η ν M p.1 p.2 := by
  constructor
  · rintro hO ⟨u, v⟩ hu hv hM
    have huV : u ∈ srcV := ⟨by rw [hu]; norm_num, by rw [hu]; norm_num⟩
    have hvV : v ∈ srcV := ⟨by rw [hv]; norm_num, by rw [hv]; norm_num⟩
    have e := internalExt_of_mem S ⟨u, huV⟩ ⟨v, hvV⟩
    simp only at e
    rw [e] at hM ⊢
    exact hO ⟨u, huV⟩ ⟨v, hvV⟩ hu hv hM
  · intro h u v hu hv hM
    have e := internalExt_of_mem S u v
    have := h ((u : ℂ), (v : ℂ)) hu hv (by rw [e]; exact hM)
    rw [e] at this
    exact this

theorem isCompact_srcV : IsCompact srcV := by
  have h : srcV = closedBall (0 : ℂ) 3 \ ball (0 : ℂ) (1 / 2) := by
    ext z
    simp [srcV, mem_closedBall, mem_ball, dist_zero_right, and_comm]
  rw [h]
  exact (isCompact_closedBall _ _).diff isOpen_ball

theorem isCompact_tgtU : IsCompact tgtU := by
  have h : tgtU = closedBall (0 : ℂ) 16 \ ball (0 : ℂ) (1 / 8) := by
    ext z
    simp [tgtU, mem_closedBall, mem_ball, dist_zero_right, and_comm]
  rw [h]
  exact (isCompact_closedBall _ _).diff isOpen_ball

/-- The pointwise relation is a Borel set of `(source metric, target metric, units, points)`. -/
theorem measurableSet_oneWayAt {α : Type*} [MeasurableSpace α] {S T : α → LSCMetric}
    (hS : Measurable S) (hT : Measurable T) {ν M : α → ℝ} (hν : Measurable ν) (hM : Measurable M)
    (η : ℝ) :
    MeasurableSet {q : α × (ℂ × ℂ) | OneWayAt (S q.1) (T q.1) η (ν q.1) (M q.1) q.2.1 q.2.2} := by
  have hgS : Measurable fun q : α × (ℂ × ℂ) => ((S q.1, q.2) : LSCMetric × (ℂ × ℂ)) :=
    (hS.comp measurable_fst).prodMk measurable_snd
  have hgT : Measurable fun q : α × (ℂ × ℂ) => ((T q.1, q.2) : LSCMetric × (ℂ × ℂ)) :=
    (hT.comp measurable_fst).prodMk measurable_snd
  have hI : Measurable fun q : α × (ℂ × ℂ) => internalExt srcV (S q.1) q.2.1 q.2.2 := by
    have h := (measurable_internalExt isCompact_srcV).comp hgS
    exact h
  have hB : Measurable fun q : α × (ℂ × ℂ) => ballSetDist tgtU η (T q.1) q.2.1 q.2.2 := by
    have h := (measurable_ballSetDist isCompact_tgtU η).comp hgT
    exact h
  have hu : MeasurableSet {q : α × (ℂ × ℂ) | ‖q.2.1‖ = 1} :=
    (measurableSet_singleton (1 : ℝ)).preimage
      (measurable_norm.comp (measurable_fst.comp measurable_snd))
  have hv : MeasurableSet {q : α × (ℂ × ℂ) | ‖q.2.2‖ = 2} :=
    (measurableSet_singleton (2 : ℝ)).preimage
      (measurable_norm.comp (measurable_snd.comp measurable_snd))
  have h1 : MeasurableSet {q : α × (ℂ × ℂ) |
      internalExt srcV (S q.1) q.2.1 q.2.2 ≤ ENNReal.ofReal (M q.1)} :=
    measurableSet_le hI (ENNReal.measurable_ofReal.comp (hM.comp measurable_fst))
  have h2 : MeasurableSet {q : α × (ℂ × ℂ) | ballSetDist tgtU η (T q.1) q.2.1 q.2.2 ≤
      internalExt srcV (S q.1) q.2.1 q.2.2 + ENNReal.ofReal (ν q.1)} :=
    measurableSet_le hB (hI.add (ENNReal.measurable_ofReal.comp (hν.comp measurable_fst)))
  have heq : {q : α × (ℂ × ℂ) | OneWayAt (S q.1) (T q.1) η (ν q.1) (M q.1) q.2.1 q.2.2} =
      {q : α × (ℂ × ℂ) | ‖q.2.1‖ = 1}ᶜ ∪ ({q : α × (ℂ × ℂ) | ‖q.2.2‖ = 2}ᶜ ∪
        ({q : α × (ℂ × ℂ) | internalExt srcV (S q.1) q.2.1 q.2.2 ≤ ENNReal.ofReal (M q.1)}ᶜ ∪
          {q : α × (ℂ × ℂ) | ballSetDist tgtU η (T q.1) q.2.1 q.2.2 ≤
            internalExt srcV (S q.1) q.2.1 q.2.2 + ENNReal.ofReal (ν q.1)})) := by
    ext q
    simp only [OneWayAt, mem_ofPred_eq, mem_union, mem_compl_iff]
    tauto
  rw [heq]
  exact hu.compl.union (hv.compl.union (h1.compl.union h2))

/-- **Universal measurability of Lemma 3.2's event** (A13 (4)): for measurable field-to-metric
maps and measurable units, the set of fields at which the event holds is universally measurable. -/
theorem umeasurableSet_lemma32EventU {𝔇 𝔜 : DistC → LSCMetric} (h𝔇 : Measurable 𝔇)
    (h𝔜 : Measurable 𝔜) {τ : DistC → ℝ} (hτ : Measurable τ) (η ν M : ℝ) :
    LQGMetric.UMeasurableSet {g | Lemma32EventU (𝔇 g) (𝔜 g) η ν M (τ g)} := by
  have hνm : Measurable fun g => ν * τ g := measurable_const.mul hτ
  have hMm : Measurable fun g => M * τ g := measurable_const.mul hτ
  have hR : MeasurableSet {q : DistC × (ℂ × ℂ) |
      OneWayAt (𝔇 q.1) (𝔜 q.1) η (ν * τ q.1) (M * τ q.1) q.2.1 q.2.2 ∧
      OneWayAt (𝔜 q.1) (𝔇 q.1) η (ν * τ q.1) (M * τ q.1) q.2.1 q.2.2} :=
    (measurableSet_oneWayAt h𝔇 h𝔜 hνm hMm η).inter (measurableSet_oneWayAt h𝔜 h𝔇 hνm hMm η)
  have h := LQGMetric.UMeasurableSet.setOf_forall hR
  convert h using 1
  ext g
  simp only [mem_ofPred_eq, Lemma32EventU, Lemma32Event, oneWayCompare_iff_forall]
  constructor
  · rintro ⟨h1, h2⟩ p
    exact ⟨h1 p, h2 p⟩
  · intro hp
    exact ⟨fun p => (hp p).1, fun p => (hp p).2⟩

end SupercriticalLFPPAS.Local
