import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Metric.Internal
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# Witnesses: the `A`-form is [C]'s intrinsic geodesic of `K`; orientations of `H↓`, `H↑`

Packet P5a. Sources: blueprint Part A, Definition `a:def-witness`, Lemma `a:lem-witness`, Definition
`a:def-H`, Lemma `a:lem-H-incl` ([C] p. 6, l. 273–276; p. 7, l. 361–363); planning audit NA1, items
20, 24, R4, R12.

* The real-parameter extension `witExt γ` of a path `γ : C([0, 1], ℝ^d)` and the witness identity
  along it (`IsWitness.internal_witExt`).
* `witness_curveLengthWith_eq`: lengths of curves along which a distance function grows linearly.
* `IsWitness.internal_annK_eq` (every continuous metric): a witness is an intrinsic `K`-geodesic at
  constant relative speed, `G(γ s, γ t; K) = |s - t| G(γ 0, γ 1; A)`.
* `isWitness_of_internal_annK_eq` (when `G(γ 0, γ 1; A) < ∞`) and `isWitness_iff` (length metrics,
  where finiteness holds by `internal_annA_ne_top`): the converse, i.e. Lemma `a:lem-witness`.
* `hup_subset_hdown` (Lemma `a:lem-H-incl`): `H↑(E, D; b) ⊆ H↓(D, E; b⁻¹)` for `b > 0`.
* Witness API for consumers: `IsWitness.of_internal_eq` (a witness depends only on the `A`-internal
  profile), `isWitness_smul_iff` (invariance under `G ↦ C G`), `isWitness_of_apply_eq` (a global
  constant-speed geodesic in `K` from `∂B_{3/4}` to `∂B_1` is a witness; used for the connectors of
  Lemma `a:lem-connector`(b)).

**Finding (recorded in the handoff).** Lemma `a:lem-witness` is stated in the blueprint "for
every continuous metric `G`". The forward direction holds for every continuous metric. The converse
needs `G(γ 0, γ 1; A) < ∞` (the blueprint's "forces equality in each term" is finite arithmetic);
for a continuous metric without rectifiable paths near `K` the converse can fail, so the iff is
stated for length metrics (the packet's scope: "continuous length metrics"), for which the
finiteness is proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### The unit annuli -/

theorem mem_annK_iff {x : Rd d} : x ∈ annK d ↔ 3 / 4 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 := by
  simp only [annK, annCl, mem_ofPred_eq, sub_zero]

theorem mem_annA_iff {x : Rd d} : x ∈ annA d ↔ 1 / 2 < ‖x‖ ∧ ‖x‖ < 7 / 2 := by
  simp only [annA, ann, mem_ofPred_eq, sub_zero]

theorem annK_subset_annA : annK d ⊆ annA d := by
  intro x hx
  rw [mem_annK_iff] at hx
  rw [mem_annA_iff]
  constructor <;> linarith [hx.1, hx.2]

theorem isOpen_annA : IsOpen (annA d) := isOpen_ann _ _ _

/-! ### The real-parameter extension of a path on `[0, 1]` -/

/-- A path `γ : C([0, 1], ℝ^d)` as a curve `ℝ → ℝ^d` (constant outside `[0, 1]`). -/
def witExt (γ : C(unitInterval, Rd d)) : ℝ → Rd d :=
  Set.IccExtend (zero_le_one' ℝ) γ

theorem witExt_of_mem (γ : C(unitInterval, Rd d)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    witExt γ t = γ ⟨t, ht⟩ :=
  Set.IccExtend_of_mem _ _ ht

@[simp]
theorem witExt_coe (γ : C(unitInterval, Rd d)) (t : unitInterval) : witExt γ t = γ t :=
  Set.IccExtend_val _ _ t

theorem witExt_zero (γ : C(unitInterval, Rd d)) : witExt γ 0 = γ 0 :=
  witExt_coe γ 0

theorem witExt_one (γ : C(unitInterval, Rd d)) : witExt γ 1 = γ 1 :=
  witExt_coe γ 1

theorem continuous_witExt (γ : C(unitInterval, Rd d)) : Continuous (witExt γ) :=
  γ.continuous.Icc_extend'

theorem witExt_mem {γ : C(unitInterval, Rd d)} {S : Set (Rd d)} (hγ : ∀ t, γ t ∈ S) (t : ℝ) :
    witExt γ t ∈ S :=
  hγ _

/-! ### Lengths along which a distance function grows linearly -/

/-- If `δ (P u) (P v) = (v - u) L` for `a ≤ u ≤ v ≤ b`, then the `δ`-length of `P` on `[a, b]` is
`(b - a) L` (every partition sum telescopes). -/
theorem witness_curveLengthWith_eq {X : Type*} {δ : X → X → ℝ≥0∞} {P : ℝ → X} {a b : ℝ}
    (hab : a ≤ b) {L : ℝ≥0∞}
    (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → δ (P u) (P v) = ENNReal.ofReal (v - u) * L) :
    curveLengthWith δ P a b = ENNReal.ofReal (b - a) * L := by
  apply le_antisymm
  · refine partitionSup_le fun p => le_of_eq ?_
    unfold IccPartition.sum
    calc ∑ i ∈ Finset.range p.n, δ (P (p.t i)) (P (p.t (i + 1)))
        = ∑ i ∈ Finset.range p.n, ENNReal.ofReal (p.t (i + 1) - p.t i) * L :=
          Finset.sum_congr rfl fun i hi => by
            obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
            exact h _ _ h1 h2 h3
      _ = (∑ i ∈ Finset.range p.n, ENNReal.ofReal (p.t (i + 1) - p.t i)) * L :=
          (Finset.sum_mul _ _ _).symm
      _ = ENNReal.ofReal (∑ i ∈ Finset.range p.n, (p.t (i + 1) - p.t i)) * L := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i hi =>
            sub_nonneg.2 (p.step (Finset.mem_range.1 hi)).2.1]
      _ = ENNReal.ofReal (b - a) * L := by
          rw [Finset.sum_range_sub (fun i => p.t i) p.n, p.last, p.zero]
  · calc ENNReal.ofReal (b - a) * L = δ (P a) (P b) := (h a b le_rfl hab le_rfl).symm
      _ ≤ curveLengthWith δ P a b := le_curveLengthWith hab

/-! ### Witnesses -/

namespace IsWitness

variable {G : ContMetric d} {γ : C(unitInterval, Rd d)}

theorem norm_apply_zero (h : IsWitness G γ) : ‖γ 0‖ = 3 / 4 := h.1

theorem norm_apply_one (h : IsWitness G γ) : ‖γ 1‖ = 1 := h.2.1

theorem mem_annK (h : IsWitness G γ) (t : unitInterval) : γ t ∈ annK d := h.2.2.1 t

theorem internal_eq (h : IsWitness G γ) (s t : unitInterval) :
    G.internal (annA d) (γ s) (γ t) =
      ENNReal.ofReal |(s : ℝ) - t| * G.internal (annA d) (γ 0) (γ 1) :=
  h.2.2.2 s t

/-- The witness identity along the real-parameter extension. -/
theorem internal_witExt (h : IsWitness G γ) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    G.internal (annA d) (witExt γ s) (witExt γ t) =
      ENNReal.ofReal |s - t| * G.internal (annA d) (γ 0) (γ 1) := by
  rw [witExt_of_mem γ hs, witExt_of_mem γ ht]
  exact h.internal_eq ⟨s, hs⟩ ⟨t, ht⟩

/-- Along a witness, `G(γ s, γ t; K) ≤ (t - s) G(γ 0, γ 1; A)` for `s ≤ t` (the sub-path lies in
`K` and its partition sums for `G(·, ·; A)` telescope). -/
theorem internal_annK_witExt_le (h : IsWitness G γ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1) :
    G.internal (annK d) (witExt γ s) (witExt γ t) ≤
      ENNReal.ofReal (t - s) * G.internal (annA d) (γ 0) (γ 1) := by
  have hc : ContinuousOn (witExt γ) (Icc s t) := (continuous_witExt γ).continuousOn
  have hK : MapsTo (witExt γ) (Icc s t) (annK d) := fun u _ => witExt_mem h.mem_annK u
  calc G.internal (annK d) (witExt γ s) (witExt γ t) ≤ G.len (witExt γ) s t :=
        G.internal_le_len hst hc hK
    _ = curveLengthWith (G.internal (annA d)) (witExt γ) s t :=
        (G.curveLengthWith_internal hc (hK.mono_right annK_subset_annA)).symm
    _ = ENNReal.ofReal (t - s) * G.internal (annA d) (γ 0) (γ 1) := by
        refine witness_curveLengthWith_eq hst fun u v hu huv hv => ?_
        rw [h.internal_witExt ⟨hs.trans hu, (huv.trans hv).trans ht⟩
          ⟨(hs.trans hu).trans huv, hv.trans ht⟩, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 huv)]

/-- **A witness is an intrinsic `K`-geodesic at constant relative speed** (Lemma `a:lem-witness`,
forward direction; every continuous metric): `G(γ s, γ t; K) = |s - t| G(γ 0, γ 1; A)`. -/
theorem internal_annK_eq (h : IsWitness G γ) (s t : unitInterval) :
    G.internal (annK d) (γ s) (γ t) =
      ENNReal.ofReal |(s : ℝ) - t| * G.internal (annA d) (γ 0) (γ 1) := by
  refine le_antisymm ?_ ?_
  · rcases le_total (s : ℝ) t with hst | hts
    · have := h.internal_annK_witExt_le s.2.1 hst t.2.2
      rw [witExt_coe, witExt_coe] at this
      rwa [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)]
    · have := h.internal_annK_witExt_le t.2.1 hts s.2.2
      rw [witExt_coe, witExt_coe, G.internal_comm] at this
      rwa [abs_of_nonneg (sub_nonneg.2 hts)]
  · rw [← h.internal_eq s t]
    exact G.internal_anti annK_subset_annA _ _

end IsWitness

/-- For a length metric, the `A`-internal distance of two points joined by a path inside `K` is
finite (the path lies in one connected component of the open set `A`). -/
theorem internal_annA_ne_top {G : ContMetric d} (hG : G.IsLength) {γ : C(unitInterval, Rd d)}
    (hK : ∀ t, γ t ∈ annK d) (s t : unitInterval) :
    G.internal (annA d) (γ s) (γ t) ≠ ⊤ := by
  have hA : ∀ u, γ u ∈ annA d := fun u => annK_subset_annA (hK u)
  set C := connectedComponentIn (annA d) (γ s) with hC
  have hrange : range γ ⊆ C :=
    (isConnected_range γ.continuous).isPreconnected.subset_connectedComponentIn
      (mem_range_self s) (range_subset_iff.2 hA)
  refine ne_top_of_le_ne_top ?_
    (G.internal_anti (connectedComponentIn_subset (annA d) (γ s)) (γ s) (γ t))
  exact G.internal_ne_top_of_isPreconnected hG isOpen_annA.connectedComponentIn
    isPreconnected_connectedComponentIn (hrange (mem_range_self s)) (hrange (mem_range_self t))

/-- **Converse of Lemma `a:lem-witness`** (finite case): a path in `K` from `∂B_{3/4}` to `∂B_1`
with `G(γ s, γ t; K) = |s - t| G(γ 0, γ 1; A)` for all `s, t` is a witness, provided
`G(γ 0, γ 1; A) < ∞`. -/
theorem isWitness_of_internal_annK_eq {G : ContMetric d} {γ : C(unitInterval, Rd d)}
    (h0 : ‖γ 0‖ = 3 / 4) (h1 : ‖γ 1‖ = 1) (hK : ∀ t, γ t ∈ annK d)
    (hfin : G.internal (annA d) (γ 0) (γ 1) ≠ ⊤)
    (hKeq : ∀ s t : unitInterval, G.internal (annK d) (γ s) (γ t) =
      ENNReal.ofReal |(s : ℝ) - t| * G.internal (annA d) (γ 0) (γ 1)) :
    IsWitness G γ := by
  refine ⟨h0, h1, hK, ?_⟩
  set L := G.internal (annA d) (γ 0) (γ 1) with hL
  -- the upper bound from `A ⊇ K`
  have hup : ∀ s t : unitInterval,
      G.internal (annA d) (γ s) (γ t) ≤ ENNReal.ofReal |(s : ℝ) - t| * L := fun s t =>
    (G.internal_anti annK_subset_annA _ _).trans (hKeq s t).le
  -- the ordered case
  have key : ∀ s t : unitInterval, (s : ℝ) ≤ t →
      G.internal (annA d) (γ s) (γ t) = ENNReal.ofReal |(s : ℝ) - t| * L := by
    intro s t hst
    refine le_antisymm (hup s t) ?_
    by_contra hlt
    push Not at hlt
    have h0s := hup 0 s
    have ht1 := hup t 1
    rw [Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg s.2.1] at h0s
    rw [Set.Icc.coe_one, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 t.2.2)] at ht1
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hst)] at hlt
    have hfin1 : ENNReal.ofReal (s : ℝ) * L ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have htri : L ≤ G.internal (annA d) (γ 0) (γ s) + G.internal (annA d) (γ s) (γ t) +
        G.internal (annA d) (γ t) (γ 1) :=
      (G.internal_triangle _ _ (γ t) _).trans
        (add_le_add (G.internal_triangle _ _ (γ s) _) le_rfl)
    have hsum : G.internal (annA d) (γ 0) (γ s) + G.internal (annA d) (γ s) (γ t) +
        G.internal (annA d) (γ t) (γ 1) <
        ENNReal.ofReal (s : ℝ) * L + ENNReal.ofReal ((t : ℝ) - s) * L +
          ENNReal.ofReal (1 - (t : ℝ)) * L := by
      refine ENNReal.add_lt_add_of_lt_of_le ?_ ?_ ht1
      · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) ht1
      · exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top hfin1 h0s) h0s hlt
    have hone : ENNReal.ofReal (s : ℝ) * L + ENNReal.ofReal ((t : ℝ) - s) * L +
        ENNReal.ofReal (1 - (t : ℝ)) * L = L := by
      rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add s.2.1 (sub_nonneg.2 hst),
        ← ENNReal.ofReal_add (by linarith [s.2.1, hst]) (sub_nonneg.2 t.2.2)]
      norm_num
    rw [hone] at hsum
    exact (lt_irrefl L) (htri.trans_lt hsum)
  intro s t
  rcases le_total (s : ℝ) t with hst | hts
  · exact key s t hst
  · rw [G.internal_comm, abs_sub_comm]
    exact key t s hts

/-- **Lemma `a:lem-witness`** (for length metrics): a path in `K` from `∂B_{3/4}` to `∂B_1` is a
witness iff it is an intrinsic `G`-geodesic of `K` at constant relative speed whose length is
`G(γ 0, γ 1; A)`, i.e. `G(γ s, γ t; K) = |s - t| G(γ 0, γ 1; A)` for all `s, t` ([C]'s
definition, NA1's shape). -/
theorem isWitness_iff {G : ContMetric d} (hG : G.IsLength) {γ : C(unitInterval, Rd d)}
    (h0 : ‖γ 0‖ = 3 / 4) (h1 : ‖γ 1‖ = 1) (hK : ∀ t, γ t ∈ annK d) :
    IsWitness G γ ↔ ∀ s t : unitInterval, G.internal (annK d) (γ s) (γ t) =
      ENNReal.ofReal |(s : ℝ) - t| * G.internal (annA d) (γ 0) (γ 1) :=
  ⟨fun h => h.internal_annK_eq,
    isWitness_of_internal_annK_eq h0 h1 hK (internal_annA_ne_top hG hK 0 1)⟩

/-! ### Witness API: locality, scaling, global geodesics -/

/-- A witness depends only on the `A`-internal profile of the metric. -/
theorem IsWitness.of_internal_eq {G G' : ContMetric d} {γ : C(unitInterval, Rd d)}
    (h : IsWitness G γ)
    (heq : ∀ z ∈ annA d, ∀ w ∈ annA d, G'.internal (annA d) z w = G.internal (annA d) z w) :
    IsWitness G' γ := by
  have hA : ∀ t, γ t ∈ annA d := fun t => annK_subset_annA (h.mem_annK t)
  refine ⟨h.norm_apply_zero, h.norm_apply_one, h.mem_annK, fun s t => ?_⟩
  rw [heq _ (hA s) _ (hA t), heq _ (hA 0) _ (hA 1)]
  exact h.internal_eq s t

/-- Witnesses are invariant under scaling the metric. -/
theorem isWitness_smul_iff {G : ContMetric d} {C : ℝ} (hC : 0 < C)
    {γ : C(unitInterval, Rd d)} : IsWitness (G.smul C hC) γ ↔ IsWitness G γ := by
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 hC).ne'
  unfold IsWitness
  simp only [ContMetric.internal_smul hC, mul_left_comm _ (ENNReal.ofReal C),
    ENNReal.mul_right_inj hC0 ENNReal.ofReal_ne_top]

/-- **A global constant-speed geodesic in `K` is a witness.** If `γ` runs in `K` from `∂B_{3/4}`
to `∂B_1` and `G(γ s, γ t) = lam |s - t|` for all `s, t`, then `G(γ s, γ t; A) = lam |s - t|` and
`γ` is a witness for `G` with `G(γ 0, γ 1; A) = lam`. -/
theorem isWitness_of_apply_eq {G : ContMetric d} {γ : C(unitInterval, Rd d)} {lam : ℝ}
    (h0 : ‖γ 0‖ = 3 / 4) (h1 : ‖γ 1‖ = 1) (hK : ∀ t, γ t ∈ annK d)
    (hgeo : ∀ s t : unitInterval, G.1 (γ s, γ t) = lam * |(s : ℝ) - t|) :
    IsWitness G γ ∧ G.internal (annA d) (γ 0) (γ 1) = ENNReal.ofReal lam := by
  -- the ordered case
  have key : ∀ s t : unitInterval, (s : ℝ) ≤ t →
      G.internal (annA d) (γ s) (γ t) = ENNReal.ofReal (lam * |(s : ℝ) - t|) := by
    intro s t hst
    refine le_antisymm ?_ (by rw [← hgeo s t]; exact G.ofReal_le_internal _ _ _)
    have hc : ContinuousOn (witExt γ) (Icc (s : ℝ) t) := (continuous_witExt γ).continuousOn
    have hA : MapsTo (witExt γ) (Icc (s : ℝ) t) (annA d) :=
      fun u _ => annK_subset_annA (witExt_mem hK u)
    have hlin : ∀ u v, (s : ℝ) ≤ u → u ≤ v → v ≤ t →
        edist ((G.pt ∘ witExt γ) u) ((G.pt ∘ witExt γ) v) =
          ENNReal.ofReal (v - u) * ENNReal.ofReal lam := by
      intro u v hu huv hv
      have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨s.2.1.trans hu, (huv.trans hv).trans t.2.2⟩
      have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨(s.2.1.trans hu).trans huv, hv.trans t.2.2⟩
      rw [Function.comp_apply, Function.comp_apply, G.edist_pt, witExt_of_mem γ hu',
        witExt_of_mem γ hv', hgeo, ← ENNReal.ofReal_mul (sub_nonneg.2 huv), abs_sub_comm,
        abs_of_nonneg (sub_nonneg.2 huv), mul_comm]
    calc G.internal (annA d) (γ s) (γ t)
          = G.internal (annA d) (witExt γ s) (witExt γ t) := by rw [witExt_coe, witExt_coe]
      _ ≤ G.len (witExt γ) s t := G.internal_le_len hst hc hA
      _ = curveLengthWith edist (G.pt ∘ witExt γ) s t := by
          rw [ContMetric.len_def, curveLengthWith_edist]
      _ = ENNReal.ofReal ((t : ℝ) - s) * ENNReal.ofReal lam :=
          witness_curveLengthWith_eq hst hlin
      _ = ENNReal.ofReal (lam * |(s : ℝ) - t|) := by
          rw [← ENNReal.ofReal_mul (sub_nonneg.2 hst), abs_sub_comm,
            abs_of_nonneg (sub_nonneg.2 hst), mul_comm]
  have hint : ∀ s t : unitInterval,
      G.internal (annA d) (γ s) (γ t) = ENNReal.ofReal (lam * |(s : ℝ) - t|) := by
    intro s t
    rcases le_total (s : ℝ) t with hst | hts
    · exact key s t hst
    · rw [G.internal_comm, abs_sub_comm]
      exact key t s hts
  have h01 : G.internal (annA d) (γ 0) (γ 1) = ENNReal.ofReal lam := by
    rw [hint, Set.Icc.coe_zero, Set.Icc.coe_one, zero_sub, abs_neg, abs_one, mul_one]
  refine ⟨⟨h0, h1, hK, fun s t => ?_⟩, h01⟩
  rw [hint, h01, ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

/-! ### Orientations -/

/-- **Orientations** (Lemma `a:lem-H-incl`; NA1 item 24, R12): `H↑(E, D; b) ⊆ H↓(D, E; b⁻¹)` for
`b > 0`. Both events are defined through a witness for `ρ^E`. -/
theorem hup_subset_hdown {D E : DistRd d → ContMetric d} {b : ℝ} (hb : 0 < b) :
    Hup E D b ⊆ Hdown D E b⁻¹ := by
  rintro g ⟨γ, hγ, hlt⟩
  refine ⟨γ, hγ, ?_⟩
  have hone : ENNReal.ofReal b⁻¹ * ENNReal.ofReal b = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hb.le), inv_mul_cancel₀ hb.ne', ENNReal.ofReal_one]
  calc (rho E g).internal (annA d) (γ 0) (γ 1)
      = ENNReal.ofReal b⁻¹ *
          (ENNReal.ofReal b * (rho E g).internal (annA d) (γ 0) (γ 1)) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal b⁻¹ * (rho D g).internal (annA d) (γ 0) (γ 1) :=
        mul_le_mul_right hlt.le _

end HigherDimLQGContinuity
