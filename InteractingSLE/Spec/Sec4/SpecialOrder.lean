import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Section 4.2: first contacts, reverse chronological order, no wrap-around, injectivity

Packet PROVE-SEC4-B. The deterministic (pathwise) steps of the proofs of Lemma 4.7, Proposition
4.9 and Aux. lemma 25 of the specification (`source/spec/p097-144.md`, §4.2, pp. 116–127).

A counterflow path `γ` is parametrized on a compact interval `[0, b]` (Lemma 4.7 proof, p. 118:
"parametrize the completed counterflow line on a compact time interval, so that a visit to its
terminal point also has a finite parameter value"), a flow path `η` on `[0, T]` (`T = T_top`).

* `IsFirstHitPoint γ b A z`: `γ|[0,b]` hits `A`, and its first point in `A` is `z`.
* `IsFirstHitPoint.of_tendsto` (Lemma 4.7 proof, p. 118, "This proves the first-contact assertion
  also at the endpoint"): if `γ` first hits `L ∪ η([0, τₙ])` at `η(τₙ)` for a monotone sequence
  `τₙ ↑ τ`, then it first hits `L ∪ η([0, τ])` at `η(τ)`.
* `image_Icc_subset_of_dense` (p. 118, "Their images lie in the completed counterflow range; its
  closedness gives containment of the completed first segment").
* `exists_visit_before` (pp. 118–119, reverse chronological order, simultaneous for all times):
  if the first-hit property holds on a dense set of times and `η` is simple before `T`, then for
  all `0 ≤ s < t ≤ T` the path `γ` visits `η(t)` strictly before its first visit to `η(s)`.
* `mem_image_Icc_of_lt` and `not_exists_wrap` (Proposition 4.9 proof and Figure 4.7, p. 120: no
  times `t₁ < t₂ < t₃` with `η(t₁), η(t₃) ∈ γ([0, τ'])` and `η(t₂) ∉ γ([0, τ'])`).
* `injOn_of_disjoint_image` (Aux. lemma 25 proof, p. 127, last paragraph): no return to the old
  trace after each time of a dense set gives injectivity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Sec4

variable {X : Type*} [TopologicalSpace X]

/-- `z` is the first point of `A` hit by the path `γ` on its parameter interval `[0, b]`: at some
`u ∈ [0, b]`, `γ u = z ∈ A`, and `γ v ∉ A` for every `v ∈ [0, u)` (Lemma 4.7: "`η'` almost surely
first hits `∂_L𝒮 ∪ η([0, τ])` at `η(τ)`"). -/
def IsFirstHitPoint (γ : ℝ → X) (b : ℝ) (A : Set X) (z : X) : Prop :=
  ∃ u ∈ Icc (0 : ℝ) b, γ u = z ∧ z ∈ A ∧ ∀ v ∈ Ico (0 : ℝ) u, γ v ∉ A

/-- A time before which `γ` avoids `A` is at most every nonnegative time at which `γ` is in `A`. -/
theorem le_of_forall_notMem_of_mem {Y : Type*} {γ : ℝ → Y} {A : Set Y} {u : ℝ}
    (hbefore : ∀ v ∈ Ico (0 : ℝ) u, γ v ∉ A) {w : ℝ} (hw0 : 0 ≤ w) (hwA : γ w ∈ A) : u ≤ w := by
  by_contra h
  exact hbefore w ⟨hw0, lt_of_not_ge h⟩ hwA

/-- A real number in the closure of `D` with an open interval around it meets `D` there. -/
theorem exists_mem_Ioo_of_subset_closure {D : Set ℝ} {T : ℝ} (hD : Icc 0 T ⊆ closure D)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) : ∃ q ∈ D, s < q ∧ q < t := by
  have hm : (s + t) / 2 ∈ closure D := hD ⟨by linarith, by linarith⟩
  obtain ⟨q, hq, hqD⟩ := mem_closure_iff.1 hm (Ioo s t) isOpen_Ioo ⟨by linarith, by linarith⟩
  exact ⟨q, hqD, hq.1, hq.2⟩

/-- `t` is in the closure of `D ∩ (q, t)` when `D` is dense in `[0, T]`, `0 ≤ q < t ≤ T`. -/
theorem mem_closure_inter_Ioo {D : Set ℝ} {T : ℝ} (hD : Icc 0 T ⊆ closure D) {q t : ℝ}
    (hq : 0 ≤ q) (hqt : q < t) (ht : t ≤ T) : t ∈ closure (D ∩ Ioo q t) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨r, hrD, hr1, hr2⟩ := exists_mem_Ioo_of_subset_closure hD (le_trans hq (le_max_left q
    (t - ε / 2))) (max_lt hqt (by linarith)) ht
  refine ⟨r, ⟨hrD, (le_max_left _ _).trans_lt hr1, hr2⟩, ?_⟩
  have : t - ε / 2 < r := (le_max_right _ _).trans_lt hr1
  rw [Real.dist_eq, abs_of_pos (by linarith)]
  linarith

/-- **First contact at the endpoint** (Lemma 4.7 proof, p. 118). Let `γ` be continuous on
`[0, b]`, and let `τₙ ↑ τ` be a monotone sequence with `τₙ ≤ τ`, `τₙ → τ` and `η(τₙ) → η(τ)`.
If, for every `n`, `γ` first hits `L ∪ η([0, τₙ])` at `η(τₙ)`, then `γ` first hits
`L ∪ η([0, τ])` at `η(τ)`. (The contact times decrease; their limit is a visit of `η(τ)`; an
earlier contact with `L ∪ η([0, τ))` would be a contact with one of the smaller sets.) -/
theorem IsFirstHitPoint.of_tendsto [T2Space X] {γ η : ℝ → X} {b τ : ℝ} {L : Set X} {τs : ℕ → ℝ}
    (hγ : ContinuousOn γ (Icc 0 b)) (hτ0 : 0 ≤ τ) (hmono : Monotone τs) (hle : ∀ n, τs n ≤ τ)
    (hlim : Tendsto τs atTop (𝓝 τ)) (hη : Tendsto (fun n => η (τs n)) atTop (𝓝 (η τ)))
    (hhit : ∀ n, IsFirstHitPoint γ b (L ∪ η '' Icc 0 (τs n)) (η (τs n))) :
    IsFirstHitPoint γ b (L ∪ η '' Icc 0 τ) (η τ) := by
  choose u hu hγu hmem hbefore using hhit
  have hsub : ∀ {m n : ℕ}, m ≤ n → L ∪ η '' Icc 0 (τs m) ⊆ L ∪ η '' Icc 0 (τs n) :=
    fun hmn => union_subset_union_right _ (image_mono (Icc_subset_Icc_right (hmono hmn)))
  have hanti : Antitone u := by
    intro m n hmn
    exact le_of_forall_notMem_of_mem (hbefore n) (hu m).1
      (hsub hmn (by rw [hγu m]; exact hmem m))
  have hbdd : BddBelow (range u) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (hu n).1⟩
  set us : ℝ := ⨅ n, u n with hus
  have hus_le : ∀ n, us ≤ u n := fun n => ciInf_le hbdd n
  have hus0 : 0 ≤ us := le_ciInf fun n => (hu n).1
  have husb : us ≤ b := (hus_le 0).trans (hu 0).2
  have hulim : Tendsto u atTop (𝓝 us) := tendsto_atTop_ciInf hanti hbdd
  -- the limit time is a visit of `η τ`
  have hγus : γ us = η τ := by
    have h1 : Tendsto (fun n => γ (u n)) atTop (𝓝 (γ us)) :=
      (hγ us ⟨hus0, husb⟩).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hulim, Eventually.of_forall fun n => hu n⟩)
    have h2 : Tendsto (fun n => γ (u n)) atTop (𝓝 (η τ)) := by
      simp only [hγu]; exact hη
    exact tendsto_nhds_unique h1 h2
  -- the first visit of `η τ` before `us`
  set S : Set ℝ := Icc 0 us ∩ γ ⁻¹' {η τ} with hS
  have hSc : IsClosed S :=
    (hγ.mono (Icc_subset_Icc_right husb)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_singleton
  have hSne : S.Nonempty := ⟨us, ⟨hus0, le_rfl⟩, hγus⟩
  have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hu0S : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  refine ⟨sInf S, ⟨hu0S.1.1, hu0S.1.2.trans husb⟩, hu0S.2, Or.inr ⟨τ, ⟨hτ0, le_rfl⟩, rfl⟩, ?_⟩
  rintro v ⟨hv0, hvlt⟩ hvA
  have hvn : ∀ n, v < u n := fun n => hvlt.trans_le (hu0S.1.2.trans (hus_le n))
  have hne : γ v ≠ η τ := by
    intro heq
    exact absurd (csInf_le hSbdd ⟨⟨hv0, hvlt.le.trans hu0S.1.2⟩, heq⟩) (not_le.2 hvlt)
  rcases hvA with hL | ⟨s, hs, hsη⟩
  · exact hbefore 0 v ⟨hv0, hvn 0⟩ (Or.inl hL)
  · rcases hs.2.lt_or_eq with hsτ | rfl
    · obtain ⟨n, hn⟩ := (hlim.eventually (Ioi_mem_nhds hsτ)).exists
      exact hbefore n v ⟨hv0, hvn n⟩ (Or.inr ⟨s, ⟨hs.1, hn.le⟩, hsη⟩)
    · exact hne hsη.symm

/-- **Containment** (Lemma 4.7 proof, p. 118): if `η(q)` lies in the range `γ([0, b])` for every
`q` of a set `D ⊆ [0, T]` dense in `[0, T]`, then `η([0, T]) ⊆ γ([0, b])` (the range of a
continuous path on a compact interval is closed). -/
theorem image_Icc_subset_of_dense [T2Space X] {γ η : ℝ → X} {b T : ℝ} {D : Set ℝ}
    (hγ : ContinuousOn γ (Icc 0 b)) (hη : ContinuousOn η (Icc 0 T)) (hDsub : D ⊆ Icc 0 T)
    (hD : Icc 0 T ⊆ closure D) (hmem : ∀ q ∈ D, η q ∈ γ '' Icc 0 b) :
    η '' Icc 0 T ⊆ γ '' Icc 0 b := by
  have hcl : IsClosed (γ '' Icc 0 b) := (isCompact_Icc.image_of_continuousOn hγ).isClosed
  rintro _ ⟨x, hx, rfl⟩
  have h1 : η x ∈ closure (η '' D) := ((hη x hx).mono hDsub).mem_closure_image (hD hx)
  exact hcl.closure_subset_iff.2 (image_subset_iff.2 hmem) h1

/-- **Later points are absorbed first** (Lemma 4.7 proof, pp. 118–119: "the counterflow
first-visit times of `η(q_n)` are bounded above by the first-visit time of `η(q)`"). Let `γ` be
continuous on `[0, b]`, `η` continuous on `[0, T]`, and `D ⊆ [0, T)` dense in `[0, T]` such that,
for every `q ∈ D`, `γ` first hits `L ∪ η([0, q])` at `η(q)`. If `γ` visits `η(q)` at a time
`u ∈ [0, b]` (`0 ≤ q`), then it visits `η(t)` by time `u` for every `t ∈ (q, T]`. -/
theorem mem_image_Icc_of_visit [T2Space X] {γ η : ℝ → X} {b T : ℝ} {L : Set X} {D : Set ℝ}
    (hγ : ContinuousOn γ (Icc 0 b)) (hη : ContinuousOn η (Icc 0 T)) (hDsub : D ⊆ Ico 0 T)
    (hD : Icc 0 T ⊆ closure D) (hhit : ∀ q ∈ D, IsFirstHitPoint γ b (L ∪ η '' Icc 0 q) (η q))
    {q u : ℝ} (hq0 : 0 ≤ q) (hu : u ∈ Icc 0 b) (hγu : γ u = η q) {t : ℝ} (hqt : q < t)
    (ht : t ≤ T) : η t ∈ γ '' Icc 0 u := by
  have hvis : η '' (D ∩ Ioo q t) ⊆ γ '' Icc 0 u := by
    rintro _ ⟨q', ⟨hq'D, hqq', -⟩, rfl⟩
    obtain ⟨u', hu', hγu', -, hbef'⟩ := hhit q' hq'D
    refine ⟨u', ⟨hu'.1, ?_⟩, hγu'⟩
    exact le_of_forall_notMem_of_mem hbef' hu.1
      (by rw [hγu]; exact Or.inr ⟨q, ⟨hq0, hqq'.le⟩, rfl⟩)
  have hcl : IsClosed (γ '' Icc 0 u) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono (Icc_subset_Icc_right hu.2))).isClosed
  have htcl : t ∈ closure (D ∩ Ioo q t) := mem_closure_inter_Ioo hD hq0 hqt ht
  have hηt : η t ∈ closure (η '' (D ∩ Ioo q t)) :=
    ((hη t ⟨hq0.trans hqt.le, ht⟩).mono fun x hx =>
      ⟨hq0.trans hx.2.1.le, (hDsub hx.1).2.le⟩).mem_closure_image htcl
  exact hcl.closure_subset_iff.2 hvis hηt

/-- **Reverse chronological order** (Lemma 4.7, "if `s < t` then `η'` hits `η(t)` before
`η(s)`"; proof pp. 118–119, simultaneous for all times). Under the hypotheses of
`mem_image_Icc_of_visit`, and if `η` is injective on `[0, T)`, then for all `0 ≤ s < t ≤ T` the
path `γ` visits `η(t)` at a time `v` up to which it has not visited `η(s)`. (Choose
`q ∈ D ∩ (s, t)`; the first contact with the prefix through `q` is at `η(q) ≠ η(s)`.) -/
theorem exists_visit_before [T2Space X] {γ η : ℝ → X} {b T : ℝ} {L : Set X} {D : Set ℝ}
    (hγ : ContinuousOn γ (Icc 0 b)) (hη : ContinuousOn η (Icc 0 T)) (hinj : InjOn η (Ico 0 T))
    (hDsub : D ⊆ Ico 0 T) (hD : Icc 0 T ⊆ closure D)
    (hhit : ∀ q ∈ D, IsFirstHitPoint γ b (L ∪ η '' Icc 0 q) (η q))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) :
    ∃ v ∈ Icc 0 b, γ v = η t ∧ ∀ w ∈ Icc 0 v, γ w ≠ η s := by
  obtain ⟨q, hqD, hsq, hqt⟩ := exists_mem_Ioo_of_subset_closure hD hs hst ht
  obtain ⟨uq, huq, hγuq, -, hbefq⟩ := hhit q hqD
  have hns : ∀ w ∈ Icc 0 uq, γ w ≠ η s := by
    rintro w ⟨hw0, hwle⟩ heq
    rcases hwle.lt_or_eq with hlt | rfl
    · exact hbefq w ⟨hw0, hlt⟩ (Or.inr ⟨s, ⟨hs, hsq.le⟩, heq.symm⟩)
    · exact (hsq.ne (hinj ⟨hs, hsq.trans (hDsub hqD).2⟩ (hDsub hqD) (heq.symm.trans hγuq))).elim
  obtain ⟨v, hv, hγv⟩ :=
    mem_image_Icc_of_visit hγ hη hDsub hD hhit (hDsub hqD).1 huq hγuq hqt ht
  exact ⟨v, ⟨hv.1, hv.2.trans huq.2⟩, hγv, fun w hw => hns w ⟨hw.1, hw.2.trans hv.2⟩⟩

/-- **First contact at the endpoint from a dense set of times** (Lemma 4.7 proof, p. 118, with
the stopping times of a countable dense set; "This proves the first-contact assertion also at the
endpoint"). Under the hypotheses of `mem_image_Icc_of_visit` with `0 < T`, the path `γ` first
hits `L ∪ η([0, T])` at `η(T)`. -/
theorem IsFirstHitPoint.of_dense [T2Space X] {γ η : ℝ → X} {b T : ℝ} {L : Set X} {D : Set ℝ}
    (hγ : ContinuousOn γ (Icc 0 b)) (hη : ContinuousOn η (Icc 0 T)) (hT : 0 < T)
    (hDsub : D ⊆ Ico 0 T) (hD : Icc 0 T ⊆ closure D)
    (hhit : ∀ q ∈ D, IsFirstHitPoint γ b (L ∪ η '' Icc 0 q) (η q)) :
    IsFirstHitPoint γ b (L ∪ η '' Icc 0 T) (η T) := by
  obtain ⟨q₀, hq₀D, -, -⟩ := exists_mem_Ioo_of_subset_closure hD le_rfl hT le_rfl
  -- `η T` is visited by every first-hit time of a point of `D`
  have hvis : ∀ q ∈ D, ∀ u ∈ Icc 0 b, γ u = η q → η T ∈ γ '' Icc 0 u := fun q hq u hu hγu =>
    mem_image_Icc_of_visit hγ hη hDsub hD hhit (hDsub hq).1 hu hγu (hDsub hq).2 le_rfl
  set S : Set ℝ := Icc 0 b ∩ γ ⁻¹' {η T} with hS
  have hSc : IsClosed S := hγ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  obtain ⟨u₀, hu₀, hγu₀, -, -⟩ := hhit q₀ hq₀D
  obtain ⟨v₁, hv₁, hγv₁⟩ := hvis q₀ hq₀D u₀ hu₀ hγu₀
  have hSne : S.Nonempty := ⟨v₁, ⟨hv₁.1, hv₁.2.trans hu₀.2⟩, hγv₁⟩
  have hSbdd : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
  have hmS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  refine ⟨sInf S, hmS.1, hmS.2, Or.inr ⟨T, ⟨hT.le, le_rfl⟩, rfl⟩, ?_⟩
  rintro w ⟨hw0, hwlt⟩ hwA
  -- `w` precedes every first-hit time of a point of `D`
  have hwq : ∀ q ∈ D, ∀ u ∈ Icc 0 b, γ u = η q → (∀ v ∈ Ico (0 : ℝ) u,
      γ v ∉ L ∪ η '' Icc 0 q) → γ w ∉ L ∪ η '' Icc 0 q := by
    intro q hq u hu hγu hbef
    obtain ⟨v, hv, hγv⟩ := hvis q hq u hu hγu
    have : sInf S ≤ v := csInf_le hSbdd ⟨⟨hv.1, hv.2.trans hu.2⟩, hγv⟩
    exact hbef w ⟨hw0, hwlt.trans_le (this.trans hv.2)⟩
  have hne : γ w ≠ η T := fun heq =>
    absurd (csInf_le hSbdd ⟨⟨hw0, hwlt.le.trans hmS.1.2⟩, heq⟩) (not_le.2 hwlt)
  rcases hwA with hL | ⟨s, hs, hsη⟩
  · obtain ⟨u, hu, hγu, -, hbef⟩ := hhit q₀ hq₀D
    exact hwq q₀ hq₀D u hu hγu hbef (Or.inl hL)
  · rcases hs.2.lt_or_eq with hsT | rfl
    · obtain ⟨q, hqD, hsq, -⟩ := exists_mem_Ioo_of_subset_closure hD hs.1 hsT le_rfl
      obtain ⟨u, hu, hγu, -, hbef⟩ := hhit q hqD
      exact hwq q hqD u hu hγu hbef (Or.inr ⟨s, ⟨hs.1, hsq.le⟩, hsη⟩)
    · exact hne hsη.symm

/-- **Lemma 4.7, pathwise conclusion** (pp. 118–119). Let the counterflow path `γ` be continuous
on `[0, b]` and the flow path `η` continuous on `[0, T]` (`0 < T`) and injective on `[0, T)`.
Suppose that, for every time `q` of a set `D ⊆ [0, T)` dense in `[0, T]` (e.g. the rational
times), `γ` first hits `L ∪ η([0, q])` at `η(q)` (the strict case `τ < T_top` of Lemma 4.7, a.s.
simultaneously for countably many stopping times). Then `γ` first hits `L ∪ η([0, T])` at
`η(T)`, the range of `γ` contains `η([0, T])`, and `γ` hits the points of `η` in reverse
chronological order: for `0 ≤ s < t ≤ T` it visits `η(t)` before its first visit to `η(s)`. -/
theorem isFirstHitPoint_and_image_subset_and_reverse [T2Space X] {γ η : ℝ → X} {b T : ℝ}
    {L : Set X} {D : Set ℝ} (hγ : ContinuousOn γ (Icc 0 b)) (hη : ContinuousOn η (Icc 0 T))
    (hT : 0 < T) (hinj : InjOn η (Ico 0 T)) (hDsub : D ⊆ Ico 0 T) (hD : Icc 0 T ⊆ closure D)
    (hhit : ∀ q ∈ D, IsFirstHitPoint γ b (L ∪ η '' Icc 0 q) (η q)) :
    IsFirstHitPoint γ b (L ∪ η '' Icc 0 T) (η T) ∧ η '' Icc 0 T ⊆ γ '' Icc 0 b ∧
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → ∃ v ∈ Icc 0 b, γ v = η t ∧ ∀ w ∈ Icc 0 v, γ w ≠ η s :=
  ⟨IsFirstHitPoint.of_dense hγ hη hT hDsub hD hhit,
    image_Icc_subset_of_dense hγ hη (hDsub.trans Ico_subset_Icc_self) hD fun q hq => by
      obtain ⟨u, hu, hγu, -, -⟩ := hhit q hq
      exact ⟨u, hu, hγu⟩,
    fun _ _ hs hst ht => exists_visit_before hγ hη hinj hDsub hD hhit hs hst ht⟩

/-- **No wrap-around** (Proposition 4.9 proof and Figure 4.7, p. 120). Under the reverse
chronological order of `exists_visit_before`, if `η(s)` has been absorbed by `γ([0, c])` and
`s < t ≤ T`, then `η(t)` has been absorbed by `γ([0, c])` as well. -/
theorem mem_image_Icc_of_lt {Y : Type*} {γ η : ℝ → Y} {b T c : ℝ}
    (hrev : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → ∃ v ∈ Icc 0 b, γ v = η t ∧ ∀ w ∈ Icc 0 v, γ w ≠ η s)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T) (hmem : η s ∈ γ '' Icc 0 c) :
    η t ∈ γ '' Icc 0 c := by
  obtain ⟨u, hu, hγu⟩ := hmem
  obtain ⟨v, hv, hγv, hne⟩ := hrev s t hs hst ht
  have hvu : v < u := lt_of_not_ge fun h => hne u ⟨hu.1, h⟩ hγu
  exact ⟨v, ⟨hv.1, hvu.le.trans hu.2⟩, hγv⟩

/-- **No wrap-around**, the source's form (Proposition 4.9 proof, p. 120): there are no times
`t₁ < t₂ < t₃ ≤ T` with `η(t₁), η(t₃) ∈ γ([0, c])` but `η(t₂) ∉ γ([0, c])`. -/
theorem not_exists_wrap {Y : Type*} {γ η : ℝ → Y} {b T c : ℝ}
    (hrev : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → ∃ v ∈ Icc 0 b, γ v = η t ∧ ∀ w ∈ Icc 0 v, γ w ≠ η s) :
    ¬ ∃ t₁ t₂ t₃ : ℝ, 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ ≤ T ∧ η t₁ ∈ γ '' Icc 0 c ∧
      η t₃ ∈ γ '' Icc 0 c ∧ η t₂ ∉ γ '' Icc 0 c := by
  rintro ⟨t₁, t₂, t₃, h0, h12, h23, h3, h1, -, h2⟩
  exact h2 (mem_image_Icc_of_lt hrev h0 h12 (h23.le.trans h3) h1)

/-- **Injectivity from no return** (Aux. lemma 25 proof, p. 127, last paragraph). If `Q` meets
every nondegenerate open subinterval of `[0, T]`, and for every `q ∈ Q` the path after `q` never
returns to its trace through `q` (`η((q, T]) ∩ η([0, q]) = ∅`), then `η` is injective on
`[0, T]`. -/
theorem injOn_of_disjoint_image {Y : Type*} {η : ℝ → Y} {T : ℝ} {Q : Set ℝ}
    (hQ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → ∃ q ∈ Q, s < q ∧ q < t)
    (hret : ∀ q ∈ Q, Disjoint (η '' Ioc q T) (η '' Icc 0 q)) : InjOn η (Icc 0 T) := by
  have key : ∀ s t : ℝ, s ∈ Icc 0 T → t ∈ Icc 0 T → s < t → η s ≠ η t := by
    intro s t hs ht hst heq
    obtain ⟨q, hqQ, hsq, hqt⟩ := hQ s t hs.1 hst ht.2
    exact disjoint_left.1 (hret q hqQ) ⟨t, ⟨hqt, ht.2⟩, rfl⟩ ⟨s, ⟨hs.1, hsq.le⟩, heq⟩
  intro s hs t ht heq
  rcases lt_trichotomy s t with hlt | heq' | hgt
  · exact (key s t hs ht hlt heq).elim
  · exact heq'
  · exact (key t s ht hs hgt heq.symm).elim

end Sec4

end InteractingSLE
