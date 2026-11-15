/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeData

/-!
# Chain data and bounded images of a node experiment

Packet PROVE-PROP59-NODETREE. The node experiment reads the node tree after the node prefix (PROVE-PROP59-NODES'
`subFam`). Its chain data use the joint chart of the whole tree (no Loewner shift, PROVE-PROP59-NODES §3.3): the
trace of a subtree candidate's whole path covers its node-relative capacities, inside the closure of the joint-chart
images of the node prefix points and of the descendant points of the node.

## Generic tree lemmas

* `TreeData.IsTree.alive_append`, `qLast_append_le`, `α_append`: along an extension of a list `pre`;
* `TreeData.exists_trace`: PROVE-PROP59-PIECES' trace of an alive candidate (pointwise form);
* **`TreeData.isChainAll_subFam`**: gap-free chain data of the subtree after `pre`, in the image set `imageG Z`, when
  the subtree's positions at positive rational times lie in `Z`.

## The node experiment

* `descPts`: the descendant points of the node `n` (chart `Q`); `nodeZ`: node prefix points (on the event that the
  node prefix is pre-contact) and descendant points;
* **`ae_qPathF_mem_descPts`**: the subtree paths at rational times after the node's terminal time are descendant
  points (PROVE-PROP513C's tree, `descendantAt_surjective`);
* **`isChainAll_subFam_nodeData`**, **`isBounded_nodeImage`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu WangWu.ImgWord LawUnique Prop59System Prop59Stage
open Prop59Pieces Prop59Nodes CrossRestart
open Sec7.StripWall (goodPathSet)
open Sec7.Lemma71C (capClock)

/-! ### Generic lemmas along an extension -/

section Generic

variable {Ω : Type*} {nL₀ nR₀ : ℕ} {D : TreeData Ω nL₀ nR₀}

theorem TreeData.IsTree.qLast_append_le (hT : D.IsTree) {m : ℕ} (pre : Fin m → ℝ≥0) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0), D.valid (m + j) (Fin.append pre t) →
      D.valid m pre ∧ qLast m pre ≤ qLast (m + j) (Fin.append pre t)
  | 0, t, hv => by
    have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    rw [append_elim0] at hv ⊢
    exact ⟨hv, le_rfl⟩
  | j + 1, t, hv => by
    obtain ⟨hv', hle, -⟩ := hT.init (m + j) (Fin.append pre t : Fin (m + (j + 1)) → ℝ≥0) hv
    rw [init_append] at hv' hle
    obtain ⟨h1, h2⟩ := TreeData.IsTree.qLast_append_le hT pre j (Fin.init t) hv'
    exact ⟨h1, h2.trans hle⟩

/-- Along an extension, the paths agree with the path of `pre` up to its last switch. -/
theorem TreeData.IsTree.α_append (hT : D.IsTree) {m : ℕ} (pre : Fin m → ℝ≥0) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0), D.valid (m + j) (Fin.append pre t) → ∀ (ω : Ω) (u : ℝ), 0 ≤ u →
      u ≤ qLast m pre → D.α (m + j) (Fin.append pre t) ω u = D.α m pre ω u
  | 0, t, _, ω, u, _, _ => by
    have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    rw [append_elim0]
    rfl
  | j + 1, t, hv, ω, u, hu0, hu => by
    have h := hT.pfx (m + j) (Fin.append pre t : Fin (m + (j + 1)) → ℝ≥0) hv ω u hu0
      (hu.trans (TreeData.IsTree.qLast_append_le hT pre (j + 1) t hv).2)
    refine h.trans ?_
    rw [init_append]
    have hv' := (hT.init (m + j) (Fin.append pre t : Fin (m + (j + 1)) → ℝ≥0) hv).1
    rw [init_append] at hv'
    exact TreeData.IsTree.α_append hT pre j (Fin.init t) hv' ω u hu0 hu

variable [MeasurableSpace Ω]

/-- An alive candidate of the subtree after `pre` has an alive root `pre`. -/
theorem TreeData.IsTree.alive_append (hD : D.IsReg) (hT : D.IsTree) {m : ℕ} (pre : Fin m → ℝ≥0) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0) {ω : Ω}, ω ∈ D.alive (m + j) (Fin.append pre t) → ω ∈ D.alive m pre
  | 0, t, ω, hω => by
    have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    rwa [append_elim0] at hω
  | j + 1, t, ω, hω => by
    have h1 := hT.alive_init hω
      ((hD.isKilledFamily (m + j) (Fin.init (Fin.append pre t : Fin (m + (j + 1)) → ℝ≥0))).arc ω)
    rw [init_append] at h1
    exact TreeData.IsTree.alive_append hD hT pre j (Fin.init t) h1

/-- **The trace of an alive candidate** (PROVE-PROP59-PIECES' chain argument at one sample): before the first new
contact, a Loewner trace from `0` covers the chart capacities `[0, start + s]` inside the closure of the images of
`Z`, provided the positions of the path at positive rational times lie in `Z`. -/
theorem TreeData.exists_trace (hD : D.IsReg) (hT : D.IsTree) {Z : Ω → Set ℂ} {j : ℕ} {t : Fin j → ℝ≥0} {ω : Ω}
    (hZ : ∀ q : ℚ, 0 < (q : ℝ) → D.α j t ω q ∈ Z ω) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < (D.cand j t).ζ ω) :
    ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
      recStart D.cand j t ω + s < T ∧ η '' Icc 0 (recStart D.cand j t ω + s) ⊆ closure (D.image Z ω) := by
  obtain ⟨hA, hlt⟩ := lt_arcζ_iff.1 hs
  have hγ := (hD.isKilledFamily j t).arc ω
  rw [D.recStart_eq hD hT j t ω hA]
  obtain ⟨S, hSP, hSlt⟩ := lt_kLife_iff.1 hlt
  rw [NNReal.coe_add] at hSlt
  have hS0 : 0 < S := by
    rcases (hγ.nonneg S hSP).eq_or_lt with h | h
    · rw [← h, hγ.capClock_zero] at hSlt
      exact absurd hSlt (not_lt.2 (add_nonneg (D.startCap j t ω).coe_nonneg s.coe_nonneg))
    · exact h
  obtain ⟨w, hw, hw0, -, η, hηL, -, hηγ⟩ := hγ.exists_traceDriver hSP hS0
  refine ⟨w, η, (D.startCap j t ω : ℝ) + s + 1, hw, hw0,
    ⟨hηL.1, hηL.2.1.mono Ico_subset_Ici_self, fun t' ht' _ => hηL.2.2 t' ht'⟩, by linarith, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hτle : x.toNNReal ≤ D.startCap j t ω + s := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_add]; exact hx.2
  have hτ : ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img j t ω) (D.pre j t ω) :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 hτle) hlt
  obtain ⟨hm, he⟩ := hγ.kInv_spec hτ
  have hle : kInv (D.img j t ω) (D.pre j t ω) x.toNNReal ≤ S :=
    hγ.kInv_le hSP hτ (by rw [Real.coe_toNNReal _ hx.1]; linarith [hx.2])
  have hxe : x = capClock (D.img j t ω) (kInv (D.img j t ω) (D.pre j t ω) x.toNNReal) := by
    rw [he, Real.coe_toNNReal _ hx.1]
  rw [hxe, hηγ _ ⟨hγ.nonneg _ hm, hle⟩]
  exact D.mem_closure_image hD hA.1 hZ hm

/-- **Gap-free chain data of the subtree after `pre`** in the image set `imageG Z`, with the node-relative start,
when the subtree's positions at positive rational times lie in `Z` (for alive candidates). -/
theorem TreeData.isChainAll_subFam (hD : D.IsReg) (hT : D.IsTree) {P : Measure Ω} {Z : Ω → Set ℂ} {m : ℕ}
    (pre : Fin m → ℝ≥0)
    (hnode : ∀ᵐ ω ∂P, ∀ j t, ω ∈ D.alive (m + j) (Fin.append pre t) → ∀ q : ℚ, 0 < (q : ℝ) →
      D.α (m + j) (Fin.append pre t) ω q ∈ Z ω) :
    IsChainAll P (subFam D.cand m pre) (D.imageG Z)
      (fun j t ω => recStart D.cand (m + j) (Fin.append pre t) ω - recStart D.cand m pre ω) where
  start_zero := ae_of_all _ fun ω => by
    show recStart D.cand (m + 0) (Fin.append pre Fin.elim0) ω - recStart D.cand m pre ω = 0
    rw [append_elim0]
    simp
  step j t q := ae_of_all _ fun ω s hs hsζ => by
    show recStart D.cand (m + (j + 1)) (Fin.append pre (Fin.snoc t q)) ω - recStart D.cand m pre ω =
      recStart D.cand (m + j) (Fin.append pre t) ω - recStart D.cand m pre ω + s
    rw [Fin.append_snoc]
    have e : recStart D.cand (m + (j + 1)) (Fin.snoc (α := fun _ => ℝ≥0) (Fin.append pre t) q) ω =
        recStart D.cand (m + j) (Fin.append pre t) ω + s :=
      recStart_step (fun j t ω => strictMono_arcClk (hD.isKilledFamily j t).arc ω) (m + j) (Fin.append pre t) q ω
        s hs
    rw [e]
    ring
  trace j t := by
    filter_upwards [hnode] with ω hZ s hs
    have hs' : (s : ℝ≥0∞) < (D.cand (m + j) (Fin.append pre t)).ζ ω := hs
    obtain ⟨hA, -⟩ := lt_arcζ_iff.1 hs'
    obtain ⟨W', η, T, hc, hW0, hη, hT', himg⟩ :=
      TreeData.exists_trace hD hT (hZ j t hA) hs'
    have h0 : 0 ≤ recStart D.cand m pre ω := recStart_nonneg D.cand m pre ω
    have hG : ω ∈ D.G := hA.1.2
    have hIG : D.imageG Z ω = D.image Z ω := by
      classical
      simp only [TreeData.imageG, hG, ↓reduceIte]
    refine ⟨W', η, T, hc, hW0, hη, by linarith, ?_⟩
    rw [hIG]
    exact (image_mono (Icc_subset_Icc_right (by linarith))).trans himg

end Generic

/-! ### The node points -/

section Node

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{u}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {E : Schedule → ℕ → Ω → Driver}

/-- **The descendant points of the node `n`** in the chart `Q`: the post-terminal portions of its descendants. -/
def descPts (E : Schedule → ℕ → Ω → Driver) (n : ℕ) (ω : Ω) : Set ℂ :=
  ⋃ m, driverTree E (descendantIndex n m) ω '' Ioc (treeTime n) (treeTime (descendantIndex n m))

/-- **The node points**: the node prefix points at positive rational times up to the last switch (on the event that
the node prefix is pre-contact) and the descendant points. -/
def nodeZ {nL₀ nR₀ : ℕ} (D : TreeData Ω nL₀ nR₀) {m : ℕ} (pre : Fin m → ℝ≥0) (Zd : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  (open scoped Classical in
    if ω ∈ D.alive m pre then {z | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ qLast m pre ∧ z = D.α m pre ω q} else ∅) ∪
    Zd ω

theorem treeTime_eq (s : ℕ) : (treeTime s : ℝ) = terminalRat (scheduleAt s) := by
  rw [treeTime, terminal, Real.coe_toNNReal _ (by exact_mod_cast (terminalRat_pos _).le)]

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P]

/-- **The subtree paths at rational times after the node's terminal time are descendant points.** -/
theorem ae_qPathF_mem_descPts
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : Fin j → ℝ≥0),
      IsValid (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) → ∀ q : ℚ,
        (terminalRat (scheduleAt n) : ℝ) < q →
        qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag (scheduleAt n))
          (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t) ω q ∈ descPts E n ω := by
  set s := scheduleAt n with hsdef
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSchedF (nodeFlag s) j t)
  filter_upwards [hg, ae_prefixDriver_eq_joined h44 hκ hκ4 hb hG hE hR] with ω hgω hpω
  intro j
  induction j with
  | zero =>
    intro t hv q hq
    have hlt : lastO (nodeLen s + 0) (Fin.append (nodePre s) t) < q := by
      have ht : t = Fin.elim0 := funext fun i => i.elim0
      subst ht
      rw [append_elim0]
      show lastO (nodeLen s) (nodePre s) < q
      rw [lastO_nodePre]
      exact_mod_cast hq
    exact mem_descPts_of_lt hgω hpω hv hlt hq
  | succ j ih =>
    intro t hv q hq
    by_cases hql : lastO (nodeLen s + (j + 1)) (Fin.append (nodePre s) t) < q
    · exact mem_descPts_of_lt hgω hpω hv hql hq
    · have hle : (q : ℝ) ≤ qLast (nodeLen s + (j + 1)) (Fin.append (nodePre s) t) := by
        rw [← lastO_eq hv]; exact_mod_cast not_lt.1 hql
      have e : qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) (nodeLen s + (j + 1))
          (Fin.append (nodePre s) t) ω q = qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h)
          (nodeFlag s) (nodeLen s + j) (Fin.init (Fin.append (nodePre s) t : Fin (nodeLen s + (j + 1)) → ℝ≥0)) ω q :=
        qPathF_pfx h44 hκ hκ4 _ _ (j := nodeLen s + j) hv ω hle
      rw [e, init_append]
      have hv' := hv.init
      rw [init_append] at hv'
      exact ih (Fin.init t) hv' q hq
where
  /-- The case of a rational time after the last switch: the endpoint of a truncated extension. -/
  mem_descPts_of_lt {n : ℕ} {ω : Ω}
      (hgω : ∀ j t, IsValid j t → ∀ k < (scheduleList (candSchedF (nodeFlag (scheduleAt n)) j t)).length,
        codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h)
          (candSchedF (nodeFlag (scheduleAt n)) j t) k ω ∈ goodPathSet)
      (hpω : ∀ s : Schedule, ∀ r : ℝ≥0, (r : ℝ≥0∞) < terminal s →
        prefixDriver E s ω r = joinedDriver (codeFam h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) s)
          0 0 (scheduleList s) ω r)
      {k : ℕ} {t : Fin k → ℝ≥0} (hv : IsValid (nodeLen (scheduleAt n) + k) (Fin.append (nodePre (scheduleAt n)) t))
      {q : ℚ} (hlt : lastO (nodeLen (scheduleAt n) + k) (Fin.append (nodePre (scheduleAt n)) t) < q)
      (hq : (terminalRat (scheduleAt n) : ℝ) < q) :
      qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + k) (Fin.append (nodePre (scheduleAt n)) t) ω q ∈ descPts E n ω := by
    have hnv := nodeValid_append hv
    set d := descOf hnv (Nat.le_add_right _ _) hlt with hd
    obtain ⟨m', hm'⟩ := descendantAt_surjective (scheduleAt n) d
    have hidx : descendantIndex n m' = scheduleIndex (mkSchedF (nodeFlag (scheduleAt n))
        (nodeLen (scheduleAt n) + k) (Fin.append (nodePre (scheduleAt n)) t) q) := by
      rw [descendantIndex, hm', hd]
      rfl
    have hpt := driverTree_mkSchedF_eq_qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) hv hlt
      (hgω _ _ hv) (hpω _)
    rw [← hidx] at hpt
    have hq0 : (0 : ℝ) < q := (by exact_mod_cast terminalRat_pos (scheduleAt n) : (0 : ℝ) < _).trans hq
    have htd : (treeTime (descendantIndex n m') : ℝ) = q := by
      rw [hidx, treeTime, scheduleAt_index, terminal_mkSchedF hv hlt, Real.coe_toNNReal _ hq0.le]
    refine mem_iUnion.2 ⟨m', _, ⟨?_, ?_⟩, hpt⟩
    · rw [htd, treeTime_eq]; exact hq
    · rw [htd]

end Node

end InteractingSLE.Sec5.Prop59NodeTree
