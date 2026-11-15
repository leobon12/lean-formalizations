/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2InteriorQ
import InteractingSLE.Spec.Supplement.GW2ScheduleR51Ident
import InteractingSLE.Spec.Exist.StagedLaw3Main

/-!
# Interior switching tips for launched stages of a GW2 schedule

Packet PROVE-T14-GW2Q2. The schedule condition is restricted to `k < l.length`:
unused drivers after the program ends have no pathwise constraints. The canonical
construction and Lemma 2.5 provide one deterministic dense set of good times.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Tip

open GW2Cone GW2Schedule GW2Later GW2Sched GW2aMulti Exist Staged StagedLaw Restart LQGMetric
open Exist.Staged Sec2.Assembly

/-- GB9a's schedule condition, applied only before a launched instruction. -/
def GW2InteriorScheduleQStatement' : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) →
        ∀ l : List (ℝ × ℝ≥0), IsSchedule Θ Q l →
        ∀ k : ℕ, k < l.length → ∀ᵐ ω ∂P,
          AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
          SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩
            (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k

/-- The coordinate indices of a finite vector, as a finite subset of the selector indices. -/
def vectorIndexSet {n : ℕ} (r : Fin n ↪ ℕ) : Finset ℕ := Finset.univ.image r

/-- Enumeration of the selected index set in the order of the given vector. -/
def vectorIndexEquiv {n : ℕ} (r : Fin n ↪ ℕ) : Fin n ≃ vectorIndexSet r :=
  Equiv.ofBijective (fun i => ⟨r i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j hij => r.injective (congrArg Subtype.val hij), fun j => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp j.2
      exact ⟨i, Subtype.ext hi⟩⟩

/-- GB9a simultaneously selects good vectors for all finite injective lists of indices.
The existing finite-set selector handles their coordinate order through `vectorIndexEquiv`. -/
theorem exists_dense_good_vectors {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [SFinite P] {ι : Type*} [Countable ι]
    (Bad : ι → (n : ℕ) → Fin n → Set (Ω × (Fin n → ℝ)))
    (hm : ∀ a n i, MeasurableSet (Bad a n i))
    (hsec : ∀ a n i ω v,
      volume {x : ℝ | (ω, Function.update v i x) ∈ Bad a n i} = 0) :
    ∃ q : ℕ → ℝ, (∀ m, 0 < q m) ∧ Ioi 0 ⊆ closure (range q) ∧
      ∀ a n (r : Fin n ↪ ℕ) i, P {ω | (ω, fun j => q (r j)) ∈ Bad a n i} = 0 := by
  classical
  have (n : ℕ) : Countable (Fin n ↪ ℕ) :=
    Function.Injective.countable (f := fun r : Fin n ↪ ℕ => (r : Fin n → ℕ))
      (fun r s hrs => Function.Embedding.ext (fun i => congrFun hrs i))
  let J := ι × (Σ n : ℕ, Fin n ↪ ℕ)
  let S : J → Finset ℕ := fun a => vectorIndexSet a.2.2
  let B : (a : J) → Set (Ω × (S a → ℝ)) := fun a =>
    ⋃ i : Fin a.2.1, {p | (p.1, fun j => p.2 (vectorIndexEquiv a.2.2 j)) ∈
      Bad a.1 a.2.1 i}
  have hnull : ∀ a, ∀ᵐ v ∂(Measure.pi fun _ : S a => (volume : Measure ℝ)),
      P {ω | (ω, v) ∈ B a} = 0 := by
    intro a
    have hBm : MeasurableSet (B a) := MeasurableSet.iUnion fun i =>
      (measurable_fst.prodMk (measurable_pi_iff.mpr fun j =>
        (measurable_pi_apply (vectorIndexEquiv a.2.2 j)).comp measurable_snd)) (hm _ _ i)
    apply ae_measure_section_eq_zero_of_ae P _ hBm
    refine Eventually.of_forall fun ω => ?_
    have hset : {v | (ω, v) ∈ B a} = ⋃ i : Fin a.2.1,
        {v | (ω, fun j => v (vectorIndexEquiv a.2.2 j)) ∈ Bad a.1 a.2.1 i} := by
      ext v
      simp only [B, mem_iUnion, mem_ofPred_eq]
    rw [hset]
    apply measure_iUnion_null
    intro i
    calc
      _ = volume {v : Fin a.2.1 → ℝ | (ω, v) ∈ Bad a.1 a.2.1 i} :=
        volume_comp_equiv (vectorIndexEquiv a.2.2)
          (show MeasurableSet {v | (ω, v) ∈ Bad a.1 a.2.1 i} from
            measurable_prodMk_left (hm _ _ i))
      _ = 0 := volume_eq_zero_of_update (measurable_prodMk_left (hm _ _ i)) i
        (hsec _ _ i ω)
  obtain ⟨q, hq0, hqd, hq⟩ := Supp8.gb9a_exists_dense P S B hnull
  refine ⟨q, hq0, hqd, fun a n r i => ?_⟩
  apply measure_mono_null
    (t := {ω | (ω, fun j : S (a, ⟨n, r⟩) => q (j : ℕ)) ∈ B (a, ⟨n, r⟩)}) _
    (hq (a, ⟨n, r⟩))
  intro ω hω
  exact mem_iUnion.mpr ⟨i, hω⟩

/-- A positive real selector dense on `(0,∞)` gives a dense selector of nonnegative times. -/
theorem dense_range_toNNReal {q : ℕ → ℝ} (hqd : Ioi 0 ⊆ closure (range q)) :
    Dense (range fun n => (q n).toNNReal) := by
  have hpos : Ioi (0 : ℝ≥0) ⊆ closure (range fun n => (q n).toNNReal) := by
    intro t ht
    have ht' : (t : ℝ) ∈ closure (range q) := hqd ht
    have hc := image_closure_subset_closure_image continuous_real_toNNReal
      (mem_image_of_mem Real.toNNReal ht')
    simpa only [Real.toNNReal_coe, ← range_comp'] using hc
  intro t
  have ht : t ∈ closure (Ioi (0 : ℝ≥0)) := by
    rw [closure_Ioi]
    exact show 0 ≤ t from bot_le
  exact (closure_minimal hpos isClosed_closure) ht

/-- The ordered absolute time vector of a schedule. -/
def scheduleVec (l : List (ℝ × ℝ≥0)) (i : Fin l.length) : ℝ := (l.get i).2

/-- A schedule's angles, retaining their membership in the prescribed countable set. -/
def scheduleAngles {Θ : Set ℝ} (l : List (ℝ × ℝ≥0)) (hl : ∀ p ∈ l, p.1 ∈ Θ) :
    List {a : ℝ // a ∈ Θ} :=
  l.attach.map fun p => ⟨p.1.1, hl p.1 p.2⟩

theorem map_fst_getD (l : List (ℝ × ℝ≥0)) (j : ℕ) :
    (l.map Prod.fst).getD j 0 = (l.getD j (0, 0)).1 := by
  induction l generalizing j with
  | nil => rfl
  | cons p l ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

theorem anglesOfList_scheduleAngles {Θ : Set ℝ} (l : List (ℝ × ℝ≥0))
    (hl : ∀ p ∈ l, p.1 ∈ Θ) :
    anglesOfList Θ (scheduleAngles l hl) = schedAngle l := by
  have hm : (scheduleAngles l hl).map Subtype.val = l.map Prod.fst := by
    simp only [scheduleAngles, List.map_map, Function.comp_def, List.attach_map_val]
  funext j
  unfold anglesOfList schedAngle
  rw [hm]
  exact map_fst_getD l j

theorem vecPrevTime_scheduleVec (l : List (ℝ × ℝ≥0)) (i : Fin l.length) :
    (vecPrevTime (scheduleVec l) i).toNNReal = schedTime 0 l i.val := by
  rcases i with ⟨j, hj⟩
  cases j with
  | zero => simp only [vecPrevTime, dite_true, Real.toNNReal_zero, schedTime]
  | succ j =>
    simp only [vecPrevTime, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel,
      scheduleVec, Real.toNNReal_coe, schedTime]
    rw [← List.getElem_eq_getD (h := by omega) (0, 0)]
    rfl

theorem vecOwnTimes_scheduleVec (l : List (ℝ × ℝ≥0)) :
    vecOwnTimes (scheduleVec l) = schedDelta 0 l := by
  funext j
  by_cases hj : j < l.length
  · simp only [vecOwnTimes, hj, dite_true, vecOwnTime, scheduleVec,
      Real.toNNReal_coe, vecPrevTime_scheduleVec, schedDelta]
    rw [← List.getElem_eq_getD (h := hj) (0, 0)]
    rfl
  · simp only [vecOwnTimes, hj, dite_false, schedDelta, List.getD,
      List.getElem?_eq_none (Nat.le_of_not_gt hj), Option.getD_none, zero_tsub,
      ENNReal.coe_zero]

theorem scheduleVec_pos {Θ : Set ℝ} {Q : Set ℝ≥0} {l : List (ℝ × ℝ≥0)}
    (hl : IsSchedule Θ Q l) (hQ : ∀ t ∈ Q, 0 < t) (i : Fin l.length) :
    0 < scheduleVec l i := by
  exact_mod_cast hQ _ (hl.1 _ (List.get_mem l i)).2

theorem vecPrevTime_lt_scheduleVec {Θ : Set ℝ} {Q : Set ℝ≥0}
    {l : List (ℝ × ℝ≥0)} (hl : IsSchedule Θ Q l) (hQ : ∀ t ∈ Q, 0 < t)
    (i : Fin l.length) : vecPrevTime (scheduleVec l) i < scheduleVec l i := by
  by_cases hi : i.val = 0
  · simpa only [vecPrevTime, hi, dite_true] using scheduleVec_pos hl hQ i
  · simp only [vecPrevTime, hi, dite_false]
    exact_mod_cast hl.2.rel_get_of_lt (a := ⟨i.val - 1, by omega⟩) (b := i)
      (show (⟨i.val - 1, by omega⟩ : Fin l.length) < i from by
        exact Fin.mk_lt_mk.mpr (by omega))

/-- GB9a's corrected schedule statement, from parametric field determination and trace existence.
The selector is chosen before the staged family; R51 identifies each successful launched prefix
with the jointly measurable canonical construction. -/
theorem gw2InteriorScheduleQStatement'_of_param (h13 : Theorem13Statement.{u})
    (h12p : Theorem12ParamStatement.{u}) : GW2InteriorScheduleQStatement'.{u} := by
  classical
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh Θ _hΘ hΘc
  obtain ⟨βA, hβA⟩ := stopLawStatement κ hκ hκ4
  obtain ⟨c₀, hc₀J, hc₀⟩ := BoundaryWord.exists_fn_eq hb
  let Roots := {x : ℝ // x = 0 ∨ x ∈ lowerArcRoots κ b jumps}
  have hroots : {x : ℝ | x = 0 ∨ x ∈ lowerArcRoots κ b jumps}.Countable :=
    (countable_singleton 0).union (countable_lowerArcRoots κ b jumps)
  have : Countable Roots := hroots.to_subtype
  have : Countable {a : ℝ // a ∈ Θ} := hΘc.to_subtype
  let A := Roots × List {a : ℝ // a ∈ Θ}
  let Bad : A → (n : ℕ) → Fin n → Set (Ω × (Fin n → ℝ)) := fun a n i =>
    vecInteriorBadSet h12p hκ Θ βA c₀ a.1.1 a.2 (n := n) (h := h) i
  obtain ⟨q, hq0, hqd, hq⟩ := exists_dense_good_vectors P Bad
    (fun a n i => measurableSet_vecInteriorBadSet h12p hκ Θ βA c₀ a.1.1
      hβA.1 hh.1 a.2 i)
    (fun a n i ω v => volume_section_vecInteriorBadSet hκ Θ βA c₀ a.1.1 a.2 i ω v)
  let Q : Set ℝ≥0 := range fun m => (q m).toNNReal
  have hQpos : ∀ t ∈ Q, 0 < t := by
    rintro t ⟨m, rfl⟩
    exact Real.toNNReal_pos.mpr (hq0 m)
  refine ⟨Q, countable_range _, dense_range_toNNReal hqd, hQpos, ?_⟩
  intro E hE hR x hx l hl k hk
  let angles := scheduleAngles l (fun p hp => (hl.1 p hp).1)
  let v := scheduleVec l
  let θ := anglesOfList Θ angles
  let Δ := vecOwnTimes v
  have hθ : θ = schedAngle l := anglesOfList_scheduleAngles l _
  have hΔ : Δ = schedDelta 0 l := vecOwnTimes_scheduleVec l
  have hprog : IsFlowProg (scheduleProgram 0 l) θ Δ := by
    rw [hθ, hΔ]
    exact isFlowProg_scheduleProgram 0 l
  have hΔtop : ∀ j, Δ j ≠ ⊤ := by
    rw [hΔ]
    exact schedDelta_ne_top 0 l
  have hchoose : ∀ i : Fin l.length, ∃ m : ℕ, q m = v i := by
    intro i
    obtain ⟨m, hm⟩ := (hl.1 _ (List.get_mem l i)).2
    refine ⟨m, ?_⟩
    have he := congrArg (fun t : ℝ≥0 => (t : ℝ)) hm
    rw [Real.coe_toNNReal _ (hq0 m).le] at he
    exact he
  choose r hr using hchoose
  have hvstrict : StrictMono v := by
    intro i j hij
    exact_mod_cast hl.2.rel_get_of_lt hij
  let R : Fin l.length ↪ ℕ := ⟨r, fun i j hij => hvstrict.injective (by
    rw [← hr i, ← hr j, hij])⟩
  have hvec : (fun i => q (R i)) = v := funext hr
  have hgood : ∀ᵐ ω ∂P, ∀ i : Fin l.length,
      (ω, v) ∉ vecInteriorBadSet h12p hκ Θ βA c₀ x angles (h := h) i := by
    apply ae_all_iff.mpr
    intro i
    have hnull := hq (⟨x, hx⟩, angles) l.length R i
    rw [hvec] at hnull
    rw [ae_iff]
    simpa only [Bad, mem_ofPred_eq, not_not] using hnull
  let spec : ExplSpec := ⟨x, true, scheduleProgram 0 l⟩
  let C := canonFam hκ h12p βA c₀ θ Δ x h
  have hBC := isBoundaryContinuedProgram_scheduleProgram (mem_Icc_of_isSchedule _hΘ hl) 0
  have hident := ae_identify_canon_R51 hκ h12p θ Δ βA c₀ h13 hβA hb hc₀J hc₀ hh
    (spec := spec) rfl hprog hΔtop (hE spec hBC) (hR spec hBC)
  filter_upwards [hgood, hident] with ω hgoodω hidentω hs
  have hklen : k ≤ spec.2.2.length := by
    change k ≤ (scheduleProgram 0 l).length
    rw [length_scheduleProgram]
    exact hk.le
  have hsE : AllSucc Δ (fun j => E spec j ω) k := by rwa [hΔ]
  have hsC : AllSucc Δ (fun j => C j ω) k := (hidentω.1 k hklen).1.mp hsE
  intro j hj
  have hjl : j < l.length := lt_trans hj hk
  let i : Fin l.length := ⟨j, hjl⟩
  let z := vecCanonCode h12p hκ Θ βA c₀ x angles v (h ω) j
  have hcode : C j ω = drvOf z :=
    vecCanonDrive_eq_drvOf_vecCanonCode h12p hκ Θ βA c₀ x angles v (h ω) j
  have htime : (vecOwnTime v i : ℝ≥0∞) < (drvOf z).2 := by
    have ht : Δ j < (C j ω).2 := hsC j hj
    rw [hcode] at ht
    simpa only [Δ, vecOwnTimes, hjl, dite_true, i] using ht
  have hz : z ∈ DSet := by
    by_contra hz
    have hzero : (drvOf z).2 = 0 := by simp [drvOf, hz]
    rw [hzero] at htime
    exact (not_lt_of_ge bot_le) htime
  have htimez : (vecOwnTime v i : ℝ≥0∞) < z.1 := by
    simpa only [drvOf_of_mem hz] using htime
  have heval : vecCanonEval h12p hκ Θ βA c₀ x angles (h := h) i (ω, v) ∈ H := by
    by_contra he
    apply hgoodω i
    refine ⟨scheduleVec_pos hl hQpos i, vecPrevTime_lt_scheduleVec hl hQpos i, ?_, he⟩
    intro a ha
    have hac : a < k := lt_of_lt_of_le ha (by change j + 1 ≤ k; omega)
    have ht := hsC a hac
    have hca := vecCanonDrive_eq_drvOf_vecCanonCode h12p hκ Θ βA c₀ x angles v (h ω) a
    change C a ω = _ at hca
    change Δ a < (C a ω).2 at ht
    rw [hca] at ht
    exact ht
  have hintC : IsInteriorStop (C j ω).1 (Δ j) := by
    rw [hcode]
    have hown : Δ j = (vecOwnTime v i : ℝ≥0∞) := by
      simp only [Δ, vecOwnTimes, hjl, dite_true, i]
    rw [hown]
    exact interiorStop_of_driverCode_eval hz htimez heval
  have hjprog : j < spec.2.2.length := lt_of_lt_of_le hj hklen
  have hsame := (hidentω.2 j hjprog (hsE.mono hj.le)).2
  change canonDrv (Δ j) (E spec j ω) = canonDrv (Δ j) (C j ω) at hsame
  have hCtime : Δ j < (C j ω).2 := hsC j hj
  have hEtime : Δ j < (E spec j ω).2 := hsE j hj
  have hstop : (fun r : ℝ≥0 => (E spec j ω).1 (min (r : ℝ≥0∞) (Δ j)).toNNReal) =
      (fun r : ℝ≥0 => (C j ω).1 (min (r : ℝ≥0∞) (Δ j)).toNNReal) := by
    have hf := congrArg Prod.fst hsame
    simpa only [canonDrv, min_eq_left hEtime.le, min_eq_left hCtime.le] using hf
  change IsInteriorStop (E spec j ω).1 (pieceStop spec (fun a => E spec a ω) j)
  have hinstr : instrTime spec j = Δ j := instrTime_eq_of_isFlowProg hprog hjprog
  rw [pieceStop, hinstr, min_eq_left hEtime.le]
  unfold IsInteriorStop at hintC ⊢
  rw [hstop]
  exact hintC

end InteractingSLE.Theorem14.GW2Tip
