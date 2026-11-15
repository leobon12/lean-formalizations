/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WmMap
import InteractingSLE.Spec.Supplement.GW2SkRec
import InteractingSLE.Spec.Supplement.GW2RootH29Read
import InteractingSLE.Spec.Supplement.GW2RootJ31Joined
import InteractingSLE.Spec.Supplement.GW2ScheduleCanon
import InteractingSLE.Spec.Supplement.GW2RdStgChain

/-!
# GW2's stage word map, part 3: the decoder of the augmented stage record

Packet PROVE-GW2-GEOM2 (round 7). The instance reads its word from the AUGMENTED stage record
`z = pairEnc (stageEnc N (cfRec, piece records), stgPreRec … T R)` (RELDET's `GW2Rd.stgRec`). The flowed word needs the
root (counterflow) record and the RELATIVE stage records `recOf (b_{j+1} − b_j) (stgDrv R b_j)` of the earlier pieces,
where `b_j` is the relative time at which piece `j` ends. The record carries `R` up to the stage start
(`augPre`, `augA`), and the physical piece records; the intermediate relative stage boundaries are read by ROOT2's
capacity reader at the physical stage times `T_j = schedTime 0 L j` of the program `L`:

* `decHist n z`: the decoded stage-start history; `stageBd x s L z j`: `0` at `j = 0`, the clipped reading
  `min (RootH29.forwardCapacity x s T_j (cf, joined physical record)) (augA z)` for `0 < j < |L|`, and `augA z` from
  `|L|` on; `pastOf cf R b n`: the root record followed by the `n` relative stage records of `R` between the
  boundaries `b`; **`stageDec x s L z = pastOf (decHist |L| z).1 (augPre z) (stageBd x s L z) |L|`**;
* `measurable_stageBd`, `measurable_pastOf`, **`measurable_stageDec`**;
* **`schedWordMap κ c′ x s L θa`** `= wordMap κ c′ x (progAngle L) |L| θa (stageDec x s L)` and
  **`schedWordMap_targets`** (the three `Good` targets);
* `pastRoot_pastOf`, `pastRoot_stageDec`: the decoded root record is the counterflow record;
* **`stageDec_augRec`**: on the instance's record `augRec x (stgPreRec … T R)` with `x ω = stageEnc |L| (cf, P)`, the
  decoder returns `pastOf cf R b |L|` with the instance's OWN relative driver `R` and boundaries
  `b j = min (reading_j) (stgStart T)` (`0 < j < |L|`), `b 0 = 0`, `b j = stgStart T` (`j ≥ |L|`);
  **`baseWord_augRec`**: the instance's base word is the root word flowed through the instance's own relative stage
  records.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Wm

open Restart Exist.Staged Exist.StagedLaw GW2TipSystem

/-! ### Records of a driver between boundaries -/

/-- **The root record followed by the relative stage records** of the driver `R` between the boundaries `b`. -/
def pastOf (cf : RecData) (R : ℝ≥0 → ℝ) (b : ℕ → ℝ≥0) : (n : ℕ) → GW2JDetR5.Past RecData n
  | 0 => cf
  | n + 1 => (pastOf cf R b n, recOf ((b (n + 1) - b n : ℝ≥0) : ℝ≥0∞) (fun u => GW2Rd.stgDrv R (b n) u, ⊤))

theorem pastRoot_pastOf (cf : RecData) (R : ℝ≥0 → ℝ) (b : ℕ → ℝ≥0) :
    ∀ n, pastRoot n (pastOf cf R b n) = cf
  | 0 => rfl
  | n + 1 => pastRoot_pastOf cf R b n

/-- A record of a driver run for a finite time reads the driver only up to that time. -/
theorem recOf_congr_top {f g : ℝ≥0 → ℝ} {t : ℝ≥0} (hfg : ∀ u ≤ t, f u = g u) :
    recOf (t : ℝ≥0∞) (f, ⊤) = recOf (t : ℝ≥0∞) (g, ⊤) := by
  unfold recOf retOf readRec
  refine Prod.ext (funext fun q => hfg _ ?_) rfl
  rw [min_eq_left (le_top : (t : ℝ≥0∞) ≤ ⊤)]
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_right _ _)).trans_eq (ENNReal.toNNReal_coe t)

/-- **Two drivers agreeing up to a bound of all boundaries give the same records.** -/
theorem pastOf_congr (cf : RecData) {R R' : ℝ≥0 → ℝ} {b : ℕ → ℝ≥0} {B : ℝ≥0} (h : ∀ u ≤ B, R u = R' u) :
    ∀ n, (∀ j ≤ n, b j ≤ B) → pastOf cf R b n = pastOf cf R' b n
  | 0, _ => rfl
  | n + 1, hb => by
    change (pastOf cf R b n, _) = (pastOf cf R' b n, _)
    rw [pastOf_congr cf h n fun j hj => hb j (hj.trans (Nat.le_succ n))]
    congr 1
    refine recOf_congr_top fun u hu => ?_
    unfold GW2Rd.stgDrv
    have h1 : b n + u ≤ B := by
      have h2 := (add_le_add_iff_left (b n)).2 hu
      rw [add_tsub_eq_max] at h2
      exact h2.trans (max_le (hb n (Nat.le_succ n)) (hb (n + 1) le_rfl))
    rw [h _ h1, h _ ((le_self_add).trans h1)]

/-! ### The decoder -/

/-- **The decoded stage-start history** (counterflow record and the `n` physical piece records). -/
def decHist (n : ℕ) (z : RecData) : RecData × (Fin n → RecData) :=
  (GW2Rd.stageEnc n).symm (GW2Rd.pairEnc.symm z).1

theorem measurable_decHist (n : ℕ) : Measurable (decHist n) :=
  (GW2Rd.stageEnc n).symm.measurable.comp (measurable_fst.comp GW2Rd.pairEnc.symm.measurable)

/-- The reading of the relative clock at the `j`-th physical stage time of the program `L` (`|L| = N`). -/
def stageRead (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData) (j : ℕ) : ℝ :=
  RootH29.forwardCapacity x s (GW2Schedule.schedTime 0 L j)
    ((decHist N z).1, RootJ31.joinedRecord L fun i => (decHist N z).2 (Fin.cast hN i))

/-- **The relative stage boundaries**: `0`, then the clipped readings, then the stage start. -/
def stageBd (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData) (j : ℕ) : ℝ≥0 :=
  if j = 0 then 0 else if j < N then min (stageRead x s L N hN z j).toNNReal (GW2Rd.augA z) else GW2Rd.augA z

/-- **The stage decoder**: the decoded root record and the relative stage records of the decoded prefix. -/
def stageDec (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData) :
    GW2JDetR5.Past RecData N :=
  pastOf (decHist N z).1 (GW2Rd.augPre z) (stageBd x s L N hN z) N

/-- The angles of a program. -/
def progAngle (L : List (ℝ × ℝ≥0)) (j : ℕ) : ℝ := (L.getD j (0, 0)).1

theorem pastRoot_stageDec (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData) :
    pastRoot N (stageDec x s L N hN z) = (decHist N z).1 :=
  pastRoot_pastOf _ _ _ _

theorem stageBd_le_augA (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (z : RecData)
    (j : ℕ) : stageBd x s L N hN z j ≤ GW2Rd.augA z := by
  unfold stageBd
  split_ifs
  · exact bot_le
  · exact min_le_right _ _
  · exact le_rfl

/-! ### Measurability -/

/-- **The records of a measurable family of continuous drivers between measurable boundaries are measurable.** -/
theorem measurable_pastOf {α : Type*} [MeasurableSpace α] {cf : α → RecData} {R : α → ℝ≥0 → ℝ}
    {b : α → ℕ → ℝ≥0} (hcf : Measurable cf) (hRm : ∀ u, Measurable fun a => R a u) (hRc : ∀ a, Continuous (R a))
    (hb : ∀ j, Measurable fun a => b a j) : ∀ n, Measurable fun a => pastOf (cf a) (R a) (b a) n
  | 0 => hcf
  | n + 1 => by
    have hF : Measurable fun a => ((fun u => GW2Rd.stgDrv (R a) (b a n) u), (⊤ : ℝ≥0∞)) :=
      (measurable_pi_iff.2 fun u => GW2Rd.measurable_stgDrv (R := fun t a => R a t) hRm hRc (hb n) u).prodMk
        measurable_const
    have hreg : ∀ a, IsRegularDriver ((fun u => GW2Rd.stgDrv (R a) (b a n) u), (⊤ : ℝ≥0∞)) := fun a =>
      ⟨(((hRc a).comp (continuous_const.add continuous_id)).sub continuous_const).continuousOn,
        by simp only [GW2Rd.stgDrv, add_zero, sub_self],
        fun t ht => absurd ht (not_le.2 ENNReal.coe_lt_top), fun h => absurd rfl h⟩
    have hT : Measurable fun a => ((b a (n + 1) - b a n : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp ((hb (n + 1)).sub (hb n))
    exact (measurable_pastOf hcf hRm hRc hb n).prodMk (GW2Schedule.measurable_recOf_joint hF hreg hT)

theorem measurable_stageRead (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (j : ℕ) :
    Measurable fun z => stageRead x s L N hN z j := by
  have hd := measurable_decHist N
  have hP : Measurable fun z => fun i : Fin L.length => (decHist N z).2 (Fin.cast hN i) :=
    measurable_pi_iff.2 fun i => (measurable_pi_apply _).comp (measurable_snd.comp hd)
  exact RootH29.measurable_forwardCapacity_random x s
    ((measurable_fst.comp hd).prodMk ((RootJ31.measurable_joinedRecord L).comp hP)) measurable_const

theorem measurable_stageBd (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (j : ℕ) :
    Measurable fun z => stageBd x s L N hN z j := by
  unfold stageBd
  split_ifs
  · exact measurable_const
  · exact (measurable_real_toNNReal.comp (measurable_stageRead x s L N hN j)).min GW2Rd.measurable_augA
  · exact GW2Rd.measurable_augA

/-- **The stage decoder is measurable.** -/
theorem measurable_stageDec (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) :
    Measurable (stageDec x s L N hN) :=
  measurable_pastOf (measurable_fst.comp (measurable_decHist N)) GW2Rd.measurable_augPre GW2Rd.continuous_augPre
    (fun j => measurable_stageBd x s L N hN j) N

/-! ### The instance's word map -/

/-- **The instance's word map**: the word map with the program's angles and the stage decoder. -/
def schedWordMap (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N)
    (θa : ℝ) : RecData → BoundaryWord :=
  wordMap κ c' x (progAngle L) N θa (stageDec x s L N hN)

/-- **The three `Good` targets of the instance's word map.** -/
theorem schedWordMap_targets (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) (θa k : ℝ) :
    Measurable (schedWordMap κ c' x s L N hN θa) ∧
      (range fun y => Supp8.Q3Stop.wordType k (schedWordMap κ c' x s L N hN θa y)).Countable ∧
      ∀ y, (schedWordMap κ c' x s L N hN θa y).IsSorted :=
  wordMap_targets κ c' x (progAngle L) N θa (measurable_stageDec x s L N hN) k

/-! ### The decoder returns the instance's own relative stage records -/

section Instance

variable {Ω : Type*} {sp : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {V : Ω → ℝ≥0∞} {T : ℝ≥0}
  {R : ℝ≥0 → Ω → ℝ}

/-- The relative stage boundaries of an instance: `0`, the clipped readings at the earlier physical stage times, the
instance's stage start. -/
def instBd (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (cf : RecData)
    (P : Fin N → RecData) (a : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  if j = 0 then 0 else if j < N then
    min (RootH29.forwardCapacity x s (GW2Schedule.schedTime 0 L j)
      (cf, RootJ31.joinedRecord L fun i => P (Fin.cast hN i))).toNNReal a
  else a

theorem decHist_augRec (N : ℕ) {xr y : Ω → RecData} {ω : Ω} {cf : RecData} {P : Fin N → RecData}
    (hx : xr ω = GW2Rd.stageEnc N (cf, P)) : decHist N (GW2Rd.augRec xr y ω) = (cf, P) := by
  unfold decHist GW2Rd.augRec
  rw [GW2Rd.pairEnc.symm_apply_apply, hx]
  exact (GW2Rd.stageEnc N).symm_apply_apply _

/-- **The decoder returns the instance's own relative stage records**: on the augmented record of an instance with
relative driver `R` (continuous, from `0`), the decoded past is the root record followed by the records of `R` between
the instance's boundaries `instBd …` (the clipped readings and the stage start `stgStart T`). -/
theorem stageDec_augRec (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) {xr : Ω → RecData}
    {ω : Ω} {cf : RecData} {P : Fin N → RecData} (hx : xr ω = GW2Rd.stageEnc N (cf, P))
    (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) :
    stageDec x s L N hN (GW2Rd.augRec xr (GW2Rd.stgPreRec sp W Wα ζα GT V T R) ω) =
      pastOf cf (fun u => R u ω) (instBd x s L N hN cf P (GW2Rd.stgStart sp W Wα ζα GT V T ω)) N := by
  have hd := decHist_augRec N (y := GW2Rd.stgPreRec sp W Wα ζα GT V T R) hx
  have hσ : GW2Rd.stgRecDec N (xr ω) = cf := by
    unfold GW2Rd.stgRecDec
    rw [hx, (GW2Rd.stageEnc N).symm_apply_apply]
  obtain ⟨-, hA, hPre⟩ := GW2Rd.augDec_spec (rec := fun _ => cf) (ω := ω) hσ hRc hR0
  have hbd : stageBd x s L N hN (GW2Rd.augRec xr (GW2Rd.stgPreRec sp W Wα ζα GT V T R) ω) =
      instBd x s L N hN cf P (GW2Rd.stgStart sp W Wα ζα GT V T ω) := by
    funext j
    unfold stageBd stageRead instBd
    rw [hd, hA]
  unfold stageDec
  rw [hd, hbd]
  refine pastOf_congr cf (B := GW2Rd.stgStart sp W Wα ζα GT V T ω) (fun u hu => hPre u (hA ▸ hu)) N
    fun j _ => ?_
  unfold instBd
  split_ifs
  · exact bot_le
  · exact min_le_right _ _
  · exact le_rfl

/-- **The instance's base word is the root word flowed through the instance's own relative stage records.** -/
theorem baseWord_augRec (κ : ℝ) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0) (L : List (ℝ × ℝ≥0)) (N : ℕ)
    (hN : L.length = N) {xr : Ω → RecData} {ω : Ω} {cf : RecData} {P : Fin N → RecData}
    (hx : xr ω = GW2Rd.stageEnc N (cf, P)) (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0) :
    baseWord κ c' x (progAngle L) N (stageDec x s L N hN)
        (GW2Rd.augRec xr (GW2Rd.stgPreRec sp W Wα ζα GT V T R) ω) =
      GW2JDetR5.stageWord (κ := κ) (rootWord κ c' x) (progAngle L) N
        (pastOf cf (fun u => R u ω) (instBd x s L N hN cf P (GW2Rd.stgStart sp W Wα ζα GT V T ω)) N) := by
  unfold baseWord
  rw [stageDec_augRec x s L N hN hx hRc hR0]

end Instance

end InteractingSLE.Theorem14.GW2Wm
