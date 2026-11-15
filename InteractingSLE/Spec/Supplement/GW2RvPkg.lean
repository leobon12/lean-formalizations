import InteractingSLE.Spec.Supplement.GW2RvSlow
import InteractingSLE.Spec.Supplement.GW2RvStrict
import InteractingSLE.Spec.Supplement.GW2RzWire
import InteractingSLE.Spec.Supplement.GW2SdzPair

/-!
# Theorem 1.4, GW2: the package family at every root and the wiring of `VPairInputsXCS`

PROVE-GW2-ROOTX round 4 (decision D8). The concrete per-(history, candidate) stage variables of GW2 at a
root `x = rootPt r.1`, built from the root-`x` instances `GW2Rv.schedInstSX` (the corrected union shape) on a
scaled, strictly increasing, exhausting root-`x` version family (`SchedVerX`, e.g. `schedVerXCanon`):

* `pkgX h13 ver ch K` — near slots `(instX …).varX` at `K`'s near stops, slow slots `slowStageVarX` (the root-`x`
  slow stop of BUF's `lowCapStop` form), and `trivVar` at the roots that are not `GoodRoot` (negative root
  points or `s = 0`; the retained gate is null there, `ae_goodRoot_of_gate`);
* `vpkgXSafe_pkgX` — `VPkgXSafe` from the owners' instance inputs `InstInputsX` and BUF's `NearStopsX`;
* `vDriverIdN_pkgX`, `vStopExhaustsN_pkgX` — S1's driver identification and stop exhaustion at root 0, with no
  input;
* `vPairInputsXCS_of_rootx` / `vPairInputsXCS_of_sameSlots` — SDE's `VPairInputsXCS` from `RootPairInputsX`
  (resp. for any package with the same slots, such as SDE's near selection of `pkgX`), and Theorem 1.4 from it
  (`theorem14Statement_J32_scaled_rootx`).

The owners' remaining fields are exactly `RootPairInputsX`'s `inst` (RELDET/STAGEMEAN/GEOM2), `nearStop`,
`nearImg`, `shell` (BUF) and `words` (SDE).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rv

open Exist.StagedLaw Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2Rd GW2Rz GW2Sde GW2Sdh GW2Sdi GW2Sdx GW2Sdy
  GW2Sdz GW2Bh Supp8.Q3Stop

/-! ### The roots where the root-`x` instances apply -/

/-- **A good root**: a nonnegative root point and a positive retained time. -/
def GoodRoot {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : Prop :=
  0 ≤ rootPt r.1 ∧ 0 < c.s

/-- **The retained gate lives on good roots** (the cover event's root is admissible and its counterflow tip is
interior). -/
theorem ae_goodRoot_of_gate {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : ∀ᵐ ξ ∂c.P, ξ ∈ GW2Sdg.rootGate c r l → GoodRoot c r := by
  filter_upwards [RootCv.ae_coverEvent_spec h13 c r, c.hα] with ξ hcover hα hG
  obtain ⟨hseed, hsH, -⟩ := hcover hG.1
  refine ⟨RootH29.rootPt_nonneg_of_seedOK c hseed, ?_⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ c.s) with h | h
  · exfalso
    rw [← h, hα.1] at hsH
    exact (lt_irrefl (0 : ℝ)) hsH
  · exact h

/-! ### Version families at a root -/

/-- **A version family of a candidate at its root** (decision D3 at a root): announced root-`x` versions (at a
nonnegative root point) with finite monotone caps, strictly increasing on the good records, whose caps exhaust the
history's capacity plus the gain. -/
structure SchedVerX {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) where
  R : ℕ → ℝ≥0 → Ω → ℝ
  V : ℕ → Ω → ℝ≥0∞
  isA : 0 ≤ rootPt r.1 → ∀ n,
    IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)
  mono : ∀ n ω, V n ω ≤ V (n + 1) ω
  fin : ∀ n ω, V n ω ≠ ⊤
  strict : 0 ≤ rootPt r.1 → ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
    ∀ n, V n ω < V (n + 1) ω
  exhausts : 0 ≤ rootPt r.1 → ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
    ∀ᶠ n in atTop, ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V n ξ

/-- Version families for every source setup, root, history and candidate. -/
abbrev SchedVerXFamily :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), SchedVerX c r l a

section Canon

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

include h13 in
/-- **An exhausting root-`x` family exhausts the history's capacity plus the gain.** -/
theorem ae_exhausts_of_eventually {V : ℕ → Ω → ℝ≥0∞}
    (hev : ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < V n ξ) :
    ∀ᵐ ξ ∂c.P, ∀ u : ℝ≥0, u < GW2Sdg.rootGain c r l a ξ →
      ∀ᶠ n in atTop, ((GW2Sdg.rootHistCap c r l a ξ + u : ℝ≥0) : ℝ≥0∞) < V n ξ := by
  filter_upwards [hev, ae_exactPair_rootX h13 c r l a, ae_histCap_add_gainX h13 c r l a] with ξ hevξ hpair hsum
    u hu
  have hpos : 0 < GW2Sdg.rootGain c r l a ξ := lt_of_le_of_lt zero_le hu
  obtain ⟨hgx, hTc, -⟩ := hpair (live_of_gain_pos c r l a hpos)
  filter_upwards [hevξ hgx _ hTc] with n hn
  rw [← hsum hpos] at hn
  exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (add_le_add_right hu.le _)) hn

/-- **The canonical version family at a root**: at a nonnegative root point the strictly increasing root-`x`
family of `GW2Rv.exists_schedVersionsXA_strict` (chosen); a constant family otherwise (never read there). -/
def schedVerXCanon : SchedVerX c r l a :=
  open Classical in
  if hx : 0 ≤ rootPt r.1 then
    { R := (exists_schedVersionsXA_strict h13 c r l a hx).choose
      V := (exists_schedVersionsXA_strict h13 c r l a hx).choose_spec.choose
      isA := fun _ => (exists_schedVersionsXA_strict h13 c r l a hx).choose_spec.choose_spec.1
      mono := (exists_schedVersionsXA_strict h13 c r l a hx).choose_spec.choose_spec.2.1
      fin := (exists_schedVersionsXA_strict h13 c r l a hx).choose_spec.choose_spec.2.2.2.1
      strict := fun _ => (exists_schedVersionsXA_strict h13 c r l a hx).choose_spec.choose_spec.2.2.1
      exhausts := fun _ => ae_exhausts_of_eventually h13 c r l a
        (exists_schedVersionsXA_strict h13 c r l a hx).choose_spec.choose_spec.2.2.2.2 }
  else
    { R := fun _ _ _ => 0
      V := fun _ _ => 1
      isA := fun h => absurd h hx
      mono := fun _ _ => le_rfl
      fin := fun _ _ => ENNReal.one_ne_top
      strict := fun h => absurd h hx
      exhausts := fun h => absurd h hx }

end Canon

/-- **The canonical version families**, every source setup, root, history and candidate. -/
def schedVerXCanonFamily (h13 : Exist.Theorem13Statement.{u}) : SchedVerXFamily.{u} :=
  fun _ _ _ c r l a => schedVerXCanon h13 c r l a

/-! ### The package at every root -/

section Pkg

variable (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

/-- **The corrected root-`x` instance of version `n`** of a candidate at a nonnegative root point. -/
abbrev instX (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) (hx : 0 ≤ rootPt r.1) : StageInst Ω :=
  schedInstSX c r l a (schedGTX h13 c r l a) ((ver Ω c r l a).isA hx n) (ch Ω c r l a)

open Classical in
/-- **The near slot** `(l, n, m, a)` at every root: the root-`x` instance of version `m` with the near stop of the
base package at a good root, the trivial variable otherwise. -/
def nearSlotX (K : PkgFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (n m a : ℕ) : StageVar Ω :=
  if h : GoodRoot c r then (instX h13 ver ch Ω c r l a m h.1).varX c r l (rootPt r.1) ((K Ω c r).nearStop l n m a)
  else trivVar c r l

open Classical in
/-- **The slow slot** `(l, a, n)` at every root: decision D3's root-`x` slow stage variable `n` at a good root, the
trivial variable otherwise. -/
def slowSlotX (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) : StageVar Ω :=
  if h : GoodRoot c r then slowStageVarX h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) n
  else trivVar c r l

/-- **GW2's package family at every root** (decision D8): the near data and shells of a base package `K`, the near
variables `(l, n, m, a)` on the root-`x` instance of version `m` with `K`'s near stops, and the slow variable `n` on
the instance of version `n + 1` with the cap `V n` (trivial variables at the roots where no root-`x` instance
applies). -/
def pkgX (K : PkgFamily.{u}) : VPkgXFamily.{u} := fun Ω _ _ c r =>
  { nearFamily := (K Ω c r).nearFamily
    nearCandidate := (K Ω c r).nearCandidate
    nearVar := fun l n m a => nearSlotX h13 ver ch K Ω c r l n m a
    slowShell := (K Ω c r).slowShell
    slowVar := fun l a n => slowSlotX h13 ver ch Ω c r l a n }

/-- **The owners' inputs of the root-`x` instances** (the word map, the record event, `u₀`, and the open lines
inputs `GW2Rz.OpenLinesX`), at good roots on time-ordered histories, for every version. -/
structure InstInputsX : Prop where
  word : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
    Measurable (ch Ω c r l a).β ∧ (range fun y => wordType c.κ ((ch Ω c r l a).β y)).Countable ∧
      ∀ y, ((ch Ω c r l a).β y).IsSorted
  measurableSet_E₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
      MeasurableSet (ch Ω c r l a).E₀
  u₀ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → GoodRoot c r → ∀ a : ℕ,
      IsBoundedHarmonicExtension c.b c.jumps (ch Ω c r l a).u₀
  openLines : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → (h : GoodRoot c r) →
    ∀ a n : ℕ, OpenLinesX (instX h13 ver ch Ω c r l a n h.1) c r l (rootPt r.1) (measurable_schedW c r l a)

variable {h13 ver ch}

/-- **The root-`x` instances are good** at good roots on time-ordered histories. -/
theorem InstInputsX.goodX (hI : InstInputsX h13 ver ch) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} (hTO : HistOrdered c r l)
    (h : GoodRoot c r) (a n : ℕ) : (instX h13 ver ch Ω c r l a n h.1).GoodX c r l (rootPt r.1) :=
  schedInstSX_good c r l a h.2 h.1 (schedGTX_spec h13 c r l a) ((ver Ω c r l a).isA h.1 n) ((ver Ω c r l a).fin n)
    (ch Ω c r l a) (hI.word Ω c r l hTO h a) (hI.measurableSet_E₀ Ω c r l hTO h a) (hI.u₀ Ω c r l hTO h a)
    (hI.openLines Ω c r l hTO h a n)

/-- **The near stops of a base package are good on the root-`x` instances** (BUF's input), eventually in `m`. -/
def NearStopsX (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
    (K : PkgFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → (h : GoodRoot c r) → ∀ n : ℕ,
      ∀ᶠ m in atTop, ∀ a : ℕ, ((K Ω c r).nearStop l n m a).GoodX (instX h13 ver ch Ω c r l a m h.1) c r l (rootPt r.1)

/-- **`VPkgXSafe` for the package at every root** (the `safe` field of SDE's `VPairInputsXCS`): from the owners'
instance inputs and the near stops; the slow stops are proved good (`GW2Rv.lowCapStopX_good_family`). -/
theorem vpkgXSafe_pkgX (hI : InstInputsX h13 ver ch) {K : PkgFamily.{u}} (hK : NearStopsX h13 ver ch K) :
    VPkgXSafe (pkgX h13 ver ch K) := by
  classical
  refine vpkgXSafe_of_safeSlots _ (fun Ω _ _ c r l hTO n => ?_) (fun n Ω _ _ c r k l _ hTO a => ?_)
  · by_cases h : GoodRoot c r
    · filter_upwards [hK Ω c r l hTO h n] with m hm a
      refine Or.inr ⟨instX h13 ver ch Ω c r l a m h.1, (K Ω c r).nearStop l n m a, rootPt r.1, ?_,
        hI.goodX hTO h a m, hm a⟩
      change nearSlotX h13 ver ch K Ω c r l n m a = _
      unfold nearSlotX
      simp only [h, ↓reduceDIte]
    · refine Eventually.of_forall fun m a => Or.inl ?_
      change nearSlotX h13 ver ch K Ω c r l n m a = _
      unfold nearSlotX
      simp only [h, ↓reduceDIte]
  · by_cases h : GoodRoot c r
    · refine Or.inr ⟨slowInstX h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) n,
        slowCapStopX h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) n, rootPt r.1, ?_,
        hI.goodX hTO h a (n + 1), ?_⟩
      · change slowSlotX h13 ver ch Ω c r l a n = _
        unfold slowSlotX
        simp only [h, ↓reduceDIte]
      · exact lowCapStopX_good_family h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) h.1
          (ver Ω c r l a).mono (ver Ω c r l a).fin ((ver Ω c r l a).strict h.1) (fun n => hI.goodX hTO h a (n + 1)) n
    · refine Or.inl ?_
      change slowSlotX h13 ver ch Ω c r l a n = _
      unfold slowSlotX
      simp only [h, ↓reduceDIte]

/-- **`VDriverIdN` for the package at every root** (the `driverId` field of SDE's `VPairInputsXCS`; no input): at a
good root BUF's S1 at the root (`GW2Rv.vDriverIdN_slowStageVarX`), elsewhere the gate is null. -/
theorem vDriverIdN_pkgX (K : PkgFamily.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) :
    VDriverIdN (pkgX h13 ver ch K) Ω c r l a n := by
  classical
  by_cases h : GoodRoot c r
  · refine vDriverIdN_slowStageVarX h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) h.1
      (ver Ω c r l a).mono (ver Ω c r l a).fin n ?_
    change slowSlotX h13 ver ch Ω c r l a n = _
    unfold slowSlotX
    simp only [h, ↓reduceDIte]
  · filter_upwards [ae_goodRoot_of_gate h13 c r l] with ξ hξ hG
    exact absurd (hξ hG) h

/-- **D3a's exhaust form for the package at every root** (the `stopExhausts` field of SDE's `VPairInputsXCS`):
from the family's exhaustion at a good root; elsewhere the gate is null. -/
theorem vStopExhaustsN_pkgX (K : PkgFamily.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    VStopExhaustsN (pkgX h13 ver ch K) Ω c r l a := by
  classical
  by_cases h : GoodRoot c r
  · have hvar : ∀ n, (pkgX h13 ver ch K Ω c r).slowVar l a n =
        slowStageVarX h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) n := fun n => by
      change slowSlotX h13 ver ch Ω c r l a n = _
      unfold slowSlotX
      simp only [h, ↓reduceDIte]
    filter_upwards [(ver Ω c r l a).exhausts h.1, ae_all_iff.2 fun n =>
      ae_slowStageVarX_stop_eq h13 c r l a ((ver Ω c r l a).isA h.1) (fun _ => ch Ω c r l a) h.1 n]
      with ξ hex hstop _ u hu
    have hlive := live_of_gain_pos c r l a (lt_of_le_of_lt zero_le hu)
    filter_upwards [hex u hu] with n hn
    have hcap : ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) < (ver Ω c r l a).V (n + 1) ξ :=
      ((ENNReal.coe_le_coe.2 le_self_add).trans_lt hn).trans_le ((ver Ω c r l a).mono n ξ)
    rw [hvar n, hstop n hlive hcap, lt_tsub_iff_left, ← ENNReal.coe_add]
    exact hn
  · filter_upwards [ae_goodRoot_of_gate h13 c r l] with ξ hξ hG
    exact absurd (hξ hG) h

end Pkg

/-! ### Any package with the same slots (e.g. SDE's near selection `withNearS`) -/

section Slots

variable {V V' : VPkgXFamily.{u}}

/-- **Two packages with the same slots**: equal near and slow stage variables (the near families, candidates and
shells may differ, as in SDE's `withNear`/`withNearS`). -/
def SameSlots (V V' : VPkgXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    (V' Ω c r).nearVar = (V Ω c r).nearVar ∧ (V' Ω c r).slowVar = (V Ω c r).slowVar

theorem vpkgXSafe_of_sameSlots (h : VPkgXSafe V) (hs : SameSlots V V') : VPkgXSafe V' where
  nearSafe Ω _ _ c r l hTO n := by
    rw [(hs Ω c r).1]
    exact h.nearSafe Ω c r l hTO n
  slowSafe n Ω _ _ c r k l hl hTO a := by
    rw [(hs Ω c r).2]
    exact h.slowSafe n Ω c r k l hl hTO a

theorem vDriverIdN_of_sameSlots {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {a n : ℕ} (h : VDriverIdN V Ω c r l a n)
    (hs : SameSlots V V') : VDriverIdN V' Ω c r l a n := by
  unfold VDriverIdN
  rw [(hs Ω c r).2]
  exact h

theorem vStopExhaustsN_of_sameSlots {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {a : ℕ} (h : VStopExhaustsN V Ω c r l a)
    (hs : SameSlots V V') : VStopExhaustsN V' Ω c r l a := by
  unfold VStopExhaustsN
  rw [(hs Ω c r).2]
  exact h

end Slots

/-- **SDE's `VPairInputsXCS` for any package with the slots of the package at every root** (for instance SDE's near
selection `withNearS` of it): `lam_ne`, `safe`, `driverId` and `stopExhausts` are discharged as in
`vPairInputsXCS_of_rootx`; `words`, `nearImg` and `shell` are the owners' fields for that package. -/
theorem vPairInputsXCS_of_sameSlots {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    {ch : SchedChoiceFamily.{u}} {Kb : ℕ → PkgFamily.{u}} {gap : RootCv.GapFamily.{u}} {V : ℕ → VPkgXFamily.{u}}
    (hs : ∀ k, SameSlots (pkgX h13 ver ch (Kb k)) (V k)) (hI : InstInputsX h13 ver ch)
    (hnear : ∀ k : ℕ, NearStopsX h13 ver ch (Kb k)) (hwords : ∀ k : ℕ, VWordsX (J32S gap) (V k) nearLam)
    (hnearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      VNearImgOn ((V k).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
        (((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l))
    (hshell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
        ∀ᵐ ω ∂c.P, ω ∈ ((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l →
          ShellFactLe c.κ (RootJ31.sourceDriftBound c r) ((V 0 Ω c r).slowShell l a ω) ∧
            ((V 0 Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω) :
    VPairInputsXCS V nearLam gap where
  lam_ne := nearLam_ne
  safe k := vpkgXSafe_of_sameSlots (vpkgXSafe_pkgX hI (hnear k)) (hs k)
  words := hwords
  nearImg := hnearImg
  driverId _ _ _ c r _ l _ a n := vDriverIdN_of_sameSlots (vDriverIdN_pkgX (Kb 0) c r l a n) (hs 0)
  stopExhausts _ _ _ c r _ l _ a := vStopExhaustsN_of_sameSlots (vStopExhaustsN_pkgX (Kb 0) c r l a) (hs 0)
  shell := hshell

/-! ### SDE's successor pair and Theorem 1.4 at every root -/

/-- **The owners' remaining inputs of SDE's successor pair for the package at every root**: the instance inputs
(RELDET's union marks and locality, STAGEMEAN's mean, no-threshold and conditional GFF, the word map's properties,
`u₀`), the near stops (BUF), the near words (SDE), the lossy near facts (BUF) and the shells (BUF, GEOM2). The fields
`lam_ne`, `safe`, `driverId` and `stopExhausts` of `GW2Sdz.VPairInputsXCS` are proved from these
(`vPairInputsXCS_of_rootx`). -/
structure RootPairInputsX (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) (Kb : ℕ → PkgFamily.{u}) (gap : RootCv.GapFamily.{u}) : Prop where
  inst : InstInputsX h13 ver ch
  nearStop : ∀ k : ℕ, NearStopsX h13 ver ch (Kb k)
  words : ∀ k : ℕ, VWordsX (J32S gap) (pkgX h13 ver ch (Kb k)) nearLam
  nearImg : ∀ (k : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
    VNearImgOn ((pkgX h13 ver ch (Kb k)).at 0) nearLam Ω c r l ((k : ℝ≥0∞) + 1)⁻¹
      (((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l)
  shell : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 → ∀ a : ℕ,
      ∀ᵐ ω ∂c.P, ω ∈ ((J32S gap Ω c).experiment r).data.alive ((J32S gap Ω c).G r) l →
        ShellFactLe c.κ (RootJ31.sourceDriftBound c r) ((pkgX h13 ver ch (Kb 0) Ω c r).slowShell l a ω) ∧
          ((pkgX h13 ver ch (Kb 0) Ω c r).slowShell l a ω).start = GW2Bf.histStart c r l ω

/-- **SDE's `VPairInputsXCS` for the package at every root** (decision D8's wiring): `lam_ne` (R112's dilations),
`safe` (the root-`x` engine on the owners' instance inputs, and the slow stops proved good), `driverId` (BUF's S1 at
the root, proved) and `stopExhausts` (D3a's exhaust form from the version family, proved) are discharged. -/
theorem vPairInputsXCS_of_rootx {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    {ch : SchedChoiceFamily.{u}} {Kb : ℕ → PkgFamily.{u}} {gap : RootCv.GapFamily.{u}}
    (hK : RootPairInputsX h13 ver ch Kb gap) :
    VPairInputsXCS (fun k => pkgX h13 ver ch (Kb k)) nearLam gap where
  lam_ne := nearLam_ne
  safe k := vpkgXSafe_pkgX hK.inst (hK.nearStop k)
  words := hK.words
  nearImg := hK.nearImg
  driverId _ _ _ c r _ l _ a n := vDriverIdN_pkgX (Kb 0) c r l a n
  stopExhausts _ _ _ c r _ l _ a := vStopExhaustsN_pkgX (Kb 0) c r l a
  shell := hK.shell

/-- **SDE's successor pair at every root**: both lossy binders for J32 on the scaled cover from the owners' remaining
inputs at every root (decisions D1, D3, D3a, D8; R113, R114, R118; Theorems 1.2–1.3, R48). -/
theorem retainedComparisonsLossy_rootx (h12p₀ : Exist.Staged.Theorem12ParamStatement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u})
    (ch : SchedChoiceFamily.{u}) (Kb : ℕ → PkgFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hK : RootPairInputsX h13 ver ch Kb gap) :
    RetainedNearModelsLossyStatement (J32S gap) ∧ RetainedSlowComparisonsLossyStatement (J32S gap) :=
  retainedComparisonsLossyXCS_vpkg h12p₀ h13₀ h13 _ nearLam gap (vPairInputsXCS_of_rootx hK)

/-- **Theorem 1.4 with J32 on the scaled cover, the package at every root** (SDE's
`GW2Sdz.theorem14Statement_J32_scaled_vpkgXCS` fed with `vPairInputsXCS_of_rootx`): binders the gap's measurability
and positivity, the owners' remaining inputs at every root, and SB2's three statements. -/
theorem theorem14Statement_J32_scaled_rootx (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
    (Kb : ℕ → PkgFamily.{u}) (hK : RootPairInputsX h13 ver ch Kb gap)
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  theorem14Statement_J32_scaled_vpkgXCS gap hgap hpos _ nearLam (vPairInputsXCS_of_rootx hK) hN hgeo hcond

end InteractingSLE.Theorem14.GW2Rv
