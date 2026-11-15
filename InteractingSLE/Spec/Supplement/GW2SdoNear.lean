/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoWord
import InteractingSLE.Spec.Supplement.GW2SdoReidx
import InteractingSLE.Spec.Supplement.GW2GmJoin
import InteractingSLE.Spec.Supplement.GW2SgDec

/-!
# The near words (N1)–(N2) at a root `x`: one stage record for all candidates, eventually

Packet PROVE-GW2-SDE (round 14). The near word of the history `l` is read at the selected candidate, which changes
with the index `m`. With ROOTX's root-`x` instances (`GW2Rz.schedInstX`) and any root-`x` version families of the
candidates (monotone, each passing the history's clock eventually), re-indexed deterministically
(`exists_reindex_eventually_all`):

* `mem_aliveRecX` (pathwise): the augmented root-`x` stage record is a live record (`GW2Rz.aliveRecX`) when the
  counterflow record is good and the stage start is below the cap (the cap is a path rule of the version);
* **`exists_reindex_nearRecords`**: there are monotone re-indexings `ψ a` (`ψ a m ≥ m`) and ONE record `pre` such that
  almost surely, on a good counterflow record with the history time before every candidate's root-`x` contact,
  eventually in `m`, EVERY candidate's instance with version `ψ a m` has stage record `augRec (stageEncRec c r l) pre`,
  and this record is live for it;
* **`exists_reindex_nearWords`**: with GEOM2's root-`x` word map (`GW2Wm.schedWordMapX`, any angle `θ a` per candidate),
  every such instance's word at its record is `upW (θ a χ) (base ω)` for ONE base word
  `base = baseWordX … (augRec (stageEncRec c r l) pre)`: the near words (N1)–(N2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdo

open Restart Exist.StagedLaw GW2Rz GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

/-- **A live root-`x` stage record** (pathwise): good counterflow record and stage start below the cap. -/
theorem mem_aliveRecX {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {T : ℝ≥0} {R : ℝ≥0 → Ω → ℝ} {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρ : Supp8.GB6.HullId.IsPathRule ρ) {N : ℕ} {x : Ω → RecData} {ω : Ω}
    (hx : stgRecDec N (x ω) = cfRec s Wα ζα ω) (hRc : Continuous fun u => R u ω) (hR0 : R 0 ω = 0)
    (hgood : cfRec s Wα ζα ω ∈ goodX x₀ s) (hVρ : V ω = ρ (cfRec s Wα ζα ω, fun u => R u ω))
    (hlt : (stgStartX x₀ s Wα ζα W GT V T ω : ℝ≥0∞) < V ω) :
    augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω ∈ aliveRecX N x₀ s ρ := by
  obtain ⟨hd1, hd2, hd3⟩ := augDec_specX (x₀ := x₀) (s := s) (W := W) (Wα := Wα) (ζα := ζα) (GT := GT) (V := V)
    (T := T) hx hRc hR0
  refine ⟨hd1 ▸ hgood, ?_⟩
  rw [hd1, hd2]
  by_contra hcon
  have hle := not_lt.1 hcon
  have hpr : ρ (cfRec s Wα ζα ω, fun u => R u ω) =
      ρ (cfRec s Wα ζα ω, augPre (augRec x (stgPreRecX x₀ s Wα ζα W GT V T R) ω)) :=
    hρ _ _ _ fun u hu => hd3 u (by rw [hd2]; exact ENNReal.coe_le_coe.1 (hu.trans hle))
  rw [← hpr, ← hVρ] at hle
  exact absurd (hlt.trans_le hle) (lt_irrefl _)

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
theorem continuous_schedW (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ω : Ω) : Continuous (schedW c r l a · ω) ∧ schedW c r l a 0 ω = 0 := by
  unfold schedW
  split_ifs
  · exact Gm.continuous_futureJoined c r l a ω
  · exact ⟨continuous_const, rfl⟩

/-- **One live stage record for all candidates, eventually** (re-indexed root-`x` versions). -/
theorem exists_reindex_nearRecords (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1)
    (Rv : ℕ → ℕ → ℝ≥0 → Ω → ℝ) (Vv : ℕ → ℕ → Ω → ℝ≥0∞)
    (hA : ∀ a k, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (Rv a k)
      (Vv a k))
    (hmono : ∀ a ω, Monotone fun k => Vv a k ω)
    (hex : ∀ a, ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ∃ k, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < Vv a k ω) :
    ∃ ψ : ℕ → ℕ → ℕ, (∀ a, Monotone (ψ a)) ∧ (∀ a m, m ≤ ψ a m) ∧ ∃ pre : Ω → RecData,
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (∀ a, (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω) →
        ∀ᶠ m in atTop, ∀ a,
          stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (Vv a (ψ a m))
            (historyTime c r l) (Rv a (ψ a m)) ω = pre ω ∧
          augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            (Vv a (ψ a m)) (historyTime c r l) (Rv a (ψ a m))) ω ∈
            aliveRecX ((entryList l).length + 1) (rootPt r.1) c.s (hA a (ψ a m)).1.2.choose := by
  classical
  set T := historyTime c r l with hTdef
  set x₀ := rootPt r.1 with hx₀
  -- the good events of the slots
  set E : ℕ → ℕ → Set Ω := fun a k =>
    {ω | ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l a) T ω) < Vv a k ω} with hEdef
  have hEm : ∀ a k, MeasurableSet (E a k) := fun a k => by
    have hclk : Measurable fun ω => clockX x₀ c.s c.W c.ζ (schedW c r l a) T ω :=
      RootH29.measurable_forwardCapacity_random x₀ c.s
        (measurable_recPair (measurable_gb6Rec_src c) (measurable_schedW c r l a)
          (fun ω => (continuous_schedW c r l a ω).1) (fun ω => (continuous_schedW c r l a ω).2) T)
        measurable_const
    exact measurableSet_lt (ENNReal.measurable_ofReal.comp hclk) (hA a k).1.1.2.2.2.2.1
  have hEmono : ∀ a, Monotone (E a) := fun a k k' hkk' ω hω => lt_of_lt_of_le hω (hmono a ω hkk')
  obtain ⟨ψ, hψmono, hψge, hψ⟩ := exists_reindex_eventually_all (μ := c.P) E hEm hEmono
  -- the common record: that of the first good slot
  set pre : Ω → RecData := fun ω =>
    if h : ∃ p : ℕ × ℕ, ω ∈ E p.1 p.2 then
      stgPreRecX x₀ c.s c.W c.ζ (schedW c r l h.choose.1) (schedGTX h13 c r l h.choose.1)
        (Vv h.choose.1 h.choose.2) T (Rv h.choose.1 h.choose.2) ω
    else stgPreRecX x₀ c.s c.W c.ζ (schedW c r l 0) (schedGTX h13 c r l 0) (Vv 0 0) T (Rv 0 0) ω with hpre
  refine ⟨ψ, hψmono, hψge, pre, ?_⟩
  have hpair : ∀ᵐ ω ∂c.P, ∀ p q : ℕ × ℕ, cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s →
      ((T : ℝ≥0∞) < contactX x₀ c.s (schedTr c r l p.1) c.α ω ∧
        ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l p.1) T ω) < Vv p.1 p.2 ω) →
      ((T : ℝ≥0∞) < contactX x₀ c.s (schedTr c r l q.1) c.α ω ∧
        ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l q.1) T ω) < Vv q.1 q.2 ω) →
      stgPreRecX x₀ c.s c.W c.ζ (schedW c r l p.1) (schedGTX h13 c r l p.1) (Vv p.1 p.2) T (Rv p.1 p.2) ω =
        stgPreRecX x₀ c.s c.W c.ζ (schedW c r l q.1) (schedGTX h13 c r l q.1) (Vv q.1 q.2) T (Rv q.1 q.2) ω :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q =>
      ae_stgPreRecX_sched_eq h13 c r l p.1 q.1 hs hx (hA p.1 p.2).1.1 (hA q.1 q.2).1.1
  have hρ : ∀ᵐ ω ∂c.P, ∀ p : ℕ × ℕ,
      Vv p.1 p.2 ω = (hA p.1 p.2).1.2.choose (cfRec c.s c.W c.ζ ω, fun u => Rv p.1 p.2 u ω) :=
    ae_all_iff.2 fun p => (hA p.1 p.2).1.2.choose_spec.2.2
  have hexAll := ae_all_iff.2 hex
  have hGTall : ∀ᵐ ω ∂c.P, ∀ a, ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s :=
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  filter_upwards [hψ, hpair, hρ, hexAll, hGTall] with ω hω hpω hρω hexω hGTω hcf hcon
  filter_upwards [hω] with m hm a
  have hgood : ω ∈ E a (ψ a m) := hm a (hexω a hcf (hcon a))
  have hex0 : ∃ p : ℕ × ℕ, ω ∈ E p.1 p.2 := ⟨(a, ψ a m), hgood⟩
  have heq : stgPreRecX x₀ c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (Vv a (ψ a m)) T
      (Rv a (ψ a m)) ω = pre ω := by
    simp only [hpre, hex0, ↓reduceDIte]
    exact hpω (a, ψ a m) hex0.choose hcf ⟨hcon a, hgood⟩ ⟨hcon _, hex0.choose_spec⟩
  refine ⟨heq, ?_⟩
  have hstart : (stgStartX x₀ c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (Vv a (ψ a m)) T ω : ℝ≥0∞) <
      Vv a (ψ a m) ω := by
    rw [stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx ((hGTω a).2 hcf) (hcon a) hgood]
    exact hgood
  exact mem_aliveRecX (hA a (ψ a m)).1.2.choose_spec.2.1 (stgRecDec_stageEncRec c r l ω)
    ((hA a (ψ a m)).1.1.2.1 ω) ((hA a (ψ a m)).1.1.2.2.1 ω) hcf (hρω (a, ψ a m)) hstart

/-- **The near words (N1)–(N2) at a root `x`** (GEOM2's root-`x` word map, any angles `θ a`): with re-indexed
versions, almost surely on a good counterflow record with the history time before every candidate's root-`x` contact,
eventually in `m`, EVERY candidate's instance reads the word `upW (θ a χ) (base ω)` of ONE base word at its stage
record, and the record is in the instance's record event as soon as it is in `E₀ a`. -/
theorem exists_reindex_nearWords (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1)
    (Rv : ℕ → ℕ → ℝ≥0 → Ω → ℝ) (Vv : ℕ → ℕ → Ω → ℝ≥0∞)
    (hA : ∀ a k, IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (Rv a k)
      (Vv a k))
    (hmono : ∀ a ω, Monotone fun k => Vv a k ω)
    (hex : ∀ a, ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ∃ k, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c r l) ω) < Vv a k ω)
    (c' : BoundaryWord) (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (θ : ℕ → ℝ) (E₀ : ℕ → Set RecData)
    (u₀ : ℕ → ℂ → ℝ) (ℋ : ℕ → ℝ≥0 → MeasurableSpace Ω) :
    ∃ ψ : ℕ → ℕ → ℕ, (∀ a, Monotone (ψ a)) ∧ (∀ a m, m ≤ ψ a m) ∧ ∃ base : Ω → BoundaryWord,
      ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
        (∀ a, (historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω) →
        ∀ᶠ m in atTop, ∀ a,
          ((schedInstX c r l a (schedGTX h13 c r l a) (hA a (ψ a m))
              (GW2Wm.wmChoiceX c.κ c' (rootPt r.1) c.s L N hN (θ a) (E₀ a) (u₀ a) (ℋ a))).srecX c r l
              (rootPt r.1) ω ∈ E₀ a →
            (schedInstX c r l a (schedGTX h13 c r l a) (hA a (ψ a m))
              (GW2Wm.wmChoiceX c.κ c' (rootPt r.1) c.s L N hN (θ a) (E₀ a) (u₀ a) (ℋ a))).srecX c r l
              (rootPt r.1) ω ∈ (schedInstX c r l a (schedGTX h13 c r l a) (hA a (ψ a m))
              (GW2Wm.wmChoiceX c.κ c' (rootPt r.1) c.s L N hN (θ a) (E₀ a) (u₀ a) (ℋ a))).E) ∧
          (schedInstX c r l a (schedGTX h13 c r l a) (hA a (ψ a m))
              (GW2Wm.wmChoiceX c.κ c' (rootPt r.1) c.s L N hN (θ a) (E₀ a) (u₀ a) (ℋ a))).β
            ((schedInstX c r l a (schedGTX h13 c r l a) (hA a (ψ a m))
              (GW2Wm.wmChoiceX c.κ c' (rootPt r.1) c.s L N hN (θ a) (E₀ a) (u₀ a) (ℋ a))).srecX c r l
              (rootPt r.1) ω) = GW2Rd.upW (θ a * chiC c.κ) (base ω) := by
  obtain ⟨ψ, hψm, hψge, pre, hpre⟩ := exists_reindex_nearRecords h13 c r l hs hx Rv Vv hA hmono hex
  refine ⟨ψ, hψm, hψge, fun ω => GW2Wm.baseWordX c.κ c' (rootPt r.1) c.s L N hN
    (augRec (stageEncRec c r l) pre ω), ?_⟩
  filter_upwards [hpre] with ω hω hcf hcon
  filter_upwards [hω hcf hcon] with m hm a
  obtain ⟨heq, hlive⟩ := hm a
  have hrec : (schedInstX c r l a (schedGTX h13 c r l a) (hA a (ψ a m))
      (GW2Wm.wmChoiceX c.κ c' (rootPt r.1) c.s L N hN (θ a) (E₀ a) (u₀ a) (ℋ a))).srecX c r l (rootPt r.1) ω =
      augRec (stageEncRec c r l) pre ω := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (schedGTX h13 c r l a) (Vv a (ψ a m)) (historyTime c r l) (Rv a (ψ a m))) ω = _
    simp only [augRec, heq]
  refine ⟨fun h0 => ⟨h0, hlive⟩, ?_⟩
  rw [hrec]
  rfl

end InteractingSLE.Theorem14.GW2Sdo
