/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdqGap

/-!
# The near structure (N3), step F′: every history reads the root prefix as the reference does

Packet PROVE-GW2-SDE (round 16). All histories at a root share the root prefix, so the relative drivers of their
instances agree with the reference on the root prefix's clock:

* **`versions_agree`** (pathwise): two root-`x` versions of explorations that agree up to a time `T > 0`, with `T`
  before both contacts and the clock at `T` below both caps, agree on `[0, clock T]` (both are J31's reader of the
  horizon `T`, ROOTX's `version_eq_reader`; the endpoint by continuity);
* **`schedW_eq_root`**: on successful histories, every candidate's explored driver is the root stage's up to the root
  time (`GW2Sde.joinedRead_append_eq`, `stopRec_schedSpec_append`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Sdq

open Restart Exist.StagedLaw GW2Rz GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31

variable {Ω : Type*} {x₀ : ℝ} {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {W W' : ℝ≥0 → Ω → ℝ}
  {γ γ' α : Ω → ℝ≥0 → ℂ} {GT GT' : Set Ω}

/-- **Two versions of explorations agreeing up to `T` agree on the clock of `T`** (pathwise). -/
theorem versions_agree (hGT : ∀ ω ∈ GT, PhysGoodX x₀ s Wα ζα W γ α ω)
    (hGT' : ∀ ω ∈ GT', PhysGoodX x₀ s Wα ζα W' γ' α ω) (hs : 0 < s) (hx : 0 ≤ x₀) {R R' : ℝ≥0 → Ω → ℝ}
    {V V' : Ω → ℝ≥0∞} {T : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) (hω' : ω ∈ GT')
    (hR : VersionAtX x₀ s Wα ζα W γ α R V ω) (hR' : VersionAtX x₀ s Wα ζα W' γ' α R' V' ω) (hT0 : 0 < T)
    (hTc : (T : ℝ≥0∞) < contactX x₀ s γ α ω) (hTc' : (T : ℝ≥0∞) < contactX x₀ s γ' α ω)
    (hWW : ∀ t ≤ T, W t ω = W' t ω) (hV : ENNReal.ofReal (clockX x₀ s Wα ζα W T ω) < V ω)
    (hV' : ENNReal.ofReal (clockX x₀ s Wα ζα W' T ω) < V' ω) :
    ∀ u ≤ (clockX x₀ s Wα ζα W T ω).toNNReal, R u ω = R' u ω := by
  have hclk := GW2Sdo.clockX_congr (x₀ := x₀) (Wα := Wα) (ζα := ζα) (s := s) hWW
  have hlt : ∀ u : ℝ≥0, (u : ℝ) < clockX x₀ s Wα ζα W T ω → R u ω = R' u ω := fun u hu => by
    have huV : (u : ℝ≥0∞) ≤ V ω := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_le_ofReal hu.le).trans hV.le
    have huV' : (u : ℝ≥0∞) ≤ V' ω := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_le_ofReal (hu.le.trans hclk.le)).trans hV'.le
    rw [version_eq_reader hGT hs hx hω hR hT0 hTc hu huV,
      version_eq_reader hGT' hs hx hω' hR' hT0 hTc' (hclk ▸ hu) huV', GW2Sdo.recPair_congr hWW]
  intro u hu
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ (clockX x₀ s Wα ζα W T ω).toNNReal) with h0 | hpos
  · have hu0 : u = 0 := le_antisymm (h0 ▸ hu) (by simp)
    rw [hu0, hR.2.1, hR'.2.1]
  · have heq : EqOn (fun t => R t ω) (fun t => R' t ω) (Iio (clockX x₀ s Wα ζα W T ω).toNNReal) :=
      fun t ht => hlt t (by
        have ht' : t < (clockX x₀ s Wα ζα W T ω).toNNReal := ht
        have hcpos : 0 < clockX x₀ s Wα ζα W T ω := by
          by_contra hc
          rw [Real.toNNReal_of_nonpos (not_lt.1 hc)] at hpos
          exact lt_irrefl _ hpos
        rw [← Real.coe_toNNReal _ hcpos.le]
        exact_mod_cast ht')
    have hcl := heq.closure hR.1 hR'.1
    rw [closure_Iio' (show (Iio (clockX x₀ s Wα ζα W T ω).toNNReal).Nonempty from ⟨0, hpos⟩)] at hcl
    exact hcl hu

section Root

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The canonical records of a program's prefix do not see the appended tail. -/
theorem stopRec_schedSpec_append_list (c : SourceData Ω) (x : ℝ) (L : List (ℝ × ℝ≥0)) :
    ∀ (tail : List (ℝ × ℝ≥0)) {j : ℕ} (_ : j < L.length) (ω : Ω),
      stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x (L ++ tail)) j ω =
        stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L) j ω := by
  intro tail
  induction tail using List.reverseRecOn with
  | nil => intro j _ ω; rw [List.append_nil]
  | append_singleton tail y ih =>
    intro j hj ω
    rw [← List.append_assoc, stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x y
      (by rw [List.length_append]; omega) ω]
    exact ih hj ω

/-- **Every candidate's joined future driver is the root stage's up to the root time.** -/
theorem futureJoined_eq_root (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ Sec5.Prop513Schedule.lastTime 0 [rootEntry r.1]) :
    Gm.futureJoined c r l a ω t = Gm.futureJoined c (r.1, 0) [] 0 ω t := by
  have hF : futureProgram c r l a = [rootEntry r.1] ++ ((entryList l).reverse ++
      [((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a)]) := by
    simp only [futureProgram, historyProgram, schedOf, List.cons_append, List.nil_append]
  have hF0 : futureProgram c (r.1, 0) [] 0 = [rootEntry r.1] ++
      [((candidateAngle c (r.1, 0) 0 : ℝ), historyTime c (r.1, 0) [] + candidateCap c (r.1, 0) 0)] := by
    simp only [futureProgram, historyProgram, schedOf, entryList, List.map_nil, List.reverse_nil,
      List.cons_append, List.nil_append]
  unfold Gm.futureJoined
  have e1 : joinedRead [rootEntry r.1] (programRecords c (rootPt r.1) [rootEntry r.1] ω) t =
      joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t := by
    rw [hF]
    exact GW2Sde.joinedRead_append_eq _ _ _ _ (fun i hi hi' =>
      (stopRec_schedSpec_append_list c (rootPt r.1) [rootEntry r.1] _ hi ω).symm) ht
  have e2 : joinedRead [rootEntry r.1] (programRecords c (rootPt r.1) [rootEntry r.1] ω) t =
      joinedRead (futureProgram c (r.1, 0) [] 0)
        (programRecords c (rootPt (r.1, 0).1) (futureProgram c (r.1, 0) [] 0) ω) t := by
    rw [hF0]
    exact GW2Sde.joinedRead_append_eq _ _ _ _ (fun i hi hi' =>
      (stopRec_schedSpec_append_list c (rootPt r.1) [rootEntry r.1] _ hi ω).symm) ht
  rw [← e1, e2]

/-- **On successful histories, every candidate's explored driver is the root stage's up to the root time.** -/
theorem schedW_eq_root (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    {ω : Ω} (hs1 : oldSuccess c r l ω) (hs2 : oldSuccess c (r.1, 0) [] ω) {t : ℝ≥0}
    (ht : t ≤ Sec5.Prop513Schedule.lastTime 0 [rootEntry r.1]) :
    schedW c r l a t ω = schedW c (r.1, 0) [] 0 t ω := by
  unfold schedW
  rw [ite_eq_left_of_eq_true _ _ (eq_true hs1), ite_eq_left_of_eq_true _ _ (eq_true hs2)]
  exact futureJoined_eq_root c r l a ω ht

end Root

section AE

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
theorem historyTime_root (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    historyTime c (r.1, 0) [] = Sec5.Prop513Schedule.lastTime 0 [rootEntry r.1] := by
  rw [GW2Sde.historyTime_eq_lastTime]
  rfl

/-- **Every history's version reads the root prefix as the reference version does** (almost surely, on a good
counterflow record, both histories successful, the root time before both contacts, the clock at the root time below
both caps). -/
theorem ae_root_versions_agree (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R' : ℝ≥0 → Ω → ℝ}
    {V' : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V') (n : ℕ) :
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → oldSuccess c (r.1, 0) [] ω →
      (historyTime c (r.1, 0) [] : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      (historyTime c (r.1, 0) [] : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c (r.1, 0) [] 0) c.α ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) []) ω) < V' ω →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c (r.1, 0) [] 0) (historyTime c (r.1, 0) []) ω) <
        (refVer h13 c r.1 hx).2 n ω →
      ∀ u ≤ (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) []) ω).toNNReal,
        R' u ω = (refVer h13 c r.1 hx).1 n u ω := by
  have hspec := refVer_spec h13 c r.1 hx
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT', -, hGTae'⟩ := schedGTX_spec h13 c (r.1, 0) [] 0
  filter_upwards [hA.2.2.2.2.2.2, (hspec.1 n).1.1.2.2.2.2.2.2, hGTae, hGTae'] with ω h1 h1' hg hg' hcf hs1 hs2
    hc hc' hV hV' u hu
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ historyTime c (r.1, 0) []) with h0 | hT0
  · have hclk0 : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (historyTime c (r.1, 0) []) ω ≤ 0 := by
      rw [← h0]
      exact ENNReal.ofReal_eq_zero.1 (clockX_props hGT hs hx (hg.2 hcf)).2.2
    rw [Real.toNNReal_of_nonpos hclk0] at hu
    have hu0 : u = 0 := le_antisymm hu (by simp)
    rw [hu0, hA.2.2.1 ω, (hspec.1 n).1.1.2.2.1 ω]
  · refine versions_agree hGT hGT' hs hx (hg.2 hcf) (hg'.2 hcf) ⟨hA.2.1 ω, hA.2.2.1 ω, (h1 hcf).2.2⟩
      ⟨(hspec.1 n).1.1.2.1 ω, (hspec.1 n).1.1.2.2.1 ω, (h1' hcf).2.2⟩ hT0 hc hc'
      (fun t ht => schedW_eq_root c r l a hs1 hs2 (ht.trans (historyTime_root c r).le)) hV ?_ u hu
    exact hV'

end AE

end InteractingSLE.Theorem14.GW2Sdq
