/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TuPast
import InteractingSLE.Spec.Supplement.GW2RuShell
import InteractingSLE.Spec.Supplement.GW2SdrSpan

/-!
# Decision D37 (with D43): the far junction on every alive history of `J32S gapFam`

Packet PROVE-GW2-RELDET (round 32). With the two-sided gap `GW2Sdq.gapFam` (decision D43), on every alive history of
the scaled J32, at every good slot (the history's clock below the version's cap), the decoded past of the stage has the
far junction of the lower, rightward structure.

* `three_sqrt_lt_of_junctionFun`: `3 < 2ᵏ·junctionFun p` puts both of `p`'s junctions beyond `3√s` (`λ ≥ 17/35`);
* `stgStartX_mono`, `trueBdX_mono_sched`: the decoder's boundaries are ordered (time-ordered history);
* **`ae_root_junctionFun`**: on alive histories the root record of every good slot satisfies `3 < 2ᵏ·junctionFun`
  (it is the gap's reference record; SDE's `ae_firstSpan` with the two-sided gap);
* **`ae_drift_sign`**: after a passed test of `(l₁, a₁)` at `q₁`, the version of the next history moved, between
  the root time and `q₁`, toward the side of that test: `0 < (−1)^{|l₁|} (R(clock q₁) − R(clock v₀))` (ROOTX's
  `ae_sourceX_eq_version`, `version_eq_of_drv_eq`);
* **`ae_farJunction`**: the far junction of `GW2Wm.pastOf cf R (trueBdX …) N` at every alive history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Wm
  GW2Schedule GW2Tip Sec5.Prop513Schedule GW2Sdp

/-! ### The gap's bound on the root junctions -/

/-- **The two-sided gap puts both root junctions beyond `3√s`.** -/
theorem three_sqrt_lt_of_junctionFun {k : ℕ} {lam : ℝ≥0} (hlam : (17 / 35 : ℝ≥0) ≤ lam) {p : RecData}
    (h : 3 < (2 : ℝ) ^ k * GW2Sdq.junctionFun p) :
    3 * Real.sqrt (GW2Sdh.nearRootScale k lam) < -markPosL (rdrv p) (rtime p) 0 ∧
      3 * Real.sqrt (GW2Sdh.nearRootScale k lam) < markPos (rdrv p) (rtime p) 0 := by
  set m := min (-markPosL (rdrv p) (rtime p) 0) (markPos (rdrv p) (rtime p) 0) with hm
  have hA : (0 : ℝ) < 2 ^ k := by positivity
  have hJ : GW2Sdq.junctionFun p = 17 / 35 * min m 1 := rfl
  have hlam' : (17 / 35 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
  have hmin : min m 1 ≤ m := min_le_left _ _
  have hm3 : 3 < 2 ^ k * (17 / 35) * m := by
    rw [hJ] at h
    nlinarith
  have hmpos : 0 < m := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hpos : (0 : ℝ) < 2 ^ k * lam := mul_pos hA (lt_of_lt_of_le (by norm_num) hlam')
  have hsq : Real.sqrt (GW2Sdh.nearRootScale k lam) = ((2 : ℝ) ^ k * lam)⁻¹ := by
    rw [← GW2Sdh.sqrt_nearRootScale_inv, inv_inv]
  have hml : m * (2 ^ k * (17 / 35)) ≤ m * (2 ^ k * lam) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlam' hA.le) hmpos.le
  have key : 3 * Real.sqrt (GW2Sdh.nearRootScale k lam) < m := by
    rw [hsq, ← div_eq_mul_inv, div_lt_iff₀ hpos]
    nlinarith
  exact ⟨key.trans_le (min_le_left _ _), key.trans_le (min_le_right _ _)⟩

/-! ### The decoder's boundaries are ordered -/

section Bd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
/-- The root-`x` stage start is monotone in the physical time. -/
theorem stgStartX_mono {x₀ : ℝ} {sp : ℝ≥0} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ}
    {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX x₀ sp Wα ζα W γ α ω) (hs : 0 < sp) (hx : 0 ≤ x₀) {V : Ω → ℝ≥0∞}
    {ω : Ω} (hV : V ω ≠ ⊤) {t t' : ℝ≥0} (htt : t ≤ t') :
    stgStartX x₀ sp Wα ζα W GT V t ω ≤ stgStartX x₀ sp Wα ζα W GT V t' ω := by
  unfold stgStartX stgStartMX
  exact ENNReal.toNNReal_mono (ne_top_of_le_ne_top hV (min_le_right _ _))
    (min_le_min_right _ (monotone_physClockX hGT hs hx ω htt))

/-- **The decoder's boundaries of a time-ordered history are ordered.** -/
theorem trueBdX_mono_sched (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {V : Ω → ℝ≥0∞} {ω : Ω}
    (hV : V ω ≠ ⊤) (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) :
    ∀ j < (entryList l).length,
      trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (RootJ31.historyTime c r l) ω (j + 1) ≤
        trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (RootJ31.historyTime c r l) ω (j + 2) := by
  intro j hj
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r l a
  have hLN : (RootJ31.historyProgram c r l).length = (entryList l).length + 1 := GW2Ru.length_historyProgram c r l
  have h1 : j + 1 < (entryList l).length + 1 := by omega
  unfold trueBdX
  rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_left h1, ite_eq_right (Nat.succ_ne_zero _)]
  have hj1 : j < (RootJ31.historyProgram c r l).length := by omega
  by_cases h2 : j + 2 < (entryList l).length + 1
  · rw [ite_eq_left h2]
    refine stgStartX_mono hGT hs hx hV ?_
    have hj2 : j + 1 < (RootJ31.historyProgram c r l).length := by omega
    rw [Gm.schedTime_succ_eq_getElem hj1, Gm.schedTime_succ_eq_getElem hj2]
    exact List.pairwise_iff_getElem.1 hord.1 j (j + 1) hj1 hj2 (Nat.lt_succ_self j)
  · rw [ite_eq_right h2]
    exact stgStartX_mono hGT hs hx hV (GW2Ru.schedTime_le_historyTime c r l hord (by omega))

end Bd

/-! ### The root junctions on alive histories -/

section Root

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **On alive histories of `J32S gapFam`, the root record of a good slot satisfies `3 < 2ᵏ·junctionFun`**: it is
the gap's reference record (SDE's `ae_firstSpan`, with the two-sided gap). -/
theorem ae_root_junctionFun (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) {R' : ℝ≥0 → Ω → ℝ} {V' : Ω → ℝ≥0∞}
    (hA : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R' V') :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) < V' ω →
      3 < (2 : ℝ) ^ r.2 * GW2Sdq.junctionFun (recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
        (RootJ31.historyTime c (r.1, 0) []) ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤)) := by
  have h13 : Exist.Theorem13Statement.{u} := Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
  set x := r.1 with hxdef
  have hspec := GW2Sdq.refVer_spec h13 c x hx
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  obtain ⟨hGT0, -, hGTae0⟩ := schedGTX_spec h13 c (x, 0) [] 0
  filter_upwards [GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r, GW2Ru.ae_nil_lt_contactX h13 c (x, 0),
    GW2Sdq.ae_gapFam_eq c x ⟨hx, hs⟩, GW2Sdq.ae_refFun_eq h13 c x hx hs,
    ae_all_iff.2 fun n => GW2Sdq.ae_root_versions_agree h13 c r l a hs hx hA n, hGTae, hGTae0]
    with ω hgoodEv hnil hgap href hagree hGTω hGTω0 halive hV'
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hcover, hsucc, hord⟩ := RootJ32.alive_spec c r l ω halive32
  have halive0 : ω ∈ (RootJ32.experiment c (x, 0)).data.alive ((RootJ32.construction c).G (x, 0)) [] := hcover
  have hsucc0 : RootJ31.oldSuccess c (x, 0) [] ω := (RootJ32.alive_spec c (x, 0) [] ω halive0).2.1
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hTc0 := hnil 0 halive0
  have hTle := GW2Sdr.historyTime_root_le c r l hord
  have hTc : ((RootJ31.historyTime c (x, 0) [] : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt x) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 hTle).trans_lt (hcon a)
  have hω := hGTω.2 hcf
  have hω0 := hGTω0.2 hcf
  have hmono := (clockX_props hGT hs hx hω).2.1
  have hV'0 : ENNReal.ofReal (clockX (rootPt x) c.s c.W c.ζ (schedW c r l a)
      (RootJ31.historyTime c (x, 0) []) ω) < V' ω := (hmono hTc (hcon a) hTle).trans_lt hV'
  obtain ⟨n, hn1, hn2⟩ := (href hcf hTc0).exists
  have hWW : ∀ t ≤ RootJ31.historyTime c (x, 0) [], schedW c r l a t ω = schedW c (x, 0) [] 0 t ω := fun t ht =>
    GW2Sdq.schedW_eq_root c r l a hsucc hsucc0 (ht.trans (GW2Sdq.historyTime_root c r).le)
  have hclk : clockX (rootPt x) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c (x, 0) []) ω =
      clockX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (RootJ31.historyTime c (x, 0) []) ω :=
    GW2Sdo.clockX_congr hWW
  have hag := hagree n hcf hsucc hsucc0 hTc hTc0 hV'0 hn2
  have hS := GW2Sdo.stgStartX_eq_clockX hGT0 hs hx hω0 hTc0 hn2
  have hq : recOf (((clockX (rootPt x) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c (x, 0) []) ω).toNNReal :
      ℝ≥0) : ℝ≥0∞) (fun u => R' u ω, ⊤) = GW2Sdq.refPre h13 c x hx n ω := by
    change _ = recOf ((stgStartX (rootPt x) c.s c.W c.ζ (schedW c (x, 0) [] 0) (schedGTX h13 c (x, 0) [] 0)
      ((GW2Sdq.refVer h13 c x hx).2 n) (RootJ31.historyTime c (x, 0) []) ω : ℝ≥0) : ℝ≥0∞)
        (fun u => (GW2Sdq.refVer h13 c x hx).1 n u ω, ⊤)
    rw [hS, ← hclk]
    exact recOf_congr_top hag
  rw [hq]
  have hsc : RootCv.scaledCoverEvent c (GW2Sdq.gapFam Ω c) r ω :=
    GW2Sdr.alive_subset_scaledCover GW2Sdq.gapFam c r l halive
  have hg3 : 3 < 2 ^ r.2 * GW2Sdq.gapFam Ω c x ω := hsc.2
  rw [← hgap.symm.trans hn1]
  exact hg3

end Root

/-! ### The drift after the root stage -/

section Drift

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The drift after the root stage points to the side of the last passed test**: almost surely, at every alive
history `l = e :: l₁` of J32 with the history's clock below the cap of a version `R` of `(l, a)`, the version moved
between the root time and the history's time by `(−1)^{|l₁|} 2ᵏ ΔR ∈ (7/4, 9/4)`; in particular toward the side of
the sign `(−1)^{|l₁|}` (ROOTX's reading `ae_sourceX_eq_version` of the passed test of `(l₁, a₁)`). -/
theorem ae_drift_sign (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) < V ω →
      ∀ (e : EntryIdx c.Θ c.Q) (l₁ : List (EntryIdx c.Θ c.Q)), l = e :: l₁ →
        7 / 4 < (-1) ^ l₁.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
          (R (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω).toNNReal ω -
            R (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (rootEntry r.1).2 ω).toNNReal ω) := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hfam := fun (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ) => exists_schedVersionsXA_mono h13 c r l' a' hx
  choose Rn Vn hverN _ _ hcovN using hfam
  have hX : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' n : ℕ),
      0 < (RootJ31.sourceSample c r l' a' ω).1 → (rootEntry r.1).2 ≤ RootJ31.historyTime c r l' →
      ∀ q : ℝ≥0, RootJ31.historyTime c r l' ≤ q →
        q < RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') q ω) < Vn l' a' n ω →
        RootJ32.sourceX c r l' a' ω q = (-1) ^ l'.length * (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) *
          (Rn l' a' n (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') q ω).toNNReal ω -
            Rn l' a' n (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (rootEntry r.1).2 ω).toNNReal ω) := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'; rw [ae_all_iff]; intro n
    exact GW2Ru.ae_sourceX_eq_version h13 c r l' a' hx (hverN l' a' n).1.1
  have hP : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ), 0 < (RootJ31.sourceSample c r l' a' ω).1 →
      ((RootJ31.historyTime c r l' + RootJ31.sourceBuffer c r l' a' ω : ℝ≥0) : ℝ≥0∞) <
        contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'
    exact (ae_exactPair_rootX h13 c r l' a').mono fun _ h hl => (h hl).2.1
  have hC : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ),
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → ∀ t : ℝ≥0,
        (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l' a') c.α ω →
        ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') t ω) < Vn l' a' n ω := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'
    exact hcovN l' a'
  have hVA : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' n : ℕ),
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l' a') (schedTr c r l' a') c.α (Rn l' a' n) (Vn l' a' n) ω := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'; rw [ae_all_iff]; intro n
    exact GW2Ru.versionAtX_of_isRelVersionX (hverN l' a' n).1.1
  have hG : ∀ᵐ ω ∂c.P, ∀ (l' : List (EntryIdx c.Θ c.Q)) (a' : ℕ),
      (ω ∈ schedGTX h13 c r l' a' ↔ cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s) := by
    rw [ae_all_iff]; intro l'; rw [ae_all_iff]; intro a'
    exact (schedGTX_spec h13 c r l' a').2.2
  filter_upwards [hX, hP, hC, hVA, hG, GW2Ru.ae_alive_goodEvent h13 c r, GW2Ru.ae_cons_schedW_eq h13 c r,
    GW2Ru.versionAtX_of_isRelVersionX hver] with ω hX hP hC hVA hG hgood hW hR halive hV e l₁ hl
  subst hl
  obtain ⟨hgx, hcon⟩ := hgood _ halive
  obtain ⟨θ₁, q₁⟩ := e
  obtain ⟨halive₁, hx₁⟩ := halive
  obtain ⟨a₁, ha₁⟩ := mem_iUnion.1 hx₁
  obtain ⟨hang₁, htest₁⟩ := mem_iUnion.1 ha₁
  change RootJ31.candidateAngle c r a₁ = θ₁ at hang₁
  subst hang₁
  have hT : RootJ31.historyTime c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) = q₁ :=
    Gm.historyTime_cons c r l₁ _ q₁
  obtain ⟨hTq₁, hqF₁, hlive₁, -⟩ := RootJ32.test_spec c r l₁ a₁ q₁ ω htest₁
  have hord₁ := RootJ32.timeOrdered_historyProgram_of_alive c r l₁ ω halive₁
  have hv₁ := Gm.rootTime_le_historyTime c r l₁ hord₁
  have hq₁0 : (0 : ℝ≥0) < q₁ := lt_of_le_of_lt zero_le hTq₁
  have hv₀q₁ : (rootEntry r.1).2 ≤ (q₁ : ℝ≥0) := hv₁.trans hTq₁.le
  have hW₁ : ∀ t ≤ (q₁ : ℝ≥0), schedW c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) a t ω =
      schedW c r l₁ a₁ t ω := hW l₁ a₁ q₁ a halive₁ htest₁
  have hq₁c : ((q₁ : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) a) c.α ω := hT ▸ hcon a
  have hq₁c₁ : ((q₁ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l₁ a₁) c.α ω :=
    (ENNReal.coe_le_coe.2 hqF₁.le).trans_lt (hP l₁ a₁ hlive₁)
  obtain ⟨hGT, -, -⟩ := schedGTX_spec h13 c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) a
  obtain ⟨hGT₁, -, -⟩ := schedGTX_spec h13 c r l₁ a₁
  have hωG := (hG ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) a).2 hgx
  have hωG₁ := (hG l₁ a₁).2 hgx
  have hs := pos_of_physGoodX (hGT ω hωG)
  obtain ⟨n₁, hn₁⟩ := (hC l₁ a₁ hgx q₁ hq₁c₁).exists
  set cl : ℝ≥0 → ℝ := fun t =>
    clockX (rootPt r.1) c.s c.W c.ζ (schedW c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) a) t ω with hcl
  have hcl₁ : ∀ t ≤ (q₁ : ℝ≥0), clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l₁ a₁) t ω = cl t := fun t ht =>
    (GW2Sdo.clockX_congr fun u hu => hW₁ u (hu.trans ht)).symm
  obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hωG
  have hcl0 : ∀ t, 0 ≤ cl t := fun t => RootJ32.forwardCapacity_nonneg _ _ _ _
  have hv0c : (((rootEntry r.1).2 : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r ((RootJ31.candidateAngle c r a₁, q₁) :: l₁) a) c.α ω :=
    (ENNReal.coe_le_coe.2 hv₀q₁).trans_lt hq₁c
  have hv₀₁ : (cl (rootEntry r.1).2).toNNReal ≤ (cl q₁).toNNReal :=
    Real.toNNReal_le_toNNReal ((ENNReal.ofReal_le_ofReal_iff (hcl0 q₁)).1 (hmono hv0c hq₁c hv₀q₁))
  have hVq₁ : ENNReal.ofReal (cl q₁) < V ω := by rw [← hT]; exact hV
  have hRR₁ := GW2Ru.version_eq_of_drv_eq hGT hGT₁ hs hx hωG hωG₁ (hR hgx) (hVA l₁ a₁ n₁ hgx) hq₁0 hq₁c hq₁c₁ hW₁ hVq₁
    hn₁
  have hX₁ := hX l₁ a₁ n₁ hlive₁ hv₁ q₁ hTq₁.le hqF₁ hn₁
  rw [hcl₁ q₁ le_rfl, hcl₁ _ hv₀q₁, ← hRR₁ _ le_rfl, ← hRR₁ _ hv₀₁] at hX₁
  have hband : RootJ32.sourceX c r l₁ a₁ ω q₁ ∈ Ioo (7 / 4) (9 / 4) := htest₁.2.2.2
  rw [hX₁] at hband
  rw [hT]
  exact hband.1

end Drift

/-! ### The far junction -/

section Far

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The near dilations are at least `17/35`. -/
theorem le_nearLam (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    (17 / 35 : ℝ≥0) ≤ GW2Sdh.nearLam Ω c r l ω := by
  unfold GW2Sdh.nearLam
  split_ifs
  · rw [div_le_one (by norm_num)]
    norm_num
  · exact le_rfl

/-- **D37's far junction on every alive history of `J32S gapFam`** (decision D43): almost surely, at every alive
history and every good slot of a version `R` of `(l, a)` (the history's clock below the cap), the decoded past of the
stage has the far junction of the lower, rightward structure at the near scale, in the orientation of `l`. -/
theorem ae_farJunction (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞}
    (hver : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (hfin : ∀ ω, V ω ≠ ⊤) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) < V ω →
      FarJunction (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
        (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω)
          (trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V
            (RootJ31.historyProgram c r l) ((entryList l).length + 1) (RootJ31.historyTime c r l) ω)
          ((entryList l).length + 1)) := by
  obtain ⟨hGT, -, hGTae⟩ := schedGTX_spec h13 c r l a
  filter_upwards [ae_root_junctionFun c r l a hx hs hver, ae_drift_sign h13 c r hx l a hver,
    GW2Ru.ae_alive_goodEvent h13 c r, hGTae] with ω hroot hdrift hgood hGTω halive hV
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hgx, hcon⟩ := hgood l halive32
  have hωG := hGTω.2 hgx
  have hord := RootJ32.timeOrdered_historyProgram_of_alive c r l ω halive32
  have hv₀T : (rootEntry r.1).2 ≤ RootJ31.historyTime c r l := Gm.rootTime_le_historyTime c r l hord
  obtain ⟨-, hmono, -⟩ := clockX_props hGT hs hx hωG
  have hv0c : (((rootEntry r.1).2 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω :=
    (ENNReal.coe_le_coe.2 hv₀T).trans_lt (hcon a)
  have hv0V : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (rootEntry r.1).2 ω) < V ω :=
    (hmono hv0c (hcon a) hv₀T).trans_lt hV
  set b := trueBdX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) V
    (RootJ31.historyProgram c r l) ((entryList l).length + 1) (RootJ31.historyTime c r l) ω with hbdef
  -- the boundaries
  have hb0 : b 0 = 0 := by
    rw [hbdef]
    unfold trueBdX
    rw [ite_eq_left rfl]
  have hbN : b ((entryList l).length + 1) =
      (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω).toNNReal := by
    rw [hbdef]
    unfold trueBdX
    rw [ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (lt_irrefl _),
      GW2Sdo.stgStartX_eq_clockX hGT hs hx hωG (hcon a) hV]
  have hb1 : b 1 = (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (rootEntry r.1).2 ω).toNNReal := by
    rw [hbdef]
    unfold trueBdX
    rw [ite_eq_right one_ne_zero]
    by_cases h1 : 1 < (entryList l).length + 1
    · rw [ite_eq_left h1, Gm.schedTime_succ_eq_getElem (by rw [GW2Ru.length_historyProgram]; omega)]
      exact GW2Sdo.stgStartX_eq_clockX hGT hs hx hωG hv0c hv0V
    · rw [ite_eq_right h1]
      have hl0 : l = [] := by
        have h0 : (entryList l).length = 0 := by omega
        simpa [entryList] using h0
      have hT0 : RootJ31.historyTime c r l = (rootEntry r.1).2 := by
        rw [hl0]
        exact GW2Ru.historyTime_nil c r
      rw [GW2Sdo.stgStartX_eq_clockX hGT hs hx hωG (hcon a) hV, hT0]
  have hbord := trueBdX_mono_sched h13 c r l a hx hs (hfin ω) hord
  -- the root junctions
  have e0 : RootJ31.historyTime c (r.1, 0) [] = (rootEntry r.1).2 := GW2Ru.historyTime_nil c (r.1, 0)
  have hroot' := hroot halive hV
  rw [e0] at hroot'
  obtain ⟨hJL, hJR⟩ := three_sqrt_lt_of_junctionFun (le_nearLam c r l ω) hroot'
  have hp : (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b 1).2 =
      recOf (((clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (rootEntry r.1).2 ω).toNNReal : ℝ≥0) : ℝ≥0∞)
        (fun u => R u ω, ⊤) := by
    rw [pastOf_one_snd _ (hver.2.2.1 ω) hb0, hb1]
  set sq := 3 * Real.sqrt (GW2Sdh.nearRootScale r.2 (GW2Sdh.nearLam Ω c r l ω)) with hsq
  have hR1 : sq ≤ junctionR 1 (pastFirst (entryList l).length
      (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b ((entryList l).length + 1))) := by
    rw [pastFirst_pastOf_one]
    change sq ≤ markPos (rdrv (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b 1).2)
      (rtime (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b 1).2) 0
    rw [hp]
    exact hJR.le
  have hL1 : sq ≤ -junctionL 1 (pastFirst (entryList l).length
      (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b ((entryList l).length + 1))) := by
    rw [pastFirst_pastOf_one]
    change sq ≤ -markPosL (rdrv (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b 1).2)
      (rtime (GW2Wm.pastOf (cfRec c.s c.W c.ζ ω) (fun u => R u ω) b 1).2) 0
    rw [hp]
    exact hJL.le
  -- the drift after the root piece
  have hd := pastDrift_pastOf (cfRec c.s c.W c.ζ ω) (hver.2.1 ω) b (entryList l).length hbord
  rw [hbN, hb1] at hd
  have hfj := far_junction_of_drift (entryList l).length _ (b := 0) hR1 hL1
  rw [add_zero, neg_zero] at hfj
  have hk : (0 : ℝ) < (((2 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ) := by positivity
  by_cases hl : l = []
  · have hT0 : RootJ31.historyTime c r l = (rootEntry r.1).2 := by
      rw [hl]
      exact GW2Ru.historyTime_nil c r
    rw [hT0, sub_self] at hd
    exact ⟨fun _ => hfj.1 hd.le, fun _ => hfj.2 hd.ge⟩
  obtain ⟨e, l₁, hl'⟩ := List.exists_cons_of_ne_nil hl
  have hsgn := hdrift halive32 hV e l₁ hl'
  rw [← hd] at hsgn
  have hlen : l.length = l₁.length + 1 := by rw [hl', List.length_cons]
  refine ⟨fun hf => hfj.1 ?_, fun hf => hfj.2 ?_⟩
  · rw [hlen, GW2Sdf.flipOf, decide_eq_false_iff_not, Nat.odd_add_one, not_not] at hf
    rw [hf.neg_one_pow] at hsgn
    nlinarith
  · rw [hlen, GW2Sdf.flipOf, decide_eq_true_iff, Nat.odd_add_one, Nat.not_odd_iff_even] at hf
    rw [hf.neg_one_pow] at hsgn
    nlinarith

end Far

end InteractingSLE.Theorem14.GW2Rd
