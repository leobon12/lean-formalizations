/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ByFin
import InteractingSLE.Spec.Supplement.GW2NhStmt

/-!
# D75's bad sets are avoided at one sample under the stopped uncapped law (D83)

Packet PROVE-GW2-BUF (round 22; D83). The canonical driver `Wc` now satisfies the stopped uncapped law
`GW2Ni.IsCanonUXS`. Split on "the contact comes first" (every time before the uncapped contact is at most
`T + uncLife`):

* contact first: `IsCanonUXS.isCanonUX_of_le` gives the old form and round 21's `avoid_atS` applies, with the uncapped
  exit before `min (L_u, d_u)`;
* otherwise the death comes before the contact, so the death clock is finite and the exit is before it (`hexitD`,
  `ae_uncExit_lt_death`). A time `t₁ < T + ζ` with `e + S < clock t₁` follows by intermediate values, and
  `avoid_ofT` finishes.

* **`avoid_atS2`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh
  GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})

/-- **The bad sets are avoided at one sample** for large caps and large buffers, under the stopped uncapped law. -/
theorem avoid_atS2 {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (n i : ℕ)
    (hα : IsGeneratingTrace (c.W · ξ) ⊤ (c.α ξ)) (hW : Continuous (c.W · ξ)) (hW0 : c.W 0 ξ = 0) (hζ : c.ζ ξ = ⊤)
    (harc : ∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ξ u‖ < 1)
    (huc : Continuous (GW2Ni.uncW c r l i · ξ)) (hu0 : GW2Ni.uncW c r l i 0 ξ = 0)
    (huγ : IsGeneratingTrace (GW2Ni.uncW c r l i · ξ) ⊤ (GW2Ni.uncTr c r l i ξ))
    {Wc : ℝ≥0 → ℝ} (hcanU : GW2Ni.IsCanonUXS c r l i ξ Wc)
    (hUA : ∀ a : ℕ, RootJ31.candidateAngle c r a = RootJ31.angleEnumeration c r i →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a,
        schedW c r l a t ξ = GW2Ni.uncW c r l i t ξ ∧ schedTr c r l a ξ t = GW2Ni.uncTr c r l i ξ t)
    (hGT : ∀ a, ξ ∈ schedGTX h13 c r l a) (hcov : ξ ∈ RootCv.coverEvent c r) (hold : RootJ31.oldSuccess c r l ξ)
    (hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (href : ∀ a j : ℕ,
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (ver₀ Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l)
          ((ver₀ Ω c r l a).R j) ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ)
    (hver : ∀ a j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver₀ Ω c r l a).V j ξ →
      fwdHull (fun q : ℝ => (ver₀ Ω c r l a).R j q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (hexh : ∀ a : ℕ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      t < RootJ31.historyTime c r l + RootJ31.candidateCap c r a →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ →
      ∀ᶠ k in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < (ver₀ Ω c r l a).V k ξ)
    (hexitC : GW2Ni.IsCanonUX c r l i ξ Wc →
      exitN c r l n (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ,
          stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
        ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
        min (ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (GW2Ni.uncW c r l i · ξ)
          (GW2Ni.uncTr c r l i ξ) (c.α ξ))) (GW2Ni.uncDeathX c r l i ξ))
    (hexitD : GW2Ni.uncDeathX c r l i ξ < ⊤ →
      exitN c r l n (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ,
          stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
        ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
          GW2Ni.uncDeathX c r l i ξ) :
    ∃ Q : ℝ≥0, ∀ q : ℕ, Q ≤ (RootJ31.timeEnumeration c r q : ℝ≥0) →
      ∀ᶠ b in atTop, ξ ∉ ZbS h13 ver₀ ch c r l n i q b := by
  classical
  by_cases hcf' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ →
      (t : ℝ≥0∞) ≤ (RootJ31.historyTime c r l : ℝ≥0∞) + GW2Ni.uncLife c r l i ξ
  · -- the contact comes first: the stopped law is the unstopped one
    have hcanU' := GW2Ni.IsCanonUXS.isCanonUX_of_le c r l i hcanU hcf'
    exact avoid_atS h13 ver₀ ch c r l hx hs ξ n i hα hW hW0 hζ harc huc hu0 huγ hcanU' hUA hGT hcov hold hTc href
      hver hexh (hexitC hcanU')
  -- the death comes before the contact
  simp only [not_forall, not_le] at hcf'
  obtain ⟨t₀, ht₀c, ht₀l⟩ := hcf'
  obtain ⟨hWc, hWc0, hK, -, -⟩ := hcanU
  have hexitD' := hexitD
  set T := RootJ31.historyTime c r l with hT
  set x₀ := rootPt r.1 with hx₀
  set clu : ℝ≥0 → ℝ := fun t => clockX x₀ c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ with hclu
  set S : ℝ≥0 := (clu T).toNNReal with hS
  set y := augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ with hy
  set e := exitN c r l n (y, stgDrv Wc S) with he
  set Tcu := contactX x₀ c.s (GW2Ni.uncTr c r l i) c.α ξ with hTcu
  set du := GW2Ni.uncDeathX c r l i ξ with hdu
  obtain ⟨ha0, hsm, hac⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc huc hu0 huγ
  have hang : ∀ q b : ℕ, RootJ31.candidateAngle c r (Nat.pair i (Nat.pair q b)) = RootJ31.angleEnumeration c r i :=
    fun q b => GW2Sdy.candidateAngle_pair c r i _
  have hcapq : ∀ q b : ℕ, RootJ31.candidateCap c r (Nat.pair i (Nat.pair q b)) =
      (RootJ31.timeEnumeration c r q : ℝ≥0) := fun q b => by
    simp only [RootJ31.candidateCap, Nat.unpair_pair]
  have hT0 : ∀ q : ℕ, T < T + (RootJ31.timeEnumeration c r q : ℝ≥0) := fun q =>
    lt_add_of_pos_right T (c.hQpos _ (RootJ31.timeEnumeration c r q).2)
  have hTcu : (T : ℝ≥0∞) < Tcu := by
    have h := hUA (Nat.pair i (Nat.pair 0 0)) (hang 0 0)
    rw [hcapq] at h
    exact lt_contactX_of_agree (fun u hu => (h u hu).2) (hT0 0) (hTc _)
  have hclT0 : 0 ≤ clu T := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with h | h
    · rw [hclu, ← h]; exact ha0.ge
    · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < Tcu := lt_of_le_of_lt (by exact_mod_cast zero_le) hTcu
      exact le_of_lt (lt_of_eq_of_lt ha0.symm (hsm h0 hTcu h))
  have hSr : (S : ℝ) = clu T := Real.coe_toNNReal _ hclT0
  have hfinl : GW2Ni.uncLife c r l i ξ ≠ ⊤ := by
    intro h
    rw [h, add_top] at ht₀l
    exact not_top_lt ht₀l
  have hcond : GW2Ni.uncLife c r l i ξ ≠ ⊤ ∧
      ((T + (GW2Ni.uncLife c r l i ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < Tcu := by
    refine ⟨hfinl, ?_⟩
    rw [ENNReal.coe_add, ENNReal.coe_toNNReal hfinl]
    exact ht₀l.trans ht₀c
  set lf := (GW2Ni.uncLife c r l i ξ).toNNReal with hlf
  have hdu' : du = ENNReal.ofReal (clu (T + lf)) := by
    rw [hdu]
    unfold GW2Ni.uncDeathX
    exact ite_eq_left hcond
  have he₂ : e + S < du := hexitD' (by rw [hdu']; exact ENNReal.ofReal_lt_top)
  -- a time `t₁ < T + ζ` with `e + S < clock t₁`
  have hfin : e + S ≠ ⊤ := ne_top_of_lt he₂
  rw [hdu'] at he₂
  have hv : (e + S).toReal < clu (T + lf) := (ENNReal.lt_ofReal_iff_toReal_lt hfin).1 he₂
  have hcont : ContinuousOn clu (Icc 0 (T + lf)) := hac.mono fun t ht => lt_of_le_of_lt
    (ENNReal.coe_le_coe.2 ht.2) hcond.2
  set w := ((e + S).toReal + clu (T + lf)) / 2 with hw
  have hSle : (S : ℝ) ≤ (e + S).toReal := by
    rw [ENNReal.toReal_add (ne_top_of_le_ne_top hfin le_self_add) ENNReal.coe_ne_top]
    simp
  have hwmem : w ∈ Icc (clu 0) (clu (T + lf)) := by
    have h0 : clu 0 = 0 := ha0
    have hS0 : (0 : ℝ) ≤ S := S.2
    rw [h0, hw]
    constructor <;> linarith
  obtain ⟨t₁, ht₁, ht₁eq'⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ T + lf) hcont hwmem
  have ht₁eq : clu t₁ = w := ht₁eq'
  have ht₁c : (t₁ : ℝ≥0∞) < Tcu := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht₁.2) hcond.2
  have hTt₁ : T < t₁ := by
    by_contra h
    rw [not_lt] at h
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h', ← hSr] at ht₁eq; rw [hw] at ht₁eq; linarith
    · have h2 : clu t₁ < clu T := hsm ht₁c hTcu h'
      rw [← hSr, ht₁eq, hw] at h2; linarith
  have ht₁l : t₁ < T + lf := by
    rcases eq_or_lt_of_le ht₁.2 with h | h
    · rw [h, hw] at ht₁eq; linarith
    · exact h
  have het₁ : e + S < ENNReal.ofReal (clu t₁) := by
    rw [ht₁eq]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 (by rw [hw]; linarith)
  have ht₁d : ENNReal.ofReal (clu t₁) ≤ du := by
    rw [hdu']
    exact ENNReal.ofReal_le_ofReal (by rw [ht₁eq, hw]; linarith)
  have hlife : ((t₁ - T : ℝ≥0) : ℝ≥0∞) < GW2Ni.uncLife c r l i ξ := by
    rw [← ENNReal.coe_toNNReal hcond.1]
    exact ENNReal.coe_lt_coe.2 ((tsub_lt_iff_left hTt₁.le).2 ht₁l)
  exact avoid_ofT h13 ver₀ ch c r l hx hs ξ n i hα hW hW0 hζ harc huc hu0 huγ hWc hWc0 hK hUA hGT hcov hold hTc href
    hver hexh hTt₁ ht₁c het₁ ht₁d hlife

end InteractingSLE.Theorem14.GW2Bh
