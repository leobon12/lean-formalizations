/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxDth
import InteractingSLE.Spec.Supplement.GW2BwAgree

/-!
# The threshold at the uncapped death, from a capped candidate (one sample)

Packet PROVE-GW2-BUF (round 21; D75). When the uncapped piece of angle `i` dies before the uncapped contact
(`GW2Ni.uncDeathX < ⊤`, at `T + ζ`), take the candidate `a = Nat.pair i (Nat.pair q 0)` whose cap passes `ζ + 1`. Its
explored curve is the uncapped one up to `T + cap`, so its death clock is the uncapped death clock, and below its
caps (which are below the death clock) its versions agree with any canonical driver `Wc` of the uncapped curve
(`agree_below_clock`). So the death threshold of the base family (`DeathThrXStatementS3`, read at the sample) applies
to `Wc` at that candidate.

* **`thr_unc_death`**.
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

/-- **The threshold at the uncapped death** for a canonical driver of the uncapped curve, read at a capped
candidate of the angle. -/
theorem thr_unc_death {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (i : ℕ)
    (hα : IsGeneratingTrace (c.W · ξ) ⊤ (c.α ξ)) (hW : Continuous (c.W · ξ)) (hW0 : c.W 0 ξ = 0) (hζ : c.ζ ξ = ⊤)
    (harc : ∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ξ u‖ < 1)
    (huc : Continuous (GW2Ni.uncW c r l i · ξ)) (hu0 : GW2Ni.uncW c r l i 0 ξ = 0)
    (huγ : IsGeneratingTrace (GW2Ni.uncW c r l i · ξ) ⊤ (GW2Ni.uncTr c r l i ξ))
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ) < GW2Ni.uncDeathX c r l i ξ →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ)
    (hUA : ∀ a : ℕ, RootJ31.candidateAngle c r a = RootJ31.angleEnumeration c r i →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a,
        schedW c r l a t ξ = GW2Ni.uncW c r l i t ξ ∧ schedTr c r l a ξ t = GW2Ni.uncTr c r l i ξ t)
    (hGT : ∀ a, ξ ∈ schedGTX h13 c r l a)
    (hTc : ∀ a, ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hcovξ : ∀ a, ∃ j, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
      (RootJ31.historyTime c r l) ξ) < (ver₀ Ω c r l a).V j ξ)
    (hcaps : ∀ a, 0 < candLife c r l a ξ → ∀ n, (ver₀ Ω c r l a).V n ξ < deathClockX c r l a ξ)
    (hver : ∀ a j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver₀ Ω c r l a).V j ξ →
      fwdHull (fun q : ℝ => (ver₀ Ω c r l a).R j q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (hthr : ∀ a : ℕ, ∀ W' : ℝ≥0 → ℝ, Continuous W' → W' 0 = 0 →
      (0 < candLife c r l a ξ → ∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < (ver₀ Ω c r l a).V n ξ →
        (ver₀ Ω c r l a).R n q ξ = W' q) →
      deathClockX c r l a ξ < ⊤ →
      ∀ j : ℕ, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver₀ Ω c r l a).V j ξ →
        ∃ u : ℝ≥0, ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
            ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) + u = deathClockX c r l a ξ ∧
          GW2Nv.StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver₀ ch Ω c r l a j hx).srecX c r l (rootPt r.1) ξ))
            (stgDrv W' (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
              ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l) ξ)) u)
    (hdL : GW2Ni.uncDeathX c r l i ξ < ⊤) :
    ∃ a j : ℕ, ∃ u : ℝ≥0, RootJ31.candidateAngle c r a = RootJ31.angleEnumeration c r i ∧
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (ver₀ Ω c r l a).V j ξ ∧
      ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) + u =
        GW2Ni.uncDeathX c r l i ξ ∧
      GW2Nv.StageThresholdN c.κ ((ch Ω c r l a).β ((instX h13 ver₀ ch Ω c r l a j hx).srecX c r l (rootPt r.1) ξ))
        (stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal)
        u := by
  classical
  have hcond : GW2Ni.uncLife c r l i ξ ≠ ⊤ ∧ ((RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal :
      ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ := by
    by_contra h
    apply ne_of_lt hdL
    unfold GW2Ni.uncDeathX
    exact ite_eq_right h
  have hdu' : GW2Ni.uncDeathX c r l i ξ = ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i)
      (RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal) ξ) := by
    unfold GW2Ni.uncDeathX
    exact ite_eq_left hcond
  obtain ⟨q, hq⟩ := GW2Ni.exists_capIdx_ge c r ((GW2Ni.uncLife c r l i ξ).toNNReal + 1)
  have hang : RootJ31.candidateAngle c r (Nat.pair i (Nat.pair q 0)) = RootJ31.angleEnumeration c r i :=
    GW2Sdy.candidateAngle_pair c r i _
  have hcapq : RootJ31.candidateCap c r (Nat.pair i (Nat.pair q 0)) = (RootJ31.timeEnumeration c r q : ℝ≥0) := by
    simp only [RootJ31.candidateCap, Nat.unpair_pair]
  have hcapl : RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal <
      RootJ31.historyTime c r l + (RootJ31.timeEnumeration c r q : ℝ≥0) :=
    (add_lt_add_iff_left _).2 (lt_of_lt_of_le (lt_add_one _) hq)
  have hUA' := hUA (Nat.pair i (Nat.pair q 0)) hang
  rw [hcapq] at hUA'
  have hlifea : candLife c r l (Nat.pair i (Nat.pair q 0)) ξ = GW2Ni.uncLife c r l i ξ :=
    GW2Rd.candLife_eq_of_angle c r l (by rw [hang, GW2Ni.candidateAngle_angCand]) ξ
  have hlfc : ((RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal : ℝ≥0) : ℝ≥0∞) <
      contactX (rootPt r.1) c.s (schedTr c r l (Nat.pair i (Nat.pair q 0))) c.α ξ :=
    lt_contactX_of_agree (fun u hu => ((hUA' u hu).2).symm) hcapl hcond.2
  -- the candidate's death clock is the uncapped one
  have hdca : deathClockX c r l (Nat.pair i (Nat.pair q 0)) ξ = GW2Ni.uncDeathX c r l i ξ := by
    have hle : candLife c r l (Nat.pair i (Nat.pair q 0)) ξ ≤
        (RootJ31.candidateCap c r (Nat.pair i (Nat.pair q 0)) : ℝ≥0∞) := by
      rw [hlifea, hcapq, ← ENNReal.coe_toNNReal hcond.1]
      exact ENNReal.coe_le_coe.2 ((le_add_of_nonneg_right zero_le_one).trans hq)
    have hlt : ((RootJ31.historyTime c r l + (candLife c r l (Nat.pair i (Nat.pair q 0)) ξ).toNNReal : ℝ≥0) :
        ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l (Nat.pair i (Nat.pair q 0))) c.α ξ := by
      rw [hlifea]; exact hlfc
    have hdc' : deathClockX c r l (Nat.pair i (Nat.pair q 0)) ξ = ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ
        (schedW c r l (Nat.pair i (Nat.pair q 0)))
        (RootJ31.historyTime c r l + (candLife c r l (Nat.pair i (Nat.pair q 0)) ξ).toNNReal) ξ) := by
      unfold deathClockX
      exact ite_eq_left ⟨hle, hlt⟩
    have hck : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q 0)))
        (RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal) ξ =
        clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i)
          (RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal) ξ :=
      clockX_eq_of_agree fun u hu => (hUA' u (hu.trans hcapl.le)).1
    rw [hdc', hdu', hlifea, hck]
  have hdfin : deathClockX c r l (Nat.pair i (Nat.pair q 0)) ξ < ⊤ := by rw [hdca]; exact hdL
  -- the versions agree with `Wc` below their caps
  obtain ⟨⟨hwc₁, hw0₁, hγ₁⟩, -, -, -, -⟩ :=
    (schedGTX_spec h13 c r l (Nat.pair i (Nat.pair q 0))).1 ξ (hGT _)
  have hagree : 0 < candLife c r l (Nat.pair i (Nat.pair q 0)) ξ → ∀ (n : ℕ) (q' : ℝ≥0),
      (q' : ℝ≥0∞) < (ver₀ Ω c r l (Nat.pair i (Nat.pair q 0))).V n ξ →
      (ver₀ Ω c r l (Nat.pair i (Nat.pair q 0))).R n q' ξ = Wc q' := by
    intro hpos n q' hq'
    have hA := (ver₀ Ω c r l (Nat.pair i (Nat.pair q 0))).isA hx n
    have hVd : (ver₀ Ω c r l (Nat.pair i (Nat.pair q 0))).V n ξ < ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ
        (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l + (GW2Ni.uncLife c r l i ξ).toNNReal) ξ) := by
      rw [← hdu', ← hdca]
      exact hcaps _ hpos n
    exact agree_below_clock c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁ huc hu0 huγ
      (fun u hu => (hUA' u hu).1) (fun u hu => (hUA' u hu).2) (hA.1.1.2.1 ξ) (hA.1.1.2.2.1 ξ) (hver _ n)
      hWc hWc0 hK hcapl hcond.2 hdu'.ge q' (lt_min hq' (hq'.trans hVd))
  -- a version passing the clock, and the threshold
  obtain ⟨j, hj⟩ := hcovξ (Nat.pair i (Nat.pair q 0))
  have hclka : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q 0)))
      (RootJ31.historyTime c r l) ξ =
      clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ :=
    clockX_eq_of_agree fun u hu => (hUA' u (hu.trans le_self_add)).1
  have hSj := GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l (Nat.pair i (Nat.pair q 0))).1 hs hx (hGT _)
    (hTc _) hj
  have hSV : ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.pair i (Nat.pair q 0)))
      (schedGTX h13 c r l (Nat.pair i (Nat.pair q 0))) ((ver₀ Ω c r l (Nat.pair i (Nat.pair q 0))).V j)
      (RootJ31.historyTime c r l) ξ : ℝ≥0) : ℝ≥0∞) < (ver₀ Ω c r l (Nat.pair i (Nat.pair q 0))).V j ξ := by
    rw [hSj]
    exact hj
  obtain ⟨u, hu, hthrN⟩ := hthr _ Wc hWc hWc0 hagree hdfin j hSV
  rw [hSj, hclka, hdca] at hu
  rw [hSj, hclka] at hthrN
  exact ⟨_, j, u, hang, hj, hu, hthrN⟩

end InteractingSLE.Theorem14.GW2Bh
