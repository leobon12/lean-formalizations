/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BxPkg
import InteractingSLE.Spec.Supplement.GW2BwAgree

/-!
# A candidate whose cap passes an uncapped clock value past the exit is good from some version on (one sample)

Packet PROVE-GW2-BUF (round 21; D75, the `{¬ ∃ k, goodFrom k}` part of the corrected `kSel` bad set). Let `e` be the
near cell's exit on a canonical driver `Wc` of the uncapped curve of angle `i` (`GW2Ni.IsCanonUX`), and `t₁` a time
after the history, before the uncapped contact and the life, with `e + S < clock t₁ ≤ d_u`. For a candidate `a` of the
angle whose cap passes `t₁`:

* the clock at `t₁` is below `a`'s death clock, so the base family exhausts it (`ExhStopStatement`'s form at the
  sample): eventually `clock t₁ < V_k`;
* below `min (V_k, clock t₁)` the version agrees with `Wc` (`agree_below_clock`), so its exit is `e`
  (`pathRule_stgDrv_eq`), and `e + S < V_k`: version `k` is good.

* **`goodFrom_of_unc`**.
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

/-- **A candidate whose cap passes an uncapped clock value past the exit is good from some version on.** -/
theorem goodFrom_of_unc {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (n i : ℕ)
    (hα : IsGeneratingTrace (c.W · ξ) ⊤ (c.α ξ)) (hW : Continuous (c.W · ξ)) (hW0 : c.W 0 ξ = 0) (hζ : c.ζ ξ = ⊤)
    (harc : ∀ u ∈ Icc 0 c.s, rootPt r.1 * ‖c.α ξ u‖ < 1)
    (huc : Continuous (GW2Ni.uncW c r l i · ξ)) (hu0 : GW2Ni.uncW c r l i 0 ξ = 0)
    (huγ : IsGeneratingTrace (GW2Ni.uncW c r l i · ξ) ⊤ (GW2Ni.uncTr c r l i ξ))
    {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ) < GW2Ni.uncDeathX c r l i ξ →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t ξ)
    (a : ℕ) (hang : RootJ31.candidateAngle c r a = RootJ31.angleEnumeration c r i)
    (hUA : ∀ t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a,
      schedW c r l a t ξ = GW2Ni.uncW c r l i t ξ ∧ schedTr c r l a ξ t = GW2Ni.uncTr c r l i ξ t)
    (hGT : ξ ∈ schedGTX h13 c r l a)
    (hTc : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (href : ∀ j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (ver₀ Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l) ((ver₀ Ω c r l a).R j) ξ =
        GW2Rl.refPreV h13 ver₀ Ω c r l ξ)
    (hver : ∀ j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver₀ Ω c r l a).V j ξ →
      fwdHull (fun q : ℝ => (ver₀ Ω c r l a).R j q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (hexh : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      t < RootJ31.historyTime c r l + RootJ31.candidateCap c r a →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ →
      ∀ᶠ k in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < (ver₀ Ω c r l a).V k ξ)
    {t₁ : ℝ≥0} (hTt₁ : RootJ31.historyTime c r l < t₁)
    (ht₁c : (t₁ : ℝ≥0∞) < contactX (rootPt r.1) c.s (GW2Ni.uncTr c r l i) c.α ξ)
    (ht₁cap : t₁ < RootJ31.historyTime c r l + RootJ31.candidateCap c r a)
    (het₁ : exitN c r l n (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ,
        stgDrv Wc (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal) +
      ((clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) (RootJ31.historyTime c r l) ξ).toNNReal : ℝ≥0∞) <
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ))
    (ht₁d : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ) ≤ GW2Ni.uncDeathX c r l i ξ)
    (hlife : ((t₁ - RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < GW2Ni.uncLife c r l i ξ) :
    ∃ K : ℕ, ξ ∈ goodFrom h13 ver₀ ch c r l hx (exitN c r l) n a K := by
  set T := RootJ31.historyTime c r l with hT
  set y := augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ with hy
  set S := (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) T ξ).toNNReal with hS
  have hE : IsPathRule (exitN c r l n) := (exitB_spec Ω c r l n 0).1
  obtain ⟨⟨hwc₁, hw0₁, hγ₁⟩, -, -, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hGT
  obtain ⟨-, hsma, -⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁
  have ht₁a : (t₁ : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
    lt_contactX_of_agree (fun u hu => ((hUA u hu).2).symm) ht₁cap ht₁c
  have hclk₁ : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t₁ ξ =
      clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ :=
    clockX_eq_of_agree fun u hu => (hUA u (hu.trans ht₁cap.le)).1
  have hclkT : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ =
      clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) T ξ :=
    clockX_eq_of_agree fun u hu => (hUA u (hu.trans le_self_add)).1
  -- the clock at `t₁` is below the death clock
  have hdc : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t₁ ξ) < deathClockX c r l a ξ := by
    unfold deathClockX
    split_ifs with hd
    · have hlifea : candLife c r l a ξ = GW2Ni.uncLife c r l i ξ :=
        GW2Rd.candLife_eq_of_angle c r l (by rw [hang, GW2Ni.candidateAngle_angCand]) ξ
      have hfin : candLife c r l a ξ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hd.1
      have hlt' : t₁ - T < (candLife c r l a ξ).toNNReal := by
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin, hlifea]
        exact hlife
      have hlt : t₁ < T + (candLife c r l a ξ).toNNReal := by
        calc t₁ = T + (t₁ - T) := (add_tsub_cancel_of_le hTt₁.le).symm
          _ < T + (candLife c r l a ξ).toNNReal := (add_lt_add_iff_left T).2 hlt'
      have h0 : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t₁ ξ := RootH29.forwardCapacity_nonneg _ _ _ _
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).2 (hsma ht₁a hd.2 hlt)
    · exact ENNReal.ofReal_lt_top
  -- eventually the versions pass `clock t₁`, and are good
  have hev : ∀ᶠ k in atTop, ξ ∈ goodVer h13 ver₀ ch c r l hx (exitN c r l) n a k := by
    filter_upwards [hexh t₁ ht₁a ht₁cap hdc] with k hk
    have hk' : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ) <
        (ver₀ Ω c r l a).V k ξ := by rw [← hclk₁]; exact hk
    have hTk : ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ) < (ver₀ Ω c r l a).V k ξ := by
      refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hk
      exact (hsma hTc ht₁a hTt₁).le
    have hSk : stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V k) T ξ =
        S := by
      rw [GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hTk, hclkT]
    have hyk : (instX h13 ver₀ ch Ω c r l a k hx).srecX c r l (rootPt r.1) ξ = y := by
      change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a)
        (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V k) T ((ver₀ Ω c r l a).R k)) ξ = _
      simp only [augRec]
      exact congrArg (fun p => pairEnc (stageEncRec c r l ξ, p)) (href k hTk)
    have hA := (ver₀ Ω c r l a).isA hx k
    have hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) < min ((ver₀ Ω c r l a).V k ξ)
        (ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (GW2Ni.uncW c r l i) t₁ ξ)) →
        (ver₀ Ω c r l a).R k u ξ = Wc u :=
      agree_below_clock c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc₁ hw0₁ hγ₁ huc hu0 huγ
        (fun u hu => (hUA u hu).1) (fun u hu => (hUA u hu).2) (hA.1.1.2.1 ξ) (hA.1.1.2.2.1 ξ) (hver k)
        hWc hWc0 hK ht₁cap ht₁c ht₁d
    have hexk : exitN c r l n (y, stgDrv (fun u => (ver₀ Ω c r l a).R k u ξ) S) =
        exitN c r l n (y, stgDrv Wc S) :=
      pathRule_stgDrv_eq hE y hag (lt_min (het₁.trans hk') het₁)
    show exitN c r l n ((instX h13 ver₀ ch Ω c r l a k hx).srecX c r l (rootPt r.1) ξ,
        stgDrv (fun q => (ver₀ Ω c r l a).R k q ξ)
          (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V k) T ξ)) +
      ((stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver₀ Ω c r l a).V k) T ξ :
        ℝ≥0) : ℝ≥0∞) < (ver₀ Ω c r l a).V k ξ
    rw [hyk, hSk, hexk]
    exact het₁.trans hk'
  obtain ⟨K, hK'⟩ := eventually_atTop.1 hev
  refine ⟨K, ?_⟩
  simp only [goodFrom, mem_iInter]
  exact fun j hj => hK' j hj

end InteractingSLE.Theorem14.GW2Bh
