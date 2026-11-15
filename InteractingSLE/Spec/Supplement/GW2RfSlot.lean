/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvCore
import InteractingSLE.Spec.Supplement.GW2RlNear

/-!
# The near clauses at one kernel sample from a good slot, for any base family (D77 (4), for BUF)

PROVE-GW2-ROOTX round 16 (D77 item 4: the piece BUF names under "For ROOTX" in its round 21). BUF's round-19
`GW2Bh.slot_clauses` (`GW2BvCore`) re-stated for a base family `ver₀`, any re-indexing `ψ` (the family read is
ROOTX's `GW2Rl.verU ver₀ ψ`), any choice family `ch` and BUF's exits `exitB`:

* the stage-law hypothesis `hcan` is replaced by the version agreement `hag` (its only use was `R_J' = R_J` below
  `V_J`);
* the near-stop identity is the unfolding of `nearStopPkgX` through `GW2Rl.pkgX_nearVar_eq`;
* otherwise round 19's proof verbatim (`schedVerXDeathFamily h13 ↦ ver₀`, `pkgCh … ↦ ch`, `pkgVerF ↦ verU ver₀ ψ`,
  `pkgKbF ↦ nearStopPkgX … exitB K₀`, `pkgPsi … + m' ↦ psiAll ver₀ ψ … + m'`, `refPre ↦ GW2Rl.refPreV h13 ver₀`).

* **`slot_clausesU`** — the statement exactly as BUF consumes it (its handoff, round 21, "For ROOTX (D77)").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rf

open GW2Bh Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4
  GW2JDetR11 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx GW2Sdy

/-- **The near clauses of the near slot `(l, n, m' + 1, a)` of the package on `GW2Rl.verU ver₀ ψ` at one kernel
sample, from a good slot** (BUF's `slot_clauses` for any base family, re-indexing and choice family). -/
theorem slot_clausesU (h13 : Exist.Theorem13Statement.{u}) (ver₀ : SchedVerXFamily.{u}) (ψ : GW2Bh.PsiFam.{u})
    (ch : SchedChoiceFamily.{u}) (K₀ : PkgFamily.{u}) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1)
    (hs : 0 < c.s) (ξ : Ω) (n m' a : ℕ) (f : NearCrossingFamily.{u} c.κ)
    (hgood : ξ ∈ goodVer h13 (ver₀) (ch) c r l hx (exitN c r l) n a
      (GW2Rl.psiAll ver₀ ψ Ω c r l a m' + m'))
    (hcf : cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s)
    (hTc : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hGT : ξ ∈ schedGTX h13 c r l a)
    (href : ∀ j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (ver₀ Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((ver₀ Ω c r l a).V j) (RootJ31.historyTime c r l)
          ((ver₀ Ω c r l a).R j) ξ = GW2Rl.refPreV h13 ver₀ Ω c r l ξ)
    (hag : ∀ (j j' : ℕ) (q : ℝ≥0), j ≤ j' → (q : ℝ≥0∞) < (ver₀ Ω c r l a).V j ξ →
      (ver₀ Ω c r l a).R j' q ξ = (ver₀ Ω c r l a).R j q ξ)
    (hsh : famShapeB f = shapeD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ))
    (hL : ∀ i : Fin f.nL,
      f.xL i = posLD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) i)
    (hR : ∀ j : Fin f.nR,
      f.xR j = posRD c r l (augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ) j)
    (hsrc : ¬ ((GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) <
      ((pkgX h13 (GW2Rl.verU ver₀ ψ) (ch) (nearStopPkgX h13 (GW2Rl.verU ver₀ ψ) ch exitB K₀) Ω c r).nearVar l n
        (m' + 1) a).stop ξ))
    (hreachX : ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
      GW2Bf.histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 →
      τ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) →
      τ ≤ (GW2Rl.verU ver₀ ψ Ω c r l a).V (m' + 1) ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
      2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
        (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx).drvX c (rootPt r.1)
          (t / (4 : ℝ≥0) ^ r.2) ξ)) →
      RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet)
    (hband : GW2Bf.histStart c r l ξ < 2 + 1 / 8 ∧
      (lamL l : ℝ) * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8)
    (hphys : 0 < (RootJ31.sourceSample c r l a ξ).1 →
      physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (RootJ31.historyTime c r l) ξ =
        ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞))
    (hgo : f.goLeft = false) :
    let v := (pkgX h13 (GW2Rl.verU ver₀ ψ) (ch) (nearStopPkgX h13 (GW2Rl.verU ver₀ ψ) ch exitB K₀) Ω c r).nearVar l
      n (m' + 1) a
    0 < (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ ∧
      (∀ v' : ℝ≥0, (v' : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ → v' < (n : ℝ≥0) →
        GW2Sdg.imgState f.xL f.xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) v' ∉ nearBuffer f n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ →
        GW2Sdg.imgState f.xL f.xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) t ∈ nearTarget f →
        RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet := by
  intro v
  set V0 := ver₀ Ω c r l a with hV0
  set J := GW2Rl.psiAll ver₀ ψ Ω c r l a m' + m' with hJ
  set J' := GW2Rl.psiAll ver₀ ψ Ω c r l a (m' + 1) + (m' + 1) with hJ'
  set T := RootJ31.historyTime c r l with hT
  set clk := clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ with hclk
  set S := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (V0.V J) T ξ with hS
  set S' := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (V0.V J') T ξ with hS'
  have hJJ' : J ≤ J' := Nat.add_le_add (GW2Rl.monotone_psiAll ver₀ ψ Ω c r l a (Nat.le_succ m'))
    (Nat.le_succ m')
  have hVmono : V0.V J ξ ≤ V0.V J' ξ :=
    (monotone_nat_of_le_succ fun j => V0.mono j ξ) hJJ'
  have hfinJ : V0.V J ξ ≠ ⊤ := V0.fin J ξ
  -- goodness at `J`
  have hg0 : exitN c r l n ((instX h13 (ver₀) (ch) Ω c r l a J hx).srecX c r l
      (rootPt r.1) ξ, fun t => (instX h13 (ver₀) (ch) Ω c r l a J hx).drvX c
        (rootPt r.1) t ξ) + (S : ℝ≥0∞) < V0.V J ξ := hgood
  have hSlt : (S : ℝ≥0∞) < V0.V J ξ := lt_of_le_of_lt le_add_self hg0
  -- the slot passes the clock
  have hphysEq := physClockX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc
  have hclkJ : ENNReal.ofReal clk < V0.V J ξ := by
    have h := lt_of_start_lt hfinJ hSlt
    rwa [hphysEq] at h
  have hclkJ' : ENNReal.ofReal clk < V0.V J' ξ := hclkJ.trans_le hVmono
  -- the common start and record
  have hSeq : S = clk.toNNReal := GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hclkJ
  have hSeq' : S' = clk.toNNReal :=
    GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hclkJ'
  have hSS : S' = S := by rw [hSeq, hSeq']
  have hrecJ : (instX h13 (ver₀) (ch) Ω c r l a J hx).srecX c r l (rootPt r.1) ξ =
      augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      (V0.V J) T (V0.R J)) ξ = _
    simp only [augRec, href J hclkJ]
  have hrecJ' : (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx).srecX c r l (rootPt r.1) ξ =
      augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      (V0.V J') T (V0.R J')) ξ = _
    simp only [augRec, href J' hclkJ']
  set y := augRec (stageEncRec c r l) (fun ω => GW2Rl.refPreV h13 ver₀ Ω c r l ω) ξ with hy
  -- the versions agree below `V_J`
  have hag' : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V0.V J ξ → V0.R J' q ξ = V0.R J q ξ := fun q hq => hag J J' q hJJ' hq
  -- the exit on version `m' + 1`'s path
  have hE := (exitB_spec Ω c r l n a).1
  have hgood0 : exitB.{u} Ω c r l n a (y, stgDrv (fun q => V0.R J q ξ) S) + (S : ℝ≥0∞) < V0.V J ξ := by
    have h := hg0
    rw [hrecJ] at h
    exact h
  have hgood' : exitB.{u} Ω c r l n a (y, stgDrv (fun q => V0.R J' q ξ) S) < V0.V J ξ - (S : ℝ≥0∞) :=
    good_transfer hE hag' hgood0
  -- the near stop
  have hv : v = (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx).varX c r l (rootPt r.1)
      ((nearStopPkgX h13 (GW2Rl.verU ver₀ ψ) ch exitB K₀ Ω c r).nearStop l n (m' + 1) a) :=
    GW2Rl.pkgX_nearVar_eq (h13 := h13) (nearStopPkgX h13 (GW2Rl.verU ver₀ ψ) ch exitB K₀) c r ⟨hx, hs⟩ l n (m' + 1) a
  have hstop : v.stop ξ = min (V0.V J ξ - (S : ℝ≥0∞))
      (exitB.{u} Ω c r l n a (y, killPath ((fun t => stgDrv (fun q => V0.R J' q ξ) S t),
        V0.V J' ξ - (S : ℝ≥0∞)))) := by
    have hg : GoodRoot c r := ⟨hx, hs⟩
    have h : v.stop ξ = min ((lowCapStopX c l (instX h13 (GW2Rl.verU ver₀ ψ) ch Ω c r l a (m' + 1) hx) (rootPt r.1)
          ((GW2Rl.verU ver₀ ψ Ω c r l a).V m') ((GW2Rl.verU ver₀ ψ Ω c r l a).isA hx m').1.2.choose).stop ξ)
        (exitB.{u} Ω c r l n a
          ((instX h13 (GW2Rl.verU ver₀ ψ) ch Ω c r l a (m' + 1) hx).srecX c r l (rootPt r.1) ξ,
            killPath ((fun t => (instX h13 (GW2Rl.verU ver₀ ψ) ch Ω c r l a (m' + 1) hx).drvX c (rootPt r.1) t ξ),
              (instX h13 (GW2Rl.verU ver₀ ψ) ch Ω c r l a (m' + 1) hx).capX c (rootPt r.1) ξ))) := by
      rw [hv]
      change ((nearStopPkgX h13 (GW2Rl.verU ver₀ ψ) ch exitB K₀ Ω c r).nearStop l n (m' + 1) a).stop ξ = _
      simp only [nearStopPkgX, hg, ↓reduceDIte, Nat.add_sub_cancel]
      rfl
    have hlow : (lowCapStopX c l (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx)
        (rootPt r.1) ((GW2Rl.verU ver₀ ψ Ω c r l a).V m') ((GW2Rl.verU ver₀ ψ Ω c r l a).isA hx m').1.2.choose).stop ξ =
        V0.V J ξ - (S' : ℝ≥0∞) := by
      simp only [lowCapStopX, hcf, ↓reduceIte]
      rfl
    have hcapX : (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx).capX c (rootPt r.1) ξ =
        V0.V J' ξ - (S : ℝ≥0∞) := by
      change V0.V J' ξ - (S' : ℝ≥0∞) = _
      rw [hSS]
    have hdrv : (fun t => (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx).drvX c
        (rootPt r.1) t ξ) = stgDrv (fun q => V0.R J' q ξ) S := by
      funext t
      change stgDrv (fun q => V0.R J' q ξ) S' t = _
      rw [hSS]
    rw [h, hlow, hrecJ', hcapX, hdrv, hSS]
  have hvR : ∀ t, v.R t ξ = stgDrv (fun q => V0.R J' q ξ) S t := fun t => by
    rw [hv]
    change stgDrv (fun q => V0.R J' q ξ) S' t = _
    rw [hSS]
  have hwc : Continuous (stgDrv (fun q => V0.R J' q ξ) S) :=
    continuous_stgDrv ((V0.isA hx J').1.1.2.1 ξ) S
  have hw0 : stgDrv (fun q => V0.R J' q ξ) S 0 = 0 := by simp [stgDrv]
  have hLcap : V0.V J ξ - (S : ℝ≥0∞) ≤ V0.V J' ξ - (S : ℝ≥0∞) := tsub_le_tsub_right hVmono _
  refine vnearClauses_of_good c r l f n v ξ hwc hw0 hvR hLcap hstop hsh hL hR hgood' fun t ht htv htar => ?_
  -- clause (iii)
  have hstopG : v.stop ξ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) := not_lt.1 hsrc
  refine reach_of_frame_visit r l f hgo (stgDrv (fun q => V0.R J' q ξ) S) (τ := v.stop ξ)
    (fun t' ht' hvis => ?_) t htv htar
  -- the sample is live, so the stage start is the history's capacity
  have hpos : 0 < v.stop ξ := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, mul_zero] at ht'
    exact (ENNReal.not_lt_zero ht').elim
  have hgain : 0 < (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) := hpos.trans_le hstopG
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 := by
    have h1 := GW2Bf.j32Sample_fst c r l a ξ
    rw [RootJ32.sourceSample_fst] at h1
    rw [h1]
    exact ENNReal.mul_pos (pow_ne_zero _ (by norm_num)) hgain.ne'
  have hcap : (S : ℝ≥0∞) = ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞) := by
    rw [← hphys hlive, hphysEq, hSeq]
    rfl
  have hτV : v.stop ξ ≤ (GW2Rl.verU ver₀ ψ Ω c r l a).V (m' + 1) ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
    rw [← hcap, hstop]
    exact (min_le_left _ _).trans hLcap
  refine hreachX (lamL l) (v.stop ξ) t' (by exact_mod_cast lamL_pos l) hband.1 hband.2 hstopG hτV ht' ?_
  have e : (instX h13 (GW2Rl.verU ver₀ ψ) (ch) Ω c r l a (m' + 1) hx).drvX c (rootPt r.1)
      (t' / (4 : ℝ≥0) ^ r.2) ξ = stgDrv (fun q => V0.R J' q ξ) S (t' / (4 : ℝ≥0) ^ r.2) := by
    change stgDrv (fun q => V0.R J' q ξ) S' _ = _
    rw [hSS]
  rw [e]
  exact hvis

end InteractingSLE.Theorem14.GW2Rf
