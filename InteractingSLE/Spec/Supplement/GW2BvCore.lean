/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvReach

/-!
# The near clauses at one kernel sample from a good slot

Packet PROVE-GW2-BUF (round 19; the core of nearImg). Take a kernel sample `ξ` at which:
* the death family's slot `J` behind version `m'` of the final version family is good (round 18's `goodVer`);
* the slot passes the history's clock;
* the slots' prefix records are the reference one;
* the canonical driver of the stage law exists;
* the source-buffer loss does not occur.

Then the final near slot `(l, n, m' + 1, a)` satisfies the three clauses of `VNearImgOn` for a rightward family `f`
whose shape and positions are those decoded from the reference record:
* the near stop is `min (V_J − S, exit)`;
* the exit on version `m' + 1`'s path equals the exit on slot `J`'s, by `good_transfer` (the canonical driver
  agrees with both versions);
* clause (iii) is `reach_of_frame_visit` with ROOTX's driver identification at the slot.

* `lt_of_start_lt`, **`slot_clauses`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4 GW2JDetR11
  GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx GW2Sdy

/-- A stage start below the cap means the physical clock is below the cap. -/
theorem lt_of_start_lt {p V : ℝ≥0∞} (hV : V ≠ ⊤) (h : ((min p V).toNNReal : ℝ≥0∞) < V) : p < V := by
  by_contra hc
  rw [not_lt] at hc
  rw [min_eq_right hc, ENNReal.coe_toNNReal hV] at h
  exact lt_irrefl _ h

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})

/-- **The near clauses of the final near slot at one kernel sample, from a good slot.** -/
theorem slot_clauses {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (n m' a : ℕ) (f : NearCrossingFamily.{u} c.κ)
    (hgood : ξ ∈ goodVer h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hx (exitN c r l) n a
      (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m' + m'))
    (hcf : cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s)
    (hTc : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hGT : ξ ∈ schedGTX h13 c r l a)
    (href : ∀ j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (schedVerXDeathFamily h13 Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((schedVerXDeathFamily h13 Ω c r l a).V j) (RootJ31.historyTime c r l)
          ((schedVerXDeathFamily h13 Ω c r l a).R j) ξ = refPre h13 Ω c r l ξ)
    (hcan : ∃ Wc : ℝ≥0 → ℝ, IsCanonX c r l a (schedVerXDeathFamily h13 Ω c r l a).R
      (schedVerXDeathFamily h13 Ω c r l a).V ξ Wc)
    (hsh : famShapeB f = shapeD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ))
    (hL : ∀ i : Fin f.nL, f.xL i = posLD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ) i)
    (hR : ∀ j : Fin f.nR, f.xR j = posRD c r l (augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ) j)
    (hsrc : ¬ ((GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) <
      ((pkgX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) (pkgKbF h13 h12 K₀) Ω c r).nearVar l n (m' + 1) a).stop ξ))
    (hreachX : ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
      GW2Bf.histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 →
      τ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) →
      τ ≤ (pkgVerF h13 h12 Ω c r l a).V (m' + 1) ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
      2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
        (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx).drvX c (rootPt r.1)
          (t / (4 : ℝ≥0) ^ r.2) ξ)) →
      RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet)
    (hband : GW2Bf.histStart c r l ξ < 2 + 1 / 8 ∧
      (lamL l : ℝ) * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8)
    (hphys : 0 < (RootJ31.sourceSample c r l a ξ).1 →
      physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (RootJ31.historyTime c r l) ξ =
        ((GW2Sdg.rootHistCap c r l a ξ : ℝ≥0) : ℝ≥0∞))
    (hgo : f.goLeft = false) :
    let v := (pkgX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) (pkgKbF h13 h12 K₀) Ω c r).nearVar l n (m' + 1) a
    0 < (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ ∧
      (∀ v' : ℝ≥0, (v' : ℝ≥0∞) = (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ → v' < (n : ℝ≥0) →
        GW2Sdg.imgState f.xL f.xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) v' ∉ nearBuffer f n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * ((lamL l : ℝ≥0) : ℝ≥0∞) ^ 2 * v.stop ξ →
        GW2Sdg.imgState f.xL f.xR (fun s => (-1 : ℝ) ^ l.length *
          ((2 : ℝ) ^ r.2 * (lamL l : ℝ) * v.R (s / ((4 : ℝ≥0) ^ r.2 * lamL l ^ 2)) ξ)) t ∈ nearTarget f →
        RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet := by
  intro v
  set ver₀ := schedVerXDeathFamily h13 Ω c r l a with hver₀
  set J := pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m' + m' with hJ
  set J' := pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (m' + 1) + (m' + 1) with hJ'
  set T := RootJ31.historyTime c r l with hT
  set clk := clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ with hclk
  set S := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (ver₀.V J) T ξ with hS
  set S' := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (ver₀.V J') T ξ with hS'
  have hJJ' : J ≤ J' := Nat.add_le_add (monotone_pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (Nat.le_succ m'))
    (Nat.le_succ m')
  have hVmono : ver₀.V J ξ ≤ ver₀.V J' ξ :=
    (monotone_nat_of_le_succ fun j => ver₀.mono j ξ) hJJ'
  have hfinJ : ver₀.V J ξ ≠ ⊤ := ver₀.fin J ξ
  -- goodness at `J`
  have hg0 : exitN c r l n ((instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a J hx).srecX c r l
      (rootPt r.1) ξ, fun t => (instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a J hx).drvX c
        (rootPt r.1) t ξ) + (S : ℝ≥0∞) < ver₀.V J ξ := hgood
  have hSlt : (S : ℝ≥0∞) < ver₀.V J ξ := lt_of_le_of_lt le_add_self hg0
  -- the slot passes the clock
  have hphysEq := physClockX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc
  have hclkJ : ENNReal.ofReal clk < ver₀.V J ξ := by
    have h := lt_of_start_lt hfinJ hSlt
    rwa [hphysEq] at h
  have hclkJ' : ENNReal.ofReal clk < ver₀.V J' ξ := hclkJ.trans_le hVmono
  -- the common start and record
  have hSeq : S = clk.toNNReal := GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hclkJ
  have hSeq' : S' = clk.toNNReal :=
    GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hclkJ'
  have hSS : S' = S := by rw [hSeq, hSeq']
  have hrecJ : (instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a J hx).srecX c r l (rootPt r.1) ξ =
      augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      (ver₀.V J) T (ver₀.R J)) ξ = _
    simp only [augRec, href J hclkJ]
  have hrecJ' : (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx).srecX c r l (rootPt r.1) ξ =
      augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      (ver₀.V J') T (ver₀.R J')) ξ = _
    simp only [augRec, href J' hclkJ']
  set y := augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ with hy
  -- the versions agree below `V_J`
  obtain ⟨Wc, -, -, hagree, -, -⟩ := hcan
  have hag : ∀ q : ℝ≥0, (q : ℝ≥0∞) < ver₀.V J ξ → ver₀.R J' q ξ = ver₀.R J q ξ := fun q hq => by
    rw [hagree J' q (hq.trans_le hVmono), hagree J q hq]
  -- the exit on version `m' + 1`'s path
  have hE := (exitB_spec Ω c r l n a).1
  have hgood0 : exitB.{u} Ω c r l n a (y, stgDrv (fun q => ver₀.R J q ξ) S) + (S : ℝ≥0∞) < ver₀.V J ξ := by
    have h := hg0
    rw [hrecJ] at h
    exact h
  have hgood' : exitB.{u} Ω c r l n a (y, stgDrv (fun q => ver₀.R J' q ξ) S) < ver₀.V J ξ - (S : ℝ≥0∞) :=
    good_transfer hE hag hgood0
  -- the near stop
  have hv : v = (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx).varX c r l (rootPt r.1)
      ((pkgKbF h13 h12 K₀ Ω c r).nearStop l n (m' + 1) a) :=
    pkgNearVar_eq h13 h12 (psiGoodFam h13 h12) cwSrc exitB K₀ c r ⟨hx, hs⟩ l n (m' + 1) a
  have hstop : v.stop ξ = min (ver₀.V J ξ - (S : ℝ≥0∞))
      (exitB.{u} Ω c r l n a (y, killPath ((fun t => stgDrv (fun q => ver₀.R J' q ξ) S t),
        ver₀.V J' ξ - (S : ℝ≥0∞)))) := by
    have h := pkgF_nearVar_stop h13 h12 K₀ (fun _ _ _ _ _ _ _ _ _ => 0) c r ⟨hx, hs⟩ l 0 n m' a ξ
    change v.stop ξ = _ at h
    have hlow : (lowCapStopX c l (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx)
        (rootPt r.1) ((pkgVerF h13 h12 Ω c r l a).V m') ((pkgVerF h13 h12 Ω c r l a).isA hx m').1.2.choose).stop ξ =
        ver₀.V J ξ - (S' : ℝ≥0∞) := by
      simp only [lowCapStopX, hcf, ↓reduceIte]
      rfl
    have hcapX : (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx).capX c (rootPt r.1) ξ =
        ver₀.V J' ξ - (S : ℝ≥0∞) := by
      change ver₀.V J' ξ - (S' : ℝ≥0∞) = _
      rw [hSS]
    have hdrv : (fun t => (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx).drvX c
        (rootPt r.1) t ξ) = stgDrv (fun q => ver₀.R J' q ξ) S := by
      funext t
      change stgDrv (fun q => ver₀.R J' q ξ) S' t = _
      rw [hSS]
    rw [h, hlow, hrecJ', hcapX, hdrv, hSS]
  have hvR : ∀ t, v.R t ξ = stgDrv (fun q => ver₀.R J' q ξ) S t := fun t => by
    rw [hv]
    change stgDrv (fun q => ver₀.R J' q ξ) S' t = _
    rw [hSS]
  have hwc : Continuous (stgDrv (fun q => ver₀.R J' q ξ) S) :=
    continuous_stgDrv ((ver₀.isA hx J').1.1.2.1 ξ) S
  have hw0 : stgDrv (fun q => ver₀.R J' q ξ) S 0 = 0 := by simp [stgDrv]
  have hLcap : ver₀.V J ξ - (S : ℝ≥0∞) ≤ ver₀.V J' ξ - (S : ℝ≥0∞) := tsub_le_tsub_right hVmono _
  refine vnearClauses_of_good c r l f n v ξ hwc hw0 hvR hLcap hstop hsh hL hR hgood' fun t ht htv htar => ?_
  -- clause (iii)
  have hstopG : v.stop ξ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) := not_lt.1 hsrc
  refine reach_of_frame_visit r l f hgo (stgDrv (fun q => ver₀.R J' q ξ) S) (τ := v.stop ξ)
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
  have hτV : v.stop ξ ≤ (pkgVerF h13 h12 Ω c r l a).V (m' + 1) ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) := by
    rw [← hcap, hstop]
    exact (min_le_left _ _).trans hLcap
  refine hreachX (lamL l) (v.stop ξ) t' (by exact_mod_cast lamL_pos l) hband.1 hband.2 hstopG hτV ht' ?_
  have e : (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a (m' + 1) hx).drvX c (rootPt r.1)
      (t' / (4 : ℝ≥0) ^ r.2) ξ = stgDrv (fun q => ver₀.R J' q ξ) S (t' / (4 : ℝ≥0) ^ r.2) := by
    change stgDrv (fun q => ver₀.R J' q ξ) S' _ = _
    rw [hSS]
  rw [e]
  exact hvis

end InteractingSLE.Theorem14.GW2Bh
