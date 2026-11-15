/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BwUnc

/-!
# On a good slot the exit term is the death slot's exit

Packet PROVE-GW2-BUF (round 20; `hsrc`). At one sample, take a candidate `a` whose death-family slot `J` behind
version `m − 1` of the final version family is good, and let `J'` be version `m`'s slot (`J ≤ J'`). Assume the
slots' records are the reference one. Then the exit on slot `J`'s path plus the start is below `V_J`, and the bad
set's exit term of the slot `(l, n, m, a)` (on version `m`'s killed path) is the exit on slot `J'`'s path whenever
that exit plus the start is below `V_J'`. No stage law is used (the two slots are compared with a canonical driver
by the caller).

* **`exitTerm_eq_of_good`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh
  GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u})

/-- **On a good slot, the exit term is the exit on version `m`'s slot**, when that exit is below its cap. -/
theorem exitTerm_eq_of_good {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s) (ξ : Ω)
    (n m a : ℕ)
    (hgood : ξ ∈ goodVer h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hx (exitN c r l) n a
      (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (m - 1) + (m - 1)))
    (hTc : ((RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (hGT : ξ ∈ schedGTX h13 c r l a)
    (href : ∀ j : ℕ, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ) <
        (schedVerXDeathFamily h13 Ω c r l a).V j ξ →
      stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
          ((schedVerXDeathFamily h13 Ω c r l a).V j) (RootJ31.historyTime c r l)
          ((schedVerXDeathFamily h13 Ω c r l a).R j) ξ = refPre h13 Ω c r l ξ) :
    let J := pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (m - 1) + (m - 1)
    let J' := pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a m + m
    let S := (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ξ).toNNReal
    let y := augRec (stageEncRec c r l) (fun ω => refPre h13 Ω c r l ω) ξ
    exitN c r l n (y, stgDrv (fun q => (schedVerXDeathFamily h13 Ω c r l a).R J q ξ) S) + (S : ℝ≥0∞) <
        (schedVerXDeathFamily h13 Ω c r l a).V J ξ ∧
      (schedVerXDeathFamily h13 Ω c r l a).V J ξ ≤ (schedVerXDeathFamily h13 Ω c r l a).V J' ξ ∧
      (exitN c r l n (y, stgDrv (fun q => (schedVerXDeathFamily h13 Ω c r l a).R J' q ξ) S) + (S : ℝ≥0∞) <
          (schedVerXDeathFamily h13 Ω c r l a).V J' ξ →
        exitTerm h13 h12 c r l hx n m a ξ =
          exitN c r l n (y, stgDrv (fun q => (schedVerXDeathFamily h13 Ω c r l a).R J' q ξ) S)) := by
  intro J J' S y
  set ver₀ := schedVerXDeathFamily h13 Ω c r l a with hver₀
  set T := RootJ31.historyTime c r l with hT
  set clk := clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) T ξ with hclk
  set SJ := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (ver₀.V J) T ξ with hSJ
  set SJ' := stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) (ver₀.V J') T ξ with hSJ'
  have hJJ' : J ≤ J' := Nat.add_le_add (monotone_pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (Nat.sub_le m 1))
    (Nat.sub_le m 1)
  have hVmono : ver₀.V J ξ ≤ ver₀.V J' ξ := (monotone_nat_of_le_succ fun j => ver₀.mono j ξ) hJJ'
  have hg0 : exitN c r l n ((instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a J hx).srecX c r l
      (rootPt r.1) ξ, fun t => (instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a J hx).drvX c
        (rootPt r.1) t ξ) + (SJ : ℝ≥0∞) < ver₀.V J ξ := hgood
  have hSlt : (SJ : ℝ≥0∞) < ver₀.V J ξ := lt_of_le_of_lt le_add_self hg0
  have hphysEq := physClockX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc
  have hclkJ : ENNReal.ofReal clk < ver₀.V J ξ := by
    have h := lt_of_start_lt (ver₀.fin J ξ) hSlt
    rwa [hphysEq] at h
  have hclkJ' : ENNReal.ofReal clk < ver₀.V J' ξ := hclkJ.trans_le hVmono
  have hSeq : SJ = S := GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hclkJ
  have hSeq' : SJ' = S := GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx hGT hTc hclkJ'
  have hrecJ : (instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a J hx).srecX c r l (rootPt r.1) ξ =
      y := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      (ver₀.V J) T (ver₀.R J)) ξ = _
    simp only [augRec]
    exact congrArg (fun p => pairEnc (stageEncRec c r l ξ, p)) (href J hclkJ)
  have hrecJ' : (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).srecX c r l (rootPt r.1) ξ = y := by
    change augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      (ver₀.V J') T (ver₀.R J')) ξ = _
    simp only [augRec]
    exact congrArg (fun p => pairEnc (stageEncRec c r l ξ, p)) (href J' hclkJ')
  have hE := (exitB_spec Ω c r l n a).1
  have h1 : exitB.{u} Ω c r l n a (y, stgDrv (fun q => ver₀.R J q ξ) SJ) + (SJ : ℝ≥0∞) < ver₀.V J ξ := by
    have h := hg0
    rw [hrecJ] at h
    exact h
  have hgoodJ : exitB.{u} Ω c r l n a (y, stgDrv (fun q => ver₀.R J q ξ) S) + (S : ℝ≥0∞) < ver₀.V J ξ := by
    rw [hSeq] at h1
    exact h1
  refine ⟨hgoodJ, hVmono, fun hJ' => ?_⟩
  have hltcap : exitB.{u} Ω c r l n a (y, stgDrv (fun q => ver₀.R J' q ξ) S) < ver₀.V J' ξ - (S : ℝ≥0∞) :=
    lt_tsub_iff_right.2 hJ'
  have hcapX : (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).capX c (rootPt r.1) ξ =
      ver₀.V J' ξ - (S : ℝ≥0∞) := by
    change ver₀.V J' ξ - (SJ' : ℝ≥0∞) = _
    rw [hSeq']
  have hdrv : (fun t => (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).drvX c (rootPt r.1) t ξ) =
      stgDrv (fun q => ver₀.R J' q ξ) S := by
    funext t
    change stgDrv (fun q => ver₀.R J' q ξ) SJ' t = _
    rw [hSeq']
  have e1 : exitTerm h13 h12 c r l hx n m a ξ = exitB.{u} Ω c r l n a (y, killPath
      (stgDrv (fun q => ver₀.R J' q ξ) S, ver₀.V J' ξ - (S : ℝ≥0∞))) := by
    show exitB.{u} Ω c r l n a ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).srecX c r l
      (rootPt r.1) ξ, killPath ((fun t => (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).drvX c
        (rootPt r.1) t ξ), (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).capX c
        (rootPt r.1) ξ)) = _
    rw [hrecJ', hcapX, hdrv]
  rw [e1, rule_killPath_eq hE y (stgDrv (fun q => ver₀.R J' q ξ) S, ver₀.V J' ξ - (S : ℝ≥0∞)) hltcap]
  rfl

end InteractingSLE.Theorem14.GW2Bh
