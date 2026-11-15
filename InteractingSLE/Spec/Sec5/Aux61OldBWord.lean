/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Conf2KB
import InteractingSLE.Spec.Restart.RetAux79Zone
import InteractingSLE.Spec.Sec7.Lemma71PTrace
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom
import InteractingSLE.Spec.Supplement.BHMeanReal
import InteractingSLE.Spec.Sec5.Aux61GInstBounds

/-!
# Aux. 61's old boundary, IV: the flowed reference word on the old real boundary (deterministic)

Packet PROVE-AUX61-OLDB. MEAN's (c1), deterministic half: at a real point `x′` of the restart chart whose
`F_q`-boundary value is real (an old real boundary point of the chart domain `ℍ ∖ K_q`), off the two base images and the
images of the word's marks, the time-`0` reference mean read through `F_q` and the coupling mean of the flowed word have
the same limit, so `fibMean0 − canonMean → 0` there.

* **`tendsto_couplingMean_sub_old`** (generic, for a proper-arc Loewner trace): `p = F̄_t(x′)` is a nonzero real point
  off the closed hull with a forward solution ending at `x′` (`Sec7.Lemma71P.exists_isForwardSol_of_notMem`, the base
  points excluded by `GlueImg.extendFrom_real_cases`); `x′ = g_t(p) − W_t` is the real flow of the alive point `p`
  (`Restart.RetAux79.isForwardSol_real_cases`), so the flowed force datum at `x′` is the initial one at `p`
  (`forceBoundaryData_flow_right/left`); the bounded harmonic extensions converge to these values, and the derivative
  term `Im log f_t′ → 0` at `p` (`Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure`).
* **`IsGluedSlit.tendsto_old`**: the glued instance, through the chart path frozen at `q` (a proper arc): the finite
  exceptional set `oldExc`, the old point `p` with `F_q → p`, and `fibMean0 d ∘ F_q − canonMean ∘ F_q → 0` (with
  GLUEINST's `tendsto_meanF_sub_couplingMean_sub_q` for the cutoff and Green parts).

Deterministic; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3 or the post-contact kernel.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)

namespace InteractingSLE.Sec5.Aux61OldB

open WangWu (IsProperArc chartAL chartAR)
open MartChar.RealFlow (rightImg gImg Alive)
open Restart.FlowStopIdentCMI (geomL geomR)
open YuanCorollary13 (extDrive extTrace)

/-! ### The generic comparison -/

section Generic

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- **The old real boundary of a proper-arc chart** (generic): at a real `x′` with real `F_t`-boundary value, off the
two base images and the flowed jump set, the boundary value `p` is a nonzero real point off the closed hull,
`F_t → p`, and the coupling mean of the flowed word minus the initial word's extension, read through `F_t`, tends to
`0`. -/
theorem tendsto_couplingMean_sub_old (hη : IsLoewnerTrace W η) (harc : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 < t) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {u u₀ : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => geomL W t (xL i)) (fun j => geomR W t (xR j)))
      (forceJumpSet (fun i => geomL W t (xL i)) (fun j => geomR W t (xR j))) u)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {x' : ℝ} (hx'H : extendFrom H (fwdMapInv W t) x' ∉ H) (hL : x' ≠ chartAL W t) (hR : x' ≠ chartAR W t)
    (hJ : x' ∉ forceJumpSet (fun i => geomL W t (xL i)) (fun j => geomR W t (xR j))) :
    ∃ p : ℝ, (p : ℂ) ∉ closure (fwdHull W t) ∧ extendFrom H (fwdMapInv W t) x' = (p : ℂ) ∧
      Tendsto (fwdMapInv W t) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ)) ∧
      Tendsto (fun y => couplingMean κ W t u (fwdMapInv W t y) - u₀ (fwdMapInv W t y)) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  set F := extendFrom H (fwdMapInv W t) (x' : ℂ) with hFdef
  have him : F.im = 0 := le_antisymm (not_lt.1 hx'H) (GlueImg.extendFrom_im_nonneg hη hW hW0 ht.le x')
  set p : ℝ := F.re with hpdef
  have hFp : F = (p : ℂ) := Complex.ext (by simp [hpdef]) (by simp [him])
  have hp0 : p ≠ 0 := by
    rcases GlueImg.extendFrom_real_cases hη harc hW hW0 ht him with ⟨-, h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hL
    · exact absurd h hR
    · exact h.ne'
    · exact h.ne
  have hnot : F ∉ η '' Icc 0 t := by
    rintro ⟨s, hs, hηs⟩
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, harc.zero, hFp] at hηs
      exact hp0 (by exact_mod_cast hηs.symm)
    · have h1 := harc.mem_H s hpos
      rw [hηs] at h1
      exact absurd him (ne_of_gt h1)
  obtain ⟨v, hv, hvt, -⟩ := Sec7.Lemma71P.exists_isForwardSol_of_notMem hη hW hW0 ht.le him hnot
  have hpcl : (p : ℂ) ∉ closure (fwdHull W t) := ZhanGT4.A2TipSep.not_mem_closure_fwdHull_of_isForwardSol hW ht.le hv
  have hFt0 : Tendsto (fwdMapInv W t) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ)) := by
    rw [← hFp]
    exact (hη.hasBdryLimits hW hW0 ht.le).tendsto (show (0 : ℝ) ≤ (x' : ℂ).im by simp)
  have hFt : Tendsto (fwdMapInv W t) (𝓝[H] (x' : ℂ)) (𝓝[H] (p : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hFt0, eventually_nhdsWithin_of_forall fun y hy =>
      QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht.le hy⟩
  -- the flowed datum at `x′` is the initial datum at `p`
  have hcase : p ∉ forceJumpSet xL xR ∧
      forceBoundaryData κ ρL ρR (fun i => geomL W t (xL i)) (fun j => geomR W t (xR j)) x' =
        forceBoundaryData κ ρL ρR xL xR p := by
    rcases Restart.RetAux79.isForwardSol_real_cases hW hW0 ht.le hv with ⟨hpos, hal, hvx⟩ | ⟨hneg, hal, hvx⟩
    · replace hal : Alive W p t := hal
      replace hpos : 0 < p := hpos
      have hx' : x' = gImg W p t - W t := by rw [hvt] at hvx; exact_mod_cast hvx
      have hxR' : ∀ j, xR j ≠ p := fun j hj => hJ (Or.inr (Or.inr ⟨j, by
        simp only [geomR, hj, MartChar.RealFlow.rightImg_eq_gImg hW ht.le hal, hx']⟩))
      refine ⟨?_, ?_⟩
      · rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
        · exact hp0 h
        · linarith [hxL i]
        · exact hxR' j hj
      · rw [hx']
        exact Restart.RetAux79.forceBoundaryData_flow_right ρL ρR hW ht.le hpos hal hxR'
    · replace hal : Alive (fun s => -W s) (-p) t := hal
      replace hneg : p < 0 := hneg
      have hx' : x' = -gImg (fun s => -W s) (-p) t - W t := by rw [hvt] at hvx; exact_mod_cast hvx
      have hxL' : ∀ i, xL i ≠ p := fun i hi => hJ (Or.inr (Or.inl ⟨i, by
        simp only [geomL, hi, MartChar.RealFlow.rightImg_eq_gImg (w := fun s => -W s) hW.neg ht.le hal, hx']⟩))
      refine ⟨?_, ?_⟩
      · rintro (h | ⟨i, hi⟩ | ⟨j, hj⟩)
        · exact hp0 h
        · exact hxL' i hi
        · linarith [hxR j]
      · rw [hx']
        have h := Restart.RetAux79.forceBoundaryData_flow_left (κ := κ) (xR := xR) ρL ρR hW ht.le (x := -p)
          (by linarith) hal (fun i h => hxL' i (neg_inj.1 h)) (fun i h => hJ (Or.inr (Or.inl ⟨i, by
            simp only [geomL]; rw [← h, hx']⟩)))
        rw [neg_neg] at h
        exact h
  obtain ⟨hJ₀, hval⟩ := hcase
  refine ⟨p, hpcl, hFp, hFt0, ?_⟩
  have h1 := hu.2.2 x' hJ
  have h2 := (hu₀.2.2 p hJ₀).comp hFt
  have h3 := (Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hW hW0 ht.le hpcl).comp hFt
  have h := (h1.sub (h3.const_mul (chiC κ))).sub h2
  rw [mul_zero, sub_zero, hval, sub_self] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [couplingMean, Function.comp_apply, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht.le hy]

end Generic

/-! ### The glued instance -/

namespace GluedOld

open Aux61Conf2 (IsGluedSlit)

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {w : ℝ → ℝ} {γ : ℝ → ℂ} {Tc t : ℝ}

theorem rightImg_extW (hg : IsGluedSlit Wph η r τ c D w γ Tc t) (x : ℝ) :
    rightImg (extDrive w t) x t = rightImg w x t :=
  Supp8.GB6.rightImg_congr hg.hw hg.tpos.le fun _ hr => YuanCorollary13.extDrive_eq hr.2

theorem rightImg_neg_extW (hg : IsGluedSlit Wph η r τ c D w γ Tc t) (x : ℝ) :
    rightImg (fun s => -extDrive w t s) x t = rightImg (fun s => -w s) x t :=
  Supp8.GB6.rightImg_congr (w' := fun s => -w s) hg.hw.neg hg.tpos.le fun _ hr => by
    simp only [YuanCorollary13.extDrive_eq hr.2]

theorem geomL_extW (hg : IsGluedSlit Wph η r τ c D w γ Tc t) (x : ℝ) : geomL (extDrive w t) t x = geomL w t x := by
  simp only [geomL, rightImg_neg_extW hg, YuanCorollary13.extDrive_eq le_rfl]

theorem geomR_extW (hg : IsGluedSlit Wph η r τ c D w γ Tc t) (x : ℝ) : geomR (extDrive w t) t x = geomR w t x := by
  simp only [geomR, rightImg_extW hg, YuanCorollary13.extDrive_eq le_rfl]

theorem chartAL_extW (hg : IsGluedSlit Wph η r τ c D w γ Tc t) : chartAL (extDrive w t) t = chartAL w t := by
  simp only [chartAL, rightImg_neg_extW hg, YuanCorollary13.extDrive_eq le_rfl]

theorem chartAR_extW (hg : IsGluedSlit Wph η r τ c D w γ Tc t) : chartAR (extDrive w t) t = chartAR w t := by
  simp only [chartAR, rightImg_extW hg, YuanCorollary13.extDrive_eq le_rfl]

end GluedOld

open Aux61Conf2 (IsGluedSlit)
open Aux61Fib (FibCode FibData)
open Aux61Win (IsCutoffOn meanF)
open Restart.FlowStopIdentCMI (CMCut)
open Aux61FibK (canonExt)
open Aux61UnionK (canonMean)
open Aux61GlueK (refMean0 fibMean0)

universe v

variable {Wph : ℝ → ℝ} {η : ℝ → ℂ} {r τ : ℝ} {c : Chart} {D : Set ℂ} {γ : ℝ → ℂ} {Tc : ℝ}

/-- The chart driver of a code, read on `ℝ`. -/
abbrev chartW (s : FibCode) : ℝ → ℝ := fun r : ℝ => FibCode.driver r.toNNReal s

/-- **The old-boundary exceptional set** of the chart word at fibre time `q`: the two base images and the images of the
word's marks (a finite set). -/
def oldExc (d : FibData) (s : FibCode) (q : ℝ≥0) : Set ℝ :=
  insert (chartAL (chartW s) q) (insert (chartAR (chartW s) q)
    (forceJumpSet (fun i => geomL (chartW s) q (flowLineXL d.bR d.JR 0 i))
      (fun j => geomR (chartW s) q (flowLineXR d.bR d.JR 0 j))))

theorem oldExc_finite (d : FibData) (s : FibCode) (q : ℝ≥0) : (oldExc d s q).Finite :=
  (((Set.finite_range _).union (Set.finite_range _)).insert 0).insert _ |>.insert _

/-- **(c1), deterministic half, at a glued sample.** At a real `x′ ∉ oldExc` whose `F_q`-boundary value is real, that
value is a real point `p` off the closed chart hull, `F_q → p`, and `fibMean0 d ∘ F_q − canonMean ∘ F_q → 0`. -/
theorem tendsto_fibMean0_sub_canonMean_old (d : FibData) {s : FibCode} {q : ℝ≥0}
    (hg : IsGluedSlit Wph η r τ c D (chartW s) γ Tc q) {F₀ : CMCut} {N : Set ℂ} (hF : IsCutoffOn F₀ d.q N d.O₀)
    (hKN : closure (fwdHull (chartW s) q) ⊆ N) {x' : ℝ} (hx' : x' ∉ oldExc d s q)
    (hx'H : extendFrom H (fwdMapInv (chartW s) q) x' ∉ H) :
    ∃ p : ℝ, (p : ℂ) ∉ closure (fwdHull (chartW s) q) ∧ Tendsto (fwdMapInv (chartW s) q) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ)) ∧
      Tendsto (fun y => fibMean0 d (fwdMapInv (chartW s) q y) -
        canonMean.{v} d F₀ (ULift.up s) q (fwdMapInv (chartW s) q y)) (𝓝[H] (x' : ℂ)) (𝓝 0) := by
  have hw := hg.hw
  have hw0 := hg.hw0
  have hq := hg.tpos
  have hu : IsBoundedHarmonicExtension
      (forceBoundaryData d.κ (flowLineRhoL d.κ d.bR d.JR 0 0) (flowLineRhoR d.κ d.bR d.JR 0 0)
        (fun i => geomL (extDrive (chartW s) q) q (flowLineXL d.bR d.JR 0 i))
        (fun j => geomR (extDrive (chartW s) q) q (flowLineXR d.bR d.JR 0 j)))
      (forceJumpSet (fun i => geomL (extDrive (chartW s) q) q (flowLineXL d.bR d.JR 0 i))
        (fun j => geomR (extDrive (chartW s) q) q (flowLineXR d.bR d.JR 0 j)))
      (canonExt.{v} d (ULift.up s) q) := by
    simp only [GluedOld.geomL_extW hg, GluedOld.geomR_extW hg]
    exact Aux61UnionK.bhe_canonExt.{v} d (ULift.up s) q
  have hu₀ := Aux61GlueK.refMean0_ext d
  simp only [sub_zero] at hu₀
  have hx'H' : extendFrom H (fwdMapInv (extDrive (chartW s) q) q) x' ∉ H := by rwa [hg.extendFrom_extW]
  have hL : x' ≠ chartAL (extDrive (chartW s) q) q := by
    rw [GluedOld.chartAL_extW hg]; exact fun h => hx' (h ▸ mem_insert _ _)
  have hR : x' ≠ chartAR (extDrive (chartW s) q) q := by
    rw [GluedOld.chartAR_extW hg]; exact fun h => hx' (h ▸ mem_insert_of_mem _ (mem_insert _ _))
  have hJ : x' ∉ forceJumpSet (fun i => geomL (extDrive (chartW s) q) q (flowLineXL d.bR d.JR 0 i))
      (fun j => geomR (extDrive (chartW s) q) q (flowLineXR d.bR d.JR 0 j)) := by
    simp only [GluedOld.geomL_extW hg, GluedOld.geomR_extW hg]
    exact fun h => hx' (mem_insert_of_mem _ (mem_insert_of_mem _ h))
  obtain ⟨p, hpcl, hFp, hFt, hlim⟩ := tendsto_couplingMean_sub_old hg.ext_trace hg.ext_arc hg.continuous_extW
    hg.extW_zero hq (Theorem14.GW3Word.flowLineXL_nonpos d.bR d.JR) (Theorem14.GW3Word.flowLineXR_nonneg d.bR d.JR)
    hu hu₀ hx'H' hL hR hJ
  rw [hg.fwdHull_extW] at hpcl
  rw [hg.extendFrom_extW] at hFp
  have hev : ∀ᶠ y in 𝓝[H] (x' : ℂ), fwdMapInv (extDrive (chartW s) q) q y = fwdMapInv (chartW s) q y :=
    eventually_nhdsWithin_of_forall fun y hy => hg.fwdMapInv_extW hy
  have hFt' : Tendsto (fwdMapInv (chartW s) q) (𝓝[H] (x' : ℂ)) (𝓝 (p : ℂ)) := hFt.congr' hev
  refine ⟨p, hpcl, hFt', ?_⟩
  -- the cutoff and Green parts (GLUEINST)
  have hcont : ContinuousOn (extendFrom H (fwdMapInv (chartW s) q)) Hbar := by
    rw [← hg.extendFrom_extW]
    exact (hg.ext_trace.hasBdryLimits hg.continuous_extW hg.extW_zero hq.le).continuousOn
  have h13 := Aux61GInst.tendsto_meanF_sub_couplingMean_sub_q (κ := d.κ) (v := canonExt.{v} d (ULift.up s) q) hF
    hw hw0 hq.le hKN (Ψ := extendFrom H (fwdMapInv (chartW s) q))
    (fun y hy => WangWu.extendFrom_fwdMapInv_eq hw hw0 hq.le hy) hcont x' (by rw [hFp]; simp)
  have h := hlim.neg.sub h13
  rw [neg_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have e1 : extendFrom H (fwdMapInv (chartW s) q) y = fwdMapInv (chartW s) q y :=
    WangWu.extendFrom_fwdMapInv_eq hw hw0 hq.le hy
  have e2 : couplingMean d.κ (extDrive (chartW s) q) q (canonExt.{v} d (ULift.up s) q)
      (fwdMapInv (extDrive (chartW s) q) q y) =
      couplingMean d.κ (chartW s) q (canonExt.{v} d (ULift.up s) q) (fwdMapInv (chartW s) q y) := by
    rw [hg.fwdMapInv_extW hy]
    exact Markov.couplingMean_congr_of_eqOn (fun _ hr => YuanCorollary13.extDrive_eq hr.2) hq.le le_rfl _ _ _
  rw [e1, hg.fwdMapInv_extW hy, ← hg.fwdMapInv_extW hy, e2, hg.fwdMapInv_extW hy]
  simp only [fibMean0, canonMean]
  rw [show (Ito.rpath fun x => Aux61Fib.fibW x (ULift.up.{v} s)) = chartW s from rfl]
  ring

end InteractingSLE.Sec5.Aux61OldB
