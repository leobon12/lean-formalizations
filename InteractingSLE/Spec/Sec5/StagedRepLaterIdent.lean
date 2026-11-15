/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterRoot

/-!
# Prop 5.9's root stage: the candidate observable as an explicit scaled killed word

Packet PROVE-STAGED-REP2. On a good pair `γ = (field, history)` (`gamGood`), the observable `gamObs` of PIECES' root
candidate is the start `(0, λ x)` with `λ = rootLam` and the samples of the killed word of the image curve
`g = Ψ ∘ (code path)` **scaled by `λ`** (`gamObs_eq`, through `TreeData.pieceSamp_cand_zero` and the Loewner scaling of
`StagedRepLaterScale`). PIECES' own root candidate has the same explicit form at good samples
(`rootObs_eq_gamObs`), and so has the dilated glued image word (`StagedRepLaterLaw`).

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Sec4 GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces StagedKCand StagedKill
open WangWu.ImgWord

section Gam

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')

/-- The scaled samples of a killed word: `t ↦ λ (W, V)(t/λ²)`, lifetime `λ² × life`. -/
def scSamp {nL nR : ℕ} (lam : ℝ) (g : ℝ → ℂ) (Pc : Set ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Samp nL nR :=
  samp (fun u => lam * kW g Pc (tf lam * u)) (fun i u => lam * kVL g Pc xL i (tf lam * u))
    (fun k u => lam * kVR g Pc xR k (tf lam * u)) ((show ℝ≥0∞ from kLife g Pc) / (tf lam : ℝ≥0∞))

/-- **The samples of a dilated killed word** are the scaled samples. -/
theorem samp_kW_smul {nL nR : ℕ} {g : ℝ → ℂ} {Pc : Set ℝ} (hg : IsKilledArc g Pc) {lam : ℝ} (hlam : 0 < lam)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    samp (kW (fun v => (lam : ℂ) * g v) Pc) (fun i => kVL (fun v => (lam : ℂ) * g v) Pc (fun i => lam * xL i) i)
      (fun k => kVR (fun v => (lam : ℂ) * g v) Pc (fun k => lam * xR k) k)
      (kLife (fun v => (lam : ℂ) * g v) Pc) = scSamp lam g Pc xL xR := by
  have hW : kW (fun v => (lam : ℂ) * g v) Pc = fun u => lam * kW g Pc (tf lam * u) := funext (kW_smul hg hlam)
  have hL : (fun i => kVL (fun v => (lam : ℂ) * g v) Pc (fun i => lam * xL i) i) =
      fun i u => lam * kVL g Pc xL i (tf lam * u) := funext fun i => funext (kVL_smul hg hlam xL i)
  have hR : (fun k => kVR (fun v => (lam : ℂ) * g v) Pc (fun k => lam * xR k) k) =
      fun k u => lam * kVR g Pc xR k (tf lam * u) := funext fun k => funext (kVR_smul hg hlam xR k)
  have hζ := kLife_smul hg hlam
  rw [hW, hL, hR, scSamp]
  exact congrArg _ hζ

/-- The code path of the stage-0 candidate on `Gam`. -/
abbrev gamPath (γ : Gam) : ℝ → ℂ := qPath h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) Prod.fst 0 Fin.elim0 γ

/-- **The root observable on a good pair** is the start `(0, λ x)` and the scaled samples of the killed word of the
image curve. -/
theorem gamObs_eq (r : ℝ≥0) {γ : Gam} (hγ : γ ∈ gamGood h44 hκ hκ4 (x₀ := x₀) hb) :
    gamObs h44 hκ hκ4 (x₀ := x₀) hb r γ = (((0 : ℝ), fun i => rootLam r γ.2 * rootXL hκ hb x₀ r γ.2 i,
      fun j => rootLam r γ.2 * rootXR hκ hb x₀ r γ.2 j),
      scSamp (rootLam r γ.2) (imgCurve (cfDrv0 r γ.2) r (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ))
        (preContact (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ) (cfHullQ r γ.2)) (rootXL hκ hb x₀ r γ.2)
        (rootXR hκ hb x₀ r γ.2)) := by
  set D := gamData h44 hκ hκ4 (x₀ := x₀) hb r with hD
  have hReg := isReg_gamData h44 hκ hκ4 (x₀ := x₀) hb r
  have hv : D.valid 0 Fin.elim0 := isValid_zero _
  have hGc : γ ∈ D.Gc 0 Fin.elim0 := ⟨hv, hγ⟩
  have hgood := hReg.good_Gc 0 Fin.elim0 γ hGc
  have hcf : CfGood r γ.2 := hgood.1
  have hα : IsProperArc (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ) := hgood.2
  have hg : IsKilledArc (imgCurve (cfDrv0 r γ.2) r (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ))
      (preContact (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ) (cfHullQ r γ.2)) := by
    rw [hcf.2]
    exact isKilledArc_imgCurve (continuous_cfDrv0 r γ.2) (cfDrv0_zero r γ.2) r.coe_nonneg hcf.1 hα
  have himg : D.img 0 Fin.elim0 γ = fun u => (rootLam r γ.2 : ℂ) *
      imgCurve (cfDrv0 r γ.2) r (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ) u := tImg_of_mem hGc
  have hpre : D.pre 0 Fin.elim0 γ = preContact (gamPath h44 hκ hκ4 (x₀ := x₀) hb γ) (cfHullQ r γ.2) :=
    tPre_of_mem hGc
  have hS := TreeData.pieceSamp_cand_zero D Fin.elim0 ((hReg.isKilledFamily 0 Fin.elim0).arc γ) hγ hv
  have hxL : D.xL0 γ = fun i => rootLam r γ.2 * rootXL hκ hb x₀ r γ.2 i := rfl
  have hxR : D.xR0 γ = fun j => rootLam r γ.2 * rootXR hκ hb x₀ r γ.2 j := rfl
  rw [himg, hpre, hxL, hxR] at hS
  have hlam := rootLam_pos r γ.2
  rw [samp_kW_smul hg hlam] at hS
  simp only [gamObs]
  rw [hS]
  rfl

end Gam

end InteractingSLE.Sec5.CrossCond.StagedRepLater
