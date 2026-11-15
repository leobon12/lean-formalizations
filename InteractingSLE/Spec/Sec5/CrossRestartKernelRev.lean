/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelChart
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssemblyMean

/-!
# The reversed-slit data of the counterflow restart

Packet PROVE-CFRESTART. `CrossRestartKernelChart` identifies the counterflow restart chart with the reversed-slit
chart `revChart Ũ σ̃` of Proposition 4.9's cross-conditioning chain (PROVE-GLUECOND3–10). This file collects, from the
restart data of PROVE-SEC5-G/H (`IsRestartAlive`: the counterflow hull `K′` in its chart `M_q` stays in `ℍ` and the
closures of `K^U_σ` and of `M_q⁻¹(K′) ∪ {E(z₀)}` are disjoint), **all the hull hypotheses of the reversed-slit
lemmas** with the roles of Lemma 4.7's direction — new curve = the counterflow `(Wc, t)`, obstacle = `R(K^Ũ_{σ̃})` —
in one structure `IsRevData`:

* the obstacle `R(K^Ũ_{σ̃}) = M_q(K^U_σ)` is closed, and the closures of `K^Ũ_{σ̃}` and of `K′` meet `ℝ` only at `0`;
* `K′` misses the obstacle, and the closures are disjoint in both orders (`hdis` of
  `Aux8Inf.exists_loewner_revChart_image` and of `GlueImg.tendsto_imgTheta_of_ultrafilter`);
* the restart chart is `c · revChart Ũ σ̃` (`c > 0`).

**`exists_isRevData`** produces it; **`IsRevData.exists_image`** is Aux. 8 for the counterflow hull in the
reversed-slit chart (the image Loewner chain of the counterflow in the restart chart, up to the dilation `c`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H fwdHull fwdMap)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Sec5.CrossRestart

open WangWu hiding ratPt exists_ratPt_dist_lt
open ConformalImage ConformalImageFull

/-- **The reversed-slit data of the counterflow restart**: the flow-line segment `K^U_σ` (chart `E`), the counterflow
hull `K′ = K^{Wc}_t` (chart `M_q`), the transformed segment hull `K^Ũ_{σ̃} = cfMob(K^U_σ)` and the dilation `c`, with
every hull hypothesis of the reversed-slit lemmas for the new curve `Wc` and the obstacle `R(K^Ũ_{σ̃})`. -/
structure IsRevData (q : ℝ) (U : ℝ → ℝ) (σ x₁ : ℝ) (Wc : ℝ → ℝ) (t : ℝ) (Ũ : ℝ → ℝ) (σ' c : ℝ) : Prop where
  drv_cont : Continuous Ũ
  drv_zero : Ũ 0 = 0
  time_nonneg : 0 ≤ σ'
  c_pos : 0 < c
  hull_eq : fwdHull Ũ σ' = cfMob q '' fwdHull U σ
  chart_eq : ∀ ξ ∈ H, realMobius 0 (-(1 + q)) 1 1 ξ ∉ fwdHull U σ →
    restartMap q U σ x₁ ξ = (c : ℂ) * revChart Ũ σ' ξ
  real_obst : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Ũ σ')
  real_new : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wc t)
  obst_closed : IsClosed (negInv '' fwdHull Ũ σ')
  disj : Disjoint (fwdHull Wc t) (negInv '' fwdHull Ũ σ')
  dis_new : Disjoint (closure (fwdHull Wc t)) (closure (negInv '' fwdHull Ũ σ'))
  dis_obst : Disjoint (closure (fwdHull Ũ σ')) (closure (negInv '' fwdHull Wc t))

variable {q : ℝ} {U : ℝ → ℝ} {σ x₁ : ℝ} {Wc : ℝ → ℝ} {t : ℝ}

/-- **The reversed-slit data exist** for a flow-line segment hull `K^U_σ` whose closure meets `ℝ` only at the seed
and a counterflow hull `K^{Wc}_t` whose closure meets `ℝ` only at its start, when the closures of `K^U_σ` and of
`M_q⁻¹(K^{Wc}_t) ∪ {E(z₀)}` are disjoint (`IsRestartAlive.far₂`), with `x₁ = g_σ(−1 − q)`. -/
theorem exists_isRevData (hq : 0 < q) (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
    (hK0 : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull U σ)) (hx₁ : (x₁ : ℂ) = bdryVal U (-1 - q) σ)
    (hWc : Continuous Wc) (ht : 0 ≤ t)
    (hK'0 : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wc t))
    (hfar : Disjoint (closure (fwdHull U σ))
      (insert ((-1 - q : ℝ) : ℂ) (closure (realMobius 0 (-(1 + q)) 1 1 '' fwdHull Wc t)))) :
    ∃ (Ũ : ℝ → ℝ) (σ' c : ℝ), IsRevData q U σ x₁ Wc t Ũ σ' c := by
  have hpole : ((-1 - q : ℝ) : ℂ) ∉ closure (fwdHull U σ) := fun h =>
    Set.disjoint_left.1 hfar h (mem_insert _ _)
  obtain ⟨r, hr, hrd⟩ := Metric.mem_nhds_iff.1 (isOpen_compl_iff.2 isClosed_closure |>.mem_nhds hpole)
  have hball : Disjoint (ball ((-1 - q : ℝ) : ℂ) r) (fwdHull U σ) :=
    Set.disjoint_left.2 fun z hz hzK => hrd hz (subset_closure hzK)
  obtain ⟨Ũ, σ', c, hŨc, hŨ0, hσ', hc, hK, hchart⟩ := exists_revChart_restartMap hq hU hU0 hσ hr hball hx₁
  have hobst0 : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Ũ σ') := by
    rw [hK]
    exact ofReal_notMem_closure_cfMob_image hq (InteractingSLE.isBounded_fwdHull hU σ) hpole hK0
  have hHH := isHPHull_fwdHull hŨc hσ'
  have hclosed : IsClosed (negInv '' fwdHull Ũ σ') :=
    GlueCond.isClosed_image_negInv_of_closure hHH.1 hHH.2.1 (CrossCond.Word49.closure_inter_H_subset_fwdHull hŨc hσ')
      hobst0
  have hm1 : (-1 : ℂ) ∉ closure (fwdHull Wc t) := by
    have := hK'0 (-1) (by norm_num)
    simpa using this
  have hdis_new : Disjoint (closure (fwdHull Wc t)) (closure (negInv '' fwdHull Ũ σ')) :=
    disjoint_closure_cfHull_negInv hq hK (isHPHull_fwdHull hU hσ).1 hm1
      (hfar.mono_right (subset_insert _ _))
  have hdisj : Disjoint (fwdHull Wc t) (negInv '' fwdHull Ũ σ') :=
    hdis_new.mono subset_closure subset_closure
  exact ⟨Ũ, σ', c, ⟨hŨc, hŨ0, hσ', hc, hK, hchart, hobst0, hK'0, hclosed, hdisj, hdis_new,
    CrossCond.Word49.disjoint_closure_fwdHull_negInv hWc ht hK'0 hŨc hσ' hdisj⟩⟩

namespace IsRevData

variable {Ũ : ℝ → ℝ} {σ' c : ℝ}

/-- **Aux. 8 for the counterflow hull in the reversed-slit chart**: the images `revChart Ũ σ̃ (K^{Wc}_r)`, `r ≤ t`,
are the Loewner hulls of a continuous driver `W''` (`W'' 0 = 0`) at the half-capacity clock `τ`, continuous and
strictly increasing with `τ 0 = 0` (the image chain of the counterflow in the restart chart, up to the dilation `c`). -/
theorem exists_image (hd : IsRevData q U σ x₁ Wc t Ũ σ' c) (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) (ht : 0 ≤ t) :
    ∃ τ W'' : ℝ → ℝ, Continuous W'' ∧ W'' 0 = 0 ∧ τ 0 = 0 ∧ StrictMonoOn τ (Icc 0 t) ∧
      ContinuousOn τ (Icc 0 t) ∧ ∀ r ∈ Icc (0 : ℝ) t,
        τ r = hcapSet (revChart Ũ σ' '' fwdHull Wc r) / 2 ∧ fwdHull W'' (τ r) = revChart Ũ σ' '' fwdHull Wc r :=
  Aux8Inf.exists_loewner_revChart_image hd.drv_cont hd.drv_zero hd.time_nonneg hd.real_obst hWc hWc0 ht hd.dis_new

end IsRevData

end InteractingSLE.Sec5.CrossRestart
