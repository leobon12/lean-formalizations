/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdBasic
import InteractingSLE.Spec.Sec7.PocketWordAssembly

/-!
# The counterflow reaches new wall points only through the pocket

Packet PROVE-WALL-ORDER, the pocket-side half of target (3). Specification Aux. lemma 37 (p. 197: "for every interval
`[a, b] ⊂ [τ, σ)` on which `η'([a, b]) ∩ C = ∅`, the two functions `u_i` are constant") and supplement §5.4 ("Progress
of that attachment would identify its flow germ with a new counterflow germ"): the attachment of a wall moves only
while the counterflow visits the pocket. Read pathwise with the reverse first-visit order of the wall:

* **`exists_mem_pocket_before_firstVisit`**: if a wall point `α(v)` is visited for the first time at `t₁ ∈ (τ, σ)`,
  then on every interval `[a, t₁]`, `τ ≤ a < t₁`, the counterflow visits the pocket `C`;
* **`mem_closure_pocket_visits`**: hence `α(v)` is a limit of pocket points `η(t) ∈ C` with `t ↑ t₁` (the wall point
  is reached from the pocket side);
* `mem_closure_pocket_visits_cfgR`, `…_cfgL`: both walls of a bounded reverse-contained pocket.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.WallOrd

open PocketJordan

variable {η : ℝ → ℂ} {C : Set ℂ} {α : ℝ → ℂ} {τ σ : ℝ}

/-- **A newly visited wall point is preceded by pocket visits**: with the attachment of `α` constant on every interval
of `[τ, σ)` avoiding `C` (Aux. lemma 37) and `α` visited in reverse first-visit order from its end `α 1` (visited by
time `a`), a first visit of `α(v)` at `t₁ ∈ (a, σ)` forces a visit of `C` during `[a, t₁]`. -/
theorem exists_mem_pocket_before_firstVisit (hη : ContinuousOn η (Ici 0)) (hαc : ContinuousOn α (Icc 0 1))
    (hconst : ∀ a b : ℝ, τ ≤ a → a ≤ b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
      Sec6.firstVisit (fun t => η '' Icc 0 t) α b = Sec6.firstVisit (fun t => η '' Icc 0 t) α a)
    (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t) {v t₁ a : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (ht₁ : η t₁ = α v) (hfresh : α v ∉ η '' Ico 0 t₁) (hτa : τ ≤ a) (ha0 : 0 ≤ a) (ha : a < t₁) (ht₁σ : t₁ < σ)
    (h1 : α 1 ∈ η '' Icc 0 a) : ∃ t ∈ Icc a t₁, η t ∈ C := by
  by_contra hno
  push Not at hno
  have hc := hconst a t₁ hτa ha.le ht₁σ fun t ht => hno t ht
  -- the visited parameters at time `a`: closed, nonempty, upward closed, and missing `v`
  set V := {w ∈ Icc (0 : ℝ) 1 | α w ∈ η '' Icc 0 a} with hV
  have hVne : V.Nonempty := ⟨1, ⟨zero_le_one, le_rfl⟩, h1⟩
  have hVb : BddBelow V := ⟨0, fun w hw => hw.1.1⟩
  have hKc : IsClosed (η '' Icc 0 a) :=
    (isCompact_Icc.image_of_continuousOn (hη.mono fun t ht => ht.1)).isClosed
  have hVc : IsClosed V := hαc.preimage_isClosed_of_isClosed isClosed_Icc hKc
  have hvV : v ∉ V := by
    rintro ⟨-, u, hu, hηu⟩
    exact hfresh ⟨u, ⟨hu.1, hu.2.trans_lt ha⟩, hηu⟩
  have hlt : v < sInf V := by
    refine lt_of_le_of_ne (le_csInf hVne fun w hw => ?_) fun he => hvV (he ▸ hVc.csInf_mem hVne hVb)
    by_contra hwv
    exact hvV ⟨hv, hrev a w hw.1 v hv (not_le.1 hwv).le hw.2⟩
  -- at time `t₁` the parameter `v` is visited
  have hle : Sec6.firstVisit (fun t => η '' Icc 0 t) α t₁ ≤ v :=
    csInf_le ⟨0, fun w hw => hw.1.1⟩ ⟨hv, t₁, ⟨ha0.trans ha.le, le_rfl⟩, ht₁⟩
  have : Sec6.firstVisit (fun t => η '' Icc 0 t) α a = sInf V := rfl
  linarith

/-- **A newly visited wall point is reached from the pocket**: it is a limit of pocket points `η(t) ∈ C` with
`t ∈ [a, t₁)`. -/
theorem mem_closure_pocket_visits (hη : ContinuousOn η (Ici 0)) (hαc : ContinuousOn α (Icc 0 1))
    (hconst : ∀ a b : ℝ, τ ≤ a → a ≤ b → b < σ → (∀ t ∈ Icc a b, η t ∉ C) →
      Sec6.firstVisit (fun t => η '' Icc 0 t) α b = Sec6.firstVisit (fun t => η '' Icc 0 t) α a)
    (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t) {v t₁ a : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (hvC : α v ∉ C) (ht₁ : η t₁ = α v) (hfresh : α v ∉ η '' Ico 0 t₁) (hτa : τ ≤ a) (ha0 : 0 ≤ a)
    (ha : a < t₁) (ht₁σ : t₁ < σ) (h1 : α 1 ∈ η '' Icc 0 a) :
    α v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ C}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hct : ContinuousWithinAt η (Ici 0) t₁ := hη t₁ (ha0.trans ha.le)
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hct ε hε
  set a' := max a (t₁ - δ / 2) with ha'
  have ha'1 : a' < t₁ := max_lt ha (by linarith)
  have h1' : α 1 ∈ η '' Icc 0 a' := by
    obtain ⟨u, hu, hηu⟩ := h1
    exact ⟨u, ⟨hu.1, hu.2.trans (le_max_left _ _)⟩, hηu⟩
  obtain ⟨t, ht, htC⟩ := exists_mem_pocket_before_firstVisit hη hαc hconst hrev hv ht₁ hfresh
    (hτa.trans (le_max_left _ _)) (ha0.trans (le_max_left _ _)) ha'1 ht₁σ h1'
  have htt : t ≠ t₁ := fun he => hvC (ht₁ ▸ he ▸ htC)
  have ht0 : (0 : ℝ) ≤ t := ha0.trans ((le_max_left _ _).trans ht.1)
  refine ⟨η t, ⟨t, ⟨⟨(le_max_left _ _).trans ht.1, lt_of_le_of_ne ht.2 htt⟩, htC⟩, rfl⟩, ?_⟩
  have hd : dist t t₁ < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, le_max_right a (t₁ - δ / 2)]
  rw [← ht₁, dist_comm]
  exact hδε ht0 hd

/-! ### Both walls of a bounded reverse-contained pocket -/

section Config

open WangWu PocketCoord PocketWordAssembly

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ}

/-- The pocket-side visits of one wall of a bounded reverse-contained pocket, from its `IsCfPocketConfig` data. -/
theorem mem_closure_pocket_visits_cfgAux (hc : IsCfPocketConfig R L r W η) {α : ℝ → ℂ}
    (hαc : ContinuousOn α (Icc 0 1)) (hα1 : α 1 = cfArcR R L r 1)
    (hαF : ∀ v ∈ Icc (0 : ℝ) 1, α v ∈ frontier (cfPocket R L r))
    (hconst : ∀ a b : ℝ, firstHit η (cfArcR R L r 1) ≤ a → a ≤ b → b < firstHit η (cfArcR R L r 0) →
      (∀ t ∈ Icc a b, η t ∉ cfPocket R L r) →
      Sec6.firstVisit (fun t => η '' Icc 0 t) α b = Sec6.firstVisit (fun t => η '' Icc 0 t) α a)
    (hrev : R16.IsReverseVisitOrder α fun t => η '' Icc 0 t) {v t₁ a : ℝ} (hv : v ∈ Icc (0 : ℝ) 1)
    (ht₁ : η t₁ = α v) (hfresh : α v ∉ η '' Ico 0 t₁) (hτa : firstHit η (cfArcR R L r 1) ≤ a) (ha : a < t₁)
    (ht₁σ : t₁ < firstHit η (cfArcR R L r 0)) :
    α v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ cfPocket R L r}) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded
  have hη0 : η 0 = 0 := hc.trace.1
  obtain ⟨-, hv1, huv, -⟩ := hc.conf.changeCorner_props
  have hy : ∃ t, cfArcR R L r 1 ∈ η '' Icc 0 t := by
    have e : cfArcR R L r 1 = cfPt (toDisc (Lemma71I.realPath R) (rightHi R L r)) := by
      simp only [cfArcR, one_mul, add_sub_cancel]
    rw [e]
    exact wall_visited hη0 hc.conf.right hc.visR ⟨(hc.conf.rightLo_pos h0).trans huv, hv1.2⟩
  obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hc.trace.2.1 hy
  have hCo : IsOpen (cfPocket R L r) := (hc.conf.isCfPocket h0).isOpen
  have hvC : α v ∉ cfPocket R L r := fun h => by
    have := hαF v hv
    rw [hCo.frontier_eq] at this
    exact this.2 h
  refine mem_closure_pocket_visits hc.trace.2.1 hαc hconst hrev hv hvC ht₁ hfresh hτa (hτ0.trans hτa) ha ht₁σ ?_
  rw [hα1]
  exact ⟨_, ⟨hτ0, hτa⟩, hτ⟩

/-- **The right wall of a bounded reverse-contained pocket is reached from the pocket side.** -/
theorem mem_closure_pocket_visits_cfgR (hc : IsCfPocketConfig R L r W η) {v t₁ a : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (ht₁ : η t₁ = cfArcR R L r v) (hfresh : cfArcR R L r v ∉ η '' Ico 0 t₁)
    (hτa : firstHit η (cfArcR R L r 1) ≤ a) (ha : a < t₁) (ht₁σ : t₁ < firstHit η (cfArcR R L r 0)) :
    cfArcR R L r v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ cfPocket R L r}) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded
  have hP := hc.conf.isCfPocket h0
  refine mem_closure_pocket_visits_cfgAux hc hP.cont₁ rfl (fun w hw => ?_)
    (fun a b h1 h2 h3 h4 => (hc.attach a b h1 h2 h3 h4).1)
    (R7StopIn.cfArcR_rev hc.conf h0 hc.trace.1 hc.revR) hv ht₁ hfresh hτa ha ht₁σ
  rw [hP.frontier_eq]
  exact Or.inl ⟨w, hw, rfl⟩

/-- **The left wall of a bounded reverse-contained pocket is reached from the pocket side.** -/
theorem mem_closure_pocket_visits_cfgL (hc : IsCfPocketConfig R L r W η) {v t₁ a : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) (ht₁ : η t₁ = cfArcL R L r v) (hfresh : cfArcL R L r v ∉ η '' Ico 0 t₁)
    (hτa : firstHit η (cfArcR R L r 1) ≤ a) (ha : a < t₁) (ht₁σ : t₁ < firstHit η (cfArcR R L r 0)) :
    cfArcL R L r v ∈ closure (η '' {t | t ∈ Ico a t₁ ∧ η t ∈ cfPocket R L r}) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hc.conf hc.bounded
  have hP := hc.conf.isCfPocket h0
  refine mem_closure_pocket_visits_cfgAux hc hP.cont₂ hP.seed (fun w hw => ?_)
    (fun a b h1 h2 h3 h4 => (hc.attach a b h1 h2 h3 h4).2)
    (R7StopIn.cfArcL_rev hc.conf h0 hc.trace.1 hc.revL) hv ht₁ hfresh hτa ha ht₁σ
  rw [hP.frontier_eq]
  exact Or.inr ⟨w, hw, rfl⟩

end Config

end InteractingSLE.Sec7.WallOrd
