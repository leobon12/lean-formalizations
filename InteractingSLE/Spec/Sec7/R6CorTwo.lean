/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6CorMixed
import InteractingSLE.Spec.Sec7.R6TwoFace
import InteractingSLE.Spec.Sec7.OuterInGeomAe

/-!
# R.6's face for the bounded two-outer shape without Aux. lemma 136 (Astra's inner-side argument)

Packet PROVE-R6-CORNER, second round. One realization: the bounded outer pocket `C = cfPocket R L r` at a live
relative capacity `q > 0` with fibre end `T = T_C(q)`, and the bounded outer pocket `V = cfPocket R M r' ⊆ C` (two
outer arms: the shared wall is `R`, the left wall `M` is the left frontier) holding the tip `η(T)`. With
`q_T = c_V(T)` (the same original time):

* `inter_subset_of_frontier_balls`: a clopen argument on the connected domain `D_C`;
* `outer_visit_facts`: at a strict visit `t` of an outer pocket, `T(c(t)) = t`, `D(c(t)) ⊆ ℍ ∖ K_t` and
  `C ∩ ∂D(c(t)) ⊆ η([0, t])`;
* **`two_identity_at_visit`**: `D_V(c_V(t)) ⊆ D_C(c_C(t))` and `D_C(c_C(t)) ∩ V ⊆ D_V(c_V(t))` at every strict visit
  `t` of `V`, when `M` is visited in reverse order. A point of `D_C(c_C(t))` on `∂V` lies on `V`'s open left arc
  (`R`'s arc and the two corners are off `C`); it is unvisited at `t`, so by reverse visits no later point of `M` is,
  and its coordinate exceeds every real contact of `V`'s trace (the ray lemma): it is alive for `V`. This replaces
  the exposed-point local agreement of Aux. lemma 136;
* `hlater_two`: the common later time for the driver identification (the identity at a later visit `t₂`);
* **`two_face`**: `R6FaceR` for the current charts of `C` at `q` and `V` at every close later `q'`, through
  `R6Cor.r6FaceR_left_of_reflection` (as `corner_face_sharedR`, the seed corner included);
* `ae_rev_ML`: `M_L` is visited in reverse order a.s. (`OuterIn.ae_walls_r7` for `β_L`);
* **`r6FaceSTwoRemaining_of_walls`**: `R6Two.R6FaceSTwoRemaining k rL rR c c'` from Prop. 4.11 and Lemma 4.7 (`h411`,
  `h47`, `h47T`, all proved upstream), `4 < k`, `0 ≤ c`, `0 ≤ c'`.

R43/R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Cor

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe R6Fc
open WangWu (chartAL chartAR)
open SupercriticalConformalCovariance (IsConformalBijection)

/-- **A clopen argument.** If `D` is preconnected, `V` and `Dv ⊆ D` are open, `Dv ≠ ∅`, every point of `D ∩ V` in the
closure of `Dv` lies in `Dv`, and every point of `D` on the frontier of `V` has a ball whose part in `V` lies in `Dv`,
then `D ∩ V ⊆ Dv`. -/
theorem inter_subset_of_frontier_balls {D V Dv : Set ℂ} (hD : IsPreconnected D) (hV : IsOpen V) (hDv : IsOpen Dv)
    (hne : Dv.Nonempty) (hsub : Dv ⊆ D) (hcl : ∀ w ∈ D, w ∈ V → w ∈ closure Dv → w ∈ Dv)
    (hfr : ∀ m ∈ D, m ∈ frontier V → ∃ ρ > 0, V ∩ ball m ρ ⊆ Dv) : D ∩ V ⊆ Dv := by
  set O₁ : Set ℂ := {x | ∃ ρ > 0, V ∩ ball x ρ ⊆ Dv} with hO₁
  have hO₁o : IsOpen O₁ := by
    rw [Metric.isOpen_iff]
    rintro x ⟨ρ, hρ, hx⟩
    refine ⟨ρ / 2, half_pos hρ, fun y hy => ⟨ρ / 2, half_pos hρ, fun z hz => hx ⟨hz.1, ?_⟩⟩⟩
    have h1 := mem_ball.1 hy
    have h2 := mem_ball.1 hz.2
    rw [mem_ball]
    linarith [dist_triangle z y x]
  have hDvO : Dv ⊆ O₁ := fun y hy => by
    obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hDv y hy
    exact ⟨ρ, hρ, fun z hz => hρD hz.2⟩
  have hO₂o : IsOpen (V \ closure Dv) := hV.sdiff isClosed_closure
  have hdisj : Disjoint O₁ (V \ closure Dv) := by
    rw [disjoint_left]
    rintro x ⟨ρ, hρ, hx⟩ ⟨hxV, hxc⟩
    exact hxc (subset_closure (hx ⟨hxV, mem_ball_self hρ⟩))
  have hcover : D ⊆ O₁ ∪ (V \ closure Dv) := by
    intro x hxD
    by_cases hxV : x ∈ V
    · by_cases hxc : x ∈ closure Dv
      · exact Or.inl (hDvO (hcl x hxD hxV hxc))
      · exact Or.inr ⟨hxV, hxc⟩
    · left
      by_cases hxcV : x ∈ closure V
      · exact hfr x hxD ⟨hxcV, by rw [hV.interior_eq]; exact hxV⟩
      · obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl x hxcV
        exact ⟨ρ, hρ, fun z hz => absurd (subset_closure hz.1) (hρV hz.2)⟩
  obtain ⟨y, hy⟩ := hne
  have hDO := hD.subset_left_of_subset_union hO₁o hO₂o hdisj hcover ⟨y, hsub hy, hDvO hy⟩
  rintro x ⟨hxD, hxV⟩
  obtain ⟨ρ, hρ, hx⟩ := hDO hxD
  exact hx ⟨hxV, mem_ball_self hρ⟩

section Visit

variable {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}

/-- **A bounded outer pocket at a strict visit time `t`**: with `c = c_C(t)`, the capacity is positive and live, the
fibre end of `c` is `t`, the current domain at `c` misses the physical hull `K_t`, and its frontier inside `C` lies on
`η([0, t])`. -/
theorem outer_visit_facts (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R ω) (L ω) r) {c : ℝ≥0} (hc : (c : ℝ) = innerRelCap R L r η ψ t ω) :
    0 < c ∧ (c : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧ outerFibreEnd R L r η ψ c ω = t ∧
      ((curChart A R L r η ψ n c ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) t ∧
      cfPocket (R ω) (L ω) r ∩ frontier ((curChart A R L r η ψ n c ω).dom : Set ℂ) ⊆ η ω '' Icc 0 t := by
  have hcf := hcfg ω hω
  have hP := hcf.toPocket (hψ ω hω)
  have hv := hP.erase.mem_visitSet ht0 ht
  obtain ⟨hpos, hlive⟩ := SideVis.erasure_relCap_pos_lt_of_visit hP.erase hP.driven hv
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := hP.driven
  have hcpos : 0 < c := by rw [← NNReal.coe_pos, hc]; exact hpos
  have hclive : (c : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
    rw [← ENNReal.ofReal_coe_nnreal, hc]; exact hlive
  have htI : t ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    ⟨hv.1.1.le, hv.1.2⟩
  have hend : outerFibreEnd R L r η ψ c ω = t := by
    unfold outerFibreEnd
    have h1 : capInv (travAll R L r η ψ ω) c = PocketStopMarked.relTime (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) t := by
      rw [hc]; exact hγ.capInv_eq (PocketStopMarked.Outer.relTime_nonneg hP htI)
    rw [h1, PocketStopMarked.Outer.clockOf_relTime hP htI]
    exact hP.erase.fibre_clock_of_mem hv
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded)
  have hJarc : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1)
      (ψ ω) := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
  refine ⟨hcpos, hclive, hend, fun w hw => ?_, fun w hw => ?_⟩
  · have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAll R L r η ψ ω) s.toNNReal) c) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hclive]; exact hw
    have h : w ∈ H \ fwdHull (W ω) (outerFibreEnd R L r η ψ c ω) :=
      relDomain_subset_domain hcf.erase hcf.trace hcf.continuous_W hcf.W_zero (hCH ω hω) hCb hJarc hγ
        c.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hclive) hzD
    rwa [hend] at h
  · have h : w ∈ η ω '' Icc 0 (outerFibreEnd R L r η ψ c ω) :=
      outer_frontier_subset_trace (n := n) hcfg hψ hω hclive hw
    rwa [hend] at h

end Visit

section Two

variable {Ω : Type*} {A A' : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
  {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}

/-- **The same-time inclusion at a strict visit of a nested outer pocket** `V ⊆ C` (both bounded outer):
`D_V(c_V(t)) ⊆ D_C(c_C(t))`, given one common point. The frontier of `D_C(c_C(t))` inside `C` lies on `η([0, t])`,
which `D_V(c_V(t)) ⊆ ℍ ∖ K_t` misses. -/
theorem two_dom_subset_at_visit {R' L' : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R' ω) (L' ω) r') {c c' : ℝ≥0} (hc : (c : ℝ) = innerRelCap R L r η ψ t ω)
    (hc' : (c' : ℝ) = innerRelCap R' L' r' η ψ' t ω)
    (hmeet : (((curChart A' R' L' r' η ψ' n' c' ω).dom : Set ℂ) ∩ (curChart A R L r η ψ n c ω).dom).Nonempty) :
    ((curChart A' R' L' r' η ψ' n' c' ω).dom : Set ℂ) ⊆ (curChart A R L r η ψ n c ω).dom := by
  obtain ⟨-, hlive', -, hdomV, -⟩ := outer_visit_facts (n := n') hcfg' hψ' hω' ht0 ht hc'
  obtain ⟨-, -, -, -, hfrC⟩ := outer_visit_facts (n := n) hcfg hψ hω ht0 (hsub ht) hc
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ' : IsDrivenCurve (travAll R' L' r' η ψ' ω) := ((hcfg' ω hω').props (hψ' ω hω')).1
  have hI : (curChart A' R' L' r' η ψ' n' c' ω).IsConformal :=
    PocketStopSide.isConformal_relChart_of_driven hγ' hlive' hcI
  refine dom_subset_of_frontier_disjoint hI (disjoint_left.2 fun w hwI hwf => ?_) hmeet
  have hwV : w ∈ cfPocket (R' ω) (L' ω) r' :=
    ((relChart_dom_eq_inter (n := n') hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) hω' hγ' hlive').subset hwI).1
  have hwt := hfrC ⟨hsub hwV, hwf⟩
  have hwK := hdomV hwI
  refine hwK.2 ?_
  rw [(hcfg ω hω).trace.2.2 t ht0]
  exact ⟨hwK.1, Or.inl (subset_closure hwt)⟩

/-- **The identity at a strict visit** (Astra's inner-side argument for two outer arms): for bounded outer pockets
`V = cfPocket R M r' ⊆ C = cfPocket R L r` sharing the right wall `R`, with `M` visited in reverse order and
`D_V(c_V(t)) ⊆ D_C(c_C(t))`, also `D_C(c_C(t)) ∩ V ⊆ D_V(c_V(t))`. A point of `D_C(c_C(t))` on `∂V` is on `V`'s
open left arc (the right arc and corners are on `R`, off `C`); it is unvisited by time `t`, so by reverse visits no
later point of `M` is visited and its coordinate exceeds every real contact of `V`'s trace (ray lemma): it is alive.
-/
theorem two_inter_subset_at_visit {M : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (M ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (M ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (M ω) (η ω))
    (hsub : cfPocket (R ω) (M ω) r' ⊆ cfPocket (R ω) (L ω) r) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R ω) (M ω) r') {c c' : ℝ≥0} (hc : (c : ℝ) = innerRelCap R L r η ψ t ω)
    (hc' : (c' : ℝ) = innerRelCap R M r' η ψ' t ω)
    (hincl : ((curChart A' R M r' η ψ' n' c' ω).dom : Set ℂ) ⊆ (curChart A R L r η ψ n c ω).dom) :
    ((curChart A R L r η ψ n c ω).dom : Set ℂ) ∩ cfPocket (R ω) (M ω) r' ⊆
      (curChart A' R M r' η ψ' n' c' ω).dom := by
  have hcf := hcfg ω hω
  have hcf' := hcfg' ω hω'
  obtain ⟨-, hlive, -, hdomC, -⟩ := outer_visit_facts (n := n) hcfg hψ hω ht0 (hsub ht) hc
  obtain ⟨-, hlive', -, -, hfrV⟩ := outer_visit_facts (n := n') hcfg' hψ' hω' ht0 ht hc'
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (M ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (M ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (M ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hcO, -, -⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  have hγ' : IsDrivenCurve (travAll R M r' η ψ' ω) := (hcf'.props (hψ' ω hω')).1
  have hO : (curChart A R L r η ψ n c ω).IsConformal := PocketStopSide.isConformal_relChart_of_driven hγ hlive hcO
  have hI : (curChart A' R M r' η ψ' n' c' ω).IsConformal :=
    PocketStopSide.isConformal_relChart_of_driven hγ' hlive' hcI
  have hOdom := relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hlive
  have hIdom := relChart_dom_eq_inter (n := n') hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) hω' hγ' hlive'
  have hD : IsPreconnected ((curChart A R L r η ψ n c ω).dom : Set ℂ) := by
    rw [hO.coe_dom]; exact convex_H.isPreconnected.image _ hO.1.continuousOn
  have hne : ((curChart A' R M r' η ψ' n' c' ω).dom : Set ℂ).Nonempty := by
    rw [hI.coe_dom]
    exact ⟨_, Complex.I, show (0 : ℝ) < Complex.I.im by simp, rfl⟩
  have hKt : ∀ w ∈ H, w ∈ η ω '' Icc 0 t → w ∈ fwdHull (W ω) t := fun w hwH hw => by
    rw [hcf.trace.2.2 t ht0]; exact ⟨hwH, Or.inl (subset_closure hw)⟩
  refine inter_subset_of_frontier_balls hD (hCo' ω hω') (curChart A' R M r' η ψ' n' c' ω).dom.isOpen hne hincl ?_ ?_
  · intro w hwD hwV hwcl
    by_contra hwI
    have hwf : w ∈ frontier ((curChart A' R M r' η ψ' n' c' ω).dom : Set ℂ) :=
      ⟨hwcl, by rw [(curChart A' R M r' η ψ' n' c' ω).dom.isOpen.interior_eq]; exact hwI⟩
    have hwK := hdomC hwD
    exact hwK.2 (hKt w hwK.1 (hfrV ⟨hwV, hwf⟩))
  intro m hmD hmfr
  have hmK := hdomC hmD
  have hmC : m ∈ cfPocket (R ω) (L ω) r := (hOdom.subset hmD).1
  have h0V := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf'.conf hcf'.bounded
  obtain ⟨-, hv, huv, -, hb, -, -, -⟩ := hcf'.conf.changeCorner_props
  have hu0 := hcf'.conf.rightLo_pos h0V
  have ha0 := hcf'.conf.leftLo_pos h0V
  have hRnot : ∀ θ ∈ Icc (rightLo (R ω) (M ω) r') (rightHi (R ω) (M ω) r'),
      R6Fd.wallPt (R ω) θ ∉ cfPocket (R ω) (L ω) r :=
    fun θ hθ => R6Fd.wallPt_notMem hcf.conf (Or.inl rfl) ⟨hu0.trans_le hθ.1, hθ.2.trans hv.2⟩
  have hmx : m ≠ cfPt (openPt (R ω) (M ω) r') := fun he => by
    rw [he] at hmC; exact hRnot _ ⟨le_rfl, huv.le⟩ hmC
  have hmcl : m ∈ closure (cfPocket (R ω) (M ω) r') \ {cfPt (openPt (R ω) (M ω) r')} := ⟨hmfr.1, hmx⟩
  have hJ : Sec6.IsJordanCoord (cfPocket (R ω) (M ω) r') (cfPt (openPt (R ω) (M ω) r'))
      (cfPt (closePt (R ω) (M ω) r')) (ψ' ω) := hψ' ω hω'
  have him : (ψ' ω m).im = 0 := hJ.2.2.2.2.1 m ⟨hmfr, hmx⟩
  rcases lt_trichotomy (ψ' ω m).re 0 with hneg | hzero | hpos
  · obtain ⟨θ, hθ, hmθ⟩ := frontier_neg_right_arc hcf'.conf h0V hcf'.oriented (hψ' ω hω') hmfr hmx hneg
    rw [hmθ] at hmC
    exact absurd hmC (hRnot θ ⟨hθ.1.le, hθ.2.le⟩)
  · have hy := ((R6Fd.right_arc_facts hcf'.conf h0V hcf'.oriented (hψ' ω hω')).1 _ ⟨huv, le_rfl⟩)
    have he : ψ' ω m = ψ' ω (R6Fd.wallPt (R ω) (rightHi (R ω) (M ω) r')) := by
      have hy0 : ψ' ω (R6Fd.wallPt (R ω) (rightHi (R ω) (M ω) r')) = 0 := hJ.2.2.2.2.2.1
      apply Complex.ext
      · rw [hzero, hy0, Complex.zero_re]
      · rw [him, hy.2]
    have hme := hJ.2.1 hmcl hy.1 he
    rw [hme] at hmC
    exact absurd hmC (hRnot _ ⟨huv.le, le_rfl⟩)
  obtain ⟨θ, hθ, hmθ⟩ := frontier_pos_left_arc hcf'.conf h0V hcf'.oriented (hψ' ω hω') hmfr hmx hpos
  obtain ⟨-, -, hanti⟩ := R6Fd.left_arc_facts hcf'.conf h0V hcf'.oriented (hψ' ω hω')
  have hP' := hcf'.toPocket (hψ' ω hω')
  have hL' := hP'.erase.clock_σ_pos
  have hv' := hP'.erase.mem_visitSet ht0 ht
  have htI : t ∈ Ico (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) :=
    ⟨hv'.1.1.le, hv'.1.2⟩
  have hrel0 := PocketStopMarked.Outer.relTime_nonneg hP' htI
  have hcapInv : capInv (travAll R M r' η ψ' ω) c' = PocketStopMarked.relTime (η ω) (cfPocket (R ω) (M ω) r')
      (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) t := by
    rw [hc']; exact hγ'.capInv_eq hrel0
  have hx0 : cfArcR (R ω) (M ω) r' 0 = cfPt (openPt (R ω) (M ω) r') := cfArcR_zero_eq _ _ _
  have halive : ψ' ω m ∉ closure (fwdHull (fun s : ℝ => segDriver (travAll R M r' η ψ' ω) s.toNNReal) c') := by
    rw [hγ'.fwdHull_segDriver c'.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hlive')]
    intro hcl
    have hmreal : ψ' ω m = (((ψ' ω m).re : ℝ) : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact him)
    rw [hmreal] at hcl
    have hZc : IsCompact (travAll R M r' η ψ' ω '' Icc 0 (capInv (travAll R M r' η ψ' ω) c')) :=
      isCompact_Icc.image_of_continuousOn (hγ'.continuousOn.mono Icc_subset_Ici_self)
    have hZH : travAll R M r' η ψ' ω '' Icc 0 (capInv (travAll R M r' η ψ' ω) c') ⊆ Hbar := by
      rintro _ ⟨u, hu, rfl⟩
      have h := hP'.erase.erasedPath_mem (clockOf_mem_Ico hL' hu.1)
      exact hJ.2.2.1 ⟨h.1, fun he => h.2 (he.trans hx0.symm)⟩
    obtain ⟨_, ⟨u, hu, rfl⟩, hzim, hzre⟩ := R6Fd.exists_real_ge_of_mem_closure_fillH hZc hZH hcl
    have hpm₀ := hP'.erase.erasedPath_mem (clockOf_mem_Ico hL' hu.1)
    set p := erasedPath (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1))
      (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0))
      (clockOf (pocketClock (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1))
        (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0))) u) with hpdef
    have hpm : p ∈ closure (cfPocket (R ω) (M ω) r') \ {cfPt (openPt (R ω) (M ω) r')} :=
      ⟨hpm₀.1, fun he => hpm₀.2 (he.trans hx0.symm)⟩
    have hψp : travAll R M r' η ψ' ω u = ψ' ω p := rfl
    rw [hψp] at hzim hzre
    have hpV : p ∉ cfPocket (R ω) (M ω) r' := fun h => by
      have h2 : (0 : ℝ) < (ψ' ω p).im := (hψ' ω hω').2.2.2.1.2.mapsTo h
      rw [hzim] at h2; exact lt_irrefl _ h2
    have hpfr : p ∈ frontier (cfPocket (R ω) (M ω) r') :=
      ⟨hpm.1, by rw [(hCo' ω hω').interior_eq]; exact hpV⟩
    obtain ⟨θ', hθ', hpθ⟩ := frontier_pos_left_arc hcf'.conf h0V hcf'.oriented (hψ' ω hω') hpfr hpm.2
      (by linarith)
    have hθθ' : θ' ≤ θ := by
      by_contra hlt
      push Not at hlt
      have h : (ψ' ω (R6Fd.wallPt (M ω) θ')).re < (ψ' ω (R6Fd.wallPt (M ω) θ)).re :=
        hanti ⟨hθ.1, hθ.2.le⟩ ⟨hθ'.1, hθ'.2.le⟩ hlt
      rw [← hpθ, ← hmθ] at h
      linarith
    -- the contact time is at most `t`
    have hu' : clockOf (pocketClock (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1))
        (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0))) u ≤
        pocketClock (η ω) (cfPocket (R ω) (M ω) r') (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1))
          (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) t := by
      rw [← PocketStopMarked.Outer.clockOf_relTime hP' htI]
      exact (strictMonoOn_clockOf hL').monotoneOn hu.1 hrel0 (hcapInv ▸ hu.2)
    have hft := hP'.erase.monotone_fibre hu'
    rw [hP'.erase.fibre_clock_of_mem hv'] at hft
    have hpt : p ∈ η ω '' Icc 0 t :=
      ⟨_, ⟨hP'.erase.nonneg.trans (hP'.erase.fibre_mem _).1, hft⟩, rfl⟩
    have hθ'I : θ' ∈ Ioc (0 : ℝ) 1 := ⟨ha0.trans hθ'.1, hθ'.2.le.trans hb.2⟩
    have hθI : θ ∈ Ioc (0 : ℝ) 1 := ⟨ha0.trans hθ.1, hθ.2.le.trans hb.2⟩
    rw [hpθ] at hpt
    have hmt : m ∈ η ω '' Icc 0 t := by
      rw [hmθ]; exact PocketJordan.wall_rev hcf'.conf.left hcf.trace.1 hrev hθ'I hθI hθθ' hpt
    exact hmK.2 (hKt m hmK.1 hmt)
  obtain ⟨ρ, hρ, hρI⟩ := R6Fc.exists_ball_subset_of_alive hJ hcf'.conf.cfPt_openPt_notMem hmcl halive
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  rw [hIdom]
  exact hρI hz

/-- **The identity at a strict visit, with the common point found near the tip**
(`R6Two.exists_rat_meet_near_tip_two`): both `D_V(c_V(t)) ⊆ D_C(c_C(t))` and `D_C(c_C(t)) ∩ V ⊆ D_V(c_V(t))`. -/
theorem two_identity_at_visit {M : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (M ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (M ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (M ω) (η ω))
    (hsub : cfPocket (R ω) (M ω) r' ⊆ cfPocket (R ω) (L ω) r) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : η ω t ∈ cfPocket (R ω) (M ω) r') {c c' : ℝ≥0} (hc : (c : ℝ) = innerRelCap R L r η ψ t ω)
    (hc' : (c' : ℝ) = innerRelCap R M r' η ψ' t ω) :
    ((curChart A' R M r' η ψ' n' c' ω).dom : Set ℂ) ⊆ (curChart A R L r η ψ n c ω).dom ∧
      ((curChart A R L r η ψ n c ω).dom : Set ℂ) ∩ cfPocket (R ω) (M ω) r' ⊆
        (curChart A' R M r' η ψ' n' c' ω).dom := by
  obtain ⟨-, hlive, hend, -, -⟩ := outer_visit_facts (n := n) hcfg hψ hω ht0 (hsub ht) hc
  obtain ⟨-, -, -, -, -⟩ := outer_visit_facts (n := n') hcfg' hψ' hω' ht0 ht hc'
  have htip : η ω (outerFibreEnd R L r η ψ c ω) ∈ cfPocket (R ω) (M ω) r' := by rw [hend]; exact ht
  obtain ⟨q'', hlo, -, hlive'', -, hmeet, -⟩ := R6Two.exists_rat_meet_near_tip_two (n := n) (n' := n') hcfg hψ hω
    hlive hcfg' hψ' hω' hsub htip one_pos
  rw [hend, ← hc'] at hlo
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (M ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (M ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (M ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  obtain ⟨hcI, -, -⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hγ' : IsDrivenCurve (travAll R M r' η ψ' ω) := ((hcfg' ω hω').props (hψ' ω hω')).1
  have hle : c' ≤ StripSys.rt q'' := by
    rw [← NNReal.coe_le_coe, StripSys.rt, Real.coe_toNNReal _ ((NNReal.coe_nonneg c').trans hlo.le)]
    exact hlo.le
  have hanti := R6Two.relChart_dom_antitone (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R ω) (M ω) r')
    ψ' ω) (n' ω)) hcI hγ' hlive'' hle
  obtain ⟨z, hzV, hzC⟩ := hmeet
  have hincl := two_dom_subset_at_visit (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hsub ht0 ht hc hc'
    ⟨z, hanti hzV, hzC⟩
  exact ⟨hincl, two_inter_subset_at_visit hcfg hψ hcfg' hψ' hω hω' hrev hsub ht0 ht hc hc' hincl⟩

/-- **The common later time (two outer pockets)**: for small `s, s'` a time `t₂` just after `T = T_C(q)` with
`η(t₂) ∈ V` gives an inner capacity `q₂' = c_V(t₂) ∈ (q_T, q_T + s')` and an outer capacity `q₂ ∈ (c_C(t₂), q + s)`;
on `V`, `ψ'(z) ∈ K^V_{q₂'}` means `z ∉ D_V(c_V(t₂))`, hence (the identity at `t₂`) `z ∉ D_C(c_C(t₂)) ⊇ D_C(q₂)`. -/
theorem hlater_two {M : Ω → ℝ≥0 → ℂ}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (M ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (M ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (M ω) (η ω))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsub : cfPocket (R ω) (M ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEnd R L r η ψ q ω)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R ω) (M ω) r')
    {WC WU : ℝ → ℝ} {t₁ t₁' : ℝ≥0} (hqt₁ : q < t₁) (ht₁ : (t₁ : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hqTt₁' : innerRelCap R M r' η ψ' (outerFibreEnd R L r η ψ q ω) ω < t₁')
    (hCdom : ∀ q₂ : ℝ≥0, q₂ < t₁ → ((curChart A R L r η ψ n q₂ ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q₂))
    (hUdom : ∀ q₂ : ℝ≥0, q₂ < t₁' → ((curChart A' R M r' η ψ' n' q₂ ω).dom : Set ℂ) =
      cfPocket (R ω) (M ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU q₂)) :
    ∀ s > 0, ∀ s' > 0, ∃ q₂ q₂' : ℝ, (q : ℝ) ≤ q₂ ∧ q₂ < q + s ∧
      innerRelCap R M r' η ψ' (outerFibreEnd R L r η ψ q ω) ω < q₂' ∧
      q₂' < innerRelCap R M r' η ψ' (outerFibreEnd R L r η ψ q ω) ω + s' ∧
      ∀ z ∈ cfPocket (R ω) (M ω) r', ψ' ω z ∈ fwdHull WU q₂' → ψ ω z ∈ fwdHull WC q₂ := by
  intro s hs s' hs'
  set T := outerFibreEnd R L r η ψ q ω with hTdef
  set qT := innerRelCap R M r' η ψ' T ω with hqTdef
  have hcf := hcfg ω hω
  have hcf' := hcfg' ω hω'
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  have hPo := hcf.toPocket (hψ ω hω)
  have hP'o := hcf'.toPocket (hψ' ω hω')
  have hqlive : ENNReal.ofReal (q : ℝ) < capLife (travAll R L r η ψ ω) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec q.coe_nonneg hqlive
  obtain ⟨hTmem, hTrel⟩ := PocketStopMarked.Outer.relTime_fibre_clockOf hPo hc0
  replace hTmem : T ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    hTmem
  replace hTrel : PocketStopMarked.relTime (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) T = capInv (travAll R L r η ψ ω) q := hTrel
  have hrelT : PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) T = q := by
    unfold PocketStopMarked.relCap
    rw [hTrel]
    exact hcq
  have hvT := hP'o.erase.mem_visitSet hT0 htip
  have hTI : T ∈ Ico (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) :=
    ⟨hvT.1.1.le, hvT.1.2⟩
  set s₁ := min s ((t₁ : ℝ) - q) with hs₁
  have hs₁0 : 0 < s₁ := lt_min hs (sub_pos.2 (by exact_mod_cast hqt₁))
  set s₁' := min s' ((t₁' : ℝ) - qT) with hs₁'
  have hs₁'0 : 0 < s₁' := lt_min hs' (by linarith)
  have hcC := PocketStopMarked.Outer.continuousOn_relCap hPo T hTmem
  have hcU := PocketStopMarked.Outer.continuousOn_relCap hP'o T hTI
  have hσ : T < min (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) :=
    lt_min hTmem.2 hTI.2
  have hmem : ∀ σ₀ τ₀ : ℝ, τ₀ ≤ T → T < σ₀ → Ico τ₀ σ₀ ∈ 𝓝[>] T := fun σ₀ τ₀ h1 h2 =>
    mem_of_superset (Ioo_mem_nhdsGT h2) fun t ht => ⟨h1.trans ht.1.le, ht.2⟩
  have e2 : ∀ᶠ t in 𝓝[>] T, PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t < q + s₁ := by
    have h := (hcC.mono_of_mem_nhdsWithin (hmem _ _ hTmem.1 hTmem.2)).tendsto
    rw [hrelT] at h
    exact h.eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ t in 𝓝[>] T, PocketStopMarked.relCap (η ω) (cfPocket (R ω) (M ω) r')
      (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) (ψ' ω) t <
        qT + s₁' := by
    have h := (hcU.mono_of_mem_nhdsWithin (hmem _ _ hTI.1 hTI.2)).tendsto
    exact h.eventually (gt_mem_nhds (by show qT < qT + s₁'; linarith))
  have e4 : ∀ᶠ t in 𝓝[>] T, η ω t ∈ cfPocket (R ω) (M ω) r' := by
    have h := ((hcf.trace.2.1 T hT0).mono_of_mem_nhdsWithin
      (mem_of_superset self_mem_nhdsWithin fun t ht => le_of_lt (lt_of_le_of_lt hT0 ht))).tendsto
    exact h.eventually (hP'o.erase.isOpen.mem_nhds htip)
  obtain ⟨t₂, ht₂I, ht₂C, ht₂U, ht₂η⟩ :=
    ((show ∀ᶠ t in 𝓝[>] T, t ∈ Ioo T _ from Ioo_mem_nhdsGT hσ).and (e2.and (e3.and e4))).exists
  have ht₂C' : t₂ ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    ⟨hTmem.1.trans ht₂I.1.le, ht₂I.2.trans_le (min_le_left _ _)⟩
  have ht₂U' : t₂ ∈ Ico (firstHit (η ω) (cfArcR (R ω) (M ω) r' 1)) (firstHit (η ω) (cfArcR (R ω) (M ω) r' 0)) :=
    ⟨hTI.1.trans ht₂I.1.le, ht₂I.2.trans_le (min_le_right _ _)⟩
  have ht₂0 : 0 ≤ t₂ := hT0.trans ht₂I.1.le
  set q₂' := innerRelCap R M r' η ψ' t₂ ω with hq₂'def
  have hq₂' : qT < q₂' := R6Two.relCap_outer_lt_of_visit hP'o hvT ht₂U' ht₂I.1
  set c₂ := innerRelCap R L r η ψ t₂ ω with hc₂
  have hc₂q : (q : ℝ) ≤ c₂ := by
    rw [← hrelT]; exact PocketStopMarked.Outer.monotoneOn_relCap hPo hTmem ht₂C' ht₂I.1.le
  have ht₂C'' : c₂ < q + s₁ := ht₂C
  set q₂ := (c₂ + (q + s₁)) / 2 with hq₂def
  have hq₂lo : c₂ < q₂ := by linarith
  have hq₂hi : q₂ < q + s₁ := by linarith
  refine ⟨q₂, q₂', by linarith, hq₂hi.trans_le (by linarith [min_le_left s ((t₁ : ℝ) - q)]), hq₂',
    ht₂U.trans_le (by linarith [min_le_left s' ((t₁' : ℝ) - qT)]), fun z hzU hzK => ?_⟩
  have hqT0' : 0 ≤ qT := (SideVis.erasure_relCap_pos_lt_of_visit hP'o.erase hP'o.driven hvT).1.le
  have hq₂'0 : 0 ≤ q₂' := hqT0'.trans hq₂'.le
  have hc₂0 : 0 ≤ c₂ := (q.coe_nonneg).trans hc₂q
  -- the identity at `t₂`
  obtain ⟨-, hid⟩ := two_identity_at_visit (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub ht₂0 ht₂η
    (c := c₂.toNNReal) (c' := q₂'.toNNReal) (Real.coe_toNNReal _ hc₂0) (Real.coe_toNNReal _ hq₂'0)
  have ht₂U'' : q₂' < qT + s₁' := ht₂U
  have hq₂'t : q₂'.toNNReal < t₁' := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq₂'0]
    linarith [min_le_right s' ((t₁' : ℝ) - qT)]
  by_contra hzC
  have hq₂0 : 0 ≤ q₂ := (q.coe_nonneg).trans (by linarith)
  have hq₂t : q₂.toNNReal < t₁ := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq₂0]
    linarith [min_le_right s ((t₁ : ℝ) - q)]
  have hq₂live : ((q₂.toNNReal : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) :=
    lt_trans (by exact_mod_cast hq₂t) ht₁
  have hzCq : z ∈ ((curChart A R L r η ψ n q₂.toNNReal ω).dom : Set ℂ) := by
    rw [hCdom _ hq₂t, Real.coe_toNNReal _ hq₂0]
    exact ⟨hsub hzU, (hψ ω hω).2.2.2.1.2.mapsTo (hsub hzU), hzC⟩
  obtain ⟨hcO, -, -⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have hle : c₂.toNNReal ≤ q₂.toNNReal := Real.toNNReal_le_toNNReal hq₂lo.le
  have hz2 := R6Two.relChart_dom_antitone (c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r)
    ψ ω) (n ω)) hcO hγ hq₂live hle hzCq
  have hzV := hid ⟨hz2, hzU⟩
  have hzV' : z ∈ ((curChart A' R M r' η ψ' n' q₂'.toNNReal ω).dom : Set ℂ) := hzV
  rw [hUdom _ hq₂'t, Real.coe_toNNReal _ hq₂'0] at hzV'
  exact hzV'.2.2 hzK

/-- The relative capacity of an outer pocket at the fibre end of `q` is `q`. -/
theorem relCap_outerFibreEnd {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) :
    innerRelCap R L r η ψ (outerFibreEnd R L r η ψ q ω) ω = q := by
  have hcf := hcfg ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  have hPo := hcf.toPocket (hψ ω hω)
  have hqlive : ENNReal.ofReal (q : ℝ) < capLife (travAll R L r η ψ ω) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec q.coe_nonneg hqlive
  obtain ⟨-, hTrel⟩ := PocketStopMarked.Outer.relTime_fibre_clockOf hPo hc0
  show PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) (outerFibreEnd R L r η ψ q ω) = q
  unfold PocketStopMarked.relCap
  rw [show PocketStopMarked.relTime (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (outerFibreEnd R L r η ψ q ω) = capInv (travAll R L r η ψ ω) q
    from hTrel]
  exact hcq

/-- **R.6's face for the bounded two-outer shape at every close later inner time** (both pockets bounded and outer,
`V = cfPocket R Lv r' ⊆ C` sharing the right wall `R`, `Lv` visited in reverse order). As `corner_face_sharedR`, with
Astra's inner-side identity `D_C(q) ∩ V = D_V(c_V(T))` (`two_identity_at_visit`) in place of the contained pocket's
`D_U(c_U(T)) = U ∖ K_T`; no Aux. lemma 136 and no exposed-point hypothesis. -/
theorem two_face {A A' : Set Ω} {R L Lv : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (Lv ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (Lv ω) r' (ψ' ω)) (hω : ω ∈ A) (hω' : ω ∈ A')
    (hrev : IsWallReverseVisit (Lv ω) (η ω)) {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsub : cfPocket (R ω) (Lv ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (hT0 : 0 ≤ outerFibreEnd R L r η ψ q ω)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R ω) (Lv ω) r') :
    ∃ εW > 0, ∀ q' : ℝ≥0, innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω < q' →
      (q' : ℝ) < innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω + εW →
      ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) ⊆ (curChart A R L r η ψ n q ω).dom →
      ∀ ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ, vL 0 = seedL R L r η ψ q ω → vR 0 = seedR R L r η ψ q ω →
        wL 0 = seedL R Lv r' η ψ' q' ω → wR 0 = seedR R Lv r' η ψ' q' ω → ρL 0 = σL 0 →
        R6FaceR ρL ρR σL σR vL vR wL wR (curChart A R L r η ψ n q ω) (curChart A' R Lv r' η ψ' n' q' ω)
          (H \ ((curChart A R L r η ψ n q ω).dom : Set ℂ)) (H \ ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ)) := by
  classical
  -- the outer pocket
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have h0C := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) := isBounded_image_negInv h0C
  have hx₀ : cfPt (openPt (R ω) (L ω) r) ∉ cfPocket (R ω) (L ω) r := hcf.conf.cfPt_openPt_notMem
  have hJ : Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
      (cfPt (closePt (R ω) (L ω) r)) (ψ ω) := hψ ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props (hψ ω hω)).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    chart_facts (n := n) hCo hCH hψc hCb hx₀ hJ hω hγ ht₁
  obtain ⟨hOc, hOdom, hOfwd, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAll R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : seedR R L r η ψ q ω = chartAR WC q := seedR_eq hWC hWCq
  have hvL : seedL R L r η ψ q ω = chartAL WC q := seedL_eq hWC hWCq
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hηC hWC hWC0 q.coe_nonneg
  have hTC : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r := hsub htip
  have htrace : capTrace (travAll R L r η ψ ω) q = ψ ω (η ω (outerFibreEnd R L r η ψ q ω)) := rfl
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCeq q q.coe_nonneg (by exact_mod_cast hqt₁'.le)]
    change capTrace (travAll R L r η ψ ω) q ∈ H
    rw [htrace]
    exact (hψc ω hω).2.mapsTo hTC
  have hvR0 : 0 < chartAR WC q := chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  have hvL0 : chartAL WC q < 0 := chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC
  set EO : ℂ → ℂ := fun z => E₀ (extendFrom H (fwdMapInv WC q) z) with hEOdef
  have hOphys : ((curChart A R L r η ψ n q ω).dom : Set ℂ) ⊆ H \ fwdHull (W ω) (outerFibreEnd R L r η ψ q ω) := by
    intro w hwO
    have hJarc : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1)
        (ψ ω) := by
      rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
    have hzD : w ∈ cfPocket (R ω) (L ω) r ∩
        ψ ω ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver (travAll R L r η ψ ω) s.toNNReal) q) := by
      rw [← relChart_dom_eq_inter (n := n) hCo hCH hψc hω hγ hq]; exact hwO
    exact relDomain_subset_domain hcf.erase hcf.trace hcf.continuous_W hcf.W_zero (hCH ω hω) hCb hJarc hγ
      q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) hzD
  -- the inner pocket
  have hcf' := hcfg' ω hω'
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R ω) (Lv ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R ω) (Lv ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R ω) (Lv ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  have hψc' : ∀ ω ∈ A', IsConformalBijection (ψ' ω) (cfPocket (R ω) (Lv ω) r') H := fun ω hω =>
    (hψ' ω hω).2.2.2.1
  have h0U := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf'.conf hcf'.bounded
  have hUb : Bornology.IsBounded (cfPocket (R ω) (Lv ω) r') := isBounded_image_negInv h0U
  have hx₀' : cfPt (openPt (R ω) (Lv ω) r') ∉ cfPocket (R ω) (Lv ω) r' := hcf'.conf.cfPt_openPt_notMem
  have hJ' : Sec6.IsJordanCoord (cfPocket (R ω) (Lv ω) r') (cfPt (openPt (R ω) (Lv ω) r'))
      (cfPt (closePt (R ω) (Lv ω) r')) (ψ' ω) := hψ' ω hω'
  have hγ' : IsDrivenCurve (travAll R Lv r' η ψ' ω) := (hcf'.props (hψ' ω hω')).1
  have hP'o := hcf'.toPocket (hψ' ω hω')
  have hvisit := hP'o.erase.mem_visitSet hT0 htip
  obtain ⟨hqTpos, hqTlive⟩ : 0 < innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω ∧
      ENNReal.ofReal (innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω) <
        capLife (travAll R Lv r' η ψ' ω) :=
    SideVis.erasure_relCap_pos_lt_of_visit hP'o.erase hP'o.driven hvisit
  set qT := innerRelCap R Lv r' η ψ' (outerFibreEnd R L r η ψ q ω) ω with hqTdef
  have hqT0 : (0 : ℝ) ≤ qT := hqTpos.le
  have hqTc : ((qT.toNNReal : ℝ≥0) : ℝ) = qT := Real.coe_toNNReal _ hqT0
  obtain ⟨t₁', hqTt₁', ht₁'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hqTlive
  have hqTt : qT.toNNReal < t₁' := ENNReal.coe_lt_coe.1 hqTt₁'
  have hqTt' : qT < t₁' := by rw [← hqTc]; exact_mod_cast hqTt
  obtain ⟨E₀', hE₀', hE₀'c, hE₀'m, WU, hWU, hWU0, hWUeq, ηU, hηU, hηUeq, hUf⟩ :=
    chart_facts (n := n') hCo' hCH' hψc' hUb hx₀' hJ' hω' hγ' ht₁'
  obtain ⟨hI₀c, hI₀dom, hI₀fwd, hI₀E, hI₀Ec⟩ := hUf qT.toNNReal hqTt
  rw [hqTc] at hI₀dom hI₀fwd hI₀E hI₀Ec
  -- the inner tip at the visit time
  have htrU : capTrace (travAll R Lv r' η ψ' ω) qT.toNNReal = ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) :=
    R6Two.capTrace_relCap_outer_of_visit hP'o hvisit
  have hψ'T : ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) ∈ H := (hψc' ω hω').2.mapsTo htip
  have htipU : extendFrom H (fwdMapInv WU qT) ((0 : ℝ) : ℂ) = ψ' ω (η ω (outerFibreEnd R L r η ψ q ω)) := by
    have h1 := hηU.tendsto_fwdMapInv_tip hWU hWU0 hqT0
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηUeq qT hqT0 hqTt'.le, ← htrU]
    simp only [capTrace, hqTc]
  have hwR0 : 0 < chartAR WU qT := chartAR_pos_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwL0 : chartAL WU qT < 0 := chartAL_neg_of_tip hηU hWU hWU0 hqT0 (htipU ▸ hψ'T)
  have hwLR : chartAL WU qT < chartAR WU qT := hwL0.trans hwR0
  obtain ⟨hFTc, hFTeq, hFTm⟩ := extendFrom_props hηU hWU hWU0 hqT0
  set EI₀ : ℂ → ℂ := fun z => E₀' (extendFrom H (fwdMapInv WU qT) z) with hEI₀def
  set tip := η ω (outerFibreEnd R L r η ψ q ω) with htipdef
  have hEI₀0 : EI₀ ((0 : ℝ) : ℂ) = tip := by
    simp only [hEI₀def, htipU]
    rw [hE₀' hψ'T]
    exact (hψc' ω hω').2.injOn.leftInvOn_invFunOn htip
  -- the same-time inclusion and the identity (Astra's inner-side argument, reverse visits of `Lv`)
  obtain ⟨hI₀O, hid⟩ := two_identity_at_visit (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hsub hT0 htip
    (c := q) (c' := qT.toNNReal) (relCap_outerFibreEnd hcfg hψ hω hq).symm hqTc
  -- the inverse of the inner Jordan coordinate on `ℍ`
  have hinvU : ∀ k ∈ H, E₀' k ∈ cfPocket (R ω) (Lv ω) r' ∧ ψ' ω (E₀' k) = k := fun k hk => by
    rw [hE₀' hk]
    have hex : ∃ a ∈ cfPocket (R ω) (Lv ω) r', ψ' ω a = k := (hψc' ω hω').2.surjOn hk
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hullImg : ∀ k ∈ fwdHull WU qT, E₀' k ∉ ((curChart A R L r η ψ n q ω).dom : Set ℂ) := by
    intro k hk hkO
    have hkH : k ∈ H := QuantumZipper.fwdHull_mono.2 _ hk
    obtain ⟨heU, hek⟩ := hinvU k hkH
    have hmem : E₀' k ∈ ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := hid ⟨hkO, heU⟩
    rw [hI₀dom] at hmem
    have := hmem.2
    rw [Set.mem_preimage, hek] at this
    exact this.2 hk
  have hnotD : ∀ t ∈ Icc (chartAL WU qT) (chartAR WU qT),
      EI₀ t ∉ ((curChart A R L r η ψ n q ω).dom : Set ℂ) := fun t ht =>
    notMem_of_mem_closure_of_subset (K := E₀' '' fwdHull WU qT) (curChart A R L r η ψ n q ω).dom.isOpen
      (fun w hw => ⟨(hOphys hw).1, fun ⟨k, hk, hke⟩ => hullImg k hk (hke ▸ hw)⟩)
      (mem_closure_of_dead (KT := E₀' '' fwdHull WU qT) hE₀'c (QuantumZipper.fwdHull_mono.2 _)
        (fun k hk => ⟨k, hk, rfl⟩) (dead_of_mem_Icc hηU hWU hWU0 hqTpos hwLR ht))
  have hb0 : (extendFrom H (fwdMapInv WU qT) (chartAL WU qT : ℂ)).re ≤ 0 :=
    R6Fd.re_landL_le hηU hWU hWU0 hqTpos (x := 0) (by
      simpa using ConformalImageFull.zero_mem_closure_fwdHull hWU hWU0 hqTpos)
  have harcR : ∀ t : ℝ, t < chartAL WU qT → ∃ θ ∈ Ioo (rightLo (R ω) (Lv ω) r') (rightHi (R ω) (Lv ω) r'),
      EI₀ t = R6Fd.wallPt (R ω) θ := by
    intro t ht
    obtain ⟨him, hgt⟩ := landL_re_gt hηU hWU hWU0 hqTpos hwLR ht
    have hpm := hE₀'m (hFTm (real_mem_Hbar t))
    have hψp : ψ' ω (EI₀ t) = extendFrom H (fwdMapInv WU qT) (t : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar t))
    have hpU : EI₀ t ∉ cfPocket (R ω) (Lv ω) r' := fun h => by
      have := (hψc' ω hω').2.mapsTo h
      rw [hψp] at this
      have h2 : (0 : ℝ) < (extendFrom H (fwdMapInv WU qT) (t : ℂ)).im := this
      rw [him] at h2
      exact lt_irrefl _ h2
    have hpfr : EI₀ t ∈ frontier (cfPocket (R ω) (Lv ω) r') :=
      ⟨hpm.1, by rw [(hCo' ω hω').interior_eq]; exact hpU⟩
    exact frontier_neg_right_arc hcf'.conf h0U hcf'.oriented (hψ' ω hω') hpfr hpm.2 (by rw [hψp]; linarith)
  have hθI : ∀ θ ∈ Ioo (rightLo (R ω) (Lv ω) r') (rightHi (R ω) (Lv ω) r'), θ ∈ Ioc (0 : ℝ) 1 := by
    obtain ⟨-, hv', -, -, -, -, -, -⟩ := hcf'.conf.changeCorner_props
    exact fun θ hθ => ⟨(hcf'.conf.rightLo_pos h0U).trans hθ.1, hθ.2.le.trans hv'.2⟩
  have hnotA : ∀ t : ℝ, t < chartAL WU qT → EI₀ t ∉ cfPocket (R ω) (L ω) r := by
    intro t ht
    obtain ⟨θ, hθ, he⟩ := harcR t ht
    rw [he]
    exact R6Fd.wallPt_notMem hcf.conf (Or.inl rfl) (hθI θ hθ)
  set a := chartAL WU qT - 2 with hadef
  set ty := chartAL WU qT - 1 with htydef
  have hnot : ∀ t ∈ Ioo a (chartAR WU qT), EI₀ t ∉ ((curChart A R L r η ψ n q ω).dom : Set ℂ) := by
    intro t ht
    rcases le_or_gt (chartAL WU qT) t with h | h
    · exact hnotD t ⟨h, ht.2.le⟩
    · exact fun hm => hnotA t h (hOc.dom_subset hm |> fun _ => by rw [hOdom] at hm; exact hm.1)
  -- the outer corner `x₀` is not a landing of the inner chart
  have hxne : ∀ z ∈ Hbar, EI₀ z ≠ cfPt (openPt (R ω) (L ω) r) := by
    intro z hz he
    have hm := hE₀'m (hFTm hz)
    have hcl : cfPt (openPt (R ω) (L ω) r) ∈ closure (cfPocket (R ω) (Lv ω) r') := he ▸ hm.1
    exact hm.2 (he.trans (openPt_eq_of_mem_closure_right hcf.conf h0C hcf'.conf h0U hsub hcl))
  have hEI₀C : ∀ z ∈ Hbar, EI₀ z ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    fun z hz => ⟨closure_mono hsub (hE₀'m (hFTm hz)).1, hxne z hz⟩
  obtain ⟨C₀, hC₀⟩ := exists_norm_fwdMapInv_sub_le hWC hWC0 q.coe_nonneg
  have hbdd : ∀ t ∈ Ioo a (chartAR WU qT), ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (t : ℂ),
      ‖(curChart A R L r η ψ n q ω).1 ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ M := by
    intro t _
    have hpC := hEI₀C t (real_mem_Hbar t)
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hJ.1 _ hpC) 1 one_pos
    refine ⟨‖ψ ω (EI₀ t)‖ + 1 + C₀, ?_⟩
    have hev : ∀ᶠ z in 𝓝[Hbar] (t : ℂ), EI₀ z ∈ ball (EI₀ t) δ :=
      (hI₀Ec _ (real_mem_Hbar t)).tendsto.eventually (ball_mem_nhds _ hδ)
    filter_upwards [nhdsWithin_mono _ QuantumZipper.H_subset_Hbar hev, self_mem_nhdsWithin] with z hzb hzH
    have hwI := hI₀c.inv_mem_dom hzH
    have hwO := hI₀O hwI
    have hwO' := hwO
    rw [hOdom] at hwO'
    rw [hOfwd _ hwO'.1]
    have hwz : (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z = EI₀ z := (hI₀E hzH).symm
    have h1 := norm_fwdMap_le hWC hWC0 q.coe_nonneg hC₀ hwO'.2
    have hwx : (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z ∈
        closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
      ⟨subset_closure hwO'.1, fun h => hx₀ (h ▸ hwO'.1)⟩
    have h2 := hδψ hwx (by rw [hwz]; exact hzb)
    rw [dist_eq_norm] at h2
    have h3 : ‖ψ ω ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)‖ ≤ ‖ψ ω (EI₀ t)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (ψ ω ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z)) (ψ ω (EI₀ t))
      linarith
    linarith
  -- the driver identification
  have hdrv := hdrv_of_later (O := curChart A R L r η ψ n q ω) (I₀ := curChart A' R Lv r' η ψ' n' qT.toNNReal ω)
    hWC hWC0 hWU hWU0 q.coe_nonneg hqT0 hOfwd hOdom hI₀fwd hI₀dom hsub hI₀O (hψc' ω hω')
    (hlater_two (n := n) (n' := n') hcfg hψ hcfg' hψ' hω hω' hrev hq hsub hT0 htip hqt₁' ht₁ hqTt'
      (fun q₂ hq₂ => (hCf q₂ hq₂).2.1) (fun q₂ hq₂ => (hUf q₂ hq₂).2.1))
  -- the test point on the old hull inside `U`
  have hEI₀d : DifferentiableOn ℂ EI₀ H := hI₀c.1.congr fun z hz => hI₀E hz
  have hEI₀i : InjOn EI₀ H := hI₀c.injOn.congr hI₀E.symm
  have hEI₀0' : EI₀ 0 = tip := by simpa using hEI₀0
  obtain ⟨tξ, htξ, htξU, htξne⟩ := R6Land.exists_exposed_landing hEI₀d hI₀Ec hEI₀i (hCo' ω hω')
    (by rw [hEI₀0']; exact htip) hwL0.le le_rfl hwL0
  rw [hEI₀0'] at htξne
  have hpytip : EI₀ ty ≠ tip := fun h => hnotA ty (by linarith) (h ▸ hTC)
  set d₀ := min (dist (EI₀ tξ) tip) (dist (EI₀ ty) tip) with hd₀
  have hd₀pos : 0 < d₀ := lt_min (dist_pos.2 htξne) (dist_pos.2 hpytip)
  obtain ⟨ρ₁, hρ₁, hρ₁E⟩ := Metric.continuousWithinAt_iff.1 (hI₀Ec _ (real_mem_Hbar 0)) (d₀ / 2) (half_pos hd₀pos)
  set ρ := min (-tξ / 4) (ρ₁ / 2) with hρdef
  have hρ0 : 0 < ρ := lt_min (by linarith [htξ.2]) (half_pos hρ₁)
  have h2ρ : tξ < -(2 * ρ) := by linarith [min_le_left (-tξ / 4) (ρ₁ / 2), htξ.2]
  have hρnear : ∀ z ∈ Hbar, ‖z‖ ≤ ρ → dist (EI₀ z) tip < d₀ / 2 := fun z hz hzn => by
    have h := hρ₁E hz (by
      rw [Complex.ofReal_zero, dist_zero_right]; linarith [min_le_right (-tξ / 4) (ρ₁ / 2)])
    rwa [hEI₀0] at h
  -- the window of later inner times
  obtain ⟨θ₁, hθ₁, hθ₁K⟩ := exists_shift_hull_small hWU qT (show (0 : ℝ) < 2 * ρ by linarith)
  obtain ⟨θW, hθW, hθWc⟩ := Metric.continuousAt_iff.1 (hWU.continuousAt (x := qT)) (ρ / 96) (by positivity)
  have hARc : ContinuousAt (fun t => chartAR WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.sub hWU.continuousAt
  have hALc : ContinuousAt (fun t => chartAL WU t) qT := by
    have h1 := (MartChar.RealFlow.continuousOn_rightImg hWU.neg 0).continuousAt (Ici_mem_nhds hqTpos)
    exact h1.neg.sub hWU.continuousAt
  obtain ⟨θa, hθa, hθaR⟩ := Metric.continuousAt_iff.1 hARc (chartAR WU qT) hwR0
  obtain ⟨θb, hθb, hθbL⟩ := Metric.continuousAt_iff.1 hALc (-chartAL WU qT) (by linarith)
  set εW := min (min θ₁ θW) (min ((ρ / 32) ^ 2) (min (min θa θb) (t₁' - qT))) with hεWdef
  have hεW : 0 < εW := lt_min (lt_min hθ₁ hθW) (lt_min (by positivity) (lt_min (lt_min hθa hθb) (by linarith)))
  refine ⟨εW, hεW, fun q' hq'lo hq'hi hIncl ρL ρR σL σR vL vR wL wR hvLv hvR' hwLv hwR' hρσ => ?_⟩
  have hq'lo' : qT < q' := hq'lo
  have hq'hi' : (q' : ℝ) < qT + εW := hq'hi
  have hm1 : εW ≤ θ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : εW ≤ θW := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : εW ≤ (ρ / 32) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : εW ≤ min θa θb := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm5 : εW ≤ t₁' - qT := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hq't : q' < t₁' := by
    have : (q' : ℝ) < t₁' := by linarith
    exact_mod_cast this
  have hq'pos : (0 : ℝ) < q' := hqTpos.trans hq'lo'
  obtain ⟨hIc, hIdom, hIfwd, hIE, hIEc⟩ := hUf q' hq't
  have hWUq : ∀ s ∈ Icc (0 : ℝ) q', segDriver (travAll R Lv r' η ψ' ω) s.toNNReal = WU s := fun s hs =>
    hWUeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hq't.le)⟩
  have hwRe : seedR R Lv r' η ψ' q' ω = chartAR WU q' := seedR_eq hWU hWUq
  have hwLe : seedL R Lv r' η ψ' q' ω = chartAL WU q' := seedL_eq hWU hWUq
  have hdq : dist (q' : ℝ) qT < min θa θb := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have hwR0' : 0 < chartAR WU q' := by
    have h := hθaR (hdq.trans_le (min_le_left _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.2]
  have hwL0' : chartAL WU q' < 0 := by
    have h := hθbL (hdq.trans_le (min_le_right _ _))
    rw [Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  have hwLR' : chartAL WU q' < chartAR WU q' := hwL0'.trans hwR0'
  obtain ⟨hF'c, hF'eq, hF'm⟩ := extendFrom_props hηU hWU hWU0 q'.coe_nonneg
  set δ := (q' : ℝ) - qT with hδdef
  have hδ0 : 0 ≤ δ := by linarith
  have hsmall : fwdHull (QuantumZipper.RS.shiftDrive WU qT) δ ⊆ closedBall 0 ρ := by
    have h := hθ₁K δ hδ0 (by linarith)
    rwa [show 2 * ρ / 2 = ρ by ring] at h
  -- the increment: away from `0` in the same-time chart, points stay in the later domain
  have hinc : ∀ z ∈ H, ρ < ‖z‖ →
      (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 z ∈ ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro z hz hzn
    rw [← hI₀E hz]
    show E₀' (extendFrom H (fwdMapInv WU qT) z) ∈ _
    rw [hFTeq hz]
    have hk := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWU hWU0 hqT0 hz
    obtain ⟨heU, hek⟩ := hinvU _ hk.1
    rw [hIdom]
    refine ⟨heU, ?_⟩
    show ψ' ω (E₀' (fwdMapInv WU qT z)) ∈ H \ fwdHull WU q'
    rw [hek]
    refine ⟨hk.1, fun hkq => ?_⟩
    have hdiff : fwdMapInv WU qT z ∈ fwdHull WU (qT + δ) \ fwdHull WU qT := by
      rw [hδdef, add_sub_cancel]; exact ⟨hkq, hk.2⟩
    rw [Sec5.fwdHull_add_sdiff_eq_image hWU hWU0 hqT0 hδ0] at hdiff
    obtain ⟨a, ha, hae⟩ := hdiff
    have haH : a ∈ H := QuantumZipper.fwdHull_mono.2 _ ha
    have haz : a = z := QuantumZipper.RS.injOn_fwdMapInv hWU hWU0 hqT0 haH hz hae
    have := hsmall ha
    rw [mem_closedBall, dist_zero_right, haz] at this
    linarith
  have hinc0 : ∀ᶠ w in 𝓝[H] (0 : ℂ),
      ‖(curChart A' R Lv r' η ψ' n' qT.toNNReal ω).1 ((curChart A' R Lv r' η ψ' n' q' ω).2.1 w)‖ ≤ ρ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) (half_pos hρ0))] with w hwH hwb
    rw [← hIE hwH]
    show ‖(curChart A' R Lv r' η ψ' n' qT.toNNReal ω).1 (E₀' (extendFrom H (fwdMapInv WU q') w))‖ ≤ ρ
    rw [hF'eq hwH]
    have hvH := QuantumZipper.RS.fwdMapInv_mem_H hWU hWU0 q'.coe_nonneg hwH
    obtain ⟨hvU, hvk⟩ := hinvU _ hvH
    rw [hI₀fwd _ hvU, hvk]
    have hq'eq : (q' : ℝ) = qT + δ := by rw [hδdef]; ring
    rw [hq'eq, QuantumZipper.RS.fwdMapInv_add_shift hWU hWU0 hqT0 hδ0 hwH]
    have hsH := QuantumZipper.RS.fwdMapInv_mem_H (QuantumZipper.RS.continuous_shiftDrive hWU qT)
      (QuantumZipper.RS.shiftDrive_zero WU qT) hδ0 hwH
    rw [QuantumZipper.RS.fwdMap_fwdMapInv hWU hWU0 hqT0 hsH]
    have hM : ∀ s ∈ Icc (0 : ℝ) δ, |QuantumZipper.RS.shiftDrive WU qT s| ≤ ρ / 96 := by
      intro s hs
      have h := hθWc (show dist (qT + s) qT < θW by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]; linarith [hs.2])
      rw [Real.dist_eq] at h
      exact h.le
    have h1 := InteractingSLE.norm_fwdMapInv_sub_le (QuantumZipper.RS.continuous_shiftDrive hWU qT)
      (QuantumZipper.RS.shiftDrive_zero WU qT) hδ0 hM hwH
    have hsq : Real.sqrt δ < ρ / 32 := by
      rw [Real.sqrt_lt' (by positivity)]; linarith
    have hwn : ‖w‖ < ρ / 2 := by simpa [mem_ball, dist_zero_right] using hwb
    have h2 : ‖fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w‖ ≤
        ‖w‖ + ‖fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w - w‖ := by
      calc _ = ‖w + (fwdMapInv (QuantumZipper.RS.shiftDrive WU qT) δ w - w)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  -- the two test landings
  have htξab : tξ ∈ Ioo a (chartAR WU qT) := ⟨by linarith [htξ.1], by linarith [htξ.2]⟩
  have hpξC : EI₀ tξ ∈ cfPocket (R ω) (L ω) r := hsub htξU
  have hpξO := hnot tξ htξab
  have hψpξ : ψ ω (EI₀ tξ) ∈ fwdHull WC q := by
    by_contra hn
    exact hpξO (by rw [hOdom]; exact ⟨hpξC, (hψc ω hω).2.mapsTo hpξC, hn⟩)
  have hψ'pξ : ψ' ω (EI₀ tξ) ∈ fwdHull WU q' := by
    have hn : EI₀ tξ ∉ ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun h => hpξO (hI₀O h)
    rw [hI₀dom] at hn
    have hH := (hψc' ω hω').2.mapsTo htξU
    have : ψ' ω (EI₀ tξ) ∈ fwdHull WU qT := by
      by_contra hk; exact hn ⟨htξU, hH, hk⟩
    exact QuantumZipper.fwdHull_mono.1 hq'lo'.le this
  obtain ⟨θy, hθy, hpyθ⟩ := harcR ty (by linarith)
  obtain ⟨hNC1, hNC2, hNC3⟩ := R6Fd.nonCorner_of_right_open hcf.conf hcf'.conf h0U hθy
  rw [← hpyθ] at hNC1 hNC2 hNC3
  have hpyU : EI₀ ty ∈ closure (cfPocket (R ω) (Lv ω) r') := frontier_subset_closure hNC1
  obtain ⟨εy, hεy, hεyU⟩ := inter_ball_subset_of_noncorner hJ hCb hx₀ (hCo' ω hω') hsub hpyU
    (closure_mono hsub hpyU) (hxne _ (real_mem_Hbar ty)) hNC2
  have hψ'py : ψ' ω (EI₀ ty) = extendFrom H (fwdMapInv WU qT) (ty : ℂ) :=
    jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hFTm (real_mem_Hbar ty))
  have hpyAlive : ψ' ω (EI₀ ty) ∉ closure (fwdHull WU qT) := by
    rw [hψ'py]; exact alive_of_not_mem_Icc hηU hWU hWU0 hqT0 (Or.inl (by linarith))
  have hIncl₀ : cfPocket (R ω) (Lv ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) ⊆
      cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) := by
    rw [← hI₀dom, ← hOdom]; exact hI₀O
  have hOU : ∀ w ∈ ((curChart A R L r η ψ n q ω).dom : Set ℂ), w ∈ cfPocket (R ω) (Lv ω) r' →
      w ∈ ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).dom : Set ℂ) := fun w hwO hwU => hid ⟨hwO, hwU⟩
  have hpyCalive : ψ ω (EI₀ ty) ∉ closure (fwdHull WC q) := by
    have hΛa : cfPocket (R ω) (L ω) r ∩ ball (EI₀ ty) εy ⊆ cfPocket (R ω) (Lv ω) r' := hεyU
    have hΛ : cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fwdHull WC q) ∩ ball (EI₀ ty) εy ⊆
        cfPocket (R ω) (Lv ω) r' ∩ ψ' ω ⁻¹' (H \ fwdHull WU qT) := fun w hw => by
      have hwO : w ∈ ((curChart A R L r η ψ n q ω).dom : Set ℂ) := by rw [hOdom]; exact hw.1
      have := hOU w hwO (hΛa ⟨hw.1.1, hw.2⟩)
      rwa [hI₀dom] at this
    exact (alive_iff hJ hCb hx₀ hJ' hUb hx₀' hsub (QuantumZipper.fwdHull_mono.2 _)
      (QuantumZipper.fwdHull_mono.2 _) hIncl₀ hΛa hΛ (mem_ball_self (half_pos hεy)) (hEI₀C ty (real_mem_Hbar ty))
      (hE₀'m (hFTm (real_mem_Hbar ty)))).2 hpyAlive
  -- dead and alive in the outer chart
  have hdeadO : ∀ x : ℝ, EO x = EI₀ tξ → vL 0 < x ∧ x ≤ vR 0 := by
    intro x hx
    rw [hvLv, hvL, hvR', hvR]
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_ext hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    refine ⟨lt_of_not_ge fun hle => ?_, not_lt.1 fun hgt => ?_⟩
    · rcases hle.lt_or_eq with hlt | heq
      · exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inl hlt) (hψx ▸ subset_closure hψpξ)
      · have him := R6Fd.landL_im_eq_zero hηC hWC hWC0 q.coe_nonneg
        rw [← heq, ← hψx] at him
        have hH : (0 : ℝ) < (ψ ω (EI₀ tξ)).im := (hψc ω hω).2.mapsTo hpξC
        linarith
    · exact alive_of_not_mem_Icc hηC hWC hWC0 q.coe_nonneg (Or.inr hgt) (hψx ▸ subset_closure hψpξ)
  have haliveO : ∀ x : ℝ, EO x = EI₀ ty → x < vL 0 ∨ vR 0 < x := by
    intro x hx
    rw [hvLv, hvL, hvR', hvR]
    by_contra hxI
    push Not at hxI
    have hψx : ψ ω (EO x) = extendFrom H (fwdMapInv WC q) (x : ℂ) :=
      jordan_comp_ext hJ hE₀ hE₀c hE₀m (hFm (real_mem_Hbar x))
    rw [hx] at hψx
    exact hpyCalive (hψx ▸ dead_of_mem_Icc hηC hWC hWC0 hq0' (hvL0.trans hvR0) hxI)
  -- dead and alive in the later inner chart
  have hdeadI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ tξ → wL 0 < x ∧ x < wR 0 := by
    intro x hx
    rw [hwLv, hwLe, hwR', hwRe]
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hx] at hψx
    have hH : (0 : ℝ) < (ψ' ω (EI₀ tξ)).im := (hψc' ω hω').2.mapsTo htξU
    refine ⟨lt_of_not_ge fun hle => ?_, lt_of_not_ge fun hge => ?_⟩
    · rcases hle.lt_or_eq with hlt | heq
      · exact alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg (Or.inl hlt) (hψx ▸ subset_closure hψ'pξ)
      · have him := R6Fd.landL_im_eq_zero hηU hWU hWU0 q'.coe_nonneg
        rw [← heq, ← hψx] at him
        linarith
    · rcases hge.lt_or_eq with hgt | heq
      · exact alive_of_not_mem_Icc hηU hWU hWU0 q'.coe_nonneg (Or.inr hgt) (hψx ▸ subset_closure hψ'pξ)
      · have him := R6Fd.landR_im_eq_zero hηU hWU hWU0 q'.coe_nonneg
        rw [heq, ← hψx] at him
        linarith
  -- the later hull near the old one: `K_{q'} ⊆ K_{q_T} ∪ F̄_{q_T}(ℍ̄ ∩ B̄(0, ρ))`
  set S := (fun z => extendFrom H (fwdMapInv WU qT) z) '' (Hbar ∩ closedBall 0 ρ) with hSdef
  have hSc : IsClosed S := by
    have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) ρ) := by
      refine (isCompact_closedBall 0 ρ).inter_left ?_
      rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact isClosed_closure
    exact (hK.image_of_continuousOn (hFTc.mono inter_subset_left)).isClosed
  have hKsub : fwdHull WU q' ⊆ fwdHull WU qT ∪ S := by
    intro k hk
    by_cases hkT : k ∈ fwdHull WU qT
    · exact Or.inl hkT
    · right
      have hdiff : k ∈ fwdHull WU (qT + δ) \ fwdHull WU qT := by
        rw [hδdef, add_sub_cancel]; exact ⟨hk, hkT⟩
      rw [Sec5.fwdHull_add_sdiff_eq_image hWU hWU0 hqT0 hδ0] at hdiff
      obtain ⟨a, ha, rfl⟩ := hdiff
      have haH : a ∈ H := QuantumZipper.fwdHull_mono.2 _ ha
      exact ⟨a, ⟨QuantumZipper.H_subset_Hbar haH, hsmall ha⟩, hFTeq haH⟩
  have hfar : ∀ p ∈ closure (cfPocket (R ω) (Lv ω) r') \ {cfPt (openPt (R ω) (Lv ω) r')}, d₀ ≤ dist p tip →
      ψ' ω p ∉ S := by
    rintro p hp hpd ⟨z, hz, hze⟩
    have hpe : EI₀ z = p := by
      show E₀' (extendFrom H (fwdMapInv WU qT) z) = p
      have hze' : extendFrom H (fwdMapInv WU qT) z = ψ' ω p := hze
      rw [hze']; exact R6Fd.extension_psi_eq hJ' hx₀' hE₀' hE₀'c hp
    have := hρnear z hz.1 (by simpa [mem_closedBall, dist_zero_right] using hz.2)
    rw [hpe] at this
    linarith
  have haliveI : ∀ x : ℝ, E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ)) = EI₀ ty → x < wL 0 ∨ wR 0 < x := by
    intro x hx
    rw [hwLv, hwLe, hwR', hwRe]
    by_contra hxI
    push Not at hxI
    have hψx : ψ' ω (E₀' (extendFrom H (fwdMapInv WU q') (x : ℂ))) = extendFrom H (fwdMapInv WU q') (x : ℂ) :=
      jordan_comp_ext hJ' hE₀' hE₀'c hE₀'m (hF'm (real_mem_Hbar x))
    rw [hx] at hψx
    have hd := dead_of_mem_Icc hηU hWU hWU0 hq'pos hwLR' hxI
    rw [← hψx] at hd
    have hcl : closure (fwdHull WU q') ⊆ closure (fwdHull WU qT) ∪ S :=
      (closure_mono hKsub).trans (by rw [closure_union, hSc.closure_eq])
    rcases hcl hd with h | h
    · exact hpyAlive h
    · exact hfar _ (hE₀'m (hFTm (real_mem_Hbar ty))) (min_le_right _ _) h
  -- local agreement at the two test landings
  have hloc : ∀ p : ℂ, d₀ ≤ dist p tip → ∀ ε₁ > 0,
      ((curChart A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε₁ ⊆ cfPocket (R ω) (Lv ω) r' →
      ∃ ε > 0, ((curChart A R L r η ψ n q ω).dom : Set ℂ) ∩ ball p ε ⊆
        ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    intro p hpd ε₁ hε₁ hsubU
    refine ⟨min ε₁ (d₀ / 2), lt_min hε₁ (half_pos hd₀pos), fun w hw => ?_⟩
    have hwU := hsubU ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
    have hwI := hOU w hw.1 hwU
    have hz := hI₀c.fwd_mem hwI
    have hwe : (curChart A' R Lv r' η ψ' n' qT.toNNReal ω).2.1 ((curChart A' R Lv r' η ψ' n' qT.toNNReal ω).1 w) = w :=
      hI₀c.inv_fwd hwI
    rw [← hwe]
    refine hinc _ hz (lt_of_not_ge fun hle => ?_)
    have h1 := hρnear _ (QuantumZipper.H_subset_Hbar hz) hle
    rw [hI₀E hz, hwe] at h1
    have h2 : dist w p < d₀ / 2 := (mem_ball.1 hw.2).trans_le (min_le_right _ _)
    have h3 := dist_triangle p w tip
    rw [dist_comm p w] at h3
    linarith
  have hlocξ : ∃ ε > 0, ((curChart A R L r η ψ n q ω).dom : Set ℂ) ∩ ball (EI₀ tξ) ε ⊆
      ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) := by
    obtain ⟨ε₁, hε₁, hε₁U⟩ := Metric.isOpen_iff.1 (hCo' ω hω') _ htξU
    exact hloc _ (min_le_left _ _) ε₁ hε₁ fun w hw => hε₁U hw.2
  have hlocy := hloc _ (min_le_right _ _) εy hεy fun w hw => by
    rw [hOdom] at hw
    exact hεyU ⟨hw.1.1, hw.2⟩
  -- the bound of the later inner coordinate near the inner landings
  obtain ⟨C₀', hC₀'⟩ := exists_norm_fwdMapInv_sub_le hWU hWU0 q'.coe_nonneg
  have hbddI : ∀ t ∈ Ioo a (chartAR WU qT), ∃ ε > 0, ∃ M : ℝ,
      ∀ w ∈ ((curChart A' R Lv r' η ψ' n' q' ω).dom : Set ℂ) ∩ ball (EI₀ t) ε,
        ‖(curChart A' R Lv r' η ψ' n' q' ω).1 w‖ ≤ M := by
    intro t _
    have hpU := hE₀'m (hFTm (real_mem_Hbar t))
    obtain ⟨ε, hε, hεψ⟩ := Metric.continuousWithinAt_iff.1 (hJ'.1 _ hpU) 1 one_pos
    refine ⟨ε, hε, ‖ψ' ω (EI₀ t)‖ + 1 + C₀', fun w hw => ?_⟩
    have hwI := hw.1
    rw [hIdom] at hwI
    rw [hIfwd _ hwI.1]
    have h1 := norm_fwdMap_le hWU hWU0 q'.coe_nonneg hC₀' hwI.2
    have hwx : w ∈ closure (cfPocket (R ω) (Lv ω) r') \ {cfPt (openPt (R ω) (Lv ω) r')} :=
      ⟨subset_closure hwI.1, fun h => hx₀' (h ▸ hwI.1)⟩
    have h2 := hεψ hwx (mem_ball.1 hw.2)
    rw [dist_eq_norm] at h2
    have h3 := norm_le_norm_add_norm_sub' (ψ' ω w) (ψ' ω (EI₀ t))
    linarith
  exact r6FaceR_left_of_reflection hOc hI₀c hIc hI₀O hIncl hOE hOEc hI₀E hI₀Ec hIE hIEc hwR0 hnot hbdd hdrv hρ0
    hinc hinc0 h2ρ (by linarith [htξ.1]) (by linarith) hdeadO haliveO hdeadI haliveI (by rw [hwLv, hwLe]; exact hwL0')
    hρσ hlocξ hlocy hbddI


end Two

section Final

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide
open Sec5.Prop55Half (IsSeedProper)

universe u

/-- **The left frontier `M_L` is visited in reverse order**, almost surely (`OuterIn.ae_walls_r7` for the flow line
`β_L` at angle `π/2`, and `M_L = β_L` a.s.). -/
theorem ae_rev_ML {k rL rR c c' : ℝ} (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {αR βR βL αL : Ω → ℝ≥0 → ℂ} {ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞}
    (hcfg : IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL)
    {R L : Ω → ℝ≥0 → ℂ} {η : Ω → ℝ → ℂ} (hV : IsR7Versions P W' αR αL R L η) {ML : Ω → ℝ≥0 → ℂ}
    (hML : IsFrontierVersion P βL ML) : ∀ᵐ ω ∂P, IsWallReverseVisit (ML ω) (η ω) := by
  have hβLs : ∀ᵐ ω ∂P, Lemma71I.IsSimpleProper (βL ω) :=
    hcfg.regular.mono fun ω hω => IsSeedProper.isSimpleProper hω.2.2.1
  have hwβL := OuterIn.ae_walls_r7 h411 h47 h47T hk4 hc hc' hcfg.gff hcfg.counterflow (θ := π / 2)
    ⟨by linarith [Real.pi_pos], le_rfl⟩ hcfg.flow_βL hβLs hV.η_cont hV.η_zero hV.η_trace
  filter_upwards [hwβL, hML.2.2.2] with ω hw he
  rw [he]
  exact hw.1

/-- **R.6's face, shape `Two` (two bounded outer pockets), PROVED from the reverse visits of `M_L`** (Prop. 4.11 and
Lemma 4.7 through `OuterIn.ae_walls_r7`): Astra's inner-side identity replaces Aux. lemma 136. -/
theorem r6FaceSTwoRemaining_of_walls {k rL rR c c' : ℝ} (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (h47T : ∀ θ : ℝ, -(π / 2) < θ → θ < π / 2 → Sec5.RestartGen.Lemma47QHitTStatement.{u} θ)
    (hk4 : 4 < k) (hc : 0 ≤ c) (hc' : 0 ≤ c') : R6Two.R6FaceSTwoRemaining.{u} k rL rR c c' := by
  intro _ _ Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [ae_rev_ML h411 h47 h47T hk4 hc hc' hcfg hV hML] with ω hrev hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hcfO := (hA ω hωA).1
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcfO.props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAll R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ∈ cfPocket (R ω) (ML ω) (StripSys.rt s) := by
    unfold outerFibreEnd
    rw [hinv]
    exact hrel
  have hT0 : 0 ≤ outerFibreEnd R L r η ψ (StripSys.rt q) ω :=
    hcfO.erase.nonneg.trans (hcfO.erase.fibre_mem _).1
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hcfg' : ∀ ω ∈ A', IsOuterCfg (R ω) (ML ω) (StripSys.rt s) (fun t : ℝ => W' t.toNNReal ω) (η ω) :=
    fun ω hω => (hA' ω hω).1
  have hψ' : ∀ ω ∈ A', IsCfJordan (R ω) (ML ω) (StripSys.rt s) (ψ' ω) := fun ω hω => (hA' ω hω).2
  have hP'o := (hcfg' ω hωA').toPocket (hψ' ω hωA')
  have hqT0 : 0 ≤ innerRelCap R ML (StripSys.rt s) η ψ' (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω :=
    (SideVis.erasure_relCap_pos_lt_of_visit hP'o.erase hP'o.driven (hP'o.erase.mem_visitSet hT0 htip)).1.le
  obtain ⟨εW, hεW, hpkg⟩ := two_face (n := n) (n' := n') (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2)
    hcfg' hψ' hωA hωA' hrev hq0' hqlive hsub hT0 htip
  refine ⟨εW, hεW, fun q' hlo hhi hlive _ hincl => ?_⟩
  have hrt' : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ (hqT0.trans hlo.le)
  have hγ' : IsDrivenCurve (travAll R ML (StripSys.rt s) η ψ' ω) := ((hcfg' ω hωA').props (hψ' ω hωA')).1
  have hcO := (R5Phase.shiftChart_dom_facts (n := n)
    (fun ω hω => isOpen_image_negInv' (hA ω hω).1.conf.isOpen_changePocket (hA ω hω).1.conf.changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hA ω hω).1.conf.changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) ω hωA).1
  have hcI := (R5Phase.shiftChart_dom_facts (n := n')
    (fun ω hω => isOpen_image_negInv' (hcfg' ω hω).conf.isOpen_changePocket (hcfg' ω hω).conf.changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hcfg' ω hω).conf.changePocket_subset_H)
    (fun ω hω => (hψ' ω hω).2.2.2.1) ω hωA').1
  rw [pocketSet_eq hωA hqlive hγ hcO, pocketSet_eq hωA' hlive hγ' hcI]
  exact hpkg (StripSys.rt q') (by rw [hrt']; exact hlo) (by rw [hrt']; exact hhi) hincl _ _ _ _ _ _ _ _ rfl rfl rfl
    rfl rfl

end Final

end InteractingSLE.Sec7.R6Cor
