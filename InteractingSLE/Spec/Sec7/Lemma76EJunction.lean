/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76EDet
import InteractingSLE.Spec.Supplement.G12RemSwallow
import InteractingSLE.Spec.Sec5.Aux22StripAlive
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Sec7.LocalExtGChart
import QuantumZipper.Proofs.Zipper.B5LocF1Side
import QuantumZipper.Proofs.Thm11.ForwardTamed

/-!
# The junction continuation inequality for flow lines (`FlowLineJunctionStatement`)

Packet PROVE-LEMMA76E. Specification §7.2, proof of Lemma 7.6 (p. 269): "There is one additional possible prime end:
`V^α_R` itself, whose impression is the physical rightmost real point `x_R` swallowed by the first hull. It matters only
if its first visit occurs at a parameter `u_R < ξ₁`. In that case the first path continued after this visit. If `c` is
the original field height immediately to the right of `x_R`, its swallowed right force sum is `(c + θ₁χ)/λ − 1`.
Continuation implies that this sum is greater than `−2`, hence `c + θ₁χ > −λ`. This also covers `u_R = 0`, using
admissibility of the starting right force group."

For one path of the driving evolution (`Sec2.IsForcePath`) with a simple continuous generating trace `γ`, at a time
`u < ζ` at which `γ(u) = X ∈ ℝ` is the rightmost real point of `γ([0, u])`:

* **`vR_eq_w_iff`**: the right marks merged with the driver at `u` are exactly those at positions `≤ X`:
  - a mark `x_k > X` is separated: a point `X'' ∈ (X, x_k)` is alive at `u` (the trace stays off `[X'', ∞)`; box
    argument and `ZhanGT4.exists_isForwardSol_of_disjoint_ball`), and `V^k_u = R^{x_k}_u ≥ g_u(X'') > W_u`
    (`SideHeight.vR_eq_rightImg_frozenDrive`);
  - a mark `x_j ≤ X` is merged: `X` is alive before `u`, so `V^j − W ≤ g(X) − W`; if the gap of `X` stayed `≥ c > 0`
    near `u`, `X` would be alive at `u` (`MartChar.RealFlow.Alive.of_forall_le_cflow`), so a disc around `X` would miss
    `K_u` (`GB7a.exists_ball_notMem_fwdHull`), while the trace points `γ(s) ∈ closure K_s` tend to `X`
    (`G12.trace_mem_closure_fwdHull`);
* the threshold condition fails at `u`, so the merged sum exceeds `−2`; for the flow-line word that sum is
  `(b(x_R⁺) + θχ)/λ − 1` (`Exist.sum_filter_flowLineXR_seed`, `Exist.eq_rightLim_add_sum_seed`);
* **`flowLineJunctionStatement`**: `FlowLineJunctionStatement` (with Aux. lemma 25 for the simplicity of the trace).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC fwdHull IsForwardSol)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma76E

open MartChar.RealFlow
open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-! ### Alive real points from the trace -/

/-- **A forward solution from a real point right of the driver gives a positive real solution.** -/
theorem alive_of_isForwardSol {W : ℝ → ℝ} (hW : Continuous W) {y t : ℝ} (ht : 0 ≤ t) (hy : W 0 < y)
    {v : ℝ → ℂ} (hv : IsForwardSol W (y : ℂ) t v) : Alive W y t := by
  obtain ⟨hc, -, heq⟩ := QuantumZipper.B5.real_eq_of_isForwardSol hv
  exact ⟨fun q => (v q).re, hc, fun s hs => ⟨QuantumZipper.re_pos_isForwardSol_real hW ht hv hy s hs, heq s hs⟩⟩

/-- **A real point beyond the trace is alive.** If the generating trace stays off `[y, ∞)` on `[0, t]`, `y > 0`, then
`y` is alive at `t` for the driver frozen after any `t₂ > t` below the lifetime. -/
theorem alive_of_trace_off {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hg : IsGeneratingTrace w ζ γ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {t₂ : ℝ} (ht₂ : ENNReal.ofReal t₂ < ζ)
    {t : ℝ≥0} (htt₂ : (t : ℝ) < t₂) {y : ℝ} (hy : 0 < y) (hoff : ∀ s ≤ t, ∀ r : ℝ, y ≤ r → γ s ≠ r) :
    Alive (frozenDrive w t₂) y t := by
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hwc ht₂
  have ht₂0 : 0 ≤ t₂ := t.coe_nonneg.trans htt₂.le
  have hW0 : W 0 = 0 := by rw [hWdef, InteractingSLE.frozenDrive_zero ht₂0, hw0]
  have htζ : (t : ℝ≥0∞) < ζ := by
    refine lt_of_le_of_lt ?_ ht₂
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal htt₂.le
  set A := γ '' Icc 0 t with hA
  have hAc : IsCompact A :=
    isCompact_Icc.image_of_continuousOn (hg.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans htζ.le)
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) t = fillH A := by
    have h := hg.2.2 t htζ
    rw [isFilling_iff_inter_H_eq_fillH hAc.isBounded hAc.isClosed,
      inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := fun s : ℝ => w s.toNNReal)).2 _)] at h
    exact h
  have hKW : fwdHull W t = fwdHull (fun s : ℝ => w s.toNNReal) t :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt t.coe_nonneg htt₂ fun s hs => frozenDrive_eq hs
  obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
  set e : ℝ := max R y + 1 with he
  have hyR : y ≤ e := by rw [he]; linarith [le_max_right R y]
  have heR : R < |e| := by
    rw [abs_of_pos (by rw [he]; linarith [le_max_right R y])]
    rw [he]; linarith [le_max_left R y]
  obtain ⟨ρ, hρ, hball⟩ := Sec5.Aux22Strip.exists_ball_notMem_fillH_aux hAc hR (a := y) (b := e) (e := e) (x := y)
    (fun r hr ⟨s, hs, hγ⟩ => hoff s hs.2 r hr.1 hγ) ⟨le_rfl, hyR⟩ ⟨hyR, le_rfl⟩ heR
  obtain ⟨v, hv⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 hy.ne' t.coe_nonneg hρ (by
    rw [hKW, hK, Set.disjoint_left]
    exact fun z hz => hball z hz)
  exact alive_of_isForwardSol hW t.coe_nonneg (by rw [hW0]; exact hy) hv

/-- **A real point visited by the trace at `u > 0` is not alive at `u`**: otherwise a disc around it misses `K_u`
(`GB7a.exists_ball_notMem_fwdHull`), while the trace points `γ(s) ∈ closure K_s ⊆ closure K_u`, `s < u`, tend to it
(the argument of `G12.tendsto_gap_eq_zero_of_visit`, for a real point instead of a mark). -/
theorem not_alive_of_visit {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hg : IsGeneratingTrace w ζ γ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {t₂ : ℝ} (ht₂ : ENNReal.ofReal t₂ < ζ)
    {u : ℝ≥0} (hu0 : 0 < u) (hut₂ : (u : ℝ) < t₂) {X : ℝ} (hvis : γ u = X) :
    ¬ Alive (frozenDrive w t₂) X u := by
  intro hal
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hwc ht₂
  have ht₂0 : 0 ≤ t₂ := u.coe_nonneg.trans hut₂.le
  have hW0 : W 0 = 0 := by rw [hWdef, InteractingSLE.frozenDrive_zero ht₂0, hw0]
  have hu0' : (0 : ℝ) < u := NNReal.coe_pos.2 hu0
  have huζ : (u : ℝ≥0∞) ≤ ζ := by
    refine (lt_of_le_of_lt ?_ ht₂).le
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hut₂.le
  obtain ⟨r, hr, hnot⟩ := GB7a.exists_ball_notMem_fwdHull hW u.coe_nonneg (WangWu.isForwardSol_of_alive hW hal)
  have hUw : ∀ s : ℝ, 0 ≤ s → s < u → W s = w s.toNNReal := fun s hs0 hsu =>
    frozenDrive_eq ⟨hs0, hsu.le.trans hut₂.le⟩
  have hL' := GB7a.isLoewnerTraceLT_of_agree hg huζ hUw
  have hlimη := GB7a.tendsto_comp_toNNReal hg huζ hu0
  rw [hvis] at hlimη
  have hev : ∀ᶠ s in 𝓝[<] (u : ℝ), γ s.toNNReal ∈ ball (X : ℂ) (r / 2) :=
    hlimη (ball_mem_nhds _ (half_pos hr))
  obtain ⟨s, hs1, hs2⟩ := (hev.and (Ioo_mem_nhdsLT hu0')).exists
  have hcl := Supp7.G12.trace_mem_closure_fwdHull hW hW0 hL' hs2.1 hs2.2
  have hcl' : γ s.toNNReal ∈ closure (fwdHull W u) :=
    closure_mono (QuantumZipper.fwdHull_mono.1 hs2.2.le) hcl
  obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hcl' (r / 2) (half_pos hr)
  refine hnot z ?_ hzK
  rw [mem_ball] at hs1
  rw [← dist_eq_norm]
  linarith [dist_triangle z (γ s.toNNReal) (X : ℂ), dist_comm z (γ s.toNNReal)]

/-! ### The marks merged with the driver at a rightmost real visit -/

section Merge

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {B : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

/-- A mark beyond the visited rightmost real point is separated from the driver. -/
theorem w_lt_vR_of_lt (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ) (hg : IsGeneratingTrace w ζ γ)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ) {X : ℝ} (hX0 : 0 ≤ X)
    (hmax : ∀ s ≤ u, (γ s).im = 0 → (γ s).re ≤ X) {i : Fin nR} (hi : X < xR i) : w u < vR i u := by
  have hF := hp.isForcePath
  obtain ⟨t₂, hut₂, ht₂ζ⟩ := Supp7.G11.exists_real_gt_lt hu
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hF.continuousOn_w ht₂ζ
  set X'' : ℝ := (X + xR i) / 2 with hX''
  have hal : Alive W X'' u := by
    refine alive_of_trace_off hg hF.continuousOn_w hF.w_zero ht₂ζ hut₂ (by rw [hX'']; linarith) ?_
    intro s hs r hr hγ
    have h1 := hmax s hs (by rw [hγ]; simp)
    rw [hγ] at h1
    simp only [ofReal_re] at h1
    rw [hX''] at hr
    linarith
  have hvR := SideHeight.vR_eq_rightImg_frozenDrive hp ht₂ζ hut₂.le i
  have h1 : rightImg W X'' u ≤ rightImg W (xR i) u :=
    rightImg_mono_index hW u.coe_nonneg (by rw [hX'']; linarith)
  have h2 := rightImg_eq_gImg hW u.coe_nonneg hal
  have h3 := hal.lt_gImg hW ⟨u.coe_nonneg, le_rfl⟩
  have h4 : W u = w u := by
    rw [hWdef, frozenDrive_eq ⟨u.coe_nonneg, hut₂.le⟩, Real.toNNReal_coe]
  rw [hvR]
  linarith

/-- **A mark at or before the visited rightmost real point is merged with the driver** (`u > 0`): before `u` the
visited point `X` is alive and dominates the mark, `V^j − W ≤ g(X) − W`; the gap of `X` gets arbitrarily small just
before `u` (otherwise `X` would be alive at `u`, `Alive.of_forall_le_cflow`, contradicting `not_alive_of_visit`), so
`V^j_u = W_u` by continuity. -/
theorem vR_eq_w_of_le (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ) (hg : IsGeneratingTrace w ζ γ)
    (hinj : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {u : ℝ≥0} (hu0 : 0 < u) (hu : (u : ℝ≥0∞) < ζ) {X : ℝ}
    (hX0 : 0 < X) (hvis : γ u = X) (hmax : ∀ s ≤ u, (γ s).im = 0 → (γ s).re ≤ X) {i : Fin nR}
    (hi : xR i ≤ X) : vR i u = w u := by
  have hF := hp.isForcePath
  obtain ⟨t₂, hut₂, ht₂ζ⟩ := Supp7.G11.exists_real_gt_lt hu
  set W := frozenDrive w t₂ with hWdef
  have hW : Continuous W := continuous_frozenDrive_of_lt hF.continuousOn_w ht₂ζ
  have hWw : ∀ t : ℝ≥0, (t : ℝ) ≤ t₂ → W t = w t := fun t ht => by
    rw [hWdef, frozenDrive_eq ⟨t.coe_nonneg, ht⟩, Real.toNNReal_coe]
  -- `X` is alive strictly before `u`
  have hoff : ∀ t : ℝ≥0, t < u → ∀ s ≤ t, ∀ r : ℝ, X ≤ r → γ s ≠ r := by
    intro t htu s hs r hr hγ
    have h1 := hmax s (hs.trans htu.le) (by rw [hγ]; simp)
    rw [hγ] at h1
    simp only [ofReal_re] at h1
    have hrX : r = X := le_antisymm h1 hr
    have hsζ : (s : ℝ≥0∞) ≤ ζ := ((ENNReal.coe_le_coe.2 (hs.trans htu.le)).trans hu.le)
    have := hinj hsζ hu.le (by rw [hγ, hvis, hrX])
    exact absurd (this ▸ hs.trans_lt htu) (lt_irrefl _)
  have halive : ∀ t : ℝ≥0, t < u → Alive W X t := fun t htu =>
    alive_of_trace_off hg hF.continuousOn_w hF.w_zero ht₂ζ ((NNReal.coe_lt_coe.2 htu).trans hut₂) hX0
      (hoff t htu)
  have hnot := not_alive_of_visit hg hF.continuousOn_w hF.w_zero ht₂ζ hu0 hut₂ hvis
  -- the mark is dominated by `X` before `u`
  have hdom : ∀ t : ℝ≥0, t < u → vR i t - w t ≤ cflow W X t := fun t htu => by
    have htt₂ : (t : ℝ) ≤ t₂ := ((NNReal.coe_lt_coe.2 htu).trans hut₂).le
    rw [SideHeight.vR_eq_rightImg_frozenDrive hp ht₂ζ htt₂ i, ← hWw t htt₂]
    have h1 := rightImg_mono_index hW t.coe_nonneg hi (w := W)
    rw [rightImg_eq_gImg hW t.coe_nonneg (halive t htu), gImg] at h1
    linarith
  -- continuity of the gap at `u`
  have hcont : ContinuousAt (fun t => vR i t - w t) u := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact (((hF.continuousOn_vR i).sub hF.continuousOn_w).continuousAt (hopen.mem_nhds hu))
  refine le_antisymm ?_ (hF.w_le_vR hu i)
  suffices h : ∀ ε > 0, vR i u - w u < ε by
    by_contra hlt
    have := h (vR i u - w u) (by linarith)
    exact lt_irrefl _ this
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (half_pos hε)
  set s₀ : ℝ≥0 := u - min (δ / 2).toNNReal (u / 2) with hs₀
  have hmin_pos : 0 < min (δ / 2).toNNReal (u / 2) :=
    lt_min (Real.toNNReal_pos.2 (half_pos hδ)) (half_pos hu0)
  have hmin_le : min (δ / 2).toNNReal (u / 2) ≤ u := (min_le_right _ _).trans (half_le_self (by positivity))
  have hs₀u : s₀ < u := tsub_lt_self hu0 hmin_pos
  have hs₀δ : (u : ℝ) - s₀ < δ := by
    rw [hs₀, NNReal.coe_sub hmin_le]
    have h1 : ((min (δ / 2).toNNReal (u / 2) : ℝ≥0) : ℝ) ≤ δ / 2 := by
      calc ((min (δ / 2).toNNReal (u / 2) : ℝ≥0) : ℝ) ≤ ((δ / 2).toNNReal : ℝ) := by
            exact_mod_cast min_le_left _ _
        _ = δ / 2 := Real.coe_toNNReal _ (by linarith)
    linarith
  -- a time in `[s₀, u)` where the gap of `X` is below `ε / 2`
  obtain ⟨s, hs₀s, hsu, hcs⟩ : ∃ s : ℝ, (s₀ : ℝ) ≤ s ∧ s < u ∧ cflow W X s < ε / 2 := by
    by_contra hno
    push Not at hno
    refine hnot (Alive.of_forall_le_cflow hW (halive s₀ hs₀u) s₀.coe_nonneg (half_pos hε) fun t ht hal => ?_)
    rcases lt_or_eq_of_le ht.2 with htu | htu
    · exact hno t ht.1 htu
    · exact absurd (htu ▸ hal) hnot
  have hs0 : 0 ≤ s := s₀.coe_nonneg.trans hs₀s
  set s' : ℝ≥0 := s.toNNReal with hs'
  have hs'u : s' < u := by rw [hs', Real.toNNReal_lt_iff_lt_coe hs0]; exact hsu
  have hs'coe : (s' : ℝ) = s := Real.coe_toNNReal _ hs0
  have hd := hdom s' hs'u
  rw [hs'coe] at hd
  have hdist : dist s' u < δ := by
    rw [NNReal.dist_eq, hs'coe, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have h1 := hδc hdist
  rw [Real.dist_eq] at h1
  have h2 := (abs_lt.1 h1).1
  linarith

/-- **The right marks merged with the driver at a rightmost real visit** are exactly those at positions `≤ X`. -/
theorem vR_eq_w_iff (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ) (hg : IsGeneratingTrace w ζ γ)
    (hinj : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ) {X : ℝ} (hvis : γ u = X)
    (hmax : ∀ s ≤ u, (γ s).im = 0 → (γ s).re ≤ X) (i : Fin nR) : vR i u = w u ↔ xR i ≤ X := by
  have hF := hp.isForcePath
  have hγ0 : γ 0 = 0 := hg.1
  have hX0 : 0 ≤ X := by
    have := hmax 0 zero_le (by rw [hγ0]; simp)
    rwa [hγ0, Complex.zero_re] at this
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0
  · subst hu0
    have hX : X = 0 := by
      have := congrArg Complex.re (hvis.symm.trans hγ0)
      simpa using this
    have hxi : 0 ≤ xR i := by
      have := hF.w_le_vR hu i
      rwa [hF.w_zero, hF.vR_zero] at this
    rw [hF.vR_zero, hF.w_zero, hX]
    exact ⟨fun h => h.le, fun h => le_antisymm h hxi⟩
  · have hXpos : 0 < X := by
      refine lt_of_le_of_ne hX0 fun hX => ?_
      have h1 : γ u = γ 0 := by rw [hvis, hγ0, ← hX]; simp
      have := hinj hu.le (by simp) h1
      exact absurd this hu0.ne'
    constructor
    · intro he
      by_contra hlt
      exact absurd he (ne_of_gt (w_lt_vR_of_lt hp hg hu hX0 hmax (not_le.1 hlt)))
    · exact vR_eq_w_of_le hp hg hinj hu0 hu hXpos hvis hmax

/-- **Continuation past a rightmost real visit**: the right marks at positions `≤ X` have weight sum `> −2` (the
threshold condition fails at `u < ζ`, and they are the marks merged with the driver). -/
theorem neg_two_lt_sum_of_visit (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR B ζ)
    (hg : IsGeneratingTrace w ζ γ) (hinj : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ}) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ)
    {X : ℝ} (hvis : γ u = X) (hmax : ∀ s ≤ u, (γ s).im = 0 → (γ s).re ≤ X) :
    -2 < ∑ i ∈ Finset.univ.filter (fun i => xR i ≤ X), ρR i := by
  have hth := hp.isForcePath.not_threshold hu
  unfold ForceWord.ThresholdCondition at hth
  push Not at hth
  have he : Finset.univ.filter (fun i => vR i u = w u) = Finset.univ.filter (fun i => xR i ≤ X) :=
    Finset.filter_congr fun i _ => vR_eq_w_iff hp hg hinj hu hvis hmax i
  rw [← he]
  exact hth.2

end Merge

/-! ### The swallowed right force sum of the flow-line word -/

section Sum

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- The right marks of the flow-line word are the seed `0` and the genuine jumps `z > x`, at `z − x`. -/
theorem flowLineXR_cases (x : ℝ) (i : Fin (flowLineNR b J x)) :
    flowLineXR b J x i = 0 ∨ ∃ z ∈ J, x < z ∧ flowLineXR b J x i = z - x := by
  revert i
  unfold flowLineXR flowLineNR
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Or.inl (Fin.cons_zero _ _)
  · right
    have hmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (x < ·)) rfl j
    rw [Finset.mem_filter] at hmem
    exact ⟨_, (Finset.mem_filter.1 hmem.1).1, hmem.2, Fin.cons_succ _ _ _⟩

/-- A gap to the right of a point free of jump candidates. -/
theorem exists_gap (J : Finset ℝ) (c : ℝ) : ∃ ε > 0, ∀ z ∈ J, c < z → c + ε ≤ z := by
  rcases (J.filter (c < ·)).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun z hz hcz => ?_⟩
    have : z ∈ J.filter (c < ·) := Finset.mem_filter.2 ⟨hz, hcz⟩
    rw [he] at this
    exact absurd this (Finset.notMem_empty z)
  · refine ⟨(J.filter (c < ·)).min' hne - c, ?_, fun z hz hcz => ?_⟩
    · have := (Finset.mem_filter.1 ((J.filter (c < ·)).min'_mem hne)).2
      linarith
    · have := (J.filter (c < ·)).min'_le z (Finset.mem_filter.2 ⟨hz, hcz⟩)
      linarith

/-- **The swallowed right force sum** of the flow-line word from `x` at angle `θ`, up to a position `X ≥ 0`:
`∑_{x^{i,R} ≤ X} ρ^{i,R} = (b((x + X)⁺) + θχ)/λ − 1`. -/
theorem sum_filter_flowLineXR_le {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (x θ : ℝ)
    {X : ℝ} (hX : 0 ≤ X) :
    ∑ i ∈ Finset.univ.filter (fun i => flowLineXR b J x i ≤ X), flowLineRhoR κ b J x θ i =
      (rightLim b (X + x) + θ * chiC κ) / sleLambda κ - 1 := by
  have hΛ : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  obtain ⟨ε, hε, hgap⟩ := exists_gap J (X + x)
  set y : ℝ := X + ε / 2 with hy
  have hy0 : 0 < y := by rw [hy]; linarith
  have hyJ : y + x ∉ J := fun h => by
    have := hgap _ h (by rw [hy]; linarith)
    rw [hy] at this
    linarith
  -- no mark in `(X, y]`
  have hfilt : Finset.univ.filter (fun i => flowLineXR b J x i ≤ X) =
      Finset.univ.filter (fun i => flowLineXR b J x i ≤ y) := by
    refine Finset.filter_congr fun i _ => ⟨fun h => h.trans (by rw [hy]; linarith), fun h => ?_⟩
    rcases flowLineXR_cases x i with h0 | ⟨z, hz, hxz, he⟩
    · rw [h0]; exact hX
    · by_contra hlt
      rw [he] at h hlt
      have := hgap z hz (by linarith)
      rw [hy] at h
      linarith
  rw [hfilt, Exist.sum_filter_flowLineXR_seed x θ hy0 hyJ]
  have htel := Exist.eq_rightLim_add_sum_seed hb (x := x) (y := y + x) (by linarith) hyJ
  -- `b` is constant on `(X + x, X + x + ε)`
  have hconst : ∀ t ∈ Ioo (X + x) (X + x + ε), b t = b (y + x) := by
    intro t ht
    have hfree : ∀ z ∈ Icc (min t (y + x)) (max t (y + x)), z ∉ J := fun z hz hzJ => by
      have h1 : X + x < z := lt_of_lt_of_le (lt_min ht.1 (by rw [hy]; linarith)) hz.1
      have h2 : z < X + x + ε := lt_of_le_of_lt hz.2 (max_lt ht.2 (by rw [hy]; linarith))
      have := hgap z hzJ h1
      linarith
    rcases le_total t (y + x) with h | h
    · exact (Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb h fun z hz => hfree z
        ⟨(min_le_left _ _).trans hz.1, hz.2.trans (le_max_right _ _)⟩).symm
    · exact Sec4.eq_of_forall_notMem_of_isPiecewiseConstant hb h fun z hz => hfree z
        ⟨(min_le_right _ _).trans hz.1, hz.2.trans (le_max_left _ _)⟩
  have hR : rightLim b (X + x) = b (y + x) := Sec4.rightLim_eq_of_forall (by linarith) hconst
  rw [hR, htel]
  field_simp
  ring

end Sum

/-! ### Flow lines -/

/-- **The junction continuation inequality for flow lines** (`FlowLineJunctionStatement`; proof of Lemma 7.6,
p. 269). Almost surely: the trace is simple (Aux. lemma 25) and generated by the coupling's driver, whose path satisfies
`IsIntegratedSLEPath`; at a rightmost real visit `η(u) = x_R`, `u < ζ`, the right marks at positions `≤ x_R − x` are
merged with the driver and their weight sum `(b(x_R⁺) + θχ)/λ − 1` exceeds `−2`. -/
theorem flowLineJunctionStatement : FlowLineJunctionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ Ω _ P _ h η ζ hη
  have hpg := Restart.ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, htr⟩ := hη
  filter_upwards [hcoup.1.2.2.2.2, htr, hpg] with ω hωp hωt hωg
  intro u hu him hmax
  set γ : ℝ≥0 → ℂ := fun t => η ω t - x with hγ
  set X : ℝ := (η ω u).re - x with hX
  have hγ0 : η ω 0 = x := Sec7.IsPathGood.zero hωg
  have hinj : InjOn γ {t | (t : ℝ≥0∞) ≤ ζ ω} := fun s hs t ht he =>
    hωg.1 hs ht (sub_left_injective he)
  have hvis : γ u = X := by
    rw [hγ, hX]
    apply Complex.ext <;> simp [him]
  have hmax' : ∀ s ≤ u, (γ s).im = 0 → (γ s).re ≤ X := fun s hs hs0 => by
    have h0 : (η ω s).im = 0 := by simpa [hγ] using hs0
    have h1 := hmax s hs h0
    simp only [hγ, hX, sub_re, ofReal_re]
    linarith
  have hX0 : 0 ≤ X := by
    have h1 := hmax 0 zero_le (by rw [hγ0]; simp)
    rw [hγ0, ofReal_re] at h1
    rw [hX]
    linarith
  have hsum := neg_two_lt_sum_of_visit hωp hωt hinj hu hvis hmax'
  rw [sum_filter_flowLineXR_le hκ hb x θ hX0] at hsum
  have hXx : X + x = (η ω u).re := by rw [hX]; ring
  rw [hXx] at hsum
  have hl := Sec4.sleLambda_pos hκ
  have h1 : -1 < (rightLim b (η ω u).re + θ * chiC κ) / sleLambda κ := by linarith
  rw [lt_div_iff₀ hl] at h1
  linarith

end Lemma76E

end Sec7

end InteractingSLE
