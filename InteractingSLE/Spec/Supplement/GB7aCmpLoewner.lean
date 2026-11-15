/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux25Real
import InteractingSLE.Spec.Dimension.FiniteCover
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite

/-!
# GB7a's pathwise comparison input: deterministic Loewner facts

Packet PROVE-GB7A3. Deterministic facts about a chordal Loewner chain driven by a continuous `U : ℝ → ℝ`
(`U 0 = 0`) with a continuous trace `η` before a horizon (`IsLoewnerTraceLT`), used to prove the pathwise half of
Lemma GB7a's proof (`GB7a.GB7aCmpInput`, `GB7aB.lean`):

* `exists_ball_notMem_fwdHull`: near a real point alive at time `t` no point of `ℍ` is swallowed by `t`;
* `not_isForwardSol_of_tendsto`: a real point approached by the trace from `ℍ` (with `η(s) ∈ K_s`) is not alive
  at the limit time;
* `exists_isForwardSol_of_le`: an alive real point stays alive as long as a force coordinate below it stays
  bounded away from the driver;
* `exists_isForwardSol_of_mem_closure`: a nonzero real point off the prefix `η([0, t])` and in the closure of
  `ℍ \ K_t` is alive at `t`;
* `IsLoewnerTraceLT.chart_of_mem_H`: a later trace point in `ℍ` off the prefix is an interior point of the chart
  at time `q`: its chart image is the shifted tip, in `ℍ`, and it lies in `ℍ \ K_q`;
* `isForwardSol_shift_of_centred`: a nonvanishing centred force coordinate is a forward solution in the chart;
* `lt_re_of_centred`, `re_lt_of_centred`: **strict order** between a force coordinate and the real flow of an
  alive point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open QuantumZipper.RS (shiftDrive)
open Aux25 (exists_real_of_isForwardSol pos_of_ne_zero_of_pos sub_le_max_of_centredEq isForwardSol_shift)

variable {U : ℝ → ℝ}

/-! ### Alive real points and the hulls -/

/-- Near a real point alive at time `t`, no point is swallowed by `t`. -/
theorem exists_ball_notMem_fwdHull (hU : Continuous U) {y t : ℝ} (ht : 0 ≤ t) {v : ℝ → ℂ}
    (hv : IsForwardSol U (y : ℂ) t v) :
    ∃ r > 0, ∀ z : ℂ, ‖z - y‖ < r → z ∉ fwdHull U t := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hv
  have hE : 0 < Real.exp (2 / δ ^ 2 * t) := Real.exp_pos _
  refine ⟨δ / Real.exp (2 / δ ^ 2 * t), div_pos hδ hE, fun z hzy hz => ?_⟩
  exact not_mem_fwdHull_of_isForwardSol hU hv hδ hlow hz.1 (by rwa [lt_div_iff₀ hE] at hzy) hz

/-- **A real limit point of the trace is not alive at the limit time.** If `η(s) ∈ K_s` for `s ∈ [p, T)` and
`η(s) → y ∈ ℝ` as `s ↑ T`, then `y` is not alive on `[0, T]`. -/
theorem not_isForwardSol_of_tendsto (hU : Continuous U) {p T : ℝ} (hpT : p < T) (hT : 0 ≤ T)
    {η : ℝ → ℂ} (hmem : ∀ s ∈ Ico p T, η s ∈ fwdHull U s) {y : ℝ}
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) : ¬ ∃ v, IsForwardSol U (y : ℂ) T v := by
  rintro ⟨v, hv⟩
  obtain ⟨r, hr, hnot⟩ := exists_ball_notMem_fwdHull hU hT hv
  have h1 : ∀ᶠ s in 𝓝[<] T, η s ∈ ball (y : ℂ) r := hlim (ball_mem_nhds _ hr)
  have h2 : ∀ᶠ s in 𝓝[<] T, s ∈ Ico p T := Ico_mem_nhdsLT hpT
  obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
  rw [mem_ball, dist_eq_norm] at hs1
  exact hnot (η s) hs1 (QuantumZipper.fwdHull_mono.1 hs2.2.le (hmem s hs2))

/-- **Extension of an alive real point along a force coordinate bounded below.** Let `y > 0` be alive on
`[0, q]` (solution `v`), and let `u` solve the centred equation on every `[q, s]`, `s < T`, with `u ≥ c > 0` on
`[q, T)` and `u(q) ≤ Re v(q)`. Then `y` is alive on `[0, T]`: its real flow stays above `u`. -/
theorem exists_isForwardSol_of_le (hU : Continuous U) (hU0 : U 0 = 0) {y q T c : ℝ} (hy : 0 < y)
    (hq : 0 ≤ q) (hqT : q ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol U (y : ℂ) q v) (hc : 0 < c)
    {u : ℝ → ℝ}
    (hu : ∀ s ∈ Ico q T, ContinuousOn u (Icc q s) ∧
      (∀ s₁ ∈ Icc q s, ∀ s₂ ∈ Icc q s, s₁ ≤ s₂ →
        u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r) ∧
      IntervalIntegrable (fun r => 2 / u r) volume q s)
    (hcu : ∀ s ∈ Ico q T, c ≤ u s) (huq : u q ≤ (v q).re) :
    ∃ v', IsForwardSol U (y : ℂ) T v' := by
  by_contra hdead
  obtain ⟨σ, hσ, hsw⟩ := exists_realSwallowAt hU hU0 hy (hq.trans hqT) hdead
  have hqσ : q < σ := by
    by_contra hle
    push Not at hle
    exact hsw.2.2 ⟨v, QuantumZipper.isForwardSol_restrict hv hσ.1.le hle⟩
  obtain ⟨c₀, hc₀, hc₀le⟩ := exists_pos_le_re_of_isForwardSol hU hU0 hy hq hv
  refine hsw.2.2 (exists_isForwardSol_of_forall_lt hU hU0 hσ.1 (fun s hs => hsw.2.1 s hs)
    (lt_min hc hc₀) fun s hs => ?_)
  rcases le_or_gt s q with hsq | hsq
  · rw [fwdMap_eq_of_isForwardSol hU hv ⟨hs.1, hsq⟩]
    exact (min_le_right _ _).trans (hc₀le s ⟨hs.1, hsq⟩)
  obtain ⟨vs, hvs⟩ := hsw.2.1 s hs
  obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := exists_real_of_isForwardSol hU hs.1 hvs
  rw [hU0, sub_zero] at hX0
  have hXpos : ∀ r ∈ Icc (0 : ℝ) s, 0 < X r :=
    pos_of_ne_zero_of_pos hXc (fun r hr => (hXv r hr).1) (by rw [hX0]; exact hy)
  have hsub : Icc q s ⊆ Icc 0 s := Icc_subset_Icc_left hq
  have hsT : s ∈ Ico q T := ⟨hsq.le, hs.2.trans_le hσ.2⟩
  obtain ⟨huc, hueq, huint⟩ := hu s hsT
  have hnull : volume {r | r ∈ Icc q s ∧ X r = 0} = 0 :=
    measure_mono_null (fun r hr => absurd hr.2 (hXpos r (hsub hr.1)).ne') measure_empty
  have hXint' : IntervalIntegrable (fun r => 2 / X r) volume q s :=
    hXint.mono_set (by rw [uIcc_of_le hsq.le, uIcc_of_le hs.1]; exact hsub)
  have hcmp := sub_le_max_of_centredEq (W := U) (u := X) (X := u) (hXc.mono hsub)
    (fun r hr => (hXpos r (hsub hr)).le)
    (fun s₁ h₁ s₂ h₂ h₁₂ => hXeq s₁ (hsub h₁) s₂ (hsub h₂) h₁₂) hXint' hnull huc hueq huint s
    ⟨hsq.le, le_rfl⟩
  have hXq : X q = (v q).re := by
    have e1 := fwdMap_eq_of_isForwardSol hU hvs ⟨hq, hsq.le⟩
    have e2 := fwdMap_eq_of_isForwardSol hU hv ⟨hq, le_rfl⟩
    rw [(hXv q ⟨hq, hsq.le⟩).2] at e1
    rw [← e2, e1, Complex.ofReal_re]
  have hmax : max (u q - X q) 0 = 0 := max_eq_right (by rw [hXq]; linarith)
  rw [hmax] at hcmp
  rw [fwdMap_eq_of_isForwardSol hU hvs ⟨hs.1, le_rfl⟩, (hXv s ⟨hs.1, le_rfl⟩).2, Complex.ofReal_re]
  have := hcu s hsT
  exact (min_le_left _ _).trans (by linarith)

/-- **A nonzero real point off the prefix and in the closure of `ℍ \ K_t` is alive at `t`.** A small disc
around it misses the prefix; its upper half is connected and meets the unbounded part `ℍ \ K_t`, so it misses
the filling `K_t`. -/
theorem exists_isForwardSol_of_mem_closure (hU : Continuous U) (hU0 : U 0 = 0) {T' : ℝ}
    {η : ℝ → ℂ} (hη : IsLoewnerTraceLT U T' η) {t : ℝ} (ht : 0 ≤ t) (htT : t < T') {y : ℝ}
    (hy0 : y ≠ 0) (hyη : (y : ℂ) ∉ η '' Icc 0 t) (hcl : (y : ℂ) ∈ closure (H \ fwdHull U t)) :
    ∃ v, IsForwardSol U (y : ℂ) t v := by
  set A := η '' Icc 0 t with hA
  have hAc : IsClosed A := (hη.isCompact_image htT).isClosed
  obtain ⟨r, hr, hrA⟩ : ∃ r > 0, ball (y : ℂ) r ⊆ Aᶜ := Metric.isOpen_iff.1 hAc.isOpen_compl _ hyη
  refine ZhanGT4.exists_isForwardSol_of_disjoint_ball hU hU0 hy0 ht hr ?_
  rw [Set.disjoint_left]
  intro z hzb hzK
  have hK : fwdHull U t = fillH A := hη.2.2 t ht htT
  obtain ⟨w', hw'S, hdist⟩ := Metric.mem_closure_iff.1 hcl r hr
  set S : Set ℂ := ball (y : ℂ) r ∩ H with hSdef
  have hSpre : IsPreconnected S := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hSsub : S ⊆ H \ closure A := fun z' hz' => ⟨hz'.2, by rw [hAc.closure_eq]; exact hrA hz'.1⟩
  have hzS : z ∈ S := ⟨hzb, (QuantumZipper.fwdHull_mono.2 t) hzK⟩
  have hw'S' : w' ∈ S := ⟨by rw [mem_ball, dist_comm]; exact hdist, hw'S.1⟩
  have hcomp := hSpre.subset_connectedComponentIn hzS hSsub hw'S'
  rw [hK] at hzK
  have hzb' : Bornology.IsBounded (connectedComponentIn (H \ closure A) z) := by
    rcases hzK.2 with h | h
    · exact absurd h (hSsub hzS).2
    · exact h
  rw [connectedComponentIn_eq hcomp] at hzb'
  exact hw'S.2 (by rw [hK]; exact ⟨hw'S.1, Or.inr hzb'⟩)

/-! ### The chart at time `q` -/

/-- **A later trace point in `ℍ` off the prefix is interior in the chart at `q`.** Its chart image
`f_q(η(q + u))` is the shifted tip `γ_q(u)`, which lies in `ℍ`, and `η(q + u) ∈ ℍ \ K_q`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.chart_of_mem_H {T' : ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTraceLT U T' η) (hU : Continuous U) (hU0 : U 0 = 0) {q u : ℝ} (hq : 0 ≤ q)
    (hu : 0 ≤ u) (hquT : q + u < T') (hH : η (q + u) ∈ H) (hnot : η (q + u) ∉ η '' Icc 0 q) :
    loewnerTip (shiftDrive U q) u ∈ H ∧ fwdMap U q (η (q + u)) = loewnerTip (shiftDrive U q) u ∧
      η (q + u) ∈ H \ fwdHull U q := by
  have hS := (hη.isLoewnerTraceLT_shift hU hU0 hq).1
  have hUS := QuantumZipper.RS.continuous_shiftDrive hU q
  have hUS0 := QuantumZipper.RS.shiftDrive_zero U q
  have huT : u < T' - q := by linarith
  have htr := hS.trace_eq hUS hUS0 hu huT
  have hlim := hS.tendsto_fwdMapInv_mul_I hUS hUS0 hu huT
  rw [← htr] at hlim
  rcases hη.mem_image_or_mem_prefix hU hU0 hq hu hquT hlim hH with ⟨h1, h2⟩ | h
  · rw [htr] at h1 h2
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hq h1]
    · rw [h2]
      exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hq h1
  · exact absurd h hnot

/-- **A nonvanishing centred force coordinate is a forward solution in the chart at `a`.** -/
theorem isForwardSol_shift_of_centred {a b : ℝ} (hab : a ≤ b) {u : ℝ → ℝ}
    (huc : ContinuousOn u (Icc a b)) (hne : ∀ s ∈ Icc a b, u s ≠ 0)
    (hueq : ∀ s₁ ∈ Icc a b, ∀ s₂ ∈ Icc a b, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r) :
    IsForwardSol (shiftDrive U a) (u a : ℂ) (b - a) (fun s => (u (a + s) : ℂ)) := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) (b - a), a + s ∈ Icc a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.continuous_ofReal.comp_continuousOn
      (huc.comp (continuous_const.add continuous_id).continuousOn hmem)
  · show ((u (a + s) : ℝ) : ℂ) ≠ 0
    exact_mod_cast hne _ (hmem s hs)
  · have h1 := hueq a ⟨le_rfl, hab⟩ (a + s) (hmem s hs) (by linarith [hs.1])
    have h2 : (∫ r in a..(a + s), 2 / u r) = ∫ r in (0 : ℝ)..s, 2 / u (a + r) := by
      rw [intervalIntegral.integral_comp_add_left (fun r => 2 / u r) a, add_zero]
    have h3 : (∫ r in (0 : ℝ)..s, (2 : ℂ) / (u (a + r) : ℂ)) =
        ((∫ r in (0 : ℝ)..s, 2 / u (a + r) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r _ => ?_
      push_cast
      rfl
    have h4 : u (a + s) = u a - (U (a + s) - U a) + ∫ r in (0 : ℝ)..s, 2 / u (a + r) := by
      rw [← h2]
      linarith
    rw [h3]
    simp only [shiftDrive]
    rw [h4]
    push_cast
    ring

/-- A nonvanishing centred force coordinate on `[0, b]` is a forward solution of `U` itself (`U 0 = 0`). -/
theorem isForwardSol_of_centred (hU0 : U 0 = 0) {b : ℝ} (hb : 0 ≤ b) {u : ℝ → ℝ}
    (huc : ContinuousOn u (Icc 0 b)) (hne : ∀ s ∈ Icc 0 b, u s ≠ 0)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) b, ∀ s₂ ∈ Icc (0 : ℝ) b, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r) :
    IsForwardSol U (u 0 : ℂ) b (fun s => (u s : ℂ)) := by
  have h := isForwardSol_shift_of_centred (U := U) hb huc hne hueq
  have e : shiftDrive U 0 = U := by
    funext r
    simp [shiftDrive, hU0]
  rw [e, sub_zero] at h
  simpa only [zero_add] using h

/-! ### Strict order between a force coordinate and an alive real point -/

/-- **A force coordinate starting below an alive real point stays strictly below it.** Let `y > 0` be alive on
`[0, q]` (solution `v`) and let `u ≥ 0` solve the centred equation on `[0, q]` with `u(0) < y`. Then
`u(q) < Re v(q)`. After the last zero of `u` both are positive solutions, which keep their strict order. -/
theorem lt_re_of_centred (hU : Continuous U) (hU0 : U 0 = 0) {y q : ℝ} (hy : 0 < y) (hq : 0 ≤ q)
    {v : ℝ → ℂ} (hv : IsForwardSol U (y : ℂ) q v) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 q))
    (hu0 : ∀ s ∈ Icc 0 q, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) q, ∀ s₂ ∈ Icc (0 : ℝ) q, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r)
    (h0 : u 0 < y) : u q < (v q).re := by
  obtain ⟨X, hXc, hXv, hX0, -, -⟩ := exists_real_of_isForwardSol hU hq hv
  rw [hU0, sub_zero] at hX0
  have hXpos : ∀ r ∈ Icc (0 : ℝ) q, 0 < X r :=
    pos_of_ne_zero_of_pos hXc (fun r hr => (hXv r hr).1) (by rw [hX0]; exact hy)
  have hvX : ∀ r ∈ Icc (0 : ℝ) q, (v r).re = X r := fun r hr => by
    rw [(hXv r hr).2, Complex.ofReal_re]
  by_cases huq : u q = 0
  · rw [huq, hvX q ⟨hq, le_rfl⟩]
    exact hXpos q ⟨hq, le_rfl⟩
  -- a restart time `a` after which `u > 0`, with `u a < X a`
  suffices key : ∃ a ∈ Icc (0 : ℝ) q, (∀ s ∈ Icc a q, 0 < u s) ∧ u a < X a by
    obtain ⟨a, ha, hpos, hlt⟩ := key
    have hsolu := isForwardSol_shift_of_centred (U := U) ha.2 (huc.mono (Icc_subset_Icc_left ha.1))
      (fun s hs => (hpos s hs).ne') (fun s₁ h₁ s₂ h₂ h₁₂ =>
        hueq s₁ ⟨ha.1.trans h₁.1, h₁.2⟩ s₂ ⟨ha.1.trans h₂.1, h₂.2⟩ h₁₂)
    have hsolv := isForwardSol_shift hv ha.1 ha.2
    rw [(hXv a ha).2] at hsolv
    have h := re_lt_of_isForwardSol (QuantumZipper.RS.continuous_shiftDrive hU a)
      (QuantumZipper.RS.shiftDrive_zero U a) (hpos a ⟨le_rfl, ha.2⟩) hlt hsolu hsolv (q - a)
      ⟨sub_nonneg.2 ha.2, le_rfl⟩
    simp only [add_sub_cancel, Complex.ofReal_re] at h
    exact h
  by_cases hz : ∃ s ∈ Icc (0 : ℝ) q, u s = 0
  · set Z := {s | s ∈ Icc (0 : ℝ) q ∧ u s = 0} with hZ
    have hZc : IsClosed Z := by
      have := huc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0 : ℝ)))
      simpa [hZ, Set.preimage, Set.inter_def, and_comm] using this
    have hZb : BddAbove Z := ⟨q, fun s hs => hs.1.2⟩
    have hZne : Z.Nonempty := let ⟨s, hs, hs0⟩ := hz; ⟨s, hs, hs0⟩
    set s₀ := sSup Z with hs₀
    have hs₀Z : s₀ ∈ Z := hZc.csSup_mem hZne hZb
    rcases hs₀Z.1.2.lt_or_eq with hs₀q | hs₀q
    · -- after the last zero `s₀ < q`
      have hgt : ∀ s ∈ Ioc s₀ q, 0 < u s := fun s hs => by
        refine lt_of_le_of_ne (hu0 s ⟨hs₀Z.1.1.trans hs.1.le, hs.2⟩) fun h => ?_
        have : s ≤ s₀ := le_csSup hZb ⟨⟨hs₀Z.1.1.trans hs.1.le, hs.2⟩, h.symm⟩
        exact absurd hs.1 (not_lt.2 this)
      have hD : 0 < X s₀ - u s₀ := by rw [hs₀Z.2, sub_zero]; exact hXpos s₀ hs₀Z.1
      have hcw : ContinuousWithinAt (fun s => X s - u s) (Icc s₀ q) s₀ :=
        ((hXc.sub huc).mono (Icc_subset_Icc_left hs₀Z.1.1)) s₀ ⟨le_rfl, hs₀q.le⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hcw _ hD
      set a := min (s₀ + δ / 2) q with ha
      have has₀ : s₀ < a := lt_min (by linarith) hs₀q
      have haq : a ≤ q := min_le_right _ _
      have hdist : dist a s₀ < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.2 has₀)]
        have : a ≤ s₀ + δ / 2 := min_le_left _ _
        linarith
      have hclose := hball ⟨has₀.le, haq⟩ hdist
      rw [Real.dist_eq] at hclose
      refine ⟨a, ⟨hs₀Z.1.1.trans has₀.le, haq⟩, fun s hs => hgt s ⟨has₀.trans_le hs.1, hs.2⟩, ?_⟩
      have := neg_abs_le (X a - u a - (X s₀ - u s₀))
      linarith
    · -- the last zero is `q`: excluded
      exact absurd (hs₀q ▸ hs₀Z.2) huq
  · push Not at hz
    exact ⟨0, ⟨le_rfl, hq⟩, fun s hs => lt_of_le_of_ne (hu0 s hs) (hz s hs).symm, by rw [hX0]; exact h0⟩

/-- **A force coordinate starting above an alive real point stays strictly above it.** Let `y > 0` be alive on
`[0, q]` (solution `v`) and let `u ≥ 0` solve the centred equation on `[0, q]` (integrable reciprocal, null zero
set) with `y < u(0)`. Then `Re v(q) < u(q)`: `u` stays above the real flow of `y`, hence positive, so both are
positive solutions keeping their strict order. -/
theorem re_lt_of_centred (hU : Continuous U) (hU0 : U 0 = 0) {y q : ℝ} (hy : 0 < y) (hq : 0 ≤ q)
    {v : ℝ → ℂ} (hv : IsForwardSol U (y : ℂ) q v) {u : ℝ → ℝ} (huc : ContinuousOn u (Icc 0 q))
    (hu0 : ∀ s ∈ Icc 0 q, 0 ≤ u s)
    (hueq : ∀ s₁ ∈ Icc (0 : ℝ) q, ∀ s₂ ∈ Icc (0 : ℝ) q, s₁ ≤ s₂ →
      u s₂ - u s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / u r)
    (huint : IntervalIntegrable (fun s => 2 / u s) volume 0 q)
    (hnull : volume {s | s ∈ Icc (0 : ℝ) q ∧ u s = 0} = 0) (h0 : y < u 0) : (v q).re < u q := by
  obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := exists_real_of_isForwardSol hU hq hv
  rw [hU0, sub_zero] at hX0
  have hXpos : ∀ r ∈ Icc (0 : ℝ) q, 0 < X r :=
    pos_of_ne_zero_of_pos hXc (fun r hr => (hXv r hr).1) (by rw [hX0]; exact hy)
  have hcmp := sub_le_max_of_centredEq (W := U) (u := u) (X := X) huc hu0 hueq huint hnull hXc hXeq hXint
  have hmax : max (X 0 - u 0) 0 = 0 := max_eq_right (by rw [hX0]; linarith)
  have hupos : ∀ s ∈ Icc (0 : ℝ) q, 0 < u s := fun s hs => by
    have h1 := hcmp s hs
    rw [hmax] at h1
    linarith [hXpos s hs]
  have hsolu := isForwardSol_of_centred hU0 hq huc (fun s hs => (hupos s hs).ne') hueq
  have h := re_lt_of_isForwardSol hU hU0 hy h0 hv hsolu q ⟨hq, le_rfl⟩
  simpa only [Complex.ofReal_re] using h

end GB7a

end InteractingSLE
