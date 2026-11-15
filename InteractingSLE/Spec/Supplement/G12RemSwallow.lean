/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Core
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Foundations.Loewner.FiniteEndpoint

/-!
# Lemma G12's remainder: swallowing versus visiting a right mark (deterministic)

Packet PROVE-G12B. Supplement §7.9, proof of Lemma G12 (`source/spec/p481-528.md` L588–L590): "The first visit to
`x_j` must occur at its first swallowing time. If it was previously swallowed at a strictly farther real endpoint,
then `x_j` has a trace-free upper half-neighborhood inside that filled hull and cannot subsequently be visited from
the active domain. […] At `τ`, every farther right mark remains separated from the driver".

For one path of an integrated `SLE_κ(ρ)` evolution (its force part `Sec2.IsForcePath`) with a continuous generating
trace `η`, and a right mark `y = x_j > 0`:

* `trace_ne_of_gap_eq_zero`: **a mark swallowed off the prefix is never visited.** If `V^j_u = W_u` at some
  `u < ζ` and `η ≠ y` on `[0, u]`, then `η ≠ y` on `[0, ζ]` (a half-disc around `y` lies in `K_u`);
* `tendsto_gap_eq_zero_of_visit`: at a visit `η(T) = y` with `y` alive before `T`, the gap `V^j − W` tends to `0`;
* `tendsto_gap_pos_of_visit`: **at such a visit every farther right mark is alive**: `V^k − W` has a positive limit
  at `T⁻` for `x_k > y` (the ray lemma `FiniteEndpoint.not_tendsto_fwdMap_of_disjoint_ray`: the trace on `[0, T]`
  stays off `[x_k, ∞)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE

namespace Supp7

namespace G12

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-! ### Separated right marks are forward solutions -/

/-- **A right force point separated from the driver before `T ≤ ζ` solves the centred forward flow** on `[0, r]`,
`r < T`, for every driver `U` agreeing with `w` before `T` (`Sec2.IsForcePath.isForwardSol_gapR` with `T ≤ ζ`). -/
theorem isForwardSol_gapR_of_le (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {T : ℝ≥0}
    (hTζ : (T : ℝ≥0∞) ≤ ζ) {j : Fin nR} (hgap : ∀ t : ℝ≥0, t < T → w t < vR j t) {U : ℝ → ℝ}
    (hU : ∀ r : ℝ, 0 ≤ r → r < T → U r = w r.toNNReal) {r : ℝ} (hr : r < T) :
    IsForwardSol U (xR j : ℂ) r (Sec2.IsForcePath.gapR vR w j) := by
  have hlt : ∀ s ∈ Icc (0 : ℝ) r, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs => by
    refine lt_of_lt_of_le ?_ hTζ
    rw [ENNReal.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hs.1]
    exact hs.2.trans_lt hr
  have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) r) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun s hs =>
    hlt s hs
  refine ⟨?_, fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.continuous_ofReal.comp_continuousOn
      (((h.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps).sub
        (h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps))
  · have hsT : s.toNNReal < T := by
      rw [Real.toNNReal_lt_iff_lt_coe hs.1]; exact hs.2.trans_lt hr
    simp only [Sec2.IsForcePath.gapR, ne_eq, Complex.ofReal_eq_zero, sub_eq_zero]
    exact (hgap _ hsT).ne'
  · have hs0 : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1
    have hveq := h.vR_eq (hlt s hs) j
    rw [hs0] at hveq
    have hint : (∫ q in (0 : ℝ)..s, (2 : ℂ) / Sec2.IsForcePath.gapR vR w j q) =
        ((∫ q in (0 : ℝ)..s, 2 / (vR j q.toNNReal - w q.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun q _ => ?_
      simp only [Sec2.IsForcePath.gapR]
      push_cast
      rfl
    rw [hint, hU s hs.1 (hs.2.trans_lt hr)]
    simp only [Sec2.IsForcePath.gapR]
    rw [hveq]
    push_cast
    ring

/-! ### A mark swallowed off the prefix is never visited -/

/-- **The first collision of a right mark before `u`.** If `V^j_u = W_u` at `u < ζ` for a mark `x_j > 0`, there is a
first collision time `u₁ ∈ (0, u]`: `V^j_{u₁} = W_{u₁}` and `W < V^j` before `u₁`. -/
theorem exists_first_collision (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) {j : Fin nR} (hy : 0 < xR j)
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ) (hgap : vR j u = w u) :
    ∃ u₁ : ℝ≥0, u₁ ≤ u ∧ 0 < u₁ ∧ vR j u₁ = w u₁ ∧ ∀ t : ℝ≥0, t < u₁ → w t < vR j t := by
  set S : Set ℝ≥0 := Icc 0 u ∩ (fun t => vR j t - w t) ⁻¹' {0} with hS
  have hcont : ContinuousOn (fun t => vR j t - w t) (Icc 0 u) :=
    ((h.continuousOn_vR j).sub h.continuousOn_w).mono fun t ht =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) hu
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSne : S.Nonempty := ⟨u, ⟨zero_le, le_rfl⟩, by simp [hgap]⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem hSne (OrderBot.bddBelow S)
  have hlt : ∀ t : ℝ≥0, t < sInf S → w t < vR j t := by
    intro t ht
    have htζ : (t : ℝ≥0∞) < ζ :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (ht.le.trans hmem.1.2)) hu
    refine lt_of_le_of_ne (h.w_le_vR htζ j) fun he => ?_
    have htS : t ∈ S := ⟨⟨zero_le, ht.le.trans hmem.1.2⟩, by simp [he]⟩
    exact absurd (csInf_le (OrderBot.bddBelow S) htS) (not_le.2 ht)
  refine ⟨sInf S, hmem.1.2, pos_iff_ne_zero.2 fun h0 => ?_, sub_eq_zero.1 hmem.2, hlt⟩
  have h2 := hmem.2
  rw [h0] at h2
  simp only [Set.mem_preimage, Set.mem_singleton_iff, h.vR_zero, h.w_zero, sub_zero] at h2
  linarith

/-- **A mark swallowed off the prefix is never visited.** If `V^j_u = W_u` at some `u < ζ` (the mark `y = x_j > 0`
has been swallowed by `u`) and `η ≠ y` on `[0, u]`, then `η ≠ y` on `[0, ζ]`: `y` is not alive at `u`, so (being off
the prefix) it is not in the closure of `ℍ ∖ K_u`, i.e. a half-disc around `y` lies in `K_u`, and the trace adds
nothing to that half-disc after `u` (`G11.false_of_hull_stable`). -/
theorem trace_ne_of_gap_eq_zero (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hη : IsGeneratingTrace w ζ η)
    {j : Fin nR} (hy : 0 < xR j) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ) (hgap : vR j u = w u)
    (hoff : ∀ s : ℝ≥0, s ≤ u → η s ≠ xR j) : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η t ≠ xR j := by
  intro t ht
  rcases le_or_gt t u with htu | htu
  · exact hoff t htu
  intro hηt
  obtain ⟨t₂, hut₂, ht₂ζ⟩ := G11.exists_real_gt_lt hu
  set U : ℝ → ℝ := frozenDrive w t₂ with hUdef
  have hU : Continuous U := continuous_frozenDrive_of_lt h.continuousOn_w ht₂ζ
  have hu0 : (0 : ℝ) ≤ u := u.coe_nonneg
  have hUw : ∀ s : ℝ, 0 ≤ s → s < t₂ → U s = w s.toNNReal := fun s hs0 hs =>
    frozenDrive_eq ⟨hs0, hs.le⟩
  have hU0 : U 0 = 0 := by rw [hUw 0 le_rfl (hu0.trans_lt hut₂)]; simpa using h.w_zero
  have hL : IsLoewnerTraceLT U t₂ (fun s : ℝ => η s.toNNReal) := hη.isLoewnerTraceLT ht₂ζ
  -- `y` is not alive at `u`
  obtain ⟨u₁, hu₁u, hu₁0, hcol, hbefore⟩ := exists_first_collision h hy hu hgap
  have hu₁ζ : (u₁ : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hu₁u).trans hu.le
  have hUw₁ : ∀ r : ℝ, 0 ≤ r → r < u₁ → U r = w r.toNNReal := fun r hr0 hr =>
    hUw r hr0 (hr.trans ((NNReal.coe_le_coe.2 hu₁u).trans_lt hut₂))
  have hnot₁ : ¬ ∃ v, IsForwardSol U (xR j : ℂ) u₁ v := by
    refine Sec2.IsForcePath.not_exists_isForwardSol_of_tendsto hu₁0
      (fun r hr => isForwardSol_gapR_of_le h hu₁ζ hbefore hUw₁ hr) ?_
    have hc : ContinuousWithinAt (Sec2.IsForcePath.gapR vR w j) (Icc 0 (u₁ : ℝ)) (u₁ : ℝ) := by
      have hmaps : MapsTo Real.toNNReal (Icc (0 : ℝ) u₁) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun s hs => by
        refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hu
        exact (Real.toNNReal_le_iff_le_coe.2 hs.2).trans hu₁u
      exact (Complex.continuous_ofReal.comp_continuousOn
        (((h.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn hmaps).sub
          (h.continuousOn_w.comp continuous_real_toNNReal.continuousOn hmaps))) _
        ⟨u₁.coe_nonneg, le_rfl⟩
    have h0 : Sec2.IsForcePath.gapR vR w j u₁ = 0 := by
      simp [Sec2.IsForcePath.gapR, hcol]
    rw [← h0]
    exact hc.tendsto.mono_left (nhdsWithin_mono _ Ico_subset_Icc_self)
  have hnot : ¬ ∃ v, IsForwardSol U (xR j : ℂ) u v := fun ⟨v, hv⟩ =>
    hnot₁ ⟨v, QuantumZipper.isForwardSol_restrict hv u₁.coe_nonneg (NNReal.coe_le_coe.2 hu₁u)⟩
  -- a half-disc around `y` lies in `K_u`
  have hyη : (xR j : ℂ) ∉ (fun s : ℝ => η s.toNNReal) '' Icc 0 (u : ℝ) := by
    rintro ⟨s, hs, hse⟩
    exact hoff s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2) hse
  have hcl : (xR j : ℂ) ∉ closure (H \ fwdHull U u) := fun hcl =>
    hnot (GB7a.exists_isForwardSol_of_mem_closure hU hU0 hL hu0 hut₂ hy.ne' hyη hcl)
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ z ∈ H \ fwdHull U u, r ≤ dist (xR j : ℂ) z := by
    by_contra hne
    push Not at hne
    exact hcl (Metric.mem_closure_iff.2 fun ε hε => by
      obtain ⟨z, hz, hzd⟩ := hne ε hε
      exact ⟨z, hz, hzd⟩)
  have hKu : fwdHull U u = fwdHull (fun s : ℝ => w s.toNNReal) u :=
    fwdHull_eq_of_eqOn hu0 hut₂ fun s hs => frozenDrive_eq hs
  refine G11.false_of_hull_stable hη h.continuousOn_w h.w_zero (lt_of_le_of_lt zero_le htu) ht
    (U := ball (xR j : ℂ) r) isOpen_ball (by rw [hηt]; exact mem_ball_self hr)
    (ε := (t : ℝ) - u) (by have : (u : ℝ) < t := htu; linarith) fun s₁ s₂ hs₁ _ _ z hz => ?_
  have hzH : z ∈ H := (QuantumZipper.fwdHull_mono.2 _) hz.2
  have hzK : z ∈ fwdHull U u := by
    by_contra hzK
    have := hball z ⟨hzH, hzK⟩
    have hz1 := hz.1
    rw [mem_ball, dist_comm] at hz1
    linarith
  rw [hKu] at hzK
  exact QuantumZipper.fwdHull_mono.1 (show (u : ℝ) ≤ s₁ by linarith) hzK

/-! ### At a visit: the gap of the visited mark vanishes, the farther marks stay alive -/

/-- The trace point at a time `s ∈ (0, T)` lies in the closure of the hull `K_s`. -/
theorem trace_mem_closure_fwdHull {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} {γ : ℝ → ℂ}
    (hL : IsLoewnerTraceLT U T γ) {s : ℝ} (hs0 : 0 < s) (hsT : s < T) : γ s ∈ closure (fwdHull U s) :=
  YuanCorollary13.mem_closure_fwdHull_of_tendsto hU hU0 hs0 (hL.tendsto_fwdMapInv_tip hU hU0 hs0.le hsT)

/-- **The gap of a visited mark tends to `0`.** If `η(T) = y = x_j > 0`, `W < V^j` before `T ≤ ζ` and `V^j − W → L`
at `T⁻`, then `L = 0`: otherwise `y` stays alive through `T` (`GB7a.exists_isForwardSol_of_le`), so a disc around `y`
misses `K_T`, while the trace points `η(s) ∈ closure K_s ⊆ closure K_T` tend to `y`. -/
theorem tendsto_gap_eq_zero_of_visit (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hη : IsGeneratingTrace w ζ η)
    {j : Fin nR} (hy : 0 < xR j) {T : ℝ≥0} (hT0 : 0 < T) (hTζ : (T : ℝ≥0∞) ≤ ζ) (hvis : η T = xR j)
    (hlife : ∀ t : ℝ≥0, t < T → w t < vR j t) {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    (hUw : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) {L : ℝ}
    (hL : Tendsto (fun t => vR j t - w t) (𝓝[<] T) (𝓝 L)) : L = 0 := by
  have hT0' : (0 : ℝ) < T := NNReal.coe_pos.2 hT0
  have := Sec2.IsForcePath.neBot_nhdsLT hT0
  have hL0 : 0 ≤ L := ge_of_tendsto hL (by
    filter_upwards [self_mem_nhdsWithin] with s hs using (sub_pos.2 (hlife s hs)).le)
  by_contra hne
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
  set u : ℝ → ℝ := fun r => vR j r.toNNReal - w r.toNNReal with hudef
  have hwc := h.continuousOn_w
  have pkg := fun (s : ℝ) (hs0 : 0 ≤ s) (hsT : s < T) => GB7a.centredPkg hwc (h.continuousOn_vR j)
    (fun t ht => h.integrable_gapR ht j) (fun t ht => h.vR_eq ht j) (h.volume_collisionR j) hTζ hUw hs0 hsT
  have hupos : ∀ s ∈ Ico (0 : ℝ) T, 0 < u s := fun s hs => by
    refine sub_pos.2 (hlife _ ?_)
    rw [Real.toNNReal_lt_iff_lt_coe hs.1]; exact hs.2
  have huL : Tendsto u (𝓝[<] (T : ℝ)) (𝓝 L) := GB7a.tendsto_comp_toNNReal' hT0 hL
  -- a positive lower bound of the gap on `[0, T)`
  obtain ⟨c, hc, hcu⟩ : ∃ c > 0, ∀ s ∈ Ico (0 : ℝ) T, c ≤ u s := by
    have hev : ∀ᶠ s in 𝓝[<] (T : ℝ), L / 2 < u s := huL (lt_mem_nhds (by linarith))
    obtain ⟨T₁, hT₁, hT₁sub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
    have hT₂ : max T₁ 0 < T := max_lt hT₁ hT0'
    obtain ⟨huc, -, -⟩ := pkg (max T₁ 0) (le_max_right _ _) hT₂
    obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (le_max_right T₁ 0)) huc
    refine ⟨min (u s₀) (L / 2), lt_min (hupos s₀ ⟨hs₀.1, hs₀.2.trans_lt hT₂⟩) (by linarith),
      fun s hs => ?_⟩
    rcases le_or_gt s (max T₁ 0) with h' | h'
    · exact (min_le_left _ _).trans (hmin ⟨hs.1, h'⟩)
    · exact (min_le_right _ _).trans (hT₁sub ⟨(le_max_left _ _).trans_lt h', hs.2⟩).le
  -- `y` is alive through `T`
  have hv0 : IsForwardSol U (xR j : ℂ) 0 (Sec2.IsForcePath.gapR vR w j) :=
    isForwardSol_gapR_of_le h hTζ hlife hUw hT0'
  have hu0 : u 0 ≤ (Sec2.IsForcePath.gapR vR w j 0).re := by
    simp [hudef, Sec2.IsForcePath.gapR]
  obtain ⟨v', hv'⟩ := GB7a.exists_isForwardSol_of_le hU hU0 hy le_rfl hT0'.le hv0 hc
    (fun s hs => by
      obtain ⟨h1, h2, h3, -⟩ := pkg s hs.1 hs.2
      exact ⟨h1, h2, h3⟩) hcu hu0
  obtain ⟨r, hr, hnot⟩ := GB7a.exists_ball_notMem_fwdHull hU T.coe_nonneg hv'
  -- the trace points before `T` approach `y` from `closure K_T`
  have hL' : IsLoewnerTraceLT U T (fun s : ℝ => η s.toNNReal) := GB7a.isLoewnerTraceLT_of_agree hη hTζ hUw
  have hlimη := GB7a.tendsto_comp_toNNReal hη hTζ hT0
  rw [hvis] at hlimη
  have hev : ∀ᶠ s in 𝓝[<] (T : ℝ), η s.toNNReal ∈ ball (xR j : ℂ) (r / 2) :=
    hlimη (ball_mem_nhds _ (half_pos hr))
  obtain ⟨s, hs1, hs2⟩ := (hev.and (Ioo_mem_nhdsLT hT0')).exists
  have hcl := trace_mem_closure_fwdHull hU hU0 hL' hs2.1 hs2.2
  have hcl' : η s.toNNReal ∈ closure (fwdHull U T) :=
    closure_mono (QuantumZipper.fwdHull_mono.1 hs2.2.le) hcl
  obtain ⟨z, hzK, hzd⟩ := Metric.mem_closure_iff.1 hcl' (r / 2) (half_pos hr)
  refine hnot z ?_ hzK
  rw [mem_ball] at hs1
  rw [← dist_eq_norm]
  linarith [dist_triangle z (η s.toNNReal) (xR j : ℂ), dist_comm z (η s.toNNReal)]

/-- **The ray lemma with a real end point off the ray.** Let the trace `γ` of `U` be continuous on `[0, T]`, let
`y₀ > 0` be alive before `T`, and let `γ(T)` not lie on `[y₀, ∞)`. Then `G_r(y₀) ↛ 0` as `r ↑ T`
(`FiniteEndpoint.notMem_H_of_tendsto_fwdMap`, whose end point is in `ℍ`). -/
theorem not_tendsto_fwdMap_of_trace_off_ray {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T y₀ : ℝ}
    (hT : 0 < T) (hy₀ : 0 < y₀) {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Icc 0 T)) (htrace : IsLoewnerTraceLT U T γ)
    (halive : ∀ r ∈ Ico (0 : ℝ) T, ∃ u, IsForwardSol U (y₀ : ℂ) r u)
    (hend : ∀ b : ℝ, y₀ ≤ b → γ T ≠ b) :
    ¬ Tendsto (fun r => fwdMap U r y₀) (𝓝[<] T) (𝓝 0) := by
  intro hlim
  have hcpt : ∀ t ∈ Icc (0 : ℝ) T, IsCompact (γ '' Icc 0 t) := fun t ht =>
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc le_rfl ht.2))
  have hfillH : ∀ t ∈ Ico (0 : ℝ) T, fwdHull U t = fillH (γ '' Icc 0 t) := fun t ht =>
    htrace.2.2 t ht.1 ht.2
  have hγ0 : γ 0 = 0 := htrace.1
  -- Step 1: the trace does not meet the ray `[y₀, ∞)`
  have hstep1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → γ t ≠ b := by
    intro t ht b hb heq
    rcases ht.2.lt_or_eq with htT | htT
    · rcases ht.1.lt_or_eq with ht0 | ht0
      · obtain ⟨u, hu⟩ := halive t ⟨ht.1, htT⟩
        obtain ⟨v, hv⟩ : ∃ v, IsForwardSol U (b : ℂ) t v := by
          rcases hb.lt_or_eq with hlt | hlt
          · exact QuantumZipper.RS.exists_isForwardSol_of_lt hU ht.1 (by rw [hU0]; exact hy₀) hlt hu
          · exact ⟨u, hlt ▸ hu⟩
        obtain ⟨δ, hδ, hδv⟩ := exists_two_mul_le_norm_of_isForwardSol ht.1 hv
        have htip := htrace.tendsto_fwdMapInv_tip hU hU0 ht.1 htT
        have hcl := YuanCorollary13.mem_closure_fwdHull_of_tendsto hU hU0 ht0 htip
        rw [heq] at hcl
        have hρ : 0 < δ / Real.exp (2 / δ ^ 2 * t) := div_pos hδ (Real.exp_pos _)
        obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hcl _ hρ
        have hzb' : ‖z - (b : ℂ)‖ < δ / Real.exp (2 / δ ^ 2 * t) := by
          rw [← dist_eq_norm, dist_comm]; exact hzb
        exact not_mem_fwdHull_of_isForwardSol hU hv hδ hδv hzK.1
          ((lt_div_iff₀ (Real.exp_pos _)).1 hzb') hzK
      · rw [← ht0, hγ0] at heq
        have := congrArg Complex.re heq
        simp only [Complex.zero_re, Complex.ofReal_re] at this
        linarith
    · rw [htT] at heq
      exact hend b hb heq
  -- Step 2: a positive distance between the trace and the ray
  set F : Set ℂ := {z | z.im = 0 ∧ y₀ ≤ z.re} with hFdef
  have hFc : IsClosed F :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hFne : F.Nonempty := ⟨(y₀ : ℂ), by rw [hFdef]; exact ⟨by simp, by simp⟩⟩
  have hnotF : ∀ t ∈ Icc (0 : ℝ) T, γ t ∉ F := fun t ht hF =>
    hstep1 t ht (γ t).re hF.2 (Complex.ext (by simp) (by simp [hF.1]))
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le)
    ((continuous_infDist_pt F).comp_continuousOn hγc)
  set d := infDist (γ t₀) F with hd
  have hdpos : 0 < d := (hFc.notMem_iff_infDist_pos hFne).1 (hnotF t₀ ht₀)
  have hdist : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → d ≤ dist (γ t) b := fun t ht b hb =>
    (hmin ht).trans (infDist_le_dist_of_mem (show (b : ℂ) ∈ F from ⟨by simp, by simpa using hb⟩))
  -- Step 3: the `d/2`-neighbourhood of the ray avoids every hull
  have hray : ∀ r ∈ Ico (0 : ℝ) T, ∀ y : ℝ, y₀ ≤ y →
      Disjoint (ball (y : ℂ) (d / 2)) (fwdHull U r) := by
    intro r hr y hy
    rw [Set.disjoint_left]
    intro z hzb hzK
    rw [hfillH r hr] at hzK
    have hAc : closure (γ '' Icc 0 r) = γ '' Icc 0 r :=
      (hcpt r (Ico_subset_Icc_self hr)).isClosed.closure_eq
    set C : Set ℂ := (ball (y : ℂ) (d / 2) ∩ H) ∪ {w | y ≤ w.re ∧ 0 < w.im ∧ w.im < d / 2}
      with hC
    have hzC : z ∈ C := Or.inl ⟨hzb, hzK.1⟩
    have hp1 : (⟨y, d / 4⟩ : ℂ) ∈ ball (y : ℂ) (d / 2) ∩ H := by
      refine ⟨?_, show (0 : ℝ) < d / 4 by positivity⟩
      rw [mem_ball, dist_eq_norm]
      refine FiniteEndpoint.norm_lt_of_abs_re_add_abs_im_lt ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_self,
        abs_zero, sub_zero, zero_add]
      rw [abs_of_pos (by positivity)]
      linarith
    have hp2 : (⟨y, d / 4⟩ : ℂ) ∈ {w : ℂ | y ≤ w.re ∧ 0 < w.im ∧ w.im < d / 2} :=
      ⟨le_rfl, show (0 : ℝ) < d / 4 by positivity, show d / 4 < d / 2 by linarith⟩
    have hCpre : IsPreconnected C :=
      IsPreconnected.union _ hp1 hp2
        ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
        ((convex_halfSpace_re_ge y).inter ((convex_halfSpace_im_gt 0).inter
          (convex_halfSpace_im_lt (d / 2)))).isPreconnected
    have hCsub : C ⊆ H \ closure (γ '' Icc 0 r) := by
      intro w hw
      have hwH : w ∈ H := by
        rcases hw with hw | hw
        · exact hw.2
        · exact hw.2.1
      refine ⟨hwH, ?_⟩
      rw [hAc]
      rintro ⟨t, ht, rfl⟩
      have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hr.2.le⟩
      rcases hw with hw | hw
      · have := hdist t htT y hy
        have hw1 := hw.1
        rw [mem_ball] at hw1
        linarith
      · have := hdist t htT (γ t).re (hy.trans hw.1)
        have hle : dist (γ t) ((γ t).re : ℂ) < d / 2 := by
          rw [dist_eq_norm]
          refine FiniteEndpoint.norm_lt_of_abs_re_add_abs_im_lt ?_
          simp only [Complex.sub_re, Complex.ofReal_re, sub_self, abs_zero, Complex.sub_im,
            Complex.ofReal_im, sub_zero, zero_add]
          rw [abs_of_pos hw.2.1]
          exact hw.2.2
        linarith
    have hCunb : ¬ Bornology.IsBounded C := by
      intro hb
      obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hb
      have hw : (⟨max y (R + 1), d / 4⟩ : ℂ) ∈ C :=
        Or.inr ⟨le_max_left _ _, show (0 : ℝ) < d / 4 by positivity,
          show d / 4 < d / 2 by linarith⟩
      have h1 := hR _ hw
      have h2 := Complex.abs_re_le_norm (⟨max y (R + 1), d / 4⟩ : ℂ)
      have h3 : R + 1 ≤ |(⟨max y (R + 1), d / 4⟩ : ℂ).re| :=
        (le_max_right _ _).trans (le_abs_self _)
      linarith
    rcases hzK.2 with hzA | hbdd
    · exact (hCsub hzC).2 hzA
    · exact hCunb (hbdd.subset (hCpre.subset_connectedComponentIn hzC hCsub))
  -- Step 4: the ray lemma
  exact FiniteEndpoint.not_tendsto_fwdMap_of_disjoint_ray hU hU0 hT hy₀ (half_pos hdpos) hray halive hlim

/-- **At a visit, every farther right mark is alive.** If `η(T) = y = x_j > 0`, `W < V^j` before `T ≤ ζ`, and
`V^k − W → L` at `T⁻` for a mark `x_k > y`, then `L > 0`: the trace on `[0, T]` stays off `[x_k, ∞)`, so the ray
lemma forbids `G_r(x_k) → 0`. -/
theorem tendsto_gap_pos_of_visit (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) (hord : IsOrderedForceWord xL xR)
    (hη : IsGeneratingTrace w ζ η) {j k : Fin nR} (hjk : xR j < xR k) {T : ℝ≥0} (hT0 : 0 < T)
    (hTζ : (T : ℝ≥0∞) ≤ ζ) (hvis : η T = xR j) (hlife : ∀ t : ℝ≥0, t < T → w t < vR j t) {U : ℝ → ℝ}
    (hU : Continuous U) (hU0 : U 0 = 0) (hUw : ∀ s : ℝ, 0 ≤ s → s < T → U s = w s.toNNReal) {L : ℝ}
    (hL : Tendsto (fun t => vR k t - w t) (𝓝[<] T) (𝓝 L)) : 0 < L := by
  have hT0' : (0 : ℝ) < T := NNReal.coe_pos.2 hT0
  have hjk' : j ≤ k := by
    by_contra hkj; rw [not_le] at hkj; exact absurd (hord.2.2.1 hkj.le) (not_le.2 hjk)
  have hltζ : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht => (ENNReal.coe_lt_coe.2 ht).trans_le hTζ
  have hlifek : ∀ t : ℝ≥0, t < T → w t < vR k t := fun t ht =>
    lt_of_lt_of_le (hlife t ht) (h.monotone_vR (hltζ t ht) hjk')
  have hy₀ : 0 < xR k := by
    have := hlifek 0 hT0
    rwa [h.w_zero, h.vR_zero] at this
  have hsol : ∀ r : ℝ, r < T → IsForwardSol U (xR k : ℂ) r (Sec2.IsForcePath.gapR vR w k) := fun r hr =>
    isForwardSol_gapR_of_le h hTζ hlifek hUw hr
  set γ : ℝ → ℂ := fun s => η s.toNNReal with hγ
  have hγc : ContinuousOn γ (Icc 0 (T : ℝ)) := by
    refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ
    exact (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)).trans hTζ
  have htrace : IsLoewnerTraceLT U T γ := GB7a.isLoewnerTraceLT_of_agree hη hTζ hUw
  have hend : ∀ b : ℝ, xR k ≤ b → γ T ≠ b := by
    intro b hb he
    have : (xR j : ℂ) = b := by rw [← hvis]; simpa [hγ] using he
    have := congrArg Complex.re this
    simp only [Complex.ofReal_re] at this
    linarith
  have hnot := not_tendsto_fwdMap_of_trace_off_ray hU hU0 hT0' hy₀ hγc htrace
    (fun r hr => ⟨_, hsol r hr.2⟩) hend
  have := Sec2.IsForcePath.neBot_nhdsLT hT0
  have hL0 : 0 ≤ L := ge_of_tendsto hL (by
    filter_upwards [self_mem_nhdsWithin] with s hs using (sub_pos.2 (hlifek s hs)).le)
  refine lt_of_le_of_ne hL0 fun hL0' => hnot ?_
  have hm : Tendsto Real.toNNReal (𝓝[<] (T : ℝ)) (𝓝[<] T) := by
    rw [← nhdsWithin_Ico_eq_nhdsLT hT0']
    exact Sec2.IsForcePath.tendsto_toNNReal_nhdsLT T
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp ((hL0' ▸ hL).comp hm)
  rw [Complex.ofReal_zero] at h2
  refine h2.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hT0'] with r hr
  exact (fwdMap_eq_of_isForwardSol hU (hsol r hr.2) ⟨hr.1.le, le_rfl⟩).symm

end G12

end Supp7

end InteractingSLE
