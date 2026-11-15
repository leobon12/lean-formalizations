import InteractingSLE.Spec.Dimension.Transfer
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.Zipper.RegContRandom

/-!
# New trace points after a time `s` come from the mapped-out future (proof of Aux. lemma 15)

Specification, proof of Aux. lemma 15 (`source/spec/p049-096.md`, lines 870–872, p. 89): "the
countably many localized mapped futures cover every interior physical trace point after pulling
back by `g_a⁻¹`; repeated later visits add no new points", and "a conformal map and its inverse
are Lipschitz on compact interior subsets", so each pullback preserves the dimension bound.

Deterministic form, for the radial-limit trace `γ = trace W` and the trace `γ^s = trace W^s` of the
shifted driver `W^s(u) = W(s + u) − W(s)` (`QuantumZipper.RS.shiftDrive`):

* `trace_add_mem_image_or_mem_prefix`: if `γ(s + u) ∈ ℍ`, then either `γ^s(u) ∈ ℍ` and
  `γ(s + u) = F_s(γ^s(u))`, or `γ(s + u)` is an old point, `γ(s + u) ∈ γ([0, s])`. In the second
  case `γ(s + u)` is a limit of points of `ℍ \ K_s` but not a point of the open set `ℍ \ K_s` (there
  `g_s` is continuous and would send it to the real limit `γ^s(u)`), so it lies on the frontier of
  `ℍ \ K_s` in `ℍ`, which the trace prefix generates;
* `trace_image_Icc_add_inter_H_subset`: `γ([s, s + T]) ∩ ℍ ⊆ F_s(γ^s([0, T]) ∩ ℍ) ∪ γ([0, s])`;
* `dimH_trace_image_Icc_add_inter_H_diff_le`: the new points `γ([s, s + T]) ∩ ℍ \ γ([0, s])` have
  Hausdorff dimension at most that of `γ^s([0, T]) ∩ ℍ` (`F_s` is holomorphic on `ℍ`).
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper QuantumZipper.RS

/-- **A trace point after time `s` is either the image of the future trace or an old point.** -/
theorem trace_add_mem_image_or_mem_prefix {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u)
    (hunif : TendstoUniformlyOn (fun (y : ℝ) (r : ℝ) => fwdMapInv W r (y * Complex.I)) (trace W)
      (𝓝[>] 0) (Icc 0 s))
    (hcont : ContinuousOn (trace W) (Icc 0 s))
    (hlimS : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W s) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace (shiftDrive W s) u)))
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W (s + u) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace W (s + u))))
    (hq : trace W (s + u) ∈ H) :
    (trace (shiftDrive W s) u ∈ H ∧ trace W (s + u) = fwdMapInv W s (trace (shiftDrive W s) u)) ∨
      trace W (s + u) ∈ trace W '' Icc 0 s := by
  set p := trace (shiftDrive W s) u with hp
  set q := trace W (s + u) with hqdef
  by_cases hpH : p ∈ H
  · exact Or.inl ⟨hpH, (trace_add_of_tendsto_shift hW hW0 hs hu hpH hlimS).2.2⟩
  right
  have hsu : 0 ≤ s + u := add_nonneg hs hu
  -- the approximating points lie in `ℍ \ K_s`
  have hmem : ∀ y : ℝ, 0 < y → fwdMapInv W (s + u) (y * Complex.I) ∈ H \ fwdHull W s := by
    intro y hy
    have h1 : fwdMapInv W (s + u) (y * Complex.I) ∈ H \ fwdHull W (s + u) := by
      rw [← image_fwdMapInv_H hW hW0 hsu]
      exact mem_image_of_mem _ (mul_I_mem_H hy)
    exact ⟨h1.1, fun h => h1.2 (fwdHull_mono.1 (le_add_of_nonneg_right hu) h)⟩
  have hcl : q ∈ closure (H \ fwdHull W s) :=
    mem_closure_of_tendsto hlim (eventually_mem_nhdsWithin.mono fun y hy => hmem y hy)
  -- `q` is not a point of the open set `ℍ \ K_s`
  have hnot : q ∉ H \ fwdHull W s := by
    intro hqU
    have hopen : IsOpen (H \ fwdHull W s) := FwdHolo.isOpen_compl_fwdHull hW hs
    have hcontg : ContinuousAt (fwdMap W s) q :=
      ((FwdHolo.differentiableOn_fwdMap hW hs).differentiableAt
        (hopen.mem_nhds hqU)).continuousAt
    have h1 : Tendsto (fun y : ℝ => fwdMap W s (fwdMapInv W (s + u) (y * Complex.I))) (𝓝[>] 0)
        (𝓝 (fwdMap W s q)) := hcontg.tendsto.comp hlim
    have h2 : Tendsto (fun y : ℝ => fwdMap W s (fwdMapInv W (s + u) (y * Complex.I))) (𝓝[>] 0)
        (𝓝 p) := by
      refine hlimS.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
      exact fwdMapInv_shift_eq hW hW0 hs hu (mul_I_mem_H hy)
    have hpq : p = fwdMap W s q := tendsto_nhds_unique h2 h1
    exact hpH (hpq ▸ FwdHolo.mapsTo_fwdMap hW hs hqU)
  have hfr : q ∈ frontier (H \ fwdHull W s) ∩ H := by
    refine ⟨?_, hq⟩
    rw [(FwdHolo.isOpen_compl_fwdHull hW hs).frontier_eq]
    exact ⟨hcl, hnot⟩
  exact frontier_compl_fwdHull_inter_H_subset hW hW0 hs hunif hcont hfr

/-- `γ([s, s + T]) ∩ ℍ ⊆ F_s(γ^s([0, T]) ∩ ℍ) ∪ γ([0, s])`, when the radial limits exist on the
relevant time intervals. -/
theorem trace_image_Icc_add_inter_H_subset {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s)
    (hunif : TendstoUniformlyOn (fun (y : ℝ) (r : ℝ) => fwdMapInv W r (y * Complex.I)) (trace W)
      (𝓝[>] 0) (Icc 0 s))
    (hcont : ContinuousOn (trace W) (Icc 0 s))
    (hlimS : ∀ u ∈ Icc 0 T, Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W s) u (y * Complex.I))
      (𝓝[>] 0) (𝓝 (trace (shiftDrive W s) u)))
    (hlim : ∀ u ∈ Icc 0 T, Tendsto (fun y : ℝ => fwdMapInv W (s + u) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace W (s + u)))) :
    trace W '' Icc s (s + T) ∩ H ⊆
      fwdMapInv W s '' (trace (shiftDrive W s) '' Icc 0 T ∩ H) ∪ trace W '' Icc 0 s := by
  rintro _ ⟨⟨t, ⟨hst, htT⟩, rfl⟩, htH⟩
  set u := t - s with hu
  have hu0 : 0 ≤ u := sub_nonneg.2 hst
  have huT : u ∈ Icc 0 T := ⟨hu0, by rw [hu]; linarith⟩
  have ht : t = s + u := by rw [hu]; ring
  rw [ht] at htH ⊢
  rcases trace_add_mem_image_or_mem_prefix hW hW0 hs hu0 hunif hcont (hlimS u huT) (hlim u huT)
    htH with ⟨hpH, heq⟩ | hold
  · exact Or.inl ⟨_, ⟨mem_image_of_mem _ huT, hpH⟩, heq.symm⟩
  · exact Or.inr hold

/-- **Pullback preserves the dimension bound.** The new interior trace points after time `s`
have Hausdorff dimension at most that of the interior part of the future trace `γ^s([0, T])`. -/
theorem dimH_trace_image_Icc_add_inter_H_diff_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s)
    (hunif : TendstoUniformlyOn (fun (y : ℝ) (r : ℝ) => fwdMapInv W r (y * Complex.I)) (trace W)
      (𝓝[>] 0) (Icc 0 s))
    (hcont : ContinuousOn (trace W) (Icc 0 s))
    (hlimS : ∀ u ∈ Icc 0 T, Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W s) u (y * Complex.I))
      (𝓝[>] 0) (𝓝 (trace (shiftDrive W s) u)))
    (hlim : ∀ u ∈ Icc 0 T, Tendsto (fun y : ℝ => fwdMapInv W (s + u) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace W (s + u)))) :
    dimH ((trace W '' Icc s (s + T) ∩ H) \ trace W '' Icc 0 s)
      ≤ dimH (trace (shiftDrive W s) '' Icc 0 T ∩ H) := by
  have hsub : (trace W '' Icc s (s + T) ∩ H) \ trace W '' Icc 0 s ⊆
      fwdMapInv W s '' (trace (shiftDrive W s) '' Icc 0 T ∩ H) := by
    intro x ⟨hx, hxold⟩
    rcases trace_image_Icc_add_inter_H_subset hW hW0 hs hunif hcont hlimS hlim hx with h | h
    · exact h
    · exact absurd h hxold
  refine (dimH_mono hsub).trans ?_
  exact dimH_image_le_of_differentiableOn (U := H) QuantumZipper.isOpen_H
    (differentiableOn_fwdMapInv hW hW0 hs) inter_subset_right

/-- The trace at time `0` is not in `ℍ` (`K_0 = ∅`). -/
theorem trace_zero_notMem_H {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W 0 (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W 0))) :
    trace W 0 ∉ H := by
  intro hH
  rcases trace_mem_fwdHull_or_real hW hW0 le_rfl hlim with h | h
  · have h1 := swallowTime_pos (z := trace W 0) hW hH
    have h2 : swallowTime W (trace W 0) ≤ ENNReal.ofReal 0 := h.2
    rw [ENNReal.ofReal_zero] at h2
    exact absurd h1 (not_lt.2 h2)
  · exact (show (0 : ℝ) < (trace W 0).im from hH).ne' h

/-- **Covering by localized futures** (proof of Aux. lemma 15, p. 89, pathwise form). Let the
radial-limit trace `γ = trace W` be continuous with locally uniform radial limits on `[0, ζ)`.
Suppose countably many localizations `(s i, T i, X i)` are given, with `s i + T i < ζ`: `X i` is a
continuous driver with `X i 0 = 0` that agrees with the shifted driver `W^{s i}` on `[0, T i]`, whose
trace is the radial limit on `[0, T i]` and has interior dimension at most `d`; and suppose every
time `t ∈ (0, ζ)` with `γ(t) ∈ ℍ` lies in some `(s i, s i + T i]`. Then `dim_H(γ([0, ζ)) ∩ ℍ) ≤ d`.
Every interior point is covered at its first visit time, which is positive because `γ(0) ∉ ℍ`; at
that time it is a new point after `s i`, hence a pullback of a point of the future trace. -/
theorem dimH_trace_inter_H_le_of_cover {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {ζ : ℝ≥0∞} {d : ℝ≥0∞}
    (hcont : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < ζ → ContinuousOn (trace W) (Icc 0 t))
    (hunif : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < ζ →
      TendstoUniformlyOn (fun (y : ℝ) (r : ℝ) => fwdMapInv W r (y * Complex.I)) (trace W)
        (𝓝[>] 0) (Icc 0 t))
    {ι : Type*} [Countable ι] (s T : ι → ℝ) (X : ι → ℝ → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hT : ∀ i, 0 ≤ T i) (hsT : ∀ i, ENNReal.ofReal (s i + T i) < ζ)
    (hX : ∀ i, Continuous (X i)) (hX0 : ∀ i, X i 0 = 0)
    (hXeq : ∀ i, EqOn (shiftDrive W (s i)) (X i) (Icc 0 (T i)))
    (hXlim : ∀ i, ∀ u ∈ Icc 0 (T i), Tendsto (fun y : ℝ => fwdMapInv (X i) u (y * Complex.I))
      (𝓝[>] 0) (𝓝 (trace (X i) u)))
    (hXdim : ∀ i, dimH (trace (X i) '' Ici 0 ∩ H) ≤ d)
    (hcover : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < ζ → trace W t ∈ H →
      ∃ i, s i < t ∧ t ≤ s i + T i) :
    dimH (trace W '' {t | 0 ≤ t ∧ ENNReal.ofReal t < ζ} ∩ H) ≤ d := by
  -- the shifted drivers
  have hWs : ∀ i, Continuous (shiftDrive W (s i)) := fun i => continuous_shiftDrive hW (s i)
  have hWs0 : ∀ i, shiftDrive W (s i) 0 = 0 := fun i => shiftDrive_zero W (s i)
  have htrace_eq : ∀ i, ∀ u ∈ Icc 0 (T i), trace (shiftDrive W (s i)) u = trace (X i) u :=
    fun i u hu => trace_congr_drive (hWs i) (hWs0 i) (hX i) (hX0 i) hu.1
      (fun r hr => hXeq i ⟨hr.1, hr.2.trans hu.2⟩)
  have hlimS : ∀ i, ∀ u ∈ Icc 0 (T i), Tendsto
      (fun y : ℝ => fwdMapInv (shiftDrive W (s i)) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace (shiftDrive W (s i)) u)) := by
    intro i u hu
    rw [htrace_eq i u hu]
    refine (hXlim i u hu).congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    exact (RegCont.fwdMapInv_congr (hWs i) (hWs0 i) (hX i) (hX0 i) (hXeq i) hu
      (mul_I_mem_H hy)).symm
  have hlimW : ∀ i, ∀ u ∈ Icc 0 (T i), Tendsto
      (fun y : ℝ => fwdMapInv W (s i + u) (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace W (s i + u))) := fun i u hu =>
    (hunif _ (add_nonneg (hs i) (hT i)) (hsT i)).tendsto_at
      ⟨add_nonneg (hs i) hu.1, by linarith [hu.2]⟩
  have hpiece : ∀ i, dimH ((trace W '' Icc (s i) (s i + T i) ∩ H) \ trace W '' Icc 0 (s i)) ≤ d := by
    intro i
    have hsTi : ENNReal.ofReal (s i) < ζ :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [hT i])) (hsT i)
    refine (dimH_trace_image_Icc_add_inter_H_diff_le hW hW0 (hs i) (hunif _ (hs i) hsTi)
      (hcont _ (hs i) hsTi) (hlimS i) (hlimW i)).trans ?_
    have himg : trace (shiftDrive W (s i)) '' Icc 0 (T i) = trace (X i) '' Icc 0 (T i) :=
      image_congr fun u hu => htrace_eq i u hu
    rw [himg]
    exact (dimH_mono (inter_subset_inter_left _ (image_mono Icc_subset_Ici_self))).trans (hXdim i)
  -- every interior trace point is a new point of some piece, at its first visit
  have hsub : trace W '' {t | 0 ≤ t ∧ ENNReal.ofReal t < ζ} ∩ H ⊆
      ⋃ i, (trace W '' Icc (s i) (s i + T i) ∩ H) \ trace W '' Icc 0 (s i) := by
    rintro _ ⟨⟨t, ⟨ht0, htζ⟩, rfl⟩, hzH⟩
    set z := trace W t with hz
    set A : Set ℝ := Icc 0 t ∩ trace W ⁻¹' {z} with hA
    have hAc : IsClosed A :=
      (hcont t ht0 htζ).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have htA : t ∈ A := ⟨⟨ht0, le_rfl⟩, rfl⟩
    have hAne : A.Nonempty := ⟨t, htA⟩
    have hAbdd : BddBelow A := ⟨0, fun r hr => hr.1.1⟩
    set t₀ := sInf A with ht₀
    have ht₀A : t₀ ∈ A := hAc.csInf_mem hAne hAbdd
    have ht₀le : ∀ r ∈ A, t₀ ≤ r := fun r hr => csInf_le hAbdd hr
    have ht₀z : trace W t₀ = z := ht₀A.2
    have ht₀t : t₀ ≤ t := ht₀A.1.2
    have ht₀ζ : ENNReal.ofReal t₀ < ζ := lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht₀t) htζ
    have ht₀pos : 0 < t₀ := by
      rcases ht₀A.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hlim0 := (hunif t ht0 htζ).tendsto_at ⟨le_rfl, ht0⟩
        refine trace_zero_notMem_H hW hW0 hlim0 ?_
        rw [h, ht₀z]; exact hzH
    obtain ⟨i, hi1, hi2⟩ := hcover t₀ ht₀pos ht₀ζ (ht₀z ▸ hzH)
    refine mem_iUnion.2 ⟨i, ⟨⟨t₀, ⟨hi1.le, hi2⟩, ht₀z⟩, hzH⟩, ?_⟩
    rintro ⟨r, hr, hrz⟩
    have hrA : r ∈ A := ⟨⟨hr.1, by linarith [hr.2]⟩, hrz⟩
    have := ht₀le r hrA
    linarith [hr.2]
  refine (dimH_mono hsub).trans ?_
  rw [dimH_iUnion]
  exact iSup_le hpiece

end InteractingSLE.Dimension
