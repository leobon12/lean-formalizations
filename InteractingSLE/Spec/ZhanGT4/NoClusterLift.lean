/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoForceRecur
import InteractingSLE.Spec.ZhanGT4.CrosscutRestart
import InteractingSLE.Spec.ZhanGT4.CollarBoundary

/-!
# Lemma 3.4, the deterministic part: lifting a real terminal cluster point through a restart

Packet PROVE-ZHAN-GT4-B2. Source: Astra, *Follow-up proofs*, §B.3 L1236–L1259 (ruling R38); additional note Lemma 3.4,
L1479–L1505 (ruling R39). The source proves the absence of real terminal cluster points for the separated two-force law
in the strip chart, with the annulus estimate (additional note Lemma 3.1) forcing the images `c(T)`, `d(T)` of the
swallowed real extremes far from the upper mark. In the chordal picture the same crowding is elementary: a real point
`x'` alive at `T` on the left of the driver, between the left mark `p_L` and `0`, has

  `g_T(p_L) ≤ g_T(x') ≤ g_T(p_L) + (x' − p_L)`,

because two left real flows approach each other (`∂ₜ(g(y) − g(x)) = 2/(g(y) − W) − 2/(g(x) − W) ≤ 0` for
`g(x) < g(y) < W`). So the exterior inverse coordinates between the two mark images lie in two bands of widths `|p_L|`
and `p_R` next to the marks, while the marks themselves move apart (`(V_R − V_L)² ≥ 8t`).

## Main results

* `re_sub_le_of_isForwardSol`: **two real flows on the same side of the driver approach each other**.
* `band_of_isForwardSol_neg`, `band_of_isForwardSol_pos`: the band bounds above.
* `IsTermCluster`: `x` is a terminal cluster point of `η` (`MapClusterPt x atTop η`).
* `exists_band_cluster`: **the lifting lemma.** Let `η` generate the chain of a continuous driver on `[0, ∞)`, `T > 0`,
  `η₂` generate the chain of the driver restarted at `T`, and let the inverse boundary be interior at `T` ((G5),
  `HasInteriorInverseBoundary`). If `p_L < 0 < p_R` are alive at `T` and `x ∈ (p_L, p_R)` is a terminal cluster point of
  `η`, then `η₂` has a real terminal cluster point in `[V_L, V_L − p_L] ∪ [V_R − p_R, V_R]`, where `V_L`, `V_R` are the
  centred images of `p_L`, `p_R` at `T`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### Real flows on one side of the driver approach each other -/

section Contraction

variable {W : ℝ → ℝ}

/-- `2/z` has real part `2/re z` on the real axis. -/
theorem re_two_div_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : (2 / z).re = 2 / z.re := by
  have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
  rw [this, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_re]

/-- **Two real flows on the same side of the driver approach each other.** If `x, y` are alive on `[0, T]`, the flow of
`x` stays strictly below that of `y`, and both stay on the same side of `0` (positive product), then
`f_T(y) − f_T(x) ≤ y − x`. -/
theorem re_sub_le_of_isForwardSol (hW : Continuous W) {x y T : ℝ} (hT : 0 ≤ T) {u v : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) (hv : IsForwardSol W (y : ℂ) T v)
    (hord : ∀ t ∈ Icc (0 : ℝ) T, (u t).re < (v t).re)
    (hsign : ∀ t ∈ Icc (0 : ℝ) T, 0 < (u t).re * (v t).re) :
    (v T).re - (u T).re ≤ y - x := by
  have himu := im_isForwardSol_real hW hT hu
  have himv := im_isForwardSol_real hW hT hv
  set D : ℝ → ℝ := fun s => (v s + (W s : ℂ)).re - (u s + (W s : ℂ)).re with hD
  have hDe : ∀ s, D s = (v s).re - (u s).re := fun s => by simp [hD]
  have hderiv : ∀ s ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt D ((2 / v s).re - (2 / u s).re) (Icc 0 T) s := fun s hs => by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s (FwdHolo.hasDerivWithinAt_shift hv hs)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s (FwdHolo.hasDerivWithinAt_shift hu hs)
    exact h1.sub h2
  have hanti : AntitoneOn D (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun s => (2 / v s).re - (2 / u s).re)
      (fun s hs => (hderiv s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hderiv s (interior_subset hs)).mono interior_subset
    · have hs' := interior_subset hs
      rw [re_two_div_of_im_eq_zero (himv s hs'), re_two_div_of_im_eq_zero (himu s hs')]
      have h1 := hord s hs'
      have h2 := hsign s hs'
      have hu0 : (u s).re ≠ 0 := fun h => by rw [h, zero_mul] at h2; exact lt_irrefl _ h2
      have hv0 : (v s).re ≠ 0 := fun h => by rw [h, mul_zero] at h2; exact lt_irrefl _ h2
      rw [div_sub_div _ _ hv0 hu0]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by rw [mul_comm]; exact h2.le)
  have h0 := hanti ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  rw [hDe, hDe, FwdHolo.sol_zero hu hT, FwdHolo.sol_zero hv hT] at h0
  simp only [sub_re, ofReal_re] at h0
  linarith

/-- **The left band.** If `p_L < x' < 0` are alive at `T` (`W 0 = 0`), then
`f_T(p_L) < f_T(x') ≤ f_T(p_L) + (x' − p_L)`. -/
theorem band_of_isForwardSol_neg (hW : Continuous W) (hW0 : W 0 = 0) {pL x' T : ℝ} (hT : 0 ≤ T)
    (hx' : x' < 0) (hpx : pL < x') {u v : ℝ → ℂ} (hu : IsForwardSol W (pL : ℂ) T u)
    (hv : IsForwardSol W (x' : ℂ) T v) :
    (fwdMap W T pL).re < (fwdMap W T x').re ∧ (fwdMap W T x').re ≤ (fwdMap W T pL).re + (x' - pL) := by
  have hord : ∀ t ∈ Icc (0 : ℝ) T, (u t).re < (v t).re := fun t ht =>
    re_lt_of_isForwardSol_neg hW hW0 hx' hpx hu hv ht
  have hneg : ∀ t ∈ Icc (0 : ℝ) T, (v t).re < 0 := fun t ht => by
    have := re_fwdMap_neg hW hW0 hx' hv ht
    rwa [fwdMap_eq_of_isForwardSol hW hv ht] at this
  have hsign : ∀ t ∈ Icc (0 : ℝ) T, 0 < (u t).re * (v t).re := fun t ht =>
    mul_pos_of_neg_of_neg ((hord t ht).trans (hneg t ht)) (hneg t ht)
  have hle := re_sub_le_of_isForwardSol hW hT hu hv hord hsign
  rw [fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩]
  exact ⟨hord T ⟨hT, le_rfl⟩, by linarith⟩

/-- **The right band.** If `0 < x' < p_R` are alive at `T` (`W 0 = 0`), then
`f_T(p_R) − (p_R − x') ≤ f_T(x') < f_T(p_R)`. -/
theorem band_of_isForwardSol_pos (hW : Continuous W) (hW0 : W 0 = 0) {pR x' T : ℝ} (hT : 0 ≤ T)
    (hx' : 0 < x') (hpx : x' < pR) {u v : ℝ → ℂ} (hu : IsForwardSol W (pR : ℂ) T u)
    (hv : IsForwardSol W (x' : ℂ) T v) :
    (fwdMap W T pR).re - (pR - x') ≤ (fwdMap W T x').re ∧ (fwdMap W T x').re < (fwdMap W T pR).re := by
  have hord : ∀ t ∈ Icc (0 : ℝ) T, (v t).re < (u t).re := fun t ht =>
    re_lt_of_isForwardSol hW hW0 hx' hpx hv hu t ht
  have hpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (v t).re := fun t ht => by
    have := re_fwdMap_pos hW hW0 hx' hv ht
    rwa [fwdMap_eq_of_isForwardSol hW hv ht] at this
  have hsign : ∀ t ∈ Icc (0 : ℝ) T, 0 < (v t).re * (u t).re := fun t ht =>
    mul_pos (hpos t ht) ((hpos t ht).trans (hord t ht))
  have hle := re_sub_le_of_isForwardSol hW hT hv hu hord hsign
  rw [fwdMap_eq_of_isForwardSol hW hu ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hv ⟨hT, le_rfl⟩]
  exact ⟨by linarith, hord T ⟨hT, le_rfl⟩⟩

end Contraction

/-! ### Terminal cluster points -/

/-- `x` is a **terminal cluster point** of `η`: `η(t)` comes arbitrarily close to `x` at arbitrarily late times. -/
def IsTermCluster (η : ℝ≥0 → ℂ) (x : ℂ) : Prop := MapClusterPt x atTop η

theorem isTermCluster_iff_not {η : ℝ≥0 → ℂ} {x : ℂ} :
    IsTermCluster η x ↔ ¬ ∃ d > (0 : ℝ), ∀ᶠ t in atTop, d ≤ ‖η t - x‖ := by
  rw [IsTermCluster, mapClusterPt_iff_frequently]
  constructor
  · rintro h ⟨d, hd, hev⟩
    obtain ⟨t, ht1, ht2⟩ := ((h _ (ball_mem_nhds x hd)).and_eventually hev).exists
    rw [mem_ball, dist_eq_norm] at ht1
    linarith
  · intro h s hs
    obtain ⟨d, hd, hds⟩ := Metric.mem_nhds_iff.1 hs
    by_contra hf
    rw [not_frequently] at hf
    refine h ⟨d, hd, hf.mono fun t ht => ?_⟩
    by_contra hlt
    push Not at hlt
    exact ht (hds (by rw [mem_ball, dist_eq_norm]; exact hlt))

/-! ### The lifting lemma -/

section Lift

variable {w : ℝ≥0 → ℝ}

/-- **Lifting a real terminal cluster point through a restart** (B.3 L1251–L1256; additional note L1497–L1500: "Any
original lower cluster at or outside the two extremes would lift to a future lower cluster at or outside
`[c(T) − ξ_T, d(T) − ξ_T]`, by the full inverse assertion in (G1)"). Let `η` generate the chain of a continuous driver
`w` on `[0, ∞)`, `η₂` that of the driver restarted at `T`, and let the inverse boundary at `T` be interior ((G5)). If
`p_L`, `p_R` are alive at `T`, then every terminal cluster point `x ∈ (p_L, p_R)` of `η` gives a real terminal cluster
point of `η₂` in `[V_L, V_L − p_L] ∪ [V_R − p_R, V_R]` (`V_L`, `V_R` the centred images of `p_L`, `p_R` at `T`). -/
theorem exists_band_cluster (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {T : ℝ≥0} {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w T) ⊤ η₂)
    (hG5 : HasInteriorInverseBoundary (fun s : ℝ => w s.toNNReal) T) {pL pR : ℝ} {uL uR : ℝ → ℂ}
    (huL : IsForwardSol (fun s : ℝ => w s.toNNReal) (pL : ℂ) T uL)
    (huR : IsForwardSol (fun s : ℝ => w s.toNNReal) (pR : ℂ) T uR) {x : ℝ} (hxL : pL < x)
    (hxR : x < pR) (hcl : IsTermCluster η x) :
    ∃ y : ℝ, IsTermCluster η₂ y ∧
      (y ∈ Icc (fwdMap (fun s : ℝ => w s.toNNReal) T pL).re
          ((fwdMap (fun s : ℝ => w s.toNNReal) T pL).re - pL) ∨
        y ∈ Icc ((fwdMap (fun s : ℝ => w s.toNNReal) T pR).re - pR)
          (fwdMap (fun s : ℝ => w s.toNNReal) T pR).re) := by
  set Wr : ℝ → ℝ := fun s : ℝ => w s.toNNReal with hWr
  have hWrc : Continuous Wr := hw.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simp [hWr, hw0]
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  -- the extension `F̄_T` and the join
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := T) ENNReal.coe_lt_top
  have hσt₂ : (T : ℝ) < (T : ℝ) + 1 := lt_add_one _
  have hfc : Continuous (frozenDrive w ((T : ℝ) + 1)) := continuous_frozenDrive hw.continuousOn
  obtain ⟨hF, -, hEq, hcont, -, ⟨C, hC⟩, -⟩ := h₁.extend_props hσt₂ hfc hw0
  set Fb := extendFrom H (fwdMapInv (frozenDrive w ((T : ℝ) + 1)) T) with hFb
  have hEq' : EqOn Fb (fwdMapInv Wr T) H := fun z hz => by rw [hEq hz, hF]
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (T : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hjoin, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have hjoinF : ∀ t : ℝ≥0, T < t → η t = Fb (η₂ (t - T)) := by
    intro t ht
    rw [hη.eq_of_le hjoin hwc hw0 le_top, Sec7.joinTrace_of_lt ht, hF]
  have hw₂ : Continuous fun s : ℝ => Sec7.shiftNN w T s.toNNReal := by
    unfold Sec7.shiftNN
    exact ((hw.comp (continuous_const.add continuous_id)).sub continuous_const).comp continuous_real_toNNReal
  have hη₂H : ∀ s, η₂ s ∈ Hbar := fun s =>
    Sec4.im_nonneg_of_isGeneratingTrace hw₂ (Sec7.shiftNN_zero w T) hη₂ s
  have hf0 : frozenDrive w ((T : ℝ) + 1) 0 = 0 := by
    simp [frozenDrive, min_eq_left (show (0 : ℝ) ≤ (T : ℝ) + 1 by positivity), hw0]
  have hFbH : ∀ z ∈ H, Fb z ∈ H := fun z hz => by
    rw [hEq hz]
    exact QuantumZipper.RS.fwdMapInv_mem_H hfc hf0 T.coe_nonneg hz
  -- Step 1: `x` is a terminal cluster point of `F̄ ∘ η₂`
  have hcl₂ : MapClusterPt (x : ℂ) atTop fun s => Fb (η₂ s) := by
    rw [IsTermCluster, mapClusterPt_iff_frequently] at hcl
    rw [mapClusterPt_iff_frequently]
    intro S hS
    have h1 : ∃ᶠ t in atTop, Fb (η₂ (t - T)) ∈ S := by
      refine (hcl S hS).mp ((eventually_gt_atTop T).mono fun t ht h => ?_)
      rwa [← hjoinF t ht]
    have htend : Tendsto (fun t : ℝ≥0 => t - T) atTop atTop :=
      tendsto_atTop.2 fun b => (eventually_ge_atTop (b + T)).mono fun t ht =>
        le_tsub_of_add_le_right ht
    exact htend.frequently h1
  -- Step 2: compactness gives a cluster point `y` of `η₂` with `F̄ y = x`
  have hseq : ∀ n : ℕ, ∃ s : ℝ≥0, (n : ℝ≥0) ≤ s ∧ ‖Fb (η₂ s) - x‖ < 1 / ((n : ℝ) + 1) := fun n => by
    have hb := mapClusterPt_iff_frequently.1 hcl₂ _
      (ball_mem_nhds (x : ℂ) (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
    obtain ⟨s, hs1, hs2⟩ := (hb.and_eventually (eventually_ge_atTop (n : ℝ≥0))).exists
    exact ⟨s, hs2, by rwa [mem_ball, dist_eq_norm] at hs1⟩
  choose s hs using hseq
  set K : Set ℂ := closedBall (0 : ℂ) (‖(x : ℂ)‖ + 1 + C) ∩ Hbar with hK
  have hHbc : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right hHbc
  have hyK : ∀ n, η₂ (s n) ∈ K := fun n => by
    refine ⟨?_, hη₂H _⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 := hC _ (hη₂H (s n))
    have h2 := (hs n).2
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    calc ‖η₂ (s n)‖ ≤ ‖(x : ℂ)‖ + ‖Fb (η₂ (s n)) - x‖ + ‖Fb (η₂ (s n)) - η₂ (s n)‖ := by
          have e : η₂ (s n) = x + (Fb (η₂ (s n)) - x) - (Fb (η₂ (s n)) - η₂ (s n)) := by ring
          calc ‖η₂ (s n)‖ = ‖(x : ℂ) + (Fb (η₂ (s n)) - x) - (Fb (η₂ (s n)) - η₂ (s n))‖ := by
                rw [← e]
            _ ≤ ‖(x : ℂ) + (Fb (η₂ (s n)) - x)‖ + ‖Fb (η₂ (s n)) - η₂ (s n)‖ := norm_sub_le _ _
            _ ≤ _ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖(x : ℂ)‖ + 1 + C := by linarith
  obtain ⟨y, hyKm, φ, hφ, hlim⟩ := hKc.tendsto_subseq hyK
  have hsφ : Tendsto (fun n => s (φ n)) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge (b : ℝ)
    refine (eventually_ge_atTop m).mono fun n hn => ?_
    have h1 : (m : ℝ≥0) ≤ (φ n : ℝ≥0) := by exact_mod_cast hn.trans (hφ.id_le n)
    rw [← NNReal.coe_le_coe] at h1 ⊢
    exact hm.trans (h1.trans (by exact_mod_cast (hs (φ n)).1))
  have hcly : IsTermCluster η₂ y := MapClusterPt.of_comp hsφ hlim.mapClusterPt
  have hFy : Fb y = x := by
    have hA : Tendsto (fun n => Fb (η₂ (s (φ n)))) atTop (𝓝 (Fb y)) :=
      (hcont y hyKm.2).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hη₂H _⟩)
    have hB : Tendsto (fun n => Fb (η₂ (s (φ n)))) atTop (𝓝 (x : ℂ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ((hs (φ n)).2).le.trans ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      have : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    exact tendsto_nhds_unique hA hB
  -- Step 3: `y` is real
  have hyim : y.im = 0 := by
    rcases (show 0 ≤ y.im from hyKm.2).lt_or_eq with hpos | hzero
    · have := hFbH y hpos
      rw [hFy] at this
      exact absurd this (by simp [H])
    · exact hzero.symm
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
  -- Step 4: `y` lies in the exterior coordinates
  have hyext : y.re ∈ exteriorCoords Wr T := by
    by_contra hne
    obtain ⟨p, hpH, hp⟩ := hG5 y.re hne
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := ((y.re : ℝ) : ℂ)) (by simp)
    have h1 : Tendsto Fb (𝓝[H] ((y.re : ℝ) : ℂ)) (𝓝 (x : ℂ)) := by
      rw [← hyr, ← hFy]
      exact ((hcont y hyKm.2).mono fun z (hz : 0 < z.im) => le_of_lt hz).tendsto
    have h2 : Tendsto Fb (𝓝[H] ((y.re : ℝ) : ℂ)) (𝓝 p) :=
      hp.congr' (eventually_nhdsWithin_of_forall fun z hz => (hEq' hz).symm)
    have := tendsto_nhds_unique h1 h2
    rw [← this] at hpH
    exact absurd hpH (by simp [H])
  -- Step 5: the band
  obtain ⟨r, hrS, hr⟩ := mem_closure_iff_seq_limit.1 hyext
  choose x' hx'alive hx'r using hrS
  choose v hv using hx'alive
  have hFx' : ∀ n, Fb (r n) = x' n := fun n => by
    have h := extension_fwdMap_eq_of_isForwardSol hWrc hWr0 hT0 hEq' hcont (hv n)
    rwa [fwdMap_eq_ofReal_re hWrc (hv n) ⟨hT0, le_rfl⟩, hx'r n] at h
  have hx'lim : Tendsto x' atTop (𝓝 x) := by
    have hc : Tendsto (fun n => ((r n : ℝ) : ℂ)) atTop (𝓝 y) := by
      rw [hyr]; exact (Complex.continuous_ofReal.tendsto _).comp hr
    have h := (hcont y hyKm.2).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hc, Eventually.of_forall fun n => show (0 : ℝ) ≤ ((r n : ℝ) : ℂ).im by simp⟩)
    rw [hFy] at h
    have h' : Tendsto (fun n => ((x' n : ℝ) : ℂ)) atTop (𝓝 (x : ℂ)) :=
      h.congr fun n => by simp only [Function.comp_apply, hFx' n]
    exact (Complex.continuous_re.tendsto _).comp h' |>.congr (fun n => by simp) |>.trans (by simp)
  have hB : IsClosed (Icc (fwdMap Wr T pL).re ((fwdMap Wr T pL).re - pL) ∪
      Icc ((fwdMap Wr T pR).re - pR) (fwdMap Wr T pR).re) := isClosed_Icc.union isClosed_Icc
  have hev : ∀ᶠ n in atTop, r n ∈ Icc (fwdMap Wr T pL).re ((fwdMap Wr T pL).re - pL) ∪
      Icc ((fwdMap Wr T pR).re - pR) (fwdMap Wr T pR).re := by
    filter_upwards [hx'lim (Ioo_mem_nhds hxL hxR)] with n hn
    rw [← hx'r n]
    rcases lt_trichotomy (x' n) 0 with hneg | hzero | hpos
    · obtain ⟨h1, h2⟩ := band_of_isForwardSol_neg hWrc hWr0 hT0 hneg hn.1 huL (hv n)
      exact Or.inl ⟨h1.le, by linarith⟩
    · exact absurd (hzero ▸ hv n) (not_isForwardSol_zero hWr0 hT0)
    · obtain ⟨h1, h2⟩ := band_of_isForwardSol_pos hWrc hWr0 hT0 hpos hn.2 huR (hv n)
      exact Or.inr ⟨by linarith, h2.le⟩
  refine ⟨y.re, by rw [← hyr]; exact hcly, hB.mem_of_tendsto hr hev⟩

end Lift

end InteractingSLE.ZhanGT4
