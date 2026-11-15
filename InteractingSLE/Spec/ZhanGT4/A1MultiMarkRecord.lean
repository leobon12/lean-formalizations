/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkLarge
import LQGDimension.LFPP.SegCombLaw
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Zhan's A.1 (R80): the family's noise and stop events on the stopped records

Packet PROVE-A1-MULTIMARK. `A1Family.FamilyRect.ofRect` (and its mirror) asks, for every rectangle `m`, that the image
data before the cap agree with functions measurable for the product `𝓜` of the two stopped records (`hgW`, `hgVL`,
`hgVR`, `hgN`), that the noise stopped at the cap and the cap be `𝓜`-measurable (`hNs`, `hSm`), and that the events of
the stopped σ-algebra `𝓔` of the conditioning curve before the cap be `𝓜`-events (`hstop`). Here the noise and stop
premises are reduced to the driver and force premises and to the cap:

* `exists_measurable_of_tendsto`: a pointwise limit on any set has a measurable version there;
* `tendsto_riemann_Icc`: left Riemann sums of a function continuous on `[a, b]` converge (the host's
  `LQGDimension.SegLaw.tendsto_riemannSum`, after an affine change of variable);
* **`exists_measurable_integral_before`**: the integral `∫₀ʳ g` has a measurable version before the cap, from measurable
  versions of the integrand at each time before the cap, continuity on `(0, r]` and integrability on `[0, r]` (a
  singular entrance at `0`, as for seeds, is allowed);
* **`exists_measurable_seedCapacityNoise_before`**, **`exists_measurable_noise_of_geometry`**: `hgN` for the residual
  noise `seedCapacityNoise` from `hgW`, `hgVL`, `hgVR` and the deterministic geometry before the cap;
* **`measurable_stopped_of_before`**: `hNs` from `hgN`, `hSm`, continuity and `N 0 = 0`;
* `measurable_eval_at`: a continuous process at a measurable random time (the form of a cap `a(T)`);
* **`measurableSet_fst_inter_cap`**, **`measurableSet_snd_inter_cap`**: `hstop` when the cap vanishes once the frozen
  time is after the conditioning curve's rectangle exit and the conditioning record is stopped at `τ ∧ S_kᵐ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1MultiMark

/-! ### Measurable versions of limits and integrals -/

section Generic

variable {Z : Type*} [𝓜 : MeasurableSpace Z]

/-- **A pointwise limit on any set has a measurable version there** (Mathlib's `StronglyMeasurable.limUnder`). -/
theorem exists_measurable_of_tendsto {f : ℕ → Z → ℝ} (hf : ∀ n, Measurable (f n)) {E : Set Z} {F : Z → ℝ}
    (h : ∀ z ∈ E, Tendsto (f · z) atTop (𝓝 (F z))) : ∃ G : Z → ℝ, Measurable G ∧ ∀ z ∈ E, F z = G z :=
  ⟨fun z => limUnder atTop (f · z), (StronglyMeasurable.limUnder fun n => (hf n).stronglyMeasurable).measurable,
    fun z hz => ((h z hz).limUnder_eq).symm⟩

omit 𝓜 in
/-- **Left Riemann sums of a function continuous on `[a, b]` converge** to its integral (the host's
`LQGDimension.SegLaw.tendsto_riemannSum` after the change of variable `s = a + u (b − a)`). -/
theorem tendsto_riemann_Icc {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn h (Icc a b)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, (b - a) * h (a + (k : ℝ) / N * (b - a))) atTop
      (𝓝 (∫ s in a..b, h s)) := by
  set h' : ℝ → ℝ := fun s => h (max a (min s b)) with hh'
  have hc' : Continuous h' := hc.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
    fun s => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have heq : ∀ s ∈ Icc a b, h' s = h s := fun s hs => by
    simp only [hh', min_eq_left hs.2, max_eq_right hs.1]
  set g : ℝ → ℝ := fun u => (b - a) * h' ((b - a) * u + a) with hg
  have hgc : Continuous g := continuous_const.mul (hc'.comp ((continuous_const.mul continuous_id).add continuous_const))
  have hint : ∫ u in (0 : ℝ)..1, g u = ∫ s in a..b, h s := by
    have h1 : ∫ u in (0 : ℝ)..1, g u = (b - a) • ∫ u in (0 : ℝ)..1, h' ((b - a) * u + a) := by
      rw [hg, intervalIntegral.integral_const_mul, smul_eq_mul]
    rw [h1, intervalIntegral.smul_integral_comp_mul_add]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    exact heq s hs
  have hlim := LQGDimension.SegLaw.tendsto_riemannSum hgc
  rw [hint] at hlim
  refine hlim.congr fun N => ?_
  simp only [LQGDimension.SegLaw.riemannSum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : (k : ℝ) < N := by exact_mod_cast Finset.mem_range.1 hk
  have hN : (0 : ℝ) < N := lt_of_le_of_lt (Nat.cast_nonneg k) hkN
  have hu0 : 0 ≤ (k : ℝ) / N := div_nonneg (Nat.cast_nonneg k) hN.le
  have hu1 : (k : ℝ) / N ≤ 1 := (div_le_one hN).2 hkN.le
  have hmem : a + (k : ℝ) / N * (b - a) ∈ Icc a b :=
    ⟨by nlinarith [sub_nonneg.2 hab], by nlinarith [sub_nonneg.2 hab]⟩
  simp only [hg]
  rw [show (b - a) * ((k : ℝ) / N) + a = a + (k : ℝ) / N * (b - a) by ring, heq _ hmem]

/-- **The integral of a process before the cap has a measurable version** (Riemann sums on `[ε, r]` at times in
`(0, r]`, then `ε → 0`): if at each time the integrand agrees before the cap with a measurable function, and for each
sample before the cap it is continuous on `(0, r]` and integrable on `[0, r]`, then `z ↦ ∫₀ʳ g(s, z) ds` agrees before
the cap with a measurable function. A singular entrance at `0` (a seed) is allowed. -/
theorem exists_measurable_integral_before {cap : Z → ℝ≥0} {g : ℝ≥0 → Z → ℝ} {r : ℝ≥0}
    (hg : ∀ s : ℝ≥0, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z → 0 < s → s ≤ r → g s z = f z)
    (hc : ∀ z, r < cap z → ContinuousOn (fun s : ℝ => g s.toNNReal z) (Ioc 0 r))
    (hi : ∀ z, r < cap z → IntervalIntegrable (fun s : ℝ => g s.toNNReal z) volume 0 r) :
    ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z → ∫ s in (0 : ℝ)..r, g s.toNNReal z = f z := by
  choose fg hfg hfge using hg
  rcases eq_or_lt_of_le (zero_le (a := r)) with hr | hr
  · refine ⟨fun _ => 0, measurable_const, fun z _ => ?_⟩
    rw [← hr, NNReal.coe_zero, intervalIntegral.integral_same]
  have hr' : (0 : ℝ) < r := hr
  set ε : ℕ → ℝ := fun k => (r : ℝ) / ((k : ℝ) + 2) with hεdef
  have hε0 (k : ℕ) : 0 < ε k := div_pos hr' (by positivity)
  have hεr (k : ℕ) : ε k ≤ r := div_le_self hr'.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hεt : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa only [hεdef] using h1.const_div_atTop (r : ℝ)
  have hinner (k : ℕ) : ∃ F : Z → ℝ, Measurable F ∧
      ∀ z ∈ {z | r < cap z}, ∫ s in ε k..r, g s.toNNReal z = F z := by
    refine exists_measurable_of_tendsto (f := fun N z => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
      ((r : ℝ) - ε k) * fg (ε k + (j : ℝ) / N * ((r : ℝ) - ε k)).toNNReal z) (fun N => ?_) fun z hz => ?_
    · exact (Finset.measurable_sum _ fun j _ => (hfg _).const_mul _).const_mul _
    · have hcon : ContinuousOn (fun s : ℝ => g s.toNNReal z) (Icc (ε k) r) :=
        (hc z hz).mono fun s hs => ⟨(hε0 k).trans_le hs.1, hs.2⟩
      refine (tendsto_riemann_Icc (hεr k) hcon).congr fun N => ?_
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjN : (j : ℝ) < N := by exact_mod_cast Finset.mem_range.1 hj
      have hN : (0 : ℝ) < N := lt_of_le_of_lt (Nat.cast_nonneg j) hjN
      have hu0 : 0 ≤ (j : ℝ) / N := div_nonneg (Nat.cast_nonneg j) hN.le
      have hu1 : (j : ℝ) / N ≤ 1 := (div_le_one hN).2 hjN.le
      have hd : 0 ≤ (r : ℝ) - ε k := sub_nonneg.2 (hεr k)
      have hpos : 0 < ε k + (j : ℝ) / N * ((r : ℝ) - ε k) := by nlinarith [hε0 k]
      have hle : ε k + (j : ℝ) / N * ((r : ℝ) - ε k) ≤ r := by nlinarith
      rw [hfge _ z hz (Real.toNNReal_pos.2 hpos) (Real.toNNReal_le_iff_le_coe.2 hle)]
  choose F hF hFe using hinner
  refine exists_measurable_of_tendsto hF fun z hz => ?_
  have hiz := hi z hz
  have hprim := intervalIntegral.continuousOn_primitive_interval' hiz (left_mem_uIcc (a := (0 : ℝ)) (b := r))
  have h0 : (0 : ℝ) ∈ uIcc (0 : ℝ) r := left_mem_uIcc
  have hmem (k : ℕ) : ε k ∈ uIcc (0 : ℝ) r := by rw [uIcc_of_le hr'.le]; exact ⟨(hε0 k).le, hεr k⟩
  have hlim0 : Tendsto (fun k => ∫ s in (0 : ℝ)..ε k, g s.toNNReal z) atTop (𝓝 0) := by
    have h := (hprim 0 h0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hεt, Eventually.of_forall hmem⟩)
    simpa only [Function.comp_def, intervalIntegral.integral_same] using h
  have hsplit (k : ℕ) : F k z = (∫ s in (0 : ℝ)..r, g s.toNNReal z) - ∫ s in (0 : ℝ)..ε k, g s.toNNReal z := by
    rw [← hFe k z hz, intervalIntegral.integral_interval_sub_left hiz
      (hiz.mono_set (by rw [uIcc_of_le (hε0 k).le, uIcc_of_le hr'.le]; exact Icc_subset_Icc le_rfl (hεr k)))]
  simp only [hsplit]
  simpa only [sub_zero] using tendsto_const_nhds.sub hlim0

/-! ### The residual noise before the cap (`hgN`) -/

/-- **`hgN` for the residual noise** (`seedCapacityNoise`): if the driver and the force points agree before the cap with
measurable functions at each time (`hgW`, `hgVL`, `hgVR`), and before the cap each gap is continuous and nonzero on
`(0, r]` with integrable reciprocal on `[0, r]`, then the residual noise at `r` agrees before the cap with a measurable
function. -/
theorem exists_measurable_seedCapacityNoise_before {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {cap : Z → ℝ≥0} {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ} (r : ℝ≥0)
    (hW : ∀ s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → W s z = f z)
    (hVL : ∀ i s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → VL i s z = f z)
    (hVR : ∀ j s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → VR j s z = f z)
    (hcW : ∀ z, r < cap z → ContinuousOn (fun s : ℝ => W s.toNNReal z) (Ioc 0 r))
    (hcL : ∀ z, r < cap z → ∀ i, ContinuousOn (fun s : ℝ => VL i s.toNNReal z) (Ioc 0 r))
    (hcR : ∀ z, r < cap z → ∀ j, ContinuousOn (fun s : ℝ => VR j s.toNNReal z) (Ioc 0 r))
    (hneL : ∀ z, r < cap z → ∀ i, ∀ s ∈ Ioc (0 : ℝ) r, W s.toNNReal z ≠ VL i s.toNNReal z)
    (hneR : ∀ z, r < cap z → ∀ j, ∀ s ∈ Ioc (0 : ℝ) r, W s.toNNReal z ≠ VR j s.toNNReal z)
    (hiL : ∀ z, r < cap z → ∀ i,
      IntervalIntegrable (fun s : ℝ => (W s.toNNReal z - VL i s.toNNReal z)⁻¹) volume 0 r)
    (hiR : ∀ z, r < cap z → ∀ j,
      IntervalIntegrable (fun s : ℝ => (W s.toNNReal z - VR j s.toNNReal z)⁻¹) volume 0 r) :
    ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z →
      seedCapacityNoise κ ρL ρR (W · z) (fun i s => VL i s z) (fun j s => VR j s z) r = f z := by
  have hint (V : ℝ≥0 → Z → ℝ) (ρ : ℝ) (hV : ∀ s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → V s z = f z)
      (hcV : ∀ z, r < cap z → ContinuousOn (fun s : ℝ => V s.toNNReal z) (Ioc 0 r))
      (hne : ∀ z, r < cap z → ∀ s ∈ Ioc (0 : ℝ) r, W s.toNNReal z ≠ V s.toNNReal z)
      (hi : ∀ z, r < cap z → IntervalIntegrable (fun s : ℝ => (W s.toNNReal z - V s.toNNReal z)⁻¹) volume 0 r) :
      ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z →
        ∫ s in (0 : ℝ)..r, ρ / (W s.toNNReal z - V s.toNNReal z) = f z := by
    refine exists_measurable_integral_before (g := fun s z => ρ / (W s z - V s z)) (fun s => ?_)
      (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨fW, hfW, hfWe⟩ := hW s
      obtain ⟨fV, hfV, hfVe⟩ := hV s
      refine ⟨fun z => ρ / (fW z - fV z), measurable_const.div (hfW.sub hfV), fun z hz _ hsr => ?_⟩
      simp only [hfWe z (hsr.trans_lt hz), hfVe z (hsr.trans_lt hz)]
    · exact continuousOn_const.div ((hcW z hz).sub (hcV z hz)) fun s hs => sub_ne_zero.2 (hne z hz s hs)
    · simpa only [div_eq_mul_inv] using (hi z hz).const_mul ρ
  obtain ⟨fW, hfW, hfWe⟩ := hW r
  choose fL hfL hfLe using fun i => hint (VL i) (ρL i) (hVL i) (fun z hz => hcL z hz i) (fun z hz => hneL z hz i)
    (fun z hz => hiL z hz i)
  choose fR hfR hfRe using fun j => hint (VR j) (ρR j) (hVR j) (fun z hz => hcR z hz j) (fun z hz => hneR z hz j)
    (fun z hz => hiR z hz j)
  refine ⟨fun z => (fW z - ∑ i, fL i z - ∑ j, fR j z) / Real.sqrt κ, ?_, fun z hz => ?_⟩
  · exact ((hfW.sub (Finset.measurable_sum _ fun i _ => hfL i)).sub
      (Finset.measurable_sum _ fun j _ => hfR j)).div_const _
  · simp only [seedCapacityNoise, hfWe z hz, fun i => hfLe i z hz, fun j => hfRe j z hz]

/-- **`hgN` from the deterministic geometry before the cap**: if at every sample with a positive cap the driver and the
force points stopped at the cap have `SeedImageGeometry` up to the cap (A1-FAMILY's `hgeom`, here at every such
sample), and the driver and the force points agree before the cap with measurable functions at each time, then so does
the residual noise. -/
theorem exists_measurable_noise_of_geometry {nL nR : ℕ} (κ : ℝ) {xL : Z → Fin nL → ℝ} {xR : Z → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {cap : Z → ℝ≥0} {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ}
    {VR : Fin nR → ℝ≥0 → Z → ℝ}
    (hW : ∀ s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → W s z = f z)
    (hVL : ∀ i s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → VL i s z = f z)
    (hVR : ∀ j s, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, s < cap z → VR j s z = f z)
    (hgeo : ∀ z, 0 < cap z → SeedImageGeometry (xL z) (xR z) ρL ρR (fun t => W (min t (cap z)) z)
      (fun i t => VL i (min t (cap z)) z) (fun j t => VR j (min t (cap z)) z) (cap z)) (r : ℝ≥0) :
    ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z →
      seedCapacityNoise κ ρL ρR (W · z) (fun i s => VL i s z) (fun j s => VR j s z) r = f z := by
  have hpos {z : Z} (hz : r < cap z) : 0 < cap z := lt_of_le_of_lt (zero_le (a := r)) hz
  have hmin {z : Z} (hz : r < cap z) {s : ℝ} (hs : s ≤ r) : min s.toNNReal (cap z) = s.toNNReal :=
    min_eq_left ((Real.toNNReal_le_iff_le_coe.2 hs).trans hz.le)
  have hcont {z : Z} (hz : r < cap z) {f : ℝ≥0 → ℝ} (hf : Continuous fun t => f (min t (cap z))) :
      ContinuousOn (fun s : ℝ => f s.toNNReal) (Ioc 0 r) :=
    ((hf.comp continuous_real_toNNReal).continuousOn).congr fun s hs => by
      simp only [Function.comp_apply, hmin hz hs.2]
  have hint {z : Z} (hz : r < cap z) {w v : ℝ≥0 → ℝ}
      (hi : IntervalIntegrable (fun s : ℝ => (w (min s.toNNReal (cap z)) - v (min s.toNNReal (cap z)))⁻¹) volume 0 r) :
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 r :=
    hi.congr fun s hs => by
      rw [uIoc_of_le r.coe_nonneg] at hs
      simp only [hmin hz hs.2]
  refine exists_measurable_seedCapacityNoise_before κ ρL ρR r hW hVL hVR
    (fun z hz => hcont hz (f := fun t => W t z) (hgeo z (hpos hz)).continuous_w)
    (fun z hz i => hcont hz (f := fun t => VL i t z) ((hgeo z (hpos hz)).continuous_left i))
    (fun z hz j => hcont hz (f := fun t => VR j t z) ((hgeo z (hpos hz)).continuous_right j))
    (fun z hz i s hs => ?_) (fun z hz j s hs => ?_)
    (fun z hz i => hint hz (w := fun t => W t z) (v := fun t => VL i t z)
      ((hgeo z (hpos hz)).integrable_left r hz.le i))
    (fun z hz j => hint hz (w := fun t => W t z) (v := fun t => VR j t z)
      ((hgeo z (hpos hz)).integrable_right r hz.le j))
  · have h := (hgeo z (hpos hz)).left_lt s.toNNReal (Real.toNNReal_pos.2 hs.1)
      ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hz.le) i
    simp only [hmin hz hs.2] at h
    exact h.ne'
  · have h := (hgeo z (hpos hz)).right_gt s.toNNReal (Real.toNNReal_pos.2 hs.1)
      ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hz.le) j
    simp only [hmin hz hs.2] at h
    exact h.ne

/-! ### The noise stopped at the cap (`hNs`) -/

/-- **`hNs` from `hgN` and `hSm`**: a process that is continuous in time, `0` at time `0`, and agrees before a
measurable cap with a measurable function at each time, is measurable at the cap: `z ↦ N(t ∧ cap z, z)` is measurable
(the dyadic times strictly below `t ∧ cap` approximate it from below). -/
theorem measurable_stopped_of_before {N : ℝ≥0 → Z → ℝ} {cap : Z → ℝ≥0} (hcap : Measurable cap)
    (hN : ∀ r, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z → N r z = f z)
    (hNc : ∀ z, Continuous (N · z)) (hN0 : ∀ z, N 0 z = 0) (t : ℝ≥0) :
    Measurable fun z => N (min t (cap z)) z := by
  choose f hf hfe using hN
  set m : Z → ℝ := fun z => ((min t (cap z) : ℝ≥0) : ℝ) with hmdef
  have hmm : Measurable m := (measurable_const.min hcap).coe_nnreal_real
  set k : ℕ → Z → ℕ := fun n z => ⌈(2 : ℝ) ^ n * m z⌉₊ - 1 with hkdef
  have hkm (n : ℕ) : Measurable (k n) :=
    (measurable_from_nat (f := fun j : ℕ => j - 1)).comp (measurable_const.mul hmm).nat_ceil
  set q : ℕ → ℕ → ℝ≥0 := fun n j => (j : ℝ≥0) / 2 ^ n with hqdef
  set g : ℕ → Z → ℝ := fun n z => if 0 < m z then f (q n (k n z)) z else 0 with hgdef
  have hgm (n : ℕ) : Measurable (g n) :=
    Measurable.ite (measurableSet_lt measurable_const hmm)
      (A1Marg.measurable_eval_nat (F := fun j => f (q n j)) (fun j => hf _) (hkm n)) measurable_const
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun z => ?_)
  by_cases hz : 0 < m z
  · -- the dyadic times below `t ∧ cap z`
    have hq (n : ℕ) : ((q n (k n z) : ℝ≥0) : ℝ) = ((⌈(2 : ℝ) ^ n * m z⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n := by
      simp only [hqdef, hkdef, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    have hx (n : ℕ) : 0 < (2 : ℝ) ^ n * m z := mul_pos (by positivity) hz
    have hc1 (n : ℕ) : 1 ≤ ⌈(2 : ℝ) ^ n * m z⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (hx n)).ne'
    have hcast (n : ℕ) : ((⌈(2 : ℝ) ^ n * m z⌉₊ - 1 : ℕ) : ℝ) = (⌈(2 : ℝ) ^ n * m z⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub (hc1 n), Nat.cast_one]
    have hlt (n : ℕ) : ((q n (k n z) : ℝ≥0) : ℝ) < m z := by
      rw [hq, hcast, div_lt_iff₀ (by positivity)]
      have := Nat.ceil_lt_add_one (hx n).le
      linarith
    have hge (n : ℕ) : m z - 1 / 2 ^ n ≤ ((q n (k n z) : ℝ≥0) : ℝ) := by
      rw [hq, hcast]
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      have := Nat.le_ceil ((2 : ℝ) ^ n * m z)
      have e : m z - 1 / 2 ^ n = ((2 : ℝ) ^ n * m z - 1) / 2 ^ n := by field_simp
      rw [e]
      exact (div_le_div_iff_of_pos_right h2).2 (by linarith)
    have hqt : Tendsto (fun n => q n (k n z)) atTop (𝓝 (min t (cap z))) := by
      rw [← NNReal.tendsto_coe]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hge fun n => (hlt n).le
      have h2 : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
        simpa only [one_div, Function.comp_def] using
          tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
      simpa only [sub_zero] using tendsto_const_nhds.sub h2
    refine ((hNc z).tendsto _).comp hqt |>.congr fun n => ?_
    have hcz : q n (k n z) < cap z := by
      have h1 : ((q n (k n z) : ℝ≥0) : ℝ) < ((cap z : ℝ≥0) : ℝ) :=
        (hlt n).trans_le (NNReal.coe_le_coe.2 (min_le_right _ _))
      exact_mod_cast h1
    simp only [Function.comp_apply, hgdef, hz, ↓reduceIte, hfe _ z hcz]
  · have h0 : min t (cap z) = 0 := by
      have : ((min t (cap z) : ℝ≥0) : ℝ) = 0 := le_antisymm (not_lt.1 hz) (NNReal.coe_nonneg _)
      exact NNReal.coe_eq_zero.1 this
    simp only [hgdef, hz, ↓reduceIte, h0, hN0]
    exact tendsto_const_nhds

/-- **A continuous process read at a measurable random time is measurable** (Carathéodory: continuous in time,
measurable at each time; Mathlib's `measurable_uncurry_of_continuous_of_measurable`). This is the form in which a cap
`a(T(z))` (a continuous capacity clock at a measurable own exit `T`) is a record-measurable function. -/
theorem measurable_eval_at {U : ℝ≥0 → Z → ℝ} (hU : ∀ t, Measurable (U t)) (hc : ∀ z, Continuous (U · z))
    {T : Z → ℝ≥0} (hT : Measurable T) : Measurable fun z => U (T z) z :=
  (measurable_uncurry_of_continuous_of_measurable hc hU).comp (hT.prodMk measurable_id)

end Generic

/-! ### Events of the stopped σ-algebra before the cap (`hstop`) -/

section Stop

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

omit mX in
/-- **`hstop`, conditioning curve on `Y`**: if the conditioning record is stopped at `τ ∧ ρ` (`ρ` the rectangle exit)
and the cap event `{s < cap}` is a record event contained in `{τ ≤ ρ}` (the cap vanishes once the frozen time is after
the rectangle exit), then every event `B` of the stopped σ-algebra at `τ` gives the record event
`{y ∈ B} ∩ {s < cap}`. -/
theorem measurableSet_snd_inter_cap {𝓖 : Filtration ℝ≥0 mY} {τ ρ : Y → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hρ : IsStoppingTime 𝓖 ρ) {𝓐 : MeasurableSpace X} {cap : X × Y → ℝ≥0} {s : ℝ≥0}
    (hcap : MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 (hτ.min hρ).measurableSpace] {z | s < cap z})
    (hle : ∀ z, s < cap z → τ z.2 ≤ ρ z.2) {B : Set Y} (hB : MeasurableSet[hτ.measurableSpace] B) :
    MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 (hτ.min hρ).measurableSpace]
      (Prod.snd ⁻¹' B ∩ {z | s < cap z}) := by
  have e : Prod.snd ⁻¹' B ∩ {z : X × Y | s < cap z} =
      Prod.snd ⁻¹' (B ∩ {y | τ y ≤ ρ y}) ∩ {z | s < cap z} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.1, hle z h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [e]
  exact (@measurable_snd X Y 𝓐 (hτ.min hρ).measurableSpace _ (hτ.measurableSet_inter_le hρ B hB)).inter hcap

omit mY in
/-- **`hstop`, conditioning curve on `X`** (mirror of `measurableSet_snd_inter_cap`). -/
theorem measurableSet_fst_inter_cap {𝓖 : Filtration ℝ≥0 mX} {τ ρ : X → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hρ : IsStoppingTime 𝓖 ρ) {𝓑 : MeasurableSpace Y} {cap : X × Y → ℝ≥0} {s : ℝ≥0}
    (hcap : MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min hρ).measurableSpace 𝓑] {z | s < cap z})
    (hle : ∀ z, s < cap z → τ z.1 ≤ ρ z.1) {B : Set X} (hB : MeasurableSet[hτ.measurableSpace] B) :
    MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min hρ).measurableSpace 𝓑]
      (Prod.fst ⁻¹' B ∩ {z | s < cap z}) := by
  have e : Prod.fst ⁻¹' B ∩ {z : X × Y | s < cap z} =
      Prod.fst ⁻¹' (B ∩ {x | τ x ≤ ρ x}) ∩ {z | s < cap z} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨h.1, hle z h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [e]
  exact (@measurable_fst X Y (hτ.min hρ).measurableSpace 𝓑 _ (hτ.measurableSet_inter_le hρ B hB)).inter hcap

end Stop

end InteractingSLE.ZhanGT4.A1MultiMark
