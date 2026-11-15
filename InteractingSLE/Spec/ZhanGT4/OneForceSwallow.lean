/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.OneForceMark
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBessel

/-!
# The separated one-force law swallows every positive point (Part B.2, (E7))

Packet PROVE-ZHAN-GT4-B3. Source: Astra, *Follow-up proofs and dependency audit*, §B.2 L1113–L1125 (ruling R38): "Next
take a lower point `x₀ > R_ε + 1` … The scale exit formula therefore makes the probability of reaching zero before level
`M` tend to one … Thus the swallowing time `T` of `x₀` is finite almost surely." (Additional note, Lemma 3.2,
L1427–L1433,
ruling R39.)

In the chordal picture no scale function is needed for `κ > 4`. For a left force `ρ ≥ κ/2 − 2 > 0` the driver is
`W = √κ B + ∫ ρ/(W − V)`, with a nonnegative, nondecreasing drift. The centred flow `u_t = g_t(x₀) − W_t` of `x₀ > 0`
solves `u' = 2/u − W'`, so it stays below the centred flow of `x₀` driven by `√κ B` alone (an ordinary `SLE_κ`):
`(u − v)' = 2/u − 2/v − ρ/(W − V) ≤ 0` wherever `u > v > 0` (`re_le_of_isForwardSol_of_drift`). Ordinary `SLE_κ`,
`κ > 4`, swallows `x₀` at a finite time (`ae_exists_realSwallowAt`, [RS05] Lemma 6.1), where its flow tends to `0`; the
flow of `x₀` under `W` cannot survive past it.

Since real flows on opposite sides of the driver move apart (`sub_le_re_sub_of_isForwardSol_opp`), the force gap
`W − V` is at least `x₀ − p − u_t(x₀)` before the swallowing time, so it exceeds every level
(`IsIntegratedSLEEvolution.ae_exists_le_gap_oneForce`).

## Main results

* `le_zero_of_hasDerivWithinAt`: a comparison principle on `[0, T]`.
* `re_le_of_isForwardSol_of_drift`, `sub_le_re_sub_of_isForwardSol_opp`: deterministic comparisons of real flows.
* `IsIntegratedSLEEvolution.ae_realSwallowAt_oneForce`: **every positive point is swallowed at a finite time**, `κ > 4`.
* `IsIntegratedSLEEvolution.ae_exists_le_gap_oneForce`: **the force gap is unbounded**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper

/-! ### A comparison principle -/

/-- **Comparison on `[0, T]`.** A function with derivative `D'` within `[0, T]`, `D 0 ≤ 0`, and `D' ≤ 0` wherever
`D > 0`, stays `≤ 0` on `[0, T]`. -/
theorem le_zero_of_hasDerivWithinAt {D D' : ℝ → ℝ} {T : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt D (D' s) (Icc 0 T) s) (h0 : D 0 ≤ 0)
    (hneg : ∀ s ∈ Icc (0 : ℝ) T, 0 < D s → D' s ≤ 0) : ∀ t ∈ Icc (0 : ℝ) T, D t ≤ 0 := by
  have hcont : ContinuousOn D (Icc 0 T) := fun s hs => (hd s hs).continuousWithinAt
  intro t₁ ht₁
  by_contra hpos
  push Not at hpos
  set S : Set ℝ := Icc 0 t₁ ∩ D ⁻¹' Iic 0 with hS
  have hsub : Icc (0 : ℝ) t₁ ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht₁.2
  have hSc : IsClosed S := (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht₁.1⟩, h0⟩
  have hbdd : BddAbove S := ⟨t₁, fun s hs => hs.1.2⟩
  set t₀ := sSup S with ht₀
  have ht₀S : t₀ ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hbdd
  have hlt : t₀ < t₁ := lt_of_le_of_ne ht₀S.1.2 fun h => by
    have := ht₀S.2
    rw [h] at this
    exact absurd this (not_le.2 hpos)
  have hposI : ∀ s ∈ Ioc t₀ t₁, 0 < D s := fun s hs => by
    by_contra hle
    push Not at hle
    have : s ≤ t₀ := le_csSup hbdd ⟨⟨ht₀S.1.1.trans hs.1.le, hs.2⟩, hle⟩
    linarith [hs.1]
  have hsub' : Icc t₀ t₁ ⊆ Icc 0 T := fun s hs => ⟨ht₀S.1.1.trans hs.1, hs.2.trans ht₁.2⟩
  have hanti : AntitoneOn D (Icc t₀ t₁) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁) (f' := D') (hcont.mono hsub')
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact (hd s (hsub' (Ioo_subset_Icc_self hs))).mono (interior_subset.trans hsub')
    · rw [interior_Icc] at hs
      exact hneg s (hsub' (Ioo_subset_Icc_self hs)) (hposI s ⟨hs.1, hs.2.le⟩)
  have := hanti ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt.le
  have h2 : D t₀ ≤ 0 := ht₀S.2
  linarith

/-! ### Deterministic comparisons of real flows -/

section Flows

variable {W W₀ : ℝ → ℝ}

theorem hasDerivWithinAt_re_shift (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun r => (u r + (W r : ℂ)).re) (2 / (u s).re) (Icc 0 T) s := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s (FwdHolo.hasDerivWithinAt_shift hu hs)
  have him := im_isForwardSol_real hW (hs.1.trans hs.2) hu s hs
  rw [← re_two_div_of_im_eq_zero him]
  exact h

/-- **A nonnegative extra drift keeps a positive real flow lower.** If `W − W₀ = ∫₀ g` on `[0, T]` with `g ≥ 0`
continuous, the centred flows of `x > 0` under `W` and `W₀` satisfy `u_t ≤ v_t` on `[0, T]`. -/
theorem re_le_of_isForwardSol_of_drift (hW : Continuous W) (hW₀ : Continuous W₀) (hW0 : W 0 = 0)
    (hW₀0 : W₀ 0 = 0) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ s, 0 ≤ g s) {x T : ℝ}
    (hWW : ∀ t ∈ Icc (0 : ℝ) T, W t - W₀ t = ∫ s in (0 : ℝ)..t, g s) (hx : 0 < x) {u v : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) (hv : IsForwardSol W₀ (x : ℂ) T v) :
    ∀ t ∈ Icc (0 : ℝ) T, (u t).re ≤ (v t).re := by
  intro t ht
  have hT : (0 : ℝ) ≤ T := ht.1.trans ht.2
  set D : ℝ → ℝ := fun r => (u r + (W r : ℂ)).re - (v r + (W₀ r : ℂ)).re - ∫ s in (0 : ℝ)..r, g s with hD
  have hDe : ∀ t ∈ Icc (0 : ℝ) T, D t = (u t).re - (v t).re := fun t ht => by
    simp only [hD, Complex.add_re, Complex.ofReal_re]
    rw [← hWW t ht]
    ring
  have hupos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (u t).re := fun t ht =>
    re_pos_isForwardSol_real hW (ht.1.trans ht.2) hu (by rw [hW0]; exact hx) t ht
  have hvpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (v t).re := fun t ht =>
    re_pos_isForwardSol_real hW₀ (ht.1.trans ht.2) hv (by rw [hW₀0]; exact hx) t ht
  have hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt D (2 / (u s).re - 2 / (v s).re - g s) (Icc 0 T) s :=
    fun s hs => ((hasDerivWithinAt_re_shift hW hu hs).sub (hasDerivWithinAt_re_shift hW₀ hv hs)).sub
      ((hg.integral_hasStrictDerivAt 0 s).hasDerivAt.hasDerivWithinAt)
  have h0 : D 0 ≤ 0 := by
    rw [hDe 0 ⟨le_rfl, hT⟩, FwdHolo.sol_zero hu hT, FwdHolo.sol_zero hv hT]
    simp [hW0, hW₀0]
  have hneg : ∀ s ∈ Icc (0 : ℝ) T, 0 < D s → 2 / (u s).re - 2 / (v s).re - g s ≤ 0 := by
    intro s hs hDs
    rw [hDe s hs] at hDs
    have h1 : 2 / (u s).re ≤ 2 / (v s).re :=
      div_le_div_of_nonneg_left (by norm_num) (hvpos s hs) (by linarith)
    linarith [hg0 s]
  have := le_zero_of_hasDerivWithinAt hd h0 hneg t ht
  rw [hDe t ht] at this
  linarith

/-- **Real flows on opposite sides of the driver move apart.** For `x < 0 < y` alive on `[0, T]`,
`y − x ≤ f_T(y) − f_T(x)` (centred values). -/
theorem sub_le_re_sub_of_isForwardSol_opp (hW : Continuous W) (hW0 : W 0 = 0) {x y T : ℝ} (hT : 0 ≤ T)
    (hx : x < 0) (hy : 0 < y) {u v : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u)
    (hv : IsForwardSol W (y : ℂ) T v) : y - x ≤ (v T).re - (u T).re := by
  set D : ℝ → ℝ := fun r => (v r + (W r : ℂ)).re - (u r + (W r : ℂ)).re with hD
  have hDe : ∀ r, D r = (v r).re - (u r).re := fun r => by simp [hD]
  have hupos : ∀ t ∈ Icc (0 : ℝ) T, (u t).re < 0 := fun t ht => by
    have := re_fwdMap_neg hW hW0 hx hu ht
    rwa [fwdMap_eq_of_isForwardSol hW hu ht] at this
  have hvpos : ∀ t ∈ Icc (0 : ℝ) T, 0 < (v t).re := fun t ht =>
    re_pos_isForwardSol_real hW (ht.1.trans ht.2) hv (by rw [hW0]; exact hy) t ht
  have hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt D (2 / (v s).re - 2 / (u s).re) (Icc 0 T) s :=
    fun s hs => (hasDerivWithinAt_re_shift hW hv hs).sub (hasDerivWithinAt_re_shift hW hu hs)
  have hmono : MonotoneOn D (Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) (f' := fun s => 2 / (v s).re - 2 / (u s).re)
      (fun s hs => (hd s hs).continuousWithinAt) (fun s hs => ?_) (fun s hs => ?_)
    · exact (hd s (interior_subset hs)).mono interior_subset
    · have hs' := interior_subset hs
      have h1 : 0 < 2 / (v s).re := div_pos (by norm_num) (hvpos s hs')
      have h2 : 2 / (u s).re < 0 := div_neg_of_pos_of_neg (by norm_num) (hupos s hs')
      show 0 ≤ 2 / (v s).re - 2 / (u s).re
      linarith
  have h := hmono ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
  rw [hDe, hDe, FwdHolo.sol_zero hu hT, FwdHolo.sol_zero hv hT] at h
  simp only [Complex.ofReal_re, hW0, Complex.ofReal_zero, sub_zero] at h
  linarith

end Flows

/-! ### The one-force law -/

section Prob

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL ρL : Fin 1 → ℝ} {xR ρR : Fin 0 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin 1 → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- A word with one left mark `≤ 0` and no right mark is ordered. -/
theorem isOrderedForceWord_oneLeft (hx : xL 0 ≤ 0) : IsOrderedForceWord xL xR :=
  ⟨fun i j _ => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j], fun i => by
    rw [Fin.fin_one_eq_zero i]; exact hx, fun a => a.elim0, fun i => i.elim0⟩

/-- A word with one left mark of weight `≥ κ/2 − 2` and no right mark has admissible partial sums. -/
theorem hasAdmissiblePartialSums_oneLeft (hρ : κ / 2 - 2 ≤ ρL 0) :
    Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR := by
  refine ⟨fun x _ ⟨i, hi⟩ => ?_, fun x _ ⟨j, _⟩ => j.elim0⟩
  have e : (Finset.univ.filter fun k : Fin 1 => x < xL k) = Finset.univ := by
    refine Finset.filter_true_of_mem fun k _ => ?_
    rw [Fin.fin_one_eq_zero k]; rw [Fin.fin_one_eq_zero i] at hi; exact hi
  rw [e, Fin.sum_univ_one]
  exact hρ

/-- The good event of a separated one-force evolution: infinite lifetime, continuous state, the mark strictly left of
the driver at all times, and the integrated equations of the mark and of the driver. -/
theorem IsIntegratedSLEEvolution.ae_good_oneForce (hκ : 0 < κ) (hx : xL 0 < 0) (hρ : κ / 2 - 2 ≤ ρL 0)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ Continuous (fun t => VL 0 t ω) ∧
      (∀ t, VL 0 t ω < W t ω) ∧
      (∀ t : ℝ≥0, VL 0 t ω = xL 0 + ∫ s in (0 : ℝ)..t, 2 / (VL 0 s.toNNReal ω - W s.toNNReal ω)) ∧
      ∀ t : ℝ≥0, W t ω = Real.sqrt κ * B t ω + ∫ s in (0 : ℝ)..t, ρL 0 / (W s.toNNReal ω - VL 0 s.toNNReal ω) := by
  filter_upwards [Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ (isOrderedForceWord_oneLeft hx.le)
    (hasAdmissiblePartialSums_oneLeft hρ) hE, hE.2.2.2.2] with ω ⟨hζ, hsep⟩ hp
  rw [hζ] at hp
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ⊤} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => ENNReal.coe_lt_top)
  have hsL : ∀ t, VL 0 t ω < W t ω := fun t => by
    rcases eq_zero_or_pos t with rfl | h0
    · have e1 : W 0 ω = 0 := hp.1
      have e2 : VL 0 0 ω = xL 0 := hp.2.1 0
      rw [e1, e2]; exact hx
    · exact (hsep t h0).1 0
  refine ⟨hζ, hcont hp.2.2.2.1, hp.1, hcont (hp.2.2.2.2.1 0), hsL,
    fun t => hp.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top 0, fun t => ?_⟩
  have h := hp.2.2.2.2.2.2.2.2.2.2.2.2.1 t ENNReal.coe_lt_top
  simp only [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h
  exact h

/-- **Every positive point is swallowed at a finite time** (B.2 (E7), `κ > 4`; additional note Lemma 3.2): for a
separated one-force evolution with weight `≥ κ/2 − 2`, almost surely `x₀ > 0` has a swallowing time. -/
theorem IsIntegratedSLEEvolution.ae_realSwallowAt_oneForce (hκ4 : 4 < κ) (hx : xL 0 < 0)
    (hρ : κ / 2 - 2 ≤ ρL 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {x₀ : ℝ}
    (hx₀ : 0 < x₀) : ∀ᵐ ω ∂P, ∃ σ, RealSwallowAt (fun r : ℝ => W r.toNNReal ω) x₀ σ := by
  have hκ : 0 < κ := by linarith
  have hρ0 : 0 ≤ ρL 0 := by linarith
  obtain ⟨B', hBm, hBc, hB0, hBM, hae⟩ := exists_continuous_version_zero hE.1
  filter_upwards [ae_exists_realSwallowAt hBM.1 hBm hBc hB0 hκ4 hx₀, hae,
    IsIntegratedSLEEvolution.ae_good_oneForce hκ hx hρ hE] with ω ⟨σ, hσ⟩ hBB ⟨_, hwc, hw0, hvc, hsep, _, hweq⟩
  set Wr : ℝ → ℝ := fun r => W r.toNNReal ω with hWr
  have hWrc : Continuous Wr := hwc.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simp [hWr, hw0]
  have hW₀c : Continuous (drive κ B' ω) := drive_continuous (hBc ω)
  have hW₀0 : drive κ B' ω 0 = 0 := by simp [drive, hB0 ω]
  set g : ℝ → ℝ := fun r => ρL 0 / (W r.toNNReal ω - VL 0 r.toNNReal ω) with hg
  have hgc : Continuous g := continuous_const.div ((hwc.sub hvc).comp continuous_real_toNNReal)
    fun r => (sub_pos.2 (hsep _)).ne'
  have hg0 : ∀ r, 0 ≤ g r := fun r => div_nonneg hρ0 (sub_pos.2 (hsep _)).le
  have hWW : ∀ T : ℝ, ∀ t ∈ Icc (0 : ℝ) T, Wr t - drive κ B' ω t = ∫ s in (0 : ℝ)..t, g s := by
    intro T t ht
    have h := hweq t.toNNReal
    rw [Real.coe_toNNReal _ ht.1] at h
    simp only [hWr, drive, hBB t.toNNReal]
    rw [h]
    ring
  by_contra hno
  have hdead : ¬ ∃ u, IsForwardSol Wr (x₀ : ℂ) σ u := by
    rintro ⟨u, hu⟩
    have hle : ∀ s ∈ Ico (0 : ℝ) σ, (u s).re ≤ (fwdMap (drive κ B' ω) s x₀).re := by
      intro s hs
      obtain ⟨v, hv⟩ := hσ.2.1 s hs
      have h := re_le_of_isForwardSol_of_drift hWrc hW₀c hWr0 hW₀0 hgc hg0 (hWW s) hx₀
        (isForwardSol_restrict hu hs.1 hs.2.le) hv s ⟨hs.1, le_rfl⟩
      rwa [fwdMap_eq_of_isForwardSol hW₀c hv ⟨hs.1, le_rfl⟩]
    have hσ0 := hσ.1
    have hne : (𝓝[Ico (0 : ℝ) σ] σ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hσ0.ne]
      exact ⟨hσ0.le, le_rfl⟩
    have h1 : Tendsto (fun s => (fwdMap (drive κ B' ω) s x₀).re) (𝓝[Ico (0 : ℝ) σ] σ) (𝓝 0) := by
      have h := ((Complex.continuous_re.tendsto 0).comp
        (tendsto_fwdMap_of_realSwallowAt hW₀c hW₀0 hx₀ hσ)).mono_left
          (nhdsWithin_mono σ (fun r (hr : r ∈ Ico (0 : ℝ) σ) => (hr.2 : r < σ)))
      rw [Complex.zero_re] at h
      exact h
    have h2 : Tendsto (fun s => (u s).re) (𝓝[Ico (0 : ℝ) σ] σ) (𝓝 (u σ).re) :=
      ((Complex.continuous_re.tendsto _).comp ((hu.1 σ ⟨hσ0.le, le_rfl⟩).tendsto)).mono_left
        (nhdsWithin_mono _ Ico_subset_Icc_self)
    have h3 := le_of_tendsto_of_tendsto h2 h1 (eventually_nhdsWithin_of_forall hle)
    have h4 := re_pos_isForwardSol_real hWrc hσ0.le hu (by rw [hWr0]; exact hx₀) σ ⟨hσ0.le, le_rfl⟩
    linarith
  obtain ⟨σ', -, hσ'⟩ := exists_realSwallowAt hWrc hWr0 hx₀ hσ.1.le hdead
  exact hno ⟨σ', hσ'⟩

/-- **The force gap is unbounded** (`κ > 4`): almost surely `W − V` exceeds every level at some time. -/
theorem IsIntegratedSLEEvolution.ae_exists_le_gap_oneForce (hκ4 : 4 < κ) (hx : xL 0 < 0)
    (hρ : κ / 2 - 2 ≤ ρL 0) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ L : ℝ, ∃ t : ℝ≥0, L ≤ W t ω - VL 0 t ω := by
  have hκ : 0 < κ := by linarith
  filter_upwards [ae_all_iff.2 fun n : ℕ => IsIntegratedSLEEvolution.ae_realSwallowAt_oneForce hκ4 hx hρ hE
    (x₀ := (n : ℝ) + 1) (by positivity), IsIntegratedSLEEvolution.ae_good_oneForce hκ hx hρ hE]
    with ω hsw ⟨_, hwc, hw0, hvc, hsep, hveq, _⟩ L
  set Wr : ℝ → ℝ := fun r => W r.toNNReal ω with hWr
  have hWrc : Continuous Wr := hwc.comp continuous_real_toNNReal
  have hWr0 : Wr 0 = 0 := by simp [hWr, hw0]
  obtain ⟨n, hn⟩ := exists_nat_ge (2 * L)
  set x₀ : ℝ := (n : ℝ) + 1 with hx₀
  have hx₀0 : 0 < x₀ := by positivity
  obtain ⟨σ, hσ⟩ := hsw n
  have : (𝓝[<] σ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hσ.1⟩
  have htend := (Complex.continuous_re.tendsto 0).comp (tendsto_fwdMap_of_realSwallowAt hWrc hWr0 hx₀0 hσ)
  have hev : ∀ᶠ s in 𝓝[<] σ, (fwdMap Wr s x₀).re < x₀ / 2 ∧ s ∈ Ioo 0 σ :=
    (htend.eventually (gt_mem_nhds (show (0 : ℂ).re < x₀ / 2 by rw [Complex.zero_re]; positivity))).and
      (Ioo_mem_nhdsLT hσ.1)
  obtain ⟨s, hs1, hs2⟩ := hev.exists
  obtain ⟨v, hv⟩ := hσ.2.1 s ⟨hs2.1.le, hs2.2⟩
  have huL := isForwardSol_of_force hwc hvc (fun t => (hsep t).ne) hveq s
  have hexp := sub_le_re_sub_of_isForwardSol_opp hWrc hWr0 hs2.1.le hx hx₀0 huL hv
  rw [fwdMap_eq_of_isForwardSol hWrc hv ⟨hs2.1.le, le_rfl⟩] at hs1
  have e : ((fun r : ℝ => ((VL 0 r.toNNReal ω - W r.toNNReal ω : ℝ) : ℂ)) s).re =
      VL 0 s.toNNReal ω - W s.toNNReal ω := by simp
  rw [e] at hexp
  refine ⟨s.toNNReal, ?_⟩
  have h2 : 2 * L ≤ x₀ := by rw [hx₀]; linarith
  linarith

end Prob

end InteractingSLE.ZhanGT4
