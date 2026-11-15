/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.FiniteExceptionDisk
import InteractingSLE.Spec.Sec6.ConformalGrowth
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo
import InteractingSLE.Foundations.PrimeEnd.Jordan

/-!
# Aux. lemma 28: uniqueness with finitely many exceptional prime ends

Packet PROVE-SEC6-A (specification §6.1, `source/spec/p145-192.md`, `#aux-28`, p. 162).

**Aux. lemma 28.** Let `C` be a bounded Jordan domain, let `f : 𝔻 → C` be conformal, and let `H`
be harmonic in `C`. Suppose that, for every `ε > 0`, `|H(z)| ≤ C_ε (1 + dist(z, ∂C)^{−ε})`. Let
`φ : C → ℍ` be conformal, let `g` be a bounded harmonic function in `ℍ`, and fix a real `χ` and a
continuous branch of `arg φ'` in `C`. Put `F_C = g ∘ φ − χ arg φ'`. If `H − F_C` tends to zero
continuously at every boundary point of `C` except a finite set, then `H = F_C` in `C`. The same
conclusion holds when `C` is merely simply connected, provided the boundary condition is
interpreted in the disk and the exceptional set consists of finitely many prime ends.

## Lean statements

* `InteractingSLE.Sec6.aux28_eqOn_of_tendsto_disk`: the simply connected form. The boundary
  condition is read in the disk through `f` (prime ends of `C` are the points of the unit circle
  under `f`); the exceptional set is a finite set of points of the circle.
* `InteractingSLE.Sec6.aux28_eqOn_of_tendsto_jordan`: the bounded Jordan form, with the boundary
  condition at the physical boundary points of `C`. The conformal map `f` of the source is not a
  hypothesis: the closed-disk Carathéodory–Schoenflies map
  (`InteractingSLE.Foundations.Schoenflies.schoenflies_disc`) is used instead.

Carriers: a conformal map is `SupercriticalConformalCovariance.IsConformalBijection` (holomorphic
and bijective); `ℍ = {w | 0 < Im w}`; "a continuous branch of `arg φ'`" is a function `A`
continuous on `C` with `φ'(z) = |φ'(z)| e^{i A(z)}`.

## Proof (as in the source)

`u = (H − F_C) ∘ f` is harmonic on the disk. Koebe and distortion give
`dist(f(ζ), ∂C) ≥ c (1 − |ζ|)^{1 + C₂}`, so `H ∘ f = O((1 − |ζ|)^{−1/4})` (choosing
`ε = 1/(4(1 + C₂))`); `g ∘ φ ∘ f` is bounded; and `arg φ' ∘ f = Im(log (φ ∘ f)') − Im(log f')`
grows logarithmically (`norm_derivLog_sub_le`). Hence `|u| ≤ C' (1 − |ζ|)^{−1/4}`, and the disk
step `eqOn_zero_of_growth` gives `u = 0`.
-/

noncomputable section

open Complex Metric Set Filter Topology
open scoped Real

namespace InteractingSLE.Sec6

open QuantumZipper.CA.Koebe SupercriticalConformalCovariance

/-- A continuous branch `A` of `arg φ'` gives a holomorphic logarithm `log |φ'| + i A` of `φ'`. -/
theorem isDerivLog_of_arg_branch {φ : ℂ → ℂ} {C : Set ℂ} (hCo : IsOpen C)
    (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im}) {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) :
    IsDerivLog φ (fun z => (Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I) C := by
  have hne : ∀ z ∈ C, deriv φ z ≠ 0 := fun z hz =>
    QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn hCo hφ.1 hφ.2.injOn hz
  have hexp : ∀ z ∈ C, exp ((Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I) = deriv φ z := by
    intro z hz
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.2 (hne z hz)),
      ← hA z hz]
  have hd : DifferentiableOn ℂ (deriv φ) C := hφ.1.deriv hCo
  have hcont : ContinuousOn (fun z => (Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I) C := by
    refine ContinuousOn.add ?_ ((Complex.continuous_ofReal.comp_continuousOn hAc).mul
      continuousOn_const)
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact (hd.continuousOn.norm).log fun z hz => (norm_pos_iff.2 (hne z hz)).ne'
  exact ⟨differentiableOn_of_continuousOn_of_exp_eq hCo hcont hd hexp, hexp⟩

/-- For an open `C ≠ ℂ` and `z ∈ C`, `dist(z, Cᶜ) ≤ dist(z, ∂C)`. -/
theorem infDist_compl_le_infDist_frontier {C : Set ℂ} (hCo : IsOpen C) (hne : C.Nonempty)
    (hC : C ≠ univ) (z : ℂ) : infDist z Cᶜ ≤ infDist z (frontier C) := by
  have hfr : (frontier C).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
    rcases h with h | h
    · exact hne.ne_empty h
    · exact hC h
  refine infDist_le_infDist_of_subset ?_ hfr
  intro x hx
  rw [hCo.frontier_eq] at hx
  exact hx.2

/-- **Aux. lemma 28**, simply connected form: the boundary condition is interpreted in the disk,
and the exceptional set is a finite set of points of the unit circle (finitely many prime ends). -/
theorem aux28_eqOn_of_tendsto_disk {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {Hh : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd Hh C)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ C,
      |Hh z| ≤ Cε * (1 + infDist z (frontier C) ^ (-ε)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im})
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g {w : ℂ | 0 < w.im})
    (hgb : ∃ M, ∀ w : ℂ, 0 < w.im → |g w| ≤ M) (χ : ℝ) {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) {E : Set ℂ} (hEfin : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ C, Hh z = g (φ z) - χ * A z := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hfim : f '' ball 0 1 = C := hfb.image_eq
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- the derivative lifts
  have hL := isDerivLog_of_arg_branch hCo hφ hAc hA
  set L := fun z => (Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I
  obtain ⟨ℓf, hℓf⟩ := exists_isDerivLog isOpen_ball isSimplyConnected_unitBall hfd
    (fun ζ hζ => QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hζ)
  have hLm := IsDerivLog.comp isOpen_ball hCo hφ.1 hfd hfb.mapsTo hL hℓf
  have hmd : DifferentiableOn ℂ (φ ∘ f) (ball 0 1) := hφ.1.comp hfd hfb.mapsTo
  have hminj : InjOn (φ ∘ f) (ball 0 1) := hφ.2.injOn.comp hfinj hfb.mapsTo
  -- `A ∘ f = Im (L_m − ℓ_f)`
  have hAf : ∀ ζ ∈ ball (0 : ℂ) 1, A (f ζ) = (L (f ζ) + ℓf ζ - ℓf ζ).im := by
    intro ζ _
    simp [L]
  -- growth of `A ∘ f`
  set K₀ := ‖(L (f 0) + ℓf 0) - ℓf 0‖
  have hAgrowth : ∀ ζ ∈ ball (0 : ℂ) 1,
      |A (f ζ)| ≤ K₀ + 2 * koebeDistExp * (-Real.log (1 - ‖ζ‖)) := by
    intro ζ hζ
    have h1 := norm_derivLog_sub_le hmd hminj hLm hζ
    have h2 := norm_derivLog_sub_le hfd hfinj hℓf hζ
    rw [hAf ζ hζ]
    refine (Complex.abs_im_le_norm _).trans ?_
    calc ‖L (f ζ) + ℓf ζ - ℓf ζ‖
        = ‖((L (f ζ) + ℓf ζ) - (L (f 0) + ℓf 0)) - (ℓf ζ - ℓf 0) +
            ((L (f 0) + ℓf 0) - ℓf 0)‖ := by ring_nf
      _ ≤ ‖(L (f ζ) + ℓf ζ) - (L (f 0) + ℓf 0)‖ + ‖ℓf ζ - ℓf 0‖ + K₀ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by simp only [L] at h1 ⊢; linarith
  -- Koebe: distance to the boundary
  have hCne : C.Nonempty := ⟨f 0, hfb.mapsTo hball0⟩
  have hCuniv : C ≠ univ := hfim ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hfd hfinj
  set κ := koebeCovConst * ‖deriv f 0‖
  have hκ : 0 < κ := mul_pos koebeCovConst_pos
    (norm_pos_iff.2 (QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hball0))
  have hdist : ∀ ζ ∈ ball (0 : ℂ) 1,
      κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) ≤ infDist (f ζ) (frontier C) := by
    intro ζ hζ
    have := koebe_mul_pow_le_infDist hfd hfinj hζ
    rw [hfim] at this
    exact this.trans (infDist_compl_le_infDist_frontier hCo hCne hCuniv _)
  -- the subpower bound for `H ∘ f`
  set ε₀ : ℝ := 1 / (4 * (1 + koebeDistExp))
  have hε₀ : 0 < ε₀ := by have := koebeDistExp_pos; positivity
  obtain ⟨Cε, hCε⟩ := hgrowth ε₀ hε₀
  have hHgrowth : ∀ ζ ∈ ball (0 : ℂ) 1,
      |Hh (f ζ)| ≤ |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
    intro ζ hζ
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hpow0 : 0 < κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) := by positivity
    have hd := hdist ζ hζ
    have h1 : infDist (f ζ) (frontier C) ^ (-ε₀) ≤ (κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)) ^ (-ε₀) :=
      Real.rpow_le_rpow_of_nonpos hpow0 hd (by linarith)
    have h2 : (κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)) ^ (-ε₀) =
        κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_mul hr.le]
      congr 2
      simp only [ε₀]
      have := koebeDistExp_pos
      field_simp
    have h3 : 1 ≤ (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have hfz : f ζ ∈ C := hfb.mapsTo hζ
    have h4 := hCε (f ζ) hfz
    have hκp : 0 ≤ κ ^ (-ε₀) := by positivity
    calc |Hh (f ζ)| ≤ Cε * (1 + infDist (f ζ) (frontier C) ^ (-ε₀)) := h4
      _ ≤ |Cε| * (1 + infDist (f ζ) (frontier C) ^ (-ε₀)) := by
          have : 0 ≤ 1 + infDist (f ζ) (frontier C) ^ (-ε₀) := by
            have := Real.rpow_nonneg (infDist_nonneg (x := f ζ) (s := frontier C)) (-ε₀)
            linarith
          exact mul_le_mul_of_nonneg_right (le_abs_self _) this
      _ ≤ |Cε| * (1 + κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr; rw [← h2]; exact h1
      _ ≤ |Cε| * ((1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) + κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr
      _ = |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by ring
  -- the total bound
  obtain ⟨M, hM⟩ := hgb
  set u : ℂ → ℝ := fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))
  set C' := |Cε| * (1 + κ ^ (-ε₀)) + |M| + |χ| * (K₀ + 8 * koebeDistExp)
  have hugrowth : ∀ ζ ∈ ball (0 : ℂ) 1, |u ζ| ≤ C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
    intro ζ hζ
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hP : 1 ≤ (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have hlog := neg_log_le_four_mul_rpow hr
    have hgz : |g (φ (f ζ))| ≤ M := hM _ (hφ.2.mapsTo (hfb.mapsTo hζ))
    have hAz := hAgrowth ζ hζ
    have hH := hHgrowth ζ hζ
    have hK₀ : 0 ≤ K₀ := norm_nonneg _
    have hC2 := koebeDistExp_pos
    have hA' : |A (f ζ)| ≤ (K₀ + 8 * koebeDistExp) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
      calc |A (f ζ)| ≤ K₀ + 2 * koebeDistExp * (-Real.log (1 - ‖ζ‖)) := hAz
        _ ≤ K₀ * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) +
            2 * koebeDistExp * (4 * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
            gcongr
            · nlinarith
        _ = _ := by ring
    simp only [u]
    calc |Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))|
        ≤ |Hh (f ζ)| + (|g (φ (f ζ))| + |χ| * |A (f ζ)|) := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) +
          (|M| * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) +
            |χ| * ((K₀ + 8 * koebeDistExp) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)))) := by
          gcongr
          · exact hgz.trans ((le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg _) hP))
      _ = C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by simp only [C']; ring
  -- harmonicity of `u`
  have hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1) := by
    intro ζ hζ
    have hfa : AnalyticAt ℂ f ζ := hfd.analyticAt (isOpen_ball.mem_nhds hζ)
    have hfz : f ζ ∈ C := hfb.mapsTo hζ
    have hφa : AnalyticAt ℂ φ (f ζ) := hφ.1.analyticAt (hCo.mem_nhds hfz)
    have h1 : InnerProductSpace.HarmonicAt (Hh ∘ f) ζ :=
      QuantumZipper.FieldLawler.fl_harmonicAt_comp hfa (hH _ hfz)
    have h2 : InnerProductSpace.HarmonicAt (g ∘ (φ ∘ f)) ζ :=
      QuantumZipper.FieldLawler.fl_harmonicAt_comp (hφa.comp hfa) (hg _ (hφ.2.mapsTo hfz))
    have h3 : InnerProductSpace.HarmonicAt (fun ζ => (L (f ζ) + ℓf ζ - ℓf ζ).im) ζ := by
      have : AnalyticAt ℂ (fun ζ => L (f ζ) + ℓf ζ - ℓf ζ) ζ :=
        (hLm.1.sub hℓf.1).analyticAt (isOpen_ball.mem_nhds hζ)
      exact this.harmonicAt_im
    have h3' : InnerProductSpace.HarmonicAt (fun ζ => χ * A (f ζ)) ζ := by
      have h := h3.const_smul (c := χ)
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h
      filter_upwards [isOpen_ball.mem_nhds hζ] with w hw
      simp only [Pi.smul_apply, smul_eq_mul, hAf w hw]
    exact h1.sub (h2.sub h3')
  -- conclusion
  set E' : Finset ℂ := hEfin.toFinset.filter (fun p => ‖p‖ = 1)
  have hE' : ∀ p ∈ E', ‖p‖ = 1 := fun p hp => (Finset.mem_filter.1 hp).2
  have hbd' : ∀ q : ℂ, ‖q‖ = 1 → q ∉ E' → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0) := by
    intro q hq hqE
    refine hbd q (mem_sphere_zero_iff_norm.2 hq) fun hqE' => hqE ?_
    exact Finset.mem_filter.2 ⟨hEfin.mem_toFinset.2 hqE', hq⟩
  have hzero := eqOn_zero_of_growth hu hE' (by norm_num) (by norm_num) hugrowth hbd'
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hfb.surjOn hz
  have := hzero ζ hζ
  simp only [u] at this
  linarith

/-- **Aux. lemma 28**, bounded Jordan form. Let `C` be a bounded Jordan domain (open, connected,
bounded, with Jordan-curve frontier), `H` harmonic in `C` with
`|H(z)| ≤ C_ε (1 + dist(z, ∂C)^{−ε})` for every `ε > 0`, `φ : C → ℍ` conformal, `g` bounded
harmonic in `ℍ`, `χ` real and `A` a continuous branch of `arg φ'` on `C`. If
`H − (g ∘ φ − χ A)` tends to zero at every boundary point of `C` outside a finite set `P`, then
`H = g ∘ φ − χ A` on `C`. (The source's conformal map `f : 𝔻 → C` is not needed as a hypothesis.) -/
theorem aux28_eqOn_of_tendsto_jordan {C : Set ℂ} (hCo : IsOpen C) (hCc : IsConnected C)
    (hCb : Bornology.IsBounded C) (hJ : LQGMetric.JordanMap.IsJordanCurve (frontier C))
    {Hh : ℂ → ℝ} (hH : InnerProductSpace.HarmonicOnNhd Hh C)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ C,
      |Hh z| ≤ Cε * (1 + infDist z (frontier C) ^ (-ε)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im})
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g {w : ℂ | 0 < w.im})
    (hgb : ∃ M, ∀ w : ℂ, 0 < w.im → |g w| ≤ M) (χ : ℝ) {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) {P : Set ℂ} (hPfin : P.Finite)
    (hbd : ∀ x ∈ frontier C, x ∉ P →
      Tendsto (fun z => Hh z - (g (φ z) - χ * A z)) (𝓝[C] x) (𝓝 0)) :
    ∀ z ∈ C, Hh z = g (φ z) - χ * A z := by
  obtain ⟨p₀, hp₀⟩ := hCc.nonempty
  have hDeq := connectedComponentIn_compl_frontier_eq hCo hCc hp₀
  have hp₀Γ : p₀ ∈ (frontier C)ᶜ := by
    rw [← hDeq] at hp₀; exact connectedComponentIn_subset _ _ hp₀
  obtain ⟨f, hfc, hfi, hfd, -, hfball, hfsph⟩ :=
    Foundations.Schoenflies.schoenflies_disc hJ hp₀Γ (by rw [hDeq]; exact hCb)
  rw [hDeq] at hfball
  have hfi' : InjOn f (ball 0 1) := hfi.mono ball_subset_closedBall
  have hf : IsConformalBijection f (ball 0 1) C := ⟨hfd, hfball ▸ hfi'.bijOn_image⟩
  set E : Set ℂ := sphere (0 : ℂ) 1 ∩ f ⁻¹' P
  have hEfin : E.Finite := by
    refine Set.Finite.of_finite_image (hPfin.subset ?_) (hfi.mono fun z hz =>
      sphere_subset_closedBall hz.1)
    rintro _ ⟨z, hz, rfl⟩; exact hz.2
  refine aux28_eqOn_of_tendsto_disk hCo hf hH hgrowth hφ hg hgb χ hAc hA hEfin ?_
  intro q hq hqE
  have hfq : f q ∈ frontier C := hfsph ▸ mem_image_of_mem f hq
  have hfqP : f q ∉ P := fun h => hqE ⟨hq, h⟩
  have hlim : Tendsto f (𝓝[ball 0 1] q) (𝓝[C] (f q)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((hfc q (sphere_subset_closedBall hq)).mono ball_subset_closedBall).tendsto
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact hfball ▸ mem_image_of_mem f hζ
  exact (hbd (f q) hfq hfqP).comp hlim

end InteractingSLE.Sec6
