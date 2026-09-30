import QuantumZipper.Proofs.Thm18.G1HolderRed
import Mathlib.Analysis.Complex.Liouville

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-HOLDER: Hölder continuity of a factored conformal map (deterministic)

Steps 3–5 of `handoff/G1-HOLDER.md`. If on each bounded part of `ℍ` the map `ψ` factors as
`ψ = f ∘ F`, with `f` `α`-Hölder on bounded parts of `ℍ` and `F : ℍ → ℍ` conformal, bounded,
and with `Im F(z) ≤ K Im z` (boundary Lipschitz bound), then `ψ` is `α`-Hölder on bounded parts
of `Hbar` (`locHolderHbar_of_factor`).

Ingredients: the Cauchy estimate (mathlib `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`)
turns the Hölder bound of `f` into `‖f'(u)‖ ≤ C (min(Im u, 1)/2)^{α-1}`; the Koebe 1/4 theorem
(`CA.Koebe.infDist_compl_image_ge`, Garnett–Marshall, *Harmonic Measure*, Cor. I.4.4) gives
`c₁ Im z ‖F'(z)‖ ≤ Im F(z) ≤ K Im z`; the chain rule then gives
`‖ψ'(z)‖ ≤ C' (min 1 (Im z))^{α-1}`, and the Hardy–Littlewood integration
(`RS.hardyLittlewood_holder`; Pommerenke, *Boundary Behaviour of Conformal Maps*, §4.6 (7)) the
Hölder bound on `ℍ`, extended to `Hbar` by continuity. This combination is the standard proof of
RS Thm 5.2's last step (Rohde–Schramm, Ann. Math. 161 (2005), p. 22); its use for the factored
side map is an own argument (see the handoff).
-/

noncomputable section

open Filter Set Function Metric Topology Complex

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-- Cauchy estimate: a map `α`-Hölder on `ℍ ∩ closedBall 0 ρ` has
`‖f'(u)‖ ≤ C (min (Im u) 1 / 2)^{α-1}` when `‖u‖ + 1 ≤ ρ`. -/
theorem norm_deriv_le_of_holder {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f H) {α C ρ : ℝ}
    (hC : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖f z - f w‖ ≤ C * ‖z - w‖ ^ α)
    {u : ℂ} (hu : u ∈ H) (huρ : ‖u‖ + 1 ≤ ρ) :
    ‖deriv f u‖ ≤ C * (min u.im 1 / 2) ^ (α - 1) := by
  have hy : 0 < u.im := hu
  set r := min u.im 1 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrim : r < u.im := by
    have : min u.im 1 ≤ u.im := min_le_left _ _
    linarith
  have hr1 : r ≤ 1 / 2 := by
    have : min u.im 1 ≤ 1 := min_le_right _ _
    linarith
  have hsub : closedBall u r ⊆ H := by
    intro z hz
    rw [mem_closedBall, Complex.dist_eq] at hz
    have h1 : |(z - u).im| ≤ ‖z - u‖ := Complex.abs_im_le_norm _
    have h2 : (z - u).im = z.im - u.im := Complex.sub_im _ _
    show 0 < z.im
    have := neg_abs_le (z - u).im
    linarith
  have hnorm : ∀ z ∈ closedBall u r, ‖z‖ ≤ ρ := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - u) + u‖ := by ring_nf
      _ ≤ ‖z - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  have hd : DiffContOnCl ℂ (fun z => f z - f u) (ball u r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball u hr0.ne']
    exact (hf.mono hsub).sub_const _
  have hsph : ∀ z ∈ sphere u r, ‖f z - f u‖ ≤ C * r ^ α := by
    intro z hz
    have hz' : z ∈ closedBall u r := sphere_subset_closedBall hz
    have h := hC z (hsub hz') u (hsub (mem_closedBall_self hr0.le)) (hnorm z hz')
      (hnorm u (mem_closedBall_self hr0.le))
    rw [mem_sphere, dist_eq_norm] at hz
    rwa [hz] at h
  have hK := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr0 hd hsph
  have hder : deriv (fun z => f z - f u) u = deriv f u := by
    rw [deriv_sub_const]
  rw [hder] at hK
  calc ‖deriv f u‖ ≤ C * r ^ α / r := hK
    _ = C * r ^ (α - 1) := by rw [Real.rpow_sub_one hr0.ne', mul_div_assoc]

/-- Koebe: for `F : ℍ → ℍ` conformal, `c₁ Im z ‖F'(z)‖ ≤ Im F(z)`. -/
theorem koebe_mul_le_im {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) (hinj : InjOn F H)
    (hmaps : MapsTo F H H) {z : ℂ} (hz : z ∈ H) :
    CA.Koebe.koebeCovConst * z.im * ‖deriv F z‖ ≤ (F z).im := by
  have h := CA.Koebe.infDist_compl_image_ge (f := F) hd hinj (z := z) hz
  refine h.trans ?_
  have hmem : ((F z).re : ℂ) ∈ (F '' {z : ℂ | 0 < z.im})ᶜ := by
    rintro ⟨w, hw, hwe⟩
    have := hmaps hw
    rw [hwe] at this
    simp [H] at this
  refine (infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
  rw [Complex.dist_eq]
  have : F z - ((F z).re : ℂ) = ((F z).im : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hmaps hz)]

/-- Hölder bounds on `ℍ ∩ closedBall 0 (R+1)` pass to `Hbar ∩ closedBall 0 R` for a map
continuous on `Hbar`. -/
theorem holder_Hbar_of_holder_H {ψ : ℂ → ℂ} (hc : ContinuousOn ψ Hbar) {α C R : ℝ}
    (h : ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ R + 1 → ‖w‖ ≤ R + 1 → ‖ψ z - ψ w‖ ≤ C * ‖z - w‖ ^ α) :
    ∀ z ∈ Hbar, ∀ w ∈ Hbar, ‖z‖ ≤ R → ‖w‖ ≤ R → ‖ψ z - ψ w‖ ≤ C * ‖z - w‖ ^ α := by
  intro z hz w hw hzR hwR
  have hlim : ∀ p ∈ Hbar, Tendsto (fun ε : ℝ => ψ (p + ε * I)) (𝓝[>] 0) (𝓝 (ψ p)) := by
    intro p hp
    have ht : Tendsto (fun ε : ℝ => p + ε * I) (𝓝[>] 0) (𝓝[Hbar] p) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun ε hε => ?_⟩
      · have : Continuous fun ε : ℝ => p + ε * I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · show 0 ≤ (p + ε * I).im
        simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one,
          add_zero]
        have : (0 : ℝ) ≤ p.im := hp
        have : (0 : ℝ) < ε := hε
        linarith
    exact (hc p hp).tendsto.comp ht
  have hlimn : Tendsto (fun ε : ℝ => ‖ψ (z + ε * I) - ψ (w + ε * I)‖) (𝓝[>] 0)
      (𝓝 ‖ψ z - ψ w‖) := ((hlim z hz).sub (hlim w hw)).norm
  refine le_of_tendsto hlimn ?_
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε1 hε0
  have hε0' : (0 : ℝ) < ε := hε0
  have hmemH : ∀ p ∈ Hbar, p + ε * I ∈ H := by
    intro p hp
    show 0 < (p + ε * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, mul_one, add_zero]
    have : (0 : ℝ) ≤ p.im := hp
    linarith
  have hnorm : ∀ p : ℂ, ‖p‖ ≤ R → ‖p + ε * I‖ ≤ R + 1 := by
    intro p hp
    calc ‖p + ε * I‖ ≤ ‖p‖ + ‖(ε : ℂ) * I‖ := norm_add_le _ _
      _ = ‖p‖ + ε := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hε0']
      _ ≤ R + 1 := by linarith
  have h1 := h _ (hmemH z hz) _ (hmemH w hw) (hnorm z hzR) (hnorm w hwR)
  have hsub : z + ε * I - (w + ε * I) = z - w := by ring
  rwa [hsub] at h1

/-- **Hölder continuity of a factored map.** If for every `R` the map `ψe` factors on `ℍ` as
`f ∘ F`, with `f` holomorphic and `α`-Hölder on bounded parts of `ℍ`, and `F : ℍ → ℍ` conformal,
bounded on `ℍ ∩ closedBall 0 R` and with `Im F(z) ≤ K Im z` there, then `ψe` (continuous on
`Hbar`) is `LocHolderHbar` with exponent `α`. -/
theorem locHolderHbar_of_factor {ψe : ℂ → ℂ} (hc : ContinuousOn ψe Hbar) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1)
    (h : ∀ R : ℝ, ∃ f F : ℂ → ℂ, DifferentiableOn ℂ f H ∧
      (∀ ρ : ℝ, ∃ C : ℝ, ∀ z ∈ H, ∀ w ∈ H, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ →
        ‖f z - f w‖ ≤ C * ‖z - w‖ ^ α) ∧
      DifferentiableOn ℂ F H ∧ InjOn F H ∧ MapsTo F H H ∧ (∀ z ∈ H, ψe z = f (F z)) ∧
      (∃ M : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → ‖F z‖ ≤ M) ∧
      (∃ K : ℝ, ∀ z ∈ H, ‖z‖ ≤ R → (F z).im ≤ K * z.im)) :
    LocHolderHbar ψe := by
  refine ⟨α, hα, fun R => ?_⟩
  set R0 := max R 0 with hR0
  obtain ⟨f, F, hfd, hfh, hFd, hFi, hFm, hfac, ⟨M, hM⟩, ⟨K, hK⟩⟩ := h (R0 + 3)
  obtain ⟨C, hC⟩ := hfh (max M 0 + 1)
  set c := CA.Koebe.koebeCovConst with hcdef
  have hc0 : 0 < c := CA.Koebe.koebeCovConst_pos
  have hψd : ∀ z ∈ H, HasDerivAt ψe (deriv f (F z) * deriv F z) z := by
    intro z hz
    have hFz : HasDerivAt F (deriv F z) z :=
      (hFd.differentiableAt (isOpen_H.mem_nhds hz)).hasDerivAt
    have hfz : HasDerivAt f (deriv f (F z)) (F z) :=
      (hfd.differentiableAt (isOpen_H.mem_nhds (hFm hz))).hasDerivAt
    refine (hfz.comp z hFz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_H.mem_nhds hz] with w hw
    exact hfac w hw
  have hψdiff : DifferentiableOn ℂ ψe H := fun z hz =>
    (hψd z hz).differentiableAt.differentiableWithinAt
  set C' := max C 0 with hC'def
  set K' := max K 0 with hK'def
  set D2 : ℝ := (1 / 2 : ℝ) ^ (α - 1) with hD2
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hD20 : 0 ≤ D2 := Real.rpow_nonneg (by norm_num) _
  set Cst := C' * D2 * (K' ^ α / c + K' / c) with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  have hbd : ∀ p ∈ H, ‖p‖ ≤ (R0 + 1) + 2 → ‖deriv ψe p‖ ≤ Cst * (min 1 p.im) ^ (α - 1) := by
    intro p hp hpR
    have hy : 0 < p.im := hp
    set y := p.im with hydef
    set u := F p with hudef
    have huH : 0 < u.im := hFm hp
    have hpR' : ‖p‖ ≤ R0 + 3 := by linarith
    have hu1 : ‖u‖ + 1 ≤ max M 0 + 1 := by linarith [hM p hp hpR', le_max_left M 0]
    have hfu := norm_deriv_le_of_holder hfd hC (hFm hp) hu1
    set a := ‖deriv F p‖ with hadef
    have ha0 : 0 ≤ a := norm_nonneg _
    have hkoe : c * y * a ≤ u.im := koebe_mul_le_im hFd hFi hFm hp
    have hKu : u.im ≤ K' * y := (hK p hp hpR').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le)
    have hderiv : deriv ψe p = deriv f u * deriv F p := (hψd p hp).deriv
    rw [hderiv, norm_mul, ← hadef]
    have hmin1 : 1 ≤ (min 1 y) ^ (α - 1) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (lt_min one_pos hy) (min_le_left _ _)
        (by linarith)
    have hminy : y ^ (α - 1) ≤ (min 1 y) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos (lt_min one_pos hy) (min_le_right _ _) (by linarith)
    rcases eq_or_lt_of_le ha0 with ha | ha
    · rw [← ha, mul_zero]
      exact mul_nonneg hCst0 (Real.rpow_nonneg (le_min zero_le_one hy.le) _)
    set s := c * y * a with hsdef
    have hs0 : 0 < s := by positivity
    have haA : a ≤ K' / c := by
      rw [le_div_iff₀ hc0]
      have : c * y * a ≤ K' * y := hkoe.trans hKu
      nlinarith
    -- `f'` bound transported to `s`
    have hmono : (min u.im 1 / 2) ^ (α - 1) ≤ (min s 1 / 2) ^ (α - 1) := by
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      have : min s 1 ≤ min u.im 1 := min_le_min_right _ hkoe
      linarith
    have hhalf : (min s 1 / 2) ^ (α - 1) = (min s 1) ^ (α - 1) * D2 := by
      rw [div_eq_mul_one_div, Real.mul_rpow (by positivity) (by norm_num)]
    have hminle : (min s 1) ^ (α - 1) ≤ s ^ (α - 1) + 1 := by
      rw [min_comm]; exact RS.hl_min_rpow_le hs0
    have hsa : s ^ (α - 1) * a ≤ K' ^ α / c * y ^ (α - 1) := by
      rw [Real.rpow_sub_one hs0.ne', Real.rpow_sub_one hy.ne']
      have hsK : s ^ α ≤ (K' * y) ^ α :=
        Real.rpow_le_rpow hs0.le (hkoe.trans hKu) hα.le
      rw [Real.mul_rpow hK'0 hy.le] at hsK
      have hsa' : s ^ α / s * a = s ^ α / (c * y) := by
        rw [hsdef]; field_simp
      rw [hsa']
      rw [div_le_iff₀ (by positivity)]
      have : K' ^ α / c * (y ^ α / y) * (c * y) = K' ^ α * y ^ α := by
        field_simp
      rw [this]
      exact hsK
    calc ‖deriv f u‖ * a ≤ C' * (min u.im 1 / 2) ^ (α - 1) * a := by
          refine mul_le_mul_of_nonneg_right (hfu.trans ?_) ha0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
      _ ≤ C' * ((min s 1) ^ (α - 1) * D2) * a := by
          rw [← hhalf]; gcongr
      _ ≤ C' * ((s ^ (α - 1) + 1) * D2) * a := by gcongr
      _ = C' * D2 * (s ^ (α - 1) * a + a) := by ring
      _ ≤ C' * D2 * (K' ^ α / c * y ^ (α - 1) + K' / c) := by gcongr
      _ ≤ C' * D2 * (K' ^ α / c * (min 1 y) ^ (α - 1) + K' / c * (min 1 y) ^ (α - 1)) := by
          gcongr
          · exact le_mul_of_one_le_right (by positivity) hmin1
      _ = Cst * (min 1 y) ^ (α - 1) := by rw [hCst]; ring
  obtain ⟨C'', -, hC''⟩ := RS.hardyLittlewood_holder hψdiff hCst0 hα hα1 hbd
  refine ⟨C'', fun z hz w hw hzR hwR => holder_Hbar_of_holder_H hc hC'' z hz w hw ?_ ?_⟩
  · exact hzR.trans (le_max_left _ _)
  · exact hwR.trans (le_max_left _ _)

end G1RC
end Thm18Asm
end QuantumZipper
