import QuantumZipper.Proofs.Complex.KernelLimit

/-!
# The Carathéodory kernel theorem (EXT-CA KT1, statement fixed by DECISIONS D7)

`caratheodory_kernel_theorem`: let `f n` map `𝔻` conformally onto `G n` with `f n 0 = w₀`,
`f n'(0) > 0`, and let `g` map `𝔻` conformally onto `D` with `g 0 = w₀`, `g'(0) > 0`. If
`G n → D` with respect to `w₀` in the sense of kernel convergence (`KernelConvergesTo`,
Pommerenke's conditions (i)–(ii)), then `f n → g` locally uniformly in `𝔻`.

This is the direction "`G_n → G` ⇒ `f_n → f`" of Pommerenke, *Boundary Behaviour of Conformal
Maps* (1992), Theorem 1.8, p. 14, in the non-degenerate case `G ≠ {w₀}` (D7). We follow
Pommerenke's proof of part (b):

* `dist(w₀, ∂G_n)` is bounded above by (ii) and below by (i), so by Koebe (Cor. 1.4, here
  `Koebe.koebeCovConst_mul_le_infDist`, `Koebe.infDist_le_mul_norm_deriv`) `f_n'(0)` is
  bounded above and below for large `n`; the growth theorem (`Koebe.norm_sub_le_growth_global`,
  K4) makes `(f_n)` locally bounded and Montel (A4) gives convergent subsequences;
* a subsequential limit `h` has `h(0) = w₀`, `h'(0) > 0`, so it is injective (Hurwitz, A5);
  its image is `D` (Pommerenke's part (a) plus uniqueness of the kernel, p. 13, here
  `image_subset_of_tendsto`, `subset_image_of_tendsto`), so `h = g` by uniqueness of the
  normalized Riemann map (`eqOn_of_image_eq_of_deriv_pos`);
* if `f_n ↛ g`, a subsequence stays away from `g` on a compact set; its sub-subsequential limit
  is `g` by the above: contradiction.
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped ComplexOrder

namespace QuantumZipper.CA.Kernel

theorem norm_eq_re_of_pos {z : ℂ} (hz : 0 < z) : ‖z‖ = z.re := by
  obtain ⟨a, ha, rfl⟩ := exists_ofReal_of_pos hz
  simp [Complex.norm_real, abs_of_pos ha]

/-- Every sequence as in the kernel theorem has a subsequence converging to `g`. -/
theorem exists_subseq_tendsto_of_kernel {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ}
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1)) (hfi : ∀ n, InjOn (f n) (ball 0 1))
    (hfim : ∀ n, f n '' ball 0 1 = G n) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0)
    (hgd : DifferentiableOn ℂ g (ball 0 1)) (hgi : InjOn g (ball 0 1))
    (hgim : g '' ball 0 1 = D) (hg0 : g 0 = w₀) (hg' : 0 < deriv g 0)
    (hker : KernelConvergesTo G D w₀) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      TendstoLocallyUniformlyOn (fun k => f (ψ k)) g atTop (ball 0 1) := by
  have h0B : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hw₀D : w₀ ∈ D := hgim ▸ hg0 ▸ mem_image_of_mem g h0B
  have hDo : IsOpen D := hgim ▸ isOpen_image_ball hgd hgi
  have hDne : D ≠ univ := hgim ▸ Koebe.image_ball_ne_univ one_pos hgd hgi
  have hDc : IsPreconnected D := hgim ▸ (convex_ball (0 : ℂ) 1).isPreconnected.image g
    hgd.continuousOn
  have hDsing : D ≠ {w₀} := by
    intro hD
    have h12 : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]; norm_num
    have hmem : g (1 / 2) ∈ D := hgim ▸ mem_image_of_mem g h12
    rw [hD, mem_singleton_iff, ← hg0] at hmem
    have := hgi h12 h0B hmem
    norm_num at this
  obtain ⟨hi', hii⟩ := hker
  have hi : ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n := by
    rcases hi' with h | h
    · exact absurd h hDsing
    · exact h.2.2.2.2
  have hGo : ∀ n, IsOpen (G n) := fun n => hfim n ▸ isOpen_image_ball (hfd n) (hfi n)
  -- lower bound on `f_n'(0)` from condition (i) at `w₀`
  obtain ⟨U, hU, hUev⟩ := hi w₀ hw₀D
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hlow : ∀ᶠ n in atTop, r ≤ ‖deriv (f n) 0‖ := by
    filter_upwards [hUev] with n hn
    have h1 := Koebe.infDist_le_mul_norm_deriv one_pos (hfd n) (hfi n)
    have hne : (f n '' ball 0 1)ᶜ.Nonempty := by
      rw [nonempty_compl]; exact Koebe.image_ball_ne_univ one_pos (hfd n) (hfi n)
    have h2 : r ≤ infDist (f n 0) (f n '' ball 0 1)ᶜ := by
      rw [le_infDist hne]
      intro y hy
      by_contra hlt
      push Not at hlt
      apply hy
      rw [hfim n]
      apply hn
      apply hrU
      rw [mem_ball, dist_comm, ← hf0 n]
      exact hlt
    linarith
  -- upper bound on `f_n'(0)` from condition (ii) at a boundary point of `D`
  obtain ⟨w, hw⟩ := nonempty_frontier_iff.2 ⟨⟨w₀, hw₀D⟩, hDne⟩
  obtain ⟨u, hu, hut⟩ := hii w hw
  have hup : ∀ᶠ n in atTop, ‖deriv (f n) 0‖ ≤ 48 * (dist w₀ w + 1) := by
    filter_upwards [(Metric.tendsto_nhds.1 hut) 1 one_pos] with n hn
    have h1 := Koebe.koebeCovConst_mul_le_infDist one_pos (hfd n) (hfi n)
    have hun : u n ∈ (f n '' ball 0 1)ᶜ := by
      have := hu n
      rw [(hGo n).frontier_eq, ← hfim n] at this
      exact this.2
    have h2 := infDist_le_dist_of_mem (x := f n 0) hun
    rw [hf0 n] at h1 h2
    have h3 : dist w₀ (u n) ≤ dist w₀ w + dist w (u n) := dist_triangle _ _ _
    rw [dist_comm] at hn
    rw [show Koebe.koebeCovConst = 1 / 48 from rfl] at h1
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlow.and hup)
  set M := 48 * (dist w₀ w + 1) with hMdef
  -- local boundedness (growth theorem) and Montel
  have hb : ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K →
      ∃ B, ∀ k, ∀ z ∈ K, ‖f (k + N) z‖ ≤ B := by
    intro K hK hKc
    obtain ⟨s, hs1, hKs⟩ := exists_lt_subset_ball hKc.isClosed hK
    set s' := max s 0 with hs'
    have hs'1 : s' < 1 := max_lt hs1 one_pos
    refine ⟨‖w₀‖ + M * (1 - s') ^ (-Koebe.koebeDistExp), fun k z hz => ?_⟩
    have hzB : z ∈ ball (0 : ℂ) 1 := hK hz
    have hg := Koebe.norm_sub_le_growth_global (hfd (k + N)) (hfi (k + N)) hzB
    rw [hf0, div_one] at hg
    have hdz : dist z 0 ≤ s' := (mem_ball.1 (hKs hz)).le.trans (le_max_left _ _)
    have hdz0 : 0 ≤ dist z 0 := dist_nonneg
    have hM : ‖deriv (f (k + N)) 0‖ ≤ M := (hN (k + N) (by omega)).2
    have hpow : (1 - dist z 0) ^ (-Koebe.koebeDistExp) ≤ (1 - s') ^ (-Koebe.koebeDistExp) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
        (by linarith [Koebe.koebeDistExp_pos])
    have hp0 : 0 ≤ (1 - dist z 0) ^ (-Koebe.koebeDistExp) := Real.rpow_nonneg (by linarith) _
    have hdz1 : dist z 0 ≤ 1 := by linarith
    have hkey : dist z 0 * (‖deriv (f (k + N)) 0‖ * (1 - dist z 0) ^ (-Koebe.koebeDistExp))
        ≤ M * (1 - s') ^ (-Koebe.koebeDistExp) := by
      calc _ ≤ 1 * (M * (1 - s') ^ (-Koebe.koebeDistExp)) := by
            apply mul_le_mul hdz1 _ (by positivity) zero_le_one
            exact mul_le_mul hM hpow hp0 (by positivity)
        _ = _ := one_mul _
    calc ‖f (k + N) z‖ = ‖w₀ + (f (k + N) z - w₀)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w₀‖ + ‖f (k + N) z - w₀‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  obtain ⟨φ, h, hφ, hhd, hlim⟩ := montel isOpen_ball (fun k => hfd (k + N)) hb
  set ψ : ℕ → ℕ := fun k => φ k + N with hψdef
  have hψ : StrictMono ψ := fun a b hab => Nat.add_lt_add_right (hφ hab) N
  have hlim' : TendstoLocallyUniformlyOn (fun k => f (ψ k)) h atTop (ball 0 1) := hlim
  have hFd : ∀ k, DifferentiableOn ℂ (f (ψ k)) (ball 0 1) := fun k => hfd _
  -- normalization of the limit
  have hh0 : h 0 = w₀ := by
    have := hlim'.tendsto_at h0B
    simp only [hf0] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hder := (hlim'.deriv (Eventually.of_forall hFd) isOpen_ball).tendsto_at h0B
  have hre : Tendsto (fun k => (deriv (f (ψ k)) 0).re) atTop (𝓝 (deriv h 0).re) :=
    (Complex.continuous_re.tendsto _).comp hder
  have him : Tendsto (fun k => (deriv (f (ψ k)) 0).im) atTop (𝓝 (deriv h 0).im) :=
    (Complex.continuous_im.tendsto _).comp hder
  have hre_ge : r ≤ (deriv h 0).re := by
    refine ge_of_tendsto hre (Eventually.of_forall fun k => ?_)
    rw [← norm_eq_re_of_pos (hf' _)]
    exact (hN (ψ k) (by simp [hψdef])).1
  have him0 : (deriv h 0).im = 0 := by
    have hc : (fun k => (deriv (f (ψ k)) 0).im) = fun _ => 0 := by
      funext k; exact ((Complex.pos_iff.1 (hf' (ψ k))).2).symm
    rw [hc] at him
    exact tendsto_nhds_unique him tendsto_const_nhds
  have hpos : 0 < deriv h 0 := Complex.pos_iff.2 ⟨by linarith, him0.symm⟩
  have hnc : ¬ ∃ c, EqOn h (fun _ => c) (ball 0 1) := by
    rintro ⟨c, hc⟩
    have hev : h =ᶠ[𝓝 0] fun _ => c := Filter.eventually_of_mem (isOpen_ball.mem_nhds h0B) hc
    rw [hev.deriv_eq, deriv_const] at hpos
    exact lt_irrefl _ hpos
  have hhi : InjOn h (ball 0 1) := hurwitz_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    hFd (fun k => hfi _) hlim' hnc
  -- the image of the limit is `D`
  have hsub1 : h '' ball 0 1 ⊆ D := image_subset_of_tendsto hFd (fun k => hfi _)
    (fun k => hfim _) hlim' hnc hDo (hh0 ▸ hw₀D) fun w hw => by
      obtain ⟨u, hu, hut⟩ := hii w hw
      exact ⟨u ∘ ψ, fun n => hu (ψ n), hut.comp hψ.tendsto_atTop⟩
  have hsub2 : D ⊆ h '' ball 0 1 := subset_image_of_tendsto hFd (fun k => hfi _)
    (fun k => hfim _) hlim' hhi hDc (hh0 ▸ hw₀D) fun w hw => by
      obtain ⟨U, hU, hev⟩ := hi w hw
      exact ⟨U, hU, hψ.tendsto_atTop.eventually hev⟩
  have heq : EqOn h g (ball 0 1) := eqOn_of_image_eq_of_deriv_pos hhd hhi hgd hgi
    (by rw [hgim]; exact subset_antisymm hsub1 hsub2) (hh0.trans hg0.symm) hpos hg'
  exact ⟨ψ, hψ, hlim'.congr_right heq⟩

/-- **Carathéodory kernel theorem** (Pommerenke, *Boundary Behaviour of Conformal Maps*, 1992,
Theorem 1.8, p. 14; direction "kernel convergence ⇒ locally uniform convergence", non-degenerate
limit, as fixed by DECISIONS D7). Let `f n` map `𝔻` conformally onto `G n` with `f n 0 = w₀`
and `f n'(0) > 0`, and let `g` map `𝔻` conformally onto `D` with `g 0 = w₀` and `g'(0) > 0`.
If `G n → D` with respect to `w₀` in the sense of kernel convergence, then `f n → g` locally
uniformly in `𝔻`. -/
theorem caratheodory_kernel_theorem {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ}
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1)) (hfi : ∀ n, InjOn (f n) (ball 0 1))
    (hfim : ∀ n, f n '' ball 0 1 = G n) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0)
    (hgd : DifferentiableOn ℂ g (ball 0 1)) (hgi : InjOn g (ball 0 1))
    (hgim : g '' ball 0 1 = D) (hg0 : g 0 = w₀) (hg' : 0 < deriv g 0)
    (hker : KernelConvergesTo G D w₀) :
    TendstoLocallyUniformlyOn f g atTop (ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hK hKc
  by_contra hnot
  rw [Metric.tendstoUniformlyOn_iff] at hnot
  push Not at hnot
  obtain ⟨ε, hε, hfreq⟩ := hnot
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, -, hlim⟩ := exists_subseq_tendsto_of_kernel (f := fun n => f (φ n))
    (G := fun n => G (φ n)) (fun n => hfd _) (fun n => hfi _) (fun n => hfim _)
    (fun n => hf0 _) (fun n => hf' _) hgd hgi hgim hg0 hg' (hker.comp hφ)
  have hK' := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 hlim K hK hKc
  rw [Metric.tendstoUniformlyOn_iff] at hK'
  obtain ⟨k, hk⟩ := (hK' ε hε).exists
  obtain ⟨x, hx, hxε⟩ := hP (ψ k)
  exact absurd (hk x hx) (not_lt.2 hxε)

end QuantumZipper.CA.Kernel
