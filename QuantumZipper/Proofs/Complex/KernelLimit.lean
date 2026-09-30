import QuantumZipper.Proofs.Complex.KernelBasic
import QuantumZipper.Proofs.Complex.BasicsMontel
import QuantumZipper.Proofs.Complex.BasicsHurwitz

/-!
# Carathéodory kernel theorem: identification of the image of a limit map (EXT-CA KT1, D7)

Let `F n` map `𝔻` conformally onto `G n` and `F n → h` locally uniformly on `𝔻`, `h`
injective. Following the proof of Pommerenke, *Boundary Behaviour of Conformal Maps* (1992),
Thm 1.8, p. 14 (and the uniqueness-of-kernel argument on p. 13):

* `image_subset_of_tendsto`: condition (ii) of kernel convergence forces `h(𝔻) ⊆ D`. If
  `h(𝔻)` met `∂D` at `h z`, the points `w_n ∈ ∂G_n → h z` would be values of `F n` for large
  `n` by Hurwitz's theorem (A5), but `w_n ∉ G_n = F_n(𝔻)`. (Pommerenke obtains `G* ⊂ G` from
  part (a) (i), whose proof is this Rouché/Hurwitz argument.)
* `subset_image_of_tendsto`: condition (i) forces `D ⊆ h(𝔻)`. If `w* ∈ D ∩ ∂h(𝔻)`, take
  `z` with `h z` close to `w*`; Koebe for `h` (Cor. 1.4 lower half) makes
  `(1 − |z|) |h'(z)|` small, hence by Cor. 1.4 upper half (`infDist_compl_le_schwarzPick`)
  `F_n(𝔻)` has boundary points close to `F_n(z) ≈ w*`, contradicting `D(w*, δ) ⊂ G_n`
  (Pommerenke's proof of part (a) (ii) combined with his uniqueness argument, p. 13).
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped ComplexOrder

namespace QuantumZipper.CA.Kernel

theorem tendstoLocallyUniformlyOn_sub_const {F : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {s : Set ℂ}
    {u : ℕ → ℂ} {w : ℂ} (hF : TendstoLocallyUniformlyOn F h atTop s)
    (hu : Tendsto u atTop (𝓝 w)) :
    TendstoLocallyUniformlyOn (fun n z => F n z - u n) (fun z => h z - w) atTop s := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hF ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := hF (ε / 2) (half_pos hε) x hx
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev, (Metric.tendsto_nhds.1 hu) (ε / 2) (half_pos hε)] with n hn hun y hy
  calc dist (h y - w) (F n y - u n) ≤ dist (h y) (F n y) + dist w (u n) := dist_sub_sub_le _ _ _ _
    _ < ε := by rw [dist_comm w]; linarith [hn y hy]

/-- Kernel convergence passes to subsequences (Pommerenke, p. 13). -/
theorem KernelConvergesTo.comp {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ}
    (hker : KernelConvergesTo G D w₀) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    KernelConvergesTo (fun n => G (φ n)) D w₀ := by
  obtain ⟨hi, hii⟩ := hker
  refine ⟨hi.imp id fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun w hw => ?_⟩, fun w hw => ?_⟩
  · obtain ⟨U, hU, hev⟩ := h.2.2.2.2 w hw
    exact ⟨U, hU, hφ.tendsto_atTop.eventually hev⟩
  · obtain ⟨u, hu, hut⟩ := hii w hw
    exact ⟨u ∘ φ, fun n => hu (φ n), hut.comp hφ.tendsto_atTop⟩

theorem isOpen_image_ball {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1))
    (hi : InjOn F (ball 0 1)) : IsOpen (F '' ball 0 1) :=
  Koebe.isOpen_image_of_injOn isOpen_ball hd hi subset_rfl isOpen_ball

/-- Condition (ii) of kernel convergence: the limit map takes values in `D`. -/
theorem image_subset_of_tendsto {G : ℕ → Set ℂ} {D : Set ℂ} {F : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (ball 0 1)) (hFi : ∀ n, InjOn (F n) (ball 0 1))
    (hFim : ∀ n, F n '' ball 0 1 = G n)
    (hlim : TendstoLocallyUniformlyOn F h atTop (ball 0 1))
    (hnc : ¬ ∃ c, EqOn h (fun _ => c) (ball 0 1)) (hDo : IsOpen D) (h0 : h 0 ∈ D)
    (hii : ∀ w ∈ frontier D, ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (G n)) ∧
      Tendsto u atTop (𝓝 w)) :
    h '' ball 0 1 ⊆ D := by
  have hB : IsPreconnected (ball (0 : ℂ) 1) := (convex_ball 0 1).isPreconnected
  have hhd : DifferentiableOn ℂ h (ball 0 1) :=
    hlim.differentiableOn (Eventually.of_forall hFd) isOpen_ball
  refine (hB.image h hhd.continuousOn).subset_of_closure_inter_subset hDo
    ⟨h 0, ⟨0, mem_ball_self one_pos, rfl⟩, h0⟩ ?_
  rintro w ⟨hwc, z, hz, rfl⟩
  by_contra hwD
  have hwf : h z ∈ frontier D := by
    rw [hDo.frontier_eq]; exact ⟨hwc, hwD⟩
  obtain ⟨u, hu, hut⟩ := hii _ hwf
  have hsub := tendstoLocallyUniformlyOn_sub_const hlim hut
  have hnc' : ¬ ∃ c, EqOn (fun ζ => h ζ - h z) (fun _ => c) (ball 0 1) := by
    rintro ⟨c, hc⟩
    refine hnc ⟨c + h z, fun ζ hζ => ?_⟩
    have := hc hζ
    simp only at this ⊢
    linear_combination this
  have hH := hurwitz_eventually_exists_zero isOpen_ball hB
    (fun n => (hFd n).sub_const (u n)) hsub hnc' hz (by simp) one_pos
  obtain ⟨n, ζ, hζ, -, hζ0⟩ := hH.exists
  have hmem : u n ∈ G n := by
    rw [← hFim n]; exact ⟨ζ, hζ, (sub_eq_zero.1 hζ0)⟩
  have hGo : IsOpen (G n) := hFim n ▸ isOpen_image_ball (hFd n) (hFi n)
  have := hu n
  rw [hGo.frontier_eq] at this
  exact this.2 hmem

/-- Condition (i) of kernel convergence: every point of `D` is a value of the limit map. -/
theorem subset_image_of_tendsto {G : ℕ → Set ℂ} {D : Set ℂ} {F : ℕ → ℂ → ℂ} {h : ℂ → ℂ}
    (hFd : ∀ n, DifferentiableOn ℂ (F n) (ball 0 1)) (hFi : ∀ n, InjOn (F n) (ball 0 1))
    (hFim : ∀ n, F n '' ball 0 1 = G n)
    (hlim : TendstoLocallyUniformlyOn F h atTop (ball 0 1)) (hhi : InjOn h (ball 0 1))
    (hDc : IsPreconnected D) (h0 : h 0 ∈ D)
    (hi : ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n) :
    D ⊆ h '' ball 0 1 := by
  have hhd : DifferentiableOn ℂ h (ball 0 1) :=
    hlim.differentiableOn (Eventually.of_forall hFd) isOpen_ball
  set S := h '' ball (0 : ℂ) 1 with hS
  refine hDc.subset_of_closure_inter_subset (isOpen_image_ball hhd hhi)
    ⟨h 0, h0, 0, mem_ball_self one_pos, rfl⟩ ?_
  rintro w ⟨hwc, hwD⟩
  by_contra hwS
  obtain ⟨U, hU, hUev⟩ := hi w hwD
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  set η := δ / 200 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨_, ⟨z, hz, rfl⟩, hzw⟩ := Metric.mem_closure_iff.1 hwc η hηpos
  have hKo := Koebe.koebeCovConst_mul_le_infDist_of_mem hhd hhi hz
  have hinf : infDist (h z) (h '' ball 0 1)ᶜ ≤ dist w (h z) := by
    rw [dist_comm]; exact infDist_le_dist_of_mem hwS
  have hderiv := (hlim.deriv (Eventually.of_forall hFd) isOpen_ball).tendsto_at hz
  have hval := hlim.tendsto_at hz
  obtain ⟨n, ⟨hUn, hvn⟩, hdn⟩ := ((hUev.and ((Metric.tendsto_nhds.1 hval) η hηpos)).and
    ((Metric.tendsto_nhds.1 hderiv) η hηpos)).exists
  simp only [Function.comp_apply] at hdn
  have hSP := infDist_compl_le_schwarzPick (hFd n) (hFi n) hz
  rw [hFim n] at hSP
  have hGne : (G n)ᶜ.Nonempty := by
    rw [nonempty_compl, ← hFim n]; exact Koebe.image_ball_ne_univ one_pos (hFd n) (hFi n)
  have hlow : δ - 2 * η ≤ infDist (F n z) (G n)ᶜ := by
    rw [le_infDist hGne]
    intro y hy
    have hyδ : δ ≤ dist y w := by
      by_contra hlt
      push Not at hlt
      exact hy (hUn (hδU (by rw [mem_ball]; exact hlt)))
    have h1 : dist y w ≤ dist (F n z) y + dist (F n z) w := by
      have := dist_triangle y (F n z) w; rwa [dist_comm y (F n z)] at this
    have h2 := dist_triangle (F n z) (h z) w
    rw [dist_comm w] at hzw
    linarith
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  rw [dist_zero_right, show Koebe.koebeCovConst = 1 / 48 from rfl] at hKo
  have hdF : ‖deriv (F n) z‖ ≤ ‖deriv h z‖ + η := by
    have := norm_sub_norm_le (deriv (F n) z) (deriv h z)
    rw [← dist_eq_norm] at this
    linarith
  set A := 1 - ‖z‖ with hA
  have hA0 : 0 ≤ A := by linarith
  have e1 : (1 - ‖z‖ ^ 2) * ‖deriv (F n) z‖ ≤ 2 * A * ‖deriv (F n) z‖ :=
    mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg z]) (norm_nonneg _)
  have e2 : 2 * A * ‖deriv (F n) z‖ ≤ 2 * A * (‖deriv h z‖ + η) := by gcongr
  have e3 : A * η ≤ η := by nlinarith [norm_nonneg z]
  linarith

end QuantumZipper.CA.Kernel
