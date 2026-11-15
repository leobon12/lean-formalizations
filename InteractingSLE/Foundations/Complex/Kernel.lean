import InteractingSLE.Foundations.Complex.RiemannMap
import QuantumZipper.Proofs.Complex.KernelTheorem
import QuantumZipper.Proofs.Complex.KernelChordK1
import QuantumZipper.Proofs.Complex.TopoSep
import Mathlib.Data.Rat.Denumerable

/-!
# The Carathéodory kernel theorem

Design `planning/INFRA-GEO.md` §3–§4 (packet GEO-KERNEL). Kernel convergence is QuantumZipper's
`QuantumZipper.CA.Kernel.KernelConvergesTo G D w₀` (Pommerenke, *Boundary Behaviour of Conformal
Maps* (1992), §1.4, p. 13, conditions (i)–(ii)); conformal maps are
`SupercriticalConformalCovariance.IsConformalBijection`.

## Main results

* `kernel_convergence_iff`: **Carathéodory's kernel theorem**, both directions, including the
  degenerate kernel `{w₀}` (Pommerenke 1992, Theorem 1.8, p. 14). Let `f n` map `𝔻` conformally
  onto `G n` with `f n 0 = w₀`, `f n'(0) > 0`; let `g` be the constant `w₀` if `D = {w₀}`, and
  otherwise map `𝔻` conformally onto `D` with `g 0 = w₀`, `g'(0) > 0`. Then `f n → g` locally
  uniformly in `𝔻` iff `G n → D` with respect to `w₀`.
* `kernelConvergesTo_iUnion_of_monotone`, `kernelConvergesTo_connectedComponentIn_of_antitone`,
  `kernelConvergesTo_singleton_of_antitone`: increasing domains converge to their union;
  decreasing domains converge to the component of the interior of their intersection that
  contains `w₀`, or to `{w₀}` (Pommerenke 1992, p. 13–14, the remark after the definition of the
  kernel).
* `tendsto_deriv_of_kernelConvergesTo`, `tendsto_deriv_of_antitone`, `tendsto_deriv_of_monotone`:
  the conformal radius `f'(0) = |f'(0)|` of the domain viewed from `w₀` (specification p. 74, the
  definition after (3.15): `|φ'(0)|` for `φ : 𝔻 → D`, `φ(0) = z`) is continuous along kernel
  convergence, in particular along decreasing and increasing sequences of domains (specification
  p. 179 and p. 198); `tendsto_deriv_zero_of_antitone`: it tends to `0` when the base point is not
  interior to the intersection.
* `exists_isConformalBijection_of_kernelConvergesTo`: a non-degenerate kernel of normalized
  conformal images of `𝔻` is one (so `exists_tendsto_deriv_of_antitone` needs no given limit map).
* `exists_measurable_normalizedRiemannMap`, `exists_measurable_normalizedChart`: normalized
  Riemann maps `𝔻 → U ω` and normalized charts `U ω → 𝔻` can be chosen measurably in a parameter
  `ω`, when compact inclusion in `U ω` is a measurable event (specification Lemma CM-B, p. 659:
  exhaustion and kernel convergence; here the exhausting simply connected domains are hole-filled
  finite unions of rational discs, `ratApprox`, `fillHoles`).
* `exists_isConformalBijection_ball_and_inv`, `exists_isConformalBijection_ball_onto`: the Riemann
  map normalized from the disc side (`f 0 = a`, `f'(0) > 0`).

## Proof routes

* `G n → D ⇒ f n → g`: the non-degenerate case is QuantumZipper's
  `QuantumZipper.CA.Kernel.caratheodory_kernel_theorem`. In the degenerate case, condition (ii)
  makes `dist(w₀, ∂G n) → 0`, hence `f n'(0) → 0` by Koebe's lower estimate
  (`QuantumZipper.CA.Koebe.koebeCovConst_mul_le_infDist`), and the growth theorem
  (`QuantumZipper.CA.Koebe.norm_sub_le_growth_global`) gives `f n → w₀` uniformly on compacta.
* `f n → g ⇒ G n → D`: Koebe's two estimates `c (1 − |z|) |F'(z)| ≤ dist(F z, ∂F(𝔻)) ≤
  (1 − |z|²) |F'(z)|` and the locally uniform convergence of the derivatives. Condition (i): a
  disc of radius `≍ (1 − |z|)|g'(z)|` about `g z` lies in every late `G n`. Condition (ii): a
  point `w ∈ ∂D` is approximated by `g z` with `(1 − |z|)|g'(z)|` small, so every late `G n` has
  a complementary point near `f n z ≈ g z ≈ w`, and the disc about `w` meets `∂G n`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function
open scoped ComplexOrder

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA.Kernel (KernelConvergesTo)

namespace InteractingSLE

/-! ### Elementary facts -/

/-- A ball about `w` meeting an open set `G` and its complement meets the frontier of `G`. -/
theorem ball_inter_frontier_nonempty {G : Set ℂ} (hG : IsOpen G) {w x y : ℂ} {ε : ℝ}
    (hx : x ∈ ball w ε) (hxG : x ∈ G) (hy : y ∈ ball w ε) (hyG : y ∉ G) :
    (ball w ε ∩ frontier G).Nonempty :=
  QuantumZipper.CA.Kernel.inter_frontier_nonempty_of_isPreconnected
    (convex_ball w ε).isPreconnected hG hx hxG hy hyG

/-- The frontier of a nonempty open proper subset of `ℂ` is nonempty. -/
theorem frontier_nonempty_of_isOpen {G : Set ℂ} (hne : G.Nonempty) (hG : G ≠ univ) :
    (frontier G).Nonempty :=
  nonempty_frontier_iff.2 ⟨hne, hG⟩

/-- If, for every `ε > 0`, the frontiers of `G n` eventually meet `ball w ε`, then frontier
points `u n ∈ ∂G n` converge to `w`. -/
theorem exists_tendsto_frontier {G : ℕ → Set ℂ} {w : ℂ} (hne : ∀ n, (frontier (G n)).Nonempty)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, (ball w ε ∩ frontier (G n)).Nonempty) :
    ∃ u : ℕ → ℂ, (∀ n, u n ∈ frontier (G n)) ∧ Tendsto u atTop (𝓝 w) := by
  have hex : ∀ n, ∃ y ∈ frontier (G n),
      dist w y < infDist w (frontier (G n)) + 1 / ((n : ℝ) + 1) := fun n =>
    (infDist_lt_iff (hne n)).1 (lt_add_of_pos_right _ (by positivity))
  choose u hu hud using hex
  refine ⟨u, hu, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := (h (ε / 2) (by positivity)).exists_forall_of_atTop
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (2 / ε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨y, hyb, hyf⟩ := hN₁ n (le_of_max_le_left hn)
  have h1 : infDist w (frontier (G n)) < ε / 2 :=
    (infDist_le_dist_of_mem hyf).trans_lt (by rw [dist_comm]; exact mem_ball.1 hyb)
  have h2 : 1 / ((n : ℝ) + 1) < ε / 2 := by
    have hn2 : (N₂ : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    rw [div_lt_iff₀ (by positivity)]
    have : 2 / ε < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at this
    linarith
  rw [dist_comm]
  linarith [hud n]

/-- The frontier of a singleton in `ℂ` is the singleton. -/
theorem frontier_singleton_complex (w : ℂ) : frontier ({w} : Set ℂ) = {w} := by
  rw [frontier, closure_singleton, interior_singleton, sdiff_empty]

/-- Points of the frontier of an open set are outside it. -/
theorem notMem_of_mem_frontier {G : Set ℂ} (hG : IsOpen G) {u : ℂ} (hu : u ∈ frontier G) :
    u ∉ G := by
  rw [hG.frontier_eq] at hu
  exact hu.2

/-! ### Koebe's estimates in the form used here -/

section Koebe

variable {F : ℂ → ℂ}

/-- Koebe's upper estimate (Pommerenke 1992, Cor. 1.4): `dist(F z, ℂ \ F(𝔻)) ≤ (1 − |z|²)|F'(z)|`
(QuantumZipper `infDist_compl_le_schwarzPick`). -/
theorem infDist_compl_image_le (hd : DifferentiableOn ℂ F (ball 0 1))
    (hi : InjOn F (ball 0 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    infDist (F z) (F '' ball 0 1)ᶜ ≤ (1 - ‖z‖ ^ 2) * ‖deriv F z‖ :=
  QuantumZipper.CA.Kernel.infDist_compl_le_schwarzPick hd hi hz

/-- Koebe's lower estimate with QuantumZipper's (non-sharp) constant `c = 1/48`:
`c (1 − |z|) |F'(z)| ≤ dist(F z, ℂ \ F(𝔻))`. -/
theorem koebe_mul_le_infDist_compl_image (hd : DifferentiableOn ℂ F (ball 0 1))
    (hi : InjOn F (ball 0 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    QuantumZipper.CA.Koebe.koebeCovConst * (1 - ‖z‖) * ‖deriv F z‖ ≤
      infDist (F z) (F '' ball 0 1)ᶜ := by
  have := QuantumZipper.CA.Koebe.koebeCovConst_mul_le_infDist_of_mem hd hi hz
  rwa [dist_zero_right] at this

end Koebe

/-! ### The kernel theorem -/

section KernelTheorem

variable {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ} {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}

/-- Locally uniform convergence of holomorphic maps on `𝔻` gives pointwise convergence of their
derivatives (Weierstrass; Mathlib `TendstoLocallyUniformlyOn.deriv`). -/
theorem tendsto_deriv_of_tendstoLocallyUniformlyOn
    (hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1))
    (hlim : TendstoLocallyUniformlyOn f g atTop (ball 0 1)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) :
    Tendsto (fun n => deriv (f n) z) atTop (𝓝 (deriv g z)) :=
  (hlim.deriv (Eventually.of_forall hfd) isOpen_ball).tendsto_at hz

/-- **Kernel theorem, "`f n → g` ⇒ `G n → D`"**, non-degenerate limit (Pommerenke 1992,
Theorem 1.8, p. 14): if conformal maps `f n : 𝔻 → G n` converge locally uniformly to a conformal
map `g : 𝔻 → D` with `g 0 = w₀`, then `G n → D` with respect to `w₀`. -/
theorem kernelConvergesTo_of_tendstoLocallyUniformlyOn
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n))
    (hg : IsConformalBijection g (ball 0 1) D) (hg0 : g 0 = w₀)
    (hlim : TendstoLocallyUniformlyOn f g atTop (ball 0 1)) :
    KernelConvergesTo G D w₀ := by
  have hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1) := fun n => (hf n).1
  have hfi : ∀ n, InjOn (f n) (ball 0 1) := fun n => (hf n).2.injOn
  have hfim : ∀ n, f n '' ball 0 1 = G n := fun n => (hf n).2.image_eq
  have hgim : g '' ball 0 1 = D := hg.2.image_eq
  have hGo : ∀ n, IsOpen (G n) := fun n =>
    hfim n ▸ QuantumZipper.CA.Kernel.isOpen_image_ball (hfd n) (hfi n)
  have hDo : IsOpen D := hgim ▸ QuantumZipper.CA.Kernel.isOpen_image_ball hg.1 hg.2.injOn
  set c := QuantumZipper.CA.Koebe.koebeCovConst with hcdef
  have hc : 0 < c := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hc1 : c ≤ 1 := by rw [hcdef]; norm_num [QuantumZipper.CA.Koebe.koebeCovConst]
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  refine ⟨Or.inr ⟨hDo, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← hgim]; exact ((convex_ball (0 : ℂ) 1).isConnected (nonempty_ball.2 one_pos)).image g hg.1.continuousOn
  · rw [← hgim]; exact QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hg.1 hg.2.injOn
  · rw [← hg0]; exact hg.2.mapsTo h0
  · -- condition (i): a fixed disc about `g z` lies in every late `G n`
    intro w hw
    rw [← hgim] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hdg : 0 < ‖deriv g z‖ := norm_pos_iff.2
      (QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hg.1 hg.2.injOn hz)
    have h1z : 0 < 1 - ‖z‖ := by linarith
    set ρ := c * (1 - ‖z‖) * ‖deriv g z‖ with hρ
    have hρpos : 0 < ρ := by positivity
    refine ⟨ball (g z) (ρ / 4), ball_mem_nhds _ (by positivity), ?_⟩
    have hd := tendsto_deriv_of_tendstoLocallyUniformlyOn hfd hlim hz
    have hnd : ∀ᶠ n in atTop, ‖deriv g z‖ / 2 < ‖deriv (f n) z‖ :=
      hd.norm.eventually (lt_mem_nhds (by linarith))
    have hv : ∀ᶠ n in atTop, f n z ∈ ball (g z) (ρ / 4) :=
      (hlim.tendsto_at hz).eventually (ball_mem_nhds _ (by positivity))
    filter_upwards [hnd, hv] with n hn1 hn2 y hy
    have hK := koebe_mul_le_infDist_compl_image (hfd n) (hfi n) hz
    rw [hfim n] at hK
    have hlt : dist (f n z) y < infDist (f n z) (G n)ᶜ := by
      have htri : dist (f n z) y ≤ dist (f n z) (g z) + dist y (g z) := dist_triangle_right _ _ _
      have hy' : dist y (g z) < ρ / 4 := mem_ball.1 hy
      have hn2' : dist (f n z) (g z) < ρ / 4 := mem_ball.1 hn2
      have hmul : c * (1 - ‖z‖) * (‖deriv g z‖ / 2) < c * (1 - ‖z‖) * ‖deriv (f n) z‖ :=
        mul_lt_mul_of_pos_left hn1 (by positivity)
      have : ρ / 2 = c * (1 - ‖z‖) * (‖deriv g z‖ / 2) := by rw [hρ]; ring
      linarith
    by_contra hyG
    exact absurd (infDist_le_dist_of_mem hyG) (not_le.2 hlt)
  · -- condition (ii): boundary points of `D` are limits of boundary points of `G n`
    intro w hw
    have hwD : w ∉ D := notMem_of_mem_frontier hDo hw
    have hwcl : w ∈ closure D := frontier_subset_closure hw
    have hne : ∀ n, (frontier (G n)).Nonempty := fun n =>
      frontier_nonempty_of_isOpen ⟨f n 0, (hf n).2.mapsTo h0⟩
        (hfim n ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos (hfd n) (hfi n))
    refine exists_tendsto_frontier hne fun ε hε => ?_
    obtain ⟨w', hw'D, hw'w⟩ := Metric.mem_closure_iff.1 hwcl (c * ε / 8) (by positivity)
    rw [← hgim] at hw'D
    obtain ⟨z, hz, rfl⟩ := hw'D
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    have hK := koebe_mul_le_infDist_compl_image hg.1 hg.2.injOn hz
    rw [hgim] at hK
    have hinf : infDist (g z) Dᶜ ≤ dist (g z) w := infDist_le_dist_of_mem hwD
    have h1 : (1 - ‖z‖) * ‖deriv g z‖ < ε / 8 := by
      have : c * ((1 - ‖z‖) * ‖deriv g z‖) < c * (ε / 8) := by
        calc c * ((1 - ‖z‖) * ‖deriv g z‖) = c * (1 - ‖z‖) * ‖deriv g z‖ := by ring
          _ ≤ dist (g z) w := hK.trans hinf
          _ < c * ε / 8 := by rw [dist_comm]; exact hw'w
          _ = c * (ε / 8) := by ring
      exact lt_of_mul_lt_mul_left this hc.le
    have h2 : (1 - ‖z‖ ^ 2) * ‖deriv g z‖ < ε / 4 := by
      have hq : 1 - ‖z‖ ^ 2 ≤ 2 * (1 - ‖z‖) := by nlinarith
      calc (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 2 * (1 - ‖z‖) * ‖deriv g z‖ :=
            mul_le_mul_of_nonneg_right hq (norm_nonneg _)
        _ = 2 * ((1 - ‖z‖) * ‖deriv g z‖) := by ring
        _ < 2 * (ε / 8) := by linarith
        _ = ε / 4 := by ring
    have hd := tendsto_deriv_of_tendstoLocallyUniformlyOn hfd hlim hz
    have hev1 : ∀ᶠ n in atTop, (1 - ‖z‖ ^ 2) * ‖deriv (f n) z‖ < ε / 4 :=
      (hd.norm.const_mul (1 - ‖z‖ ^ 2)).eventually (gt_mem_nhds h2)
    have hev2 : ∀ᶠ n in atTop, f n z ∈ ball (g z) (ε / 8) :=
      (hlim.tendsto_at hz).eventually (ball_mem_nhds _ (by positivity))
    filter_upwards [hev1, hev2] with n hn1 hn2
    have hU := infDist_compl_image_le (hfd n) (hfi n) hz
    rw [hfim n] at hU
    have hcne : ((G n)ᶜ).Nonempty := nonempty_compl.2
      (hfim n ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos (hfd n) (hfi n))
    obtain ⟨y, hyG, hy⟩ := (infDist_lt_iff hcne).1 (hU.trans_lt hn1)
    have hn2' : dist (f n z) (g z) < ε / 8 := mem_ball.1 hn2
    have hgw : dist (g z) w < ε / 8 := by
      rw [dist_comm]; exact hw'w.trans_le (by nlinarith)
    have hfw : dist (f n z) w < ε / 4 := by
      linarith [dist_triangle (f n z) (g z) w]
    refine ball_inter_frontier_nonempty (hGo n) (x := f n z) (y := y) ?_
      ((hf n).2.mapsTo hz) ?_ hyG
    · exact mem_ball.2 (by linarith)
    · exact mem_ball.2 (by linarith [dist_triangle y (f n z) w, dist_comm y (f n z)])

/-- **Kernel theorem, "`f n → w₀` ⇒ `G n → {w₀}`"**, degenerate limit (Pommerenke 1992,
Theorem 1.8). -/
theorem kernelConvergesTo_singleton_of_tendstoLocallyUniformlyOn
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hlim : TendstoLocallyUniformlyOn f (fun _ => w₀) atTop (ball 0 1)) :
    KernelConvergesTo G {w₀} w₀ := by
  have hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1) := fun n => (hf n).1
  have hfi : ∀ n, InjOn (f n) (ball 0 1) := fun n => (hf n).2.injOn
  have hfim : ∀ n, f n '' ball 0 1 = G n := fun n => (hf n).2.image_eq
  have hGo : ∀ n, IsOpen (G n) := fun n =>
    hfim n ▸ QuantumZipper.CA.Kernel.isOpen_image_ball (hfd n) (hfi n)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hne : ∀ n, (frontier (G n)).Nonempty := fun n =>
    frontier_nonempty_of_isOpen ⟨f n 0, (hf n).2.mapsTo h0⟩
      (hfim n ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos (hfd n) (hfi n))
  refine ⟨Or.inl rfl, ?_⟩
  intro w hw
  rw [frontier_singleton_complex, mem_singleton_iff] at hw
  subst hw
  refine exists_tendsto_frontier hne fun ε hε => ?_
  have hd := tendsto_deriv_of_tendstoLocallyUniformlyOn hfd hlim h0
  rw [deriv_const] at hd
  have hev : ∀ᶠ n in atTop, ‖deriv (f n) 0‖ < ε := by
    have := hd.norm
    rw [norm_zero] at this
    exact this.eventually (gt_mem_nhds hε)
  filter_upwards [hev] with n hn
  have hU := infDist_compl_image_le (hfd n) (hfi n) h0
  rw [hfim n, hf0 n, norm_zero] at hU
  have hcne : ((G n)ᶜ).Nonempty := nonempty_compl.2
    (hfim n ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos (hfd n) (hfi n))
  obtain ⟨y, hyG, hy⟩ := (infDist_lt_iff hcne).1 (hU.trans_lt (by simpa using hn))
  have hw0 : w ∈ G n := hf0 n ▸ (hf n).2.mapsTo h0
  exact ball_inter_frontier_nonempty (hGo n) (mem_ball_self hε) hw0
    (mem_ball.2 (by rw [dist_comm]; exact hy)) hyG

/-- **Kernel theorem, "`G n → {w₀}` ⇒ `f n → w₀`"**, degenerate kernel (Pommerenke 1992,
Theorem 1.8): condition (ii) gives boundary points of `G n` tending to `w₀`, so `f n'(0) → 0` by
Koebe's lower estimate, and the growth theorem gives uniform convergence on compacta. -/
theorem tendstoLocallyUniformlyOn_of_kernelConvergesTo_singleton
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hker : KernelConvergesTo G {w₀} w₀) :
    TendstoLocallyUniformlyOn f (fun _ => w₀) atTop (ball 0 1) := by
  have hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1) := fun n => (hf n).1
  have hfi : ∀ n, InjOn (f n) (ball 0 1) := fun n => (hf n).2.injOn
  have hfim : ∀ n, f n '' ball 0 1 = G n := fun n => (hf n).2.image_eq
  have hGo : ∀ n, IsOpen (G n) := fun n =>
    hfim n ▸ QuantumZipper.CA.Kernel.isOpen_image_ball (hfd n) (hfi n)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  set c := QuantumZipper.CA.Koebe.koebeCovConst with hcdef
  have hc : 0 < c := QuantumZipper.CA.Koebe.koebeCovConst_pos
  obtain ⟨u, hu, hut⟩ := hker.2 w₀ (by rw [frontier_singleton_complex]; exact mem_singleton _)
  -- the derivatives at `0` tend to `0`
  have hd : Tendsto (fun n => ‖deriv (f n) 0‖) atTop (𝓝 0) := by
    have hdist : Tendsto (fun n => dist w₀ (u n) / c) atTop (𝓝 0) := by
      have := ((tendsto_const_nhds (x := w₀)).dist hut).div_const c
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hdist
    have hK := koebe_mul_le_infDist_compl_image (hfd n) (hfi n) h0
    rw [hfim n, hf0 n, norm_zero, sub_zero, mul_one] at hK
    have hle : infDist w₀ (G n)ᶜ ≤ dist w₀ (u n) :=
      infDist_le_dist_of_mem (notMem_of_mem_frontier (hGo n) (hu n))
    rw [le_div_iff₀ hc]
    linarith
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball]
  intro K hK hKc
  obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball hKc.isClosed hK
  set s := max r (1 / 2) with hs
  have hs1 : s < 1 := max_lt hr1 (by norm_num)
  have hs0 : 1 / 2 ≤ s := le_max_right _ _
  set C := QuantumZipper.CA.Koebe.koebeDistExp with hC
  have hCpos : 0 < C := QuantumZipper.CA.Koebe.koebeDistExp_pos
  set M := (1 - s) ^ (-C) with hM
  have hMpos : 0 < M := Real.rpow_pos_of_pos (by linarith) _
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hd.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (M + 1) by positivity))]
    with n hn x hx
  have hxr : ‖x‖ < s := (mem_ball_zero_iff.1 (hKr hx)).trans_le (le_max_left _ _)
  have hx1 : x ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (hxr.trans hs1)
  have hg := QuantumZipper.CA.Koebe.norm_sub_le_growth_global (hfd n) (hfi n) hx1
  rw [hf0 n, dist_zero_right, div_one] at hg
  have hpow : (1 - ‖x‖) ^ (-C) ≤ M :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have hxle : ‖x‖ ≤ 1 := by linarith
  have hb : ‖x‖ * (‖deriv (f n) 0‖ * (1 - ‖x‖) ^ (-C)) ≤ ‖deriv (f n) 0‖ * M := by
    have h1 : ‖deriv (f n) 0‖ * (1 - ‖x‖) ^ (-C) ≤ ‖deriv (f n) 0‖ * M :=
      mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    have h2 : 0 ≤ ‖deriv (f n) 0‖ * (1 - ‖x‖) ^ (-C) :=
      mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
    nlinarith [norm_nonneg x]
  have hlt : ‖deriv (f n) 0‖ * M < ε := by
    have : ‖deriv (f n) 0‖ * M < ε / (M + 1) * (M + 1) := by
      have := mul_lt_mul_of_pos_right hn (show 0 < M + 1 by linarith)
      nlinarith [norm_nonneg (deriv (f n) 0)]
    rwa [div_mul_cancel₀ _ (by positivity)] at this
  rw [dist_comm, dist_eq_norm]
  linarith

/-- **Carathéodory's kernel theorem** (Pommerenke, *Boundary Behaviour of Conformal Maps* (1992),
Theorem 1.8, p. 14), both directions. Let `f n` map `𝔻` conformally onto `G n` with
`f n 0 = w₀` and `f n'(0) > 0`. If `D = {w₀}`, let `g = w₀` on `𝔻`; otherwise let `g` map `𝔻`
conformally onto `D` with `g 0 = w₀` and `g'(0) > 0`. Then `f n → g` locally uniformly in `𝔻` if
and only if `G n → D` with respect to `w₀` in the sense of kernel convergence. -/
theorem kernel_convergence_iff
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0)
    (hg : (D = {w₀} ∧ EqOn g (fun _ => w₀) (ball 0 1)) ∨
      (IsConformalBijection g (ball 0 1) D ∧ g 0 = w₀ ∧ 0 < deriv g 0)) :
    TendstoLocallyUniformlyOn f g atTop (ball 0 1) ↔ KernelConvergesTo G D w₀ := by
  rcases hg with ⟨rfl, hgc⟩ | ⟨hg, hg0, hg'⟩
  · constructor
    · intro hlim
      exact kernelConvergesTo_singleton_of_tendstoLocallyUniformlyOn hf hf0
        (hlim.congr_right hgc)
    · intro hker
      exact (tendstoLocallyUniformlyOn_of_kernelConvergesTo_singleton hf hf0 hker).congr_right
        hgc.symm
  · constructor
    · exact kernelConvergesTo_of_tendstoLocallyUniformlyOn hf hg hg0
    · intro hker
      exact QuantumZipper.CA.Kernel.caratheodory_kernel_theorem (fun n => (hf n).1)
        (fun n => (hf n).2.injOn) (fun n => (hf n).2.image_eq) hf0 hf' hg.1 hg.2.injOn
        hg.2.image_eq hg0 hg' hker

end KernelTheorem

/-! ### Monotone sequences of domains -/

section Monotone

variable {G : ℕ → Set ℂ} {w₀ : ℂ}

/-- **Increasing domains converge to their union** with respect to any point of the first one
(Pommerenke 1992, §1.4, p. 13). -/
theorem kernelConvergesTo_iUnion_of_monotone (hmono : Monotone G) (hGo : ∀ n, IsOpen (G n))
    (hGc : ∀ n, IsPreconnected (G n)) (hw₀ : w₀ ∈ G 0) (hne : (⋃ n, G n) ≠ univ) :
    KernelConvergesTo G (⋃ n, G n) w₀ := by
  have hDo : IsOpen (⋃ n, G n) := isOpen_iUnion hGo
  have hw₀n : ∀ n, w₀ ∈ G n := fun n => hmono (Nat.zero_le n) hw₀
  have hGne : ∀ n, G n ≠ univ := fun n h => hne (eq_univ_of_univ_subset (h ▸ subset_iUnion G n))
  refine ⟨Or.inr ⟨hDo, ⟨⟨w₀, mem_iUnion.2 ⟨0, hw₀⟩⟩,
    isPreconnected_iUnion ⟨w₀, mem_iInter.2 hw₀n⟩ hGc⟩, hne, mem_iUnion.2 ⟨0, hw₀⟩, ?_⟩, ?_⟩
  · intro w hw
    obtain ⟨m, hm⟩ := mem_iUnion.1 hw
    exact ⟨G m, (hGo m).mem_nhds hm, eventually_atTop.2 ⟨m, fun n hn => hmono hn⟩⟩
  · intro w hw
    have hwD : w ∉ ⋃ n, G n := notMem_of_mem_frontier hDo hw
    have hfne : ∀ n, (frontier (G n)).Nonempty := fun n =>
      frontier_nonempty_of_isOpen ⟨w₀, hw₀n n⟩ (hGne n)
    refine exists_tendsto_frontier hfne fun ε hε => ?_
    obtain ⟨x, hxD, hxw⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hw) ε hε
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxD
    filter_upwards [eventually_ge_atTop m] with n hn
    exact ball_inter_frontier_nonempty (hGo n) (mem_ball'.2 hxw) (hmono hn hm) (mem_ball_self hε)
      fun h => hwD (mem_iUnion.2 ⟨n, h⟩)

/-- A point of the closure of a component of an open set `I ⊆ ℂ` that lies in `I` lies in the
component. -/
theorem mem_connectedComponentIn_of_mem_closure {I : Set ℂ} (hI : IsOpen I) {w₀ w : ℂ}
    (hw : w ∈ closure (connectedComponentIn I w₀)) (hwI : w ∈ I) :
    w ∈ connectedComponentIn I w₀ := by
  obtain ⟨r, hr, hrI⟩ := Metric.isOpen_iff.1 hI w hwI
  obtain ⟨x, hxD, hxw⟩ := Metric.mem_closure_iff.1 hw r hr
  have hsub : ball w r ⊆ connectedComponentIn I x :=
    (convex_ball w r).isPreconnected.subset_connectedComponentIn (mem_ball'.2 hxw) hrI
  rw [← connectedComponentIn_eq hxD] at hsub
  exact hsub (mem_ball_self hr)

/-- **Decreasing domains converge to the component of the interior of their intersection that
contains `w₀`** (Pommerenke 1992, §1.4, p. 13), when `w₀` is an interior point of the
intersection. -/
theorem kernelConvergesTo_connectedComponentIn_of_antitone (hanti : Antitone G)
    (hGo : ∀ n, IsOpen (G n)) (hne : G 0 ≠ univ) (hw₀ : w₀ ∈ interior (⋂ n, G n)) :
    KernelConvergesTo G (connectedComponentIn (interior (⋂ n, G n)) w₀) w₀ := by
  set I := interior (⋂ n, G n) with hIdef
  set D := connectedComponentIn I w₀ with hDdef
  have hDo : IsOpen D := isOpen_interior.connectedComponentIn
  have hDI : D ⊆ I := connectedComponentIn_subset _ _
  have hIG : ∀ n, I ⊆ G n := fun n => interior_subset.trans (iInter_subset _ n)
  have hGne : ∀ n, G n ≠ univ := fun n h =>
    hne (eq_univ_of_univ_subset (h ▸ hanti (Nat.zero_le n)))
  refine ⟨Or.inr ⟨hDo, isConnected_connectedComponentIn_iff.2 hw₀, ?_,
    mem_connectedComponentIn hw₀, ?_⟩, ?_⟩
  · intro h
    exact hne (eq_univ_of_univ_subset (h ▸ hDI.trans (hIG 0)))
  · intro w hw
    exact ⟨D, hDo.mem_nhds hw, Eventually.of_forall fun n => hDI.trans (hIG n)⟩
  · intro w hw
    have hwD : w ∉ D := notMem_of_mem_frontier hDo hw
    have hwI : w ∉ I := fun hwI =>
      hwD (mem_connectedComponentIn_of_mem_closure isOpen_interior (frontier_subset_closure hw) hwI)
    have hfne : ∀ n, (frontier (G n)).Nonempty := fun n =>
      frontier_nonempty_of_isOpen ⟨w₀, hIG n hw₀⟩ (hGne n)
    refine exists_tendsto_frontier hfne fun ε hε => ?_
    obtain ⟨x, hxD, hxw⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hw) ε hε
    have hN : ∃ N, ¬ ball w ε ⊆ G N := by
      by_contra h
      push Not at h
      exact hwI (mem_interior.2 ⟨ball w ε, subset_iInter h, isOpen_ball, mem_ball_self hε⟩)
    obtain ⟨N, hN⟩ := hN
    obtain ⟨y, hy, hyG⟩ := not_subset.1 hN
    filter_upwards [eventually_ge_atTop N] with n hn
    exact ball_inter_frontier_nonempty (hGo n) (mem_ball'.2 hxw) (hIG n (hDI hxD)) hy
      fun h => hyG (hanti hn h)

/-- **Decreasing domains with `w₀` not interior to their intersection converge to `{w₀}`**
(Pommerenke 1992, §1.4, p. 13: the kernel is then the degenerate `{w₀}`). -/
theorem kernelConvergesTo_singleton_of_antitone (hanti : Antitone G) (hGo : ∀ n, IsOpen (G n))
    (hne : G 0 ≠ univ) (hw₀ : ∀ n, w₀ ∈ G n) (hint : w₀ ∉ interior (⋂ n, G n)) :
    KernelConvergesTo G {w₀} w₀ := by
  have hGne : ∀ n, G n ≠ univ := fun n h =>
    hne (eq_univ_of_univ_subset (h ▸ hanti (Nat.zero_le n)))
  refine ⟨Or.inl rfl, ?_⟩
  intro w hw
  rw [frontier_singleton_complex, mem_singleton_iff] at hw
  subst hw
  have hfne : ∀ n, (frontier (G n)).Nonempty := fun n =>
    frontier_nonempty_of_isOpen ⟨w, hw₀ n⟩ (hGne n)
  refine exists_tendsto_frontier hfne fun ε hε => ?_
  have hN : ∃ N, ¬ ball w ε ⊆ G N := by
    by_contra h
    push Not at h
    exact hint (mem_interior.2 ⟨ball w ε, subset_iInter h, isOpen_ball, mem_ball_self hε⟩)
  obtain ⟨N, hN⟩ := hN
  obtain ⟨y, hy, hyG⟩ := not_subset.1 hN
  filter_upwards [eventually_ge_atTop N] with n hn
  exact ball_inter_frontier_nonempty (hGo n) (mem_ball_self hε) (hw₀ n) hy
    fun h => hyG (hanti hn h)

end Monotone

/-! ### Continuity of the conformal radius

For a conformal map `f : 𝔻 → G` with `f 0 = w₀` and `f'(0) > 0`, the conformal radius of `G`
viewed from `w₀` is `|f'(0)| = f'(0)` (specification p. 74, after (3.15)). -/

section ConformalRadius

variable {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ} {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}

/-- **The conformal radius is continuous along kernel convergence**: under the hypotheses of the
kernel theorem, `f n'(0) → g'(0)`. -/
theorem tendsto_deriv_of_kernelConvergesTo
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0)
    (hg : IsConformalBijection g (ball 0 1) D) (hg0 : g 0 = w₀) (hg' : 0 < deriv g 0)
    (hker : KernelConvergesTo G D w₀) :
    Tendsto (fun n => deriv (f n) 0) atTop (𝓝 (deriv g 0)) :=
  tendsto_deriv_of_tendstoLocallyUniformlyOn (fun n => (hf n).1)
    ((kernel_convergence_iff hf hf0 hf' (Or.inr ⟨hg, hg0, hg'⟩)).2 hker) (mem_ball_self one_pos)

/-- **The conformal radius tends to `0` along convergence to a degenerate kernel `{w₀}`.** -/
theorem tendsto_deriv_zero_of_kernelConvergesTo_singleton
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hker : KernelConvergesTo G {w₀} w₀) :
    Tendsto (fun n => deriv (f n) 0) atTop (𝓝 0) := by
  have h := tendsto_deriv_of_tendstoLocallyUniformlyOn (fun n => (hf n).1)
    (tendstoLocallyUniformlyOn_of_kernelConvergesTo_singleton hf hf0 hker)
    (mem_ball_self one_pos)
  rwa [deriv_const] at h

/-- **Continuity of the conformal radius along decreasing domains** (specification p. 179 and
p. 198: "continuity of the conformal radius at every surviving point"). Let `G n` be decreasing
open proper subsets of `ℂ` and `w₀` an interior point of their intersection; let `D` be the
component of that interior containing `w₀`. Normalized conformal maps `f n : 𝔻 → G n`
(`f n 0 = w₀`, `f n'(0) > 0`) converge locally uniformly to the normalized map `g : 𝔻 → D`, and
the conformal radii converge: `f n'(0) → g'(0)`. -/
theorem tendsto_deriv_of_antitone (hanti : Antitone G) (hGo : ∀ n, IsOpen (G n))
    (hne : G 0 ≠ univ) (hw₀ : w₀ ∈ interior (⋂ n, G n))
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0)
    (hg : IsConformalBijection g (ball 0 1) (connectedComponentIn (interior (⋂ n, G n)) w₀))
    (hg0 : g 0 = w₀) (hg' : 0 < deriv g 0) :
    TendstoLocallyUniformlyOn f g atTop (ball 0 1) ∧
      Tendsto (fun n => deriv (f n) 0) atTop (𝓝 (deriv g 0)) := by
  have hker := kernelConvergesTo_connectedComponentIn_of_antitone hanti hGo hne hw₀
  exact ⟨(kernel_convergence_iff hf hf0 hf' (Or.inr ⟨hg, hg0, hg'⟩)).2 hker,
    tendsto_deriv_of_kernelConvergesTo hf hf0 hf' hg hg0 hg' hker⟩

/-- **The conformal radius tends to `0` along decreasing domains** when `w₀` is not an interior
point of their intersection. -/
theorem tendsto_deriv_zero_of_antitone (hanti : Antitone G) (hGo : ∀ n, IsOpen (G n))
    (hne : G 0 ≠ univ) (hint : w₀ ∉ interior (⋂ n, G n))
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀) :
    TendstoLocallyUniformlyOn f (fun _ => w₀) atTop (ball 0 1) ∧
      Tendsto (fun n => deriv (f n) 0) atTop (𝓝 0) := by
  have hw₀ : ∀ n, w₀ ∈ G n := fun n => hf0 n ▸ (hf n).2.mapsTo (mem_ball_self one_pos)
  have hker := kernelConvergesTo_singleton_of_antitone hanti hGo hne hw₀ hint
  exact ⟨tendstoLocallyUniformlyOn_of_kernelConvergesTo_singleton hf hf0 hker,
    tendsto_deriv_zero_of_kernelConvergesTo_singleton hf hf0 hker⟩

/-- **Continuity of the conformal radius along increasing domains**: for increasing open
connected `G n` with proper union `D` and `w₀ ∈ G 0`, the normalized maps `f n : 𝔻 → G n`
converge locally uniformly to the normalized map `g : 𝔻 → D`, and `f n'(0) → g'(0)`. -/
theorem tendsto_deriv_of_monotone (hmono : Monotone G) (hGo : ∀ n, IsOpen (G n))
    (hGc : ∀ n, IsPreconnected (G n)) (hw₀ : w₀ ∈ G 0) (hne : (⋃ n, G n) ≠ univ)
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0)
    (hg : IsConformalBijection g (ball 0 1) (⋃ n, G n)) (hg0 : g 0 = w₀) (hg' : 0 < deriv g 0) :
    TendstoLocallyUniformlyOn f g atTop (ball 0 1) ∧
      Tendsto (fun n => deriv (f n) 0) atTop (𝓝 (deriv g 0)) := by
  have hker := kernelConvergesTo_iUnion_of_monotone hmono hGo hGc hw₀ hne
  exact ⟨(kernel_convergence_iff hf hf0 hf' (Or.inr ⟨hg, hg0, hg'⟩)).2 hker,
    tendsto_deriv_of_kernelConvergesTo hf hf0 hf' hg hg0 hg' hker⟩

open QuantumZipper.CA QuantumZipper.CA.Kernel in
/-- **The non-degenerate kernel of normalized conformal images of `𝔻` is itself one**
(Pommerenke 1992, Theorem 1.8, proof of (b): a subsequential limit of the `f n` maps `𝔻`
conformally onto the kernel). If `f n : 𝔻 → G n` are conformal with `f n 0 = w₀`, `f n'(0) > 0`
and `G n → D ≠ {w₀}` with respect to `w₀`, then some conformal `g : 𝔻 → D` has `g 0 = w₀` and
`g'(0) > 0`; in particular the kernel theorem applies to `D`. The proof is QuantumZipper's
`exists_subseq_tendsto_of_kernel` (Koebe bounds on `f n'(0)`, growth theorem, Montel, Hurwitz,
and the two image inclusions), with the given limit map removed. -/
theorem exists_isConformalBijection_of_kernelConvergesTo {G : ℕ → Set ℂ} {D : Set ℂ} {w₀ : ℂ}
    {f : ℕ → ℂ → ℂ} (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n))
    (hf0 : ∀ n, f n 0 = w₀) (hf' : ∀ n, 0 < deriv (f n) 0) (hker : KernelConvergesTo G D w₀)
    (hDsing : D ≠ {w₀}) :
    ∃ g : ℂ → ℂ, IsConformalBijection g (ball 0 1) D ∧ g 0 = w₀ ∧ 0 < deriv g 0 := by
  have hfd : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1) := fun n => (hf n).1
  have hfi : ∀ n, InjOn (f n) (ball 0 1) := fun n => (hf n).2.injOn
  have hfim : ∀ n, f n '' ball 0 1 = G n := fun n => (hf n).2.image_eq
  have h0B : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  obtain ⟨hi', hii⟩ := hker
  obtain ⟨hDo, hDc, hDne, hw₀D, hi⟩ : IsOpen D ∧ IsConnected D ∧ D ≠ univ ∧ w₀ ∈ D ∧
      ∀ w ∈ D, ∃ U ∈ 𝓝 w, ∀ᶠ n in atTop, U ⊆ G n := by
    rcases hi' with h | h
    · exact absurd h hDsing
    · exact h
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
  have hhi : InjOn h (ball 0 1) := hurwitz_injOn isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hFd (fun k => hfi _) hlim' hnc
  -- the image of the limit is `D`
  have hsub1 : h '' ball 0 1 ⊆ D := image_subset_of_tendsto hFd (fun k => hfi _)
    (fun k => hfim _) hlim' hnc hDo (hh0 ▸ hw₀D) fun w hw => by
      obtain ⟨u, hu, hut⟩ := hii w hw
      exact ⟨u ∘ ψ, fun n => hu (ψ n), hut.comp hψ.tendsto_atTop⟩
  have hsub2 : D ⊆ h '' ball 0 1 := subset_image_of_tendsto hFd (fun k => hfi _)
    (fun k => hfim _) hlim' hhi hDc.isPreconnected (hh0 ▸ hw₀D) fun w hw => by
      obtain ⟨U, hU, hev⟩ := hi w hw
      exact ⟨U, hU, hψ.tendsto_atTop.eventually hev⟩
  have hb' := hhi.bijOn_image
  rw [subset_antisymm hsub1 hsub2] at hb'
  exact ⟨h, ⟨hhd, hb'⟩, hh0, hpos⟩

/-- **Continuity of the conformal radius along decreasing domains, with the limit map
constructed**: under the hypotheses of `tendsto_deriv_of_antitone` without a given limit map, the
component `D` of the interior of the intersection containing `w₀` is a normalized conformal
image `g(𝔻)`, `f n → g` locally uniformly and `f n'(0) → g'(0)`. -/
theorem exists_tendsto_deriv_of_antitone {G : ℕ → Set ℂ} {w₀ : ℂ} {f : ℕ → ℂ → ℂ}
    (hanti : Antitone G) (hGo : ∀ n, IsOpen (G n)) (hne : G 0 ≠ univ)
    (hw₀ : w₀ ∈ interior (⋂ n, G n))
    (hf : ∀ n, IsConformalBijection (f n) (ball 0 1) (G n)) (hf0 : ∀ n, f n 0 = w₀)
    (hf' : ∀ n, 0 < deriv (f n) 0) :
    ∃ g : ℂ → ℂ, (IsConformalBijection g (ball 0 1)
        (connectedComponentIn (interior (⋂ n, G n)) w₀) ∧ g 0 = w₀ ∧ 0 < deriv g 0) ∧
      TendstoLocallyUniformlyOn f g atTop (ball 0 1) ∧
      Tendsto (fun n => deriv (f n) 0) atTop (𝓝 (deriv g 0)) := by
  have hker := kernelConvergesTo_connectedComponentIn_of_antitone hanti hGo hne hw₀
  have hsing : connectedComponentIn (interior (⋂ n, G n)) w₀ ≠ {w₀} := fun h =>
    not_isOpen_singleton w₀ (h ▸ isOpen_interior.connectedComponentIn)
  obtain ⟨g, hg, hg0, hg'⟩ :=
    exists_isConformalBijection_of_kernelConvergesTo hf hf0 hf' hker hsing
  exact ⟨g, ⟨hg, hg0, hg'⟩, tendsto_deriv_of_antitone hanti hGo hne hw₀ hf hf0 hf' hg hg0 hg'⟩

end ConformalRadius

/-! ### Filling the holes of a planar set -/

section FillHoles

variable {V : Set ℂ} {R : ℝ}

/-- The **hole filling** of `V ⊆ ℂ`: the points whose connected component in `ℂ \ V` is bounded.
It contains `V` (whose points have empty component) and every bounded component of `ℂ \ V`. -/
def fillHoles (V : Set ℂ) : Set ℂ := {z | Bornology.IsBounded (connectedComponentIn Vᶜ z)}

theorem mem_fillHoles {z : ℂ} :
    z ∈ fillHoles V ↔ Bornology.IsBounded (connectedComponentIn Vᶜ z) := Iff.rfl

theorem subset_fillHoles (V : Set ℂ) : V ⊆ fillHoles V := fun z hz => by
  have hz' : z ∉ Vᶜ := fun h => h hz
  show Bornology.IsBounded (connectedComponentIn Vᶜ z)
  rw [connectedComponentIn_eq_empty hz']
  exact Bornology.isBounded_empty

theorem fillHoles_mono {W : Set ℂ} (h : V ⊆ W) : fillHoles V ⊆ fillHoles W := fun z hz =>
  (mem_fillHoles.1 hz).subset (connectedComponentIn_mono z (compl_subset_compl.2 h))

/-- Filling the holes of a subset of a simply connected open set stays inside it. -/
theorem fillHoles_subset_of_isSimplyConnected {U : Set ℂ} (hUo : IsOpen U)
    (hsc : IsSimplyConnected U) (hVU : V ⊆ U) : fillHoles V ⊆ U := by
  intro z hz
  by_contra hzU
  exact not_isBounded_connectedComponentIn_compl_of_isSimplyConnected hUo hsc hzU
    ((mem_fillHoles.1 hz).subset (connectedComponentIn_mono z (compl_subset_compl.2 hVU)))

/-- The exterior `{R < |z|}` of a disc is unbounded. -/
theorem not_isBounded_setOf_lt_norm (R : ℝ) : ¬ Bornology.IsBounded {z : ℂ | R < ‖z‖} := by
  rw [isBounded_iff_forall_norm_le]
  rintro ⟨C, hC⟩
  have ht : 0 < |R| + |C| + 1 := by positivity
  have hn : ‖((|R| + |C| + 1 : ℝ) : ℂ)‖ = |R| + |C| + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have h := hC ((|R| + |C| + 1 : ℝ) : ℂ)
    (show R < ‖((|R| + |C| + 1 : ℝ) : ℂ)‖ by rw [hn]; linarith [le_abs_self R, abs_nonneg C])
  rw [hn] at h
  linarith [le_abs_self C, abs_nonneg R]

/-- The exterior of a disc containing `V` lies in one component of `ℂ \ V`. -/
theorem setOf_lt_norm_subset_connectedComponentIn (hV : V ⊆ closedBall 0 R) {z : ℂ}
    (hz : R < ‖z‖) : {w : ℂ | R < ‖w‖} ⊆ connectedComponentIn Vᶜ z :=
  (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R).subset_connectedComponentIn hz
    fun w hw hwV => by
      have h := hV hwV
      rw [mem_closedBall, dist_zero_right] at h
      exact absurd hw (not_lt.2 h)

/-- The hole filling of a set contained in a closed disc stays in the disc. -/
theorem fillHoles_subset_closedBall (hV : V ⊆ closedBall 0 R) : fillHoles V ⊆ closedBall 0 R := by
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  exact not_isBounded_setOf_lt_norm R
    ((mem_fillHoles.1 hz).subset (setOf_lt_norm_subset_connectedComponentIn hV h))

/-- A component of a closed subset of `ℂ` is closed. -/
theorem isClosed_connectedComponentIn_of_isClosed {F : Set ℂ} (hF : IsClosed F) (x : ℂ) :
    IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · refine isClosed_of_closure_subset ?_
    exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure (mem_connectedComponentIn hx))
      (closure_minimal (connectedComponentIn_subset _ _) hF)
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-- For `V` in a closed disc of radius `R ≥ 0`, the complement of the hole filling is the
(unbounded) component of `ℂ \ V` containing the far point `R + 1`. -/
theorem compl_fillHoles_eq (hV : V ⊆ closedBall 0 R) (hR : 0 ≤ R) :
    (fillHoles V)ᶜ = connectedComponentIn Vᶜ ((R + 1 : ℝ) : ℂ) := by
  set p : ℂ := ((R + 1 : ℝ) : ℂ) with hpdef
  have hp : R < ‖p‖ := by
    rw [hpdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hE := setOf_lt_norm_subset_connectedComponentIn hV hp
  ext z
  rw [mem_compl_iff, mem_fillHoles]
  constructor
  · intro hz
    have hy : ∃ y ∈ connectedComponentIn Vᶜ z, R < ‖y‖ := by
      by_contra h
      push Not at h
      exact hz ((isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun y hy => by
        rw [mem_closedBall, dist_zero_right]; exact h y hy)
    obtain ⟨y, hyz, hyR⟩ := hy
    have hzV : z ∈ Vᶜ := by
      by_contra hzV
      rw [connectedComponentIn_eq_empty hzV] at hyz
      exact hyz
    have hyp : y ∈ connectedComponentIn Vᶜ p := hE hyR
    rw [connectedComponentIn_eq hyp, ← connectedComponentIn_eq hyz]
    exact mem_connectedComponentIn hzV
  · intro hz hb
    rw [connectedComponentIn_eq hz] at hE
    exact not_isBounded_setOf_lt_norm R (hb.subset hE)

/-- The hole filling of an open set in a closed disc is open. -/
theorem isOpen_fillHoles (hVo : IsOpen V) (hV : V ⊆ closedBall 0 R) (hR : 0 ≤ R) :
    IsOpen (fillHoles V) := by
  rw [← isClosed_compl_iff, compl_fillHoles_eq hV hR]
  exact isClosed_connectedComponentIn_of_isClosed hVo.isClosed_compl _

/-- The hole filling of a preconnected open set is preconnected: every bounded component of
`ℂ \ V` meets the closure of `V`. -/
theorem isPreconnected_fillHoles (hVo : IsOpen V) (hVc : IsPreconnected V) {a : ℂ}
    (ha : a ∈ V) : IsPreconnected (fillHoles V) := by
  refine isPreconnected_of_forall a fun y hy => ?_
  by_cases hyV : y ∈ V
  · exact ⟨V, subset_fillHoles V, ha, hyV, hVc⟩
  set C := connectedComponentIn Vᶜ y with hCdef
  have hyC : y ∈ C := mem_connectedComponentIn hyV
  have hCsub : C ⊆ fillHoles V := fun c hc => by
    show Bornology.IsBounded (connectedComponentIn Vᶜ c)
    rw [← connectedComponentIn_eq hc]
    exact hy
  have hCcl : IsClosed C := isClosed_connectedComponentIn_of_isClosed hVo.isClosed_compl y
  have hCne : C ≠ univ := fun h => not_isBounded_setOf_lt_norm 0
    ((show Bornology.IsBounded C from hy).subset (h ▸ subset_univ _))
  obtain ⟨p, hp⟩ := nonempty_frontier_iff.2 ⟨⟨y, hyC⟩, hCne⟩
  have hpC : p ∈ C := hCcl.frontier_subset hp
  have hpV : p ∈ closure V := by
    by_contra hpV
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpV
    have hball : ball p r ⊆ C := by
      show ball p r ⊆ connectedComponentIn Vᶜ y
      rw [connectedComponentIn_eq hpC]
      exact (convex_ball p r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr)
        fun w hw hwV => hrsub hw (subset_closure hwV)
    exact hp.2 (mem_interior.2 ⟨ball p r, hball, isOpen_ball, mem_ball_self hr⟩)
  refine ⟨V ∪ C, union_subset (subset_fillHoles V) hCsub, Or.inl ha, Or.inr hyC, ?_⟩
  have h1 : IsPreconnected (insert p V) :=
    hVc.subset_closure (subset_insert _ _) (insert_subset hpV subset_closure)
  have h2 := IsPreconnected.union p (mem_insert _ _) hpC h1 isPreconnected_connectedComponentIn
  rwa [insert_union, insert_eq_of_mem (show p ∈ V ∪ C from Or.inr hpC)] at h2

/-- The hole filling of a connected open set in a closed disc is simply connected: its
complement is a single unbounded component. -/
theorem isSimplyConnected_fillHoles (hVo : IsOpen V) (hVc : IsPreconnected V) {a : ℂ}
    (ha : a ∈ V) (hV : V ⊆ closedBall 0 R) (hR : 0 ≤ R) : IsSimplyConnected (fillHoles V) := by
  have hp : R < ‖((R + 1 : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  refine isSimplyConnected_of_forall_not_isBounded (isOpen_fillHoles hVo hV hR)
    ⟨⟨a, subset_fillHoles V ha⟩, isPreconnected_fillHoles hVo hVc ha⟩ fun b hb hbdd => ?_
  have hb' : b ∈ connectedComponentIn Vᶜ ((R + 1 : ℝ) : ℂ) := by
    rw [← compl_fillHoles_eq hV hR]; exact hb
  rw [compl_fillHoles_eq hV hR] at hbdd
  have hsub : connectedComponentIn Vᶜ ((R + 1 : ℝ) : ℂ) ⊆
      connectedComponentIn (connectedComponentIn Vᶜ ((R + 1 : ℝ) : ℂ)) b :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn hb' subset_rfl
  exact not_isBounded_setOf_lt_norm R
    ((hbdd.subset hsub).subset (setOf_lt_norm_subset_connectedComponentIn hV hp))

end FillHoles

/-! ### Normalized maps from the disc -/

/-- **Riemann mapping theorem with both normalizations**: the normalized chart `φ : U → 𝔻`
(`φ a = 0`, `φ'(a) > 0`) of `exists_isConformalBijection_ball`, and its inverse `invFunOn φ U`,
a conformal bijection `𝔻 → U` with value `a` and positive derivative at `0` (QuantumZipper's
`modelPullback_props`). -/
theorem exists_isConformalBijection_ball_and_inv {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsConnected U) (hsc : IsSimplyConnected U) (hne : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ φ : ℂ → ℂ, (IsConformalBijection φ U (ball 0 1) ∧ φ a = 0 ∧ 0 < deriv φ a) ∧
      IsConformalBijection (invFunOn φ U) (ball 0 1) U ∧ invFunOn φ U 0 = a ∧
      0 < deriv (invFunOn φ U) 0 := by
  obtain ⟨φ, hφ, hφ0, hre, him⟩ := exists_isConformalBijection_ball hUo hUc hsc hne ha
  have hφ' : 0 < deriv φ a := Complex.pos_iff.2 ⟨hre, him.symm⟩
  obtain ⟨hd, hi, him', h0, h'⟩ := QuantumZipper.CA.Kernel.modelPullback_props (S := id)
    differentiableOn_id (injOn_id _) (image_id _) rfl (by simp)
    hUo hφ.1 hφ.2 ha hφ0 hφ'
  have hb := hi.bijOn_image
  rw [him'] at hb
  exact ⟨φ, ⟨hφ, hφ0, hφ'⟩, ⟨hd, hb⟩, h0, h'⟩

/-- **Riemann mapping theorem, disc-to-domain normalization**: an open connected simply connected
`U ≠ ℂ` and `a ∈ U` have a conformal bijection `f : 𝔻 → U` with `f 0 = a` and `f'(0) > 0`. -/
theorem exists_isConformalBijection_ball_onto {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hsc : IsSimplyConnected U) (hne : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f : ℂ → ℂ, IsConformalBijection f (ball 0 1) U ∧ f 0 = a ∧ 0 < deriv f 0 := by
  obtain ⟨φ, -, hf⟩ := exists_isConformalBijection_ball_and_inv hUo hUc hsc hne ha
  exact ⟨_, hf⟩

/-! ### Rational discs -/

section RatDisc

/-- An enumeration of the triples `(Re c, Im c, r) ∈ ℚ³` (centre and radius of a rational
disc). -/
def ratDiscData (k : ℕ) : (ℚ × ℚ) × ℚ := Denumerable.ofNat ((ℚ × ℚ) × ℚ) k

/-- The centre of the `k`-th rational disc. -/
def ratDiscCenter (k : ℕ) : ℂ := ⟨((ratDiscData k).1.1 : ℝ), ((ratDiscData k).1.2 : ℝ)⟩

/-- The radius of the `k`-th rational disc. -/
def ratDiscRadius (k : ℕ) : ℝ := ((ratDiscData k).2 : ℝ)

theorem ratDiscData_surjective : Function.Surjective ratDiscData := fun t =>
  ⟨_, Denumerable.ofNat_encode t⟩

/-- Every point of an open set lies in a rational disc whose closure lies in the set. -/
theorem exists_ratDisc {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∃ k, x ∈ ball (ratDiscCenter k) (ratDiscRadius k) ∧
      closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨ρ, hρ0, hρε⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by positivity)
  obtain ⟨q1, hq1a, hq1b⟩ := exists_rat_btwn (show x.re - ρ / 2 < x.re by linarith)
  obtain ⟨q2, hq2a, hq2b⟩ := exists_rat_btwn (show x.im - ρ / 2 < x.im by linarith)
  obtain ⟨k, hdata⟩ := ratDiscData_surjective ((q1, q2), ρ)
  have hc : ratDiscCenter k = ⟨(q1 : ℝ), (q2 : ℝ)⟩ := by
    rw [ratDiscCenter, hdata]
  have hr : ratDiscRadius k = (ρ : ℝ) := by
    rw [ratDiscRadius, hdata]
  have hdist : dist x ⟨(q1 : ℝ), (q2 : ℝ)⟩ < ρ := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    have h1 : |(x - ⟨(q1 : ℝ), (q2 : ℝ)⟩ : ℂ).re| < ρ / 2 := by
      rw [Complex.sub_re]; exact abs_sub_lt_iff.2 ⟨by simp; linarith, by simp; linarith⟩
    have h2 : |(x - ⟨(q1 : ℝ), (q2 : ℝ)⟩ : ℂ).im| < ρ / 2 := by
      rw [Complex.sub_im]; exact abs_sub_lt_iff.2 ⟨by simp; linarith, by simp; linarith⟩
    linarith
  refine ⟨k, ?_, ?_⟩
  · rw [hc, hr, mem_ball]; exact hdist
  · rw [hc, hr]
    intro y hy
    apply hεU
    rw [mem_ball]
    have := dist_triangle y ⟨(q1 : ℝ), (q2 : ℝ)⟩ x
    rw [mem_closedBall] at hy
    linarith [dist_comm x (⟨(q1 : ℝ), (q2 : ℝ)⟩ : ℂ)]

/-- The union of the open rational discs with index in `S`. -/
def ratDiscUnion (S : Finset ℕ) : Set ℂ := ⋃ k ∈ S, ball (ratDiscCenter k) (ratDiscRadius k)

theorem ratDiscUnion_mono {S T : Finset ℕ} (h : S ⊆ T) : ratDiscUnion S ⊆ ratDiscUnion T :=
  biUnion_subset_biUnion_left (Finset.coe_subset.2 h)

theorem isOpen_ratDiscUnion (S : Finset ℕ) : IsOpen (ratDiscUnion S) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem exists_ratDiscUnion_subset_closedBall (S : Finset ℕ) :
    ∃ R, 0 ≤ R ∧ ratDiscUnion S ⊆ closedBall 0 R := by
  have hb : Bornology.IsBounded (ratDiscUnion S) :=
    (Bornology.isBounded_biUnion_finset S).2 fun _ _ => isBounded_ball
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  exact ⟨max R 0, le_max_right _ _, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- The indices `k < n` of the rational discs whose closures lie in `U`. -/
def ratDiscIndices (U : Set ℂ) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range n).filter fun k => closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U

theorem mem_ratDiscIndices {U : Set ℂ} {n k : ℕ} :
    k ∈ ratDiscIndices U n ↔ k < n ∧ closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U := by
  classical
  simp [ratDiscIndices]

theorem ratDiscIndices_mono {U : Set ℂ} {n m : ℕ} (h : n ≤ m) :
    ratDiscIndices U n ⊆ ratDiscIndices U m := fun k hk => by
  rw [mem_ratDiscIndices] at hk ⊢
  exact ⟨hk.1.trans_le h, hk.2⟩

theorem ratDiscUnion_ratDiscIndices_subset (U : Set ℂ) (n : ℕ) :
    ratDiscUnion (ratDiscIndices U n) ⊆ U := by
  intro z hz
  obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.1 hz
  exact (mem_ratDiscIndices.1 hk).2 (ball_subset_closedBall hzk)

/-- Every point `w` of an open connected `U` is, for large `n`, in the component of `a ∈ U` of
the union of the first rational discs whose closures lie in `U`: cover a path from `a` to `w`. -/
theorem exists_mem_connectedComponentIn_ratDiscUnion {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsConnected U) {a w : ℂ} (ha : a ∈ U) (hw : w ∈ U) :
    ∃ n, w ∈ connectedComponentIn (ratDiscUnion (ratDiscIndices U n)) a := by
  have hpc : IsPathConnected U := (hUo.isConnected_iff_isPathConnected).1 hUc
  have hj := hpc.joinedIn a ha w hw
  set γ := hj.somePath with hγ
  have hKc : IsCompact (range γ) := isCompact_range γ.continuous
  have hKU : range γ ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hj.somePath_mem t
  have hex : ∀ x ∈ U, ∃ k, x ∈ ball (ratDiscCenter k) (ratDiscRadius k) ∧
      closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U := fun x hx => exists_ratDisc hUo hx
  choose! kx hkx using hex
  obtain ⟨T, hT⟩ := hKc.elim_finite_subcover
    (fun x : range γ => ball (ratDiscCenter (kx x)) (ratDiscRadius (kx x)))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hkx x (hKU hx)).1⟩)
  refine ⟨(T.sup fun x => kx x) + 1, ?_⟩
  have hKsub : range γ ⊆ ratDiscUnion (ratDiscIndices U ((T.sup fun x => kx x) + 1)) := by
    intro y hy
    obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hT hy)
    refine mem_iUnion₂.2 ⟨kx x, mem_ratDiscIndices.2 ⟨?_, (hkx x (hKU x.2)).2⟩, hyx⟩
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun x : range γ => kx x) hxT)
  have hKconn : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  exact hKconn.subset_connectedComponentIn ⟨0, γ.source⟩ hKsub ⟨1, γ.target⟩

end RatDisc

/-! ### Measurable normalized Riemann maps -/

section Measurable

/-- The approximating domain attached to a finite set `S` of rational discs and a point `a`: the
hole filling of the component of `a` in the union of the discs. -/
def ratApprox (S : Finset ℕ) (a : ℂ) : Set ℂ :=
  fillHoles (connectedComponentIn (ratDiscUnion S) a)

/-- If `a` lies in the union of the discs, the approximating domain is an open, connected,
simply connected, proper subset of `ℂ` containing `a`. -/
theorem ratApprox_props {S : Finset ℕ} {a : ℂ} (ha : a ∈ ratDiscUnion S) :
    IsOpen (ratApprox S a) ∧ IsConnected (ratApprox S a) ∧ IsSimplyConnected (ratApprox S a) ∧
      ratApprox S a ≠ univ ∧ a ∈ ratApprox S a := by
  obtain ⟨R, hR, hSR⟩ := exists_ratDiscUnion_subset_closedBall S
  set V := connectedComponentIn (ratDiscUnion S) a with hV
  have hVo : IsOpen V := (isOpen_ratDiscUnion S).connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have haV : a ∈ V := mem_connectedComponentIn ha
  have hVR : V ⊆ closedBall 0 R := (connectedComponentIn_subset _ _).trans hSR
  refine ⟨isOpen_fillHoles hVo hVR hR, ⟨⟨a, subset_fillHoles V haV⟩,
    isPreconnected_fillHoles hVo hVc haV⟩, isSimplyConnected_fillHoles hVo hVc haV hVR hR,
    fun h => not_isBounded_setOf_lt_norm R ?_, subset_fillHoles V haV⟩
  exact (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
    ((subset_univ _).trans (h ▸ fillHoles_subset_closedBall hVR))

/-- The approximating domains of `U` increase. -/
theorem ratApprox_mono {U : Set ℂ} (a : ℂ) {n m : ℕ} (h : n ≤ m) :
    ratApprox (ratDiscIndices U n) a ⊆ ratApprox (ratDiscIndices U m) a :=
  fillHoles_mono (connectedComponentIn_mono a (ratDiscUnion_mono (ratDiscIndices_mono h)))

/-- The approximating domains of a simply connected open `U` lie in `U`. -/
theorem ratApprox_subset {U : Set ℂ} (hUo : IsOpen U) (hsc : IsSimplyConnected U) (a : ℂ)
    (n : ℕ) : ratApprox (ratDiscIndices U n) a ⊆ U :=
  fillHoles_subset_of_isSimplyConnected hUo hsc
    ((connectedComponentIn_subset _ _).trans (ratDiscUnion_ratDiscIndices_subset U n))

/-- The approximating domains of an open connected `U ∋ a` exhaust `U`. -/
theorem exists_mem_ratApprox {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) {a w : ℂ}
    (ha : a ∈ U) (hw : w ∈ U) : ∃ n, w ∈ ratApprox (ratDiscIndices U n) a := by
  obtain ⟨n, hn⟩ := exists_mem_connectedComponentIn_ratDiscUnion hUo hUc ha hw
  exact ⟨n, subset_fillHoles _ hn⟩

/-- The approximating domains of a simply connected `U ∋ a`, from an index `K` at which `a` lies
in the disc union on, converge to `U` with respect to `a`. -/
theorem kernelConvergesTo_ratApprox {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    (hsc : IsSimplyConnected U) (hne : U ≠ univ) {a : ℂ} (ha : a ∈ U) {K : ℕ}
    (hK : a ∈ ratDiscUnion (ratDiscIndices U K)) :
    (∀ n, a ∈ ratDiscUnion (ratDiscIndices U (n + K))) ∧
      KernelConvergesTo (fun n => ratApprox (ratDiscIndices U (n + K)) a) U a := by
  have haN : ∀ n, a ∈ ratDiscUnion (ratDiscIndices U (n + K)) := fun n =>
    ratDiscUnion_mono (ratDiscIndices_mono (Nat.le_add_left K n)) hK
  refine ⟨haN, ?_⟩
  set G : ℕ → Set ℂ := fun n => ratApprox (ratDiscIndices U (n + K)) a with hGdef
  have hGmono : Monotone G := fun n m hnm => ratApprox_mono a (Nat.add_le_add_right hnm K)
  have hGU : (⋃ n, G n) = U := by
    refine subset_antisymm (iUnion_subset fun n => ratApprox_subset hUo hsc a _) ?_
    intro w hw
    obtain ⟨m, hm⟩ := exists_mem_ratApprox hUo hUc ha hw
    exact mem_iUnion.2 ⟨m, ratApprox_mono a (Nat.le_add_right m K) hm⟩
  have := kernelConvergesTo_iUnion_of_monotone hGmono (fun n => (ratApprox_props (haN n)).1)
    (fun n => (ratApprox_props (haN n)).2.1.isPreconnected) (ratApprox_props (haN 0)).2.2.2.2
    (hGU ▸ hne)
  rwa [hGU] at this

/-- The event that the first `n` rational-disc tests for `U ω` have outcome `S` is measurable
when compact inclusion in `U ω` is. -/
theorem measurableSet_ratDiscIndices_eq {Ω : Type*} [MeasurableSpace Ω] {U : Ω → Set ℂ}
    (hmeas : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω}) (n : ℕ)
    (S : Finset ℕ) : MeasurableSet {ω | ratDiscIndices (U ω) n = S} := by
  have heq : {ω | ratDiscIndices (U ω) n = S} =
      ⋂ k : ℕ, {ω | (k < n ∧ closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U ω) ↔ k ∈ S} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.ext_iff, mem_ratDiscIndices]
  rw [heq]
  refine MeasurableSet.iInter fun k => ?_
  by_cases hk : k < n <;> by_cases hS : k ∈ S
  · have e : {ω | (k < n ∧ closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U ω) ↔ k ∈ S} =
        {ω | closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U ω} := by
      ext ω; simp [hk, hS]
    rw [e]; exact hmeas _ _
  · have e : {ω | (k < n ∧ closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U ω) ↔ k ∈ S} =
        {ω | closedBall (ratDiscCenter k) (ratDiscRadius k) ⊆ U ω}ᶜ := by
      ext ω; simp [hk, hS]
    rw [e]; exact (hmeas _ _).compl
  · simp [hk, hS]
  · simp [hk, hS]

/-- A function of the outcome of the first `n` rational-disc tests is measurable. -/
theorem measurable_comp_ratDiscIndices {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {U : Ω → Set ℂ} (hmeas : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω})
    (h : Finset ℕ → β) (n : ℕ) : Measurable fun ω => h (ratDiscIndices (U ω) n) := by
  intro B _
  have heq : (fun ω => h (ratDiscIndices (U ω) n)) ⁻¹' B =
      ⋃ S ∈ (Finset.range n).powerset, ({ω | ratDiscIndices (U ω) n = S} ∩ {_ω | h S ∈ B}) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq, Finset.mem_powerset,
      exists_prop]
    constructor
    · intro hω
      refine ⟨ratDiscIndices (U ω) n, fun k hk => ?_, rfl, hω⟩
      exact Finset.mem_range.2 (mem_ratDiscIndices.1 hk).1
    · rintro ⟨S, -, hS, hB⟩
      rw [hS]
      exact hB
  rw [heq]
  exact Finset.measurableSet_biUnion _ fun S _ =>
    (measurableSet_ratDiscIndices_eq hmeas n S).inter (MeasurableSet.const _)

/-- **Measurable normalized Riemann maps** (specification Lemma CM-B, p. 659, the part "Carathéodory
kernel convergence gives their locally uniform limit `f_U`, so the evaluations of `f_U` … are
measurable"). Let `U ω` be open, connected, simply connected, proper subsets of `ℂ` containing a
fixed point `a`, depending on a parameter `ω` so that compact inclusion `closedBall c r ⊆ U ω`
is a measurable event. Then the normalized conformal maps `F ω : 𝔻 → U ω` (`F ω 0 = a`,
`F ω'(0) > 0`) are measurable in `ω`, pointwise and jointly in `(ω, z) ∈ Ω × 𝔻`.

Proof: the maps onto the hole-filled unions of the first rational discs whose closures lie in
`U ω` depend on `ω` through finitely many measurable tests, and converge to `F ω` by the kernel
theorem for increasing domains. -/
theorem exists_measurable_normalizedRiemannMap {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → Set ℂ} {a : ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUc : ∀ ω, IsConnected (U ω))
    (hsc : ∀ ω, IsSimplyConnected (U ω)) (hne : ∀ ω, U ω ≠ univ) (ha : ∀ ω, a ∈ U ω)
    (hmeas : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω}) :
    ∃ F : Ω → ℂ → ℂ,
      (∀ ω, IsConformalBijection (F ω) (ball 0 1) (U ω) ∧ F ω 0 = a ∧ 0 < deriv (F ω) 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, Measurable fun ω => F ω z) ∧
      Measurable fun p : Ω × ball (0 : ℂ) 1 => F p.1 p.2 := by
  -- normalized maps onto the approximating domains
  have hS : ∀ S : Finset ℕ, ∃ h : ℂ → ℂ, a ∈ ratDiscUnion S →
      IsConformalBijection h (ball 0 1) (ratApprox S a) ∧ h 0 = a ∧ 0 < deriv h 0 := by
    intro S
    by_cases haS : a ∈ ratDiscUnion S
    · obtain ⟨ho, hc, hs, hn, hm⟩ := ratApprox_props haS
      obtain ⟨h, hh⟩ := exists_isConformalBijection_ball_onto ho hc hs hn hm
      exact ⟨h, fun _ => hh⟩
    · exact ⟨id, fun h => absurd h haS⟩
  choose h hh using hS
  -- the normalized maps onto `U ω`
  have hU : ∀ ω, ∃ f : ℂ → ℂ,
      IsConformalBijection f (ball 0 1) (U ω) ∧ f 0 = a ∧ 0 < deriv f 0 := fun ω =>
    exists_isConformalBijection_ball_onto (hUo ω) (hUc ω) (hsc ω) (hne ω) (ha ω)
  choose F hF using hU
  -- convergence of the approximating maps
  have hconv : ∀ ω, ∀ z ∈ ball (0 : ℂ) 1,
      Tendsto (fun n => h (ratDiscIndices (U ω) n) z) atTop (𝓝 (F ω z)) := by
    intro ω z hz
    obtain ⟨N, hN⟩ := exists_mem_connectedComponentIn_ratDiscUnion (hUo ω) (hUc ω) (ha ω) (ha ω)
    obtain ⟨haN, hker⟩ := kernelConvergesTo_ratApprox (hUo ω) (hUc ω) (hsc ω) (hne ω) (ha ω)
      (connectedComponentIn_subset _ _ hN)
    have hlim := (kernel_convergence_iff (f := fun n => h (ratDiscIndices (U ω) (n + N)))
      (fun n => (hh _ (haN n)).1) (fun n => (hh _ (haN n)).2.1) (fun n => (hh _ (haN n)).2.2)
      (Or.inr (hF ω))).2 hker
    exact (tendsto_add_atTop_iff_nat N).1 (hlim.tendsto_at hz)
  have hptw : ∀ z ∈ ball (0 : ℂ) 1, Measurable fun ω => F ω z := by
    intro z hz
    refine measurable_of_tendsto_metrizable
      (f := fun n ω => h (ratDiscIndices (U ω) n) z)
      (fun n => measurable_comp_ratDiscIndices hmeas (fun S => h S z) n) ?_
    exact tendsto_pi_nhds.2 fun ω => hconv ω z hz
  refine ⟨F, hF, hptw, ?_⟩
  have hjoint := MeasureTheory.measurable_uncurry_of_continuous_of_measurable
    (u := fun (i : ball (0 : ℂ) 1) (ω : Ω) => F ω i)
    (fun ω => (hF ω).1.1.continuousOn.domRestrict) (fun i => hptw i i.2)
  exact hjoint.comp measurable_swap


/-- **Measurable normalized charts** (specification Lemma CM-B, p. 659: the Riemann maps
`f_U : U → 𝔻` normalized by `f_U(a) = 0`, `f_U'(a) > 0`, whose evaluations at points are
measurable). Under the hypotheses of `exists_measurable_normalizedRiemannMap`, the normalized
charts `Φ ω : U ω → 𝔻`, extended by `0` off `U ω`, are measurable in `ω` at every point `z`.

Proof: the charts of the approximating domains depend on `ω` through finitely many measurable
tests; they converge to `Φ ω` at every `z ∈ U ω` because their inverses converge (kernel theorem)
and inverse convergence passes to the maps (QuantumZipper `tendstoUniformlyOn_of_invFunOn`). -/
theorem exists_measurable_normalizedChart {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → Set ℂ} {a : ℂ} (hUo : ∀ ω, IsOpen (U ω)) (hUc : ∀ ω, IsConnected (U ω))
    (hsc : ∀ ω, IsSimplyConnected (U ω)) (hne : ∀ ω, U ω ≠ univ) (ha : ∀ ω, a ∈ U ω)
    (hmeas : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ U ω}) :
    ∃ Φ : Ω → ℂ → ℂ,
      (∀ ω, IsConformalBijection (Φ ω) (U ω) (ball 0 1) ∧ Φ ω a = 0 ∧ 0 < deriv (Φ ω) a) ∧
      (∀ ω, ∀ z ∉ U ω, Φ ω z = 0) ∧ ∀ z, Measurable fun ω => Φ ω z := by
  classical
  have hS : ∀ S : Finset ℕ, ∃ φ : ℂ → ℂ, a ∈ ratDiscUnion S →
      (IsConformalBijection φ (ratApprox S a) (ball 0 1) ∧ φ a = 0 ∧ 0 < deriv φ a) ∧
      IsConformalBijection (invFunOn φ (ratApprox S a)) (ball 0 1) (ratApprox S a) ∧
      invFunOn φ (ratApprox S a) 0 = a ∧ 0 < deriv (invFunOn φ (ratApprox S a)) 0 := by
    intro S
    by_cases haS : a ∈ ratDiscUnion S
    · obtain ⟨ho, hc, hs, hn, hm⟩ := ratApprox_props haS
      obtain ⟨φ, hφ⟩ := exists_isConformalBijection_ball_and_inv ho hc hs hn hm
      exact ⟨φ, fun _ => hφ⟩
    · exact ⟨id, fun h => absurd h haS⟩
  choose φ hφ using hS
  have hU : ∀ ω, ∃ ψ : ℂ → ℂ,
      (IsConformalBijection ψ (U ω) (ball 0 1) ∧ ψ a = 0 ∧ 0 < deriv ψ a) ∧
      IsConformalBijection (invFunOn ψ (U ω)) (ball 0 1) (U ω) ∧ invFunOn ψ (U ω) 0 = a ∧
      0 < deriv (invFunOn ψ (U ω)) 0 := fun ω =>
    exists_isConformalBijection_ball_and_inv (hUo ω) (hUc ω) (hsc ω) (hne ω) (ha ω)
  choose Φ₀ hΦ₀ using hU
  set Φ : Ω → ℂ → ℂ := fun ω z => if z ∈ U ω then Φ₀ ω z else 0 with hΦdef
  have hEq : ∀ ω, EqOn (Φ ω) (Φ₀ ω) (U ω) := fun ω z hz => ite_eq_left hz
  -- the approximating chart values at a point `z`
  set c : ℂ → Finset ℕ → ℂ := fun z S =>
    if a ∈ ratDiscUnion S ∧ z ∈ ratApprox S a then φ S z else 0 with hcdef
  have hconv : ∀ ω, ∀ z ∈ U ω,
      Tendsto (fun n => c z (ratDiscIndices (U ω) n)) atTop (𝓝 (Φ₀ ω z)) := by
    intro ω z hz
    obtain ⟨N, hN⟩ := exists_mem_connectedComponentIn_ratDiscUnion (hUo ω) (hUc ω) (ha ω) (ha ω)
    obtain ⟨M, hM⟩ := exists_mem_ratApprox (hUo ω) (hUc ω) (ha ω) hz
    obtain ⟨haN, hker⟩ := kernelConvergesTo_ratApprox (hUo ω) (hUc ω) (hsc ω) (hne ω) (ha ω)
      (K := N + M) (ratDiscUnion_mono (ratDiscIndices_mono (Nat.le_add_right N M))
        (connectedComponentIn_subset _ _ hN))
    have hzG : ∀ n, z ∈ ratApprox (ratDiscIndices (U ω) (n + (N + M))) a := fun n =>
      ratApprox_mono a (by omega) hM
    have hlim := (kernel_convergence_iff
      (f := fun n => invFunOn (φ (ratDiscIndices (U ω) (n + (N + M))))
        (ratApprox (ratDiscIndices (U ω) (n + (N + M))) a))
      (fun n => (hφ _ (haN n)).2.1) (fun n => (hφ _ (haN n)).2.2.1)
      (fun n => (hφ _ (haN n)).2.2.2) (Or.inr (hΦ₀ ω).2)).2 hker
    have hunif := QuantumZipper.CA.Kernel.tendstoUniformlyOn_of_invFunOn isOpen_ball
      (fun n => (hφ _ (haN n)).1.1.2) (hΦ₀ ω).1.1.2
      (fun y hy => ((hΦ₀ ω).1.1.1.differentiableAt ((hUo ω).mem_nhds hy)).continuousAt)
      (fun n => (hφ _ (haN n)).2.1.1) (hΦ₀ ω).2.1.2.injOn hlim isCompact_singleton
      (singleton_subset_iff.2 hz)
    refine (tendsto_add_atTop_iff_nat (N + M)).1 ?_
    refine (hunif.tendsto_at (mem_singleton z)).congr' (Eventually.of_forall fun n => ?_)
    simp only [hcdef]
    rw [ite_eq_left ⟨haN n, hzG n⟩]
  refine ⟨Φ, fun ω => ⟨⟨(hΦ₀ ω).1.1.1.congr (hEq ω), (hΦ₀ ω).1.1.2.congr (hEq ω).symm⟩, ?_, ?_⟩,
    fun ω z hz => ite_eq_right hz, fun z => ?_⟩
  · rw [hEq ω (ha ω)]
    exact (hΦ₀ ω).1.2.1
  · have he : Φ ω =ᶠ[𝓝 a] Φ₀ ω := Filter.eventuallyEq_of_mem ((hUo ω).mem_nhds (ha ω)) (hEq ω)
    rw [he.deriv_eq]
    exact (hΦ₀ ω).1.2.2
  · refine measurable_of_tendsto_metrizable (f := fun n ω => c z (ratDiscIndices (U ω) n))
      (fun n => measurable_comp_ratDiscIndices hmeas (c z) n) (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hz : z ∈ U ω
    · rw [show Φ ω z = Φ₀ ω z from ite_eq_left hz]
      exact hconv ω z hz
    · have h0 : ∀ n, c z (ratDiscIndices (U ω) n) = 0 := fun n =>
        ite_eq_right fun h => hz (ratApprox_subset (hUo ω) (hsc ω) a n h.2)
      simp only [h0, show Φ ω z = 0 from ite_eq_right hz]
      exact tendsto_const_nhds

end Measurable

end InteractingSLE
