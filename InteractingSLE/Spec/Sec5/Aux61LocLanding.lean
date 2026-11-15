/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51IQEast
import QuantumZipper.Proofs.Complex.BasicsReflection

/-!
# Landing of a boundary-approaching curve in a chart with a continuous inverse boundary extension

Packet PROVE-AUX61LOC (the localization of Aux. lemmas 61–64 for the flow line restarted after contacts, the input
(E1) `Prop51I.FwdPostContactEastSideQOn` of Proposition 5.1's forward route). The source's countable localization
(Aux. lemma 64, p. 265: "On an outcome with a continuous first endpoint …, that segment, completed by its endpoint, is
compact …") and the restart chart of Lemma 5.4 (p. 133, "the largest time `t ≤ τ` such that `η(t) ∈ K′`") both read
the post-contact excursion of `η` in `ℍ ∖ R(K_s)` through the counterflow chart `Ψ = revChart w s` as a curve that
**lands** at its two ends. PROVE-PROP51H/I only had cluster points (`HitsEastSideAlong` is a `MapClusterPt`
statement: "a curve ending at a boundary point has a unique prime-end limit; not landed for these hulls"). This file
proves the landing.

**Generic landing lemma** (`tendsto_or_cobounded_of_tendsto_comp`): let `g` be continuous on `(a, b)` with values in
`ℍ`, and `F` continuous on `ℍ̄` and holomorphic on `ℍ`. If `F ∘ g → p` as `u ↓ a` with `p ∉ F(ℍ)`, then `g` lands as
`u ↓ a`: it tends to a real point or to `∞`. Proof: every finite cluster point `ζ` of `g` lies in `ℍ̄` with `F(ζ) = p`
(`mapClusterPt_im_eq_zero`), hence is real. If `g` clusters at a real `x₁` without converging to it, then for every
`r` in some `(0, ε)` the continuous `u ↦ |g(u) − x₁|` takes the value `r` at times tending to `a` (intermediate values
between visits near `x₁` and visits at distance `≥ ε`), so `x₁ + r` or `x₁ − r` is a cluster point
(`mapClusterPt_add_or_sub`); the cluster set is closed, so it contains a nondegenerate real interval
(`exists_Ioo_subset_of_add_or_sub`), on which `F ≡ p`. By the Schwarz reflection principle
(`QuantumZipper.CA.eqOn_const_of_eq_const_on_Ioo`) `F ≡ p` on a half-disc of `ℍ`, so `p ∈ F(ℍ)`: a contradiction.
Without finite cluster points `g → ∞`. The mirror statements for `u ↑ b` follow by `u ↦ −u`.

**The counterflow chart** (`revChart_landing_right`, `revChart_landing_left`): for a Loewner trace `β` of a continuous
driver `w` with `w 0 = 0` (the counterflow in its own chart), the extension of `F_s = f_s⁻¹` to `ℍ̄`
(`IsLoewnerTrace.exists_extension`) makes the generic lemma apply to `g = f_s ∘ R ∘ η`; so a curve `η` in
`ℍ ∖ R(K_s)` tending to a point outside `ℍ ∖ R(K_s)` has `Ψ ∘ η` landing at a real point or at `∞`.

**The post-contact excursion** (`exists_tendsto_revChart_of_hitsEastSideAlong`, `exists_lastContact`,
`isEastCrosscut_of_hitsEastSideAlong`): if the excursion of `η` running at `t` ends on the eastern side proper at
`u₀` (the violation of (E1)), then `Ψ ∘ η → x₁ ∈ (junR, ∞)` as `u ↑ u₀`, the excursion started at the last contact
`τ₀ ∈ (0, t)` with `η(τ₀) ∉ ℍ ∖ R(K_s)`, and `Ψ ∘ η` lands as `u ↓ τ₀` at a point of `ℝ ∪ {∞}`. So **the chart image
of an (E1)-violating excursion is a crosscut of `ℍ` from `ℝ ∪ {∞}` to the eastern side `(junR, ∞)`** — the geometric
object of the source's restart chart (Lemma 5.4's `ψ`, mapping out the crosscut's part `[τ₀, t]`).
(E1) is therefore the exclusion of such crosscuts (`postContactEastSideResidual_of_not_crosscut`; on the glued space
`FwdNoEastCrosscutQOn` and `fwdPostContactEastSideQOn_of_noCrosscut`).

Deterministic; no probabilistic input; nothing here replaces a source theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Aux61Loc

open WangWu hiding ratPt exists_ratPt_dist_lt
open CrossCond.Word49 Prop51G Prop51H Prop51I

/-! ### Cluster points of a curve in a chart -/

section Generic

variable {ι : Type*} {l : Filter ι} {g : ι → ℂ} {F : ℂ → ℂ}

/-- A curve with no finite cluster point tends to `∞`. -/
theorem tendsto_cobounded_of_forall_not_mapClusterPt (h : ∀ ζ, ¬ MapClusterPt ζ l g) :
    Tendsto g l (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop]
  intro R
  by_contra hR
  rw [not_eventually] at hR
  have hfr : ∃ᶠ u in l, g u ∈ closedBall (0 : ℂ) R :=
    hR.mono fun u hu => by
      rw [mem_closedBall, dist_zero_right]
      exact (not_le.1 hu).le
  obtain ⟨ζ, -, hζ⟩ := (isCompact_closedBall (0 : ℂ) R).exists_mapClusterPt_of_frequently hfr
  exact h ζ hζ

/-- A curve tending to `∞` has no finite cluster point. -/
theorem not_mapClusterPt_of_tendsto_cobounded (h : Tendsto g l (Bornology.cobounded ℂ)) (ζ : ℂ) :
    ¬ MapClusterPt ζ l g := by
  intro hζ
  rw [← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop] at h
  have hfar := h (‖ζ‖ + 1)
  have hnear : ∃ᶠ u in l, g u ∈ ball ζ 1 := mapClusterPt_iff_frequently.1 hζ _ (ball_mem_nhds ζ one_pos)
  obtain ⟨u, hu₁, hu₂⟩ := (hnear.and_eventually hfar).exists
  rw [mem_ball, dist_eq_norm] at hu₁
  have := norm_le_norm_add_norm_sub' (g u) ζ
  linarith [norm_sub_rev (g u) ζ]

/-- **A cluster point transfers through a map continuous on `ℍ̄`**: if `g` is eventually in `ℍ̄` and clusters at `ζ`,
then `ζ ∈ ℍ̄` and `F ∘ g` clusters at `F ζ`. -/
theorem mapClusterPt_comp_of_continuousOn (hev : ∀ᶠ u in l, g u ∈ Hbar) (hFc : ContinuousOn F Hbar) {ζ : ℂ}
    (hζ : MapClusterPt ζ l g) : ζ ∈ Hbar ∧ MapClusterPt (F ζ) l (fun u => F (g u)) := by
  have hmem : Hbar ∈ map g l := hev
  have hζH : ζ ∈ Hbar := by
    have := ClusterPt.mem_closure_of_mem hζ Hbar hmem
    rwa [QuantumZipper.isClosed_Hbar.closure_eq] at this
  refine ⟨hζH, ?_⟩
  have h1 : (𝓝 ζ ⊓ map g l).NeBot := hζ
  have h2 : 𝓝 ζ ⊓ map g l ≤ 𝓝[Hbar] ζ := inf_le_inf_left _ (le_principal_iff.2 hmem)
  have h3 : map F (𝓝 ζ ⊓ map g l) ≤ 𝓝 (F ζ) ⊓ map (fun u => F (g u)) l :=
    le_inf ((map_mono h2).trans (hFc ζ hζH)) (by
      rw [show (fun u => F (g u)) = F ∘ g from rfl, ← map_map]
      exact map_mono inf_le_right)
  exact (h1.map F).mono h3

end Generic

/-! ### The landing lemma at a left end `u ↓ a` -/

section Right

variable {g : ℝ → ℂ} {F : ℂ → ℂ} {a b : ℝ} {p : ℂ}

/-- `g` is eventually in `ℍ` as `u ↓ a`. -/
theorem eventually_mem_H_nhdsGT (hab : a < b) (hgH : ∀ u ∈ Ioo a b, g u ∈ H) : ∀ᶠ u in 𝓝[>] a, g u ∈ H :=
  Filter.mem_of_superset (Ioo_mem_nhdsGT hab) fun u hu => hgH u hu

/-- **Cluster points are real points mapped to `p`.** If `F ∘ g → p ∉ F(ℍ)` as `u ↓ a`, every finite cluster point
`ζ` of `g` is real and `F ζ = p`. -/
theorem mapClusterPt_im_eq_zero (hab : a < b) (hgH : ∀ u ∈ Ioo a b, g u ∈ H) (hFc : ContinuousOn F Hbar)
    (hp : p ∉ F '' H) (hlim : Tendsto (fun u => F (g u)) (𝓝[>] a) (𝓝 p)) {ζ : ℂ}
    (hζ : MapClusterPt ζ (𝓝[>] a) g) : ζ.im = 0 ∧ F ζ = p := by
  have hev : ∀ᶠ u in 𝓝[>] a, g u ∈ Hbar :=
    (eventually_mem_H_nhdsGT hab hgH).mono fun u hu => le_of_lt (show (0 : ℝ) < (g u).im from hu)
  obtain ⟨hζH, hcl⟩ := mapClusterPt_comp_of_continuousOn hev hFc hζ
  have hFp : F ζ = p := by
    have h4 : (𝓝 (F ζ) ⊓ 𝓝 p).NeBot := hcl.neBot.mono (inf_le_inf_left _ hlim)
    exact eq_of_nhds_neBot h4
  refine ⟨le_antisymm ?_ hζH, hFp⟩
  by_contra hpos
  exact hp ⟨ζ, show (0 : ℝ) < ζ.im from lt_of_not_ge hpos, hFp⟩

/-- **Intermediate distances are visited at times tending to `a`.** If `g` clusters at `x₁` and is frequently at
distance at least `ε` from it, it is frequently at distance exactly `r`, for every `0 < r < ε`. -/
theorem frequently_dist_eq (hab : a < b) (hgc : ContinuousOn g (Ioo a b)) {x₁ : ℂ}
    (hx₁ : MapClusterPt x₁ (𝓝[>] a) g) {ε : ℝ} (hfar : ∃ᶠ u in 𝓝[>] a, ε ≤ dist (g u) x₁) {r : ℝ} (hr : 0 < r)
    (hrε : r < ε) : ∃ᶠ u in 𝓝[>] a, dist (g u) x₁ = r := by
  rw [(nhdsGT_basis a).frequently_iff]
  intro b' hb'
  set c := min b' b with hc
  have hac : a < c := lt_min hb' hab
  have hnear : ∃ᶠ u in 𝓝[>] a, g u ∈ ball x₁ r := mapClusterPt_iff_frequently.1 hx₁ _ (ball_mem_nhds x₁ hr)
  obtain ⟨u₁, hu₁, hd₁⟩ := ((nhdsGT_basis a).frequently_iff.1 hfar) c hac
  obtain ⟨u₂, hu₂, hd₂⟩ := ((nhdsGT_basis a).frequently_iff.1 hnear) c hac
  rw [mem_ball] at hd₂
  have hsub : uIcc u₁ u₂ ⊆ Ioo a c := (ordConnected_Ioo).uIcc_subset hu₁ hu₂
  have hcb : Ioo a c ⊆ Ioo a b := Ioo_subset_Ioo_right (min_le_right _ _)
  have hφ : ContinuousOn (fun u => dist (g u) x₁) (uIcc u₁ u₂) :=
    (continuous_id.dist continuous_const).comp_continuousOn (hgc.mono (hsub.trans hcb))
  have hrm : r ∈ uIcc (dist (g u₁) x₁) (dist (g u₂) x₁) := by
    rw [mem_uIcc]
    exact Or.inr ⟨hd₂.le, by linarith⟩
  obtain ⟨v, hv, hvr⟩ := intermediate_value_uIcc hφ hrm
  exact ⟨v, Ioo_subset_Ioo_right (min_le_left _ _) (hsub hv), hvr⟩

/-- **A cluster point at distance `r`**: under the hypotheses of `frequently_dist_eq` and of
`mapClusterPt_im_eq_zero`, `x₁ + r` or `x₁ − r` is a cluster point of `g` (`x₁` real). -/
theorem mapClusterPt_add_or_sub (hab : a < b) (hgc : ContinuousOn g (Ioo a b)) (hgH : ∀ u ∈ Ioo a b, g u ∈ H)
    (hFc : ContinuousOn F Hbar) (hp : p ∉ F '' H) (hlim : Tendsto (fun u => F (g u)) (𝓝[>] a) (𝓝 p)) {x₁ : ℝ}
    (hx₁ : MapClusterPt (x₁ : ℂ) (𝓝[>] a) g) {ε : ℝ} (hfar : ∃ᶠ u in 𝓝[>] a, ε ≤ dist (g u) (x₁ : ℂ))
    {r : ℝ} (hr : 0 < r) (hrε : r < ε) :
    MapClusterPt ((x₁ + r : ℝ) : ℂ) (𝓝[>] a) g ∨ MapClusterPt ((x₁ - r : ℝ) : ℂ) (𝓝[>] a) g := by
  have hfr := frequently_dist_eq hab hgc hx₁ hfar hr hrε
  have hfr' : ∃ᶠ u in 𝓝[>] a, g u ∈ sphere (x₁ : ℂ) r := hfr.mono fun u hu => by rwa [mem_sphere]
  obtain ⟨ζ, hζs, hζ⟩ := (isCompact_sphere (x₁ : ℂ) r).exists_mapClusterPt_of_frequently hfr'
  obtain ⟨him, -⟩ := mapClusterPt_im_eq_zero hab hgH hFc hp hlim hζ
  have hζre : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [mem_sphere, hζre, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hζs
  rcases abs_eq hr.le |>.1 hζs with h | h
  · left
    have e : ζ = ((x₁ + r : ℝ) : ℂ) := by rw [hζre]; congr 1; linarith
    exact e ▸ hζ
  · right
    have e : ζ = ((x₁ - r : ℝ) : ℂ) := by rw [hζre]; congr 1; linarith
    exact e ▸ hζ

/-- **A closed set containing `x₁ + r` or `x₁ − r` for every `r ∈ (0, ε)` contains a nondegenerate open interval.** -/
theorem exists_Ioo_subset_of_add_or_sub {C : Set ℝ} (hC : IsClosed C) {x₁ ε : ℝ} (hε : 0 < ε)
    (h : ∀ r ∈ Ioo 0 ε, x₁ + r ∈ C ∨ x₁ - r ∈ C) : ∃ c d : ℝ, c < d ∧ Ioo c d ⊆ C := by
  by_cases hall : ∀ r ∈ Ioo 0 ε, x₁ + r ∈ C
  · refine ⟨x₁, x₁ + ε, by linarith, fun y hy => ?_⟩
    have := hall (y - x₁) ⟨by linarith [hy.1], by linarith [hy.2]⟩
    rwa [add_sub_cancel] at this
  push Not at hall
  obtain ⟨r₀, hr₀, hr₀C⟩ := hall
  have hopen : IsOpen {r : ℝ | x₁ + r ∉ C} :=
    hC.isOpen_compl.preimage (continuous_const.add continuous_id)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen r₀ hr₀C
  set δ' := min δ (min r₀ (ε - r₀)) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (lt_min hr₀.1 (by linarith [hr₀.2]))
  have hδ'1 : δ' ≤ δ := min_le_left _ _
  have hδ'2 : δ' ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ'3 : δ' ≤ ε - r₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨x₁ - r₀ - δ', x₁ - r₀ + δ', by linarith, fun y hy => ?_⟩
  have hr : x₁ - y ∈ Ioo 0 ε := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hnot : x₁ + (x₁ - y) ∉ C := by
    have hm : x₁ - y ∈ Metric.ball r₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    exact hball hm
  have := (h (x₁ - y) hr).resolve_left hnot
  rwa [sub_sub_cancel] at this

/-- **Boundary uniqueness**: a function continuous on `ℍ̄` and holomorphic on `ℍ` that equals `p` on a nondegenerate
real interval takes the value `p` in `ℍ` (Schwarz reflection). -/
theorem mem_image_H_of_eq_on_Ioo (hFc : ContinuousOn F Hbar) (hFd : DifferentiableOn ℂ F H) {c d : ℝ}
    (hcd : c < d) (hI : ∀ y ∈ Ioo c d, F (y : ℂ) = p) : p ∈ F '' H := by
  set m : ℝ := (c + d) / 2 with hm
  set ρ : ℝ := (d - c) / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hreal_mem : ∀ z ∈ ball (m : ℂ) ρ, z.im = 0 → z.re ∈ Ioo c d := by
    intro z hz hz0
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |z.re - m| < ρ := by
      have := Complex.abs_re_le_norm (z - m)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith
    rw [abs_lt] at h1
    exact ⟨by rw [hm, hρ] at h1; linarith [h1.1], by rw [hm, hρ] at h1; linarith [h1.2]⟩
  have hreal_eq : ∀ z ∈ ball (m : ℂ) ρ, z.im = 0 → z = (z.re : ℂ) := fun z _ hz0 =>
    Complex.ext rfl (by simp [hz0])
  have key := QuantumZipper.CA.eqOn_const_of_eq_const_on_Ioo (g := fun z => F z - p) (x := m) (r := ρ)
    ((hFd.mono inter_subset_left).sub_const p) ((hFc.mono inter_subset_left).sub continuousOn_const)
    (fun z hz hz0 => by
      rw [hreal_eq z hz hz0, hI z.re (hreal_mem z hz hz0), sub_self, Complex.zero_im]) hcd
    (c := 0) (fun y hy => ⟨by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> · rw [hm, hρ]; linarith [hy.1, hy.2], by simp only [hI y hy, sub_self]⟩)
  set z₀ : ℂ := (m : ℂ) + ((ρ / 2 : ℝ) : ℂ) * I with hz₀
  have hz₀im : z₀.im = ρ / 2 := by simp [hz₀]
  have hz₀H : z₀ ∈ H := show (0 : ℝ) < z₀.im by rw [hz₀im]; linarith
  have hz₀B : z₀ ∈ ball (m : ℂ) ρ := by
    rw [mem_ball, dist_eq_norm, hz₀, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have h0 := key z₀ ⟨le_of_lt (show (0 : ℝ) < z₀.im from hz₀H), hz₀B⟩
  exact ⟨z₀, hz₀H, sub_eq_zero.1 h0⟩

/-- **The landing lemma** (as `u ↓ a`). Let `g` be continuous on `(a, b)` with values in `ℍ`, `F` continuous on `ℍ̄`
and holomorphic on `ℍ`, and `F ∘ g → p ∉ F(ℍ)` as `u ↓ a`. Then `g` lands: it tends to a real point or to `∞`. -/
theorem tendsto_or_cobounded_of_tendsto_comp (hab : a < b) (hgc : ContinuousOn g (Ioo a b))
    (hgH : ∀ u ∈ Ioo a b, g u ∈ H) (hFc : ContinuousOn F Hbar) (hFd : DifferentiableOn ℂ F H) (hp : p ∉ F '' H)
    (hlim : Tendsto (fun u => F (g u)) (𝓝[>] a) (𝓝 p)) :
    (∃ x : ℝ, Tendsto g (𝓝[>] a) (𝓝 (x : ℂ))) ∨ Tendsto g (𝓝[>] a) (Bornology.cobounded ℂ) := by
  by_cases hex : ∃ ζ, MapClusterPt ζ (𝓝[>] a) g
  swap
  · push Not at hex
    exact Or.inr (tendsto_cobounded_of_forall_not_mapClusterPt hex)
  left
  obtain ⟨ζ, hζ⟩ := hex
  obtain ⟨him, -⟩ := mapClusterPt_im_eq_zero hab hgH hFc hp hlim hζ
  have hζre : ζ = (ζ.re : ℂ) := Complex.ext rfl (by simp [him])
  set x₁ := ζ.re with hx₁
  rw [hζre] at hζ
  refine ⟨x₁, ?_⟩
  by_contra hnt
  rw [Metric.tendsto_nhds] at hnt
  push Not at hnt
  obtain ⟨ε, hε, hfar⟩ := hnt
  have hfar' : ∃ᶠ u in 𝓝[>] a, ε ≤ dist (g u) (x₁ : ℂ) := hfar
  set C : Set ℝ := {y : ℝ | MapClusterPt (y : ℂ) (𝓝[>] a) g} with hCdef
  have hC : IsClosed C := isClosed_setOfPred_clusterPt.preimage Complex.continuous_ofReal
  obtain ⟨c, d, hcd, hsub⟩ := exists_Ioo_subset_of_add_or_sub hC hε fun r hr =>
    mapClusterPt_add_or_sub hab hgc hgH hFc hp hlim hζ hfar' hr.1 hr.2
  exact hp (mem_image_H_of_eq_on_Ioo hFc hFd hcd fun y hy =>
    (mapClusterPt_im_eq_zero hab hgH hFc hp hlim (hsub hy)).2)

/-- **The landing lemma at `∞`** (as `u ↓ a`): if `F ∘ g → ∞`, then `g → ∞`. -/
theorem tendsto_cobounded_of_tendsto_comp_cobounded (hab : a < b) (hgH : ∀ u ∈ Ioo a b, g u ∈ H)
    (hFc : ContinuousOn F Hbar) (hlim : Tendsto (fun u => F (g u)) (𝓝[>] a) (Bornology.cobounded ℂ)) :
    Tendsto g (𝓝[>] a) (Bornology.cobounded ℂ) := by
  refine tendsto_cobounded_of_forall_not_mapClusterPt fun ζ hζ => ?_
  have hev : ∀ᶠ u in 𝓝[>] a, g u ∈ Hbar :=
    (eventually_mem_H_nhdsGT hab hgH).mono fun u hu => le_of_lt (show (0 : ℝ) < (g u).im from hu)
  exact not_mapClusterPt_of_tendsto_cobounded hlim _ (mapClusterPt_comp_of_continuousOn hev hFc hζ).2

end Right

/-! ### The mirror statements at a right end `u ↑ b` -/

section Left

variable {g : ℝ → ℂ} {F : ℂ → ℂ} {a b : ℝ} {p : ℂ}

/-- Precomposition with `u ↦ −u` turns `u ↑ b` into `u ↓ −b`. -/
theorem tendsto_comp_neg_nhdsGT {β : Type*} {f : ℝ → β} {L : Filter β} (h : Tendsto f (𝓝[<] b) L) :
    Tendsto (fun u => f (-u)) (𝓝[>] (-b)) L :=
  h.comp (by simpa using (tendsto_neg_nhdsGT_neg (a := b)))

/-- And back. -/
theorem tendsto_of_comp_neg_nhdsGT {β : Type*} {f : ℝ → β} {L : Filter β}
    (h : Tendsto (fun u => f (-u)) (𝓝[>] (-b)) L) : Tendsto f (𝓝[<] b) L := by
  have h2 : Tendsto (fun u : ℝ => -u) (𝓝[<] b) (𝓝[>] (-b)) := by
    simpa using (tendsto_neg_nhdsLT_neg (a := -b))
  have := h.comp h2
  simpa [Function.comp_def] using this

/-- **The landing lemma as `u ↑ b`.** -/
theorem tendsto_or_cobounded_of_tendsto_comp_left (hab : a < b) (hgc : ContinuousOn g (Ioo a b))
    (hgH : ∀ u ∈ Ioo a b, g u ∈ H) (hFc : ContinuousOn F Hbar) (hFd : DifferentiableOn ℂ F H) (hp : p ∉ F '' H)
    (hlim : Tendsto (fun u => F (g u)) (𝓝[<] b) (𝓝 p)) :
    (∃ x : ℝ, Tendsto g (𝓝[<] b) (𝓝 (x : ℂ))) ∨ Tendsto g (𝓝[<] b) (Bornology.cobounded ℂ) := by
  have hmaps : MapsTo (fun u : ℝ => -u) (Ioo (-b) (-a)) (Ioo a b) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hgc' : ContinuousOn (fun u => g (-u)) (Ioo (-b) (-a)) := hgc.comp continuousOn_neg hmaps
  rcases tendsto_or_cobounded_of_tendsto_comp (g := fun u => g (-u)) (neg_lt_neg hab) hgc'
      (fun u hu => hgH _ (hmaps hu)) hFc hFd hp (tendsto_comp_neg_nhdsGT hlim) with ⟨x, hx⟩ | h
  · exact Or.inl ⟨x, tendsto_of_comp_neg_nhdsGT hx⟩
  · exact Or.inr (tendsto_of_comp_neg_nhdsGT h)

/-- **The landing lemma at `∞` as `u ↑ b`.** -/
theorem tendsto_cobounded_of_tendsto_comp_cobounded_left (hab : a < b) (hgH : ∀ u ∈ Ioo a b, g u ∈ H)
    (hFc : ContinuousOn F Hbar) (hlim : Tendsto (fun u => F (g u)) (𝓝[<] b) (Bornology.cobounded ℂ)) :
    Tendsto g (𝓝[<] b) (Bornology.cobounded ℂ) := by
  have hmaps : MapsTo (fun u : ℝ => -u) (Ioo (-b) (-a)) (Ioo a b) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  exact tendsto_of_comp_neg_nhdsGT (tendsto_cobounded_of_tendsto_comp_cobounded (g := fun u => g (-u))
    (neg_lt_neg hab) (fun u hu => hgH _ (hmaps hu)) hFc (tendsto_comp_neg_nhdsGT hlim))

end Left

/-! ### `R(z) = −1/z` on limits -/

section NegInv

variable {ι : Type*} {l : Filter ι} {f : ι → ℂ}

theorem ne_zero_of_mem_H' {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  rw [h] at hz
  exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)

/-- `R` maps `ℍ ∖ K` into `ℍ ∖ R(K)`. -/
theorem negInv_mem_H_diff_image {K : Set ℂ} {z : ℂ} (hz : z ∈ H \ K) : negInv z ∈ H \ negInv '' K := by
  refine ⟨negInv_mem_H hz.1, fun ⟨k, hk, e⟩ => hz.2 ?_⟩
  rw [← negInv_negInv' z, ← e, negInv_negInv']
  exact hk

/-- `R(f) → 0` when `f → ∞`. -/
theorem tendsto_negInv_of_cobounded (h : Tendsto f l (Bornology.cobounded ℂ)) :
    Tendsto (fun u => negInv (f u)) l (𝓝 (0 : ℂ)) := by
  have := (tendsto_inv₀_cobounded.comp h).neg
  simpa [negInv, Function.comp_def] using this

/-- `R(f) → ∞` when `f → 0` through nonzero values. -/
theorem tendsto_negInv_cobounded_of_tendsto_zero (h : Tendsto f l (𝓝 0)) (hne : ∀ᶠ u in l, f u ≠ 0) :
    Tendsto (fun u => negInv (f u)) l (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hn : Tendsto (fun u => ‖f u‖) l (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨by simpa using h.norm, hne.mono fun u hu => norm_pos_iff.2 hu⟩
  have := tendsto_inv_nhdsGT_zero.comp hn
  simpa [negInv, Function.comp_def, norm_neg, norm_inv] using this

/-- `R(f) → −1/x` when `f → x ≠ 0` real. -/
theorem tendsto_negInv_of_tendsto_real {x : ℝ} (hx : x ≠ 0) (h : Tendsto f l (𝓝 (x : ℂ))) :
    Tendsto (fun u => negInv (f u)) l (𝓝 ((-x⁻¹ : ℝ) : ℂ)) := by
  have := (continuousAt_negInv (Complex.ofReal_ne_zero.2 hx)).tendsto.comp h
  have e : negInv (x : ℂ) = ((-x⁻¹ : ℝ) : ℂ) := by simp [negInv]
  rw [e] at this
  exact this

/-- **Landing transfers through `R`**: if `f` (with values in `ℍ`) tends to a real point or to `∞`, so does `R ∘ f`. -/
theorem negInv_landing (hfH : ∀ᶠ u in l, f u ∈ H)
    (h : (∃ x : ℝ, Tendsto f l (𝓝 (x : ℂ))) ∨ Tendsto f l (Bornology.cobounded ℂ)) :
    (∃ x : ℝ, Tendsto (fun u => negInv (f u)) l (𝓝 (x : ℂ))) ∨
      Tendsto (fun u => negInv (f u)) l (Bornology.cobounded ℂ) := by
  rcases h with ⟨x, hx⟩ | hx
  · by_cases hx0 : x = 0
    · subst hx0
      exact Or.inr (tendsto_negInv_cobounded_of_tendsto_zero (by simpa using hx)
        (hfH.mono fun u hu => ne_zero_of_mem_H' hu))
    · exact Or.inl ⟨-x⁻¹, tendsto_negInv_of_tendsto_real hx0 hx⟩
  · exact Or.inl ⟨0, by simpa using tendsto_negInv_of_cobounded hx⟩

end NegInv

/-! ### The counterflow chart `Ψ = revChart w s` lands along curves approaching the boundary -/

section Chart

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ} {a b : ℝ} {p : ℂ}

/-- The objects of the generic lemma for the counterflow chart: `g = f_s ∘ R ∘ η` lies in `ℍ`, is continuous, and
`F(g) = R ∘ η` for the boundary extension `F` of `F_s`; `F` is holomorphic on `ℍ` with `F(ℍ) ⊆ ℍ ∖ K_s`. -/
theorem revChart_landing_data (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv w s) H) {D : Set ℝ} (hηc : ContinuousOn η D)
    (hηD : ∀ u ∈ D, η u ∈ H \ cfHullQ w s) :
    (∀ u ∈ D, fwdMap w s (negInv (η u)) ∈ H) ∧ ContinuousOn (fun u => fwdMap w s (negInv (η u))) D ∧
      (∀ u ∈ D, F (fwdMap w s (negInv (η u))) = negInv (η u)) ∧ DifferentiableOn ℂ F H ∧
      F '' H ⊆ H \ fwdHull w s := by
  have hD' : ∀ u ∈ D, negInv (η u) ∈ H \ fwdHull w s := fun u hu => negInv_notMem_fwdHull (hηD u hu)
  have hgH : ∀ u ∈ D, fwdMap w s (negInv (η u)) ∈ H := fun u hu =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hw hs (hD' u hu)
  have hbij := isConformalBijection_fwdMapInv hw hw0 hs
  refine ⟨hgH, ?_, fun u hu => ?_, hbij.1.congr hFeq, ?_⟩
  · have hrc : ContinuousOn (fun u => revChart w s (η u)) D :=
      (continuousOn_revChart hw hs).comp hηc fun u hu => hηD u hu
    have e : (fun u => fwdMap w s (negInv (η u))) = fun u => negInv (revChart w s (η u)) :=
      funext fun u => by simp only [revChart, negInv_negInv']
    rw [e]
    intro u hu
    have hne : revChart w s (η u) ≠ 0 := ne_zero_of_mem_H' (revChart_mem_H hw hs (hηD u hu))
    exact ContinuousAt.comp_continuousWithinAt (g := negInv) (f := fun u => revChart w s (η u))
      (continuousAt_negInv hne) (hrc u hu)
  · rw [hFeq (hgH u hu)]
    exact QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 hs (hD' u hu)
  · rintro _ ⟨ζ, hζ, rfl⟩
    rw [hFeq hζ]
    exact hbij.2.mapsTo hζ

/-- **The counterflow chart lands as `u ↓ a`.** Let `w` be a continuous driver with `w 0 = 0` and a Loewner trace
`β` (the counterflow in its own chart), `s ≥ 0`, and `η` continuous on `(a, b)` with values in `ℍ ∖ R(K_s)`,
tending to a point `p ∉ ℍ ∖ R(K_s)` as `u ↓ a`. Then `Ψ ∘ η` tends to a real point or to `∞`. -/
theorem revChart_landing_right (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s)
    (hab : a < b) (hηc : ContinuousOn η (Ioo a b)) (hηD : ∀ u ∈ Ioo a b, η u ∈ H \ cfHullQ w s)
    (hp : Tendsto η (𝓝[>] a) (𝓝 p)) (hpD : p ∉ H \ cfHullQ w s) :
    (∃ x : ℝ, Tendsto (fun u => revChart w s (η u)) (𝓝[>] a) (𝓝 (x : ℂ))) ∨
      Tendsto (fun u => revChart w s (η u)) (𝓝[>] a) (Bornology.cobounded ℂ) := by
  obtain ⟨F, hFeq, hFc, -⟩ := hβ.exists_extension hw hw0 hs
  obtain ⟨hgH, hgc, hFg, hFd, hFH⟩ := revChart_landing_data hw hw0 hs hFeq hηc hηD
  have hevFg : ∀ᶠ u in 𝓝[>] a, negInv (η u) = F (fwdMap w s (negInv (η u))) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hab) fun u hu => (hFg u hu).symm
  have hevH : ∀ᶠ u in 𝓝[>] a, fwdMap w s (negInv (η u)) ∈ H :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hab) fun u hu => hgH u hu
  refine negInv_landing hevH ?_
  by_cases hp0 : p = 0
  · subst hp0
    have hcob : Tendsto (fun u => negInv (η u)) (𝓝[>] a) (Bornology.cobounded ℂ) :=
      tendsto_negInv_cobounded_of_tendsto_zero hp (Filter.mem_of_superset (Ioo_mem_nhdsGT hab)
        fun u hu => ne_zero_of_mem_H' (hηD u hu).1)
    exact Or.inr (tendsto_cobounded_of_tendsto_comp_cobounded hab hgH hFc (hcob.congr' hevFg))
  · have hlim : Tendsto (fun u => F (fwdMap w s (negInv (η u)))) (𝓝[>] a) (𝓝 (negInv p)) :=
      ((continuousAt_negInv hp0).tendsto.comp hp).congr' hevFg
    have hpF : negInv p ∉ F '' H := fun hm => hpD (by
      have h1 := negInv_mem_H_diff_image (hFH hm)
      rwa [negInv_negInv'] at h1)
    exact tendsto_or_cobounded_of_tendsto_comp hab hgc hgH hFc hFd hpF hlim

/-- **The counterflow chart lands as `u ↑ b`** (mirror of `revChart_landing_right`). -/
theorem revChart_landing_left (hw : Continuous w) (hw0 : w 0 = 0) (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s)
    (hab : a < b) (hηc : ContinuousOn η (Ioo a b)) (hηD : ∀ u ∈ Ioo a b, η u ∈ H \ cfHullQ w s)
    (hp : Tendsto η (𝓝[<] b) (𝓝 p)) (hpD : p ∉ H \ cfHullQ w s) :
    (∃ x : ℝ, Tendsto (fun u => revChart w s (η u)) (𝓝[<] b) (𝓝 (x : ℂ))) ∨
      Tendsto (fun u => revChart w s (η u)) (𝓝[<] b) (Bornology.cobounded ℂ) := by
  have hmaps : MapsTo (fun u : ℝ => -u) (Ioo (-b) (-a)) (Ioo a b) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rcases revChart_landing_right (η := fun u => η (-u)) hw hw0 hβ hs (neg_lt_neg hab)
      (hηc.comp continuousOn_neg hmaps) (fun u hu => hηD _ (hmaps hu)) (tendsto_comp_neg_nhdsGT hp) hpD
    with ⟨x, hx⟩ | h
  · exact Or.inl ⟨x, tendsto_of_comp_neg_nhdsGT hx⟩
  · exact Or.inr (tendsto_of_comp_neg_nhdsGT h)

end Chart

/-! ### The post-contact excursion of (E1) is a chart crosscut -/

section Excursion

variable {w : ℝ → ℝ} {β : ℝ → ℂ} {s : ℝ} {η : ℝ → ℂ}

/-- A cluster point of a convergent curve is its limit. -/
theorem eq_of_mapClusterPt_of_tendsto {ι : Type*} {l : Filter ι} {f : ι → ℂ} {p q : ℂ} (hq : MapClusterPt q l f)
    (hp : Tendsto f l (𝓝 p)) : q = p :=
  eq_of_nhds_neBot (hq.neBot.mono (inf_le_inf_left _ hp))

/-- **An eastern end of an excursion is a landing point.** If the excursion of the proper arc `η` in `ℍ ∖ R(K_s)` on
`(t, u₀)` (`t ≥ 0`) hits the eastern side proper along `u ↑ u₀` (a cluster point of `Ψ ∘ η` in `(junR, ∞)`), then
`η(u₀) ∉ ℍ ∖ R(K_s)` and `Ψ ∘ η` **converges** as `u ↑ u₀` to a point of `(junR, ∞)`. -/
theorem exists_tendsto_revChart_of_hitsEastSideAlong (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s) {t u₀ : ℝ} (ht : 0 ≤ t) (htu : t < u₀)
    (hD : ∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s) (hhit : HitsEastSideAlong w s η (𝓝[Ioo t u₀] u₀)) :
    η u₀ ∉ H \ cfHullQ w s ∧
      ∃ x : ℝ, junR w s < x ∧ Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (x : ℂ)) := by
  obtain ⟨x, hx, hcl⟩ := hhit
  have hF : 𝓝[Ioo t u₀] u₀ ⊓ 𝓟 {u | η u ∈ H \ cfHullQ w s} ≤ 𝓝[<] u₀ :=
    inf_le_left.trans (nhdsWithin_Ioo_eq_nhdsLT htu).le
  have hcl' : MapClusterPt (x : ℂ) (𝓝[<] u₀) (fun u => revChart w s (η u)) := hcl.mono (map_mono hF)
  have hu₀ : 0 < u₀ := by linarith
  have hηcont : ContinuousAt η u₀ := hη.cont.continuousAt (Ici_mem_nhds hu₀)
  have hpD : η u₀ ∉ H \ cfHullQ w s := by
    intro hD0
    have hc : Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (revChart w s (η u₀))) :=
      (((continuousOn_revChart hw hs).continuousAt
        ((isOpen_H_diff_negInv_fwdHull hw hs).mem_nhds hD0)).tendsto.comp hηcont.tendsto).mono_left
        nhdsWithin_le_nhds
    have e := eq_of_mapClusterPt_of_tendsto hcl' hc
    have hH := revChart_mem_H hw hs hD0
    rw [← e] at hH
    exact lt_irrefl _ (show (0 : ℝ) < ((x : ℝ) : ℂ).im from hH)
  refine ⟨hpD, x, hx, ?_⟩
  have hηc : ContinuousOn η (Ioo t u₀) := hη.cont.mono fun v hv => le_of_lt (lt_of_le_of_lt ht hv.1)
  rcases revChart_landing_left hw hw0 hβ hs htu hηc hD (hηcont.tendsto.mono_left nhdsWithin_le_nhds) hpD with
    ⟨y, hy⟩ | hcob
  · rw [eq_of_mapClusterPt_of_tendsto hcl' hy]
    exact hy
  · exact absurd hcl' (not_mapClusterPt_of_tendsto_cobounded hcob _)

/-- **The last contact before a restart time.** If the proper arc `η` has met the complement of `ℍ ∖ R(K_s)` at some
time in `(0, t]` and `η(t) ∈ ℍ ∖ R(K_s)`, there is a last such time `τ₀ ∈ (0, t)`: `η(τ₀) ∉ ℍ ∖ R(K_s)` and
`η((τ₀, t]) ⊆ ℍ ∖ R(K_s)` (Lemma 5.4's "largest time `t ≤ τ` such that `η(t) ∈ K′_{τ′}`", p. 133). -/
theorem exists_lastContact (hη : IsProperArc η) (hw : Continuous w) (hs : 0 ≤ s) {t : ℝ}
    (hc : ∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s) (hD : η t ∈ H \ cfHullQ w s) :
    ∃ τ₀ ∈ Ioo 0 t, η τ₀ ∉ H \ cfHullQ w s ∧ ∀ v ∈ Ioc τ₀ t, η v ∈ H \ cfHullQ w s := by
  set S : Set ℝ := Icc 0 t ∩ η ⁻¹' (H \ cfHullQ w s)ᶜ with hS
  have hSc : IsClosed S := (hη.cont.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc
    (isOpen_H_diff_negInv_fwdHull hw hs).isClosed_compl
  obtain ⟨v, hv, hvD⟩ := hc
  have hvS : v ∈ S := ⟨⟨hv.1.le, hv.2⟩, hvD⟩
  have hbdd : BddAbove S := ⟨t, fun r hr => hr.1.2⟩
  have hmem := hSc.csSup_mem ⟨v, hvS⟩ hbdd
  have hvle : v ≤ sSup S := le_csSup hbdd hvS
  refine ⟨sSup S, ⟨lt_of_lt_of_le hv.1 hvle, lt_of_le_of_ne hmem.1.2 fun e => hmem.2 (e ▸ hD)⟩, hmem.2,
    fun r hr => ?_⟩
  by_contra hrD
  exact absurd (le_csSup hbdd ⟨⟨(lt_of_le_of_lt hmem.1.1 hr.1).le, hr.2⟩, hrD⟩) (not_le.2 hr.1)

/-- **The chart crosscut of a post-contact eastern excursion**: `η` runs in `ℍ ∖ R(K_s)` on `(τ₀, u₀)`, from a
contact time `τ₀` (`η(τ₀) ∉ ℍ ∖ R(K_s)`) to an end time `u₀` (`η(u₀) ∉ ℍ ∖ R(K_s)`); `Ψ ∘ η` lands as `u ↓ τ₀` at a
point of `ℝ ∪ {∞}`, and as `u ↑ u₀` at a point of the eastern side proper `(junR, ∞)`. In the chart `Ψ` this is a
crosscut of `ℍ` ending on the eastern side. -/
def IsEastCrosscut (w : ℝ → ℝ) (s : ℝ) (η : ℝ → ℂ) (τ₀ u₀ : ℝ) : Prop :=
  0 < τ₀ ∧ τ₀ < u₀ ∧ η τ₀ ∉ H \ cfHullQ w s ∧ η u₀ ∉ H \ cfHullQ w s ∧
    (∀ v ∈ Ioo τ₀ u₀, η v ∈ H \ cfHullQ w s) ∧
    ((∃ x₀ : ℝ, Tendsto (fun u => revChart w s (η u)) (𝓝[>] τ₀) (𝓝 (x₀ : ℂ))) ∨
      Tendsto (fun u => revChart w s (η u)) (𝓝[>] τ₀) (Bornology.cobounded ℂ)) ∧
    ∃ x₁ : ℝ, junR w s < x₁ ∧ Tendsto (fun u => revChart w s (η u)) (𝓝[<] u₀) (𝓝 (x₁ : ℂ))

/-- **A violation of (E1) is a chart crosscut** (deterministic). If `η` has met the complement of `ℍ ∖ R(K_s)` in
`(0, t]`, `η(t) ∈ ℍ ∖ R(K_s)`, and the excursion running at `t` ends on the eastern side proper at `u₀`, then the whole
excursion `(τ₀, u₀)` from the last contact `τ₀ < t` is an `IsEastCrosscut`. -/
theorem isEastCrosscut_of_hitsEastSideAlong (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s) {t u₀ : ℝ} (hc : ∃ v ∈ Ioc 0 t, η v ∉ H \ cfHullQ w s)
    (hDt : η t ∈ H \ cfHullQ w s) (htu : t < u₀) (hD : ∀ v ∈ Ioo t u₀, η v ∈ H \ cfHullQ w s)
    (hhit : HitsEastSideAlong w s η (𝓝[Ioo t u₀] u₀)) :
    ∃ τ₀ ∈ Ioo 0 t, IsEastCrosscut w s η τ₀ u₀ := by
  obtain ⟨τ₀, hτ₀, hτ₀D, hpost⟩ := exists_lastContact hη hw hs hc hDt
  obtain ⟨hu₀D, x₁, hx₁, hx₁lim⟩ :=
    exists_tendsto_revChart_of_hitsEastSideAlong hη hw hw0 hβ hs (hτ₀.1.le.trans hτ₀.2.le) htu hD hhit
  have hexc : ∀ v ∈ Ioo τ₀ u₀, η v ∈ H \ cfHullQ w s := fun v hv => by
    rcases le_or_gt v t with hvt | hvt
    · exact hpost v ⟨hv.1, hvt⟩
    · exact hD v ⟨hvt, hv.2⟩
  have hτu : τ₀ < u₀ := hτ₀.2.trans htu
  have hηc : ContinuousOn η (Ioo τ₀ u₀) := hη.cont.mono fun v hv => le_of_lt (hτ₀.1.trans hv.1)
  have hητ : Tendsto η (𝓝[>] τ₀) (𝓝 (η τ₀)) :=
    (hη.cont.continuousAt (Ici_mem_nhds hτ₀.1)).tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨τ₀, hτ₀, hτ₀.1, hτu, hτ₀D, hu₀D, hexc,
    revChart_landing_right hw hw0 hβ hs hτu hηc hexc hητ hτ₀D, x₁, hx₁, hx₁lim⟩

/-- **(E1) is the exclusion of eastern chart crosscuts** (deterministic reformulation of
`Prop51I.PostContactEastSideResidual`): for a proper arc `η` and a regular counterflow, if no `IsEastCrosscut` starts
in `(0, t)`, the residual holds at `t > 0`. -/
theorem postContactEastSideResidual_of_not_crosscut (hη : IsProperArc η) (hw : Continuous w) (hw0 : w 0 = 0)
    (hβ : IsLoewnerTrace w β) (hs : 0 ≤ s) {t : ℝ} (ht : 0 < t)
    (hno : ∀ τ₀ ∈ Ioo 0 t, ∀ u₀, t < u₀ → ¬ IsEastCrosscut w s η τ₀ u₀) :
    PostContactEastSideResidual w s t η := by
  intro hc hDt u₀ htu hD hhit
  obtain ⟨τ₀, hτ₀, hcross⟩ :=
    isEastCrosscut_of_hitsEastSideAlong hη hw hw0 hβ hs hc (hDt ht) htu hD hhit
  exact hno τ₀ hτ₀ u₀ htu hcross

end Excursion

end InteractingSLE.Sec5.Aux61Loc

/-! ### (E1) on the glued space as the exclusion of eastern chart crosscuts -/

namespace InteractingSLE.Sec5.Aux61Loc

open MeasureTheory ProbabilityTheory
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real
open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord CrossCond CrossCond.Word49 CrossCond.Theta MartChar.RealFlow LawUnique Cond44Ref Prop411Q
  CfRegQ Prop49Exit Prop51G Prop51H Prop51I

universe u

/-- **(E1) restated: no eastern chart crosscut after a contact**, almost surely on the glued space of
`Cond44Ref.Prop51QStatement`, at every positive rational counterflow time `s` and restart time `t`, on the regime
`G`: no excursion of the flow line in `ℍ ∖ R(K_s)` from a contact at `τ₀ ∈ (0, t)` to an end time `u₀ > t` is an
`IsEastCrosscut` (its `Ψ`-image a crosscut of `ℍ` landing on the eastern side proper). -/
def FwdNoEastCrosscutQOn (G : ℝ → ℝ → ℝ → Prop) : Prop :=
  GluedQ.{u} G fun s η w => ∀ t : ℚ, 0 < t → ∀ τ₀ ∈ Ioo (0 : ℝ) t, ∀ u₀ : ℝ, (t : ℝ) < u₀ →
    ¬ IsEastCrosscut w s η τ₀ u₀

/-- **(E1) from the exclusion of eastern chart crosscuts** (on any regime `G`), given the counterflow's regularity:
the deterministic reformulation `postContactEastSideResidual_of_not_crosscut` on the glued space. -/
theorem fwdPostContactEastSideQOn_of_noCrosscut {G : ℝ → ℝ → ℝ → Prop}
    (hreg : Prop51Q.CfLineRegularQStatement.{u}) (hno : FwdNoEastCrosscutQOn.{u} G) :
    FwdPostContactEastSideQOn.{u} G := by
  intro κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha Ω mΩ P _ h η ζ hh hfl Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  have hχ := Sec4.chiC_pos hκ hκ4
  have hθχ : θ₁ * chiC κ ≤ θ₂ * chiC κ := mul_le_mul_of_nonneg_right h12.le hχ.le
  have hF := Theorem15.isOrderedForceWord_flowLine (Sec7.prop74Data a b) {0} 0
  have h44 := Sec7.Lemma71H.cond44_flowLine_prop74Data (θ := θ₂) hκ (a := a) (b := b) ha (by linarith)
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hXm : Measurable fun ω => cfField κ (Exist.flowField 0 (θ₁ * chiC κ) (h ω)) :=
    (measurable_cfField κ).comp ((Exist.measurable_flowField 0 _).comp hh.1)
  have harc := ae_glue_fst (μ := P) k hXm (ae_isProperArc_of_isFlowLine hκ hκ4.le hadm hfl)
  have hregG := hreg κ hκ hκ4 a b θ₁ hb (by linarith) P h hh P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  filter_upwards [harc, hregG, hno κ hκ hκ4 a b θ₁ θ₂ h12 hG hb ha P h η ζ hh hfl P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs]
    with p hpa hpr hpn t ht
  obtain ⟨-, hwc, hw0, hβ, -, -⟩ := hpr
  exact postContactEastSideResidual_of_not_crosscut hpa hwc hw0 hβ (by exact_mod_cast hs.le)
    (by exact_mod_cast ht) (hpn t ht)

/-- **`Cond44Ref.Prop51QStatement` from Zhan's Part A inputs, the no-wrap topology and the exclusion of eastern chart
crosscuts below the critical gap** (`Prop51I.prop51QStatement_of_partA_of_eastSide` with (E1) in crosscut form). -/
theorem prop51QStatement_of_partA_of_noCrosscut (hA : PartAInputsSixteenDiv) (htopo : FwdNoWrapQStatement)
    (hno : FwdNoEastCrosscutQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Prop51QStatement.{u} :=
  prop51QStatement_of_partA_of_eastSide hA htopo
    (fwdPostContactEastSideQOn_of_noCrosscut (CfLineRegQ.cfLineRegularQStatement_of_partA hA) hno)

end InteractingSLE.Sec5.Aux61Loc
