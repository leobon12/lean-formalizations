import QuantumZipper.Proofs.Zipper.FieldLawler4JintBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-JINT: the `C_R` piece of `∂Wd` is one of the two arcs beside the tip

Task FL4-JINT (Track A round 4). With `θ₀ = arg γ(t)` the tip angle and
`J = fl4WdJ W t R ε α β p₀` (angles of half-discs of `B(0,R)` at `R e^{iθ}` inside `Wd`):

* `fl4WdJ_tip_not_mem`: `θ₀ ∉ J` (points of `γ[0,t)` accumulate at the tip);
* `fl4WdJ_nonempty`: `J ≠ ∅` (as `fl4wd_outer_nonempty`, but a frontier point of `Wd` on `C_R`
  obtained there lies in `D`, hence is not the tip, hence has its angle in `J`);
* `fl4WdJ_not_both`: `J` does not meet both `(0, θ₀)` and `(θ₀, π)`. Otherwise (chaining,
  `fl4wd_interval_subset`) `±R ∈ closure Wd`, so half-discs at `±R` lie in `Wd`; real points
  `x₊ ≈ R`, `x₋ ≈ -R` of these half-discs are `F u₊`, `F u₋` with `u₊ > 0 > u₋`
  (`fl4j_pos_preimage`, `fl4j_neg_preimage`), and `u₊, u₋ ∈ closure Z_t(Wd)`. This contradicts
  the separation `fl3top_no_cross` (the hull separates the half-disc);
* `fl4WdJ_eq`: `J = (0, θ₀)` or `J = (θ₀, π)`; `fl4WdJ_eq_Ioo`: `∃ A < B, J = (A, B)`.

Own elementary point-set arguments (Field–Lawler, *Escape probability and transience for SLE*,
EJP 20 (2015), p. 9, use the domain without comment; no published proof of this step found).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl4j_tip_arg_mem (hH : trace W t ∈ H) : arg (trace W t) ∈ Ioo 0 π := by
  have : (0 : ℝ) < (trace W t).im := hH
  exact ⟨lt_of_le_of_ne (arg_nonneg_iff.2 this.le) fun e => by
    have := (arg_eq_zero_iff.1 e.symm).2; linarith, arg_lt_pi_iff.2 (Or.inr this.ne')⟩

/-- **(a) the tip angle is not in `J`.** -/
theorem fl4WdJ_tip_not_mem (hc : SideCtx W t F) {R ε α β : ℝ}
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hnorm : ‖trace W t‖ = R) (p₀ : ℂ) :
    arg (trace W t) ∉ fl4WdJ W t R ε α β p₀ := by
  rintro ⟨-, ρ, hρ, hsub⟩
  have he : fl3Chart R (arg (trace W t)) = trace W t := by
    rw [fl3Chart, ← hnorm]; exact norm_mul_exp_arg_mul_I _
  rw [he] at hsub
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1
    (fl4wd_tip_closure hc hlt p₀ (ε := ε) (α := α) (β := β)) _ (ball_mem_nhds _ hρ)
  exact hw2.2 (hsub ⟨hw1, hw2.1⟩)

/-- **(c) `J` is nonempty.** -/
theorem fl4WdJ_nonempty (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) {η' : ℝ → ℂ}
    (hη : IsCrosscutH η') {a b : ℝ} (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a < b)
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    (fl4WdJ W t R ε α β p₀).Nonempty := by
  by_contra hne
  set Wd := fl4Wd W t R ε α β p₀
  set U := fwdMap W t '' Wd
  set S := H \ arcH η'
  have hSo : IsOpen S := lwExc_isOpen_H_diff_arc hη
  have hUo : IsOpen U := fl3cmp_image_isOpen hc (fl4wd_open hc) fl4wd_subset_D
  obtain ⟨-, -, -, -, -, hclfr, -⟩ := fl3u_FL3Unif_pieces hη ha hb hab
  have hHo := lwExc_hullComp_isOpen hη
  have hclo : closure U ∩ connectedComponentIn S (fwdMap W t p₀) ⊆ U := by
    rintro v ⟨hvU, hvC⟩
    have hvS : v ∈ S := connectedComponentIn_subset _ _ hvC
    have hvH : v ∈ H := hvS.1
    have hxD := hc.F_mem_dom hvH
    have hZx := hc.fwdMap_F hvH
    have hFc : ContinuousAt F v := hc.Fcont.continuousAt (mem_nhds_iff.2
      ⟨H, fun z (hz : 0 < z.im) => (le_of_lt hz : (0 : ℝ) ≤ z.im),
        isOpen_lt continuous_const Complex.continuous_im, hvH⟩)
    have hxcl : F v ∈ closure Wd := by
      have h1 := hFc.continuousWithinAt.mem_closure_image hvU
      refine closure_mono ?_ h1
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [hc.F_fwdMap (fl4wd_subset_D hz)]; exact hz
    by_contra hvnot
    have hxW : F v ∉ Wd := fun h => hvnot ⟨F v, h, hZx⟩
    have hxfr : F v ∈ frontier Wd := ⟨hxcl, by rwa [(fl4wd_open hc).interior_eq]⟩
    have hxR : ‖F v‖ < R := by
      have h1 : closure Wd ⊆ closedBall 0 R :=
        closure_minimal (fl4wd_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
      have h2 := h1 hxcl
      rw [mem_closedBall_zero_iff] at h2
      refine lt_of_le_of_ne h2 fun e => hne ⟨_, (fl4wd_mem_J hc hε hεR hlt p₀ hxcl e hxD.1
        fun h => hc.tip_not_mem (h ▸ hxD)).1⟩
    have h1 := hclfr (fl4wd_frontier_closure_arc hc hη hηD hxfr hxD hxR)
    rw [hZx] at h1
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 h1.1 _
      ((hSo.connectedComponentIn).mem_nhds (mem_connectedComponentIn hvS))
    have : v ∈ hullComp η' := ⟨hvS, by rw [connectedComponentIn_eq hw1]; exact hw2.2⟩
    rw [hHo.frontier_eq] at h1
    exact h1.2 this
  have hsub : connectedComponentIn S (fwdMap W t p₀) ⊆ U :=
    isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hUo
      ⟨_, mem_connectedComponentIn hpU.1, p₀, mem_connectedComponentIn hp, rfl⟩ hclo
  obtain ⟨C, hC⟩ := hc.bound
  refine hpU.2 ((isBounded_closedBall (x := (0 : ℂ)) (r := R + C)).subset
    (hsub.trans ?_))
  rintro _ ⟨z, hz, rfl⟩
  have h1 := (flWire_norm_le hc hC (fl4wd_subset_D hz)).1
  have h2 := mem_ball_zero_iff.1 (fl4wd_subset_ball hz)
  rw [mem_closedBall_zero_iff]; linarith

/-- A real point `F u = x` with a half-disc at `x` inside `Wd` gives `u ∈ closure Z_t(Wd)`. -/
lemma fl4j_mem_closure_image (hc : SideCtx W t F) {Wd : Set ℂ} {u x ρ : ℝ}
    (hFu : F u = x) (hρ : 0 < ρ) (hball : ∀ z ∈ ball (x : ℂ) ρ, 0 < z.im → z ∈ Wd) :
    (u : ℂ) ∈ closure (fwdMap W t '' Wd) := by
  refine mem_closure_of_tendsto (fl4j_vert_tendsto u) ?_
  have hT := fl4j_F_vert hc u
  rw [hFu] at hT
  filter_upwards [hT.eventually (ball_mem_nhds _ hρ), self_mem_nhdsWithin] with s hs (hs0 : 0 < s)
  have hm := fl4j_vert_mem (u := u) hs0
  exact ⟨F ((u : ℂ) + s * I), hball _ hs (hc.F_mem_dom hm).1, hc.fwdMap_F hm⟩

lemma fl4j_ball_sub {c x r ρ R : ℝ} (hxc : |x - c| = r) (h2 : 2 * r ≤ ρ) (hx : |x| + r ≤ R)
    {z : ℂ} (hz : z ∈ ball (x : ℂ) r) : z ∈ ball (c : ℂ) ρ ∧ z ∈ ball (0 : ℂ) R := by
  rw [mem_ball] at hz
  have e1 : dist (x : ℂ) (c : ℂ) = |x - c| := by
    rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
  have e2 : dist (x : ℂ) 0 = |x| := by rw [dist_zero_right, norm_real, Real.norm_eq_abs]
  have hr : 0 ≤ r := hxc ▸ abs_nonneg _
  refine ⟨mem_ball.2 ?_, mem_ball.2 ?_⟩
  · linarith [dist_triangle z (x : ℂ) (c : ℂ)]
  · linarith [dist_triangle z (x : ℂ) 0]

/-- **(b) `J` does not meet both arcs beside the tip.** -/
theorem fl4WdJ_not_both (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hnorm : ‖trace W t‖ = R) (hH : trace W t ∈ H)
    {p₀ : ℂ} (hp : p₀ ∈ fl4WdDom W t R ε α β) {θ₁ θ₂ : ℝ}
    (hθ₁ : θ₁ ∈ fl4WdJ W t R ε α β p₀) (h₁ : θ₁ < arg (trace W t))
    (hθ₂ : θ₂ ∈ fl4WdJ W t R ε α β p₀) (h₂ : arg (trace W t) < θ₂) : False := by
  have hR : 0 < R := hε.trans hεR
  set Wd := fl4Wd W t R ε α β p₀
  set θt := arg (trace W t)
  have hθt := fl4j_tip_arg_mem hH
  set g : ℝ → ℂ := fun θ => fl3Chart R θ
  have hg : Continuous g := (fl4_chart_continuous R).comp continuous_ofReal
  have hJW : ∀ φ ∈ fl4WdJ W t R ε α β p₀, g φ ∈ closure Wd := fun φ hφ =>
    ((fl4wd_outer_eq hc hε hεR hlt p₀).1 ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩).1.1
  have hsub₁ := fl4wd_interval_subset hc hε hεR hlt p₀ (a' := 0) (b' := θt)
    (fun φ hφ => ⟨hφ.1, hφ.2.trans hθt.2⟩) (fun h' => lt_irrefl _ h'.2) ⟨hθ₁.1.1, h₁⟩ hθ₁
  have hsub₂ := fl4wd_interval_subset hc hε hεR hlt p₀ (a' := θt) (b' := π)
    (fun φ hφ => ⟨hθt.1.trans hφ.1, hφ.2⟩) (fun h' => lt_irrefl _ h'.1) ⟨h₂, hθ₂.1.2⟩ hθ₂
  have hRc : ((R : ℝ) : ℂ) ∈ closure Wd := by
    have ht : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := hg.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have h0 : g 0 = R := by simp [g, fl3Chart]
    rw [h0] at ht
    rw [← closure_closure (s := Wd)]
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT hθt.1] with φ hφ
    exact hJW φ (hsub₁ hφ)
  have hRm : ((-R : ℝ) : ℂ) ∈ closure Wd := by
    have ht : Tendsto g (𝓝[<] π) (𝓝 (g π)) := hg.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
    have h0 : g π = ((-R : ℝ) : ℂ) := by simp [g, fl3Chart, exp_pi_mul_I]
    rw [h0] at ht
    rw [← closure_closure (s := Wd)]
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hθt.2] with φ hφ
    exact hJW φ (hsub₂ hφ)
  obtain ⟨ρ₁, hρ₁, hW₁, hK₁⟩ := fl4j_halfdisk hc hε hεR hlt hH (c := R) (abs_of_pos hR) hRc
  obtain ⟨ρ₂, hρ₂, hW₂, hK₂⟩ := fl4j_halfdisk hc hε hεR hlt hH (c := -R)
    (by rw [abs_neg, abs_of_pos hR]) hRm
  have hle : ∀ z ∈ trace W '' Icc 0 t, ‖z‖ ≤ R := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hs.2.lt_or_eq with h | h
    · exact (hlt s ⟨hs.1, h⟩).le
    · rw [h, hnorm]
  have hre : ∀ z ∈ trace W '' Icc 0 t, z.im = 0 → ∀ c : ℝ, ‖z - c‖ = |z.re - c| := by
    intro z _ hzi c
    have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hzi])
    rw [this, ← ofReal_sub, norm_real, Real.norm_eq_abs]; simp
  have habs : ∀ z ∈ trace W '' Icc 0 t, |z.re| ≤ R := fun z hz =>
    (abs_re_le_norm z).trans (hle z hz)
  -- the right real point
  set r₁ := min ρ₁ R / 2
  have hr₁d : r₁ = min ρ₁ R / 2 := rfl
  have hr₁ : 0 < r₁ := by positivity
  have hr₁ρ : 2 * r₁ ≤ ρ₁ := by have := min_le_left ρ₁ R; linarith
  have hr₁R : r₁ ≤ R / 2 := by have := min_le_right ρ₁ R; linarith
  obtain ⟨u₁, hu₁, hFu₁⟩ := fl4j_pos_preimage hc (x := R - r₁) hle fun z hz hzi => by
    have h1 := hK₁ z hz
    rw [hre z hz hzi] at h1
    have h2 := (abs_le.1 (habs z hz)).2
    rw [abs_of_nonpos (by linarith)] at h1
    linarith
  -- the left real point
  set r₂ := min ρ₂ R / 2
  have hr₂d : r₂ = min ρ₂ R / 2 := rfl
  have hr₂ : 0 < r₂ := by positivity
  have hr₂ρ : 2 * r₂ ≤ ρ₂ := by have := min_le_left ρ₂ R; linarith
  have hr₂R : r₂ ≤ R / 2 := by have := min_le_right ρ₂ R; linarith
  obtain ⟨u₂, hu₂, hFu₂⟩ := fl4j_neg_preimage hc (x := -R + r₂) hle fun z hz hzi => by
    have h1 := hK₂ z hz
    rw [hre z hz hzi] at h1
    have h2 := (abs_le.1 (habs z hz)).1
    rw [abs_of_nonneg (by linarith)] at h1
    linarith
  -- `Ω = Z_t(Wd)`
  set Ω := fwdMap W t '' Wd
  have hΩo : IsOpen Ω := fl3cmp_image_isOpen hc (fl4wd_open hc) fl4wd_subset_D
  have hΩc : IsConnected Ω := (isConnected_connectedComponentIn_iff.2 hp).image _
    (hc.continuousOn_fwdMap.mono fl4wd_subset_D)
  have hΩH : Ω ⊆ H := by rintro _ ⟨z, hz, rfl⟩; exact hc.mapsTo (fl4wd_subset_D hz)
  have hΩF : ∀ z ∈ Ω, ‖fwdMapInv W t z‖ < R := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hc.Feq (hc.mapsTo (fl4wd_subset_D hz)), hc.F_fwdMap (fl4wd_subset_D hz)]
    exact mem_ball_zero_iff.1 (fl4wd_subset_ball hz)
  have hcl₁ : (u₁ : ℂ) ∈ closure Ω := fl4j_mem_closure_image hc hFu₁ hr₁ fun z hz hzi => by
    obtain ⟨h1, h2⟩ := fl4j_ball_sub (c := R) (ρ := ρ₁) (R := R)
      (by rw [show R - r₁ - R = -r₁ by ring, abs_neg, abs_of_pos hr₁])
      (by linarith) (by rw [abs_of_pos (by linarith)]; linarith) hz
    exact hW₁ z h1 h2 hzi
  have hcl₂ : (u₂ : ℂ) ∈ closure Ω := fl4j_mem_closure_image hc hFu₂ hr₂ fun z hz hzi => by
    obtain ⟨h1, h2⟩ := fl4j_ball_sub (c := -R) (ρ := ρ₂) (R := R)
      (by rw [show -R + r₂ - -R = r₂ by ring, abs_of_pos hr₂])
      (by linarith) (by rw [abs_of_neg (by linarith)]; linarith) hz
    exact hW₂ z h1 h2 hzi
  refine fl3top_no_cross hc hH hnorm (fun z hz => hle z (fl4j_hull_sub hc hz)) hΩo hΩc hΩH hΩF
    hu₂ hu₁ hcl₂ hcl₁ ?_ ?_
  · rw [hFu₂, norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; linarith
  · rw [hFu₁, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith

/-- **FL4-JINT.** `J` is one of the two arcs of `(0, π)` beside the tip angle. -/
theorem fl4WdJ_eq (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hnorm : ‖trace W t‖ = R) (hH : trace W t ∈ H)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ} (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a < b)
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    fl4WdJ W t R ε α β p₀ = Ioo 0 (arg (trace W t)) ∨
      fl4WdJ W t R ε α β p₀ = Ioo (arg (trace W t)) π := by
  set J := fl4WdJ W t R ε α β p₀
  set θt := arg (trace W t)
  have hθt := fl4j_tip_arg_mem hH
  have htJ : θt ∉ J := fl4WdJ_tip_not_mem hc hlt hnorm p₀
  obtain ⟨θ, hθ⟩ := fl4WdJ_nonempty hc hε hεR hlt hη ha hb hab hηD hp hpU
  have hne : θ ≠ θt := fun e => htJ (e ▸ hθ)
  rcases lt_or_gt_of_ne hne with h | h
  · left
    ext φ
    refine ⟨fun hφ => ⟨hφ.1.1, lt_of_le_of_ne (not_lt.1 fun h' =>
        fl4WdJ_not_both hc hε hεR hlt hnorm hH hp hθ h hφ h') fun e => htJ (e ▸ hφ)⟩,
      fun hφ => fl4wd_interval_subset hc hε hεR hlt p₀ (a' := 0) (b' := θt)
        (fun φ hφ => ⟨hφ.1, hφ.2.trans hθt.2⟩) (fun h' => lt_irrefl _ h'.2) ⟨hθ.1.1, h⟩ hθ hφ⟩
  · right
    ext φ
    refine ⟨fun hφ => ⟨lt_of_le_of_ne (not_lt.1 fun h' =>
        fl4WdJ_not_both hc hε hεR hlt hnorm hH hp hφ h' hθ h) fun e => htJ (e.symm ▸ hφ),
        hφ.1.2⟩,
      fun hφ => fl4wd_interval_subset hc hε hεR hlt p₀ (a' := θt) (b' := π)
        (fun φ hφ => ⟨hθt.1.trans hφ.1, hφ.2⟩) (fun h' => lt_irrefl _ h'.1) ⟨h, hθ.1.2⟩ hθ hφ⟩

/-- **FL4-JINT (interval form).** `J = (A, B)` for some `A < B`. -/
theorem fl4WdJ_eq_Ioo (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hnorm : ‖trace W t‖ = R) (hH : trace W t ∈ H)
    {η' : ℝ → ℂ} (hη : IsCrosscutH η') {a b : ℝ} (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a < b)
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    ∃ A B : ℝ, A < B ∧ fl4WdJ W t R ε α β p₀ = Ioo A B := by
  have hθt := fl4j_tip_arg_mem hH
  rcases fl4WdJ_eq hc hε hεR hlt hnorm hH hη ha hb hab hηD hp hpU with h | h
  · exact ⟨_, _, hθt.1, h⟩
  · exact ⟨_, _, hθt.2, h⟩

end FieldLawler
end QuantumZipper
