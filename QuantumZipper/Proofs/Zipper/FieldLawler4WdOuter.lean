import QuantumZipper.Proofs.Zipper.FieldLawler4Wd
import QuantumZipper.Proofs.Zipper.FieldLawler3Polar
import QuantumZipper.Proofs.Zipper.FieldLawler3Sym

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-WD (outer piece): the `C_R` piece of `∂Wd`

Task FL4-WD, datum (ii) for the second symmetry step. For `Wd = fl4Wd W t R ε α β p₀`:

* `fl4wd_outer_nonempty`: `∂Wd ∩ C_R ≠ ∅` (otherwise `Z(Wd)` would be a bounded clopen part of
  the unbounded component `hullComp η'`);
* `fl4wd_chart`: with `J = {θ ∈ (0, π) | a half-disc of B(0,R) at R e^{iθ} lies in Wd}`,
  `FL3Arc Wd (fl3Chart R) J`;
* `fl4wd_outer_eq`: `fl3Chart R '' J ⊆ ∂Wd ∩ C_R ⊆ fl3Chart R '' J ∪ {tip, R, -R}`.

Own elementary point-set arguments (FL, EJP 20 (2015), p. 9, use the domain without comment).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- Frontier points of `Wd` in `D ∩ B(0,R)` are mapped into `closure η'`. -/
lemma fl4wd_frontier_closure_arc (hc : SideCtx W t F) {R ε α β : ℝ} {p₀ : ℂ} {η' : ℝ → ℂ}
    (hη : IsCrosscutH η') (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {x₀ : ℂ}
    (hx : x₀ ∈ frontier (fl4Wd W t R ε α β p₀)) (hD : x₀ ∈ H \ fwdHull W t) (hR : ‖x₀‖ < R) :
    fwdMap W t x₀ ∈ closure (arcH η') := by
  have hnot := fl4_frontier_cc_not_mem (fl4WdDom_isOpen hc R ε α β) p₀ hx
  have hxcl : x₀ ∈ closure (flCircArc ε α β) := by
    by_contra h
    exact hnot ⟨⟨hD.1, mem_ball_zero_iff.2 hR⟩, by rintro (h' | h'); exacts [hD.2 h', h h']⟩
  have hZ : ContinuousAt (fwdMap W t) x₀ :=
    hc.continuousOn_fwdMap.continuousAt (hc.isOpen_dom.mem_nhds hD)
  exact closure_mono (fl4wd_image_arc hc hη hηD) (hZ.continuousWithinAt.mem_closure_image hxcl)

/-- **(ii) nonempty.** `∂Wd ∩ C_R ≠ ∅`. -/
theorem fl4wd_outer_nonempty (hc : SideCtx W t F) {R ε α β : ℝ} {η' : ℝ → ℂ}
    (hη : IsCrosscutH η') {a b : ℝ} (ha : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hb : Tendsto η' (𝓝[<] 1) (𝓝 (b : ℂ))) (hab : a < b)
    (hηD : fwdMapInv W t '' arcH η' = flCircArc ε α β) {p₀ : ℂ}
    (hp : p₀ ∈ fl4WdDom W t R ε α β) (hpU : fwdMap W t p₀ ∈ hullComp η') :
    (frontier (fl4Wd W t R ε α β p₀) ∩ sphere 0 R).Nonempty := by
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
      refine lt_of_le_of_ne h2 fun e => hne ⟨F v, hxfr, by simpa using e⟩
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

/-- The angles of the "interior" points of the `C_R` piece: a half-disc of `B(0,R)` at
`R e^{iθ}` lies in `Wd`. -/
def fl4WdJ (W : ℝ → ℝ) (t R ε α β : ℝ) (p₀ : ℂ) : Set ℝ :=
  {θ | θ ∈ Ioo 0 π ∧ ∃ ρ > 0, ball (fl3Chart R θ) ρ ∩ ball 0 R ⊆ fl4Wd W t R ε α β p₀}

lemma fl4_chart_continuous (R : ℝ) : Continuous (fl3Chart R) := by
  unfold fl3Chart; fun_prop

lemma fl4_chart_norm {R : ℝ} (hR : 0 ≤ R) (z : ℂ) : ‖fl3Chart R z‖ = R * Real.exp (-z.im) := by
  simp [fl3Chart, Complex.norm_exp, abs_of_nonneg hR]

lemma fl4_chart_arg {R : ℝ} (hR : 0 < R) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    arg (fl3Chart R θ) = θ := by
  rw [fl3Chart, exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hR ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩

lemma fl4WdJ_isOpen (R ε α β : ℝ) (p₀ : ℂ) : IsOpen (fl4WdJ W t R ε α β p₀) := by
  rw [isOpen_iff_mem_nhds]
  rintro θ ⟨hθ, ρ, hρ, hsub⟩
  have hc : ContinuousAt (fun θ' : ℝ => fl3Chart R θ') θ :=
    ((fl4_chart_continuous R).comp continuous_ofReal).continuousAt
  filter_upwards [isOpen_Ioo.mem_nhds hθ,
    hc.eventually (ball_mem_nhds (fl3Chart R θ) (half_pos hρ))] with θ' h1 h2
  refine ⟨h1, ρ / 2, half_pos hρ, fun z hz => hsub ⟨?_, hz.2⟩⟩
  have := mem_ball.1 hz.1
  rw [mem_ball]
  linarith [dist_triangle z (fl3Chart R θ') (fl3Chart R θ)]

/-- **(ii) chart.** `fl3Chart R` is an `FL3Arc` chart of `Wd` over `J`. -/
theorem fl4wd_chart {R ε α β : ℝ} (hR : 0 < R) (p₀ : ℂ) :
    FL3Arc (fl4Wd W t R ε α β p₀) (fl3Chart R) (fl4WdJ W t R ε α β p₀) := by
  refine ⟨(fl4WdJ_isOpen R ε α β p₀).measurableSet, fun θ hθ => ?_, fun θ hθ θ' hθ' e => ?_⟩
  · obtain ⟨hθI, ρ, hρ, hsub⟩ := hθ
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.1
      ((fl4_chart_continuous R).continuousAt (x := (θ : ℂ))) ρ hρ
    refine ⟨r, hr, (by unfold fl3Chart; fun_prop : Differentiable ℂ (fl3Chart R)).differentiableOn,
      fun z hz => hsub ⟨mem_ball.2 (hball hz.2), ?_⟩, fun z hz hzim => ?_⟩
    · rw [mem_ball_zero_iff, fl4_chart_norm hR.le]
      have : Real.exp (-z.im) < 1 := by rw [Real.exp_lt_one_iff]; have h0 : 0 < z.im := hz.1; linarith
      nlinarith
    · set y := fl3Chart R z
      have hy : ‖y‖ = R := by rw [fl4_chart_norm hR.le, hzim]; simp
      have hyb : y ∈ ball (fl3Chart R θ) ρ := mem_ball.2 (hball hz)
      have ht : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * y) (𝓝[>] 0) (𝓝 y) := by
        have : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * y) (𝓝 0) (𝓝 (((1 - 0 : ℝ) : ℂ) * y)) :=
          ((continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
            continuous_const).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hev : ∀ᶠ s : ℝ in 𝓝[>] 0, ((1 - s : ℝ) : ℂ) * y ∈ fl4Wd W t R ε α β p₀ := by
        filter_upwards [ht.eventually (isOpen_ball.mem_nhds hyb), Ioo_mem_nhdsGT one_pos]
          with s h1 h2
        refine hsub ⟨h1, ?_⟩
        rw [mem_ball_zero_iff, norm_mul, hy, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith [h2.2])]
        nlinarith [h2.1]
      refine ⟨mem_closure_of_tendsto ht hev, fun hi => ?_⟩
      have := fl4wd_subset_ball (interior_subset hi)
      rw [mem_ball_zero_iff, hy] at this
      exact lt_irrefl _ this
  · have := congrArg arg e
    simp only at this
    rwa [fl4_chart_arg hR hθ.1, fl4_chart_arg hR hθ'.1] at this

/-- A point `x ∈ closure Wd ∩ C_R` in `ℍ` other than the tip is `fl3Chart R (arg x)` with
`arg x ∈ J`: a half-disc at `x` avoids `K_t ∪ closure ηD`, so it lies in `Wd`. -/
lemma fl4wd_mem_J (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (p₀ : ℂ) {x : ℂ}
    (hx : x ∈ closure (fl4Wd W t R ε α β p₀)) (hxR : ‖x‖ = R) (him : 0 < x.im)
    (htip : x ≠ trace W t) :
    arg x ∈ fl4WdJ W t R ε α β p₀ ∧ fl3Chart R (arg x) = x := by
  have hR : 0 < R := hε.trans hεR
  -- a neighbourhood of `x` avoiding `K ∪ closure ηD ∪ {im ≤ 0}`
  set Kc : Set ℂ := trace W '' Icc 0 t ∪ closure (flCircArc ε α β) ∪ {z : ℂ | z.im ≤ 0}
  have hKc : IsClosed Kc :=
    (((isCompact_Icc.image_of_continuousOn hc.trCont).isClosed).union isClosed_closure).union
      (isClosed_le Complex.continuous_im continuous_const)
  have hxK : x ∉ Kc := by
    rintro ((⟨s, hs, rfl⟩ | h) | h)
    · rcases hs.2.lt_or_eq with h' | h'
      · exact absurd hxR (ne_of_lt (hlt s ⟨hs.1, h'⟩))
      · exact htip (by rw [h'])
    · have := fl4_closure_arc_subset h
      rw [mem_sphere_zero_iff_norm, abs_of_pos hε, hxR] at this
      exact hεR.ne this.symm
    · exact absurd h (not_le.2 him)
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl x hxK
  have hK : fwdHull W t ⊆ trace W '' Icc 0 t := by
    rw [hc.hull]; exact image_mono Ioc_subset_Icc_self
  have hdom : ball x ρ ∩ ball 0 R ⊆ fl4WdDom W t R ε α β := by
    intro z hz
    have hzK := hρK hz.1
    refine ⟨⟨show 0 < z.im from lt_of_not_ge fun h => hzK (Or.inr h), hz.2⟩, ?_⟩
    rintro (h | h)
    · exact hzK (Or.inl (Or.inl (hK h)))
    · exact hzK (Or.inl (Or.inr h))
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff_nhds.1 hx _ (ball_mem_nhds x hρ)
  have hsub : ball x ρ ∩ ball 0 R ⊆ fl4Wd W t R ε α β p₀ := by
    have := ((convex_ball x ρ).inter (convex_ball 0 R)).isPreconnected.subset_connectedComponentIn
      ⟨hw1, fl4wd_subset_ball hw2⟩ hdom
    rwa [← connectedComponentIn_eq hw2] at this
  have hθ : arg x ∈ Ioo 0 π :=
    ⟨lt_of_le_of_ne (arg_nonneg_iff.2 him.le) fun e => by
        have := (arg_eq_zero_iff.1 e.symm).2; linarith,
      arg_lt_pi_iff.2 (Or.inr him.ne')⟩
  have hxe : fl3Chart R (arg x) = x := by
    rw [fl3Chart, ← hxR]; exact norm_mul_exp_arg_mul_I x
  exact ⟨⟨hθ, ρ, hρ, by rwa [hxe]⟩, hxe⟩

/-- **(ii) the `C_R` piece.** `fl3Chart R '' J ⊆ ∂Wd ∩ C_R ⊆ fl3Chart R '' J ∪ {tip, R, -R}`. -/
theorem fl4wd_outer_eq (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (p₀ : ℂ) :
    fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀) ⊆
        frontier (fl4Wd W t R ε α β p₀) ∩ sphere 0 R ∧
      frontier (fl4Wd W t R ε α β p₀) ∩ sphere 0 R ⊆
        fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀) ∪
          {trace W t, (R : ℂ), -(R : ℂ)} := by
  have hR : 0 < R := hε.trans hεR
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    obtain ⟨r, hr, -, -, hfr⟩ := (fl4wd_chart (W := W) (t := t) (ε := ε) (α := α) (β := β)
      hR p₀).chart θ hθ
    refine ⟨hfr θ (mem_ball_self hr) (by simp), ?_⟩
    rw [mem_sphere_zero_iff_norm, fl4_chart_norm hR.le]; simp
  · rintro x ⟨hx, hxs⟩
    have hxR : ‖x‖ = R := by simpa using hxs
    by_cases hE : x = trace W t ∨ x = (R : ℂ) ∨ x = -(R : ℂ)
    · right; simpa using hE
    left
    push Not at hE
    have hcl : closure (fl4Wd W t R ε α β p₀) ⊆ {z : ℂ | 0 ≤ z.im} :=
      closure_minimal (fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt (fl4wd_subset_D hz).1)
        (isClosed_le continuous_const Complex.continuous_im)
    have him : 0 < x.im := by
      rcases (show (0 : ℝ) ≤ x.im from hcl hx.1).lt_or_eq with h | h
      · exact h
      · exfalso
        have hre : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [← h])
        have : |x.re| = R := by rw [← hxR, hre, Complex.norm_real, Real.norm_eq_abs]; simp
        rcases (abs_eq hR.le).1 this with h' | h'
        · exact hE.2.1 (by rw [hre, h'])
        · exact hE.2.2 (by rw [hre, h']; simp)
    obtain ⟨hθ, hxe⟩ := fl4wd_mem_J hc hε hεR hlt p₀ hx.1 hxR him hE.1
    exact ⟨_, ⟨arg x, hθ, rfl⟩, hxe⟩

/-- A boundary point `x₀` of an open `Wd ⊆ B(0,R)` that is also a limit of points of
`B(0,R) \ Wd` is a limit of frontier points of `Wd` inside `B(0,R)` (segments cross `∂Wd`). -/
lemma fl4_closure_frontier_of {Wd : Set ℂ} {R : ℝ} (hWo : IsOpen Wd) (hWR : Wd ⊆ ball 0 R)
    {x₀ : ℂ} (h1 : x₀ ∈ closure Wd) (h2 : x₀ ∈ closure (ball 0 R \ Wd)) :
    x₀ ∈ closure (frontier Wd \ sphere 0 R) := by
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.1 h1 δ hδ
  obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.1 h2 δ hδ
  have hsR : segment ℝ w z ⊆ ball 0 R := (convex_ball 0 R).segment_subset (hWR hw) hz.1
  have hsδ : segment ℝ w z ⊆ ball x₀ δ :=
    (convex_ball x₀ δ).segment_subset (by rw [mem_ball, dist_comm]; exact hwd)
      (by rw [mem_ball, dist_comm]; exact hzd)
  by_contra hne
  have hsub : segment ℝ w z ⊆ Wd := by
    refine (convex_segment w z).isPreconnected.subset_of_closure_inter_subset hWo
      ⟨w, left_mem_segment ℝ w z, hw⟩ ?_
    rintro y ⟨hy1, hy2⟩
    by_contra hyW
    refine hne ⟨y, ⟨⟨hy1, by rwa [hWo.interior_eq]⟩, fun hys => ?_⟩, ?_⟩
    · have := mem_ball_zero_iff.1 (hsR hy2)
      rw [mem_sphere_zero_iff_norm] at hys
      linarith
    · have := hsδ hy2; rw [mem_ball, dist_comm] at this; exact this
  exact hz.2 (hsub (right_mem_segment ℝ w z))

/-- **(ii) harmonic measures agree.** A harmonic measure of the chart piece `fl3Chart R '' J`
in `Wd` is one of the whole `C_R` piece `∂Wd ∩ C_R`: the extra points `tip, ±R` are limits of
`∂Wd \ C_R`, where neither definition prescribes a limit. -/
theorem fl4wd_isHarmMeas_outer (hc : SideCtx W t F) {R ε α β : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (p₀ : ℂ) {V : ℂ → ℝ}
    (hV : IsHarmMeas (fl4Wd W t R ε α β p₀)
      (fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)) V) :
    IsHarmMeas (fl4Wd W t R ε α β p₀) (frontier (fl4Wd W t R ε α β p₀) ∩ sphere 0 R) V := by
  set Wd := fl4Wd W t R ε α β p₀
  set A := frontier Wd ∩ sphere 0 R
  set A' := fl3Chart R '' (((↑) : ℝ → ℂ) '' fl4WdJ W t R ε α β p₀)
  have hR : 0 < R := hε.trans hεR
  obtain ⟨hA'A, hAA'⟩ := fl4wd_outer_eq hc hε hεR hlt p₀
  have hWo : IsOpen Wd := fl4wd_open hc
  have hnotW : ∀ z : ℂ, z.im = 0 → z ∉ Wd := fun z hz hzW => by
    have := (fl4wd_subset_D hzW).1
    change 0 < z.im at this
    linarith
  have hreal : ∀ c : ℂ, c.im = 0 → ‖c‖ = R → c ∈ closure (ball 0 R \ Wd) := by
    intro c hc0 hcR
    have ht : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * c) (𝓝[>] 0) (𝓝 c) := by
      have : Tendsto (fun s : ℝ => ((1 - s : ℝ) : ℂ) * c) (𝓝 0) (𝓝 (((1 - 0 : ℝ) : ℂ) * c)) :=
        ((continuous_ofReal.comp (continuous_const.sub continuous_id)).mul
          continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT one_pos] with s hs
    refine ⟨?_, hnotW _ (by simp [hc0])⟩
    rw [mem_ball_zero_iff, norm_mul, hcR, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hs.2])]
    nlinarith [hs.1]
  have htip : trace W t ∈ closure (ball 0 R \ Wd) := by
    have htc : Tendsto (trace W) (𝓝[<] t) (𝓝 (trace W t)) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hc.tpos]
      exact (hc.trCont t (right_mem_Icc.2 hc.tpos.le)).tendsto.mono_left
        (nhdsWithin_mono _ Ioo_subset_Icc_self)
    refine mem_closure_of_tendsto htc ?_
    filter_upwards [Ioo_mem_nhdsLT hc.tpos] with s hs
    refine ⟨mem_ball_zero_iff.2 (hlt s ⟨hs.1.le, hs.2⟩), fun hsW => ?_⟩
    exact (fl4wd_subset_D hsW).2 (by rw [hc.hull]; exact ⟨s, ⟨hs.1, hs.2.le⟩, rfl⟩)
  have hkey : A \ A' ⊆ closure (frontier Wd \ A) := by
    rintro x ⟨hxA, hxA'⟩
    have hx3 : x = trace W t ∨ x = (R : ℂ) ∨ x = -(R : ℂ) := by
      rcases hAA' hxA with h | h
      · exact absurd h hxA'
      · simpa using h
    have hxR : ‖x‖ = R := by simpa using hxA.2
    have hcl : x ∈ closure (ball 0 R \ Wd) := by
      rcases hx3 with rfl | rfl | rfl
      · exact htip
      · exact hreal _ (by simp) hxR
      · exact hreal _ (by simp) hxR
    refine closure_mono ?_ (fl4_closure_frontier_of hWo fl4wd_subset_ball hxA.1.1 hcl)
    rintro y ⟨hy1, hy2⟩
    exact ⟨hy1, fun h => hy2 h.2⟩
  refine ⟨hV.harm, hV.mem01, fun x₀ hx₀ hnot => ?_, fun x₀ hx₀ hnot => ?_, fun hb => ?_⟩
  · by_cases hx' : x₀ ∈ A'
    · refine hV.one x₀ hx' fun h => hnot ?_
      refine closure_minimal ?_ isClosed_closure h
      rintro y ⟨hy1, hy2⟩
      by_cases hyA : y ∈ A
      · exact hkey ⟨hyA, hy2⟩
      · exact subset_closure ⟨hy1, hyA⟩
    · exact absurd (hkey ⟨hx₀, hx'⟩) hnot
  · exact hV.zero x₀ hx₀ fun h => hnot (closure_mono hA'A h)
  · exact hV.infty (hb.subset hA'A)

end FieldLawler
end QuantumZipper
