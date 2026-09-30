import QuantumZipper.Proofs.Zipper.FieldLawler3Wire
import QuantumZipper.Proofs.Zipper.FieldLawler3TopSep
import QuantumZipper.Proofs.Zipper.FieldLawler2Glue

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-CMP: FL (2.1) in maximum-principle form for one positive image crosscut

Task FL3-CMP (Track A, input of `FieldLawler.FLImageSumBoundStmt`).

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20
(2015) no. 10, arXiv:1407.3314, (2.1) (p. 5–6) as used in the proof of Prop. 3.4 (p. 9):
`ℰ_D(ηⱼ, γ̃) ≤ ℰ_D(ηⱼ, C_R)` — an excursion from `ηⱼ` to the far boundary must first cross `C_R`.
FL state it as an excursion-measure monotonicity; here it is in the pointwise harmonic-function
form (monotonicity of harmonic measure under domain inclusion, by the maximum principle, the
standard proof of FL (2.1); Garnett–Marshall, *Harmonic Measure*, Ch. I, Lemma 1.1 is the
maximum principle used, `fl2_harm_le_zero_off_finite`).

Setting: `D = ℍ \ K_t`, `Z = fwdMap W t`, `η'` an image crosscut with foot `a > 0`, lying in
`Z(D ∩ C_ε)`, `G` the harmonic measure of `(-N, 0)` in `hullComp η'`; `Wd ⊆ D ∩ B(0, R)` open,
connected, with `Z(Wd) ⊆ hullComp η'` and `η' ⊆ closure (Z Wd)`; `V` the harmonic measure of the
outer piece `∂Wd ∩ C_R` in `Wd`.

* `fl3cmp_le` (TARGET 1): `G ∘ Z ≤ V` on `Wd`.
* `fl3cmp_excR_le` (TARGET 2): for a chart `ψ` mapping short vertical segments above `J` into
  `Wd`, `excR (G ∘ Z ∘ ψ) J ≤ excR (V ∘ ψ) J`, given a vertical derivative of `V ∘ ψ` on `J`.

Abstract hypotheses on `Wd` (beyond open, connected, `⊆ D ∩ B(0,R)`, the two arc conditions):
`hWfr` (inside the ball, frontier points of `Wd` in `D` are mapped outside `hullComp η'`, true
for a component of `D ∩ B(0,R) ∩ Z⁻¹(hullComp η')`), and a finite set `E` containing
`closure (∂Wd \ C_R) ∩ C_R` (the points where the outer piece meets the rest of `∂Wd`; in the
Loewner setting the tip and `±R`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

lemma fl3cmp_closure_neg {N : ℝ} :
    closure (ofReal '' Ioo (-N) 0 : Set ℂ) ⊆ {z : ℂ | z.im = 0 ∧ z.re ≤ 0} := by
  refine closure_minimal ?_ ((isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le Complex.continuous_re continuous_const))
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨by simp, by simpa using hx.2.le⟩

lemma fl3cmp_image_eq (hc : SideCtx W t F) {Wd : Set ℂ} (hWD : Wd ⊆ H \ fwdHull W t) :
    fwdMap W t '' Wd = H ∩ F ⁻¹' Wd := by
  ext u
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨hc.mapsTo (hWD hz), by rw [mem_preimage, hc.F_fwdMap (hWD hz)]; exact hz⟩
  · rintro ⟨hu, hF⟩
    exact ⟨F u, hF, hc.fwdMap_F hu⟩

lemma fl3cmp_image_isOpen (hc : SideCtx W t F) {Wd : Set ℂ} (hWo : IsOpen Wd)
    (hWD : Wd ⊆ H \ fwdHull W t) : IsOpen (fwdMap W t '' Wd) := by
  rw [fl3cmp_image_eq hc hWD]
  exact (hc.Fcont.mono fun z (hz : 0 < z.im) => (le_of_lt hz : (0 : ℝ) ≤ z.im)).isOpen_inter_preimage
    (isOpen_lt continuous_const Complex.continuous_im) hWo

/-- **Rough frontier points.** At a frontier point `x₀ ∉ D` of `Wd` inside `B(0, R)`, `G ∘ Z → 0`:
every subsequential limit of `Z zₙ` is a real `u₀ > 0` (`fl3top_pos_of_foot`), outside
`[-N, 0]`. -/
theorem fl3cmp_tendsto_rough (hc : SideCtx W t F) {R ε : ℝ} (hεR : ε < R) (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {η' : ℝ → ℂ} {a : ℝ}
    (hη : IsCrosscutH η') (ha : 0 < a) (hηa : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hηε : arcH η' ⊆ {p | ‖fwdMapInv W t p‖ = ε}) {N : ℝ} {G : ℂ → ℝ}
    (hG : IsHarmMeas (hullComp η') (ofReal '' Ioo (-N) 0) G) {Wd : Set ℂ} (hWo : IsOpen Wd)
    (hWc : IsConnected Wd) (hWD : Wd ⊆ H \ fwdHull W t) (hWR : Wd ⊆ ball 0 R)
    (hWU : fwdMap W t '' Wd ⊆ hullComp η') (hWarc : arcH η' ⊆ closure (fwdMap W t '' Wd))
    {x₀ : ℂ} (hx₀ : x₀ ∉ H \ fwdHull W t) (hx₀R : ‖x₀‖ < R) :
    Tendsto (fun z => G (fwdMap W t z)) (𝓝[Wd] x₀) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bound
  have hHH : ∀ z : ℂ, z ∈ H → z ∈ Hbar := fun z hz => (le_of_lt (hz : 0 < z.im) : 0 ≤ z.im)
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  have hΩ : ∀ᶠ n in atTop, ns n ∈ Wd := (tendsto_nhdsWithin_iff.1 hns).2
  have hns' : Tendsto ns atTop (𝓝 x₀) := (tendsto_nhdsWithin_iff.1 hns).1
  have hball : ∀ᶠ n in atTop, ns n ∈ ball x₀ 1 := hns'.eventually (ball_mem_nhds _ one_pos)
  set w : ℕ → ℂ := fun n => fwdMap W t (ns n) with hw
  have hs : Bornology.IsBounded (Hbar ∩ closedBall 0 (‖x₀‖ + 1 + C)) :=
    isBounded_closedBall.subset inter_subset_right
  have hfreq : ∃ᶠ n in atTop, w n ∈ Hbar ∩ closedBall 0 (‖x₀‖ + 1 + C) := by
    refine (hΩ.and hball).frequently.mono ?_
    rintro n ⟨hn, hnb⟩
    refine ⟨hHH _ (hc.mapsTo (hWD hn)), ?_⟩
    have h1 := (flWire_norm_le hc hC (hWD hn)).1
    have e2 : ‖ns n‖ ≤ ‖x₀‖ + ‖ns n - x₀‖ := by simpa using norm_add_le x₀ (ns n - x₀)
    have e3 : ‖ns n - x₀‖ < 1 := by rw [← dist_eq_norm]; exact hnb
    rw [mem_closedBall, dist_zero_right]
    linarith
  obtain ⟨a', ha', φ, hφ, hlim⟩ := tendsto_subseq_of_frequently_bounded hs hfreq
  have hHbar : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
  have haH : a' ∈ Hbar := hHbar.closure_subset (closure_mono inter_subset_left ha')
  have hnsφ : Tendsto (ns ∘ φ) atTop (𝓝[Wd] x₀) := hns.comp hφ.tendsto_atTop
  have hΩφ : ∀ᶠ n in atTop, ns (φ n) ∈ Wd := (tendsto_nhdsWithin_iff.1 hnsφ).2
  have hFa : F a' = x₀ := by
    have h1 : Tendsto (fun n => F (w (φ n))) atTop (𝓝 (F a')) :=
      (hc.Fcont a' haH).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hlim, hΩφ.mono fun n hn => hHH _ (hc.mapsTo (hWD hn))⟩)
    have h2 : Tendsto (fun n => F (w (φ n))) atTop (𝓝 x₀) :=
      (tendsto_nhdsWithin_iff.1 hnsφ).1.congr'
        (hΩφ.mono fun n hn => (hc.F_fwdMap (hWD hn)).symm)
    exact tendsto_nhds_unique h1 h2
  have ha0 : a'.im = 0 := by
    rcases (show 0 ≤ a'.im from haH).lt_or_eq with h | h
    · exact absurd (hFa ▸ hc.F_mem_dom h) hx₀
    · exact h.symm
  have hare : ((a'.re : ℝ) : ℂ) = a' := Complex.ext (by simp) (by simp [ha0])
  have hΩimg : ∀ᶠ n in atTop, w (φ n) ∈ fwdMap W t '' Wd :=
    hΩφ.mono fun n hn => ⟨_, hn, rfl⟩
  have hacl : a' ∈ closure (fwdMap W t '' Wd) := mem_closure_of_tendsto hlim hΩimg
  have hpos : 0 < a'.re := by
    refine fl3top_pos_of_foot hc hεR hH hnorm hle (fl3cmp_image_isOpen hc hWo hWD)
      (hWc.image _ (hc.continuousOn_fwdMap.mono hWD)) (fun u hu => (hWU hu).1.1) ?_ ha hηa
      hη.2.2.1 hηε hWarc (by rw [hare]; exact hacl) (by rw [hare, hFa]; exact hx₀R)
    rintro _ ⟨z, hz, rfl⟩
    rw [hc.Feq (hc.mapsTo (hWD hz)) |>.symm, hc.F_fwdMap (hWD hz)]
    simpa using hWR hz
  have haA : a' ∉ closure (ofReal '' Ioo (-N) 0 : Set ℂ) := fun h =>
    absurd (fl3cmp_closure_neg h).2 (not_le.2 hpos)
  have hU' : Tendsto (w ∘ φ) atTop (𝓝[hullComp η'] a') :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, hΩimg.mono fun n hn => hWU hn⟩
  have haU : a' ∈ frontier (hullComp η') := by
    refine ⟨mem_closure_of_tendsto hlim (hΩimg.mono fun n hn => hWU hn), fun hi => ?_⟩
    have h' : 0 < a'.im := (interior_subset hi : a' ∈ hullComp η').1.1
    rw [ha0] at h'
    exact lt_irrefl _ h'
  exact ⟨φ, (hG.zero a' haU haA).comp hU'⟩

/-- **TARGET 1 (FL (2.1), maximum-principle form).** `G ∘ Z ≤ V` on `Wd`: Lindelöf's maximum
principle for `G ∘ Z - V` on `Wd`. On the outer piece `V → 1 ≥ G ∘ Z` (off the finite set `E`);
inside the ball `G ∘ Z → 0`, at points of `D` because they map to the frontier of
`hullComp η'` in `ℍ` (away from the real interval), and at rough points by
`fl3cmp_tendsto_rough`. -/
theorem fl3cmp_le (hc : SideCtx W t F) {R ε : ℝ} (hεR : ε < R) (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {η' : ℝ → ℂ} {a : ℝ}
    (hη : IsCrosscutH η') (ha : 0 < a) (hηa : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hηε : arcH η' ⊆ {p | ‖fwdMapInv W t p‖ = ε}) {N : ℝ} {G : ℂ → ℝ}
    (hG : IsHarmMeas (hullComp η') (ofReal '' Ioo (-N) 0) G) {Wd : Set ℂ} (hWo : IsOpen Wd)
    (hWc : IsConnected Wd) (hWD : Wd ⊆ H \ fwdHull W t) (hWR : Wd ⊆ ball 0 R)
    (hWU : fwdMap W t '' Wd ⊆ hullComp η') (hWarc : arcH η' ⊆ closure (fwdMap W t '' Wd))
    (hWfr : ∀ x₀ ∈ frontier Wd, x₀ ∈ H \ fwdHull W t → ‖x₀‖ < R →
      fwdMap W t x₀ ∉ hullComp η')
    (E : Finset ℂ) (hE : closure (frontier Wd \ sphere 0 R) ∩ sphere 0 R ⊆ E) {V : ℂ → ℝ}
    (hV : IsHarmMeas Wd (frontier Wd ∩ sphere 0 R) V) :
    ∀ z ∈ Wd, G (fwdMap W t z) ≤ V z := by
  have hWpull : Wd ⊆ flPull W t (hullComp η') := fun z hz => ⟨hWD hz, hWU ⟨z, hz, rfl⟩⟩
  have hG1 : ∀ z ∈ Wd, 0 ≤ G (fwdMap W t z) ∧ G (fwdMap W t z) ≤ 1 := fun z hz =>
    hG.mem01 _ (hWU ⟨z, hz, rfl⟩)
  have hharm : InnerProductSpace.HarmonicOnNhd ((fun z => G (fwdMap W t z)) - V) Wd :=
    fun z hz => (flWire_harm_comp hc hG.harm z (hWpull hz)).sub (hV.harm z hz)
  have hbdd : BddAbove (((fun z => G (fwdMap W t z)) - V) '' Wd) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have h1 := (hG1 z hz).2
    have h2 := (hV.mem01 z hz).1
    simp only [Pi.sub_apply]
    linarith
  have hcl : closure Wd ⊆ closedBall 0 R :=
    closure_minimal (hWR.trans ball_subset_closedBall) isClosed_closedBall
  have hfr : ∀ x₀ ∈ frontier Wd, x₀ ∉ E → ∀ δ > 0, ∃ ρ > 0,
      ∀ y ∈ Wd, dist y x₀ < ρ → ((fun z => G (fwdMap W t z)) - V) y ≤ δ := by
    intro x₀ hx₀ hxE δ hδ
    simp only [Pi.sub_apply]
    have hx₀R : ‖x₀‖ ≤ R := by simpa using hcl hx₀.1
    rcases hx₀R.lt_or_eq with hlt | heq
    · -- inside the ball: `G ∘ Z → 0`
      refine flWire_delta ?_ (fun y hy => (hV.mem01 y hy).1) hδ
      by_cases hD : x₀ ∈ H \ fwdHull W t
      · have hZc : ContinuousAt (fwdMap W t) x₀ :=
          hc.continuousOn_fwdMap.continuousAt (hc.isOpen_dom.mem_nhds hD)
        have hZ : Tendsto (fwdMap W t) (𝓝[Wd] x₀) (𝓝 (fwdMap W t x₀)) :=
          hZc.tendsto.mono_left nhdsWithin_le_nhds
        have hZ' : Tendsto (fwdMap W t) (𝓝[Wd] x₀) (𝓝[hullComp η'] (fwdMap W t x₀)) :=
          tendsto_nhdsWithin_iff.2 ⟨hZ, eventually_mem_nhdsWithin.mono fun y hy =>
            hWU ⟨y, hy, rfl⟩⟩
        have := mem_closure_iff_nhdsWithin_neBot.1 hx₀.1
        have hucl : fwdMap W t x₀ ∈ closure (hullComp η') :=
          mem_closure_of_tendsto hZ (eventually_mem_nhdsWithin.mono fun y hy =>
            hWU ⟨y, hy, rfl⟩)
        have hnot := hWfr x₀ hx₀ hD hlt
        have hfrU : fwdMap W t x₀ ∈ frontier (hullComp η') :=
          ⟨hucl, fun hi => hnot (interior_subset hi)⟩
        have hA : fwdMap W t x₀ ∉ closure (ofReal '' Ioo (-N) 0 : Set ℂ) := fun h => by
          have h1 := (fl3cmp_closure_neg h).1
          have h2 : 0 < (fwdMap W t x₀).im := hc.mapsTo hD
          rw [h1] at h2
          exact lt_irrefl _ h2
        exact (hG.zero _ hfrU hA).comp hZ'
      · exact fl3cmp_tendsto_rough hc hεR hH hnorm hle hη ha hηa hηε hG hWo hWc hWD hWR hWU
          hWarc hD hlt
    · -- on the outer piece: `V → 1`
      have hsph : x₀ ∈ sphere (0 : ℂ) R := by simpa using heq
      have hnot : x₀ ∉ closure (frontier Wd \ (frontier Wd ∩ sphere 0 R)) := by
        rw [sdiff_self_inter]
        exact fun h => hxE (hE ⟨h, hsph⟩)
      have h1 := hV.one x₀ ⟨hx₀, hsph⟩ hnot
      obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.1
        (h1.eventually (lt_mem_nhds (show 1 - δ < (1 : ℝ) by linarith)))
      refine ⟨ρ, hρ, fun y hy hyd => ?_⟩
      have h2 : 1 - δ < V y := hsub ⟨mem_ball.2 hyd, hy⟩
      have h3 := (hG1 y hy).2
      linarith
  have hinf : ∀ δ > 0, ∃ S, ∀ y ∈ Wd, S ≤ ‖y‖ → ((fun z => G (fwdMap W t z)) - V) y ≤ δ := by
    refine fun δ _ => ⟨R, fun y hy hyR => absurd hyR (not_le.2 ?_)⟩
    simpa using hWR hy
  intro z hz
  have := fl2_harm_le_zero_off_finite E hWo hharm hbdd hfr hinf z hz
  simp only [Pi.sub_apply] at this
  linarith

/-- **Discharging `hE`.** If the frontier of `Wd` off `C_R` lies in `K_t ∪ ℝ ∪ C_ε` (`ε ≠ R`)
and the trace is strictly inside `B(0, R)` before time `t`, then the outer piece meets the rest
of the frontier only at the tip and at `±R`. -/
theorem fl3cmp_E_of (hc : SideCtx W t F) {R ε : ℝ} (hR : 0 ≤ R) (hεR : ε ≠ R)
    (hlt : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) {Wd : Set ℂ}
    (hfrB : frontier Wd \ sphere 0 R ⊆ fwdHull W t ∪ range ofReal ∪ sphere 0 ε) :
    closure (frontier Wd \ sphere 0 R) ∩ sphere 0 R ⊆
      (({trace W t, (R : ℂ), -(R : ℂ)} : Finset ℂ) : Set ℂ) := by
  classical
  rintro x ⟨hx, hxs⟩
  have hxR : ‖x‖ = R := by simpa using hxs
  have hKc : IsClosed (trace W '' Icc 0 t) := (isCompact_Icc.image_of_continuousOn hc.trCont).isClosed
  have hK : fwdHull W t ⊆ trace W '' Icc 0 t := by
    rw [hc.hull]; exact image_mono Ioc_subset_Icc_self
  have hRc : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have hRr : range ofReal ⊆ {z : ℂ | z.im = 0} := by rintro _ ⟨r, rfl⟩; simp
  have hcl : closure (frontier Wd \ sphere 0 R) ⊆
      trace W '' Icc 0 t ∪ {z : ℂ | z.im = 0} ∪ sphere 0 ε :=
    closure_minimal (hfrB.trans (union_subset_union (union_subset_union hK hRr) le_rfl))
      ((hKc.union hRc).union isClosed_sphere)
  simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
  rcases hcl hx with (⟨s, hs, rfl⟩ | him) | hε
  · rcases hs.2.lt_or_eq with h | h
    · exact absurd hxR (ne_of_lt (hlt s ⟨hs.1, h⟩))
    · exact Or.inl (by rw [h])
  · have hre : ((x.re : ℝ) : ℂ) = x := Complex.ext (by simp) (by simp [show x.im = 0 from him])
    have habs : |x.re| = R := by rw [abs_re_eq_norm.2 him, hxR]
    rcases (abs_eq hR).1 habs with h | h
    · exact Or.inr (Or.inl (by rw [← hre, h]))
    · exact Or.inr (Or.inr (by rw [← hre, h]; simp))
  · exact absurd ((by simpa using hε : ‖x‖ = ε).symm.trans hxR) hεR

/-- **Excursion-integral monotonicity** from a pointwise bound `0 ≤ u ≤ φ` on `Wd`, through a
chart `ψ` mapping short vertical segments above `J` into `Wd` (`fl2_yDer_le`); the vertical
derivative of `φ ∘ ψ` on `J` is a hypothesis. -/
theorem fl3cmp_excR_mono {u φ : ℂ → ℝ} {Wd : Set ℂ} (h0 : ∀ z ∈ Wd, 0 ≤ u z)
    (hle : ∀ z ∈ Wd, u z ≤ φ z) (ψ : ℂ → ℂ) {J : Set ℝ} (hJ : MeasurableSet J)
    (hψ : ∀ x ∈ J, ∀ᶠ y : ℝ in 𝓝[>] 0, ψ ((x : ℂ) + (y : ℂ) * I) ∈ Wd)
    (hφ : ∀ x ∈ J, ∃ L : ℝ,
      Tendsto (fun y : ℝ => φ (ψ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L)) :
    excR (u ∘ ψ) J ≤ excR (φ ∘ ψ) J := by
  unfold excR
  refine MeasureTheory.setLIntegral_mono' hJ fun x hx => ENNReal.ofReal_le_ofReal ?_
  obtain ⟨L, hL⟩ := hφ x hx
  exact fl2_yDer_le (u := u ∘ ψ) (φ := φ ∘ ψ) hL ((hψ x hx).mono fun y hy => h0 _ hy)
    ((hψ x hx).mono fun y hy => hle _ hy)

/-- **TARGET 2 (flux monotonicity at the arc).** In the setting of `fl3cmp_le`, for a chart `ψ`
mapping short vertical segments above `J` into `Wd`, and given a vertical derivative of `V ∘ ψ`
at each point of `J`: `excR (G ∘ Z ∘ ψ) J ≤ excR (V ∘ ψ) J`. -/
theorem fl3cmp_excR_le (hc : SideCtx W t F) {R ε : ℝ} (hεR : ε < R) (hH : trace W t ∈ H)
    (hnorm : ‖trace W t‖ = R) (hle : ∀ z ∈ fwdHull W t, ‖z‖ ≤ R) {η' : ℝ → ℂ} {a : ℝ}
    (hη : IsCrosscutH η') (ha : 0 < a) (hηa : Tendsto η' (𝓝[>] 0) (𝓝 (a : ℂ)))
    (hηε : arcH η' ⊆ {p | ‖fwdMapInv W t p‖ = ε}) {N : ℝ} {G : ℂ → ℝ}
    (hG : IsHarmMeas (hullComp η') (ofReal '' Ioo (-N) 0) G) {Wd : Set ℂ} (hWo : IsOpen Wd)
    (hWc : IsConnected Wd) (hWD : Wd ⊆ H \ fwdHull W t) (hWR : Wd ⊆ ball 0 R)
    (hWU : fwdMap W t '' Wd ⊆ hullComp η') (hWarc : arcH η' ⊆ closure (fwdMap W t '' Wd))
    (hWfr : ∀ x₀ ∈ frontier Wd, x₀ ∈ H \ fwdHull W t → ‖x₀‖ < R →
      fwdMap W t x₀ ∉ hullComp η')
    (E : Finset ℂ) (hE : closure (frontier Wd \ sphere 0 R) ∩ sphere 0 R ⊆ E) {V : ℂ → ℝ}
    (hV : IsHarmMeas Wd (frontier Wd ∩ sphere 0 R) V) (ψ : ℂ → ℂ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hψ : ∀ x ∈ J, ∀ᶠ y : ℝ in 𝓝[>] 0, ψ ((x : ℂ) + (y : ℂ) * I) ∈ Wd)
    (hVψ : ∀ x ∈ J, ∃ L : ℝ,
      Tendsto (fun y : ℝ => V (ψ ((x : ℂ) + (y : ℂ) * I)) / y) (𝓝[>] 0) (𝓝 L)) :
    excR ((fun z => G (fwdMap W t z)) ∘ ψ) J ≤ excR (V ∘ ψ) J :=
  fl3cmp_excR_mono (fun z hz => (hG.mem01 _ (hWU ⟨z, hz, rfl⟩)).1)
    (fl3cmp_le hc hεR hH hnorm hle hη ha hηa hηε hG hWo hWc hWD hWR hWU hWarc hWfr E hE hV)
    ψ hJ hψ hVψ

end FieldLawler
end QuantumZipper
