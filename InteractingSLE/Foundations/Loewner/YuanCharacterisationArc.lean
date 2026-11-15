import InteractingSLE.Foundations.Topology.Jordan.Summary
import InteractingSLE.Foundations.Topology.PathComplement
import InteractingSLE.Foundations.Loewner.YuanCharacterisationLimit

/-!
# Simple paths in the upper half-plane: fillings, boundary extensions and the tip

Packet PROVE-YUAN-M23, inputs of [Law05, Proposition 3.76] for simple paths
(`YuanCharacterisationSimple.lean`).

## Main results

* `isConnected_compl_image_Icc`: an arc does not separate the plane (Maehara's theorem, ported in
  `Topology/Jordan/ArcNonSep.lean`, transported to `ℂ`).
* `isConnected_H_diff_image`: a simple path started on `ℝ` and otherwise in `ℍ` does not separate
  `ℍ` (reflect it across `ℝ`, fold the plane onto `ℍ̄`, push up into `ℍ`).
* `fillH_image_eq`: its filling is the path itself, `fill(ζ[0, T]) = ζ((0, T])`.
* `exists_extension_symm`: the inverse of the mapping-out function of the filling of a path
  extends continuously to `ℍ̄` (Carathéodory–Torhorst through `PathComplement`), injective on `ℍ`,
  mapping real points to the boundary.
* `exists_tendsto_of_tendsto_comp_nhdsWithin_Ioi`: the cluster-set lemma for a curve
  parameter: if `F ∘ G → v` as `u ↓ s`, then `G` converges (to a point of the fibre of `v`).
* `exists_tendsto_mapOut_tip`: **the tip**: for a simple path `γ`, `g_s(γ(u))` converges to a real
  point `U` as `u ↓ s`, and the extended inverse map sends `U` to `γ(s)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace YuanCharacterisation

/-! ### Arcs do not separate -/

/-- **An arc does not separate the plane** (Maehara; `Foundations.Jordan.arc_not_separates`),
for an injective continuous map of a compact interval into `ℂ`. -/
theorem isConnected_compl_image_Icc {Q : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn Q (Icc a b)) (hi : InjOn Q (Icc a b)) : IsConnected (Q '' Icc a b)ᶜ := by
  set L := Foundations.Jordan.Arcs.complexLIE with hL
  have hmem : ∀ x : unitInterval, a + (b - a) * (x : ℝ) ∈ Icc a b := fun x => by
    have h0 : 0 ≤ (x : ℝ) := x.2.1
    have h1 : (x : ℝ) ≤ 1 := x.2.2
    constructor <;> nlinarith
  set f : unitInterval → EuclideanSpace ℝ (Fin 2) := fun x => L (Q (a + (b - a) * (x : ℝ)))
    with hf
  have hfc : Continuous f := by
    refine L.continuous.comp (hc.comp_continuous (by fun_prop) hmem)
  have hfi : Function.Injective f := by
    intro x y hxy
    have h1 := L.injective hxy
    have h2 := hi (hmem x) (hmem y) h1
    have hba : b - a ≠ 0 := by linarith
    exact Subtype.ext (mul_left_cancel₀ hba (by linarith))
  have hemb : Topology.IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
  set A : Set (EuclideanSpace ℝ (Fin 2)) := L '' (Q '' Icc a b) with hA
  have hrange : range f = A := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, hmem x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
      have hba : 0 < b - a := by linarith
      refine ⟨⟨(τ - a) / (b - a), ⟨div_nonneg (by linarith [hτ.1]) hba.le,
        (div_le_one hba).2 (by linarith [hτ.2])⟩⟩, ?_⟩
      simp only [hf]
      congr 2
      field_simp
      ring
  have φ : A ≃ₜ unitInterval := (Homeomorph.setCongr hrange.symm).trans hemb.toHomeomorph.symm
  have hconn := Foundations.Jordan.arc_not_separates Foundations.Jordan.Brouwer.brouwerFPT φ
  have heq : (Q '' Icc a b)ᶜ = L.symm '' Aᶜ := by
    ext z
    constructor
    · intro hz
      refine ⟨L z, fun hLz => hz ?_, by simp⟩
      obtain ⟨w, hw, hwz⟩ := hLz
      rw [L.injective hwz] at hw
      exact hw
    · rintro ⟨y, hy, rfl⟩ hz
      exact hy ⟨_, hz, by simp⟩
  rw [heq]
  exact hconn.image _ L.symm.continuous.continuousOn

/-- The path reflected across `ℝ`: `ζ(τ)` for `τ ≥ 0`, `conj ζ(−τ)` for `τ < 0`. -/
def reflPath (ζ : ℝ → ℂ) (τ : ℝ) : ℂ := if 0 ≤ τ then ζ τ else conj (ζ (-τ))

section HalfPlane

variable {ζ : ℝ → ℂ} {T : ℝ}

theorem continuousOn_reflPath (hc : ContinuousOn ζ (Icc 0 T)) (h0 : (ζ 0).im = 0) :
    ContinuousOn (reflPath ζ) (Icc (-T) T) := by
  have hfr : frontier {τ : ℝ | 0 ≤ τ} = {0} := by
    have : {τ : ℝ | 0 ≤ τ} = Ici 0 := rfl
    rw [this, frontier_Ici]
  have hcl1 : closure {τ : ℝ | 0 ≤ τ} = Ici 0 := closure_Ici 0
  have hcl2 : closure {τ : ℝ | ¬ 0 ≤ τ} = Iic 0 := by
    have : {τ : ℝ | ¬ 0 ≤ τ} = Iio 0 := by ext; simp
    rw [this, closure_Iio]
  refine ContinuousOn.if ?_ ?_ ?_
  · rintro τ ⟨-, hτ⟩
    rw [hfr, mem_singleton_iff] at hτ
    subst hτ
    rw [neg_zero, Complex.conj_eq_iff_im.2 h0]
  · rw [hcl1]
    exact hc.mono fun τ hτ => ⟨hτ.2, hτ.1.2⟩
  · rw [hcl2]
    refine continuous_conj.comp_continuousOn (hc.comp (by fun_prop) fun τ hτ => ?_)
    exact ⟨neg_nonneg.2 hτ.2, by linarith [hτ.1.1]⟩

theorem injOn_reflPath (hi : InjOn ζ (Icc 0 T)) (h0 : (ζ 0).im = 0)
    (hH : MapsTo ζ (Ioc 0 T) H) : InjOn (reflPath ζ) (Icc (-T) T) := by
  intro τ hτ τ' hτ' heq
  simp only [reflPath] at heq
  have him : ∀ σ, 0 < σ → σ ≤ T → (conj (ζ σ)).im < 0 := fun σ hσ hσT => by
    rw [conj_im]; exact neg_lt_zero.2 (hH ⟨hσ, hσT⟩)
  split_ifs at heq with h1 h2 h2
  · exact hi ⟨h1, hτ.2⟩ ⟨h2, hτ'.2⟩ heq
  · have h3 := him (-τ') (by linarith) (by linarith [hτ'.1])
    rw [← heq] at h3
    rcases eq_or_lt_of_le h1 with h4 | h4
    · rw [← h4, h0] at h3; exact absurd h3 (lt_irrefl _)
    · exact absurd (hH ⟨h4, hτ.2⟩) (not_lt.2 h3.le)
  · have h3 := him (-τ) (by linarith) (by linarith [hτ.1])
    rw [heq] at h3
    rcases eq_or_lt_of_le h2 with h4 | h4
    · rw [← h4, h0] at h3; exact absurd h3 (lt_irrefl _)
    · exact absurd (hH ⟨h4, hτ'.2⟩) (not_lt.2 h3.le)
  · have heq' : ζ (-τ) = ζ (-τ') := by simpa using congrArg (starRingEnd ℂ) heq
    have := hi ⟨by linarith, by linarith [hτ.1]⟩ ⟨by linarith, by linarith [hτ'.1]⟩ heq'
    linarith

/-- **A simple path started on `ℝ` and otherwise in `ℍ` does not separate `ℍ`.** -/
theorem isConnected_H_diff_image (hT : 0 < T) (hc : ContinuousOn ζ (Icc 0 T))
    (hi : InjOn ζ (Icc 0 T)) (h0 : (ζ 0).im = 0) (hH : MapsTo ζ (Ioc 0 T) H) :
    IsConnected (H \ ζ '' Icc 0 T) := by
  set P := ζ '' Icc 0 T with hP
  have hPc : IsCompact P := isCompact_Icc.image_of_continuousOn hc
  have hPne : P.Nonempty := ⟨ζ 0, 0, ⟨le_rfl, hT.le⟩, rfl⟩
  have hconn := isConnected_compl_image_Icc (by linarith : -T < T) (continuousOn_reflPath hc h0)
    (injOn_reflPath hi h0 hH)
  -- fold the plane onto `ℍ̄`
  set fold : ℂ → ℂ := fun z => (z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * I with hfold
  have hfre : ∀ z, (fold z).re = z.re := fun z => by simp [hfold]
  have hfim : ∀ z, (fold z).im = |z.im| := fun z => by simp [hfold]
  have hfoldc : Continuous fold := by simp only [hfold]; fun_prop
  have hX : Hbar \ P = fold '' (reflPath ζ '' Icc (-T) T)ᶜ := by
    ext w
    constructor
    · rintro ⟨hw, hwP⟩
      refine ⟨w, fun hwQ => ?_, ?_⟩
      · obtain ⟨τ, hτ, hτw⟩ := hwQ
        simp only [reflPath] at hτw
        split_ifs at hτw with h
        · exact hwP ⟨τ, ⟨h, hτ.2⟩, hτw⟩
        · have : (conj (ζ (-τ))).im < 0 := by
            rw [conj_im]; exact neg_lt_zero.2 (hH ⟨by linarith, by linarith [hτ.1]⟩)
          rw [hτw] at this
          exact absurd (show (0 : ℝ) ≤ w.im from hw) (not_le.2 this)
      · exact Complex.ext (hfre w) (by rw [hfim, abs_of_nonneg (show (0 : ℝ) ≤ w.im from hw)])
    · rintro ⟨z, hz, rfl⟩
      refine ⟨show (0 : ℝ) ≤ (fold z).im by rw [hfim]; exact abs_nonneg _, ?_⟩
      rintro ⟨u, hu, hzu⟩
      apply hz
      rcases le_total 0 z.im with him | him
      · refine ⟨u, ⟨by linarith [hu.1], hu.2⟩, ?_⟩
        simp only [reflPath, hu.1, ite_true]
        rw [hzu]; exact Complex.ext (hfre z) (by rw [hfim, abs_of_nonneg him])
      · rcases eq_or_lt_of_le hu.1 with h4 | h4
        · refine ⟨0, ⟨by linarith, hT.le⟩, ?_⟩
          simp only [reflPath, le_refl, ite_true]
          rw [← h4] at hzu
          have hz0 : z.im = 0 := by
            have := congrArg Complex.im hzu
            rw [h0, hfim] at this
            exact abs_eq_zero.1 this.symm
          refine Complex.ext ?_ ?_
          · have := congrArg Complex.re hzu; rw [hfre] at this; exact this
          · rw [h0, hz0]
        · refine ⟨-u, ⟨by linarith [hu.2], by linarith⟩, ?_⟩
          simp only [reflPath, show ¬ (0 : ℝ) ≤ -u by linarith, ite_false, neg_neg]
          rw [hzu]
          exact Complex.ext (by rw [conj_re, hfre])
            (by rw [conj_im, hfim, abs_of_nonpos him, neg_neg])
  have hXc : IsConnected (Hbar \ P) := by
    rw [hX]; exact hconn.image _ hfoldc.continuousOn
  -- push `ℍ̄ \ P` up into `ℍ \ P`
  set r : ℂ → ℝ := fun z => min 1 (infDist z P) / 2 with hr
  have hrc : Continuous r := by
    simp only [hr]; exact (continuous_const.min (continuous_infDist_pt P)).div_const 2
  have hrpos : ∀ z ∉ P, 0 < r z := fun z hz => by
    simp only [hr]
    exact div_pos (lt_min one_pos ((hPc.isClosed.notMem_iff_infDist_pos hPne).1 hz)) two_pos
  have hrlt : ∀ z, r z < infDist z P ∨ z ∈ P := fun z => by
    by_cases hz : z ∈ P
    · exact Or.inr hz
    · left
      have := (hPc.isClosed.notMem_iff_infDist_pos hPne).1 hz
      simp only [hr]
      have := min_le_right 1 (infDist z P)
      linarith
  set Φ : ℂ → ℂ := fun z => z + (r z : ℂ) * I with hΦ
  have hΦc : Continuous Φ := by simp only [hΦ]; fun_prop
  have hseg : ∀ z ∈ Hbar \ P, ∀ l ∈ Icc (0 : ℝ) 1, z + ((l * r z : ℝ) : ℂ) * I ∉ P := by
    intro z hz l hl hmem
    have h1 : infDist z P ≤ dist z (z + ((l * r z : ℝ) : ℂ) * I) := infDist_le_dist_of_mem hmem
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl.1 (hrpos z hz.2).le)] at h1
    rcases hrlt z with h | h
    · nlinarith [hl.2, hrpos z hz.2]
    · exact hz.2 h
  have hsegH : ∀ z ∈ Hbar \ P, ∀ l ∈ Ioc (0 : ℝ) 1, z + ((l * r z : ℝ) : ℂ) * I ∈ H := by
    intro z hz l hl
    show 0 < (z + ((l * r z : ℝ) : ℂ) * I).im
    simp only [add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    have := mul_pos hl.1 (hrpos z hz.2)
    linarith [show (0 : ℝ) ≤ z.im from hz.1]
  have hΦX : Φ '' (Hbar \ P) ⊆ H \ P := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hseg z hz 1 ⟨zero_le_one, le_rfl⟩
    have h2 := hsegH z hz 1 ⟨one_pos, le_rfl⟩
    simp only [one_mul] at h1 h2
    exact ⟨h2, h1⟩
  have hΦXc : IsConnected (Φ '' (Hbar \ P)) := hXc.image _ hΦc.continuousOn
  obtain ⟨y₀, hy₀⟩ := hΦXc.nonempty
  refine ⟨⟨y₀, hΦX hy₀⟩, isPreconnected_of_forall y₀ fun y hy => ?_⟩
  have hyX : y ∈ Hbar \ P := ⟨H_subset_Hbar hy.1, hy.2⟩
  set S := (fun l : ℝ => y + ((l * r y : ℝ) : ℂ) * I) '' Icc 0 1 with hS
  have hSc : IsPreconnected S := isPreconnected_Icc.image _ (by fun_prop)
  have hSY : S ⊆ H \ P := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨?_, hseg y hyX l hl⟩
    rcases eq_or_lt_of_le hl.1 with h | h
    · rw [← h]; simpa using hy.1
    · exact hsegH y hyX l ⟨h, hl.2⟩
  have hΦy : Φ y ∈ S := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [hΦ]⟩
  refine ⟨Φ '' (Hbar \ P) ∪ S, union_subset hΦX hSY, Or.inl hy₀, Or.inr ⟨0, ⟨le_rfl, zero_le_one⟩,
    by simp⟩, ?_⟩
  exact hΦXc.isPreconnected.union (Φ y) ⟨y, hyX, rfl⟩ hΦy hSc

/-- The filling of a simple path started on `ℝ` and otherwise in `ℍ` is the path itself. -/
theorem fillH_image_eq (hT : 0 ≤ T) (hc : ContinuousOn ζ (Icc 0 T)) (hi : InjOn ζ (Icc 0 T))
    (h0 : (ζ 0).im = 0) (hH : MapsTo ζ (Ioc 0 T) H) : fillH (ζ '' Icc 0 T) = ζ '' Ioc 0 T := by
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · subst hT0
    rw [Ioc_self, image_empty]
    refine fillH_eq_empty_of_subset ?_
    rintro _ ⟨u, hu, rfl⟩
    rw [show u = 0 from le_antisymm hu.2 hu.1]
    exact h0.le
  have hPc : IsCompact (ζ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hc
  have hconn := isConnected_H_diff_image hTpos hc hi h0 hH
  obtain ⟨R, hR, hPR⟩ := exists_closure_subset_ball hPc.isBounded
  ext z
  constructor
  · rintro ⟨hz, h⟩
    rw [hPc.isClosed.closure_eq] at h
    by_cases hzP : z ∈ ζ '' Icc 0 T
    · obtain ⟨u, hu, rfl⟩ := hzP
      rcases eq_or_lt_of_le hu.1 with h' | h'
      · rw [← h'] at hz; exact absurd h0 (ne_of_gt hz)
      · exact ⟨u, ⟨h', hu.2⟩, rfl⟩
    · rcases h with h | h
      · exact absurd h hzP
      · exfalso
        rw [hconn.isPreconnected.connectedComponentIn ⟨hz, hzP⟩] at h
        refine not_isBounded_setOf_lt_im R (h.subset fun w hw => ⟨?_, ?_⟩)
        · show 0 < w.im; linarith [show R < w.im from hw]
        · intro hwP
          have := hPR (subset_closure hwP)
          rw [mem_ball_zero_iff] at this
          have h1 : R < w.im := hw
          linarith [abs_im_le_norm w, le_abs_self w.im]
  · rintro ⟨u, hu, rfl⟩
    exact mem_fillH_image (Ioc_subset_Icc_self hu) (hH hu)

end HalfPlane

/-! ### The inverse mapping-out function of the filling of a path -/

section Extension

variable {ζ : ℝ → ℂ} {s : ℝ}

/-- The inverse of the mapping-out function of `A = fill(ζ[0, s])` (ζ a path in `ℍ̄` started on
`ℝ`) extends continuously to `ℍ̄`; it is injective on `ℍ`, no real point is sent into its image
of `ℍ`, and it tends to `∞` at `∞`. -/
theorem exists_extension_symm (hs : 0 ≤ s) (hc : ContinuousOn ζ (Icc 0 s))
    (hζH : MapsTo ζ (Icc 0 s) Hbar) (h0 : (ζ 0).im = 0) :
    ∃ F : ℂ → ℂ, (∀ w ∈ H, F w ∈ H \ fillH (ζ '' Icc 0 s) ∧
        ConformalImage.mapOut (fillH (ζ '' Icc 0 s)) (F w) = w) ∧
      (∀ z ∈ H \ fillH (ζ '' Icc 0 s), F (ConformalImage.mapOut (fillH (ζ '' Icc 0 s)) z) = z) ∧
      DifferentiableOn ℂ F H ∧ ContinuousOn F Hbar ∧ InjOn F H ∧
      (∀ x : ℂ, x.im = 0 → F x ∉ F '' H) ∧
      Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) ∧
      MapsTo F (Hbar \ H) (frontier (H \ fillH (ζ '' Icc 0 s))) ∧
      ∃ M : ℝ, ∀ w ∈ Hbar, ‖F w - w‖ ≤ M := by
  set A := fillH (ζ '' Icc 0 s) with hAdef
  have hA : IsHPHull A := isHPHull_fillH_image_of_im hc hs h0
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  obtain ⟨h, hd, h1, h2⟩ := hg.exists_symm hA
  have hinj : InjOn h H := fun w hw w' hw' hww' => by
    rw [← (h1 w hw).2, ← (h1 w' hw').2, hww']
  have hconf : IsConformalBijection h H (H \ A) :=
    ⟨hd, fun w hw => (h1 w hw).1, hinj, fun z hz => ⟨g z, hg.1.2.mapsTo hz, h2 z hz⟩⟩
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  have hψi : Tendsto h (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) := by
    have h1' : Tendsto (fun w : ℂ => ‖w‖) (Bornology.cobounded ℂ ⊓ 𝓟 H) atTop :=
      tendsto_norm_cobounded_atTop.mono_left inf_le_left
    have h3 : Tendsto (fun w => ‖h w‖) (Bornology.cobounded ℂ ⊓ 𝓟 H) atTop := by
      refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-M) h1')
      filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
      have := hM (h w) (h1 w hw).1
      rw [(h1 w hw).2] at this
      linarith [norm_sub_norm_le w (h w), norm_sub_rev w (h w)]
    simpa only [comap_norm_atTop] using tendsto_comap_iff.2 h3
  obtain ⟨F, hFeq, hFc, hFbd, hFi⟩ :=
    exists_continuousOn_extension_of_path_of_tendsto hc hζH hconf hψi
  have hbdH : ∀ w ∈ H, ‖F w - w‖ ≤ M := fun w hw => by
    have := hM (h w) (h1 w hw).1
    rw [(h1 w hw).2, norm_sub_rev] at this
    rw [hFeq hw]
    exact this
  have hbd : ∀ w ∈ Hbar, ‖F w - w‖ ≤ M := by
    have hcl : closure H = Hbar := QuantumZipper.CA.Car.closure_H_eq_Hbar
    intro w hw
    have hwcl : w ∈ closure H := hcl ▸ hw
    have hne : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hwcl
    have hlim : Tendsto (fun z => ‖F z - z‖) (𝓝[H] w) (𝓝 ‖F w - w‖) :=
      (((hFc w hw).mono H_subset_Hbar).tendsto.sub
        (continuousWithinAt_id.tendsto)).norm
    exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall hbdH)
  refine ⟨F, fun w hw => by rw [hFeq hw]; exact h1 w hw, fun z hz => by
    rw [hFeq (hg.1.2.mapsTo hz)]; exact h2 z hz, hd.congr fun w hw => hFeq hw, hFc,
    hinj.congr fun w hw => (hFeq hw).symm, fun x hx hxF => ?_, hFi, hFbd, M, hbd⟩
  have hxb : x ∈ Hbar \ H := ⟨show 0 ≤ x.im from hx.ge, fun h' => (ne_of_gt h') hx⟩
  have hfr := hFbd hxb
  obtain ⟨w, hw, hwx⟩ := hxF
  rw [hFeq hw] at hwx
  have hmem : F x ∈ H \ A := hwx ▸ (h1 w hw).1
  have hAo : IsOpen (H \ A) := hA.isOpen
  rw [hAo.frontier_eq] at hfr
  exact hfr.2 hmem

end Extension

/-! ### The cluster-set lemma along a curve parameter -/

/-- **Cluster-set lemma** (the curve form of `exists_tendsto_of_tendsto_comp`): let `F` be
continuous on `ℍ̄`, holomorphic and injective on `ℍ`, sending no real point into `F(ℍ)`, and let
`G` take values in `ℍ̄`, be bounded, and be continuous on the members of a basis of preconnected
sets of the filter `l`. If `F ∘ G → v` along `l`, then `G` converges along `l`, to a point of the
fibre of `v`. -/
theorem exists_tendsto_of_tendsto_comp_filter {α : Type*} [TopologicalSpace α] {F : ℂ → ℂ}
    {G : α → ℂ} (hd : DifferentiableOn ℂ F H) (hc : ContinuousOn F Hbar) (hinj : InjOn F H)
    (hR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H) {l : Filter α} [l.NeBot]
    (hconn : ∀ U ∈ l, ∃ S ∈ l, S ⊆ U ∧ IsPreconnected S ∧ ContinuousOn G S)
    (hGH : ∀ᶠ w in l, G w ∈ Hbar) {R : ℝ} (hGR : ∀ᶠ w in l, ‖G w‖ ≤ R) {v : ℂ}
    (hFG : Tendsto (fun w => F (G w)) l (𝓝 v)) :
    ∃ ξ ∈ Hbar, F ξ = v ∧ Tendsto G l (𝓝 ξ) := by
  set s : Set ℂ := closedBall 0 R ∩ Hbar with hs
  have hsc : IsCompact s := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hmem : ∀ᶠ w in l, G w ∈ s := by
    filter_upwards [hGR, hGH] with w hwR hwH
    exact ⟨mem_closedBall_zero_iff.2 hwR, hwH⟩
  have hfib : ∀ ξ ∈ s, MapClusterPt ξ l G → F ξ = v := fun ξ hξ hcl =>
    eq_of_mapClusterPt hc hGH hFG hξ.2 hcl
  obtain ⟨ξ₀, hξ₀s, hξ₀⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 hmem)
  have hreal_of : ∀ (z : ℂ), z ∈ H → F z = v → ∀ η ∈ s, F η = v → η ∈ H := by
    intro z hzH hzv η hη hFη
    by_contra hηH
    have h0 : η.im = 0 := le_antisymm (not_lt.1 hηH) (show 0 ≤ η.im from hη.2)
    exact hR η h0 ⟨z, hzH, hzv.trans hFη.symm⟩
  have huniq : ∀ ξ₁ ∈ s, MapClusterPt ξ₁ l G → ∀ ξ₂ ∈ s, MapClusterPt ξ₂ l G →
      ξ₁.re < ξ₂.re → False := by
    intro ξ₁ h₁s h₁ ξ₂ h₂s h₂ hlt
    have hF₁ := hfib ξ₁ h₁s h₁
    have hF₂ := hfib ξ₂ h₂s h₂
    have hvD : v ∉ F '' H := by
      rintro ⟨z, hzH, hzv⟩
      have := hinj (hreal_of z hzH hzv ξ₁ h₁s hF₁) (hreal_of z hzH hzv ξ₂ h₂s hF₂)
        (hF₁.trans hF₂.symm)
      rw [this] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hd hc hinj hlt v
    set l' : Filter α := l ⊓ 𝓟 {w | (G w).re = m} with hl'
    have hl'ne : l'.NeBot := by
      rw [hl', inf_principal_neBot_iff]
      intro U hU
      obtain ⟨S, hSl, hSU, hSc, hGS⟩ := hconn U hU
      have hlo : ∃ w₁ ∈ S, (G w₁).re < m := by
        have hfr : ∃ᶠ w in l, G w ∈ ball ξ₁ (m - ξ₁.re) :=
          h₁.frequently (ball_mem_nhds ξ₁ (by linarith [hm.1]))
        obtain ⟨w, hwb, hwS⟩ := (hfr.and_eventually hSl).exists
        refine ⟨w, hwS, ?_⟩
        have := Complex.abs_re_le_norm (G w - ξ₁)
        rw [mem_ball, dist_eq_norm] at hwb
        rw [Complex.sub_re] at this
        linarith [le_abs_self ((G w).re - ξ₁.re)]
      have hhi : ∃ w₂ ∈ S, m < (G w₂).re := by
        have hfr : ∃ᶠ w in l, G w ∈ ball ξ₂ (ξ₂.re - m) :=
          h₂.frequently (ball_mem_nhds ξ₂ (by linarith [hm.2]))
        obtain ⟨w, hwb, hwS⟩ := (hfr.and_eventually hSl).exists
        refine ⟨w, hwS, ?_⟩
        have := Complex.abs_re_le_norm (G w - ξ₂)
        rw [mem_ball, dist_eq_norm] at hwb
        rw [Complex.sub_re] at this
        linarith [neg_abs_le ((G w).re - ξ₂.re)]
      obtain ⟨w₁, hw₁S, hw₁⟩ := hlo
      obtain ⟨w₂, hw₂S, hw₂⟩ := hhi
      have hGS' : ContinuousOn (fun w => (G w).re) S := Complex.continuous_re.comp_continuousOn hGS
      obtain ⟨w, hwS, hwm⟩ := hSc.intermediate_value hw₁S hw₂S hGS' ⟨hw₁.le, hw₂.le⟩
      exact ⟨w, hSU hwS, hwm⟩
    have hl'le : l' ≤ l := inf_le_left
    obtain ⟨ζ, hζs, hζ⟩ := hsc.exists_mapClusterPt (tendsto_principal.2 (hl'le hmem))
    have hζre : ζ.re = m := by
      by_contra hne
      have hopen : {y : ℂ | y.re ≠ m} ∈ 𝓝 ζ :=
        (isOpen_ne_fun Complex.continuous_re continuous_const).mem_nhds hne
      have hev : ∀ᶠ w in l', (G w).re = m := mem_inf_of_right (mem_principal_self _)
      obtain ⟨w, hw1, hw2⟩ := ((hζ.frequently hopen).and_eventually hev).exists
      exact hw1 hw2
    have hFζ : F ζ = v :=
      eq_of_mapClusterPt hc (hl'le hGH) (hFG.mono_left hl'le) hζs.2 hζ
    by_cases hζH : ζ ∈ H
    · exact hvD ⟨ζ, hζH, hFζ⟩
    · have h0 : ζ.im = 0 := le_antisymm (not_lt.1 hζH) (show 0 ≤ ζ.im from hζs.2)
      have : ζ = (m : ℂ) := by rw [eq_ofReal_re_of_im_eq_zero h0, hζre]
      exact hFm (this ▸ hFζ)
  have hall : ∀ ξ ∈ s, MapClusterPt ξ l G → ξ = ξ₀ := by
    intro ξ hξs hξ
    have hF := hfib ξ hξs hξ
    have hF₀ := hfib ξ₀ hξ₀s hξ₀
    rcases lt_trichotomy ξ.re ξ₀.re with h | h | h
    · exact (huniq ξ hξs hξ ξ₀ hξ₀s hξ₀ h).elim
    · by_cases hvD : v ∈ F '' H
      · obtain ⟨z, hzH, hzv⟩ := hvD
        exact hinj (hreal_of z hzH hzv ξ hξs hF) (hreal_of z hzH hzv ξ₀ hξ₀s hF₀)
          (hF.trans hF₀.symm)
      · have him : ∀ η ∈ s, F η = v → η.im = 0 := by
          intro η hη hFη
          by_contra hne
          exact hvD ⟨η, show 0 < η.im from lt_of_le_of_ne (show 0 ≤ η.im from hη.2)
            (Ne.symm hne), hFη⟩
        exact Complex.ext h ((him ξ hξs hF).trans (him ξ₀ hξ₀s hF₀).symm)
    · exact (huniq ξ₀ hξ₀s hξ₀ ξ hξs hξ h).elim
  exact ⟨ξ₀, hξ₀s.2, hfib ξ₀ hξ₀s hξ₀, hsc.tendsto_nhds_of_unique_mapClusterPt hmem hall⟩

/-! ### The tip -/

section Tip

variable {γ : ℝ → ℂ} {S s : ℝ}

/-- The filling of an initial piece of a simple path is that piece (without its real start). -/
theorem fillH_image_eq_of_le (hc : ContinuousOn γ (Icc 0 S)) (hi : InjOn γ (Icc 0 S))
    (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 S) H) (hs : 0 ≤ s) (hsS : s ≤ S) :
    fillH (γ '' Icc 0 s) = γ '' Ioc 0 s :=
  fillH_image_eq hs (hc.mono (Icc_subset_Icc_right hsS)) (hi.mono (Icc_subset_Icc_right hsS))
    (by rw [h0, zero_im]) (hH.mono_left (Ioc_subset_Ioc_right hsS))

/-- Later points of a simple path lie outside the filling of an initial piece. -/
theorem mem_H_diff_fillH_of_lt (hc : ContinuousOn γ (Icc 0 S)) (hi : InjOn γ (Icc 0 S))
    (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 S) H) (hs : 0 ≤ s) {u : ℝ} (hsu : s < u) (huS : u ≤ S) :
    γ u ∈ H \ fillH (γ '' Icc 0 s) := by
  rw [fillH_image_eq_of_le hc hi h0 hH hs (hsu.le.trans huS)]
  refine ⟨hH ⟨hs.trans_lt hsu, huS⟩, ?_⟩
  rintro ⟨u', hu', heq⟩
  have := hi ⟨hu'.1.le, hu'.2.trans (hsu.le.trans huS)⟩ ⟨(hs.trans_lt hsu).le, huS⟩ heq
  linarith [hu'.2]

/-- **The tip.** For a simple path `γ` (`γ 0 = 0`, `γ((0, S]) ⊆ ℍ`) and `0 < s < S`, the images
`g_s(γ(u))` under the mapping-out function of `fill(γ[0, s])` converge, as `u ↓ s`, to a real
point `U`, and every extension `F` of `g_s⁻¹` as in `exists_extension_symm` sends `U` to `γ(s)`. -/
theorem exists_tendsto_mapOut_tip (hc : ContinuousOn γ (Icc 0 S)) (hi : InjOn γ (Icc 0 S))
    (h0 : γ 0 = 0) (hH : MapsTo γ (Ioc 0 S) H) (hs : 0 < s) (hsS : s < S) {F : ℂ → ℂ}
    (hF1 : ∀ w ∈ H, F w ∈ H \ fillH (γ '' Icc 0 s) ∧
      ConformalImage.mapOut (fillH (γ '' Icc 0 s)) (F w) = w)
    (hF2 : ∀ z ∈ H \ fillH (γ '' Icc 0 s), F (ConformalImage.mapOut (fillH (γ '' Icc 0 s)) z) = z)
    (hFd : DifferentiableOn ℂ F H) (hFc : ContinuousOn F Hbar) (hFi : InjOn F H)
    (hFR : ∀ x : ℂ, x.im = 0 → F x ∉ F '' H) :
    ∃ U : ℝ, Tendsto (fun u => ConformalImage.mapOut (fillH (γ '' Icc 0 s)) (γ u)) (𝓝[>] s)
      (𝓝 (U : ℂ)) ∧ F U = γ s := by
  set A := fillH (γ '' Icc 0 s) with hAdef
  have hA : IsHPHull A := isHPHull_fillH_image (hc.mono (Icc_subset_Icc_right hsS.le)) hs.le h0
  set g := ConformalImage.mapOut A with hgdef
  have hg : IsMapOut A g := ConformalImage.isMapOut_mapOut hA
  have hmemA : ∀ u ∈ Ioc s S, γ u ∈ H \ A := fun u hu =>
    mem_H_diff_fillH_of_lt hc hi h0 hH hs.le hu.1 hu.2
  have hGc : ContinuousOn (fun u => g (γ u)) (Ioc s S) :=
    hg.1.1.continuousOn.comp (hc.mono fun u hu => ⟨hs.le.trans hu.1.le, hu.2⟩) hmemA
  have hIoo : Ioo s S ∈ 𝓝[>] s := Ioo_mem_nhdsGT hsS
  have hconn : ∀ U ∈ 𝓝[>] s, ∃ S' ∈ 𝓝[>] s, S' ⊆ U ∧ IsPreconnected S' ∧
      ContinuousOn (fun u => g (γ u)) S' := by
    intro U hU
    obtain ⟨b, hb, hbU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
    refine ⟨Ioo s (min b S), Ioo_mem_nhdsGT (lt_min hb hsS), fun u hu => hbU
      ⟨hu.1, hu.2.trans_le (min_le_left _ _)⟩, isPreconnected_Ioo,
      hGc.mono fun u hu => ⟨hu.1, (hu.2.trans_le (min_le_right _ _)).le⟩⟩
  obtain ⟨M, hM⟩ := hg.exists_norm_sub_le hA
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := S)).exists_bound_of_continuousOn hc
  have hGH : ∀ᶠ u in 𝓝[>] s, g (γ u) ∈ Hbar := by
    filter_upwards [hIoo] with u hu
    exact H_subset_Hbar (hg.1.2.mapsTo (hmemA u ⟨hu.1, hu.2.le⟩))
  have hGR : ∀ᶠ u in 𝓝[>] s, ‖g (γ u)‖ ≤ B + M := by
    filter_upwards [hIoo] with u hu
    have h1 := hM (γ u) (hmemA u ⟨hu.1, hu.2.le⟩)
    have h2 := hB u ⟨hs.le.trans hu.1.le, hu.2.le⟩
    calc ‖g (γ u)‖ = ‖(g (γ u) - γ u) + γ u‖ := by ring_nf
      _ ≤ ‖g (γ u) - γ u‖ + ‖γ u‖ := norm_add_le _ _
      _ ≤ B + M := by linarith
  have hFG : Tendsto (fun u => F (g (γ u))) (𝓝[>] s) (𝓝 (γ s)) := by
    have hγ : Tendsto γ (𝓝[>] s) (𝓝 (γ s)) := (hc s ⟨hs.le, hsS.le⟩).tendsto.mono_left
      (nhdsWithin_le_of_mem (mem_of_superset hIoo fun u hu => ⟨hs.le.trans hu.1.le, hu.2.le⟩))
    refine hγ.congr' ?_
    filter_upwards [hIoo] with u hu
    exact (hF2 (γ u) (hmemA u ⟨hu.1, hu.2.le⟩)).symm
  obtain ⟨ξ, hξ, hFξ, hlim⟩ :=
    exists_tendsto_of_tendsto_comp_filter hFd hFc hFi hFR hconn hGH hGR hFG
  have hγs : γ s ∈ A := mem_fillH_image ⟨hs.le, le_rfl⟩ (hH ⟨hs, hsS.le⟩)
  have hξim : ξ.im = 0 := by
    by_contra hne
    have hξH : ξ ∈ H := lt_of_le_of_ne (show 0 ≤ ξ.im from hξ) (Ne.symm hne)
    exact (hF1 ξ hξH).1.2 (hFξ ▸ hγs)
  have hξeq : ξ = (ξ.re : ℂ) := eq_ofReal_re_of_im_eq_zero hξim
  exact ⟨ξ.re, hξeq ▸ hlim, by rw [← hξeq]; exact hFξ⟩

end Tip

end YuanCharacterisation

end InteractingSLE
