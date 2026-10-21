import SmallGammaGeodesics.CC.Extension
import SmallGammaGeodesics.CC.LocalPull
import SmallGammaGeodesics.CC.LocalityConf
import SmallGammaGeodesics.CC.Coupling
import LQGMetric.Field.StandardBorelDist
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# T4: the conformal coupling on an extension of the probability space (track CC, packet CC12a)

Source: planning audit `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D17**
item 2 ("Coupling on an extension of the given space"), with GA4 A3 (the local Möbius law, an input
here) and GA5 (a11).

Let `IsConfNbhd ϕ W V`, `U = ϕ(V)` and `τ = confPull ϕ W`. Let `h` be a whole-plane GFF on
`(Ω, P)` such that the process `(h(τ g))_{g ∈ 𝓓₀(U)}` has the law of `(h(g))_{g ∈ 𝓓₀(U)}`
(hypothesis `hlaw`; for Möbius `ϕ` this is GA4's A3, `map_confPull_eq_of_isMobius` in
`CC/ExtensionMobius.lean`; for the maps `mobPhi θ` also P-L2's `map_mobTransport0_eq`).

The law hypothesis is on the pullback process **without** the drift `−Q ∫ log|ϕ'| τg` of
`confPair0`: with the drift the process has mean `Q ∫ log|ψ'| g`, which is nonzero for some
mean-zero `g` when `ϕ` is a non-affine Möbius map and `Q ≠ 0`, so it cannot be the (centred) law of
a GFF. The drift is carried by the test function `G` of the coupling form.

* **T4, core** `exists_extension_confPull`: on `Ω × DistC` there is a probability measure `P'`
  with first marginal `P` (and transfer of a.s. statements back to `P`), under which `h̄ := snd` is
  a whole-plane GFF and a.s. `h̄(g) = h(τ g)` for **every** `g ∈ 𝓓₀(U)` simultaneously.

  Proof: the T2 extension for the countable family `m_j = ι(φ_j) − (∫ φ_j) ρ`, where `(φ_j)` is
  LQGMetric's countable generating family `distGen U` of `𝓓(U)` and `ρ ∈ 𝓓(U)` has `∫ ρ = 1`.
  On the a.s. event `{h̄(m_j) = h(τ m_j) ∀ j}` the two distributions on `U`
  `A = (h̄ − ⟨h̄, ρ⟩)|_U` and `B = h ∘ τ − ⟨h, τρ⟩ ∫(·)` (a distribution by T3,
  `confPullOnCLM`) agree on every `φ_j`, hence are equal (`injective_distOn_pairings`, density of
  `(φ_j)` in every `𝓓_K`); evaluating at `g ∈ 𝓓₀(U)` gives `h̄(g) = h(τ g)`.
* **T4, coupling form** `exists_confCoupling_extension`: moreover, with a test function `G` equal to
  `Q log|ψ'|` on `U` (`ψ = invFunOn ϕ W`; a smooth cutoff times `log|ψ'|`) and the random constant
  `c = h̄(ρ) − h(τρ)`, the triple `(h ∘ fst, h̄, G − c)` is a.s. a conformal coupling
  (`IsConfCoupling`), and `confPair0 γ ϕ W V h = pair0On U (h̄ + G)` a.s.
  (`IsConfCoupling.confPair0_eq` and `pair0On_addFun_sub_const`). This is exactly the input of one
  application of `ConfCov` in CC12b.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Function TopologicalSpace Metric
open scoped Distributions

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## 1. Distributions on `O` built from continuous linear functionals -/

/-- Integration against `1`, as a distribution on `O`. -/
def intDist (O : Opens ℂ) : DistOn O := Distribution.ofFun O (fun _ => (1 : ℝ)) volume ⊤

theorem intDist_apply (O : Opens ℂ) (φ : TestOn O) : intDist O φ = ∫ x, φ x := by
  rw [intDist, Distribution.ofFun_apply ((locallyIntegrable_const (1 : ℝ)).locallyIntegrableOn _)]
  simp

/-- A continuous linear functional on `𝓓(O)` as a distribution on `O`. -/
def toDistOn (O : Opens ℂ) (L : TestOn O →L[ℝ] ℝ) : DistOn O := L

theorem toDistOn_apply (O : Opens ℂ) (L : TestOn O →L[ℝ] ℝ) (φ : TestOn O) :
    toDistOn O L φ = L φ :=
  rfl

/-! ## 2. The recentred test functions -/

/-- The inclusion `𝓓(O) → 𝓓(ℂ)`. -/
def inclTest (O : Opens ℂ) (φ : TestOn O) : TestC :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) φ

theorem coe_inclTest (O : Opens ℂ) (φ : TestOn O) : ⇑(inclTest O φ) = ⇑φ :=
  coe_monoCLM_top O φ

/-- `ι φ − (∫ φ) ρ`. -/
def recTest (O : Opens ℂ) (ρ : TestC) (φ : TestOn O) : TestC :=
  inclTest O φ - (∫ x, inclTest O φ x) • ρ

theorem coe_recTest (O : Opens ℂ) (ρ : TestC) (φ : TestOn O) :
    ⇑(recTest O ρ φ) = ⇑φ - (∫ x, φ x) • ⇑ρ := by
  have h1 : ∫ x, inclTest O φ x = ∫ x, φ x := by rw [coe_inclTest]
  funext y
  show inclTest O φ y - (∫ x, inclTest O φ x) • ρ y = _
  rw [h1, coe_inclTest]
  rfl

theorem integral_recTest (O : Opens ℂ) {ρ : TestC} (hρ : ∫ x, ρ x = 1) (φ : TestOn O) :
    ∫ x, recTest O ρ φ x = 0 :=
  GFFLaw.integral_sub_smul hρ (inclTest O φ)

theorem tsupport_sub_smul_subset (f g : ℂ → ℝ) (c : ℝ) :
    tsupport (f - c • g) ⊆ tsupport f ∪ tsupport g := by
  have hs : support (f - c • g) ⊆ support f ∪ support g := by
    intro x hx
    by_contra hn
    simp only [mem_union, mem_support, not_or, not_not] at hn
    exact hx (by simp only [Pi.sub_apply, Pi.smul_apply, hn.1, hn.2, smul_zero, sub_zero])
  exact (closure_mono hs).trans closure_union.subset

theorem tsupport_recTest_subset (O : Opens ℂ) {ρ : TestC} (hρ : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (φ : TestOn O) : tsupport (recTest O ρ φ : ℂ → ℝ) ⊆ O := by
  rw [coe_recTest]
  exact (tsupport_sub_smul_subset _ _ _).trans (union_subset φ.tsupport_subset hρ)

/-- The recentring of a mean-zero test function supported in `O` is itself. -/
theorem recTest_testOnOfSupp (O : Opens ℂ) (ρ : TestC) {g : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ O)
    (hg0 : ∫ x, g x = 0) : recTest O ρ (testOnOfSupp O g hg) = g := by
  ext y
  rw [coe_recTest]
  show g y - (∫ x, g x) • ρ y = g y
  rw [hg0, zero_smul, sub_zero]

/-! ## 3. T4, deterministic step -/

section Deterministic

variable {ϕ : ℂ → ℂ} {W V : Set ℂ}

/-- The open set `ϕ(V)`. -/
def imOpens (hϕ : IsConfNbhd ϕ W V) : Opens ℂ := ⟨ϕ '' V, hϕ.isOpen_image⟩

theorem coe_imOpens (hϕ : IsConfNbhd ϕ W V) : (imOpens hϕ : Set ℂ) = ϕ '' V :=
  rfl

theorem confPullFun_sub_smul {ϕ : ℂ → ℂ} {W : Set ℂ} (f g : ℂ → ℝ) (c : ℝ) :
    confPullFun ϕ W (f - c • g) = confPullFun ϕ W f - c • confPullFun ϕ W g := by
  funext y
  by_cases hy : y ∈ W
  · simp only [confPullFun_of_mem hy, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [confPullFun_of_notMem hy, Pi.sub_apply, Pi.smul_apply, smul_zero, sub_zero]

/-- The pullback of a recentred test function is the recentred pullback. -/
theorem confPull_recTest (hϕ : IsConfNbhd ϕ W V) {ρ : TestC}
    (hρ : tsupport (ρ : ℂ → ℝ) ⊆ ϕ '' V) (φ : TestOn (imOpens hϕ)) :
    confPull ϕ W (recTest (imOpens hϕ) ρ φ) =
      confPullOnCLM hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn (imOpens hϕ) hϕ.image_subset φ -
        (∫ x, φ x) • confPullOnCLM hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn (imOpens hϕ)
          hϕ.image_subset (testOnOfSupp (imOpens hϕ) ρ hρ) := by
  refine confPull_eq hϕ (tsupport_recTest_subset (imOpens hϕ) hρ φ) ?_
  rw [isConfPull_iff, coe_recTest]
  funext y
  show confPullFun ϕ W φ y - (∫ x, φ x) • confPullFun ϕ W ρ y = _
  rw [confPullFun_sub_smul]
  rfl

/-- **T4, deterministic step.** Let `m_j = ι φ_j − (∫ φ_j) ρ` for the countable generating family
`φ_j = distGen (ϕ(V)) j` of `𝓓(ϕ(V))`. If `x̄(m_j) = x(τ m_j)` for all `j`, then
`x̄(g) = x(τ g)` for every mean-zero test function `g` supported in `ϕ(V)`. -/
theorem apply_eq_apply_confPull_of_distGen (hϕ : IsConfNbhd ϕ W V) {ρ : TestC}
    (hρU : tsupport (ρ : ℂ → ℝ) ⊆ ϕ '' V) {xbar x : DistC}
    (hj : ∀ j, xbar (recTest (imOpens hϕ) ρ (distGen (imOpens hϕ) j)) =
      x (confPull ϕ W (recTest (imOpens hϕ) ρ (distGen (imOpens hϕ) j))))
    (g : TestC0On (ϕ '' V)) : xbar g.1.1 = x (confPull ϕ W g.1.1) := by
  set O := imOpens hϕ with hOdef
  set τ := confPullOnCLM hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn O hϕ.image_subset with hτdef
  set ρO : TestOn O := testOnOfSupp O ρ hρU with hρOdef
  -- the two distributions on `O`
  set A : DistOn O := restrictTo O (GFFLaw.recenter ρ xbar) with hAdef
  set B : DistOn O := toDistOn O (x.comp τ) - x (τ ρO) • intDist O with hBdef
  have hA : ∀ φ : TestOn O, A φ = xbar (recTest O ρ φ) := fun φ => by
    show GFFLaw.recenter ρ xbar (inclTest O φ) = _
    rw [GFFLaw.recenter_apply]
    rfl
  have hB : ∀ φ : TestOn O, B φ = x (confPull ϕ W (recTest O ρ φ)) := fun φ => by
    show x (τ φ) - x (τ ρO) * intDist O φ = _
    rw [confPull_recTest hϕ hρU φ, intDist_apply, map_sub, map_smul, smul_eq_mul]
    ring
  have hAB : A = B :=
    injective_distOn_pairings O (funext fun j => by
      show A (distGen O j) = B (distGen O j)
      rw [hA, hB]
      exact hj j)
  have key := DFunLike.congr_fun hAB (testOnOfSupp O g.1.1 g.2)
  rw [hA, hB, recTest_testOnOfSupp O ρ g.2 g.1.2] at key
  exact key

end Deterministic

/-! ## 4. T4, core: the extension -/

section Core

variable {ϕ : ℂ → ℂ} {W V : Set ℂ}

/-- The pullback of the zero test function is zero. -/
theorem confPull_zero (hϕ : IsConfNbhd ϕ W V) : confPull ϕ W 0 = 0 := by
  refine confPull_eq hϕ (by simp) fun y => ?_
  simp

/-- **T4 (CC0 D17.2), core.** Let `h` be a whole-plane GFF whose pullback process
`(h(τ g))_{g ∈ 𝓓₀(ϕ(V))}` has the law of `(h(g))_g` (GA4's A3 for Möbius maps). Then on `Ω × DistC`
there is a probability measure `P'` with first marginal `P` (a.s. statements about the first
coordinate transfer back to `P`) under which `h̄ = snd` is a whole-plane GFF and, almost surely,
`h̄(g) = h(τ g)` for every mean-zero test function `g` supported in `ϕ(V)`. -/
theorem exists_extension_confPull (hϕ : IsConfNbhd ϕ W V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P)
    (hlaw : P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1)) =
      P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1)) :
    ∃ P' : Measure (Ω × DistC), IsProbabilityMeasure P' ∧ P'.map Prod.fst = P ∧
      (∀ q : Ω → Prop, (∀ᵐ p ∂P', q p.1) → ∀ᵐ ω ∂P, q ω) ∧
      IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' ∧
      ∀ᵐ p ∂P', ∀ g : TestC0On (ϕ '' V), p.2 g.1.1 = h p.1 (confPull ϕ W g.1.1) := by
  rcases (ϕ '' V).eq_empty_or_nonempty with hU | hU
  · -- `ϕ(V) = ∅`: every mean-zero test function supported in `ϕ(V)` is zero
    have hY : Measurable fun (_ : Ω) (i : Empty) => (i.elim : ℝ) :=
      measurable_pi_iff.2 fun i => i.elim
    have hlaw' : P.map (fun (_ : Ω) (i : Empty) => (i.elim : ℝ)) =
        P.map (fun ω (i : Empty) => h ω (i.elim : TestC0).1) :=
      congrArg (Measure.map · P) (funext fun _ => funext fun i => i.elim)
    obtain ⟨P', hP', hfst, htr, hsnd, -⟩ :=
      exists_extension_of_map_eq (fun i : Empty => i.elim) P hY hh hlaw'
    refine ⟨P', hP', hfst, htr, hsnd, ae_of_all _ fun p g => ?_⟩
    have hg0 : g.1.1 = 0 := TestFunction.ext fun y =>
      image_eq_zero_of_notMem_tsupport fun hy => by
        have := g.2 hy
        rw [hU] at this
        exact this
    rw [hg0, map_zero, confPull_zero hϕ, map_zero]
  · obtain ⟨ρ, hρU, hρ⟩ := exists_testC_integral_eq_one hϕ.isOpen_image hU
    set O := imOpens hϕ with hOdef
    -- the countable recentred family `m_j`
    set m : ℕ × ℕ → TestC := fun j => recTest O ρ (distGen O j) with hmdef
    set eU : ℕ × ℕ → TestC0On (ϕ '' V) := fun j =>
      ⟨⟨m j, integral_recTest O hρ _⟩, tsupport_recTest_subset O hρU _⟩ with heUdef
    set Y : Ω → ℕ × ℕ → ℝ := fun ω j => h ω (confPull ϕ W (m j)) with hYdef
    have hY : Measurable Y :=
      measurable_pi_iff.2 fun j => (GFFInv.measurable_pair _).comp hh.measurable
    have hX1 : Measurable fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1) :=
      measurable_pi_iff.2 fun g => (GFFInv.measurable_pair _).comp hh.measurable
    have hX2 : Measurable fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1 :=
      measurable_pi_iff.2 fun g => (GFFInv.measurable_pair _).comp hh.measurable
    set π : (TestC0On (ϕ '' V) → ℝ) → (ℕ × ℕ → ℝ) := fun F j => F (eU j) with hπdef
    have hπ : Measurable π := measurable_pi_iff.2 fun j => measurable_pi_apply _
    have hlawY : P.map Y = P.map (fun ω j => h ω (eU j).1.1) := by
      have e1 : Y = π ∘ fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1) := rfl
      have e2 : (fun ω j => h ω (eU j).1.1) = π ∘ fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1 :=
        rfl
      rw [e1, e2, ← Measure.map_map hπ hX1, ← Measure.map_map hπ hX2, hlaw]
    obtain ⟨P', hP', hfst, htr, hsnd, hae⟩ :=
      exists_extension_of_map_eq (fun j => (eU j).1) P hY hh hlawY
    refine ⟨P', hP', hfst, htr, hsnd, ?_⟩
    filter_upwards [hae] with p hp g
    exact apply_eq_apply_confPull_of_distGen hϕ hρU hp g

end Core

/-! ## 5. T4, coupling form -/

section Coupling

variable {ϕ : ℂ → ℂ} {W V : Set ℂ}

/-- A smooth cutoff: `C^∞`, compactly supported in the open set `O`, equal to `1` on the compact
`K ⊆ O` (smooth Urysohn on a thickening of `K`). -/
theorem exists_smooth_cutoff {K O : Set ℂ} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ β : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧ tsupport β ⊆ O ∧
      ∀ x ∈ K, β x = 1 := by
  obtain ⟨η, hη, hηO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨f, hfd, -, hfs, hf1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := η) (E := K))
    (isClosed_cthickening (δ := η / 2) (E := K))
    (cthickening_subset_thickening' hη (by linarith) K)
  have hts : tsupport f ⊆ cthickening η K := by
    rw [tsupport, hfs]
    exact closure_thickening_subset_cthickening η K
  exact ⟨f, hfd, (hK.cthickening (r := η)).of_isClosed_subset (isClosed_tsupport f) hts,
    hts.trans hηO, fun x hx => (hf1 x).1 (self_subset_cthickening K hx)⟩

/-- `log |ψ'|` (with `ψ = invFunOn ϕ W`) is smooth on `ϕ(W)`. -/
theorem contDiffOn_log_norm_deriv_invFunOn (hW : IsOpen W) (hd : DifferentiableOn ℂ ϕ W)
    (hi : InjOn ϕ W) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log ‖deriv (invFunOn ϕ W) y‖)
      (ϕ '' W) := by
  have hψ := invFunOn_leftInv hi
  have hWo : IsOpen (ϕ '' W) := isOpen_image_conf hW hd hi
  have hdψ : DifferentiableOn ℂ (deriv (invFunOn ϕ W)) (ϕ '' W) :=
    (differentiableOn_leftInv hW hd hi hψ).deriv hWo
  have hcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (invFunOn ϕ W)) (ϕ '' W) :=
    (hdψ.contDiffOn hWo).restrict_scalars ℝ
  intro y hy
  have hne : deriv (invFunOn ϕ W) y ≠ 0 :=
    right_ne_zero_of_mul_eq_one (deriv_mul_deriv_leftInv hW hd hi hψ hy)
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ‖deriv (invFunOn ϕ W) y‖) y :=
    (contDiffAt_norm ℝ hne).comp y (hcd.contDiffAt (hWo.mem_nhds hy))
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.log ‖deriv (invFunOn ϕ W) y‖ :=
    Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hne)
  exact (h2.comp y h1).contDiffWithinAt

/-- **The drift `G`**: a test function equal to `a · log |ψ'|` on `ϕ(V)` (`ψ = invFunOn ϕ W`). -/
theorem exists_testC_eq_log_deriv (hϕ : IsConfNbhd ϕ W V) (a : ℝ) :
    ∃ G : TestC, ∀ y ∈ ϕ '' V, G y = a * Real.log ‖deriv (invFunOn ϕ W) y‖ := by
  have hW := hϕ.isOpen_W
  have hd := hϕ.differentiableOn
  have hi := hϕ.injOn
  have hWo : IsOpen (ϕ '' W) := isOpen_image_conf hW hd hi
  have hKW : ϕ '' closure V ⊆ ϕ '' W := image_mono hϕ.closure_subset
  obtain ⟨β, hβd, hβc, hβW, hβ1⟩ := exists_smooth_cutoff hϕ.isCompact_image_closure hWo hKW
  set L : ℂ → ℝ := fun y => Real.log ‖deriv (invFunOn ϕ W) y‖ with hLdef
  have hL := contDiffOn_log_norm_deriv_invFunOn hW hd hi
  have hzero : ∀ z ∉ tsupport β, a * (β z * L z) = 0 := fun z hz => by
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, mul_zero]
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z => a * (β z * L z) :=
    QuantumZipper.K3.contDiff_of_contDiffOn_of_support_subset hWo hβc.isCompact hβW
      (contDiffOn_const.mul (hβd.contDiffOn.mul hL)) hzero
  refine ⟨⟨fun z => a * (β z * L z), hcd, HasCompactSupport.intro hβc.isCompact hzero,
    subset_univ _⟩, fun y hy => ?_⟩
  show a * (β y * L y) = _
  rw [hβ1 y (image_mono subset_closure hy), one_mul]

/-- Constants are invisible to mean-zero pairings. -/
theorem pair0On_addFun_sub_const (U : Set ℂ) (x : DistC) (F : C(ℂ, ℝ)) (c : ℝ) :
    pair0On U (addFun x (F - ContinuousMap.const ℂ c)) = pair0On U (addFun x F) := by
  funext g
  simp only [pair0On, addFun]
  show x g.1.1 + ofCont (F - ContinuousMap.const ℂ c) g.1.1 = x g.1.1 + ofCont F g.1.1
  rw [ofCont_apply, ofCont_apply]
  congr 1
  have hgF : Integrable fun y => g.1.1 y * F y :=
    (g.1.1.continuous.mul F.continuous).integrable_of_hasCompactSupport
      g.1.1.hasCompactSupport.mul_right
  have hgc : Integrable fun y => g.1.1 y * c :=
    (g.1.1.continuous.mul continuous_const).integrable_of_hasCompactSupport
      g.1.1.hasCompactSupport.mul_right
  have e : (fun y => g.1.1 y * (F - ContinuousMap.const ℂ c) y) =
      fun y => g.1.1 y * F y - g.1.1 y * c := by
    funext y
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
    ring
  rw [e, integral_sub hgF hgc, integral_mul_const, g.1.2, zero_mul, sub_zero]

/-- **T4 (CC0 D17.2), coupling form.** Under the hypotheses of `exists_extension_confPull`, on
`Ω × DistC` there are a probability measure `P'` (first marginal `P`, transfer back to `P`), a test
function `G = Q log|ψ'|` on `ϕ(V)` and a measurable random constant `c` such that `h ∘ fst` and
`h̄ = snd` are whole-plane GFFs, `(h ∘ fst, h̄, G − c)` is a.s. a conformal coupling for
`(ϕ, W, V)`, and a.s. `confPair0 γ ϕ W V h = pair0On (ϕ(V)) (h̄ + G)`.
This is the input of one application of `ConfCov γ D` (CC12b). -/
theorem exists_confCoupling_extension (hϕ : IsConfNbhd ϕ W V) (γ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P)
    (hlaw : P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω (confPull ϕ W g.1.1)) =
      P.map (fun ω (g : TestC0On (ϕ '' V)) => h ω g.1.1)) :
    ∃ (P' : Measure (Ω × DistC)) (G : TestC) (c : Ω × DistC → ℝ),
      IsProbabilityMeasure P' ∧ P'.map Prod.fst = P ∧
      (∀ q : Ω → Prop, (∀ᵐ p ∂P', q p.1) → ∀ᵐ ω ∂P, q ω) ∧
      IsWholePlaneGFF (fun p : Ω × DistC => h p.1) P' ∧
      IsWholePlaneGFF (fun p : Ω × DistC => p.2) P' ∧ Measurable c ∧
      (∀ y ∈ ϕ '' V, G y = Q γ * Real.log ‖deriv (invFunOn ϕ W) y‖) ∧
      (∀ᵐ p ∂P', IsConfCoupling γ ϕ W V (h p.1) p.2 (testCont G - ContinuousMap.const ℂ (c p))) ∧
      ∀ᵐ p ∂P', confPair0 γ ϕ W V (h p.1) = pair0On (ϕ '' V) (addFun p.2 (testCont G)) := by
  obtain ⟨P', hP', hfst, htr, hsnd, hae⟩ := exists_extension_confPull hϕ P hh hlaw
  obtain ⟨G, hG⟩ := exists_testC_eq_log_deriv hϕ (Q γ)
  have hψ := invFunOn_leftInv hϕ.injOn
  -- `h ∘ fst` is a whole-plane GFF under `P'`
  have hfstG : IsWholePlaneGFF (fun p : Ω × DistC => h p.1) P' := by
    refine isWholePlaneGFF_of_map_pairProc_eq (hh.measurable.comp measurable_fst) hh ?_
    have e1 : GFFLaw.pairProc (fun p : Ω × DistC => h p.1) = GFFLaw.pairProc h ∘ Prod.fst := rfl
    rw [e1, ← Measure.map_map (GFFLaw.measurable_pairProc hh.measurable) measurable_fst, hfst]
  -- the coupling identity, reduced to `h(τ g) = h̄(g) − c ∫ g` for all `g` supported in `ϕ(V)`
  have hcoup : ∀ (x xbar : DistC) (c : ℝ),
      (∀ g : TestC, tsupport (g : ℂ → ℝ) ⊆ ϕ '' V → x (confPull ϕ W g) = xbar g - c * ∫ y, g y) →
      IsConfCoupling γ ϕ W V x xbar (testCont G - ContinuousMap.const ℂ c) := by
    intro x xbar c hx g τg hg hτ
    have hτg : τg = confPull ϕ W g := (confPull_eq hϕ hg hτ).symm
    rw [IsConfPull.integral_log_mul hϕ hψ hg hτ, hτg, hx g hg]
    have hGg : Q γ * ∫ y, Real.log ‖deriv (invFunOn ϕ W) y‖ * g y = ∫ y, G y * g y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      by_cases hy : y ∈ ϕ '' V
      · simp only [hG y hy]
        ring
      · have : g y = 0 := image_eq_zero_of_notMem_tsupport fun h' => hy (hg h')
        simp only [this, mul_zero]
    have hgG : Integrable fun y => G y * g y :=
      (G.continuous.mul g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
    have hgc : Integrable fun y => c * g y :=
      (continuous_const.mul g.continuous).integrable_of_hasCompactSupport
        g.hasCompactSupport.mul_left
    have hR : ∫ y, (testCont G - ContinuousMap.const ℂ c) y * g y =
        (∫ y, G y * g y) - c * ∫ y, g y := by
      have e : (fun y => (testCont G - ContinuousMap.const ℂ c) y * g y) =
          fun y => G y * g y - c * g y := by
        funext y
        simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
        show (G y - c) * g y = _
        ring
      rw [e, integral_sub hgG hgc, integral_const_mul]
    rw [hR, mul_neg, sub_neg_eq_add, hGg]
    ring
  rcases (ϕ '' V).eq_empty_or_nonempty with hU | hU
  · -- `ϕ(V) = ∅`: every test function supported in `ϕ(V)` is zero
    refine ⟨P', G, fun _ => 0, hP', hfst, htr, hfstG, hsnd, measurable_const, hG,
      ae_of_all _ fun p => hcoup _ _ _ fun g hg => ?_, ae_of_all _ fun p => ?_⟩
    · have hg0 : g = 0 := TestFunction.ext fun y =>
        image_eq_zero_of_notMem_tsupport fun hy => by
          have := hg hy
          rw [hU] at this
          exact this
      rw [hg0, confPull_zero hϕ, map_zero, map_zero]
      simp
    · funext g
      have hg0 : g.1.1 = 0 := TestFunction.ext fun y =>
        image_eq_zero_of_notMem_tsupport fun hy => by
          have := g.2 hy
          rw [hU] at this
          exact this
      simp only [confPair0, pair0On, hg0, confPull_zero hϕ, map_zero]
      simp
  · obtain ⟨ρ, hρU, hρ⟩ := exists_testC_integral_eq_one hϕ.isOpen_image hU
    set c : Ω × DistC → ℝ := fun p => p.2 ρ - h p.1 (confPull ϕ W ρ) with hcdef
    have hcm : Measurable c :=
      ((GFFInv.measurable_pair ρ).comp measurable_snd).sub
        ((GFFInv.measurable_pair _).comp (hh.measurable.comp measurable_fst))
    have hcouple : ∀ᵐ p ∂P', IsConfCoupling γ ϕ W V (h p.1) p.2
        (testCont G - ContinuousMap.const ℂ (c p)) := by
      filter_upwards [hae] with p hp
      refine hcoup _ _ _ fun g hg => ?_
      -- split `g = g₀ + (∫ g) ρ` with `g₀` mean-zero
      set a : ℝ := ∫ y, g y with hadef
      set g₀ : TestC := g - a • ρ with hg₀def
      have hg₀0 : ∫ y, g₀ y = 0 := GFFLaw.integral_sub_smul hρ g
      have hg₀U : tsupport (g₀ : ℂ → ℝ) ⊆ ϕ '' V :=
        (tsupport_sub_smul_subset _ _ _).trans (union_subset hg hρU)
      have h₀ := hp ⟨⟨g₀, hg₀0⟩, hg₀U⟩
      have hsplit : confPull ϕ W g = confPull ϕ W g₀ + a • confPull ϕ W ρ := by
        refine confPull_eq hϕ hg ?_
        rw [isConfPull_iff]
        funext y
        have e1 := congrFun (isConfPull_iff.1 (isConfPull_confPull hϕ hg₀U)) y
        have e2 := congrFun (isConfPull_iff.1 (isConfPull_confPull hϕ hρU)) y
        show confPull ϕ W g₀ y + a • confPull ϕ W ρ y = _
        rw [e1, e2]
        have e3 : confPullFun ϕ W (⇑g₀) = confPullFun ϕ W ⇑g - a • confPullFun ϕ W ⇑ρ :=
          confPullFun_sub_smul (ϕ := ϕ) (W := W) ⇑g ⇑ρ a
        rw [e3]
        simp only [Pi.sub_apply, Pi.smul_apply]
        ring
      have hgsplit : g = g₀ + a • ρ := by
        rw [hg₀def, sub_add_cancel]
      rw [hsplit, map_add, map_smul, ← h₀]
      simp only [hcdef]
      conv_rhs => rw [hgsplit, map_add, map_smul]
      simp only [smul_eq_mul]
      ring
    refine ⟨P', G, c, hP', hfst, htr, hfstG, hsnd, hcm, hG, hcouple, ?_⟩
    filter_upwards [hcouple] with p hp
    rw [IsConfCoupling.confPair0_eq hϕ hp, pair0On_addFun_sub_const]

end Coupling

end SmallGammaGeodesics.CC
