import SupercriticalConformalCovariance.GM24.Bridge
import SupercriticalConformalCovariance.GM24.TVReduce
import SupercriticalConformalCovariance.ZBConformal.JointMarkov

/-!
# The decomposition input of GM (2.6), from the conformal invariance of the zero-boundary GFF's joint Markov theorem

GM l. 547 ("write `h|_{U_n} = h̊_n + 𝔥_n` …"), repaired (`gm:lem-tv-conv#decomposition`): on a bounded disk `D ⊆ U` and
the image `V′ = φ(D)`, the field `h ∘ φ⁻¹` on `V′` is `z + H₀ + c` with `z` a zero-boundary GFF on `V′`,
`H₀` harmonic on `V′` and **independent** of `z` (full processes), and `c` a random constant (the circle
average used to recentre `h`).

* `exists_pullback_markov_bounded_indep`: `exists_pullback_markov_normAt_joint` after recentring,
  keeping the independent harmonic part and the constant separate;
* `confPullFun_eq_of_subset`: `|φ'|² (g ∘ φ)` does not depend on the domain `D ⊆ W` for `supp g ⊆ φ(D)`;
* `decomp_invPullDist`: the decomposition of `(h ∘ φ⁻¹)|_B` in the form of the hypothesis `hdec` of
  `tendsto_tvDist_gm24`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter Topology
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GM24

open SupercriticalConformalCovariance.ZBConformal
open SmallGammaGeodesics.CC (confPullFun confPullFun_of_mem confPullFun_of_notMem confPullOnCLM
  coe_confPullOnCLM isOpen_image_conf)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- **Markov decomposition with independence and a separate constant** (from the conformal invariance of the zero-boundary GFF). -/
theorem exists_pullback_markov_bounded_indep {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (hh : IsWholePlaneGFF h P)
    (hVb : Bornology.IsBounded (V : Set ℂ)) :
    ∃ (z : Ω → DistOn U) (H : Ω → ℂ → ℝ) (c : Ω → ℝ),
      IsZeroBoundaryGFF U z P ∧
      Measurable (fun p : Ω × U => H p.1 p.2) ∧ Measurable c ∧
      IndepFun (fun ω (ψ : TestOn U) => z ω ψ) (fun ω (x : U) => H ω x) P ∧
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (H ω) (U : Set ℂ) ∧
        ∀ ψ : TestOn U,
          (distPullback hφ (restrictTo V (h ω)) - z ω) ψ =
            (∫ x, H ω x * ψ x) + c ω * ∫ x, ψ x) := by
  obtain ⟨r, hr, hdisj⟩ := exists_radius_disjoint_sphere hVb
  let c : Ω → ℝ := fun ω => circleAvg (h ω) r 0
  have hcm : Measurable c := (measurable_circleAvg_left r 0).comp hh.measurable
  let h₀ : Ω → DistC := fun ω => addConst (h ω) (-c ω)
  obtain ⟨hh₀, hn₀⟩ := DFGPS.isNormalizedAt_recenter hh hr 0
  obtain ⟨z, H₀, hzlaw, hHm, hind, hpair⟩ :=
    exists_pullback_markov_normAt_joint hφ hh₀ hr hn₀ hdisj
  refine ⟨z, H₀, c, hzlaw, hHm, hcm, hind, ?_⟩
  filter_upwards [hpair] with ω ⟨hHarm, hrep⟩
  refine ⟨hHarm, fun ψ => ?_⟩
  let χ : TestOn V := confPushTest hφ ψ
  let t : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) χ
  have hconst_eval : (restrictTo V (h₀ ω)) χ =
      (restrictTo V (h ω)) χ - c ω * ∫ x, χ x := by
    change addConst (h ω) (-(c ω)) t = h ω t - c ω * ∫ x, χ x
    rw [GFFInv.addConst_apply]
    have ht : ∀ x, t x = χ x := by intro x; simp [t, TestFunction.monoCLM_apply]
    simp_rw [ht]
    ring
  have hstep : (distPullback hφ (restrictTo V (h ω)) - z ω) ψ =
      (distPullback hφ (restrictTo V (h₀ ω)) - z ω) ψ + c ω * ∫ x, ψ x := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, distPullback_apply,
      distPullback_apply]
    change (restrictTo V (h ω)) χ - z ω ψ =
      ((restrictTo V (h₀ ω)) χ - z ω ψ) + c ω * ∫ x, ψ x
    have hone := integral_mul_confPushTest hφ ψ (fun _ => (1 : ℝ))
    have hone' : (∫ x, χ x) = ∫ x, ψ x := by
      simpa only [χ, one_mul] using hone
    rw [← hone', hconst_eval]
    ring
  rw [hstep, hrep ψ]

/-- `|φ'|² (g ∘ φ)` does not depend on the injectivity domain, for `g` supported in `φ(D)`, `D ⊆ W`. -/
theorem confPullFun_eq_of_subset {φ : ℂ → ℂ} {W D : Set ℂ} (hi : InjOn φ W) (hDW : D ⊆ W)
    {g : ℂ → ℝ} (hg : tsupport g ⊆ φ '' D) : confPullFun φ D g = confPullFun φ W g := by
  funext x
  by_cases hxD : x ∈ D
  · rw [confPullFun_of_mem hxD, confPullFun_of_mem (hDW hxD)]
  · rw [confPullFun_of_notMem hxD]
    by_cases hxW : x ∈ W
    · rw [confPullFun_of_mem hxW]
      have : g (φ x) = 0 := image_eq_zero_of_notMem_tsupport fun hx => by
        obtain ⟨y, hy, hyx⟩ := hg hx
        exact hxD (hi (hDW hy) hxW hyx ▸ hy)
      rw [this, mul_zero]
    · rw [confPullFun_of_notMem hxW]

/-- The image `φ(D)` as an open set. -/
def imageOpens {φ : ℂ → ℂ} {D : Opens ℂ} (hd : DifferentiableOn ℂ φ D) (hi : InjOn φ D) :
    Opens ℂ :=
  ⟨φ '' D, isOpen_image_conf D.isOpen hd hi⟩

theorem isConformalBijection_image {φ : ℂ → ℂ} {D : Opens ℂ} (hd : DifferentiableOn ℂ φ D)
    (hi : InjOn φ D) : IsConformalBijection φ D (imageOpens hd hi) :=
  ⟨hd, hi.bijOn_image⟩

/-- **The decomposition of `(h ∘ φ⁻¹)|_B`** in the form of `hdec`: for `φ` holomorphic and injective on
the open `W`, a bounded open `D ⊆ W` and an open `B ⊆ φ(D)`, almost surely, for every `g ∈ 𝓓(B)`,
`(h ∘ φ⁻¹, g) = (z, g) + ∫ g H + c ∫ g` with `z` a zero-boundary GFF on `φ(D)`, `H` harmonic on `φ(D)` and
independent of `z`, `c` a random constant. -/
theorem decomp_invPullDist (hh : IsWholePlaneGFF h P) {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W)
    (hd : DifferentiableOn ℂ φ W) (hi : InjOn φ W) {D : Opens ℂ} (hDW : (D : Set ℂ) ⊆ W)
    (hDb : Bornology.IsBounded (D : Set ℂ)) {B : Opens ℂ} (hB : (B : Set ℂ) ⊆ φ '' D) :
    ∃ (z : Ω → DistOn (imageOpens (hd.mono hDW) (hi.mono hDW))) (H : Ω → ℂ → ℝ) (c : Ω → ℝ),
      IsZeroBoundaryGFF (imageOpens (hd.mono hDW) (hi.mono hDW)) z P ∧
      Measurable (fun p : Ω × (imageOpens (hd.mono hDW) (hi.mono hDW)) => H p.1 p.2) ∧
      Measurable c ∧
      IndepFun (fun ω (ψ : TestOn (imageOpens (hd.mono hDW) (hi.mono hDW))) => z ω ψ)
        (fun ω (x : imageOpens (hd.mono hDW) (hi.mono hDW)) => H ω x) P ∧
      ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (H ω) (φ '' D) ∧
        ∀ g : TestOn B,
          invPullDist hW hd hi B (hB.trans (image_mono hDW)) (h ω) g =
            restrictDist (show B ≤ imageOpens (hd.mono hDW) (hi.mono hDW) from hB) (z ω) g +
              (∫ x, g x * H ω x) + c ω * ∫ x, g x := by
  set V' := imageOpens (hd.mono hDW) (hi.mono hDW)
  have hφD := isConformalBijection_image (hd.mono hDW) (hi.mono hDW)
  have hinv := isConformalBijection_invFunOn hφD
  obtain ⟨z, H, c, hz, hHm, hcm, hind, hae⟩ :=
    exists_pullback_markov_bounded_indep hinv hh hDb
  refine ⟨z, H, c, hz, hHm, hcm, hind, ?_⟩
  filter_upwards [hae] with ω ⟨hHarm, hrep⟩
  refine ⟨hHarm, fun g => ?_⟩
  have hBV : B ≤ V' := hB
  let G : TestOn V' := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V') g
  have hG : ⇑G = ⇑g := coe_monoCLM_le hBV g
  have h1 := hrep G
  rw [distPullback_inv_eq hφD, ContinuousLinearMap.sub_apply] at h1
  have e1 : invPullDist hW hd hi B (hB.trans (image_mono hDW)) (h ω) g =
      invPullDist D.isOpen (hd.mono hDW) (hi.mono hDW) V'
        (subset_image_of_isConformalBijection hφD) (h ω) G := by
    show h ω (confPullOnCLM _ _ _ B _ g) = h ω (confPullOnCLM _ _ _ V' _ G)
    congr 1
    ext x
    rw [coe_confPullOnCLM, coe_confPullOnCLM, hG,
      confPullFun_eq_of_subset hi hDW (g.tsupport_subset.trans hB)]
  rw [e1, restrictDist_apply]
  change _ = z ω G + _ + _
  have e2 : (∫ x, g x * H ω x) = ∫ x, H ω x * G x := by
    rw [hG]; congr 1; funext x; ring
  have e3 : (∫ x, g x) = ∫ x, G x := by rw [hG]
  rw [e2, e3]
  linarith

theorem measurable_restrictDist {B V : Opens ℂ} (hBV : B ≤ V) : Measurable (restrictDist hBV) :=
  measurable_distOn_iff.mpr fun g => measurable_distOn_apply _

/-- The disk `B(0, R)` as an open set. -/
def ballOpens (R : ℝ) : Opens ℂ := ⟨ball 0 R, isOpen_ball⟩

/-- **The decomposition data of `tendsto_tvDist_gm24` exist** (GM l. 547 with the disk repair
`gm:lem-tv-conv#decomposition`, with its recentring repair): radii `R_n → ∞` with `B(0,R_n) ⊆ U_n`, and `X, Y, C`
satisfying `hdec`, `hY`, where eventually `X n = z_n|_B` for a zero-boundary GFF `z_n` on
`V′_n = φ_n(B(0,R_n))` independent of the harmonic part `Y n` (full processes on `V′_n`). -/
theorem exists_decomp_seq {U : ℕ → Set ℂ} {φ : ℕ → ℂ → ℂ} {α : ℂ}
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹))
    (hh : IsWholePlaneGFF h P) {B : Opens ℂ} (hBb : Bornology.IsBounded (B : Set ℂ)) :
    ∃ (Rr : ℕ → ℝ) (hR : ∀ n, (ballOpens (Rr n) : Set ℂ) ⊆ U n)
      (X : ℕ → Ω → DistOn B) (Y : ℕ → Ω → ℂ → ℝ) (C : ℕ → Ω → ℝ),
      Tendsto Rr atTop atTop ∧ (∀ n, Measurable (X n)) ∧ (∀ n, Measurable (C n)) ∧
      (∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ hn : (B : Set ℂ) ⊆ φ n '' U n, ∀ g : TestOn B,
        invPullDist (hopen n) (hd n) (hinj n) B hn (h ω) g =
          X n ω g + (∫ x, g x * Y n ω x) + C n ω * ∫ x, g x) ∧
      (∀ᶠ n in atTop, ∀ᵐ ω ∂P, ContinuousOn (Y n ω) B) ∧
      (∀ᶠ n in atTop, ∃ hBn : (B : Set ℂ) ⊆ φ n '' ballOpens (Rr n),
        ∃ z : Ω → DistOn (imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n))),
          IsZeroBoundaryGFF _ z P ∧ (∀ ω, X n ω = restrictDist hBn (z ω)) ∧
          IndepFun (fun ω (ψ : TestOn (imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n)))) =>
            z ω ψ) (fun ω (x : imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n))) =>
            Y n ω x) P ∧
          Measurable (fun p : Ω × imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n)) =>
            Y n p.1 p.2)) := by
  obtain ⟨Rr, hRpos, hRlarge, hRsub⟩ := SupercriticalConformalCovariance.Univalent.exhaustion_radii hopen hzeroU hexhaust
  have hR : ∀ n, (ballOpens (Rr n) : Set ℂ) ⊆ U n := hRsub
  have key : ∀ n, ∃ (X : Ω → DistOn B) (Y : Ω → ℂ → ℝ) (C : Ω → ℝ),
      Measurable X ∧ Measurable C ∧ ∀ hBn : (B : Set ℂ) ⊆ φ n '' ballOpens (Rr n),
        (∀ᵐ ω ∂P, ∀ g : TestOn B,
          invPullDist (hopen n) (hd n) (hinj n) B (hBn.trans (image_mono (hR n))) (h ω) g =
            X ω g + (∫ x, g x * Y ω x) + C ω * ∫ x, g x) ∧
        (∀ᵐ ω ∂P, ContinuousOn (Y ω) B) ∧
        ∃ z : Ω → DistOn (imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n))),
          IsZeroBoundaryGFF _ z P ∧ (∀ ω, X ω = restrictDist hBn (z ω)) ∧
          IndepFun (fun ω (ψ : TestOn (imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n)))) =>
            z ω ψ) (fun ω (x : imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n))) =>
            Y ω x) P ∧
          Measurable (fun p : Ω × imageOpens ((hd n).mono (hR n)) ((hinj n).mono (hR n)) =>
            Y p.1 p.2) := by
    intro n
    by_cases hBn : (B : Set ℂ) ⊆ φ n '' ballOpens (Rr n)
    · obtain ⟨z, H, c, hz, hHm, hcm, hind, hae⟩ :=
        decomp_invPullDist hh (hopen n) (hd n) (hinj n) (hR n) isBounded_ball hBn
      refine ⟨fun ω => restrictDist hBn (z ω), H, c,
        (measurable_restrictDist hBn).comp hz.measurable, hcm, fun _ => ⟨?_, ?_, z, hz,
          fun ω => rfl, hind, hHm⟩⟩
      · filter_upwards [hae] with ω hω
        exact hω.2
      · filter_upwards [hae] with ω hω
        exact hω.1.continuousOn.mono hBn
    · exact ⟨fun _ => 0, fun _ _ => 0, fun _ => 0, measurable_const, measurable_const,
        fun h' => absurd h' hBn⟩
  choose X Y C hXm hCm hprop using key
  obtain ⟨ρ, hρ⟩ := hBb.subset_closedBall (0 : ℂ)
  have hexD : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ ballOpens (Rr n) := by
    intro K hK
    obtain ⟨σ, hσ⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    filter_upwards [hRlarge.eventually_gt_atTop σ] with n hn
    exact hσ.trans (closedBall_subset_ball hn)
  have himg := eventually_closedBall_subset_image (U := fun n => (ballOpens (Rr n) : Set ℂ))
    (fun n => isOpen_ball) (fun n => mem_ball_self (hRpos n)) hexD
    (fun n => (hd n).mono (hR n)) (fun n => (hinj n).mono (hR n)) hzero hα hder ρ
  have hBn : ∀ᶠ n in atTop, (B : Set ℂ) ⊆ φ n '' ballOpens (Rr n) := by
    filter_upwards [himg] with n hn
    exact hρ.trans hn
  refine ⟨Rr, hR, X, Y, C, hRlarge, hXm, hCm, ?_, ?_, ?_⟩
  · filter_upwards [hBn] with n hn
    filter_upwards [(hprop n hn).1] with ω hω
    intro _ g
    exact hω g
  · filter_upwards [hBn] with n hn
    exact (hprop n hn).2.1
  · filter_upwards [hBn] with n hn
    exact ⟨hn, (hprop n hn).2.2⟩

/-- GM's Cameron–Martin shift (l. 560–561, scale repaired): `S = χ · (Y − (Y, f_r))`. -/
def cutoffShift {B : Opens ℂ} (χ : ℂ → ℝ) (fr : TestOn B) (Y : ℂ → ℝ) : ℂ → ℝ :=
  fun x => χ x * (Y x - smoothDist B Y fr)

/-- With `χ = 1` on `B`, the shift satisfies the cutoff hypothesis `hcut`. -/
theorem eqOn_cutoffShift {B : Opens ℂ} {χ : ℂ → ℝ} (hχ : EqOn χ 1 B) (fr : TestOn B)
    (Y : ℂ → ℝ) : EqOn (cutoffShift χ fr Y) (fun x => Y x - smoothDist B Y fr) B := by
  intro x hx
  simp only [cutoffShift, hχ hx, Pi.one_apply, one_mul]

end SupercriticalConformalCovariance.GM24
