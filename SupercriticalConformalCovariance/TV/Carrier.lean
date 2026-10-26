import SmallGammaGeodesics.CC.ExtensionPull
import LQGMetric.Field.ZeroBoundaryAffine

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace SupercriticalConformalCovariance.TV

open LQGMetric SmallGammaGeodesics SmallGammaGeodesics.CC

/-- No admissibility hypothesis is needed when the CM comparison is made on a disk. -/
theorem zbAdmissible_ball (z : ℂ) (r : ℝ) :
    ZBAdmissible ⟨Metric.ball z r, Metric.isOpen_ball⟩ :=
  zbAdmissible_of_isBounded Metric.isBounded_ball

/-- A fixed sequence of mean-zero local tests, obtained by recentering `distGen`. -/
def localMeanZeroGen (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (n : ℕ) : TestC0On O :=
  ⟨⟨recTest O ρ (distGen O (Nat.unpair n)),
      integral_recTest O hρ1 _⟩,
    tsupport_recTest_subset O hρO _⟩

/-- The same ball test regarded as a test on a containing domain. -/
def localMeanZeroGenOn (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) (n : ℕ) : TestOn D :=
  testOnOfSupp D (localMeanZeroGen O ρ hρO hρ1 n).1.1
    ((localMeanZeroGen O ρ hρO hρ1 n).2.trans hOD)

theorem coe_localMeanZeroGenOn (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) (n : ℕ) :
    ⇑(localMeanZeroGenOn O D hOD ρ hρO hρ1 n) =
      ⇑(localMeanZeroGen O ρ hρO hρ1 n).1.1 := rfl

/-- Observable on the fixed standard Borel carrier `ℕ → ℝ`. -/
def localCountablePath (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (x : DistC) : ℕ → ℝ :=
  fun n => x (localMeanZeroGen O ρ hρO hρ1 n).1.1

theorem measurable_localCountablePath (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1) :
    Measurable (localCountablePath O ρ hρO hρ1) :=
  measurable_pi_iff.mpr fun _ => measurable_distOn_apply _

/-- Coordinate map for a field on a containing domain. -/
def localCountablePathOn (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) (x : DistOn D) : ℕ → ℝ :=
  fun n => x (localMeanZeroGenOn O D hOD ρ hρO hρ1 n)

theorem measurable_localCountablePathOn (O D : Opens ℂ)
    (hOD : (O : Set ℂ) ⊆ D) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1) :
    Measurable (localCountablePathOn O D hOD ρ hρO hρ1) :=
  measurable_pi_iff.mpr fun _ => measurable_distOn_apply _

theorem localCountablePathOn_restrict (O D : Opens ℂ)
    (hOD : (O : Set ℂ) ⊆ D) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (x : DistC) :
    localCountablePathOn O D hOD ρ hρO hρ1 (restrictTo D x) =
      localCountablePath O ρ hρO hρ1 x := by
  funext n
  change x (inclTest D (localMeanZeroGenOn O D hOD ρ hρO hρ1 n)) =
    x (localMeanZeroGen O ρ hρO hρ1 n).1.1
  congr 1
  ext z
  rw [coe_inclTest, coe_localMeanZeroGenOn]

/-- The countable path space carries every local mean-zero pairing. -/
theorem localMeanZeroGen_determines (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    {x y : DistC}
    (heq : ∀ n : ℕ, x (localMeanZeroGen O ρ hρO hρ1 n).1.1 =
      y (localMeanZeroGen O ρ hρO hρ1 n).1.1)
    (g : TestC0On O) : x g.1.1 = y g.1.1 := by
  let A : DistOn O := restrictTo O x - x ρ • intDist O
  let B : DistOn O := restrictTo O y - y ρ • intDist O
  have hA : ∀ φ : TestOn O, A φ = x (recTest O ρ φ) := by
    intro φ
    change x (inclTest O φ) - x ρ * intDist O φ =
      x (inclTest O φ - (∫ z, inclTest O φ z) • ρ)
    rw [intDist_apply, map_sub, map_smul, smul_eq_mul]
    rw [coe_inclTest]
    ring
  have hB : ∀ φ : TestOn O, B φ = y (recTest O ρ φ) := by
    intro φ
    change y (inclTest O φ) - y ρ * intDist O φ =
      y (inclTest O φ - (∫ z, inclTest O φ z) • ρ)
    rw [intDist_apply, map_sub, map_smul, smul_eq_mul]
    rw [coe_inclTest]
    ring
  have hAB : A = B := by
    apply injective_distOn_pairings O
    funext j
    change A (distGen O j) = B (distGen O j)
    rw [hA, hB]
    simpa [localMeanZeroGen, Nat.unpair_pair] using heq (Nat.pair j.1 j.2)
  have key := DFunLike.congr_fun hAB (testOnOfSupp O g.1.1 g.2)
  rw [hA, hB, recTest_testOnOfSupp O ρ g.2 g.1.2] at key
  exact key

/-- The coordinate map exactly separates local distributions modulo constants. -/
theorem localCountablePath_eq_iff (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (x y : DistC) :
    localCountablePath O ρ hρO hρ1 x = localCountablePath O ρ hρO hρ1 y ↔
      ∀ g : TestC0On O, x g.1.1 = y g.1.1 := by
  constructor
  · intro h g
    apply localMeanZeroGen_determines O ρ hρO hρ1
    · exact fun n => congrFun h n
  · intro h
    funext n
    exact h (localMeanZeroGen O ρ hρO hρ1 n)

/-- The fixed mean-zero tests as tests on the ball itself. -/
def localMeanZeroGenBall (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (n : ℕ) : TestOn O :=
  testOnOfSupp O (localMeanZeroGen O ρ hρO hρ1 n).1.1
    (localMeanZeroGen O ρ hρO hρ1 n).2

theorem localMeanZeroGenBall_eq (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (n : ℕ) :
    localMeanZeroGenBall O ρ hρO hρ1 n =
      distGen O (Nat.unpair n) -
        (∫ x, distGen O (Nat.unpair n) x) • testOnOfSupp O ρ hρO := by
  ext z
  change recTest O ρ (distGen O (Nat.unpair n)) z =
    distGen O (Nat.unpair n) z -
      (∫ x, distGen O (Nat.unpair n) x) • ρ z
  rw [coe_recTest]
  rfl

/-- The countable tests also determine the restriction of an arbitrary distribution on the ball. -/
theorem localMeanZeroGenBall_determines (O : Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    {x y : DistOn O}
    (heq : ∀ n, x (localMeanZeroGenBall O ρ hρO hρ1 n) =
      y (localMeanZeroGenBall O ρ hρO hρ1 n))
    (g : TestC0On O) :
    x (testOnOfSupp O g.1.1 g.2) = y (testOnOfSupp O g.1.1 g.2) := by
  let ρO : TestOn O := testOnOfSupp O ρ hρO
  let A : DistOn O := x - x ρO • intDist O
  let B : DistOn O := y - y ρO • intDist O
  have hAB : A = B := by
    apply injective_distOn_pairings O
    funext j
    change A (distGen O j) = B (distGen O j)
    change x (distGen O j) - x ρO * intDist O (distGen O j) =
      y (distGen O j) - y ρO * intDist O (distGen O j)
    rw [intDist_apply]
    have hj := heq (Nat.pair j.1 j.2)
    rw [localMeanZeroGenBall_eq, Nat.unpair_pair] at hj
    simpa [map_sub, map_smul, smul_eq_mul, mul_comm] using hj
  have key := DFunLike.congr_fun hAB (testOnOfSupp O g.1.1 g.2)
  change x (testOnOfSupp O g.1.1 g.2) - x ρO *
      intDist O (testOnOfSupp O g.1.1 g.2) =
    y (testOnOfSupp O g.1.1 g.2) - y ρO *
      intDist O (testOnOfSupp O g.1.1 g.2) at key
  rw [intDist_apply] at key
  change x (testOnOfSupp O g.1.1 g.2) - x ρO * (∫ z, g.1.1 z) =
    y (testOnOfSupp O g.1.1 g.2) - y ρO * (∫ z, g.1.1 z) at key
  rw [g.1.2, mul_zero, sub_zero, mul_zero, sub_zero] at key
  exact key

/-- Restriction from a containing domain to the fixed ball. -/
def restrictDistOn (O D : Opens ℂ) (_hOD : (O : Set ℂ) ⊆ D)
    (x : DistOn D) : DistOn O :=
  x.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := D))

theorem restrictDistOn_apply (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (x : DistOn D) (φ : TestOn O) :
    restrictDistOn O D hOD x φ = x (testOnOfSupp D (inclTest O φ)
      (by simpa [coe_inclTest] using φ.tsupport_subset.trans hOD)) := by
  change x (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := D) φ) = _
  congr 1
  ext z
  change ((TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤)
      (Ω₁ := O) (Ω₂ := D) φ) : ℂ → ℝ) z = inclTest O φ z
  have h : O ≤ D := hOD
  simp [TestFunction.monoCLM_apply, h, coe_inclTest]

theorem restrictDistOn_gen (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) (x : DistOn D) (n : ℕ) :
    restrictDistOn O D hOD x (localMeanZeroGenBall O ρ hρO hρ1 n) =
      localCountablePathOn O D hOD ρ hρO hρ1 x n := by
  rw [restrictDistOn_apply]
  congr 1
  ext z
  change inclTest O (localMeanZeroGenBall O ρ hρO hρ1 n) z =
    (localMeanZeroGen O ρ hρO hρ1 n).1.1 z
  rw [coe_inclTest]
  rfl

/-- Countable coordinates determine the restriction modulo constants for fields on `D`. -/
theorem localCountablePathOn_determines (O D : Opens ℂ)
    (hOD : (O : Set ℂ) ⊆ D) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    {x y : DistOn D}
    (heq : localCountablePathOn O D hOD ρ hρO hρ1 x =
      localCountablePathOn O D hOD ρ hρO hρ1 y)
    (g : TestC0On O) :
    x (testOnOfSupp D g.1.1 (g.2.trans hOD)) =
      y (testOnOfSupp D g.1.1 (g.2.trans hOD)) := by
  have hgen : ∀ n, restrictDistOn O D hOD x
      (localMeanZeroGenBall O ρ hρO hρ1 n) =
      restrictDistOn O D hOD y (localMeanZeroGenBall O ρ hρO hρ1 n) := by
    intro n
    rw [restrictDistOn_gen, restrictDistOn_gen]
    exact congrFun heq n
  have h := localMeanZeroGenBall_determines O ρ hρO hρ1 hgen g
  rw [restrictDistOn_apply, restrictDistOn_apply] at h
  convert h using 1 <;> congr 1 <;> ext z <;>
    change g.1.1 z = inclTest O (testOnOfSupp O g.1.1 g.2) z <;>
    rw [coe_inclTest] <;> rfl

/-- The law of a domain field on the fixed countable modulo-constant carrier. -/
def zbLocalCountableLaw {Ω : Type*} [MeasurableSpace Ω]
    (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) (h : Ω → DistOn D)
    (P : Measure Ω) : Measure (ℕ → ℝ) :=
  P.map (localCountablePathOn O D hOD ρ hρO hρ1 ∘ h)

/-- The law of a whole-plane field on the same carrier. -/
def wpLocalCountableLaw {Ω : Type*} [MeasurableSpace Ω]
    (O : Opens ℂ) (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) (h : Ω → DistC)
    (P : Measure Ω) : Measure (ℕ → ℝ) :=
  P.map (localCountablePath O ρ hρO hρ1 ∘ h)

theorem isProbabilityMeasure_zbLocalCountableLaw {Ω : Type*} [MeasurableSpace Ω]
    (O D : Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) {h : Ω → DistOn D} {P : Measure Ω}
    (hh : IsZeroBoundaryGFF D h P) :
    IsProbabilityMeasure (zbLocalCountableLaw O D hOD ρ hρO hρ1 h P) := by
  have : IsProbabilityMeasure P := hh.process.gaussian.isProbabilityMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    ((measurable_localCountablePathOn O D hOD ρ hρO hρ1).comp hh.measurable).aemeasurable).mpr
      inferInstance

theorem isProbabilityMeasure_wpLocalCountableLaw {Ω : Type*} [MeasurableSpace Ω]
    (O : Opens ℂ) (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) {h : Ω → DistC} {P : Measure Ω}
    (hh : IsWholePlaneGFF h P) :
    IsProbabilityMeasure (wpLocalCountableLaw O ρ hρO hρ1 h P) := by
  have : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    ((measurable_localCountablePath O ρ hρO hρ1).comp hh.measurable).aemeasurable).mpr
      inferInstance

example : MeasurableEq (ℕ → ℝ) := inferInstance

end SupercriticalConformalCovariance.TV
