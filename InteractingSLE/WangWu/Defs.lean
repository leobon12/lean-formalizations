import InteractingSLE.Spec.Ito.Mean
import InteractingSLE.Spec.Ito.Coordinates
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Frozen.Spec.drivingFiltration
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.loewnerGreenEnergy
import QuantumZipper.Proofs.GFF.K3.C5Kernel
import LQGMetric.Field.ZeroBoundary

/-!
# Wang–Wu at `κ = 4`: objects and target statements (document §1, Definitions 1.1–1.5, 1.9; Definition 3.3)

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` ("Wang–Wu: coupling,
determination, and continuity at κ = 4", ruling R31), §1 and Definition 3.3.

The document's objects are the `κ = 4` case of the project's frozen carriers (`InteractingSLE/Frozen/Spec/`):

* **Definition 1.1** (normalization). The Green function `G_ℍ(z,w) = log |z − w̄|/|z − w|` is QuantumZipper's
  `greenH` (`greenH_eq_log_div`); the zero-boundary GFF with covariance `Q_D` is LQGMetric's
  `IsZBGFFProcess` (covariance `QuantumZipper.zeroGFFTestCov D`, the dual Dirichlet form of
  `(f,g)_∇ = (2π)⁻¹ ∫ ∇f·∇g`). The constant `λ = π/2` is the frozen `sleLambda 4` (`sleLambda_four`), and
  `χ = 2/√κ − √κ/2` vanishes at `κ = 4` (`chiC_four`): "there is no additive logarithmic derivative in this
  `κ = 4` field transformation".
* **Definition 1.2** (force data): the frozen ordered force word `IsOrderedForceWord xL xR`, weights `ρL, ρR`; the
  boundary function `b` is the frozen `forceBoundaryData 4` (`boundaryData`, `boundaryData_of_neg`,
  `boundaryData_of_nonneg`); its one-sided start values `b_L, b_R` (`startValueL`, `startValueR`,
  `tendsto_boundaryData_startValueL`, `boundaryData_eq_startValueR`), and the nontriviality criterion
  `b_L < λ`, `b_R > −λ` (`thresholdCondition_zero_iff`, `IsIntegratedSLEPath.lifetime_eq_zero_of_threshold`).
* **Definition 1.3** (stopped marked Loewner chain): the frozen `IsIntegratedSLEEvolution 4`
  (`IsMarkedChain`); `√4 = 2` gives `dW = 2 dB + ∑ ρ/(W − V) dt` (`IsIntegratedSLEPath.w_eq_four`).
* **Definition 1.4** (conditional mean): the explicit formula (1.3) (`condMean`, `meanAt`), equal to the frozen
  `couplingMean 4` for every bounded harmonic extension of the transported data (`couplingMean_four_eq`), with the
  bound `M` (`abs_condMean_le`).
* **Definition 3.3** (retained kernel domains): swallowing and stopping times `s(q)`, conformal radius `r_t(q)`
  and its limit `r_−(q)`, the kernel domain `int ⋂_{t<s(q)} D_t`, the component `C(q)`, the retained domains
  `U_t`, `U_T` and swept sets `A_t`; the frozen mean and the retained (frozen) Green kernel of Lemma 3.4.3.
* **Definition 1.5** (full level-line coupling): `IsFullLevelLineCoupling`.
* **Definition 1.9** (height convention): `heightBoundaryData`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

/-! ### Definition 1.1: normalization -/

/-- The level-line height `λ = π/2` of the document (scope line: "the normalization throughout is `λ = π/2`"). -/
def wwLambda : ℝ := Real.pi / 2

theorem wwLambda_pos : 0 < wwLambda := by unfold wwLambda; positivity

theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The frozen `λ(κ) = π/√κ` at `κ = 4` is the document's `λ = π/2`. -/
theorem sleLambda_four : sleLambda 4 = wwLambda := by
  rw [sleLambda, sqrt_four, wwLambda]

/-- `χ = 2/√κ − √κ/2 = 0` at `κ = 4`: the `κ = 4` field transformation has no logarithmic-derivative term. -/
theorem chiC_four : QuantumZipper.chiC 4 = 0 := by
  rw [QuantumZipper.chiC, sqrt_four]; norm_num

/-- The Green function of `ℍ` in the document's normalization, `G_ℍ(z, w) = log (|z − w̄| / |z − w|)`
(`−Δ_z G_ℍ(z, w) = 2π δ_w`). -/
theorem greenH_eq_log_div {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) (hzw : z ≠ w) :
    QuantumZipper.greenH z w = Real.log (‖z - conj w‖ / ‖z - w‖) := by
  have h1 : z - w ≠ 0 := sub_ne_zero.2 hzw
  have h2 : z - conj w ≠ 0 := by
    intro h
    have := congrArg Complex.im (sub_eq_zero.1 h)
    simp only [Complex.conj_im] at this
    linarith
  rw [QuantumZipper.greenH, Real.log_div (norm_ne_zero_iff.2 h2) (norm_ne_zero_iff.2 h1)]

/-! ### Definition 1.2: force data and the boundary function -/

/-- The boundary function `b` of Definition 1.2 (defined up to finitely many point values): the frozen
`forceBoundaryData` at `κ = 4`, `−λ(1 + ρ̄_{j,L})` on `(x_{j+1,L}, x_{j,L})` and `λ(1 + ρ̄_{j,R})` on
`(x_{j,R}, x_{j+1,R})`. -/
def boundaryData (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : ℝ → ℝ :=
  forceBoundaryData 4 ρL ρR xL xR

theorem boundaryData_of_neg (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {x : ℝ} (hx : x < 0) :
    boundaryData ρL ρR xL xR x =
      -wwLambda * (1 + ∑ i ∈ Finset.univ.filter (fun i => x < xL i), ρL i) := by
  rw [boundaryData, forceBoundaryData, sqrt_four, wwLambda]
  simp only [hx, ↓reduceIte]

theorem boundaryData_of_nonneg (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    boundaryData ρL ρR xL xR x =
      wwLambda * (1 + ∑ i ∈ Finset.univ.filter (fun i => xR i ≤ x), ρR i) := by
  rw [boundaryData, forceBoundaryData, sqrt_four, wwLambda]
  simp only [not_lt.2 hx, ↓reduceIte]

/-- The one-sided value `b_L` of the boundary function at `0⁻`: `−λ(1 + ∑_{x_{i,L} = 0⁻} ρ_{i,L})`. -/
def startValueL (ρL : Fin nL → ℝ) (xL : Fin nL → ℝ) : ℝ :=
  -wwLambda * (1 + ∑ i ∈ Finset.univ.filter (fun i => xL i = 0), ρL i)

/-- The one-sided value `b_R` of the boundary function at `0⁺`: `λ(1 + ∑_{x_{i,R} = 0⁺} ρ_{i,R})`. -/
def startValueR (ρR : Fin nR → ℝ) (xR : Fin nR → ℝ) : ℝ :=
  wwLambda * (1 + ∑ i ∈ Finset.univ.filter (fun i => xR i = 0), ρR i)

/-- `b(0) = b_R` (the right-hand formula applies at `0`). -/
theorem boundaryData_eq_startValueR (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (hxR : ∀ i, 0 ≤ xR i) :
    boundaryData ρL ρR xL xR 0 = startValueR ρR xR := by
  rw [boundaryData_of_nonneg _ _ _ _ le_rfl, startValueR]
  congr 2
  exact Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => le_antisymm h (hxR i), fun h => h.le⟩)
    fun _ _ => rfl

/-- A positive number below every positive value of a finite family. -/
theorem exists_pos_le_of_pos {n : ℕ} (x : Fin n → ℝ) : ∃ ε > 0, ∀ i, 0 < x i → ε ≤ x i := by
  classical
  set S : Finset ℝ := insert 1 ((Finset.univ.filter (fun i => 0 < x i)).image x) with hS
  have hne : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.min' hne, ?_, fun i hi => S.min'_le _ ?_⟩
  · obtain ⟨y, hy, hmin⟩ : ∃ y ∈ S, S.min' hne = y := ⟨_, S.min'_mem hne, rfl⟩
    rw [hmin]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      exact (Finset.mem_filter.1 hj).2
  · exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩)

/-- The boundary function is constant, equal to `b_R`, on a right neighbourhood `[0, ε)` of `0`. -/
theorem exists_boundaryData_eq_startValueR (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (hxR : ∀ i, 0 ≤ xR i) :
    ∃ ε > 0, ∀ x, 0 ≤ x → x < ε → boundaryData ρL ρR xL xR x = startValueR ρR xR := by
  obtain ⟨ε, hε, hεx⟩ := exists_pos_le_of_pos xR
  refine ⟨ε, hε, fun x hx0 hxε => ?_⟩
  rw [boundaryData_of_nonneg _ _ _ _ hx0, startValueR]
  congr 2
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => by rw [h]; exact hx0⟩)
    fun _ _ => rfl
  by_contra hne
  have hpos : 0 < xR i := lt_of_le_of_ne (hxR i) (Ne.symm hne)
  linarith [hεx i hpos]

/-- The boundary function is constant, equal to `b_L`, on a left neighbourhood `(−ε, 0)` of `0`. -/
theorem exists_boundaryData_eq_startValueL (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (hxL : ∀ i, xL i ≤ 0) :
    ∃ ε > 0, ∀ x, -ε < x → x < 0 → boundaryData ρL ρR xL xR x = startValueL ρL xL := by
  obtain ⟨ε, hε, hεx⟩ := exists_pos_le_of_pos (fun i => -xL i)
  refine ⟨ε, hε, fun x hxε hx0 => ?_⟩
  rw [boundaryData_of_neg _ _ _ _ hx0, startValueL]
  congr 2
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => by rw [h]; exact hx0⟩)
    fun _ _ => rfl
  by_contra hne
  have hpos : 0 < -xL i := by
    have := lt_of_le_of_ne (hxL i) hne
    linarith
  linarith [hεx i hpos]

/-- `b → b_L` at `0⁻`. -/
theorem tendsto_boundaryData_startValueL (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (hxL : ∀ i, xL i ≤ 0) :
    Tendsto (boundaryData ρL ρR xL xR) (𝓝[<] 0) (𝓝 (startValueL ρL xL)) := by
  obtain ⟨ε, hε, h⟩ := exists_boundaryData_eq_startValueL ρL ρR xL xR hxL
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (show -ε < 0 by linarith)] with x hx
  exact (h x hx.1 hx.2).symm

/-- `b → b_R` at `0⁺`. -/
theorem tendsto_boundaryData_startValueR (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (hxR : ∀ i, 0 ≤ xR i) :
    Tendsto (boundaryData ρL ρR xL xR) (𝓝[≥] 0) (𝓝 (startValueR ρR xR)) := by
  obtain ⟨ε, hε, h⟩ := exists_boundaryData_eq_startValueR ρL ρR xL xR hxR
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ico_mem_nhdsGE hε] with x hx
  exact (h x hx.1 hx.2).symm

/-- **The nontriviality criterion of Definition 1.2.** The continuation threshold holds at the seed `(0; x)`
exactly when `b_L < λ` or `b_R > −λ` fails. (The adjacent weights are `−b_L/λ − 1` and `b_R/λ − 1`.) -/
theorem thresholdCondition_zero_iff (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR 0 xL xR ↔
      ¬ (startValueL ρL xL < wwLambda ∧ -wwLambda < startValueR ρR xR) := by
  have hl := wwLambda_pos
  unfold ForceWord.ThresholdCondition startValueL startValueR
  set a := ∑ i ∈ Finset.univ.filter (fun i => xL i = 0), ρL i
  set b := ∑ i ∈ Finset.univ.filter (fun i => xR i = 0), ρR i
  have e1 : -wwLambda * (1 + a) < wwLambda ↔ -2 < a := by
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have e2 : -wwLambda < wwLambda * (1 + b) ↔ -2 < b := by
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [e1, e2]
  constructor
  · rintro (h | h) ⟨h1, h2⟩ <;> linarith
  · intro h
    by_contra hn
    simp only [not_or, not_le] at hn
    exact h hn

/-- If the continuation threshold holds at the seed, the killed path consists only of its starting point:
the lifetime is `0`. -/
theorem IsIntegratedSLEPath.lifetime_eq_zero_of_threshold {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hth : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ζ = 0 := by
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, -, -⟩ := hp
  by_contra hζ
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by
    rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hζ
  apply hnot 0 h0
  rw [hw0]
  convert hth using 2
  · exact hvL0 _
  · exact hvR0 _

/-! ### Definition 1.3: the stopped marked Loewner chain -/

/-- **Definition 1.3.** The stopped marked `SLE₄(ρ_L; ρ_R)` chain with lifetime the continuation threshold `T`:
the frozen integrated evolution (Definition 2.1 of the specification) at `κ = 4`. Its pathwise part is
`dW_t = 2 dB_t + ∑_{q,i} ρ_{i,q}/(W_t − V_{i,q}(t)) dt`, `V_{i,q}(t) = x_{i,q} + ∫₀ᵗ 2/(V_{i,q} − W) ds`, in the
integral sense with null collision sets and locally integrable reciprocal gaps, up to the maximal lifetime `T`
(ruling R15 Q1). -/
abbrev IsMarkedChain {Ω : Type*} {mΩ : MeasurableSpace Ω} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsIntegratedSLEEvolution 4 xL xR ρL ρR P 𝓕 W VL VR B ζ

/-- The driving equation (1.1) with `√κ = 2`. -/
theorem IsIntegratedSLEPath.w_eq_four {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t = 2 * b t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal)) := by
  have h := hp.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht
  rwa [sqrt_four] at h

/-! ### Definition 1.4: the conditional mean -/

/-- The explicit conditional mean (1.3)/(3.2) as a function of the image point `w = f_t(z)` and the centred
force images `v_{i,q} = V_{i,q}(t) − W_t`:
`η = λ (1 + ∑ ρ_{i,R}) − arg w − ½ ∑_{q,i} ρ_{i,q} arg (w − v_{i,q})` (`g_t(z) − V_{i,q}(t) = f_t(z) − v_{i,q}`;
`arg ∈ (0, π)` on `ℍ`). -/
def condMean (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) (w : ℂ) : ℝ :=
  wwLambda * (1 + ∑ i, ρR i) - Complex.arg w
    - (1 / 2) * ((∑ i, ρL i * Complex.arg (w - vL i)) + ∑ i, ρR i * Complex.arg (w - vR i))

/-- **Definition 1.4.** The conditional mean `η_t(z)` of the marked chain with driving path `w` and force images
`vL, vR`, for `z ∈ D_t`: `condMean` at `f_t(z)` and the centred images. -/
def meanAt (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  condMean ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) (QuantumZipper.fwdMap (Ito.rpath w) t z)

/-- `condMean` is the specification's explicit harmonic function `meanHarmonic` at `κ = 4`. -/
theorem condMean_eq_meanHarmonic (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) (w : ℂ) : condMean ρL ρR vL vR w = Ito.meanHarmonic 4 ρL ρR vL vR w := by
  rw [condMean, Ito.meanHarmonic, sqrt_four, wwLambda]
  ring

/-- **The mean of the document is the frozen `couplingMean` at `κ = 4`**: for centred positions
`vL i ≤ 0 ≤ vR i`, every bounded harmonic extension `u` of the time-`t` data, and `f_t(z) ∈ ℍ`. -/
theorem couplingMean_four_eq {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ}
    (hvL : ∀ i, vL i ≤ 0) (hvR : ∀ i, 0 ≤ vR i) {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData 4 ρL ρR vL vR) (forceJumpSet vL vR) u)
    {w : ℝ → ℝ} {t : ℝ} {z : ℂ} (hz : QuantumZipper.fwdMap w t z ∈ QuantumZipper.H) :
    couplingMean 4 w t u z = condMean ρL ρR vL vR (QuantumZipper.fwdMap w t z) := by
  rw [Ito.couplingMean_eq_meanHarmonic hvL hvR hu hz, chiC_four, zero_mul, sub_zero,
    condMean_eq_meanHarmonic]

/-- The bound `M` of Definition 1.4 (with `|1 + ∑ ρ_{i,R}|`; the document prints `λ(1 + ∑ ρ_{i,R})`, which is
the same when that sum is `≥ −1`). -/
def meanBound (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : ℝ :=
  wwLambda * |1 + ∑ i, ρR i| + Real.pi + Real.pi / 2 * ((∑ i, |ρL i|) + ∑ i, |ρR i|)

theorem abs_condMean_le (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)
    (w : ℂ) : |condMean ρL ρR vL vR w| ≤ meanBound ρL ρR := by
  have harg : ∀ x : ℂ, |Complex.arg x| ≤ Real.pi := fun x => Complex.abs_arg_le_pi x
  have hsum : ∀ {n : ℕ} (ρ : Fin n → ℝ) (v : Fin n → ℝ),
      |∑ i, ρ i * Complex.arg (w - v i)| ≤ Real.pi * ∑ i, |ρ i| := by
    intro n ρ v
    calc |∑ i, ρ i * Complex.arg (w - v i)| ≤ ∑ i, |ρ i * Complex.arg (w - v i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, Real.pi * |ρ i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (harg _) (abs_nonneg _)
      _ = Real.pi * ∑ i, |ρ i| := (Finset.mul_sum _ _ _).symm
  have h1 := hsum ρL vL
  have h2 := hsum ρR vR
  have h3 := harg w
  have hl := wwLambda_pos
  unfold condMean meanBound
  have habs : |wwLambda * (1 + ∑ i, ρR i)| = wwLambda * |1 + ∑ i, ρR i| := by
    rw [abs_mul, abs_of_pos hl]
  calc |wwLambda * (1 + ∑ i, ρR i) - Complex.arg w
        - (1 / 2) * ((∑ i, ρL i * Complex.arg (w - vL i)) + ∑ i, ρR i * Complex.arg (w - vR i))|
      ≤ |wwLambda * (1 + ∑ i, ρR i)| + |Complex.arg w|
        + (1 / 2) * (|∑ i, ρL i * Complex.arg (w - vL i)| + |∑ i, ρR i * Complex.arg (w - vR i)|) := by
        have := abs_sub (wwLambda * (1 + ∑ i, ρR i) - Complex.arg w)
          ((1 / 2) * ((∑ i, ρL i * Complex.arg (w - vL i)) + ∑ i, ρR i * Complex.arg (w - vR i)))
        have h4 := abs_sub (wwLambda * (1 + ∑ i, ρR i)) (Complex.arg w)
        have h5 : |(1 / 2 : ℝ) * ((∑ i, ρL i * Complex.arg (w - vL i)) + ∑ i, ρR i * Complex.arg (w - vR i))|
            ≤ (1 / 2) * (|∑ i, ρL i * Complex.arg (w - vL i)| + |∑ i, ρR i * Complex.arg (w - vR i)|) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
        linarith
    _ ≤ wwLambda * |1 + ∑ i, ρR i| + Real.pi + Real.pi / 2 * ((∑ i, |ρL i|) + ∑ i, |ρR i|) := by
        rw [habs]; linarith

/-! ### Definition 3.3: retained kernel domains -/

/-- The stopping time `s(q) = inf {t < T : q ∉ D_t} ∧ T` of a point `q` (its swallowing time under the Loewner
flow of the driving path `w`, cut at the lifetime `T = ζ`). -/
def stopTime (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (q : ℂ) : ℝ≥0∞ :=
  min (QuantumZipper.swallowTime (Ito.rpath w) q) ζ

/-- The conformal radius `r_t(z) = CR(D_t; z) = 2 Im g_t(z) / |g_t′(z)|` (3.6), with `Im g_t = Im f_t` and
`|g_t′(z)| = |f_t′(z)| = exp (Re log f_t′(z))`, `log f_t′ = logDerivFwd`. -/
def confRadius (w : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  2 * (QuantumZipper.fwdMap (Ito.rpath w) t z).im *
    Real.exp (-(QuantumZipper.logDerivFwd (Ito.rpath w) t z).re)

/-- The limiting conformal radius `r_−(q) = lim_{t ↑ s(q)} CR(D_t; q)`; the radius is nonincreasing, so the
limit is the infimum over `t < s(q)` (`0` if `s(q) = 0`). -/
def limRadius (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (q : ℂ) : ℝ :=
  ⨅ t : {t : ℝ≥0 // (t : ℝ≥0∞) < stopTime w ζ q}, confRadius w t q

/-- The open kernel `int ⋂_{0 ≤ t < s(q)} D_t` (the intersection is over times strictly before `s(q)`). -/
def kernelDomain (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (q : ℂ) : Set ℂ :=
  interior (⋂ t : {t : ℝ≥0 // (t : ℝ≥0∞) < stopTime w ζ q},
    QuantumZipper.H \ QuantumZipper.fwdHull (Ito.rpath w) t)

/-- `C(q)`: when `r_−(q) > 0`, the component containing `q` of the kernel domain (otherwise empty). -/
def retainedComponent (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (q : ℂ) : Set ℂ :=
  if 0 < limRadius w ζ q then connectedComponentIn (kernelDomain w ζ q) q else ∅

/-- The points of `ℍ ∩ (ℚ + iℚ)`, the range of the enumeration `(q_j)` of Definition 3.3 (the unions below do
not depend on the enumeration). -/
def ratPoints : Set ℂ := {q | 0 < q.im ∧ ∃ a b : ℚ, q = ⟨a, b⟩}

/-- The retained domain `U_t = D_t ∪ ⋃_{s(q_j) ≤ t, s(q_j) < T, r_−(q_j) > 0} C(q_j)` for `t < T`. -/
def retainedDomain (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (t : ℝ≥0) : Set ℂ :=
  (QuantumZipper.H \ QuantumZipper.fwdHull (Ito.rpath w) t) ∪
    ⋃ q ∈ ratPoints, ⋃ (_ : stopTime w ζ q ≤ t ∧ stopTime w ζ q < ζ ∧ 0 < limRadius w ζ q),
      retainedComponent w ζ q

/-- The terminal retained domain `U_T = ⋃_{r_−(q_j) > 0} C(q_j)` (and `U_0 = ℍ` when `T = 0`). -/
def terminalDomain (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Set ℂ :=
  if ζ = 0 then QuantumZipper.H else ⋃ q ∈ ratPoints, ⋃ (_ : 0 < limRadius w ζ q), retainedComponent w ζ q

/-- The swept set `A_t = ℍ \ U_t`. -/
def sweptSet (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) (t : ℝ≥0) : Set ℂ := QuantumZipper.H \ retainedDomain w ζ t

/-- The terminal swept set `A_T = ℍ \ U_T` (of Lebesgue area zero almost surely, Lemma 3.5). -/
def terminalSwept (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Set ℂ := QuantumZipper.H \ terminalDomain w ζ

/-- **The frozen mean** (Definition 1.5, Lemma 3.5): `η_t(z)` while `z` is active, and its limit from below at
the swallowing time (disconnection time) of `z` afterwards ("on each disconnected component freeze the harmonic
mean at its disconnection time"). On the swept set the value is immaterial (area zero, Lemma 3.5). -/
def frozenMean (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  if (t : ℝ≥0∞) < QuantumZipper.swallowTime (Ito.rpath w) z then meanAt ρL ρR w vL vR t z
  else limUnder (𝓝[<] (QuantumZipper.swallowTime (Ito.rpath w) z).toNNReal)
    (fun r => meanAt ρL ρR w vL vR r z)

/-- **The retained Green kernel** `G_{U_t}(a, b)` of Lemma 3.4.3: `G_{D_t}(a, b) = G_ℍ(f_t a, f_t b)` frozen at the
first swallowing of either argument, i.e. QuantumZipper's monotone limit
`V_t(a,b) = lim_{s ↑ min(s(a), s(b), t)} G_ℍ(f_s a, f_s b)` (`QuantumZipper.K3.VT`). (The document also sets it to
zero when an argument lies in the area-zero set `A_t`; this does not change any integral.) -/
def retainedGreen (w : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℂ) : ℝ := QuantumZipper.K3.VT (Ito.rpath w) t a b

/-- The retained Green quadratic form `Q_{U_t}(φ, φ) = ∬ φ(a) G_{U_t}(a, b) φ(b) da db`. -/
def retainedGreenEnergy (w : ℝ≥0 → ℝ) (t : ℝ≥0) (φ : ℂ → ℝ) : ℝ :=
  ∫ a, ∫ b, φ a * retainedGreen w t a b * φ b

/-! ### Definition 1.5: the full level-line coupling -/

/-- **Definition 1.5 (full level-line coupling).** A field `F` on `ℍ` coupled with a marked chain
(Definition 1.3) on `(Ω, 𝓕, P)` such that, for every finite stopping time `τ < T` of the chain's filtration
`F^K` (the frozen `drivingFiltration`: the usual augmentation of the filtration of the marked chain) and every real
test function `p`, `E[e^{i(F,p)} | F^K_τ] = exp(i ∫ η_τ p dA − ½ Q_{U_τ}(p, p))`, with `η_τ` the frozen mean and
`Q_{U_τ}` the retained Green form. The identity is on the full ambient field. -/
def IsFullLevelLineCoupling {Ω : Type*} {mΩ : MeasurableSpace Ω} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  IsIntegratedSLEEvolution 4 xL xR ρL ρR P 𝓕 W VL VR B ζ ∧ Measurable F ∧
    ∃ hX : IsMeasurableKilledDriving W VL VR ζ,
      ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ),
        (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
        ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (F ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, frozenMean ρL ρR (W · ω) (fun i => (VL i · ω))
                (fun i => (VR i · ω)) ((τ ω).untopD 0) z * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * retainedGreenEnergy (W · ω) ((τ ω).untopD 0) φ : ℝ) : ℂ))

/-! ### Definition 1.9: height convention -/

/-- **Definition 1.9.** A level line of `F` at height `u` is a zero level line of `F + u`; if `F + u` has boundary
data `b`, then `F` has boundary data `b − u`, and the conditional values of `F` on the left and right of the line
are `−λ − u` and `λ − u`. -/
def heightBoundaryData (u : ℝ) (b : ℝ → ℝ) : ℝ → ℝ := fun x => b x - u

theorem heightBoundaryData_sides (u : ℝ) :
    heightBoundaryData u (fun _ => -wwLambda) 0 = -wwLambda - u ∧
      heightBoundaryData u (fun _ => wwLambda) 0 = wwLambda - u := ⟨rfl, rfl⟩

end WangWu

end InteractingSLE
