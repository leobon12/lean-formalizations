import QuantumZipper.Proofs.Zipper.D3PlusN2TmZScale
import QuantumZipper.Proofs.Zipper.D3PlusN2HeartMix
import QuantumZipper.Proofs.Zipper.WedgeLawRef

/-!
# N2-HEART: the lateral/radial decomposition of the window data, and the sub-nodes H1–H3

Task N2-HEART, node `N2ZHeartStmt` (`D3PlusN2TmZStmt.lean`). Source: Duplantier–Miller–Sheffield,
arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78 (radial part `h_{e^{-t}}(0)` a Brownian motion,
"the rescaling procedure does not affect the projection of `h` onto `H₂(ℍ)`", independence of the
projections onto `H₁(ℍ)` and `H₂(ℍ)`), Prop. 4.8, p. 79; Sheffield, arXiv:1012.4797, p. 25.

The window data on `LocIdx K` of both embedded fields are written as
`lateral window + heartPsi (radial path)`, where
`heartPsi Q K p μ = ∫ (Q(−log‖z‖) + extP p (−log‖z‖)) dμ` reads the radial path through the
measurable dyadic extension `WedgeLaw.extP` (`p ↦ ∫ p(−log‖z‖) dμ` itself is not measurable for the
product σ-algebra; `extP p = p` for continuous `p`).

* Model side: lateral data `n2LatY X r` (the lateral part of the local field `Z`, on local measures),
  read at scale `a` through `latWin K a` (regularized evaluation at `μ.map (a ·)`); radial data
  `n2RadR` = (embedding time `Tc`, truncated re-centred radial path).
* Wedge side: lateral data `latY'' K X''` (`lateralPart X''` on the window), radial data
  `radR'' K A` (truncated wedge radial process).

Sub-nodes (exact statements below):
* **H1** `N2HLatIndepStmt`: the lateral data of `Z` are independent of the radial Brownian path
  `zRadB` (DMS p. 77, rotation invariance / reflection of the half-disc Green function).
* **H2** `N2HLatTVStmt`: TV between the model lateral window at deterministic scale `a` and the
  wedge lateral window tends to `0` as `a → 0⁺` (Markov decomposition + Cameron–Martin +
  scale invariance of the lateral part).
* **H3** `N2HModelDecompStmt`: for every window measure `μ`, a.s. on `{Tc ≥ log K + 1}` the
  model's window value is `heartF` of (lateral data, radial data) (regularity computation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## Definitions -/

/-- The radial part of the window data, read from a path through `extP`. -/
def heartPsi (Q : ℝ) (K : ℕ) (p : ℝ → ℝ) : LocIdx (K : ℝ) → ℝ :=
  fun μ => ∫ z, (Q * (-Real.log ‖z‖) + WedgeLaw.extP p (-Real.log ‖z‖)) ∂μ.1

/-- The lateral window at scale `a`: regularized evaluation of `y` at `μ.map (a ·)`. -/
def latWin (K : ℕ) (a : ℝ) (y : FieldSample) : LocIdx (K : ℝ) → ℝ :=
  fun μ => evalReg y (μ.1.map fun z => (a : ℂ) * z)

open Classical in
/-- The lateral data of the local field `Z` on the half-disc of radius `r` (on local measures;
`0` elsewhere). -/
def n2LatY {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) : FieldSample :=
  fun ν => if K3.IsLocalH 0 r ν then lateralPart (locZField X r ω) ν else 0

/-- The model's radial data: embedding time and the re-centred radial path truncated at
`−log K`. -/
def n2RadR (γ α L r : ℝ) (K : ℕ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : ℝ × (ℝ → ℝ) :=
  (ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω,
    fun s => ZoomRadial.zoomRadial α (Qc γ) (zRadB X r) (n2Lev γ α L r) ω (max s (-Real.log K)))

/-- The wedge's lateral window data. -/
def latY'' (K : ℕ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : LocIdx (K : ℝ) → ℝ :=
  fun μ => lateralPart (X ω) μ.1

/-- The wedge's truncated radial path. -/
def radR'' (K : ℕ) {Ω : Type*} (A : ℝ → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun s => A (max s (-Real.log K)) ω

/-- The wedge's window data as a function of (lateral window, radial path). -/
def heartW (γ : ℝ) (K : ℕ) (p : (LocIdx (K : ℝ) → ℝ) × (ℝ → ℝ)) : LocIdx (K : ℝ) → ℝ :=
  p.1 + heartPsi (Qc γ) K p.2

/-! ## Measurability -/

/-- Joint measurability of the regularized evaluation at a rescaled measure. -/
theorem measurable_evalReg_map_mul (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : FieldSample × ℝ => evalReg p.1 (μ.map fun z => (p.2 : ℂ) * z) := by
  have hk : ∀ k : ℕ, ∀ p : FieldSample × ℝ,
      ∫ w, avgReg p.1 k w ∂(μ.map fun z => (p.2 : ℂ) * z) = ∫ z, avgReg p.1 k ((p.2 : ℂ) * z) ∂μ := by
    intro k p
    have hm : Measurable fun z : ℂ => (p.2 : ℂ) * z := measurable_const.mul measurable_id
    rw [integral_map hm.aemeasurable]
    exact ((measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have e : (fun p : FieldSample × ℝ => evalReg p.1 (μ.map fun z => (p.2 : ℂ) * z)) =
      fun p => limUnder atTop fun k : ℕ => ∫ z, avgReg p.1 k ((p.2 : ℂ) * z) ∂μ := by
    funext p
    simp only [evalReg, hk]
  rw [e]
  have hf : ∀ k : ℕ, StronglyMeasurable
      (fun p : FieldSample × ℝ => ∫ z, avgReg p.1 k ((p.2 : ℂ) * z) ∂μ) := by
    intro k
    have hj : Measurable fun q : (FieldSample × ℝ) × ℂ => avgReg q.1.1 k ((q.1.2 : ℂ) * q.2) :=
      (measurable_avgReg k).comp ((measurable_fst.comp measurable_fst).prodMk
        ((Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).mul measurable_snd))
    exact StronglyMeasurable.integral_prod_right' hj.stronglyMeasurable
  exact (StronglyMeasurable.limUnder hf).measurable

theorem measurable_latWin_joint (K : ℕ) :
    Measurable fun p : ℝ × FieldSample => latWin K p.1 p.2 := by
  refine Measurable.of_eval fun μ => ?_
  have : IsFiniteMeasure μ.1 := μ.2.1.1
  have hs : Measurable fun p : ℝ × FieldSample => (p.2, p.1) := measurable_snd.prodMk measurable_fst
  have h2 := (measurable_evalReg_map_mul μ.1).comp hs
  exact h2

theorem measurable_locZField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {r : ℝ} (hX : IsFreeGFFModConstH X P)
    (hr : 0 < r) : Measurable (locZField X r) :=
  (measurable_extLoc r).comp (measurable_localZ hX hr)

theorem measurable_n2LatY {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} {r : ℝ} (hX : IsFreeGFFModConstH X P)
    (hr : 0 < r) : Measurable (n2LatY X r) := by
  classical
  refine measurable_pi_iff.2 fun ν => ?_
  unfold n2LatY
  by_cases h : K3.IsLocalH 0 r ν
  · haveI : IsFiniteMeasure ν := h.1.1
    simp only [h, ite_true]
    exact (WedgeTK.measurable_lateralPart_apply ν).comp (measurable_locZField hX hr)
  · simp only [h, ite_false]
    exact measurable_const

theorem measurable_latY'' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) (K : ℕ) :
    Measurable (latY'' K X) := by
  refine measurable_pi_iff.2 fun μ => ?_
  haveI : IsFiniteMeasure μ.1 := μ.2.1.1
  exact (WedgeTK.measurable_lateralPart_apply μ.1).comp (measurable_pi_iff.2 hX.measurable_coord)

/-! ## The sub-nodes -/

end D3Plus
end QuantumZipper
