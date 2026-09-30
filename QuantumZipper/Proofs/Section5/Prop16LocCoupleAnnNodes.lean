import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnn
import QuantumZipper.Proofs.Section5.Prop16LocCoupleDom
import QuantumZipper.Proofs.GFF.K3.MixedM5Lip

/-!
# DOM-a by annulus features (decision D34): the remaining nodes AN2–AN5

Route (own adaptation of Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007),
Thm 2.17, mixed form; no Riemann map, no Dirichlet problem). With `S = realSet (Icc c d)`,
`M = K3.annulusSpan D S` (closed span of the mixed local annulus features, `MixedProj.lean`) and
`M̂ = freeAnnSpan D S` (closed span of the free ones, `freeAnnFeat`):

* **AN1** (proved, `inner_freeAnnFeat`): the two generating families have the same Gram matrix,
  so `K3.exists_linearIsometry_closure_of_gram` gives `J : M →ₗᵢ HkE` onto `M̂`, `J a_i = â_i`.
* **AN5** (assembly, `DomMarkovCurveAnnStmt`, proved: `domMarkovCurveAnn_holds`,
  `Prop16LocCoupleAnnMain.lean`): take
  `E = WithLp 2 (HkE × GradSpace D)`, `ι x = (x, 0)`, `ρ₀` a unit folded circle in `ℍ` outside
  `closure D`, and
    `e μ = (J (P_M v_μ), K3.remVec D S μ)`,
    `H z = (P_M̂ᗮ (freeFold z s_z − v̂_{ρ₀}), −K3.remVec D S (fold_{z,s_z}))`
  with `s_z` any radius of a local ball at `z` (independent of the choice by the mean-value
  properties `K3.remVec_foldedCircle_eq` and `freeFold z s − freeFold z s' = freeAnnFeat ∈ M̂`).
  Gram: `K3.dualCov_mixed_eq_Qann_add`. Curve identity: `P_M̂ (v̂_μ − v̂_{ρ₀}) = J (P_M v_μ)`
  (both have pairing `∫ annulusPot_i dμ` with the generators: `K3.inner_rieszVec_annulusFeat` and
  the computation of AN1 for general `μ`; `annulusPot_i = 0` on the support of `ρ₀`), then the
  mixed representation `K3.inner_rieszVec_eq_integral_of_mem_orthogonal` and its free analogue
  AN2. Lipschitz: `K3.exists_abs_inner_remVec_sub_le` and its free analogue AN3, on compacts with a
  uniform local radius (AN4).

AN2–AN4 are stated here as `Prop`s; **none is assumed anywhere**.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3

open Classical in
/-- The free folded-circle vector `v̂_{fold_{z,s}}` (zero for degenerate data). -/
def freeFold (z : ℂ) (s : ℝ) : HkE :=
  if h : z ∈ Hbar ∧ 0 < s then freeVec ⟨foldedCircle z s, isAdmissibleH_foldedCircle h.1 h.2⟩
  else 0

/-- The local annuli `(z, s, s', R0)` of `(D, S)`: `LocalBall D S z R0`, `0 < s < s' < R0`. -/
def AnnIdx (D S : Set ℂ) : Type :=
  {p : ℂ × ℝ × ℝ × ℝ // LocalBall D S p.1 p.2.2.2 ∧ 0 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧
    p.2.2.1 < p.2.2.2}

/-- `M̂`: the closed span of the free annulus features of the local annuli of `(D, S)`. -/
def freeAnnSpan (D S : Set ℂ) : Submodule ℝ HkE :=
  (Submodule.span ℝ (Set.range fun i : AnnIdx D S => freeAnnFeat i.1.1 i.1.2.1 i.1.2.2.1)).topologicalClosure

/-- **AN2 (free representation; not proved).** Free analogue of
`K3.inner_rieszVec_eq_integral_of_mem_orthogonal`: for `u ⊥ M̂` and an admissible `μ` carried by
a compact `K` with uniform local radius `2R`, `⟪v̂_μ, u⟫ = ∫ ⟪v̂_{fold_{z,s}}, u⟫ dμ(z)`
(`0 < s < 2R`). Route: `μ − μ.bind fold_s = lim_{t→0} ∫ (fold_{z,t} − fold_{z,s}) dμ(z)` in the
free energy norm, and each `fold_{z,t} − fold_{z,s}` is a free annulus feature. -/
def FreeAnnRepStmt (D S : Set ℂ) : Prop :=
  ∀ (K : Set ℂ) (R : ℝ), MixedLocalHyp D S K R → ∀ μ : AdmT, μ.1 Kᶜ = 0 →
    ∀ s : ℝ, 0 < s → s < 2 * R → ∀ u ∈ (freeAnnSpan D S)ᗮ,
      ⟪freeVec μ, u⟫ = ∫ z, ⟪freeFold z s, u⟫ ∂μ.1

/-- **AN3 (free Lipschitz bound; not proved).** Free analogue of
`K3.exists_abs_inner_remVec_sub_le`: `|⟪v̂_{fold_{z,R}} − v̂_{fold_{z',R}}, u⟫| ≤ L |z − z'| ‖u‖`
for `u ⊥ M̂` and `z, z' ∈ K`. Route as in `MixedM5Lip.lean`: replace the folded circle by a
radially smoothed annulus measure (same pairing with `u ⊥ M̂`), whose free vector is Lipschitz in
the centre (bounded Lipschitz density, `neumannH` energy). -/
def FreeAnnLipStmt (D S : Set ℂ) : Prop :=
  ∀ (K : Set ℂ) (R : ℝ), MixedLocalHyp D S K R → ∃ L : ℝ, ∀ z ∈ K, ∀ z' ∈ K,
    ∀ u ∈ (freeAnnSpan D S)ᗮ, |⟪freeFold z R - freeFold z' R, u⟫| ≤ L * ‖z - z'‖ * ‖u‖

/-- **AN4 (uniform local radius; not proved, elementary).** Every compact subset of
`D ∪ (c,d)` has a uniform radius of local balls (compactness and `LocalBall.mono`). -/
def Prop16UnifLocalStmt : Prop :=
  ∀ (D : Set ℂ) (c d : ℝ), K3.Prop16Geometry D c d → ∀ K : Set ℂ, IsCompact K →
    K ⊆ D ∪ realSet (Ioo c d) → ∃ R > 0, MixedLocalHyp D (realSet (Icc c d)) K R

/-- **AN5 (assembly):** the general DOM-a from AN2–AN4 (AN1 is proved). Proved as
`domMarkovCurveAnn_holds` (`Prop16LocCoupleAnnMain.lean`). -/
def DomMarkovCurveAnnStmt : Prop :=
  Prop16UnifLocalStmt → (∀ D S : Set ℂ, FreeAnnRepStmt D S) → (∀ D S : Set ℂ, FreeAnnLipStmt D S) →
    ∀ (D : Set ℂ) (c d : ℝ), K3.Prop16Geometry D c d → DomMarkovCurveEStmt D c d

/-- **Proposition 1.6 from the annulus nodes and the masked Palm nodes** (through
`theorem1_6_of_domMarkovE_palmMask`). -/
theorem theorem1_6_of_ann (hAsm : DomMarkovCurveAnnStmt) (hU : Prop16UnifLocalStmt)
    (hRep : ∀ D S : Set ℂ, FreeAnnRepStmt D S) (hLip : ∀ D S : Set ℂ, FreeAnnLipStmt D S)
    (hId : Prop16PalmIdMaskStmt) (hFix : Prop16FixedZoomMaskStmt) : theorem1_6 :=
  theorem1_6_of_domMarkovE_palmMask (hAsm hU hRep hLip) hId hFix

/-- The product space of AN5 is separable. -/
example (D : Set ℂ) : TopologicalSpace.SeparableSpace (WithLp 2 (HkE × GradSpace D)) :=
  inferInstance

end Prop16Asm

end QuantumZipper
