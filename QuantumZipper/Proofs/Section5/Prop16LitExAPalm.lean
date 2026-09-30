import QuantumZipper.Proofs.Section5.Prop16LitExA
import QuantumZipper.Proofs.Section5.Prop16LitPalmCovRep
import QuantumZipper.Proofs.Section5.Prop16LitPalmCov
import QuantumZipper.Proofs.Section5.Prop16LitMeasEx

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: first half of `Prop16LitExStmt` via the Palm transfer (D98)

Ingredients (proved) for deriving, from the fixed-point statement `Prop16LitExAFixStmt` (at a
fixed boundary point `x`, for the Palm-shifted field, the chart zoom satisfies the countable
Borel condition `GoodA` of Prop16LitExA.lean), that a.e. under the weighted law the local area
limit of the chart field on `B(0, r₀ x) ∩ ℍ` exists (the assembly itself did not elaborate within
the compile budget and is not in this file). Route: the condition only reads the field on the
dyadic circles near `B(0, r₀ x) ∩ ℍ` (`goodA_congr`), hence is a Borel condition on the local
readings (`measurableSet_goodExA` applied to the rebuilt fields), and the Palm transfer
`Prop16Lit.ae_readings_of_palm` (Duplantier–Sheffield arXiv:0808.1560 §3.3) moves it from the
Palm-shifted field to the weighted law. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

namespace ExA

open Prop16Asm

/-- The countable condition for one field. -/
def GoodA (γ : ℝ) (Z : FieldSample) (r : ℝ) : Prop :=
  (∀ m : ℕ, ∀ᶠ k in atTop, areaApprox γ Z k (hbK r m) < ∞) ∧
    ∀ n : ℕ, ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, hbCut r n z * g z ∂(areaApprox γ Z k))
      atTop (𝓝 l)

/-- The integrals over a compact subset of `U` only see the circle averages near it. -/
theorem areaApprox_congr_of_circAgree {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    {Z Z' : FieldSample} (h : Prop16Area.G.CircAgree U Z Z') {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∀ᶠ k in atTop, ∀ z ∈ K, avgReg Z k z = avgReg Z' k z := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hUo hKU
  filter_upwards [Prop16Area.G.eventually_two_radius_lt hδ] with k hk z hz
  refine Prop16Area.G.avgReg_eq_of_circAgree h (H_subset_Hbar (hUH (hKU hz))) fun u hu => hδU ?_
  exact mem_cthickening_of_dist_le u z δ K hz ((mem_closedBall.1 hu.1).trans hk.le)

/-- **`GoodA` is local.** -/
theorem goodA_congr {γ : ℝ} {r : ℝ} {Z Z' : FieldSample}
    (h : Prop16Area.G.CircAgree (ball 0 r ∩ H) Z Z') (hZ : GoodA γ Z r) : GoodA γ Z' r := by
  have hUo : IsOpen (ball (0 : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  have hUH : ball (0 : ℂ) r ∩ H ⊆ H := inter_subset_right
  have hmeasK : ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 r ∩ H → ∀ᶠ k in atTop,
      areaApprox γ Z k K = areaApprox γ Z' k K := by
    intro K hK hKU
    filter_upwards [areaApprox_congr_of_circAgree hUo hUH h hK hKU] with k hk
    rw [show areaApprox γ Z k = (volume.restrict H).withDensity
        (fun z => ENNReal.ofReal (E6.areaDensK γ Z k z)) from rfl,
      show areaApprox γ Z' k = (volume.restrict H).withDensity
        (fun z => ENNReal.ofReal (E6.areaDensK γ Z' k z)) from rfl,
      withDensity_apply _ hK.measurableSet, withDensity_apply _ hK.measurableSet]
    refine setLIntegral_congr_fun hK.measurableSet fun z hz => ?_
    simp only [E6.areaDensK, hk z hz]
  obtain ⟨hfin, hconv⟩ := hZ
  refine ⟨fun m => ?_, fun n g hg => ?_⟩
  · filter_upwards [hfin m, hmeasK _ (isCompact_hbK r m) (hbK_subset r m)] with k h1 h2
    rwa [← h2]
  · obtain ⟨l, hl⟩ := hconv n g hg
    refine ⟨l, hl.congr' ?_⟩
    have hgt := famF_dense.1 g hg
    set K := tsupport (fun z => hbCut r n z * g z) with hKdef
    have hK : IsCompact K := hgt.2.1.mul_left
    have hKU : K ⊆ ball 0 r ∩ H := (tsupport_mul_subset_left).trans (tsupport_hbCut r n)
    filter_upwards [areaApprox_congr_of_circAgree hUo hUH h hK hKU] with k hk
    rw [E6.integral_areaApprox_eq, E6.integral_areaApprox_eq]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ K
    · simp only [E6.areaDensK, hk t ht]
    · have : hbCut r n t * g t = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun z => hbCut r n z * g z) ht
      simp only [this, mul_zero]

theorem exists_vague_of_goodA {γ r : ℝ} {Z : FieldSample} (h : GoodA γ Z r) :
    ∃ μ, IsVagueLimitOn (ball 0 r ∩ H) (areaApprox γ Z) μ :=
  exists_vague_of_goodExA (α := Unit) (Z := fun _ => Z) (r := fun _ => r) (q := ()) h

/-- **Node: the countable condition at a fixed boundary point, for the Palm-shifted field.** -/
def Prop16LitExAFixStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ → ∀ (C x : ℝ), x ∈ Ioo a b →
    ∀ᵐ ω ∂P, GoodA γ (zoomFieldLit γ C
      (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X x ω) x (ψ x)) (r₀ x)

/-- Locality of the chart zoom of a field and of its rebuilt readings. -/
theorem circAgree_litRep {γ C : ℝ} {D : Set ℂ} {c d a b : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hca : c ≤ a) (hbd : b ≤ d) {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ} (hfam : LitFamily D a b ψ r₀)
    (Y : FieldSample) (y : ℕ → ℝ) (hy : ∀ i, y i = Y (repMeas D a b i)) (t : ℝ)
    (ht : t ∈ Ioo a b) :
    Prop16Area.G.CircAgree (ball 0 (r₀ t) ∩ H) (zoomFieldLit γ C Y t (ψ t))
      (zoomFieldLit γ C (repFam D a b 0 y) t (ψ t)) := by
  obtain ⟨hDo, -, -, hDH, -⟩ := id hgeo
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  have hDW : D ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact Or.inl hz
    exact this.1
  have hag : Prop16Area.G.CircAgree W Y (repFam D a b 0 y) :=
    circAgree_repFam hWV Y y (fun i hi => by rw [hy i]; simp [repMeas, hi])
  obtain ⟨-, -, himg, -, hdB, -⟩ := hfam.2.2 t ht
  have hψt : Measurable (ψ t) := hfam.1.comp (measurable_const.prodMk measurable_id)
  refine circAgree_zoomFieldLit hWo hag γ C t hψt hdB.continuousOn fun u hu => ?_
  have hm : ψ t u ∈ zoomDomain D t := himg ▸ mem_image_of_mem (ψ t) hu.2
  exact ⟨zoomDomain_subset_H hDH t hm, hDW hm⟩

end ExA

end Prop16Lit

end QuantumZipper
