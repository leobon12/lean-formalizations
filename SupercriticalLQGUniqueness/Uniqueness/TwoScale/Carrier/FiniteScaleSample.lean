import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.DeterministicRatio
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.MeshEvent




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 

theorem finite_scale_ratio_of_good_sample
    {Ω : Type} (h : Ω → DistC) (ω : Ω) (D : DistC → LSCMetric)
    {lam R α M : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1)
    (hR : 0 < R) (hα1 : α < 1) (hM : 1 ≤ M)
    (z₀ : ℂ)
    (hB : BiLipschitz.Barrier.Barrier (D (h ω)))
    (hL : (D (h ω)).IsLengthSpace)
    (hfin : ∀ z ∈ TwoScale.Mesh.scaleMesh lam R z₀, ∀ k : ℕ,
      aroundDist (D (h ω))
        (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)) ≠ ∞)
    (hcount : ¬ ∃ z ∈ TwoScale.Mesh.scaleMesh lam R z₀,
      (LQGMetric.Blueprint.countOcc
        (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)
          (ENNReal.ofReal M * ENNReal.ofReal M)})
        (scaleCount lam α) ω : ℝ) <
          (1 / 2 : ℝ) * scaleCount lam α)
    (hsmall : lam ≤ scaleCutoff α
      (ENNReal.ofReal M * ENNReal.ofReal M).toReal)
    (A : EuclideanAnnulus)
    (hcenter : A.center ∈ Metric.ball z₀ (2 * R))
    (hinner : A.innerRadius = lam * R)
    (houter : A.outerRadius = lam ^ α * R)
    (K : Set ℂ) (hK : IsCompact K) (hAK : A.toSet ⊆ K)
    {P : ℝ → ℂ} {T q : ℝ}
    (hq0 : 0 < q) (hqT : q < T)
    (hP : (D (h ω)).IsCurve P 0 T) (hPK : MapsTo P (Icc 0 T) K)
    (hgeo : ∀ u v : ℝ, u ∈ Icc 0 T → v ∈ Icc 0 T → u ≤ v →
      internalEDist ((D (h ω)).pt '' K)
        ((D (h ω)).pt (P u)) ((D (h ω)).pt (P v)) =
          ENNReal.ofReal (v - u))
    (h0 : A.outerRadius ≤ dist (P 0) A.center)
    (hT : A.outerRadius ≤ dist (P T) A.center)
    (hq : dist (P q) A.center ≤ A.innerRadius) :
    aroundDist (D (h ω)) A ≤
      ENNReal.ofReal (lam ^
        (ratioExponent α (ENNReal.ofReal M * ENNReal.ofReal M).toReal / 2)) *
          acrossDist (D (h ω)) A := by
  classical
  let base := scaleBase lam R α hlam hR
  let N := scaleCount lam α
  let C : ℝ≥0∞ := ENNReal.ofReal M * ENNReal.ofReal M
  have hC0 : C ≠ 0 := by
    dsimp [C]
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith : 0 < M)).ne').ne'
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  obtain ⟨z, hz, hnear⟩ :=
    TwoScale.Mesh.exists_near_scaleMesh hlam hlam1.le hR z₀ A.center hcenter
  let S : Finset ℕ := (Finset.Icc 1 N).filter fun k =>
    h ω ∈ TwoScale.Ratio.rawRatioEvent D z (TwoScale.Ratio.ratioRadius base k) C
  have hS : S ⊆ Finset.Icc 1 N := by
    dsimp [S]
    exact Finset.filter_subset _ _
  have hhalf : (N : ℝ) / 2 ≤ (S.card : ℝ) := by
    apply le_of_not_gt
    intro hbad
    apply hcount
    refine ⟨z, hz, ?_⟩
    change (S.card : ℝ) < (1 / 2 : ℝ) * N
    nlinarith [hbad]
  have hprops := scaleCutoff_properties hα1
    (ENNReal.toReal_pos hC0 hCtop) hlam hsmall
  have hN8 : 8 ≤ N := Nat.le_floor hprops.2.1
  have hN8r : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hcardr : (2 : ℝ) ≤ (S.card : ℝ) := by linarith [hhalf]
  have hcard : 2 ≤ S.card := by exact_mod_cast hcardr
  have hgood : ∀ i ∈ S,
      aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) ≤
        C * acrossDist (D (h ω))
          (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hfinS : ∀ i ∈ S,
      aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base i)) ≠ ∞ :=
    fun i _ => hfin z hz i
  obtain ⟨i, hi, j, hj, haround, houterCost, hgrowth, hreal, hratio⟩ :=
    selected_growth_at_hit_annulus (D (h ω)) hB hL K hK
      hlam hlam1 hR hα1 A hAK hinner houter z hnear
      S hcard hS C hC0 hCtop hq0 hqT hP hPK hgeo
      h0 hT hq hgood hfinS hsmall hhalf
  exact hratio


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
