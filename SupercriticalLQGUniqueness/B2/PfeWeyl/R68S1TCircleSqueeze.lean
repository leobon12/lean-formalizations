import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TDense
import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TLsc
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CSqueeze
import SupercriticalLQGUniqueness.B2.PfeWeyl.CircleLiminf

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 

def CountableUpperShifts (g : ℕ → C(ℂ, ℝ)) : Prop :=
  ∀ (f : C(ℂ, ℝ)) (M : ℝ), (∀ z, |f z| ≤ M) →
    ∃ u : ℕ → ℕ, (∀ j z, f z ≤ g (u j) z) ∧
      ∀ (j : ℕ), ∀ z ∈ Metric.closedBall (0 : ℂ) j,
        g (u j) z ≤ f z + 1 / ((j : ℝ) + 1)

 
def FixedFieldWeylAllCircles
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (Φ : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWholePlaneGFF h P →
    ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
      (∀ δ, IsHeatSmoothing P h δ (X δ)) →
      ∀ᵐ ω ∂P, ∀ (f : C(ℂ, ℝ)) (Mf : ℝ) (hf : ∀ z, |f z| ≤ Mf),
        ∀ O O' : B2.DG20Lim.RatCircle,
          Tendsto (fun n => setDistance
            (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
              (X (ε n) ω + LQGMetric.LFPP.mollCont
                (ε n : ℝ) (ε n).property.ne' f Mf hf))
              O.toSet O'.toSet) atTop
            (𝓝 (setDistance (weylScale (ξ : ℝ) f (Φ (h ω)))
              O.toSet O'.toSet))

 
theorem setDistance_le_of_metric_le {D E : ℂ × ℂ → ℝ≥0∞}
    (hDE : ∀ p, D p ≤ E p) (O O' : Set ℂ) :
    setDistance D O O' ≤ setDistance E O O' := by
  unfold setDistance
  exact iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ =>
    iInf_mono fun _ => hDE _

 


theorem ae_weyl_rationalCircle_all_bounded_of_upper_squeeze
    (ξ : Ioi (0 : ℝ)) (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ)) (Φ : DistC → LSCMetric)
    (hW3 : FixedFieldWeylAllBounded ξ m ε Φ)
    (hgeo : NormalizedLimitGeometry Φ)
    (g : ℕ → C(ℂ, ℝ)) (M : ℕ → ℝ)
    (hM : ∀ i z, |g i z| ≤ M i) (hupper : CountableUpperShifts g)
    (hcircle : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
        (∀ δ, IsHeatSmoothing P h δ (X δ)) →
        ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ O O' : B2.DG20Lim.RatCircle,
          Tendsto (fun n => setDistance
            (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
              (X (ε n) ω + LQGMetric.LFPP.mollCont
                (ε n : ℝ) (ε n).property.ne' (g i) (M i) (hM i)))
              O.toSet O'.toSet) atTop
            (𝓝 (setDistance (weylScale (ξ : ℝ) (g i) (Φ (h ω)))
              O.toSet O'.toSet))) :
    FixedFieldWeylAllCircles ξ m ε Φ := by
  intro Ω _ P _ h hh X hX
  filter_upwards [hW3 P h hh X hX, (hgeo P h hh).2, hcircle P h hh X hX]
    with ω hWω hGω hCω f Mf hf O O'
  obtain ⟨u, hdom, hloc⟩ := hupper f Mf hf
  let G (n : ℕ) : LSCMetric := normalizedLFPPMetric (ξ : ℝ) (m (ε n))
    (X (ε n) ω + LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne' f Mf hf)
  obtain ⟨E, hE, hconv⟩ := hWω f Mf hf
  have hlow : setDistance (weylScale (ξ : ℝ) f (Φ (h ω))) O.toSet O'.toSet ≤
      liminf (fun n => setDistance (G n) O.toSet O'.toSet) atTop := by
    have hlow' := setDistance_liminf_of_compact (O := O.toSet) (O' := O'.toSet) hconv
      (isCompact_sphere _ _) (isCompact_sphere _ _)
    have hEq : (fun p => E p) = weylScale (ξ : ℝ) f (Φ (h ω)) := funext hE
    change setDistance (fun p => E p) O.toSet O'.toSet ≤
      liminf (fun n => setDistance (G n) O.toSet O'.toSet) atTop at hlow'
    rwa [hEq] at hlow'
  refine tendsto_of_le_liminf_of_limsup_le hlow ?_
  have hlimsup : ∀ j, limsup (fun n => setDistance (G n) O.toSet O'.toSet) atTop ≤
      setDistance (weylScale (ξ : ℝ) (g (u j)) (Φ (h ω))) O.toSet O'.toSet := by
    intro j
    have hmono : ∀ n, setDistance (G n) O.toSet O'.toSet ≤
        setDistance (normalizedLFPPMetric (ξ : ℝ) (m (ε n))
          (X (ε n) ω + LQGMetric.LFPP.mollCont
            (ε n : ℝ) (ε n).property.ne' (g (u j)) (M (u j)) (hM (u j))))
          O.toSet O'.toSet := by
      intro n
      exact setDistance_le_of_metric_le
        (normalizedLFPPMetric_add_mollCont_mono ξ.property.le (m (ε n))
          (X (ε n) ω) (ε n).property.ne' hf (hM (u j)) (hdom j)) _ _
    exact (limsup_le_limsup (Eventually.of_forall hmono)
      (by isBoundedDefault) (by isBoundedDefault)).trans
      (le_of_eq (Filter.Tendsto.limsup_eq (hCω (u j) O O')))
  have hlocal : ∀ (j : ℕ), ∀ z ∈ Metric.closedBall (0 : ℂ) j,
      g (u j) z ≤ f z + 1 / ((j : ℝ) + 1) := hloc
  have hη : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpoint (p : ℂ × ℂ) :
      limsup (fun j => weylScale (ξ : ℝ) (g (u j)) (Φ (h ω)) p) atTop ≤
        weylScale (ξ : ℝ) f (Φ (h ω)) p :=
    limsup_weylScale_le_of_upper ξ.property.le
      (B2.PfeLocal.continuous_euclidForget_of_small_metric _ hGω) f
      (fun j => g (u j)) _ hη hlocal p
  have hkey (p : ℂ × ℂ) (hp : p.1 ∈ O.toSet ∧ p.2 ∈ O'.toSet) :
      limsup (fun n => setDistance (G n) O.toSet O'.toSet) atTop ≤
        weylScale (ξ : ℝ) f (Φ (h ω)) p := by
    have hj : ∀ j, limsup (fun n => setDistance (G n) O.toSet O'.toSet) atTop ≤
        weylScale (ξ : ℝ) (g (u j)) (Φ (h ω)) p := fun j =>
      (hlimsup j).trans (iInf₂_le_of_le p.1 hp.1 (iInf₂_le p.2 hp.2))
    exact (le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall hj)).trans
      ((liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans (hpoint p))
  unfold setDistance
  exact le_iInf fun a => le_iInf fun ha => le_iInf fun b => le_iInf fun hb =>
    hkey (a, b) ⟨ha, hb⟩

end SupercriticalLQGUniqueness.B2.PfeWeyl
