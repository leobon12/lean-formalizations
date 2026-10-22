import HigherDimLQGMetric.Sec8b.Prop86ManyClasses

/-! The near-extreme event is covered, up to a null set, by finitely many class-count events. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

def s7b_manyFavEvent {Ω : Type} (h : Ω → DistRd d)
    (D Dt : DistRd d → ContMetric d) (ξ Q Cs R : ℝ)
    (J : ℕ) (N : ℕ → Set (Config d))
    (b : ℝ) (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ))
    (x y : Rd d) (k : ℕ) (t : ℝ)
    (c : ℤ × (Fin d → ℤ) × ℤ) : Set Ω :=
  {ω | t ≤ (((s7b_candidateFamily d J ((64 : ℝ) ^ c.1) R x y c.2.1 k).filter
    fun Z => h ω ∈ FavEventBorel D Dt ξ Q Cs ((2 : ℝ) ^ c.2.2) R
      ((64 : ℝ) ^ c.1) b J N V f x y Z).card : ℝ)}

theorem s7b_prop86_union_bound
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs B η ε R : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hR : 0 < R)
    (hεη : ε < η / 18) (hεhalf : ε ≤ 1 / 2)
    (hclass : (s7b_classSet d hε hR B).card *
      ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ ≤ s7b_sampleCount η ε)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (hx : ‖x‖ < 3 * R) (hy : ‖y‖ < 3 * R)
    (hxy : η * R ≤ ‖x - y‖)
    (k : ℕ) (hk : 1 ≤ k)
    (hkup : (k : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ)) :
    P {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
      sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω)} ≤
      ∑ c ∈ s7b_classSet d hε hR B,
        P (s7b_manyFavEvent (s7b_normalizedField h) D Dt ξ Q Cs R
          T.J T.N T.b T.V T.f x y k
          ((((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
            ⌈T.g / (4 * T.H) * k⌉₊) c) := by
  let C := s7b_classSet d hε hR B
  let E : (ℤ × (Fin d → ℤ) × ℤ) → Set Ω := fun c =>
    s7b_manyFavEvent (s7b_normalizedField h) D Dt ξ Q Cs R
      T.J T.N T.b T.V T.f x y k
      ((((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
        ⌈T.g / (4 * T.H) * k⌉₊) c
  have hmany := s7b_many_classes_ae P h hh hd hξ hQ hη hη1
    hε hR hεη hεhalf hclass hD hDt hcomp T x y hx hy hxy k hk hkup
  have hsub : ∀ᵐ ω ∂P,
      ω ∈ {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
        sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω)} →
      ω ∈ ⋃ c ∈ C, E c := by
    filter_upwards [hmany] with ω hω hw
    obtain ⟨c, hc, hcount⟩ := hω hw
    exact mem_biUnion hc (by exact hcount)
  calc
    P {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
      sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω)} ≤
        P (⋃ c ∈ C, E c) := measure_mono_ae hsub
    _ ≤ ∑ c ∈ C, P (E c) := measure_biUnion_finset_le C E
    _ = ∑ c ∈ s7b_classSet d hε hR B,
      P (s7b_manyFavEvent (s7b_normalizedField h) D Dt ξ Q Cs R
        T.J T.N T.b T.V T.f x y k
        ((((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
          ⌈T.g / (4 * T.H) * k⌉₊) c) := rfl

end HigherDimLQGMetric
