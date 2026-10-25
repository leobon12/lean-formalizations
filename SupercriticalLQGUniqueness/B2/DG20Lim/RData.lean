import SupercriticalLQGUniqueness.Frozen.Disconnects

 




set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
structure RatCircle where
  x : ℚ
  y : ℚ
  radius : ℚ
  radius_nonneg : 0 ≤ radius

namespace RatCircle

def center (O : RatCircle) : ℂ := Complex.mk (O.x : ℝ) (O.y : ℝ)

def toSet (O : RatCircle) : Set ℂ := Metric.sphere O.center (O.radius : ℝ)

def closedDisk (O : RatCircle) : Set ℂ := Metric.closedBall O.center (O.radius : ℝ)

def openDisk (O : RatCircle) : Set ℂ := Metric.ball O.center (O.radius : ℝ)

 
def Surrounds (O : RatCircle) (z : ℂ) : Prop := 0 < O.radius ∧ z ∈ O.openDisk

 
def SurroundsCircle (O I : RatCircle) : Prop :=
  0 < O.radius ∧ I.closedDisk ⊆ O.openDisk

end RatCircle

 

structure RatAnnulus where
  inner : RatCircle
  outer : RatCircle
  inner_pos : 0 < inner.radius
  nested : outer.SurroundsCircle inner

namespace RatAnnulus

def toSet (A : RatAnnulus) : Set ℂ := A.outer.closedDisk \ A.inner.openDisk

def interior (A : RatAnnulus) : Set ℂ := A.outer.openDisk \ A.inner.closedDisk

 
def OppositeSides (A : RatAnnulus) (O O' : RatCircle) : Prop :=
  (O.toSet ⊆ A.inner.closedDisk ∧ O'.toSet ⊆ A.outer.openDiskᶜ) ∨
    (O'.toSet ⊆ A.inner.closedDisk ∧ O.toSet ⊆ A.outer.openDiskᶜ)

end RatAnnulus

 


structure RData where
  across : RatCircle → RatCircle → ℝ≥0∞
  around : RatAnnulus → ℝ≥0∞
  across_symm : ∀ O O', across O O' = across O' O
  chain_lower : ∀ (k : ℕ) (O : Fin (k + 1) → RatCircle),
    (∀ i j : Fin (k + 1), i ≠ j → Disjoint (O i).toSet (O j).toSet) →
    (∀ j : ℕ, (hj : 0 < j) → (hk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet) →
    (∑ j : Fin k, across (O ⟨j.val, by omega⟩) (O ⟨j.val + 1, by omega⟩)) ≤
      across (O ⟨0, by omega⟩) (O ⟨k, by omega⟩)
  around_upper : ∀ (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
    A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
      across O₁ O₂ ≤ across O₁ O₁' + across O₂ O₂' + around A
  across_pos : ∀ O₁ O₂, Disjoint O₁.toSet O₂.toSet → 0 < across O₁ O₂

end SupercriticalLQGUniqueness.B2.DG20Lim
