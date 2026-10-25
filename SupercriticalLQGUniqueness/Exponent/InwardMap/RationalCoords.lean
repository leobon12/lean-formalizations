import SupercriticalLQGUniqueness.Exponent.InwardMap.PolygonFamilyCost




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

open LQGMetric.LFPP

theorem ratComplex_injective : Function.Injective ratComplex := by
  intro p q h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [ratComplex] at hre him
  apply Prod.ext
  · exact_mod_cast hre
  · exact_mod_cast him

theorem gaussRat_unique_coords {z : ℂ} (hz : z ∈ gaussRat) :
    ∃! p : ℚ × ℚ, ratComplex p = z := by
  obtain ⟨p, hp⟩ := hz
  refine ⟨p, ?_, ?_⟩
  · simpa [ratComplex] using hp
  · intro q hq
    apply ratComplex_injective
    calc
      ratComplex q = z := hq
      _ = ratComplex p := by simpa [ratComplex] using hp.symm

 
def gaussRatCoords (z : ℂ) (hz : z ∈ gaussRat) : ℚ × ℚ :=
  (gaussRat_unique_coords hz).choose

theorem ratComplex_gaussRatCoords (z : ℂ) (hz : z ∈ gaussRat) :
    ratComplex (gaussRatCoords z hz) = z :=
  (gaussRat_unique_coords hz).choose_spec.1


end SupercriticalLQGUniqueness.Exponent.InwardMap
