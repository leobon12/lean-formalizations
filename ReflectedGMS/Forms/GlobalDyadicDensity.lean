import ReflectedGMS.Forms.GlobalDyadicSupport
import ReflectedGMS.Forms.DyadicSupportDensity

set_option autoImplicit false

open Set Filter Topology
open scoped NNReal

namespace ReflectedGMS

theorem globalDyadicSupport_countable : globalDyadicSupport.Countable := by
  unfold globalDyadicSupport ReflectedWalk.Theorem16.dyadicMesh
  exact Set.countable_iUnion (fun _ => Set.countable_range _)

theorem globalDyadicSupport_nhdsWithin_Ioi_neBot (t : ℝ≥0) :
    (𝓝[globalDyadicSupport ∩ Ioi t] t).NeBot := by
  obtain ⟨N, ht⟩ := exists_pow_two_horizon t
  rw [nhdsWithin_globalDyadicSupport_eq N ht (Ioi t)]
  exact dyadicSupport_nhdsWithin_Ioi_neBot (2 ^ N) (by positivity) ht

theorem globalDyadicSupport_nhdsWithin_Iio_neBot {t : ℝ≥0} (ht : 0 < t) :
    (𝓝[globalDyadicSupport ∩ Iio t] t).NeBot := by
  obtain ⟨N, htN⟩ := exists_pow_two_horizon t
  rw [nhdsWithin_globalDyadicSupport_eq N htN (Iio t)]
  exact dyadicSupport_nhdsWithin_Iio_neBot (2 ^ N) (by positivity) ht htN.le

end ReflectedGMS
