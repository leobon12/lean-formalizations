/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatchGeometry
import InteractingSLE.Spec.Sec7.PocketSideInPatchClock
import InteractingSLE.Spec.Sec7.PocketSideInPatchActualClock
import InteractingSLE.Spec.Sec7.PocketSideInPatchTip
import InteractingSLE.Spec.Sec7.PocketSideInPatchCurrent
import InteractingSLE.Spec.Sec7.PocketSideInPatchGerm
import InteractingSLE.Spec.Sec7.PocketSideInPatchUniform

/-!
# Actual driver-neighborhood collars and R.5 comparisons

PROVE-POCKET-SIDEIN. At any nested actual common visit, the canonical
current inverse at zero lands at the original counterflow point. Every
current access landing inside the initial inner pocket has a current
shared collar. Hence a whole driver interval has such collars, and the
R.5 physical and corrected difference germs vanish there. The comparisons
hold on one rational-time event for a fixed countable candidate family.
The R.6 interval extending to a proper unvisited shared-side anchor,
its exact inherited height, and suitable source coverage remain open.
-/
