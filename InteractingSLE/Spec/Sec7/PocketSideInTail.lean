/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailGeometry
import InteractingSLE.Spec.Sec7.PocketSideInTailReference
import InteractingSLE.Spec.Sec7.PocketSideInTailAccess
import InteractingSLE.Spec.Sec7.PocketSideInTailContacts
import InteractingSLE.Spec.Sec7.PocketSideInTailActual
import InteractingSLE.Spec.Sec7.PocketSideInTailLimit
import InteractingSLE.Spec.Sec7.PocketSideInTailPast
import InteractingSLE.Spec.Sec7.PocketSideInTailBound
import InteractingSLE.Spec.Sec7.PocketSideInTailCanonical

/-!
# Actual unfilled old-reference collars in R.5

PROVE-POCKET-SIDEIN. At a canonical current landing away from the terminal
point and outgoing corner, actual original-time pocket charts construct
rational reference times with unfilled half-discs. The correct old incident
access is derived from the inverse-fibre theorem and local bounds. The same
collars exclude current contacts and supply the current-domain approach.
Global exceptional-fibre coverage, marked reference laws and exact
reference-height normalization remain separate obligations.
-/
