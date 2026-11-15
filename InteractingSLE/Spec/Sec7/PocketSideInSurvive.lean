/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveNeighborhood
import InteractingSLE.Spec.Sec7.PocketSideInSurviveLoewner
import InteractingSLE.Spec.Sec7.PocketSideInSurviveInitial
import InteractingSLE.Spec.Sec7.PocketSideInSurviveActual
import InteractingSLE.Spec.Sec7.PocketSideInSurviveComparison
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrementGeometry
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrementLaw
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrementGerm
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrement
import InteractingSLE.Spec.Sec7.PocketSideInSurviveHeight

/-!
# Surviving incoming accesses, actual mean increments and exact height transport

PROVE-POCKET-SIDEIN. Survival and a shared current collar supply the shared
initial neighborhood. Initial/current labeled laws prove the old-to-current
mean germ, so exact incoming height transport needs no independent increment
premise. The actual surviving access, shared collar and initial exact height
remain the source geometric inputs.
-/
