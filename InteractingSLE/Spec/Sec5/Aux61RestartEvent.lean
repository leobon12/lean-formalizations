import InteractingSLE.Spec.Sec5.Aux61RestartEventProtected

/-!
# Restart charts on the measurable original right-target event

Packet PROVE-AUX61-R1, continuation of the actual-history construction.

`frequent_inv_mem_iff_dense_chart_values` detects current-access incidence
by countably many forward evaluations at a fixed dense sequence. Its random
version proves the source's component event measurable from the retained
counterflow and own histories. No inverse-map measurability is required.

`has_original_target_restart_chart_on_protected_event` constructs the chart
on that measurable event, without a global incidence or protection premise.
The protected target event is also measured from the retained counterflow;
the landed `cfGlueAE_original_target_protected` supplies its probability-one
property for actual glued histories. The exact inherited logarithm and both
prime-end limits are preserved by the chart output.

`exists_fresh_segment_in_incident_component` proves that a simple extension
stays in the incident component for a positive original own-time interval.
It assumes no prescribed future segment is already in that component.

The source restricts to this component event. These declarations do not
assert that it contains every history pair or prove the conditional field
kernel or fibre-cover law of the consuming packets. R48 and R77 apply.
-/
