import SupercriticalLQGUniqueness.Support.LSCMetricInstCoeFun

 
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

theorem isExtMetric (D : LSCMetric) : IsExtMetric D := D.2.1
end LSCMetric
end SupercriticalLQGUniqueness
