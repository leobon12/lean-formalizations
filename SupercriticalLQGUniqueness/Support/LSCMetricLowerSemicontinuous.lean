import SupercriticalLQGUniqueness.Support.LSCMetricIsExtMetric

 
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

theorem lowerSemicontinuous (D : LSCMetric) : LowerSemicontinuous D := D.2.2
end LSCMetric
end SupercriticalLQGUniqueness
