import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Compose
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.S36




 















set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

 
theorem t58CentreInputsInput_of_radius_residual (hR : T58RadiusResidual) :
    Assembly.Inputs.T58CentreInputsInput :=
  t58CentreInputsInput_of_residual p364DyadicInput_proved hR

 

theorem t58Input_of_radius_residual (hR : T58RadiusResidual) : Assembly.Inputs.T58Input :=
  t58Input_of_residual p364DyadicInput_proved hR

 

theorem t58Input_of_budgets (hB : T58BudgetResidual) : Assembly.Inputs.T58Input :=
  t58Input_of_budget_residual p364DyadicInput_proved hB

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
