import data.real.basic

open set real

example : inj_on sqrt { x | x ≥ 0 } :=
sorry

example : inj_on (λ x, x^2) { x | x ≥ 0 } :=
sorry

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
sorry

example : range (λ x, x^2) = {y | y ≥ 0} :=
sorry