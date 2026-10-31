module
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Axioms

open MeasureTheory ProbabilityTheory

/-- The cited fixed-scale Gaussian class-indicator bound (Lemma B.1).
Only endpoint probabilities in `(0,1)` are covered. -/
axiom gaussianQuantileLipschitz {d : ℕ} {Y : Type*}
    (f : EuclideanSpace ℝ (Fin d) → Y)
    (hf : ∀ y, MeasurableSet {x | f x = y})
    (y : Y) (s : ℝ) (hs : 0 < s)
    (x z : EuclideanSpace ℝ (Fin d))
    (hx : ClassProbability f y x s ∈ Set.Ioo (0 : ℝ) 1)
    (hz : ClassProbability f y z s ∈ Set.Ioo (0 : ℝ) 1) :
    |s * Function.invFun (cdf (gaussianReal 0 1)) (ClassProbability f y x s) -
      s * Function.invFun (cdf (gaussianReal 0 1)) (ClassProbability f y z s)| ≤
      ‖x - z‖

end Axioms
