module
public import Mathlib

@[expose] public section

namespace Definition

open MeasureTheory ProbabilityTheory

/-- Exact class probability for noise `s • Z`, with `Z` standard Gaussian.
Thus the noise has mean zero and covariance `s² I`. -/
noncomputable def ClassProbability {d : ℕ} {Y : Type*}
    (f : EuclideanSpace ℝ (Fin d) → Y) (y : Y)
    (x : EuclideanSpace ℝ (Fin d)) (s : ℝ) : ℝ :=
  (((stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => s • z))
    {δ | f (x + δ) = y}).toReal

/-- A classifier on the entire ambient space and a fixed attained maximizing
selection at every positive scale. Labels need not form a finite type. -/
structure SmoothingSystem (d : ℕ) (Y : Type*) where
  f : EuclideanSpace ℝ (Fin d) → Y
  measurable_fiber : ∀ y, MeasurableSet {x | f x = y}
  g : EuclideanSpace ℝ (Fin d) → ℝ → Y
  maximizing : ∀ x s, 0 < s → ∀ y,
    ClassProbability f y x s ≤ ClassProbability f (g x s) x s

/-- The standard radius is defined only for an interior maximum probability.
`invFun` of the standard normal CDF is its ordinary inverse on `(0,1)`. -/
noncomputable def StandardRadius {d : ℕ} {Y : Type*}
    (S : SmoothingSystem d Y) (x : EuclideanSpace ℝ (Fin d))
    (s : ℝ) (_hs : 0 < s)
    (_hp : ClassProbability S.f (S.g x s) x s ∈ Set.Ioo (0 : ℝ) 1) : ℝ :=
  s * Function.invFun (cdf (gaussianReal 0 1)) (ClassProbability S.f (S.g x s) x s)

/-- Allowed scales are discrete and strictly positive. Local constancy on a
closed ball, or constancy on cells of a partition, is a separate hypothesis:
no regularity of the scale function or of its fibers is imposed here. -/
structure LocalScale (d : ℕ) where
  scales : Set ℝ
  discrete : DiscreteTopology scales
  positive : ∀ s ∈ scales, 0 < s
  sigma : EuclideanSpace ℝ (Fin d) → ℝ
  mem_scales : ∀ x, sigma x ∈ scales

/-- The classwise adaptive scaled quantile on its interior-probability domain. -/
noncomputable def ScaledClassQuantile {d : ℕ} {Y : Type*}
    (S : SmoothingSystem d Y) (L : LocalScale d) (y : Y)
    (x : EuclideanSpace ℝ (Fin d))
    (_hp : ClassProbability S.f y x (L.sigma x) ∈ Set.Ioo (0 : ℝ) 1) : ℝ :=
  L.sigma x * Function.invFun (cdf (gaussianReal 0 1))
    (ClassProbability S.f y x (L.sigma x))

/-- Certification uncertainty has its own common probability space. The three
sets below are respectively `Ec`, `Esigma`, and `Eadaptive`; their definitions
quantify simultaneously over the whole certified region. No independence or
certificate-success assumption is part of this data. -/
structure CertificationEvents {d : ℕ} {Y : Type*}
    (S : SmoothingSystem d Y) (L : LocalScale d)
    (x0 : EuclideanSpace ℝ (Fin d)) (Ω : Type*) [MeasurableSpace Ω] where
  probability : Measure Ω
  isProbability : IsProbabilityMeasure probability
  Rc : Ω → ℝ
  Rsigma : Ω → ℝ
  measurable_Rc : Measurable Rc
  measurable_Rsigma : Measurable Rsigma
  measurable_Ec : MeasurableSet {ω | ∀ x : EuclideanSpace ℝ (Fin d),
    ‖x - x0‖ ≤ Rc ω → S.g x (L.sigma x0) = S.g x0 (L.sigma x0)}
  measurable_Esigma : MeasurableSet {ω | ∀ x : EuclideanSpace ℝ (Fin d),
    ‖x - x0‖ ≤ Rsigma ω → L.sigma x = L.sigma x0}
  measurable_Eadaptive : MeasurableSet {ω | ∀ x : EuclideanSpace ℝ (Fin d),
    ‖x - x0‖ < min (Rc ω) (Rsigma ω) →
      S.g x (L.sigma x) = S.g x0 (L.sigma x0)}

end Definition
