module
public import Formalization.Result.helpers.Theorem_4p2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

namespace Theorem_4p2

open MeasureTheory

/-- Theorem 4.2: simultaneous regional certification on one probability space,
with no independence assumption on the two reported radii. -/
theorem theorem_4_2 {d : ℕ} {Y : Type*} (S : SmoothingSystem d Y)
    (L : LocalScale d) (x0 : EuclideanSpace ℝ (Fin d))
    {Ω : Type*} [MeasurableSpace Ω] (C : CertificationEvents S L x0 Ω)
    (alpha beta : ℝ) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Icc (0 : ℝ) 1)
    (hc : 1 - alpha ≤ (C.probability {ω | ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x - x0‖ ≤ C.Rc ω → S.g x (L.sigma x0) = S.g x0 (L.sigma x0)}).toReal)
    (hsigma : 1 - beta ≤ (C.probability {ω | ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x - x0‖ ≤ C.Rsigma ω → L.sigma x = L.sigma x0}).toReal) :
    1 - alpha - beta ≤ (C.probability {ω | ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x - x0‖ < min (C.Rc ω) (C.Rsigma ω) →
        S.g x (L.sigma x) = S.g x0 (L.sigma x0)}).toReal := (by
  -- formalizer:proof-begin
  letI : IsProbabilityMeasure C.probability := C.isProbability
  let Ec : Set Ω := {ω | ∀ x : EuclideanSpace ℝ (Fin d),
    ‖x - x0‖ ≤ C.Rc ω → S.g x (L.sigma x0) = S.g x0 (L.sigma x0)}
  let Eσ : Set Ω := {ω | ∀ x : EuclideanSpace ℝ (Fin d),
    ‖x - x0‖ ≤ C.Rsigma ω → L.sigma x = L.sigma x0}
  have hEc : MeasurableSet Ec := C.measurable_Ec
  have hEσ : MeasurableSet Eσ := C.measurable_Esigma
  -- The union bound controls simultaneous failure on the common space.
  have hfailure := measureReal_union_le (μ := C.probability) Ecᶜ Eσᶜ
  rw [probReal_compl_eq_one_sub hEc,
    probReal_compl_eq_one_sub hEσ] at hfailure
  have hinter := probReal_compl_eq_one_sub (μ := C.probability) (hEc.inter hEσ)
  rw [Set.compl_inter] at hinter
  have hsuccess : 1 - alpha - beta ≤ C.probability.real (Ec ∩ Eσ) := by
    change 1 - alpha ≤ C.probability.real Ec at hc
    change 1 - beta ≤ C.probability.real Eσ at hsigma
    linarith
  -- On both success events, substitute the certified constant scale.
  have hinclusion : Ec ∩ Eσ ⊆ {ω | ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x - x0‖ < min (C.Rc ω) (C.Rsigma ω) →
        S.g x (L.sigma x) = S.g x0 (L.sigma x0)} := by
    intro ω hω x hx
    have hr := lt_min_iff.mp hx
    rw [hω.2 x hr.2.le]
    exact hω.1 x hr.1.le
  exact hsuccess.trans (measureReal_mono hinclusion)
  -- formalizer:proof-end
)

end Theorem_4p2
