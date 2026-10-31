module
public import Formalization.Result.helpers.Lemma_Bp2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Axioms Definition

public section

namespace Lemma_Bp2

/-- Lemma B.2: the scaled class quantile is unit Lipschitz within each
constant-scale cell, restricted to interior class probabilities. -/
lemma lemma_B_2 {d : ℕ} {Y : Type*} (S : SmoothingSystem d Y)
    (L : LocalScale d) {I : Type*} (cells : I → Set (EuclideanSpace ℝ (Fin d)))
    (hdisjoint : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hcover : (⋃ i, cells i) = Set.univ)
    (hconstant : ∀ i, ∀ x ∈ cells i, ∀ z ∈ cells i, L.sigma x = L.sigma z)
    (y : Y) (i : I) (x z : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ cells i) (hz : z ∈ cells i)
    (hpx : ClassProbability S.f y x (L.sigma x) ∈ Set.Ioo (0 : ℝ) 1)
    (hpz : ClassProbability S.f y z (L.sigma z) ∈ Set.Ioo (0 : ℝ) 1) :
    |ScaledClassQuantile S L y x hpx - ScaledClassQuantile S L y z hpz| ≤ ‖x - z‖ := (by
  -- formalizer:proof-begin
  -- Both points have the same positive scale in this cell.
  have heq := hconstant i x hx z hz
  have hs := L.positive (L.sigma x) (L.mem_scales x)
  have hpz' : ClassProbability S.f y z (L.sigma x) ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [heq] using hpz
  -- Apply the cited fixed-scale bound at the two interior endpoints.
  have hbound := gaussianQuantileLipschitz S.f S.measurable_fiber y
    (L.sigma x) hs x z hpx hpz'
  simpa only [ScaledClassQuantile, heq] using hbound
  -- formalizer:proof-end
)

end Lemma_Bp2
