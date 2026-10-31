module
public import Formalization.Result.helpers.Theorem_4p1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Bp2

open Definition

public section

namespace Theorem_4p1

/-- Theorem 4.1, with the authorized ambient domain and interior probabilities
at the center and throughout the closed local ball. -/
theorem theorem_4_1 {d : ℕ} {Y : Type*} (S : SmoothingSystem d Y)
    (L : LocalScale d) (x0 : EuclideanSpace ℝ (Fin d)) (Rsigma : ℝ)
    (hconstant : ∀ x, ‖x - x0‖ ≤ Rsigma → L.sigma x = L.sigma x0)
    (hinterior : ∀ y z, z = x0 ∨ ‖z - x0‖ ≤ Rsigma →
      ClassProbability S.f y z (L.sigma x0) ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ x, ‖x - x0‖ < min Rsigma
      (StandardRadius S x0 (L.sigma x0)
        (L.positive _ (L.mem_scales x0))
        (hinterior (S.g x0 (L.sigma x0)) x0 (Or.inl rfl))) →
      S.g x (L.sigma x) = S.g x0 (L.sigma x0) := (by
  -- formalizer:proof-begin
  classical
  let s := L.sigma x0
  have hs : 0 < s := L.positive _ (L.mem_scales x0)
  intro x hx
  have hball := (lt_min_iff.mp hx).1.le
  have hscale : L.sigma x = s := hconstant x hball
  have hpx (y : Y) : ClassProbability S.f y x (L.sigma x) ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hscale]
    exact hinterior y x (Or.inr hball)
  have hp0 (y : Y) := hinterior y x0 (Or.inl rfl)
  -- Partition the ambient space by attained scales, as in the paper.
  let cells : Set.range L.sigma → Set (EuclideanSpace ℝ (Fin d)) :=
    fun i => {z | L.sigma z = i.val}
  have hd : Pairwise (fun i j => Disjoint (cells i) (cells j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact hij (Subtype.ext (hi.symm.trans hj))
  have hc : (⋃ i, cells i) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨⟨L.sigma z, ⟨z, rfl⟩⟩, rfl⟩
  have hk : ∀ i, ∀ z ∈ cells i, ∀ w ∈ cells i, L.sigma z = L.sigma w := by
    intro i z hz w hw
    exact hz.trans hw.symm
  let i : Set.range L.sigma := ⟨s, ⟨x0, rfl⟩⟩
  have hxcell : x ∈ cells i := hscale
  have h0cell : x0 ∈ cells i := rfl
  rw [hscale]
  by_contra hchange
  let A := S.g x0 s
  let B := S.g x s
  have hAB : A ≠ B := Ne.symm hchange
  -- Apply B.2 to A from the center to x, and to B in the reverse direction.
  have hA := Lemma_Bp2.lemma_B_2 S L cells hd hc hk A i x0 x h0cell hxcell (hp0 A) (hpx A)
  have hB := Lemma_Bp2.lemma_B_2 S L cells hd hc hk B i x x0 hxcell h0cell (hpx B) (hp0 B)
  simp only [ScaledClassQuantile, hscale] at hA hB
  rw [norm_sub_rev] at hA
  have hA' := (le_abs_self _).trans hA
  have hB' := (le_abs_self _).trans hB
  -- Maximality of B transfers the first estimate to its quantile.
  have hmono := Machinery.normal_quantile_mono
    (hinterior A x (Or.inr hball)) (hinterior B x (Or.inr hball))
    (S.maximizing x s hs A)
  have hscaled := mul_le_mul_of_nonneg_left hmono hs.le
  -- Distinct classes have disjoint events; normal symmetry supplies the radius.
  have hsum := Machinery.distinct_class_probability_sum
    S A B hAB x0 s
  have hcomp : 1 - ClassProbability S.f A x0 s ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [(hp0 A).1, (hp0 A).2]
  have hmono0 := Machinery.normal_quantile_mono
    (hp0 B) hcomp (by linarith : ClassProbability S.f B x0 s ≤ 1 - ClassProbability S.f A x0 s)
  rw [Machinery.normal_quantile_complement (hp0 A)] at hmono0
  have hscaled0 := mul_le_mul_of_nonneg_left hmono0 hs.le
  have hr := (lt_min_iff.mp hx).2
  change ‖x - x0‖ < s * Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1))
    (ClassProbability S.f A x0 s) at hr
  change L.sigma x0 = s at h0cell
  simp only [h0cell] at hA' hB'
  nlinarith
  -- formalizer:proof-end
)

end Theorem_4p1
