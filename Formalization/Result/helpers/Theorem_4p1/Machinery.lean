module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_Bp2
public import Mathlib

public section

namespace Theorem_4p1.Machinery

-- formalizer:machinery-begin

lemma normal_cdf_continuous : Continuous (ProbabilityTheory.cdf
    (ProbabilityTheory.gaussianReal 0 1)) := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  letI : MeasureTheory.NoAtoms μ := ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  have heq : (fun x => ∫ _ in Set.Iic x, (1 : ℝ) ∂μ) = ProbabilityTheory.cdf μ := by
    funext x
    simp [ProbabilityTheory.cdf_eq_real, MeasureTheory.measureReal_def]
  rw [← heq]
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ((MeasureTheory.integrable_const (1 : ℝ)).integrableOn.continuousOn_Iic_primitive_Iic
    x (show x ∈ Set.Iic (x + 1) by simp)).continuousAt (Iic_mem_nhds (by linarith))

lemma normal_cdf_strictMono : StrictMono (ProbabilityTheory.cdf
    (ProbabilityTheory.gaussianReal 0 1)) := by
  intro a b hab
  have hpos : 0 < ProbabilityTheory.gaussianReal 0 1 (Set.Ioc a b) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have := ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0) hz
    have hba : b ≤ a := by simpa [Real.volume_Ioc] using this
    exact (not_le.mpr hab) hba
  rw [← ProbabilityTheory.measure_cdf (μ := ProbabilityTheory.gaussianReal 0 1), StieltjesFunction.measure_Ioc] at hpos
  exact sub_pos.mp (ENNReal.ofReal_pos.mp hpos)

lemma normal_cdf_quantile {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)
      (Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) p) = p := by
  apply Function.invFun_eq
  obtain ⟨x, _, hx⟩ := isPreconnected_univ.intermediate_value_Ioo
    (Filter.le_principal_iff.mpr (Filter.Eventually.of_forall (fun z : ℝ => Set.mem_univ z)))
    (Filter.le_principal_iff.mpr (Filter.Eventually.of_forall (fun z : ℝ => Set.mem_univ z)))
    normal_cdf_continuous.continuousOn
    (ProbabilityTheory.tendsto_cdf_atBot (μ := ProbabilityTheory.gaussianReal 0 1))
    (ProbabilityTheory.tendsto_cdf_atTop (μ := ProbabilityTheory.gaussianReal 0 1)) hp
  exact ⟨x, hx⟩

lemma normal_quantile_mono {p q : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (h : p ≤ q) :
    Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) p ≤
      Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) q := by
  apply normal_cdf_strictMono.le_iff_le.mp
  simpa only [normal_cdf_quantile hp, normal_cdf_quantile hq] using h

lemma normal_cdf_neg (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-x) =
      1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  letI : MeasureTheory.NoAtoms μ := ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  have hm : μ.map (fun z => -z) = μ := by
    simp [μ, ProbabilityTheory.gaussianReal_map_neg]
  have he : (fun z : ℝ => -z) ⁻¹' Set.Iic (-x) = Set.Ici x := by
    ext z
    simp
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real]
  change μ.real (Set.Iic (-x)) = 1 - μ.real (Set.Iic x)
  conv_lhs => rw [← hm]
  rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.map_apply (by fun_prop) measurableSet_Iic, he]
  rw [← MeasureTheory.measure_congr MeasureTheory.Ioi_ae_eq_Ici]
  have hc := MeasureTheory.probReal_compl_eq_one_sub (μ := μ) (s := Set.Iic x) measurableSet_Iic
  simpa [Set.compl_Iic, MeasureTheory.measureReal_def] using hc

lemma normal_quantile_complement {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) (1 - p) =
      -Function.invFun (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) p := by
  apply normal_cdf_strictMono.injective
  rw [normal_cdf_quantile (show 1 - p ∈ Set.Ioo (0 : ℝ) 1 by constructor <;> linarith [hp.1, hp.2]),
    normal_cdf_neg, normal_cdf_quantile hp]

lemma distinct_class_probability_sum {d : ℕ} {Y : Type*}
    (S : Definition.SmoothingSystem d Y) (a b : Y) (hab : a ≠ b)
    (x : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    Definition.ClassProbability S.f a x s + Definition.ClassProbability S.f b x s ≤ 1 := by
  let μ := (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun z => s • z)
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin d) => s • z) := by fun_prop
  letI : MeasureTheory.IsProbabilityMeasure μ := MeasureTheory.Measure.isProbabilityMeasure_map hm.aemeasurable
  have hd : Disjoint {δ | S.f (x + δ) = a} {δ | S.f (x + δ) = b} := by
    apply Set.disjoint_left.mpr
    intro z ha hb
    exact hab (ha.symm.trans hb)
  have hb : MeasurableSet {δ | S.f (x + δ) = b} :=
    (S.measurable_fiber b).preimage (by fun_prop)
  change μ.real _ + μ.real _ ≤ 1
  rw [← MeasureTheory.measureReal_union hd hb]
  exact (MeasureTheory.measureReal_mono (Set.subset_univ _)).trans (by simp)
-- formalizer:machinery-end

end Theorem_4p1.Machinery
