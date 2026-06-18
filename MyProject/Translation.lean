import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# `Lᵖ`-continuity of translation for continuous, compactly supported functions

This slim file isolates the continuous-compact-support case of `Lᵖ`-translation continuity,
`tendsto_eLpNorm_translate_sub_continuous`, together with its supporting `Lᵖ` support bound.
It is shared between `Mollification.lean` (which bootstraps to the general `MemLp` case via
density) and `FrechetKolmogorov.lean` (which needs only the continuous case, for the
equicontinuity of mollifications).  Keeping it free of `MyProject.Sobolev` avoids dragging the
full-`Mathlib` import into the slim Fréchet–Kolmogorov file.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal NNReal

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-- An `Lᵖ` bound for a function supported in a set `L` and bounded in norm:
`‖f‖_p ≤ (vol L)^{1/p} · C`. -/
lemma eLpNorm_le_of_support_subset {f : ℝⁿ → ℝ} {L : Set ℝⁿ}
    (hsupp : Function.support f ⊆ L) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {p : ℝ≥0∞} :
    eLpNorm f p volume ≤ (volume L) ^ (p.toReal⁻¹) * ENNReal.ofReal C := by
  rw [← eLpNorm_restrict_eq_of_support_subset hsupp]
  calc eLpNorm f p (volume.restrict L)
      ≤ (volume.restrict L) Set.univ ^ (p.toReal⁻¹) * ENNReal.ofReal C :=
        eLpNorm_le_of_ae_bound (Filter.Eventually.of_forall hC)
    _ = (volume L) ^ (p.toReal⁻¹) * ENNReal.ofReal C := by rw [Measure.restrict_apply_univ]

/-- **Translation is `Lᵖ`-continuous for continuous, compactly supported functions.** -/
lemma tendsto_eLpNorm_translate_sub_continuous {g : ℝⁿ → ℝ}
    (hg : Continuous g) (h2g : HasCompactSupport g) {p : ℝ≥0∞} :
    Tendsto (fun t : ℝⁿ => eLpNorm (fun x => g (x + t) - g x) p volume) (𝓝 0) (𝓝 0) := by
  have hunif : UniformContinuous g :=
    hg.uniformContinuous_of_tendsto_cocompact (h2g.is_zero_at_infty)
  -- a fixed compact set containing all the relevant supports (for `‖t‖ < 1`)
  set L : Set ℝⁿ := Metric.cthickening 1 (tsupport g) with hLdef
  have hLc : IsCompact L := IsCompact.cthickening h2g
  set cV : ℝ≥0∞ := (volume L) ^ (p.toReal⁻¹) with hcV
  have hcV_ne : cV ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (ne_of_lt hLc.measure_lt_top)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ∞ with rfl | hε_top
  · exact Eventually.of_forall fun t => le_top
  -- pick a real modulus `η > 0` with `cV · ofReal η ≤ ε`
  have hcV1 : cV + 1 ≠ 0 := (lt_of_lt_of_le zero_lt_one le_add_self).ne'
  have hcV1_top : cV + 1 ≠ (⊤ : ℝ≥0∞) := ENNReal.add_ne_top.mpr ⟨hcV_ne, ENNReal.one_ne_top⟩
  obtain ⟨η, hη_pos, hη_le⟩ : ∃ η : ℝ, 0 < η ∧ cV * ENNReal.ofReal η ≤ ε := by
    have hdiv_top : ε / (cV + 1) ≠ (⊤ : ℝ≥0∞) := ENNReal.div_ne_top hε_top hcV1
    refine ⟨(ε / (cV + 1)).toReal, ?_, ?_⟩
    · have hne : ε / (cV + 1) ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', hcV1_top⟩
      exact ENNReal.toReal_pos hne hdiv_top
    · rw [ENNReal.ofReal_toReal hdiv_top]
      calc cV * (ε / (cV + 1)) ≤ (cV + 1) * (ε / (cV + 1)) := by gcongr; exact le_self_add
        _ = ε := ENNReal.mul_div_cancel hcV1 hcV1_top
  -- uniform continuity threshold; also force `‖t‖ < 1`
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.uniformContinuous_iff.mp hunif η hη_pos
  filter_upwards [Metric.ball_mem_nhds (0 : ℝⁿ) (lt_min hδ_pos one_pos)] with t ht
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at ht
  have ht_δ : ‖t‖ < δ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht_1 : ‖t‖ < 1 := lt_of_lt_of_le ht (min_le_right _ _)
  refine (eLpNorm_le_of_support_subset ?_ ?_).trans hη_le
  · -- support of the difference lies in `L`
    refine (Function.support_sub _ _).trans (union_subset ?_ ?_)
    · intro x hx
      have hxt : x + t ∈ tsupport g := subset_tsupport _ (by simpa using hx)
      refine Metric.mem_cthickening_of_dist_le x (x + t) 1 (tsupport g) hxt ?_
      rw [dist_eq_norm, show x - (x + t) = -t by abel, norm_neg]
      exact ht_1.le
    · exact (subset_tsupport _).trans (Metric.self_subset_cthickening _)
  · intro x
    have hd : dist (x + t) x < δ := by rw [dist_eq_norm]; simpa using ht_δ
    have := hδ hd
    rw [dist_eq_norm] at this
    exact this.le

end Sobolev
