import MyProject.FrechetKolmogorov
import MyProject.Mollification

/-!
# Fréchet–Kolmogorov / Rellich–Kondrachov: the self-contained criterion (Evans §5.7)

Discharging the mollifiability hypothesis of `totallyBounded_toLp_restrict_of_mollifiable` by an
explicit mollifier (a normalised `ContDiffBump` of radius `δ`) and the integral-form uniform
mollification bound, this gives the **self-contained sufficient direction of Fréchet–Kolmogorov**:
a uniformly bounded, uniformly `Lᵖ`-equicontinuous family is totally bounded in `Lᵖ` on a compact
domain.  This is the analytic heart of Rellich–Kondrachov (the `W^{1,p}` equicontinuity being
supplied by the gradient/translation estimate of `Rellich.lean`).
-/

open MeasureTheory Topology Filter Set
open scoped ENNReal Convolution

variable {n : ℕ}

local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

namespace Sobolev

/-- **Fréchet–Kolmogorov, sufficient direction (self-contained).**  A family `u : ι → ℝⁿ → ℝ`
that is uniformly `L^P`-bounded and **uniformly `Lᵖ`-equicontinuous** (`‖u i(·−y) − u i‖_p → 0`
uniformly in `i` as `y → 0`) is **totally bounded in `Lᵖ(K, restrict)`** on any compact `K`.
The mollifiability hypothesis is discharged by a normalised bump of radius `δ` (chosen from the
equicontinuity modulus) and the integral-form uniform mollification bound. -/
theorem totallyBounded_toLp_restrict_of_equicontinuous {ι : Type*} {K : Set ℝⁿ} (hK : IsCompact K)
    {P Q : ℝ} (hPQ : P.HolderConjugate Q) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : ι → ℝⁿ → ℝ} (hu : ∀ i, MemLp (u i) (ENNReal.ofReal P) volume)
    (hup : ∀ i, MemLp (u i) p volume) (huK : ∀ i, MemLp (u i) p (volume.restrict K))
    {B : ℝ} (hB : ∀ i, (eLpNorm (u i) (ENNReal.ofReal P) volume).toReal ≤ B)
    (hequi : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ i, ∀ y : ℝⁿ, ‖y‖ < δ →
      eLpNorm (fun x => u i (x - y) - u i x) p volume ≤ ENNReal.ofReal ε) :
    TotallyBounded (Set.range (fun i => (huK i).toLp (u i))) := by
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal P := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hPQ.lt.le
  haveI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine totallyBounded_toLp_restrict_of_mollifiable hK hPQ hu huK hB (fun ε hε => ?_)
  obtain ⟨δ, hδ, hmod⟩ := hequi ε hε
  set φ : ContDiffBump (0 : ℝⁿ) := ⟨δ / 2, δ, by positivity, by linarith⟩ with hφ
  have hηcont : Continuous (φ.normed volume) := φ.continuous_normed
  have hηcs : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hsupp : ∀ y : ℝⁿ, φ.normed volume y ≠ 0 → ‖y‖ < δ := by
    intro y hy
    have hmem : y ∈ Function.support (φ.normed volume) := hy
    rw [φ.support_normed_eq] at hmem
    rwa [Metric.mem_ball, dist_zero_right] at hmem
  refine ⟨φ.normed volume, hηcont, hηcs, fun i => ?_, fun i => ?_⟩
  · -- the convolution is `Lᵖ` on the finite-measure restricted domain
    have hcont : Continuous (fun x => ∫ y, φ.normed volume (x - y) * u i y ∂volume) :=
      continuous_convolutionIntegral hηcont hηcs ((hu i).locallyIntegrable hP1)
    refine MemLp.of_bound hcont.aestronglyMeasurable.restrict
      ((eLpNorm (φ.normed volume) (ENNReal.ofReal Q) volume).toReal * B) ?_
    exact Eventually.of_forall fun x =>
      norm_convolutionIntegral_le_of_bound hηcont hηcs hPQ hu hB i x
  · -- the convolution is `ε`-close to `u i` in `Lᵖ(K, restrict)`
    refine le_trans (eLpNorm_restrict_le _ _ _ _) ?_
    exact eLpNorm_integral_convolution_sub_le_of_modulus hηcont hηcs φ.nonneg_normed
      φ.integral_normed hp (hup i) (fun y hy => hmod i y (hsupp y hy))

end Sobolev
