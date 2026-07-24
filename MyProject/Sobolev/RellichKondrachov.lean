import MyProject.Sobolev.FrechetKolmogorov
import MyProject.Sobolev.Mollification
import MyProject.Sobolev.Rellich

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

/-- **Rellich–Kondrachov (sufficient direction).**  A family of `C¹` functions with a **uniform
`Lᵖ` gradient bound** `‖Du i‖_p ≤ M` (and a uniform `L^P` bound) is **totally bounded in
`Lᵖ(K, restrict)`** on any compact `K`.  This is the compactness behind the embedding
`W^{1,p}(U) ↪↪ Lᵖ(U)`: the uniform equicontinuity required by Fréchet–Kolmogorov is supplied by the
translation/gradient estimate `eLpNorm_translate_sub_le_of_gradient_le` (whose modulus `‖h‖·M → 0`
is `tendsto_enorm_mul_nhds_zero`), and the criterion
`totallyBounded_toLp_restrict_of_equicontinuous` closes the argument. -/
theorem rellich_kondrachov {ι : Type*} {K : Set ℝⁿ} (hK : IsCompact K)
    {P Q : ℝ} (hPQ : P.HolderConjugate Q) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : ι → ℝⁿ → ℝ} (hcont : ∀ i, ContDiff ℝ 1 (u i))
    (hu : ∀ i, MemLp (u i) (ENNReal.ofReal P) volume) (hup : ∀ i, MemLp (u i) p volume)
    (huK : ∀ i, MemLp (u i) p (volume.restrict K))
    {B : ℝ} (hB : ∀ i, (eLpNorm (u i) (ENNReal.ofReal P) volume).toReal ≤ B)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hgrad : ∀ i, eLpNorm (fun x => fderiv ℝ (u i) x) p volume ≤ M) :
    TotallyBounded (Set.range (fun i => (huK i).toLp (u i))) := by
  refine totallyBounded_toLp_restrict_of_equicontinuous hK hPQ hp hu hup huK hB (fun ε hε => ?_)
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.mp
    (ENNReal.tendsto_nhds_zero.mp (tendsto_enorm_mul_nhds_zero (n := n) hM) (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.mpr hε))
  refine ⟨δ, hδ, fun i y hy => ?_⟩
  have htr := eLpNorm_translate_sub_le_of_gradient_le (hcont i) hp (hgrad i) (-y)
  rw [enorm_neg] at htr
  exact le_trans htr (hδball y (by rw [Metric.mem_ball, dist_zero_right]; exact hy))

/-- **Fréchet–Kolmogorov, necessary direction (equicontinuity).**  If a family `u : ι → ℝⁿ → ℝ`
of `Lᵖ` functions is **totally bounded in `Lᵖ(ℝⁿ)`** (its image under `toLp` is totally bounded),
then it is **uniformly `Lᵖ`-equicontinuous**: the translation modulus `‖u i(·−y) − u i‖_p` is
uniformly small once `‖y‖` is small.  This is the exact converse of the equicontinuity hypothesis
of `totallyBounded_toLp_restrict_of_equicontinuous`; together they characterise `Lᵖ`-precompactness
through translation equicontinuity.

The proof is the symmetric `ε/3` argument: pick a finite `ε/3`-net `t` of the (totally bounded)
image; each net point's representative is translation-continuous in `Lᵖ`
(`tendsto_eLpNorm_translate_sub`), so a single `δ` works for the whole finite net
(`Set.Finite.eventually_all`); and for any `i`, splitting `u i(·−y) − u i` through the nearby net
point `z` gives three terms — two are `‖u i − z‖_p < ε/3` (translation is an `Lᵖ` isometry) and the
middle is the net point's own modulus `< ε/3`. -/
theorem uniformEquicontinuous_translate_of_totallyBounded {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) {u : ι → ℝⁿ → ℝ} (hu : ∀ i, MemLp (u i) p volume)
    (htb : TotallyBounded (Set.range (fun i => (hu i).toLp (u i)))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ i, ∀ y : ℝⁿ, ‖y‖ < δ →
      eLpNorm (fun x => u i (x - y) - u i x) p volume ≤ ENNReal.ofReal ε := by
  intro ε hε
  set F : ι → Lp ℝ p volume := fun i => (hu i).toLp (u i) with hF
  -- an `ε/3`-net of the totally bounded image
  obtain ⟨t, hTfin, hcov⟩ := Metric.totallyBounded_iff.mp htb (ε / 3) (by positivity)
  have hofR3 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.mpr (by positivity)
  -- translation continuity of each net point, made uniform over the finite net
  have hev : ∀ᶠ s in 𝓝 (0 : ℝⁿ), ∀ z ∈ t,
      eLpNorm (fun x => ⇑z (x + s) - ⇑z x) p volume ≤ ENNReal.ofReal (ε / 3) := by
    rw [hTfin.eventually_all]
    intro z _
    exact ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_translate_sub hp (Lp.memLp z))
      (ENNReal.ofReal (ε / 3)) hofR3
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδpos, fun i y hy => ?_⟩
  -- a net point `z` within `ε/3` of `F i`
  obtain ⟨z, hz, hball⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_range_self i))
  have hzmem : MemLp (⇑z) p volume := Lp.memLp z
  have hcoe : ⇑(F i) =ᵐ[volume] u i := MemLp.coeFn_toLp (hu i)
  -- the translation `x ↦ x − y` preserves volume
  have mpτ : MeasurePreserving (fun x : ℝⁿ => x - y) volume volume := by
    have := measurePreserving_add_right (volume : Measure ℝⁿ) (-y)
    simpa [sub_eq_add_neg] using this
  -- measurability of the three pieces
  have hDsm : AEStronglyMeasurable (fun x => u i x - ⇑z x) volume :=
    (hu i).aestronglyMeasurable.sub hzmem.aestronglyMeasurable
  have hAsm : AEStronglyMeasurable (fun x => u i (x - y) - ⇑z (x - y)) volume := by
    have := hDsm.comp_measurePreserving mpτ
    simpa [Function.comp] using this
  have hzτ : AEStronglyMeasurable (fun x => ⇑z (x - y)) volume := by
    have := hzmem.aestronglyMeasurable.comp_measurePreserving mpτ
    simpa [Function.comp] using this
  have hBsm : AEStronglyMeasurable (fun x => ⇑z (x - y) - ⇑z x) volume :=
    hzτ.sub hzmem.aestronglyMeasurable
  have hCsm : AEStronglyMeasurable (fun x => ⇑z x - u i x) volume :=
    hzmem.aestronglyMeasurable.sub (hu i).aestronglyMeasurable
  -- the "net" term: `‖u i − z‖_p ≤ ε/3`
  have hN : eLpNorm (fun x => u i x - ⇑z x) p volume ≤ ENNReal.ofReal (ε / 3) := by
    have hae : (fun x => u i x - ⇑z x) =ᵐ[volume] (⇑(F i) - ⇑z) := by
      filter_upwards [hcoe] with x hx
      simp only [Pi.sub_apply]; rw [hx]
    rw [eLpNorm_congr_ae hae]
    have hne : eLpNorm (⇑(F i) - ⇑z) p volume ≠ ⊤ := by
      rw [← eLpNorm_congr_ae (Lp.coeFn_sub (F i) z)]; exact Lp.eLpNorm_ne_top (F i - z)
    rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity), ← Lp.dist_def]
    exact le_of_lt (Metric.mem_ball.mp hball)
  -- term A (isometry) and term C (reflection) both equal the net term
  have hA : eLpNorm (fun x => u i (x - y) - ⇑z (x - y)) p volume
      = eLpNorm (fun x => u i x - ⇑z x) p volume := by
    have h := eLpNorm_comp_measurePreserving (g := fun x => u i x - ⇑z x) (p := p) hDsm mpτ
    simpa [Function.comp] using h
  have hC : eLpNorm (fun x => ⇑z x - u i x) p volume
      = eLpNorm (fun x => u i x - ⇑z x) p volume := by
    rw [← eLpNorm_neg (fun x => u i x - ⇑z x) p volume]
    congr 1; funext x; simp only [Pi.neg_apply]; ring
  -- term B from the uniform net modulus, instantiated at `s = −y`
  have hB_le : eLpNorm (fun x => ⇑z (x - y) - ⇑z x) p volume ≤ ENNReal.ofReal (ε / 3) := by
    have hmem : (-y) ∈ Metric.ball (0 : ℝⁿ) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_neg]; exact hy
    have hb := hδ (-y) hmem z hz
    simpa only [← sub_eq_add_neg] using hb
  -- assemble via the triangle inequality
  have hsplit : (fun x => u i (x - y) - u i x)
      = (fun x => u i (x - y) - ⇑z (x - y)) + (fun x => ⇑z (x - y) - ⇑z x)
        + (fun x => ⇑z x - u i x) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hsplit]
  calc eLpNorm ((fun x => u i (x - y) - ⇑z (x - y)) + (fun x => ⇑z (x - y) - ⇑z x)
          + (fun x => ⇑z x - u i x)) p volume
      ≤ eLpNorm ((fun x => u i (x - y) - ⇑z (x - y)) + (fun x => ⇑z (x - y) - ⇑z x)) p volume
          + eLpNorm (fun x => ⇑z x - u i x) p volume :=
        eLpNorm_add_le (hAsm.add hBsm) hCsm Fact.out
    _ ≤ (eLpNorm (fun x => u i (x - y) - ⇑z (x - y)) p volume
          + eLpNorm (fun x => ⇑z (x - y) - ⇑z x) p volume)
          + eLpNorm (fun x => ⇑z x - u i x) p volume := by
        gcongr; exact eLpNorm_add_le hAsm hBsm Fact.out
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
        add_le_add (add_le_add (hA.trans_le hN) hB_le) (hC.trans_le hN)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **Tightness half of Fréchet–Kolmogorov** (the second half of the whole-space converse):
    a family totally bounded in `Lᵖ(ℝⁿ)` is uniformly tight at infinity — for every `ε`, a single
    finite-measure set `s` works for all `i`. With `uniformEquicontinuous_translate_of_totallyBounded`
    this is the full converse. Same `ε/2`-net argument. -/
theorem unifTight_of_totallyBounded {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {u : ι → ℝⁿ → ℝ} (hu : ∀ i, MemLp (u i) p volume)
    (htb : TotallyBounded (Set.range (fun i => (hu i).toLp (u i)))) :
    ∀ ε : ℝ, 0 < ε → ∃ s : Set ℝⁿ, MeasurableSet s ∧ volume s < ⊤ ∧ ∀ i,
      eLpNorm (sᶜ.indicator (u i)) p volume ≤ ENNReal.ofReal ε := by
  intro ε hε
  set F : ι → Lp ℝ p volume := fun i => (hu i).toLp (u i) with hF
  obtain ⟨t, hTfin, hcov⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (by positivity)
  have hε2ne : (ENNReal.ofReal (ε / 2)) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  choose s hsm hsμ hsε using
    fun z : Lp ℝ p (volume : Measure ℝⁿ) =>
      (Lp.memLp z).exists_eLpNorm_indicator_compl_lt hp hε2ne
  have hSmeas : MeasurableSet (⋃ z ∈ t, s z) :=
    MeasurableSet.biUnion hTfin.countable (fun z _ => hsm z)
  have hSfin : volume (⋃ z ∈ t, s z) < ⊤ := by
    apply measure_biUnion_lt_top hTfin
    intro z _
    exact hsμ z
  refine ⟨⋃ z ∈ t, s z, hSmeas, hSfin, fun i => ?_⟩
  set S : Set ℝⁿ := ⋃ z ∈ t, s z with hSdef
  obtain ⟨z, hz, hball⟩ := Set.mem_iUnion₂.mp (hcov (Set.mem_range_self i))
  have hzmem : MemLp (⇑z) p volume := Lp.memLp z
  have hcoe : ⇑(F i) =ᵐ[volume] u i := MemLp.coeFn_toLp (hu i)
  have hSsub : Sᶜ ⊆ (s z)ᶜ := Set.compl_subset_compl.mpr (Set.subset_biUnion_of_mem hz)
  have hScmeas : MeasurableSet (Sᶜ) := hSmeas.compl
  have hDsm : AEStronglyMeasurable (fun x => u i x - ⇑z x) volume :=
    (hu i).aestronglyMeasurable.sub hzmem.aestronglyMeasurable
  -- net term: `‖u i − z‖_p ≤ ε/2`
  have hN : eLpNorm (fun x => u i x - ⇑z x) p volume ≤ ENNReal.ofReal (ε / 2) := by
    have hae : (fun x => u i x - ⇑z x) =ᵐ[volume] (⇑(F i) - ⇑z) := by
      filter_upwards [hcoe] with x hx; simp only [Pi.sub_apply]; rw [hx]
    rw [eLpNorm_congr_ae hae]
    have hne : eLpNorm (⇑(F i) - ⇑z) p volume ≠ ⊤ := by
      rw [← eLpNorm_congr_ae (Lp.coeFn_sub (F i) z)]; exact Lp.eLpNorm_ne_top (F i - z)
    rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity), ← Lp.dist_def]
    exact le_of_lt (Metric.mem_ball.mp hball)
  calc eLpNorm (Sᶜ.indicator (u i)) p volume
      = eLpNorm (Sᶜ.indicator (fun x => u i x - ⇑z x) + Sᶜ.indicator (⇑z)) p volume := by
        congr 1
        funext x
        by_cases hx : x ∈ Sᶜ
        · simp only [Pi.add_apply, Set.indicator_of_mem hx]; ring
        · simp only [Pi.add_apply, Set.indicator_of_notMem hx, add_zero]
    _ ≤ eLpNorm (Sᶜ.indicator (fun x => u i x - ⇑z x)) p volume
          + eLpNorm (Sᶜ.indicator (⇑z)) p volume :=
        eLpNorm_add_le (hDsm.indicator hScmeas) (hzmem.aestronglyMeasurable.indicator hScmeas)
          Fact.out
    _ ≤ eLpNorm (fun x => u i x - ⇑z x) p volume + eLpNorm ((s z)ᶜ.indicator (⇑z)) p volume := by
        gcongr
        · exact eLpNorm_indicator_le _
        · refine eLpNorm_mono (fun x => ?_)
          by_cases hx : x ∈ Sᶜ
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hSsub hx)]
          · rw [Set.indicator_of_notMem hx, norm_zero]; positivity
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hN (le_of_lt (hsε z))
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end Sobolev
