import MyProject.Sobolev.Extension

/-!
# Sobolev extension operator (Evans §5.4) — the operator

Continues `MyProject.Sobolev.Extension` (the reflection and `evenRefl` foundations): the linear
change of variables, the boundary-density machinery, the **bounded half-space extension operator**
`exists_memW1p_extension_halfspace`, and the rigid-motion invariance lemmas toward the general
`C¹`-domain operator.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace ContDiff Topology ENNReal Convolution Manifold

namespace Sobolev

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- **Linear change of variables for weak derivatives.** For a linear isometry `L` of `ℝⁿ`, if `v`
is the weak `(L e)`-derivative of `u`, then `v ∘ L` is the weak `e`-derivative of `u ∘ L`.  This
generalizes `isWeakDerivInDir_comp_refll` (the reflection case) to an arbitrary linear isometry: the
substitution `x = L⁻¹ y`, which preserves Lebesgue measure, together with the chain rule
`∂_e(φ ∘ L⁻¹) = ∂_{L e}φ ∘ L⁻¹`, transports the weak-derivative identity through `L`. -/
theorem isWeakDerivInDir_comp_linear (L : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ) (e : ℝⁿ) {u v : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir Set.univ (L e) u v) :
    IsWeakDerivInDir Set.univ e (fun x => u (L x)) (fun x => v (L x)) := by
  intro φ hφ
  simp only []
  have hLmp : MeasurePreserving (L : ℝⁿ → ℝⁿ) volume volume := L.measurePreserving
  have hLme : MeasurableEmbedding (L : ℝⁿ → ℝⁿ) := L.toHomeomorph.measurableEmbedding
  have hinvsymm : ∀ x, L.symm (L x) = x := L.symm_apply_apply
  -- `ψ = φ ∘ L.symm` is a test function.
  have hψ : IsTestFunction Set.univ (fun z => φ (L.symm z)) :=
    ⟨hφ.contDiff.comp L.symm.toContinuousLinearEquiv.contDiff,
      hφ.hasCompactSupport.comp_homeomorph L.symm.toHomeomorph, Set.subset_univ _⟩
  -- Chain rule: `∂_e φ` at `L.symm y` equals `∂_{L e}ψ` at `y`.
  have hpt : ∀ y, fderiv ℝ φ (L.symm y) e
      = fderiv ℝ (fun z => φ (L.symm z)) y (L e) := by
    intro y
    have hcomp : HasFDerivAt (fun z => φ (L.symm z))
        ((fderiv ℝ φ (L.symm y)).comp
          (L.symm.toContinuousLinearEquiv : ℝⁿ →L[ℝ] ℝⁿ)) y :=
      (hφ.differentiable (L.symm y)).hasFDerivAt.comp y
        L.symm.toContinuousLinearEquiv.hasFDerivAt
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ φ (L.symm y) e = fderiv ℝ φ (L.symm y) (L.symm (L e))
    rw [hinvsymm e]
  -- Change variables `x = L.symm y` on both sides via measure-preservation of `L`.
  have hcovL : ∫ x, u (L x) * fderiv ℝ φ x e
      = ∫ y, u y * fderiv ℝ φ (L.symm y) e := by
    have key := hLmp.integral_comp hLme (fun y => u y * fderiv ℝ φ (L.symm y) e)
    simp only [hinvsymm] at key
    exact key
  have hcovR : ∫ x, v (L x) * φ x = ∫ y, v y * φ (L.symm y) := by
    have key := hLmp.integral_comp hLme (fun y => v y * φ (L.symm y))
    simp only [hinvsymm] at key
    exact key
  rw [hcovL,
    show (∫ y, u y * fderiv ℝ φ (L.symm y) e)
      = ∫ y, u y * fderiv ℝ (fun z => φ (L.symm z)) y (L e) from
      integral_congr_ae (Filter.Eventually.of_forall (fun y => by simp only [hpt y])),
    h _ hψ, ← hcovR]



/-- **`W^{1,p}(ℝⁿ)` is invariant under a coordinate reflection.** If `u ∈ W^{1,p}(ℝⁿ)` then so is
`u ∘ refll i`.  Assembled from the linear change of variables `isWeakDerivInDir_comp_linear`, the
direction-scaling `IsWeakDerivInDir.dir_smul` (since `refll` sends `eⱼ ↦ ±eⱼ`), and the
`refll`-invariance of the `Lᵖ` norm. -/
theorem MemW1p.comp_refll (i : Fin n) {p : ℝ≥0∞} {u : ℝⁿ → ℝ} (hu : MemW1p Set.univ p u) :
    MemW1p Set.univ p (fun x => u (refll i x)) := by
  have hmu : MemLp u p volume := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hu.memLp
  refine ⟨?_, fun j => ?_⟩
  · rw [Measure.restrict_univ]
    exact hmu.comp_measurePreserving (refll_measurePreserving i)
  · obtain ⟨vⱼ, hvⱼ, hvⱼLp⟩ := hu.exists_weakDeriv j
    have hmvj : MemLp vⱼ p volume := by
      rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hvⱼLp
    have hd : IsWeakDerivInDir Set.univ (refll i (EuclideanSpace.single j (1 : ℝ))) u
        (fun x => (if j = i then (-1 : ℝ) else 1) * vⱼ x) := by
      rw [refll_single]
      exact hvⱼ.dir_smul (if j = i then (-1 : ℝ) else 1)
    refine ⟨fun x => (if j = i then (-1 : ℝ) else 1) * vⱼ (refll i x), ?_, ?_⟩
    · exact isWeakDerivInDir_comp_linear (refll i) (EuclideanSpace.single j (1 : ℝ)) hd
    · rw [Measure.restrict_univ]
      exact (hmvj.comp_measurePreserving (refll_measurePreserving i)).const_mul _



/-- **Translation invariance of the weak derivative.** If `v` is the weak `e`-derivative of `u`,
then `v(· + t)` is the weak `e`-derivative of `u(· + t)`.  The affine analogue of
`isWeakDerivInDir_comp_linear`: translation is measure-preserving and its derivative is the
identity, so the direction is unchanged.  A building block for `Lᵖ`/`W^{1,p}` translation-continuity
(the boundary-density argument for the half-space extension). -/
theorem isWeakDerivInDir_comp_translate (t : ℝⁿ) (e : ℝⁿ) {u v : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir Set.univ e u v) :
    IsWeakDerivInDir Set.univ e (fun x => u (x + t)) (fun x => v (x + t)) := by
  intro φ hφ
  simp only []
  have hmp : MeasurePreserving (fun x : ℝⁿ => x + t) volume volume :=
    measurePreserving_add_right volume t
  have hme : MeasurableEmbedding (fun x : ℝⁿ => x + t) :=
    (Homeomorph.addRight t).measurableEmbedding
  -- `ψ = φ(· - t)` is a test function.
  have hψ : IsTestFunction Set.univ (fun z => φ (z - t)) :=
    ⟨hφ.contDiff.comp ((contDiff_id).sub contDiff_const),
      hφ.hasCompactSupport.comp_homeomorph (Homeomorph.subRight t), Set.subset_univ _⟩
  -- Chain rule: `∂_e φ` at `y - t` equals `∂_e ψ` at `y` (translation derivative is the identity).
  have hpt : ∀ y, fderiv ℝ φ (y - t) e = fderiv ℝ (fun z => φ (z - t)) y e := by
    intro y
    have hcomp : HasFDerivAt (fun z => φ (z - t)) (fderiv ℝ φ (y - t)) y := by
      have := (hφ.differentiable (y - t)).hasFDerivAt.comp y
        ((hasFDerivAt_id y).sub_const t)
      simpa using this
    rw [hcomp.fderiv]
  -- Change variables `x = y - t` on both sides via measure-preservation of translation.
  have hcovL : ∫ x, u (x + t) * fderiv ℝ φ x e = ∫ y, u y * fderiv ℝ φ (y - t) e := by
    have key := hmp.integral_comp hme (fun y => u y * fderiv ℝ φ (y - t) e)
    simp only [add_sub_cancel_right] at key
    exact key
  have hcovR : ∫ x, v (x + t) * φ x = ∫ y, v y * φ (y - t) := by
    have key := hmp.integral_comp hme (fun y => v y * φ (y - t))
    simp only [add_sub_cancel_right] at key
    exact key
  rw [hcovL,
    show (∫ y, u y * fderiv ℝ φ (y - t) e)
      = ∫ y, u y * fderiv ℝ (fun z => φ (z - t)) y e from
      integral_congr_ae (Filter.Eventually.of_forall (fun y => by simp only [hpt y])),
    h _ hψ, ← hcovR]




/-- **`W^{1,p}(ℝⁿ)` is invariant under translation.** -/
theorem MemW1p.comp_translate (t : ℝⁿ) {p : ℝ≥0∞} {u : ℝⁿ → ℝ} (hu : MemW1p Set.univ p u) :
    MemW1p Set.univ p (fun x => u (x + t)) := by
  have hmu : MemLp u p volume := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hu.memLp
  refine ⟨?_, fun j => ?_⟩
  · rw [Measure.restrict_univ]
    exact hmu.comp_measurePreserving (measurePreserving_add_right volume t)
  · obtain ⟨vⱼ, hvⱼ, hvⱼLp⟩ := hu.exists_weakDeriv j
    have hmvj : MemLp vⱼ p volume := by
      rw [← Measure.restrict_univ (μ := (volume : Measure ℝⁿ))]; exact hvⱼLp
    refine ⟨fun x => vⱼ (x + t),
      isWeakDerivInDir_comp_translate t (EuclideanSpace.single j (1 : ℝ)) hvⱼ, ?_⟩
    rw [Measure.restrict_univ]
    exact hmvj.comp_measurePreserving (measurePreserving_add_right volume t)

/-- **Translation is continuous in `W^{1,p}`** (`1 ≤ p < ∞`): as `t → 0`, both `u(· + t) → u` and
each weak derivative `vⱼ(· + t) → vⱼ` in `Lᵖ`, so the total `W^{1,p}`-seminorm error → `0`.  The
engine of the boundary-density argument for the half-space extension; it bundles the `Lᵖ`
translation-continuity `tendsto_eLpNorm_translate_sub` over `u` and all `n` derivatives. -/
theorem tendsto_eLpNorm_translate_memW1p {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p volume) (hv : ∀ j, MemLp (v j) p volume) :
    Tendsto (fun t : ℝⁿ => eLpNorm (fun x => u (x + t) - u x) p volume
        + ∑ j, eLpNorm (fun x => v j (x + t) - v j x) p volume) (𝓝 0) (𝓝 0) := by
  have hfunc : Tendsto (fun t : ℝⁿ => eLpNorm (fun x => u (x + t) - u x) p volume) (𝓝 0) (𝓝 0) :=
    tendsto_eLpNorm_translate_sub hp hu
  have hsum : Tendsto (fun t : ℝⁿ => ∑ j, eLpNorm (fun x => v j (x + t) - v j x) p volume)
      (𝓝 0) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun j _ => tendsto_eLpNorm_translate_sub hp (hv j))
    simpa using this
  simpa using hfunc.add hsum

/-- **Restricted `Lᵖ` translation-continuity toward the boundary.** For `u ∈ Lᵖ({xᵢ > 0})`, shifting
into the interior along `+eᵢ` converges in `Lᵖ({xᵢ > 0})`: `‖u(· + s·eᵢ) − u‖_{Lᵖ({xᵢ>0})} → 0` as
`s ↓ 0`.  Proved by extending `u` by `0` to `ℝⁿ` (`= S.indicator u ∈ Lᵖ(ℝⁿ)`), applying the
whole-space translation-continuity, and squeezing (the restricted norm is `≤` the whole-space one,
and on `{xᵢ>0}` the shift `s > 0` keeps the argument inside `{xᵢ>0}` where the extension equals `u`).
The boundary-density engine for the half-space extension. -/
theorem tendsto_eLpNorm_translate_sub_restrict_pos (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i})) :
    Tendsto (fun s : ℝ => eLpNorm (fun x => u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x) p
      (volume.restrict {x : ℝⁿ | 0 < x i})) (𝓝[>] 0) (𝓝 0) := by
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  set S : Set ℝⁿ := {x : ℝⁿ | 0 < x i} with hS
  have hũ : MemLp (S.indicator u) p volume := (memLp_indicator_iff_restrict hmsGt).2 hu
  -- coordinate fact: for `x i > 0` and `s > 0`, `(x + s • eᵢ) ∈ S`.
  have hmem : ∀ {x : ℝⁿ} {s : ℝ}, 0 < x i → 0 < s → x + s • EuclideanSpace.single i (1 : ℝ) ∈ S := by
    intro x s hx hs
    have hcoord : (x + s • EuclideanSpace.single i (1 : ℝ)) i = x i + s := by
      simp [PiLp.add_apply, PiLp.smul_apply]
    simp only [hS, Set.mem_setOf_eq, hcoord]
    linarith
  -- whole-space translation-continuity for the extension, composed with `s ↦ s • eᵢ`.
  have hwhole : Tendsto (fun s : ℝ => eLpNorm
      (fun x => S.indicator u (x + s • EuclideanSpace.single i (1 : ℝ)) - S.indicator u x) p volume)
      (𝓝 0) (𝓝 0) := by
    have h2 : Tendsto (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun s : ℝ => s • EuclideanSpace.single i (1 : ℝ)) :=
        continuous_id.smul continuous_const
      simpa only [zero_smul] using hc.tendsto 0
    exact (tendsto_eLpNorm_translate_sub hp hũ).comp h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hwhole.mono_left nhdsWithin_le_nhds)
    (Filter.Eventually.of_forall (fun s => zero_le _)) ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : (0 : ℝ) < s)
  have hcongr : eLpNorm (fun x => u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x) p
        (volume.restrict S)
      = eLpNorm (fun x => S.indicator u (x + s • EuclideanSpace.single i (1 : ℝ))
        - S.indicator u x) p (volume.restrict S) := by
    refine eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2 (Filter.Eventually.of_forall
      (fun x (hx : 0 < x i) => ?_)))
    show u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x
        = S.indicator u (x + s • EuclideanSpace.single i (1 : ℝ)) - S.indicator u x
    rw [Set.indicator_of_mem (hmem hx hs), Set.indicator_of_mem (show x ∈ S from hx)]
  rw [hcongr]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- **Restricted `W^{1,p}` translation-continuity toward the boundary.**  Packaging
`tendsto_eLpNorm_translate_sub_restrict_pos` over the function together with each of its weak-gradient
components: as the inward shift `s ↓ 0`, the full `W^{1,p}({xᵢ>0})` translation increment
`‖u(·+s·eᵢ)−u‖ + ∑ⱼ‖vⱼ(·+s·eᵢ)−vⱼ‖` tends to `0`.  This is the translation half of the
mollification-up-to-the-boundary density for the half-space, mirroring the whole-space
`tendsto_eLpNorm_translate_memW1p`. -/
theorem tendsto_eLpNorm_translate_restrict_memW1p (i : Fin n) {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hv : ∀ j, MemLp (v j) p (volume.restrict {x : ℝⁿ | 0 < x i})) :
    Tendsto (fun s : ℝ =>
        eLpNorm (fun x => u (x + s • EuclideanSpace.single i (1 : ℝ)) - u x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})
        + ∑ j, eLpNorm (fun x => v j (x + s • EuclideanSpace.single i (1 : ℝ)) - v j x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})) (𝓝[>] 0) (𝓝 0) := by
  have hfunc := tendsto_eLpNorm_translate_sub_restrict_pos i hp hu
  have hsum : Tendsto (fun s : ℝ => ∑ j, eLpNorm
      (fun x => v j (x + s • EuclideanSpace.single i (1 : ℝ)) - v j x) p
      (volume.restrict {x : ℝⁿ | 0 < x i})) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun j _ => tendsto_eLpNorm_translate_sub_restrict_pos i hp (hv j))
    simpa using this
  simpa using hfunc.add hsum

/-- **Restricted `Lᵖ` mollification error.**  For `u ∈ Lᵖ(ℝⁿ)` and any set `S`, the mollification
error measured on `S` vanishes: `‖ρ_η ⋆ u − u‖_{Lᵖ(S)} → 0` as the mollifier radius `→ 0`.  Immediate
from the whole-space error `tendsto_eLpNorm_convolution_sub` by the monotonicity of `eLpNorm` under
`volume.restrict S ≤ volume`.  This supplies the `Lᵖ` half of the mollification-up-to-the-boundary
density on `S = {xᵢ>0}`. -/
theorem tendsto_eLpNorm_convolution_sub_restrict {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p volume) (S : Set ℝⁿ) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝⁿ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p
        (volume.restrict S)) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_eLpNorm_convolution_sub hp hu hφ)
    (Filter.Eventually.of_forall fun _ => zero_le _)
    (Filter.Eventually.of_forall fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- **Localized commutation identity: the derivative passes through the convolution onto a
weak derivative valid only on an open set `U`.**  The whole-space `convolution_deriv_eq` needs
`IsWeakDerivInDir univ e u v`; but the reflected mollifier `z ↦ η(x−z)` used to prove it is a test
function supported in `x − supp η`, so the identity `(∂ₑη) ⋆ u = η ⋆ v` at the point `x` needs only
that this support sits inside the set where `u` genuinely has its weak derivative.  This is the tool
that lets the mollification of an *inward-shifted* half-space function sample only the interior
`{xᵢ>0}` — the gradient half of the boundary density.  Proof is the whole-space one with the single
change `subset_univ _ ↦ hUsupp`. -/
lemma convolution_deriv_eq_of_subset {η : ℝⁿ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηsupp : HasCompactSupport η) {U : Set ℝⁿ} {u v : ℝⁿ → ℝ} (e : ℝⁿ)
    (hweak : IsWeakDerivInDir U e u v) (x : ℝⁿ) (hUsupp : tsupport (fun z => η (x - z)) ⊆ U) :
    ((fun z => fderiv ℝ η z e) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x
      = (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) x := by
  set φ : ℝⁿ → ℝ := fun z => η (x - z) with hφdef
  have hφ_cd : ContDiff ℝ ∞ φ := hη.comp (contDiff_const.sub contDiff_id)
  have hφ_cs : HasCompactSupport φ := hηsupp.comp_homeomorph (Homeomorph.subLeft x)
  have hφ_test : IsTestFunction U φ := ⟨hφ_cd, hφ_cs, hUsupp⟩
  have hchain : ∀ z, fderiv ℝ φ z e = - fderiv ℝ η (x - z) e := by
    intro z
    have hg : HasFDerivAt (fun z : ℝⁿ => x - z) (-ContinuousLinearMap.id ℝ ℝⁿ) z :=
      (hasFDerivAt_id z).const_sub x
    have hηd : HasFDerivAt η (fderiv ℝ η (x - z)) (x - z) :=
      (hη.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt φ ((fderiv ℝ η (x - z)).comp (-ContinuousLinearMap.id ℝ ℝⁿ)) z :=
      hηd.comp z hg
    rw [hcomp.fderiv]
    simp
  rw [convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hw := hweak φ hφ_test
  calc ∫ t, fderiv ℝ η (x - t) e * u t ∂volume
      = ∫ t, u t * fderiv ℝ η (x - t) e ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
    _ = -∫ t, u t * fderiv ℝ φ t e ∂volume := by
        simp_rw [hchain, mul_neg, integral_neg, neg_neg]
    _ = - -∫ t, v t * φ t ∂volume := by rw [hw]
    _ = ∫ t, η (x - t) * v t ∂volume := by
        rw [neg_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        change v t * φ t = η (x - t) * v t
        simp only [hφdef]; ring

/-- **The weak-derivative relation depends only on the values on `U`.**  A test function for `U` is
supported inside `U`, so the defining identity `∫ u·∂ₑφ = −∫ v·φ` only samples `u, v` on `U`.  Hence
if `u', v'` agree with `u, v` throughout `U`, they inherit the same weak derivative on `U`.  This lets
the zero-extension `ũ = 1_{xᵢ>0}·u` carry `u`'s weak derivative on the open half-space `{xᵢ>0}`. -/
lemma IsWeakDerivInDir.congr_eqOn {U : Set ℝⁿ} {e : ℝⁿ} {u v u' v' : ℝⁿ → ℝ}
    (h : IsWeakDerivInDir U e u v) (hu : Set.EqOn u' u U) (hv : Set.EqOn v' v U) :
    IsWeakDerivInDir U e u' v' := by
  intro φ hφ
  -- outside `tsupport φ ⊆ U` both `φ` and `∂ₑφ` vanish
  have hfd0 : ∀ x, x ∉ tsupport φ → fderiv ℝ φ x e = 0 := by
    intro x hx
    have hev : φ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    simp [hev.fderiv_eq]
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 :=
    fun x hx => (notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds
  have hL : ∫ x, u' x * fderiv ℝ φ x e = ∫ x, u x * fderiv ℝ φ x e := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u' x * fderiv ℝ φ x e = u x * fderiv ℝ φ x e
    by_cases hx : x ∈ tsupport φ
    · rw [hu (hφ.2.2 hx)]
    · rw [hfd0 x hx, mul_zero, mul_zero]
  have hR : ∫ x, v' x * φ x = ∫ x, v x * φ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show v' x * φ x = v x * φ x
    by_cases hx : x ∈ tsupport φ
    · rw [hv (hφ.2.2 hx)]
    · rw [hφ0 x hx, mul_zero, mul_zero]
  rw [hL, hR]; exact h φ hφ

/-- **Directional derivative of a smooth-left convolution, in scalar form.**  For `ρ` smooth with
compact support and `u` locally integrable, the classical directional derivative of `ρ ⋆ u`
distributes onto `ρ`: `∂ₑ(ρ ⋆ u) = (∂ₑρ) ⋆ u`.  This is Mathlib's
`HasCompactSupport.hasFDerivAt_convolution_left` (which yields the total derivative in the
`precompL` bundled form) evaluated at `e` and pushed through the Bochner integral
(`ContinuousLinearMap.integral_apply` + `precompL_apply`).  It converts the classical gradient of the
mollification into the left-handed scalar convolution `(∂ₑρ)⋆u` that `convolution_deriv_eq_of_subset`
consumes. -/
lemma fderiv_convolution_apply {ρ u : ℝⁿ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : HasCompactSupport ρ) (hu : LocallyIntegrable u volume) (x e : ℝⁿ) :
    fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x e
      = ((fun z => fderiv ℝ ρ z e) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have hfd : HasFDerivAt (ρ ⋆[L, volume] u)
      ((fderiv ℝ ρ ⋆[L.precompL ℝⁿ, volume] u) x) x :=
    hρsupp.hasFDerivAt_convolution_left L hρ1 hu x
  have hex : ConvolutionExistsAt (fderiv ℝ ρ) u x (L.precompL ℝⁿ) volume :=
    (hρsupp.fderiv ℝ).convolutionExists_left (L.precompL ℝⁿ)
      (hρ1.continuous_fderiv one_ne_zero) hu x
  rw [hfd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex]
  simp only [ContinuousLinearMap.precompL_apply]
  rw [convolution_def]

/-- **The inward-shifted mollifier samples only the interior.**  If `ρ`'s support lies in the ball of
radius `r` and the base point `x'` has `i`-th coordinate exceeding `r`, then the reflected bump
`z ↦ ρ(x'−z)` (the kernel of a convolution evaluated at `x'`) is supported entirely inside the open
half-space `{xᵢ>0}`.  This is the geometric heart of the mollification-up-to-the-boundary: after an
inward shift `s > η` the sample point `x' = x + s·eᵢ` has `x'ᵢ ≥ s > η = r`, so the whole convolution
kernel stays in `{xᵢ>0}` where the datum is genuinely Sobolev — the hypothesis
`convolution_deriv_eq_of_subset` and `IsWeakDerivInDir.congr_eqOn` need. -/
lemma tsupport_comp_sub_subset_pos {ρ : ℝⁿ → ℝ} {r : ℝ} {i : Fin n}
    (hρ : tsupport ρ ⊆ Metric.closedBall 0 r) {x' : ℝⁿ} (hx' : r < x' i) :
    tsupport (fun z => ρ (x' - z)) ⊆ {x : ℝⁿ | 0 < x i} := by
  have hcoord : ∀ w : ℝⁿ, |w i| ≤ ‖w‖ := by
    intro w
    rw [EuclideanSpace.norm_eq]
    have hle : ‖w i‖ ≤ Real.sqrt (∑ j, ‖w j‖ ^ 2) := by
      rw [show ‖w i‖ = Real.sqrt (‖w i‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt
        (Finset.single_le_sum (fun j _ => sq_nonneg ‖w j‖) (Finset.mem_univ i))
    simpa [Real.norm_eq_abs] using hle
  have hsub : tsupport (fun z => ρ (x' - z)) ⊆ (fun z => x' - z) ⁻¹' (tsupport ρ) := by
    apply closure_minimal
    · intro z hz
      have hz' : x' - z ∈ Function.support ρ := hz
      exact subset_tsupport ρ hz'
    · exact (isClosed_tsupport ρ).preimage (continuous_const.sub continuous_id)
  intro z hz
  have hball : ‖x' - z‖ ≤ r := by
    have := hρ (hsub hz); simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have h1 : |x' i - z i| ≤ r := by
    have h2 : (x' - z) i = x' i - z i := by simp [PiLp.sub_apply]
    have := le_trans (hcoord (x' - z)) hball; rwa [h2] at this
  simp only [Set.mem_setOf_eq]
  have := abs_le.mp h1
  linarith [this.1, this.2]

/-- **Function-part of the boundary density.**  With `ũ = 1_{xᵢ>0}·u` the zero-extension, the
mollified inward-shift `x ↦ (ρ_k ⋆ ũ)(x + s_k·eᵢ)` converges to `u` in `Lᵖ({xᵢ>0})` as the mollifier
radius and shift `→ 0`.  The increment telescopes as `[(ρ_k⋆ũ − ũ)(·+s_k eᵢ)]` (mollification error,
`→0` by the whole-space error `tendsto_eLpNorm_convolution_sub` + translation-invariance of the whole
`Lᵖ` norm) `+ [ũ(·+s_k eᵢ) − u]` (`=ᵐ u(·+s_k eᵢ)−u` on `{xᵢ>0}`, `→0` by
`tendsto_eLpNorm_translate_sub_restrict_pos`). -/
theorem tendsto_eLpNorm_mollify_shift_sub_restrict (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    {φ : ℕ → ContDiffBump (0 : ℝⁿ)} (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))
    {s : ℕ → ℝ} (hs0 : ∀ k, 0 < s k) (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x =>
      ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} u) (x + s k • EuclideanSpace.single i (1 : ℝ))
        - u x) p (volume.restrict {x : ℝⁿ | 0 < x i})) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  set S : Set ℝⁿ := {x : ℝⁿ | 0 < x i} with hS
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hLdef
  set ũ : ℝⁿ → ℝ := S.indicator u with hũdef
  have hũLp : MemLp ũ p volume := (memLp_indicator_iff_restrict hmsGt).2 hu
  have hũLI : LocallyIntegrable ũ volume := hũLp.locallyIntegrable hp1
  set g : ℕ → ℝⁿ → ℝ := fun k => (φ k).normed volume ⋆[L, volume] ũ with hgdef
  have hg_cont : ∀ k, Continuous (g k) := fun k =>
    (φ k).hasCompactSupport_normed.continuous_convolution_left L
      ((φ k).contDiff_normed (n := 1)).continuous hũLI
  have hmem : ∀ {x : ℝⁿ} {t : ℝ}, 0 < x i → 0 < t →
      x + t • EuclideanSpace.single i (1 : ℝ) ∈ S := by
    intro x t hx ht
    have hc : (x + t • EuclideanSpace.single i (1 : ℝ)) i = x i + t := by
      simp [PiLp.add_apply, PiLp.smul_apply]
    simp only [hS, Set.mem_setOf_eq, hc]; linarith
  -- aesm helpers (w.r.t. `volume.restrict S`)
  have haesm_g : ∀ (k : ℕ) (t : ℝ), AEStronglyMeasurable (fun x =>
      g k (x + t • EuclideanSpace.single i (1 : ℝ))) (volume.restrict S) := fun k t =>
    ((hg_cont k).comp (continuous_id.add continuous_const)).aestronglyMeasurable.restrict
  have haesm_ũ : ∀ (t : ℝ), AEStronglyMeasurable (fun x =>
      ũ (x + t • EuclideanSpace.single i (1 : ℝ))) (volume.restrict S) := fun t =>
    (hũLp.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume _).quasiMeasurePreserving).restrict
  have haesm_u : AEStronglyMeasurable u (volume.restrict S) := hu.aestronglyMeasurable
  set A : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun x =>
      g k (x + s k • EuclideanSpace.single i (1 : ℝ))
        - ũ (x + s k • EuclideanSpace.single i (1 : ℝ))) p (volume.restrict S) with hAdef
  set B : ℕ → ℝ≥0∞ := fun k => eLpNorm (fun x =>
      ũ (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x) p (volume.restrict S) with hBdef
  have hA : Tendsto A atTop (𝓝 0) := by
    have hconv : Tendsto (fun k => eLpNorm (fun x => g k x - ũ x) p volume) atTop (𝓝 0) :=
      tendsto_eLpNorm_convolution_sub hp hũLp hφ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hconv
      (Eventually.of_forall fun k => zero_le _) (Eventually.of_forall fun k => ?_)
    have haesm : AEStronglyMeasurable (fun x => g k x - ũ x) volume :=
      (hg_cont k).aestronglyMeasurable.sub hũLp.aestronglyMeasurable
    have htrans : eLpNorm (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ))
          - ũ (x + s k • EuclideanSpace.single i (1 : ℝ))) p volume
        = eLpNorm (fun x => g k x - ũ x) p volume := by
      have := eLpNorm_comp_measurePreserving (p := p) (g := fun x => g k x - ũ x)
        haesm (measurePreserving_add_right volume (s k • EuclideanSpace.single i (1 : ℝ)))
      simpa [Function.comp] using this
    calc A k ≤ eLpNorm (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ))
              - ũ (x + s k • EuclideanSpace.single i (1 : ℝ))) p volume :=
            eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (fun x => g k x - ũ x) p volume := htrans
  have hB : Tendsto B atTop (𝓝 0) := by
    have hBeq : B = fun k => eLpNorm (fun x =>
        u (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x) p (volume.restrict S) := by
      funext k
      refine eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2 (Eventually.of_forall
        (fun x (hx : 0 < x i) => ?_)))
      show ũ (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x
          = u (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x
      rw [hũdef, Set.indicator_of_mem (hmem hx (hs0 k))]
    rw [hBeq]
    exact (tendsto_eLpNorm_translate_sub_restrict_pos i hp hu).comp
      (tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hs0⟩)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using hA.add hB) (Eventually.of_forall fun k => zero_le _)
    (Eventually.of_forall fun k => ?_)
  have hsplit : (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x)
      = (fun x => g k (x + s k • EuclideanSpace.single i (1 : ℝ))
            - ũ (x + s k • EuclideanSpace.single i (1 : ℝ)))
        + (fun x => ũ (x + s k • EuclideanSpace.single i (1 : ℝ)) - u x) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [hsplit]
  exact eLpNorm_add_le ((haesm_g k (s k)).sub (haesm_ũ (s k)))
    ((haesm_ũ (s k)).sub haesm_u) hp1

/-- **Gradient identity for the mollified inward-shift.**  On the interior `{xᵢ>0}`, the classical
directional derivative of `y ↦ (ρ ⋆ ũ)(y + t·eᵢ)` (with `ũ = 1_{xᵢ>0}·u`) equals `(ρ ⋆ ṽⱼ)(·+t·eᵢ)`
with `ṽⱼ = 1_{xᵢ>0}·vⱼ` the zero-extension of the weak derivative.  Chains the chain rule,
`fderiv_convolution_apply` (`∂ⱼ(ρ⋆ũ) = (∂ⱼρ)⋆ũ`), and `convolution_deriv_eq_of_subset`
(`(∂ⱼρ)⋆ũ = ρ⋆ṽⱼ` since the inward shift `t > ψ.rOut` keeps the kernel support inside `{xᵢ>0}`, where
`ũ`, `ṽⱼ` carry `u`'s weak derivative by `congr_eqOn`).  This makes the gradient-part of the density
a corollary of the function-part applied to `vⱼ`. -/
lemma fderiv_mollify_shift_apply_of_pos (i j : Fin n) {u vj : ℝⁿ → ℝ}
    (hweak : IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) u vj)
    (huLI : LocallyIntegrable (Set.indicator {x : ℝⁿ | 0 < x i} u) volume)
    (ψ : ContDiffBump (0 : ℝⁿ)) {t : ℝ} (ht : ψ.rOut < t) {x : ℝⁿ} (hx : 0 < x i) :
    fderiv ℝ (fun y => (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator {x : ℝⁿ | 0 < x i} u) (y + t • EuclideanSpace.single i (1 : ℝ)))
        x (EuclideanSpace.single j (1 : ℝ))
      = (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} vj) (x + t • EuclideanSpace.single i (1 : ℝ)) := by
  set S : Set ℝⁿ := {x : ℝⁿ | 0 < x i} with hS
  set ρ : ℝⁿ → ℝ := ψ.normed volume with hρdef
  set c : ℝⁿ := t • EuclideanSpace.single i (1 : ℝ) with hcdef
  have hρcd : ContDiff ℝ ∞ ρ := ψ.contDiff_normed
  have hρsupp : HasCompactSupport ρ := ψ.hasCompactSupport_normed
  have hgcd : ContDiff ℝ ∞ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) :=
    hρsupp.contDiff_convolution_left _ hρcd huLI
  have hchain : fderiv ℝ (fun y => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (y + c))
        x (EuclideanSpace.single j (1 : ℝ))
      = fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (x + c)
        (EuclideanSpace.single j (1 : ℝ)) := by
    have h1 : HasFDerivAt (fun y : ℝⁿ => y + c) (ContinuousLinearMap.id ℝ ℝⁿ) x := by
      simpa using (hasFDerivAt_id x).add_const c
    have h2 : HasFDerivAt (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u)
        (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (x + c)) (x + c) :=
      (hgcd.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hcomp : HasFDerivAt
        (fun y => (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (y + c))
        (fderiv ℝ (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] S.indicator u) (x + c)) x := by
      simpa [Function.comp_def] using h2.comp x h1
    rw [hcomp.fderiv]
  rw [hchain, fderiv_convolution_apply hρcd hρsupp huLI]
  refine convolution_deriv_eq_of_subset (U := S) hρcd hρsupp (EuclideanSpace.single j (1 : ℝ))
    ?_ (x + c) ?_
  · exact hweak.congr_eqOn (fun y hy => Set.indicator_of_mem hy u)
      (fun y hy => Set.indicator_of_mem hy vj)
  · refine tsupport_comp_sub_subset_pos (r := ψ.rOut) ?_ ?_
    · rw [hρdef, tsupport, ψ.support_normed_eq]
      exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    · have hc : (x + c) i = x i + t := by rw [hcdef]; simp [PiLp.add_apply, PiLp.smul_apply]
      rw [hc]; linarith

/-- **`Lᵖ`-membership of a mollification.**  For a mollifier `η` (smooth, compact support, nonneg,
`∫η = 1`) and `f ∈ Lᵖ(ℝⁿ)`, the convolution `η ⋆ f` lies in `Lᵖ`.  Mathlib has no convolution Young
inequality, so this is obtained by triangle inequality from the project's own convolution-error bound:
`MemLp(η⋆f) = MemLp((η⋆f − f) + f)`, and `η⋆f − f ∈ Lᵖ` because `eLpNorm_convolution_sub_rpow_le`
bounds its `p`-th power by `∫η(y)·‖f(·−y)−f‖ₚ^p ≤ (2‖f‖ₚ)^p < ∞`. -/
theorem memLp_convolution {η : ℝⁿ → ℝ} (hη_cd : ContDiff ℝ ∞ η) (hη_supp : HasCompactSupport η)
    (hη_nonneg : ∀ y, 0 ≤ η y) (hη_int : ∫ y, η y = 1) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemLp u p volume) :
    MemLp (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) p volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hP0 : 0 < p.toReal := by
    have h0 : (0 : ℝ) < (1 : ℝ≥0∞).toReal := by simp
    exact h0.trans_le (ENNReal.toReal_mono hp hp1)
  have hη_cont : Continuous η := hη_cd.continuous
  have hu_li : LocallyIntegrable u volume := hu.locallyIntegrable hp1
  have hcont : Continuous (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) :=
    hη_supp.continuous_convolution_left _ hη_cont hu_li
  have hw_meas : AEMeasurable (fun y => ENNReal.ofReal (η y)) volume :=
    (ENNReal.measurable_ofReal.comp hη_cont.measurable).aemeasurable
  have hw1 : ∫⁻ y, ENNReal.ofReal (η y) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hη_cont.integrable_of_hasCompactSupport hη_supp)
      (Filter.Eventually.of_forall hη_nonneg), hη_int, ENNReal.ofReal_one]
  have hCle : ∀ y : ℝⁿ, eLpNorm (fun x => u (x - y) - u x) p volume ≤ 2 * eLpNorm u p volume := by
    intro y
    have hmp : MeasurePreserving (fun x : ℝⁿ => x - y) volume volume :=
      measurePreserving_sub_right volume y
    have h1 : eLpNorm (fun x => u (x - y)) p volume = eLpNorm u p volume :=
      eLpNorm_comp_measurePreserving hu.aestronglyMeasurable hmp
    calc eLpNorm (fun x => u (x - y) - u x) p volume
        ≤ eLpNorm (fun x => u (x - y)) p volume + eLpNorm u p volume :=
          eLpNorm_sub_le (hu.aestronglyMeasurable.comp_measurePreserving hmp)
            hu.aestronglyMeasurable hp1
      _ = 2 * eLpNorm u p volume := by rw [h1, two_mul]
  have hCfin : (2 * eLpNorm u p volume) ^ p.toReal ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg hP0.le
      (ENNReal.mul_lt_top (by norm_num) hu.2).ne).ne
  have hfin : eLpNorm (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p volume
      < ⊤ := by
    have hkey := eLpNorm_convolution_sub_rpow_le hη_cont hη_supp hη_nonneg hη_int hp hu
    have hRHS : ∫⁻ y, ENNReal.ofReal (η y)
          * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume
        ≤ (2 * eLpNorm u p volume) ^ p.toReal := by
      calc ∫⁻ y, ENNReal.ofReal (η y)
            * (eLpNorm (fun x => u (x - y) - u x) p volume) ^ p.toReal ∂volume
          ≤ ∫⁻ _y, ENNReal.ofReal (η _y) * (2 * eLpNorm u p volume) ^ p.toReal ∂volume := by
            refine lintegral_mono fun y => ?_
            gcongr
            exact hCle y
        _ = (2 * eLpNorm u p volume) ^ p.toReal * ∫⁻ y, ENNReal.ofReal (η y) ∂volume := by
            simp_rw [mul_comm (ENNReal.ofReal _)]
            rw [lintegral_const_mul'' _ hw_meas]
        _ = (2 * eLpNorm u p volume) ^ p.toReal := by rw [hw1, mul_one]
    have hlt : (eLpNorm (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p volume)
        ^ p.toReal < ⊤ := lt_of_le_of_lt (hkey.trans hRHS) hCfin.lt_top
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_rpow_of_pos hP0] at hlt
    exact lt_irrefl _ hlt
  have hsub : MemLp (fun x => (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) p volume :=
    ⟨hcont.aestronglyMeasurable.sub hu.aestronglyMeasurable, hfin⟩
  have heq : (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u)
      = fun x => ((η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x - u x) + u x := by
    funext x; ring
  rw [heq]
  exact hsub.add hu

/-- **Boundary density for the half-space (sequence form).**  A `W^{1,p}(\{xᵢ>0\})` function `u` with
weak derivatives `v` is approximated in `W^{1,p}(\{xᵢ>0\})` by a sequence of `C^∞` functions
`wₖ = (ρ_k ⋆ ũ)(·+sₖ·eᵢ)` (mollified inward-shifts, `ũ = 1_{xᵢ>0}·u`): both `‖u−wₖ‖_{Lᵖ} → 0` and,
for every `j`, `‖vⱼ − ∂ⱼwₖ‖_{Lᵖ} → 0`.  Assembles the function-part
(`tendsto_eLpNorm_mollify_shift_sub_restrict`) with the gradient identity
(`fderiv_mollify_shift_apply_of_pos`, which turns the gradient-part into the function-part applied to
`vⱼ`), over the concrete family `rInₖ=1/(k+3)`, `rOutₖ=1/(k+2)`, `sₖ=1/(k+1)`. -/
theorem exists_seq_contDiff_tendsto_halfspace (i : Fin n) {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hv : ∀ j, MemLp (v j) p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hweak : ∀ j, IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) u (v j)) :
    ∃ w : ℕ → ℝⁿ → ℝ, (∀ k, ContDiff ℝ ∞ (w k)) ∧
      Tendsto (fun k => eLpNorm (fun x => w k x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i}))
        atTop (𝓝 0) ∧
      (∀ j, Tendsto (fun k => eLpNorm
          (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ)) - v j x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})) atTop (𝓝 0)) ∧
      (∀ k, MemLp (w k) p (volume.restrict {x : ℝⁿ | 0 < x i})) ∧
      (∀ j k, MemLp (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 < x i})) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hũLp : MemLp (Set.indicator {x : ℝⁿ | 0 < x i} u) p volume :=
    (memLp_indicator_iff_restrict hmsGt).2 hu
  have huLI : LocallyIntegrable (Set.indicator {x : ℝⁿ | 0 < x i} u) volume :=
    hũLp.locallyIntegrable hp1
  have htend : ∀ c : ℝ, Tendsto (fun k : ℕ => 1 / ((k : ℝ) + c)) atTop (𝓝 0) := by
    intro c
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) + c) atTop atTop :=
      tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop
    simpa [one_div] using h1.inv_tendsto_atTop
  set ψ : ℕ → ContDiffBump (0 : ℝⁿ) := fun k =>
    { rIn := 1 / ((k : ℝ) + 3), rOut := 1 / ((k : ℝ) + 2), rIn_pos := by positivity,
      rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith) } with hψ
  set sq : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hsq
  have hφ : Tendsto (fun k => (ψ k).rOut) atTop (𝓝 0) := by simpa [hψ] using htend 2
  have hs0 : ∀ k, 0 < sq k := fun k => by rw [hsq]; positivity
  have hs : Tendsto sq atTop (𝓝 0) := by simpa [hsq] using htend 1
  have hrs : ∀ k, (ψ k).rOut < sq k := fun k => by
    show (1 : ℝ) / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1)
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  refine ⟨fun k x => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Set.indicator {x : ℝⁿ | 0 < x i} u) (x + sq k • EuclideanSpace.single i (1 : ℝ)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact ((ψ k).hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ k).contDiff_normed huLI).comp (contDiff_id.add contDiff_const)
  · exact tendsto_eLpNorm_mollify_shift_sub_restrict i hp hu hφ hs0 hs
  · intro j
    refine (tendsto_eLpNorm_mollify_shift_sub_restrict i hp (hv j) hφ hs0 hs).congr (fun k => ?_)
    refine eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2 (Filter.Eventually.of_forall
      fun x (hx : 0 < x i) => ?_))
    show ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} (v j))
          (x + sq k • EuclideanSpace.single i (1 : ℝ)) - v j x
      = fderiv ℝ (fun y => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} u) (y + sq k • EuclideanSpace.single i (1 : ℝ))) x
          (EuclideanSpace.single j (1 : ℝ)) - v j x
    rw [fderiv_mollify_shift_apply_of_pos i j (hweak j) huLI (ψ k) (hrs k) hx]
  · -- `MemLp (w k)` on `{xᵢ>0}`
    intro k
    have hconv : MemLp ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator {x : ℝⁿ | 0 < x i} u) p volume :=
      memLp_convolution (ψ k).contDiff_normed (ψ k).hasCompactSupport_normed
        (ψ k).nonneg_normed (ψ k).integral_normed hp hũLp
    exact (hconv.comp_measurePreserving
      (measurePreserving_add_right volume (sq k • EuclideanSpace.single i (1 : ℝ)))).restrict _
  · -- `MemLp (∂ⱼ(w k))` on `{xᵢ>0}`, via the gradient identity
    intro j k
    have hvjLp : MemLp (Set.indicator {x : ℝⁿ | 0 < x i} (v j)) p volume :=
      (memLp_indicator_iff_restrict hmsGt).2 (hv j)
    have hconvv : MemLp ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Set.indicator {x : ℝⁿ | 0 < x i} (v j)) p volume :=
      memLp_convolution (ψ k).contDiff_normed (ψ k).hasCompactSupport_normed
        (ψ k).nonneg_normed (ψ k).integral_normed hp hvjLp
    have hRHS : MemLp (fun x => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Set.indicator {x : ℝⁿ | 0 < x i} (v j)) (x + sq k • EuclideanSpace.single i (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 < x i}) :=
      (hconvv.comp_measurePreserving
        (measurePreserving_add_right volume (sq k • EuclideanSpace.single i (1 : ℝ)))).restrict _
    have hae : (fun x => fderiv ℝ (fun y => ((ψ k).normed volume
            ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator {x : ℝⁿ | 0 < x i} u)
            (y + sq k • EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single j (1 : ℝ)))
        =ᵐ[volume.restrict {x : ℝⁿ | 0 < x i}]
          (fun x => ((ψ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            Set.indicator {x : ℝⁿ | 0 < x i} (v j)) (x + sq k • EuclideanSpace.single i (1 : ℝ))) := by
      refine (ae_restrict_iff' hmsGt).2 (Filter.Eventually.of_forall (fun x (hx : 0 < x i) => ?_))
      exact fderiv_mollify_shift_apply_of_pos i j (hweak j) huLI (ψ k) (hrs k) hx
    exact (memLp_congr_ae hae).mpr hRHS

/-- **Restricted `Lᵖ` bound for a normal-glue-shaped function.**  Companion of
`eLpNorm_normalGlue_le` with the right-hand side measured only on the upper half-space `{xᵢ≥0}`,
provided the lower branch `B` (on `{xᵢ≤0}`) is dominated there by `g` on `{xᵢ≥0}`.  The `{xᵢ<0}`
values of `g` never enter — exactly what the bounded-extension-by-density argument requires. -/
theorem eLpNorm_normalGlue_le_restrict (i : Fin n) {p : ℝ≥0∞} (hp : 1 ≤ p) {g B : ℝⁿ → ℝ}
    (hg : AEStronglyMeasurable g volume) (hB : AEStronglyMeasurable B volume)
    (hBg : eLpNorm B p (volume.restrict {x : ℝⁿ | x i ≤ 0})
      ≤ eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i})) :
    eLpNorm (fun x => if 0 < x i then g x else B x) p volume
      ≤ 2 * eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hmsLe : MeasurableSet {x : ℝⁿ | x i ≤ 0} :=
    measurableSet_le (EuclideanSpace.proj i).continuous.measurable measurable_const
  have heqv : (fun x => if 0 < x i then g x else B x)
      = fun x => {x : ℝⁿ | 0 < x i}.indicator g x + {x : ℝⁿ | x i ≤ 0}.indicator B x := by
    funext x
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    by_cases hx : 0 < x i
    · rw [if_pos hx, if_pos hx, if_neg (not_le.2 hx), add_zero]
    · rw [if_neg hx, if_neg hx, if_pos (not_lt.1 hx), zero_add]
  rw [heqv]
  calc eLpNorm (fun x => {x : ℝⁿ | 0 < x i}.indicator g x
          + {x : ℝⁿ | x i ≤ 0}.indicator B x) p volume
      ≤ eLpNorm ({x : ℝⁿ | 0 < x i}.indicator g) p volume
        + eLpNorm ({x : ℝⁿ | x i ≤ 0}.indicator B) p volume :=
        eLpNorm_add_le (hg.indicator hmsGt) (hB.indicator hmsLe) hp
    _ = eLpNorm g p (volume.restrict {x : ℝⁿ | 0 < x i})
        + eLpNorm B p (volume.restrict {x : ℝⁿ | x i ≤ 0}) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hmsGt,
          eLpNorm_indicator_eq_eLpNorm_restrict hmsLe]
    _ ≤ eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i})
        + eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) :=
        add_le_add (eLpNorm_mono_measure g
          (Measure.restrict_mono (Set.setOf_subset_setOf.2 (fun _ hx => hx.le)) le_rfl)) hBg
    _ = 2 * eLpNorm g p (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := (two_mul _).symm

/-- **Restricted `Lᵖ` bound for the even reflection's weak gradient.**  As `eLpNorm_evenRefl_grad_le`
but measuring `∂ⱼu` only on `{xᵢ≥0}`: the reflected `eⱼ`-derivative of `evenRefl i u` has `Lᵖ` norm
`≤ 2‖∂ⱼu‖_{Lᵖ(\{xᵢ≥0\})}`.  The lower branch `(±1)·∂ⱼu∘refll` on `{xᵢ≤0}` is pushed to `∂ⱼu` on
`{xᵢ≥0}` by the measure-preserving `refll : \{xᵢ≤0\}→\{xᵢ≥0\}`. -/
theorem eLpNorm_evenRefl_grad_le_restrict (i j : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hg : AEStronglyMeasurable
      (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) volume) :
    eLpNorm (fun x => if 0 < x i then fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))
        else (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p volume
      ≤ 2 * eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
  have hmsGe : MeasurableSet {x : ℝⁿ | 0 ≤ x i} :=
    measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable
  have hB : AEStronglyMeasurable (fun x => (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) volume :=
    (hg.comp_measurePreserving (refll_measurePreserving i)).const_mul _
  have hpre : refll i ⁻¹' {x : ℝⁿ | 0 ≤ x i} = {x : ℝⁿ | x i ≤ 0} := by
    ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, refll_apply_self]; constructor <;> intro h <;>
      linarith
  have hmp : MeasurePreserving (refll i) (volume.restrict {x : ℝⁿ | x i ≤ 0})
      (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
    have h := (refll_measurePreserving i).restrict_preimage hmsGe
    rwa [hpre] at h
  have hBg : eLpNorm (fun x => (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | x i ≤ 0})
      ≤ eLpNorm (fun x => fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}) := by
    have hfun : (fun x => (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u (refll i x) (EuclideanSpace.single j (1 : ℝ)))
        = (fun y => (if j = i then (-1 : ℝ) else 1)
          * fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) ∘ refll i := rfl
    rw [hfun, eLpNorm_comp_measurePreserving
      ((hg.mono_measure Measure.restrict_le_self).const_mul _) hmp]
    split_ifs with h
    · simp only [neg_one_mul]
      exact le_of_eq (eLpNorm_neg (fun y => fderiv ℝ u y (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}))
    · simp only [one_mul, le_refl]
  exact eLpNorm_normalGlue_le_restrict i hp hg hB hBg

/-- **Extraction of an `Lᵖ` limit from a Cauchy sequence of `Lᵖ` functions.**  If the `Lp`-classes
`(f_k).toLp` form a Cauchy sequence, then by completeness of `Lᵖ` there is a limit function `G ∈ Lᵖ`
with `‖f_k − G‖_p → 0`.  Used once for the reflected approximants and once per coordinate for their
gradients in the bounded-extension-by-density argument. -/
theorem exists_memLp_tendsto_of_cauchySeq_toLp {F : ℕ → ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hF : ∀ k, MemLp (F k) p volume)
    (hcauchy : CauchySeq (fun k => (hF k).toLp (F k))) :
    ∃ G : ℝⁿ → ℝ, MemLp G p volume ∧
      Tendsto (fun k => eLpNorm (fun x => F k x - G x) p volume) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑L, Lp.memLp L, ?_⟩
  rw [← Lp.toLp_coeFn L (Lp.memLp L)] at hL
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF (⇑L) (Lp.memLp L)).mp hL

/-- The even reflection is subtractive (a consequence of linearity). -/
theorem evenRefl_sub (i : Fin n) (u v : ℝⁿ → ℝ) :
    evenRefl i (fun x => u x - v x) = fun x => evenRefl i u x - evenRefl i v x := by
  funext x; simp only [evenRefl]; split_ifs <;> rfl

/-- **Cauchy transfer through a dominated sequence.**  If `(w_k).toLp` is Cauchy in `Lᵖ(s)` and the
`Lᵖ`-increments of `E_k` are dominated by twice those of `w_k`, then `(E_k).toLp` is Cauchy in
`Lᵖ(ℝⁿ)`.  Applied with `E_k = evenRefl(w_k)` (and its reflected gradients), whose increments are
`≤ 2×` the upper-half increments of `w_k` by the restricted `≤2` bounds. -/
theorem cauchySeq_toLp_of_le {E w : ℕ → ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s : Set ℝⁿ}
    (hE : ∀ k, MemLp (E k) p volume) (hw : ∀ k, MemLp (w k) p (volume.restrict s))
    (hwCauchy : CauchySeq (fun k => (hw k).toLp (w k)))
    (hbound : ∀ m k, eLpNorm (E m - E k) p volume
      ≤ 2 * eLpNorm (w m - w k) p (volume.restrict s)) :
    CauchySeq (fun k => (hE k).toLp (E k)) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := EMetric.cauchySeq_iff.mp hwCauchy (ε / 2) (ENNReal.div_pos hε.ne' (by simp))
  refine ⟨N, fun m hm k hk => ?_⟩
  have hlt : 2 * edist ((hw m).toLp (w m)) ((hw k).toLp (w k)) < ε := by
    rw [mul_comm]
    calc edist ((hw m).toLp (w m)) ((hw k).toLp (w k)) * 2
        < ε / 2 * 2 := ENNReal.mul_lt_mul_left (by simp) (by simp) (hN m hm k hk)
      _ = ε := ENNReal.div_mul_cancel (by simp) (by simp)
  calc edist ((hE m).toLp (E m)) ((hE k).toLp (E k))
      = eLpNorm (E m - E k) p volume := Lp.edist_toLp_toLp (E m) (E k) (hE m) (hE k)
    _ ≤ 2 * eLpNorm (w m - w k) p (volume.restrict s) := hbound m k
    _ = 2 * edist ((hw m).toLp (w m)) ((hw k).toLp (w k)) := by
        rw [Lp.edist_toLp_toLp (w m) (w k) (hw m) (hw k)]
    _ < ε := hlt

/-- **Dominated `Lᵖ` limit.**  If a control sequence `c_k → cl` in `Lᵖ(s)` and the `Lᵖ(ℝⁿ)`
increments of `E_k` are dominated by `2×` those of `c_k`, then `E_k` converges in `Lᵖ(ℝⁿ)` to some
`G ∈ Lᵖ`.  Packages the Cauchy transfer and the completeness extraction; applied once to the
reflected approximants (`c = w`, `E = evenRefl w`) and once per coordinate to their gradients. -/
theorem exists_memLp_tendsto_of_dominated {c E : ℕ → ℝⁿ → ℝ} {cl : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {s : Set ℝⁿ} (hc : ∀ k, MemLp (c k) p (volume.restrict s))
    (hcl : MemLp cl p (volume.restrict s)) (hE : ∀ k, MemLp (E k) p volume)
    (hconv : Tendsto (fun k => eLpNorm (fun x => c k x - cl x) p (volume.restrict s)) atTop (𝓝 0))
    (hbound : ∀ m k, eLpNorm (E m - E k) p volume ≤ 2 * eLpNorm (c m - c k) p (volume.restrict s)) :
    ∃ G : ℝⁿ → ℝ, MemLp G p volume ∧
      Tendsto (fun k => eLpNorm (fun x => E k x - G x) p volume) atTop (𝓝 0) := by
  have hcCauchy : CauchySeq (fun k => (hc k).toLp (c k)) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' c hc cl hcl).mpr hconv).cauchySeq
  exact exists_memLp_tendsto_of_cauchySeq_toLp hE
    (cauchySeq_toLp_of_le hE hc hcCauchy hbound)

/-- **A `≤2` bound passes to the `Lᵖ`-limit.**  If `E_k → G` in `Lᵖ(ℝⁿ)`, `c_k → cl` in `Lᵖ(s)`, and
`‖E_k‖ ≤ 2‖c_k‖_{Lᵖ(s)}` for every `k`, then `‖G‖ ≤ 2‖cl‖_{Lᵖ(s)}`.  This turns the per-approximant
restricted `≤2` bounds into the operator norm bound on the limit — applied once to the extended
function and once per coordinate to its gradient. -/
theorem eLpNorm_le_two_of_tendsto {E c : ℕ → ℝⁿ → ℝ} {G cl : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {s : Set ℝⁿ} (haE : ∀ k, AEStronglyMeasurable (E k) volume)
    (haG : AEStronglyMeasurable G volume) (hacl : AEStronglyMeasurable cl (volume.restrict s))
    (hac : ∀ k, AEStronglyMeasurable (c k) (volume.restrict s))
    (hEconv : Tendsto (fun k => eLpNorm (fun x => E k x - G x) p volume) atTop (𝓝 0))
    (hcconv : Tendsto (fun k => eLpNorm (fun x => c k x - cl x) p (volume.restrict s)) atTop (𝓝 0))
    (hbound : ∀ k, eLpNorm (E k) p volume ≤ 2 * eLpNorm (c k) p (volume.restrict s)) :
    eLpNorm G p volume ≤ 2 * eLpNorm cl p (volume.restrict s) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hbnd : ∀ k, eLpNorm G p volume
      ≤ eLpNorm (fun x => E k x - G x) p volume
        + (2 * eLpNorm cl p (volume.restrict s)
           + 2 * eLpNorm (fun x => c k x - cl x) p (volume.restrict s)) := by
    intro k
    have hck : eLpNorm (c k) p (volume.restrict s)
        ≤ eLpNorm cl p (volume.restrict s)
          + eLpNorm (fun x => c k x - cl x) p (volume.restrict s) :=
      calc eLpNorm (c k) p (volume.restrict s)
          = eLpNorm (fun x => cl x + (c k x - cl x)) p (volume.restrict s) :=
            eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
              show c k x = cl x + (c k x - cl x); ring)
        _ ≤ eLpNorm cl p (volume.restrict s)
            + eLpNorm (fun x => c k x - cl x) p (volume.restrict s) :=
            eLpNorm_add_le hacl ((hac k).sub hacl) hp1
    calc eLpNorm G p volume
        = eLpNorm (fun x => (G x - E k x) + E k x) p volume :=
          eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
            show G x = (G x - E k x) + E k x; ring)
      _ ≤ eLpNorm (fun x => G x - E k x) p volume + eLpNorm (E k) p volume :=
          eLpNorm_add_le (haG.sub (haE k)) (haE k) hp1
      _ = eLpNorm (fun x => E k x - G x) p volume + eLpNorm (E k) p volume := by
          congr 1
          rw [show (fun x => G x - E k x) = (fun x : ℝⁿ => -(E k x - G x)) from
            funext fun x => by ring]
          exact eLpNorm_neg (fun x => E k x - G x) p volume
      _ ≤ eLpNorm (fun x => E k x - G x) p volume + 2 * eLpNorm (c k) p (volume.restrict s) := by
          gcongr; exact hbound k
      _ ≤ eLpNorm (fun x => E k x - G x) p volume
          + (2 * eLpNorm cl p (volume.restrict s)
             + 2 * eLpNorm (fun x => c k x - cl x) p (volume.restrict s)) := by
          gcongr; rw [← mul_add]; gcongr
  have htend : Tendsto (fun k => eLpNorm (fun x => E k x - G x) p volume
      + (2 * eLpNorm cl p (volume.restrict s)
         + 2 * eLpNorm (fun x => c k x - cl x) p (volume.restrict s)))
      atTop (𝓝 (2 * eLpNorm cl p (volume.restrict s))) := by
    have h0 : Tendsto (fun k => eLpNorm (fun x => E k x - G x) p volume
        + (2 * eLpNorm cl p (volume.restrict s)
           + 2 * eLpNorm (fun x => c k x - cl x) p (volume.restrict s)))
        atTop (𝓝 (0 + (2 * eLpNorm cl p (volume.restrict s) + 2 * 0))) :=
      hEconv.add (tendsto_const_nhds.add
        (ENNReal.Tendsto.const_mul hcconv (Or.inr (by simp))))
    simpa using h0
  exact ge_of_tendsto htend (Filter.Eventually.of_forall hbnd)

/-- **The half-space extension theorem (bounded operator).**  Every `u ∈ W^{1,p}(\{xᵢ>0\})` with weak
derivatives `v` extends to a `U ∈ W^{1,p}(ℝⁿ)` with weak derivatives `V`, agreeing with `u` a.e. on
`\{xᵢ>0\}` and satisfying the operator bounds `‖U‖_{Lᵖ(ℝⁿ)} ≤ 2‖u‖_{Lᵖ(\{xᵢ>0\})}` and
`‖Vⱼ‖_{Lᵖ(ℝⁿ)} ≤ 2‖vⱼ‖_{Lᵖ(\{xᵢ>0\})}`.  Take the boundary-density approximants `wₖ → u`, reflect
them (`Eₖ = evenRefl wₖ`), and pass to the `Lᵖ` limit: `Eₖ` and their reflected gradients are Cauchy
(restricted `≤2` bounds + `wₖ` Cauchy), so converge to `U` and `Vⱼ`; the weak-derivative relation
transfers by `isWeakDerivInDir_of_tendsto_Lp_restrict`, the `≤2` bounds pass to the limit
(`eLpNorm_le_two_of_tendsto`), and `U =ᵐ u` on `\{xᵢ>0\}` because `Eₖ = wₖ` there.  This is the
bounded `W^{1,p}` extension operator for the flat half-space — the local model of Evans §5.4. -/
theorem exists_memW1p_extension_halfspace (i : Fin n) {u : ℝⁿ → ℝ} {v : Fin n → ℝⁿ → ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hu : MemLp u p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hv : ∀ j, MemLp (v j) p (volume.restrict {x : ℝⁿ | 0 < x i}))
    (hweak : ∀ j, IsWeakDerivInDir {x : ℝⁿ | 0 < x i} (EuclideanSpace.single j (1 : ℝ)) u (v j)) :
    ∃ (U : ℝⁿ → ℝ) (V : Fin n → ℝⁿ → ℝ), MemLp U p volume ∧ (∀ j, MemLp (V j) p volume) ∧
      (∀ j, IsWeakDerivInDir Set.univ (EuclideanSpace.single j (1 : ℝ)) U (V j)) ∧
      U =ᵐ[volume.restrict {x : ℝⁿ | 0 < x i}] u ∧
      eLpNorm U p volume ≤ 2 * eLpNorm u p (volume.restrict {x : ℝⁿ | 0 < x i}) ∧
      ∀ j, eLpNorm (V j) p volume ≤ 2 * eLpNorm (v j) p (volume.restrict {x : ℝⁿ | 0 < x i}) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hmsGt : MeasurableSet {x : ℝⁿ | 0 < x i} :=
    measurableSet_lt measurable_const (EuclideanSpace.proj i).continuous.measurable
  -- `{xᵢ≥0}` and `{xᵢ>0}` agree a.e. (the boundary hyperplane is null), so the restricted measures agree
  have hset : volume.restrict {x : ℝⁿ | 0 ≤ x i} = volume.restrict {x : ℝⁿ | 0 < x i} := by
    refine Measure.restrict_congr_set ?_
    have hne : ∀ᵐ x : ℝⁿ, x i ≠ 0 := by rw [ae_iff]; simpa using volume_hyperplane_eq_zero i
    filter_upwards [hne] with x hx
    simp only [eq_iff_iff]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hx), fun h => h.le⟩
  obtain ⟨w, hw_cd, hw_fun, hw_grad, hw_mem, hw_memD⟩ :=
    exists_seq_contDiff_tendsto_halfspace i hp hu hv hweak
  have hw_cd1 : ∀ k, ContDiff ℝ 1 (w k) := fun k => (hw_cd k).of_le (by norm_num)
  have hw_diff : ∀ k x, DifferentiableAt ℝ (w k) x := fun k x =>
    ((hw_cd1 k).differentiable (by norm_num)).differentiableAt
  -- reflected approximants and their whole-space `Lᵖ` membership
  have hE_mem : ∀ k, MemLp (evenRefl i (w k)) p volume := fun k => by
    have := (memW1p_evenRefl_restrict i (hw_cd1 k) (by rw [hset]; exact hw_mem k)
      (fun j => by rw [hset]; exact hw_memD j k)).memLp
    rwa [Measure.restrict_univ] at this
  -- the reflected gradient sequence
  set V : Fin n → ℕ → ℝⁿ → ℝ := fun j k x => if 0 < x i then fderiv ℝ (w k) x
      (EuclideanSpace.single j (1 : ℝ))
    else (if j = i then (-1 : ℝ) else 1)
      * fderiv ℝ (w k) (refll i x) (EuclideanSpace.single j (1 : ℝ)) with hVdef
  have hgrad_cont : ∀ k j, Continuous (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ))) :=
    fun k j => ((hw_cd1 k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hV_mem : ∀ j k, MemLp (V j k) p volume := by
    intro j k
    have hg : AEStronglyMeasurable
        (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ))) volume :=
      (hgrad_cont k j).aestronglyMeasurable
    have hBmeas : Measurable (fun x => (if j = i then (-1 : ℝ) else 1)
        * fderiv ℝ (w k) (refll i x) (EuclideanSpace.single j (1 : ℝ))) :=
      (((hgrad_cont k j).measurable.comp (refll i).continuous.measurable)).const_mul _
    have haesm : AEStronglyMeasurable (V j k) volume :=
      (Measurable.ite hmsGt (hgrad_cont k j).measurable hBmeas).aestronglyMeasurable
    refine ⟨haesm, ?_⟩
    refine lt_of_le_of_lt (eLpNorm_evenRefl_grad_le_restrict i j hp1 hg) ?_
    have : eLpNorm (fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ))) p
        (volume.restrict {x : ℝⁿ | 0 ≤ x i}) < ⊤ := by rw [hset]; exact (hw_memD j k).2
    exact ENNReal.mul_lt_top (by simp) this
  -- weak-derivative relation of each reflected approximant
  have hE_weak : ∀ k j, IsWeakDerivInDir Set.univ (EuclideanSpace.single j (1 : ℝ))
      (evenRefl i (w k)) (V j k) := fun k j => isWeakDerivInDir_evenRefl i j (hw_cd1 k)
  -- function limit `U`
  obtain ⟨U, hU_mem, hU_conv⟩ := exists_memLp_tendsto_of_dominated
    (fun k => by rw [hset]; exact hw_mem k) (by rw [hset]; exact hu) hE_mem
    (by simpa only [hset] using hw_fun)
    (fun m k => by
      rw [show (evenRefl i (w m) - evenRefl i (w k)) = evenRefl i (fun x => w m x - w k x) from
        (evenRefl_sub i (w m) (w k)).symm]
      exact eLpNorm_evenRefl_le_restrict i hp1
        (((hw_cd1 m).continuous.sub (hw_cd1 k).continuous).aestronglyMeasurable))
  -- gradient limits `Vⱼ`, one per coordinate
  have hVexists : ∀ j, ∃ Vj : ℝⁿ → ℝ, MemLp Vj p volume ∧
      Tendsto (fun k => eLpNorm (fun x => V j k x - Vj x) p volume) atTop (𝓝 0) := by
    intro j
    refine exists_memLp_tendsto_of_dominated
      (fun k => by rw [hset]; exact hw_memD j k) (by rw [hset]; exact hv j) (fun k => hV_mem j k)
      (by simpa only [hset] using hw_grad j) (fun m k => ?_)
    -- `V j m - V j k` is the reflected gradient of `w m - w k`
    have hfd : ∀ z, fderiv ℝ (w m - w k) z (EuclideanSpace.single j (1 : ℝ))
        = fderiv ℝ (w m) z (EuclideanSpace.single j (1 : ℝ))
          - fderiv ℝ (w k) z (EuclideanSpace.single j (1 : ℝ)) := fun z => by
      rw [fderiv_sub (hw_diff m z) (hw_diff k z)]; rfl
    have hshape : (V j m - V j k)
        = (fun x => if 0 < x i then fderiv ℝ (w m - w k) x (EuclideanSpace.single j (1 : ℝ))
          else (if j = i then (-1 : ℝ) else 1)
            * fderiv ℝ (w m - w k) (refll i x) (EuclideanSpace.single j (1 : ℝ))) := by
      funext x
      simp only [hVdef, Pi.sub_apply, hfd]
      split_ifs <;> ring
    have hcc : ((fun x => fderiv ℝ (w m) x (EuclideanSpace.single j (1 : ℝ)))
          - fun x => fderiv ℝ (w k) x (EuclideanSpace.single j (1 : ℝ)))
        = fun x => fderiv ℝ (w m - w k) x (EuclideanSpace.single j (1 : ℝ)) := by
      funext x; simp only [Pi.sub_apply, hfd]
    rw [hshape, hcc]
    exact eLpNorm_evenRefl_grad_le_restrict i j hp1
      (((hgrad_cont m j).sub (hgrad_cont k j)).aestronglyMeasurable.congr
        (Filter.Eventually.of_forall fun z => (hfd z).symm))
  choose Vlim hVlim_mem hVlim_conv using hVexists
  -- assemble the bounded extension operator
  refine ⟨U, Vlim, hU_mem, hVlim_mem, ?_, ?_, ?_, ?_⟩
  · -- weak `eⱼ`-derivative of `U`
    intro j
    refine isWeakDerivInDir_of_tendsto_Lp_restrict hp1 hp (fun k => hE_weak k j)
      (fun k => ((hE_mem k).restrict _).locallyIntegrable hp1)
      (hU_mem.restrict _ |>.locallyIntegrable hp1)
      (fun k => ((hV_mem j k).restrict _).locallyIntegrable hp1)
      ((hVlim_mem j).restrict _ |>.locallyIntegrable hp1)
      (fun k => by rw [Measure.restrict_univ]; exact (hE_mem k).sub hU_mem)
      (fun k => by rw [Measure.restrict_univ]; exact (hV_mem j k).sub (hVlim_mem j))
      (by rw [Measure.restrict_univ]; exact hU_conv)
      (by rw [Measure.restrict_univ]; exact hVlim_conv j)
  · -- `U =ᵐ u` on `{xᵢ>0}`: `Eₖ = wₖ` there, `Eₖ → U`, `wₖ → u`
    have hEU : Tendsto (fun k => eLpNorm (fun x => w k x - U x) p
        (volume.restrict {x : ℝⁿ | 0 < x i})) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k => eLpNorm (fun x => evenRefl i (w k) x - U x) p
          (volume.restrict {x : ℝⁿ | 0 < x i})) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU_conv
          (Filter.Eventually.of_forall fun _ => zero_le _)
          (Filter.Eventually.of_forall fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
      refine h1.congr (fun k => eLpNorm_congr_ae ((ae_restrict_iff' hmsGt).2
        (Filter.Eventually.of_forall fun x (hx : 0 < x i) => ?_)))
      show evenRefl i (w k) x - U x = w k x - U x
      rw [evenRefl_apply_upper i (w k) hx.le]
    have hp0 : p ≠ 0 := fun h => by simp [h] at hp1
    have hau : AEStronglyMeasurable u (volume.restrict {x : ℝⁿ | 0 < x i}) :=
      hu.aestronglyMeasurable
    have hle : ∀ k, eLpNorm (fun x => U x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i})
        ≤ eLpNorm (fun x => w k x - U x) p (volume.restrict {x : ℝⁿ | 0 < x i})
          + eLpNorm (fun x => w k x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i}) := by
      intro k
      have haUwk : AEStronglyMeasurable (fun x => U x - w k x)
          (volume.restrict {x : ℝⁿ | 0 < x i}) :=
        (hU_mem.aestronglyMeasurable.sub
          (hw_cd1 k).continuous.aestronglyMeasurable).mono_measure Measure.restrict_le_self
      have hwku : AEStronglyMeasurable (fun x => w k x - u x)
          (volume.restrict {x : ℝⁿ | 0 < x i}) :=
        ((hw_cd1 k).continuous.aestronglyMeasurable.mono_measure Measure.restrict_le_self).sub hau
      calc eLpNorm (fun x => U x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i})
          = eLpNorm (fun x => (U x - w k x) + (w k x - u x)) p
              (volume.restrict {x : ℝⁿ | 0 < x i}) :=
            eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
              show U x - u x = (U x - w k x) + (w k x - u x); ring)
        _ ≤ eLpNorm (fun x => U x - w k x) p (volume.restrict {x : ℝⁿ | 0 < x i})
            + eLpNorm (fun x => w k x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i}) :=
            eLpNorm_add_le haUwk hwku hp1
        _ = eLpNorm (fun x => w k x - U x) p (volume.restrict {x : ℝⁿ | 0 < x i})
            + eLpNorm (fun x => w k x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i}) := by
            congr 1
            rw [show (fun x => U x - w k x) = (fun x : ℝⁿ => -(w k x - U x)) from
              funext fun x => by ring]
            exact eLpNorm_neg (fun x => w k x - U x) p (volume.restrict {x : ℝⁿ | 0 < x i})
    have huU : eLpNorm (fun x => U x - u x) p (volume.restrict {x : ℝⁿ | 0 < x i}) = 0 := by
      refine le_antisymm ?_ (zero_le _)
      exact ge_of_tendsto (by simpa using hEU.add hw_fun) (Filter.Eventually.of_forall hle)
    have hae0 : (fun x => U x - u x) =ᵐ[volume.restrict {x : ℝⁿ | 0 < x i}] 0 :=
      (eLpNorm_eq_zero_iff
        ((hU_mem.aestronglyMeasurable.mono_measure Measure.restrict_le_self).sub hau) hp0).mp huU
    filter_upwards [hae0] with x hx
    simpa [sub_eq_zero] using hx
  · -- operator bound `‖U‖ ≤ 2‖u‖`
    refine eLpNorm_le_two_of_tendsto (fun k => (hE_mem k).aestronglyMeasurable)
      hU_mem.aestronglyMeasurable hu.aestronglyMeasurable
      (fun k => ((hw_cd1 k).continuous.aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      hU_conv hw_fun (fun k => ?_)
    rw [← hset]
    exact eLpNorm_evenRefl_le_restrict i hp1 (hw_cd1 k).continuous.aestronglyMeasurable
  · -- operator bound `‖Vⱼ‖ ≤ 2‖vⱼ‖`
    intro j
    refine eLpNorm_le_two_of_tendsto (fun k => (hV_mem j k).aestronglyMeasurable)
      (hVlim_mem j).aestronglyMeasurable (hv j).aestronglyMeasurable
      (fun k => ((hgrad_cont k j).aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      (hVlim_conv j) (hw_grad j) (fun k => ?_)
    rw [← hset]
    exact eLpNorm_evenRefl_grad_le_restrict i j hp1 (hgrad_cont k j).aestronglyMeasurable

/-- **Half-space extension at the `W^{1,p}` level.**  Convenience form of
`exists_memW1p_extension_halfspace` taking `u ∈ W^{1,p}(\{xᵢ>0\})` as a `MemW1p` hypothesis and
returning `U ∈ W^{1,p}(ℝⁿ)` agreeing with `u` a.e. on `\{xᵢ>0\}` — the natural interface a
general-domain construction would chart-flatten and glue. -/
theorem MemW1p.exists_extension_halfspace (i : Fin n) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hu : MemW1p {x : ℝⁿ | 0 < x i} p u) :
    ∃ U : ℝⁿ → ℝ, MemW1p Set.univ p U ∧ U =ᵐ[volume.restrict {x : ℝⁿ | 0 < x i}] u := by
  choose v hv_weak hv_mem using hu.exists_weakDeriv
  obtain ⟨U, V, hU_mem, hV_mem, hV_weak, hUu, _, _⟩ :=
    exists_memW1p_extension_halfspace i hp hu.memLp hv_mem hv_weak
  exact ⟨U, ⟨by rw [Measure.restrict_univ]; exact hU_mem,
    fun j => ⟨V j, hV_weak j, by rw [Measure.restrict_univ]; exact hV_mem j⟩⟩, hUu⟩

/-! ### Toward the general-domain operator: `W^{1,p}`-invariance under a linear isometry

Boundary charts orient the boundary by a rigid motion.  The weak derivative in a rotated direction
`L eᵢ` is the linear combination `∑ₖ (L eᵢ)ₖ vₖ` of the coordinate weak derivatives, which needs the
weak derivative to be additive over a *finite sum* of directions. -/

/-- The weak derivative in the zero direction is `0`. -/
theorem isWeakDerivInDir_zero (U : Set ℝⁿ) (u : ℝⁿ → ℝ) :
    IsWeakDerivInDir U (0 : ℝⁿ) u 0 := by
  intro φ hφ; simp

/-- **Directional additivity over a finite sum.**  If `Vₖ` is the weak `eₖ`-derivative of `u` for
every `k`, then `∑_{k∈s} Vₖ` is the weak `(∑_{k∈s} eₖ)`-derivative of `u`.  Finset induction on the
sum, gluing with `dir_add_restrict`. -/
theorem IsWeakDerivInDir.dir_sum {U : Set ℝⁿ} (hU : MeasurableSet U) {ι : Type*}
    {u : ℝⁿ → ℝ} {e : ι → ℝⁿ} {V : ι → ℝⁿ → ℝ} (hu : LocallyIntegrable u (volume.restrict U))
    (hV : ∀ k, LocallyIntegrable (V k) (volume.restrict U))
    (h : ∀ k, IsWeakDerivInDir U (e k) u (V k)) (s : Finset ι) :
    IsWeakDerivInDir U (∑ k ∈ s, e k) u (fun x => ∑ k ∈ s, V k x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isWeakDerivInDir_zero U u
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsWeakDerivInDir.dir_add_restrict hU hu (hV a)
      (locallyIntegrable_finset_sum s (fun k _ => hV k)) (h a) ih

/-- **`W^{1,p}(ℝⁿ)` is invariant under a linear isometry.**  For `L : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ`,
`u ∈ W^{1,p}(ℝⁿ) ⟹ u ∘ L ∈ W^{1,p}(ℝⁿ)`.  The weak `eᵢ`-derivative of `u∘L` is `(∂_{L eᵢ}u)∘L`
(`isWeakDerivInDir_comp_linear`), and `∂_{L eᵢ}u = ∑ₖ (L eᵢ)ₖ·vₖ` expands the rotated direction over
the coordinate weak derivatives (`dir_sum` of `dir_smul`, using the orthonormal expansion
`L eᵢ = ∑ₖ (L eᵢ)ₖ • eₖ`).  A rigid-motion building block for orienting boundary charts. -/
theorem MemW1p.comp_linearIsometry (L : ℝⁿ ≃ₗᵢ[ℝ] ℝⁿ) {u : ℝⁿ → ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hu : MemW1p Set.univ p u) : MemW1p Set.univ p (fun x => u (L x)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hLmp : MeasurePreserving (L : ℝⁿ → ℝⁿ) volume volume := L.measurePreserving
  choose v hv_weak hv_mem using hu.exists_weakDeriv
  have hu_vol : MemLp u p volume := by have := hu.memLp; rwa [Measure.restrict_univ] at this
  have hv_vol : ∀ k, MemLp (v k) p volume := fun k => by
    have := hv_mem k; rwa [Measure.restrict_univ] at this
  have huLI : LocallyIntegrable u (volume.restrict (Set.univ : Set ℝⁿ)) :=
    hu.memLp.locallyIntegrable hp1
  have hvLI : ∀ k, LocallyIntegrable (v k) (volume.restrict (Set.univ : Set ℝⁿ)) :=
    fun k => (hv_mem k).locallyIntegrable hp1
  have hbasis : ∀ w : ℝⁿ, (∑ k, w k • EuclideanSpace.single k (1 : ℝ)) = w := by
    intro w
    have h := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h
  refine ⟨by rw [Measure.restrict_univ]; exact hu_vol.comp_measurePreserving hLmp, fun i => ?_⟩
  refine ⟨fun x => ∑ k, (L (EuclideanSpace.single i (1 : ℝ))) k * v k (L x), ?_, ?_⟩
  · have hdir : IsWeakDerivInDir Set.univ (L (EuclideanSpace.single i (1 : ℝ))) u
        (fun x => ∑ k, (L (EuclideanSpace.single i (1 : ℝ))) k * v k x) := by
      have hsum := IsWeakDerivInDir.dir_sum MeasurableSet.univ huLI
        (V := fun k => fun x => (L (EuclideanSpace.single i (1 : ℝ))) k * v k x)
        (fun k => (hvLI k).smul ((L (EuclideanSpace.single i (1 : ℝ))) k))
        (fun k => IsWeakDerivInDir.dir_smul ((L (EuclideanSpace.single i (1 : ℝ))) k) (hv_weak k))
        Finset.univ
      rwa [hbasis (L (EuclideanSpace.single i (1 : ℝ)))] at hsum
    exact isWeakDerivInDir_comp_linear L (EuclideanSpace.single i (1 : ℝ)) hdir
  · rw [Measure.restrict_univ]
    exact memLp_finset_sum Finset.univ
      (fun k _ => ((hv_vol k).comp_measurePreserving hLmp).const_mul _)

/-! ### The general `C¹` domain and its boundary partition of unity

We now leave the flat half-space and set up the geometry for the general extension operator.  A
bounded `C¹` domain is defined **elementarily** (Evans §5.4): near every boundary point the boundary
is the graph of a `C¹` function of `n−1` coordinates.  From compactness of the closure and Mathlib's
smooth partitions of unity we extract a finite-in-effect atlas of boundary charts together with a
subordinate smooth partition of unity — the backbone that lets us localize the extension to one
chart at a time (interior pieces extend by zero; boundary pieces flatten–reflect–extend). -/

/-- **A bounded `C¹` domain** (Evans §5.4): an open bounded set whose boundary is, near every
boundary point, the graph of a `C¹` function of `n−1` of the coordinates.  For each `x ∈ ∂Ω` there
is a ball `B(x, r)`, a coordinate index `i`, a sign `sgn = ±1`, and a `C¹` function `γ`
**independent of the `i`-th coordinate**, so that inside the ball `Ω` is exactly the open
epigraph/hypograph `{y | 0 < sgn·(yᵢ − γ y)}` (`sgn = +1`: above the graph in coordinate `i`;
`sgn = −1`: below). -/
structure IsC1Domain (Ω : Set ℝⁿ) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  chart : ∀ x ∈ frontier Ω, ∃ (r : ℝ) (i : Fin n) (sgn : ℝ) (γ : ℝⁿ → ℝ),
    0 < r ∧ (sgn = 1 ∨ sgn = -1) ∧ ContDiff ℝ 1 γ ∧
    (∀ (y : ℝⁿ) (t : ℝ), γ (y + t • EuclideanSpace.single i (1 : ℝ)) = γ y) ∧
    Ω ∩ Metric.ball x r = {y : ℝⁿ | 0 < sgn * (y i - γ y)} ∩ Metric.ball x r

/-- The closure of a bounded `C¹` domain is compact (closed and bounded in a proper space). -/
theorem IsC1Domain.isCompact_closure {Ω : Set ℝⁿ} (hΩ : IsC1Domain Ω) :
    IsCompact (closure Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩ.isBounded.closure

/-- `closure Ω = Ω ∪ frontier Ω` for open `Ω`. -/
theorem IsC1Domain.closure_eq {Ω : Set ℝⁿ} (hΩ : IsC1Domain Ω) :
    closure Ω = Ω ∪ frontier Ω := by
  rw [frontier, hΩ.isOpen.interior_eq]
  ext y
  simp only [Set.mem_union, Set.mem_diff]
  constructor
  · intro hy; by_cases h : y ∈ Ω
    · exact Or.inl h
    · exact Or.inr ⟨hy, h⟩
  · rintro (h | ⟨h, _⟩)
    · exact subset_closure h
    · exact h

/-- **Boundary partition of unity for a `C¹` domain.**  There is a smooth partition of unity
`ζ : ι → ℝⁿ → ℝ`, subordinate to opens `U`, summing to `1` on `closure Ω`, in which every open
`U j` is either contained in `Ω` (an interior piece) or is a boundary chart ball carrying valid
graph data.  This is the geometric backbone of the general extension operator: interior pieces
extend by zero, boundary pieces flatten–reflect–extend.  (Only finitely many `ζ j` are nonzero on
`closure Ω` by local finiteness, but we keep the index general here.) -/
theorem IsC1Domain.exists_boundary_partition {Ω : Set ℝⁿ} (hΩ : IsC1Domain Ω) :
    ∃ (ι : Type) (ζ : ι → ℝⁿ → ℝ) (U : ι → Set ℝⁿ),
      (∀ j, IsOpen (U j)) ∧
      (∀ j, tsupport (ζ j) ⊆ U j) ∧
      (∀ j, ContDiff ℝ (∞ : WithTop ℕ∞) (ζ j)) ∧
      (∀ j x, 0 ≤ ζ j x) ∧
      (LocallyFinite fun j => Function.support (ζ j)) ∧
      (∀ x ∈ closure Ω, ∑ᶠ j, ζ j x = 1) ∧
      (∀ j, U j ⊆ Ω ∨ ∃ (x : ℝⁿ) (r : ℝ) (i : Fin n) (sgn : ℝ) (γ : ℝⁿ → ℝ),
          U j = Metric.ball x r ∧ 0 < r ∧ (sgn = 1 ∨ sgn = -1) ∧ ContDiff ℝ 1 γ ∧
          (∀ (y : ℝⁿ) (t : ℝ), γ (y + t • EuclideanSpace.single i (1 : ℝ)) = γ y) ∧
          Ω ∩ Metric.ball x r = {y : ℝⁿ | 0 < sgn * (y i - γ y)} ∩ Metric.ball x r) := by
  classical
  choose r idx sgn γ hr hsgn hγcd hγindep hchart using hΩ.chart
  set ι : Type := Option (frontier Ω) with hι
  set U : ι → Set ℝⁿ := fun j => j.rec Ω (fun x => Metric.ball (x : ℝⁿ) (r x x.2)) with hU
  have hUopen : ∀ j, IsOpen (U j) := by
    intro j; cases j with
    | none => exact hΩ.isOpen
    | some x => exact Metric.isOpen_ball
  have hcover : closure Ω ⊆ ⋃ j, U j := by
    intro y hy
    rw [hΩ.closure_eq] at hy
    rcases hy with hyΩ | hyfr
    · exact Set.mem_iUnion.2 ⟨none, hyΩ⟩
    · refine Set.mem_iUnion.2 ⟨some ⟨y, hyfr⟩, ?_⟩
      change y ∈ Metric.ball (y : ℝⁿ) (r y hyfr)
      rw [Metric.mem_ball, dist_self]
      exact hr y hyfr
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℝⁿ))
    isClosed_closure U hUopen hcover
  refine ⟨ι, fun j => (f j : ℝⁿ → ℝ), U, hUopen, hf, fun j => ?_, fun j => f.nonneg j,
    f.locallyFinite, fun x hx => f.sum_eq_one hx, fun j => ?_⟩
  · exact contMDiff_iff_contDiff.mp (f j).contMDiff
  · cases j with
    | none => exact Or.inl (subset_refl Ω)
    | some x => exact Or.inr ⟨(x : ℝⁿ), r x x.2, idx x x.2, sgn x x.2, γ x x.2, rfl,
        hr x x.2, hsgn x x.2, hγcd x x.2, hγindep x x.2, hchart x x.2⟩

end Sobolev
