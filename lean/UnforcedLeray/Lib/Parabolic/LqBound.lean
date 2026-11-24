import UnforcedLeray.Lib.Parabolic.OffSupport
import UnforcedLeray.Lib.CZCore.LpBound

/-!
# `L^q` bounds for `∂_i∂_j (∂_t - Δ)^{-1}` and `∂_t (∂_t - Δ)^{-1}` (INF02 T7)


target T7 (`secondDerivOp_eLpNorm_le`), §4 BP-B steps 4–7; decision D4 of `scoping/README.md` §3:
the parabolic instance (weights `(2,1,…,1)`) of the anisotropic Calderón–Zygmund core
`Lib/CZCore` (`IsCZConvolution`, `lp_bound`). Manuscript: eq:free-stress-11
(`paper/main.tex` lines 7447–7477, blueprint unit B0423) for `1 < q < ∞`, at `ν = 1` (the
`ν`-scaling is part of INF02 T8).

* `backOp_offSupport`: the transpose `backOp` has the kernel `K(-Z)` off the support.
* `pullL2`, `pushL2`: the isometries `L²(ℝ × ℝ^d) ≅ L²(ℝ^{1+d})` induced by `psEquiv`.
* `isCZConvolution_coord`, `isCZConvolution_coord_back`: the transported operator and its
  transpose are anisotropic CZ convolution operators for the weights `parWeights d`, with
  kernels `causalKernelCoord i j` and `v ↦ causalKernelCoord i j (-v)`.
* `secondDerivOp_eLpNorm_le` (**INF02 T7**): for `1 < p < ∞` there is `C` with
  `‖∂_i∂_j (∂_t - Δ)^{-1} F‖_p ≤ C ‖F‖_p` for every `F ∈ L² ∩ L^p`.
* `timeDerivOp = I + Σᵢ secondDerivOp i i` (the operator `F ↦ ∂_t u`, `u = (∂_t - Δ)^{-1}F`, since
  `∂_t u = F + Δu`), `norm_timeDerivOp_le` (`‖·‖ ≤ 1 + d` on `L²`) and
  `timeDerivOp_eLpNorm_le` (`L^p`).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Parabolic

open MeasureTheory Real Set Filter Metric
open scoped ENNReal NNReal ContDiff Topology RealInnerProductSpace

open UnforcedLeray.Gaussian (Euc gaussKernel)
open UnforcedLeray.CZ (anisoNorm homDim IsCZConvolution)

variable {d : ℕ}

section BackOffSupport

variable {ν : ℝ}

theorem causalKernelNu_trev (ν : ℝ) (i j : Fin d) (V : PS d) :
    causalKernelNu ν i j (trev V) = causalKernelNu ν i j (-V) := by
  unfold causalKernelNu trev
  simp only [Prod.fst_neg, Prod.snd_neg, mul_neg]
  rw [causalKernel_neg_space]

/-- **Off-support representation of the transpose.** If `G ∈ L²` vanishes a.e. off a compact
`S`, then for a.e. `Z ∉ S`, `(backOp G)(Z) = ∫ K_ν(-(Z - W)) G(W) dW`. -/
theorem backOp_offSupport (hν : 0 < ν) (i j : Fin d) (G : Lp ℝ 2 (volume : Measure (PS d)))
    {S : Set (PS d)} (hS : IsCompact S) (hG : ∀ᵐ Y ∂volume, Y ∉ S → G Y = 0) :
    ∀ᵐ Z ∂volume, Z ∉ S → backOp hν i j G Z = ∫ W, causalKernelNu ν i j (-(Z - W)) * G W := by
  have hR := measurePreserving_trev (d := d)
  have hRS : IsCompact (trev '' S) := hS.image continuous_trev
  have hRG : ∀ᵐ Y ∂volume, Y ∉ trev '' S → reflL2 d G Y = 0 := by
    have h1 := hR.quasiMeasurePreserving.ae hG
    filter_upwards [coeFn_reflL2 G, h1] with Y hY1 hY2 hYS
    rw [hY1, Function.comp_apply]
    exact hY2 fun h => hYS ⟨trev Y, h, trev_trev Y⟩
  have hoff := secondDerivOp_offSupport hν i j (reflL2 d G) hRS hRG
  have hoff' := hR.quasiMeasurePreserving.ae hoff
  filter_upwards [coeFn_reflL2 (secondDerivOp hν i j (reflL2 d G)), hoff'] with Z h1 h2 hZS
  have hZ' : trev Z ∉ trev '' S := by
    rintro ⟨W, hW, hWZ⟩
    have : W = Z := by rw [← trev_trev W, hWZ, trev_trev]
    exact hZS (this ▸ hW)
  change (reflL2 d) ((secondDerivOp hν i j) ((reflL2 d) G)) Z = _
  rw [h1, Function.comp_apply, h2 hZ']
  -- change of variables `Y = trev W`
  have hcv := hR.integral_comp (MeasurableEquiv.measurableEmbedding
      ⟨⟨trev, trev, trev_trev, trev_trev⟩, continuous_trev.measurable, continuous_trev.measurable⟩)
    (fun Y => causalKernelNu ν i j (trev Z - Y) * reflL2 d G Y)
  rw [← hcv]
  refine integral_congr_ae ?_
  have hG' := hR.quasiMeasurePreserving.ae (coeFn_reflL2 G)
  filter_upwards [hG'] with W hW
  rw [hW, Function.comp_apply, trev_trev, ← trev_sub, causalKernelNu_trev]

end BackOffSupport

section Transport

/-- Pull back along `psEquiv`: `L²(ℝ × ℝ^d) → L²(ℝ^{1+d})`. -/
def pullL2 (d : ℕ) :
    Lp ℝ 2 (volume : Measure (PS d)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (psEquiv d) measurePreserving_psEquiv).toContinuousLinearMap

/-- Push forward along `psEquiv`: `L²(ℝ^{1+d}) → L²(ℝ × ℝ^d)`. -/
def pushL2 (d : ℕ) :
    Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (PS d)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (psEquiv d).symm
    (measurePreserving_psEquiv.symm (psEquiv d))).toContinuousLinearMap

theorem coeFn_pullL2 (F : Lp ℝ 2 (volume : Measure (PS d))) :
    ⇑(pullL2 d F) =ᵐ[volume] ⇑F ∘ psEquiv d :=
  Lp.coeFn_compMeasurePreserving F _

theorem coeFn_pushL2 (f : Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ))) :
    ⇑(pushL2 d f) =ᵐ[volume] ⇑f ∘ (psEquiv d).symm :=
  Lp.coeFn_compMeasurePreserving f _

theorem pullL2_pushL2 (f : Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ))) :
    pullL2 d (pushL2 d f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pullL2 (pushL2 d f),
    measurePreserving_psEquiv.quasiMeasurePreserving.ae (coeFn_pushL2 f)] with v h1 h2
  rw [h1, Function.comp_apply, h2, Function.comp_apply, MeasurableEquiv.symm_apply_apply]

theorem pushL2_pullL2 (F : Lp ℝ 2 (volume : Measure (PS d))) :
    pushL2 d (pullL2 d F) = F := by
  refine Lp.ext ?_
  filter_upwards [coeFn_pushL2 (pullL2 d F),
    (measurePreserving_psEquiv.symm (psEquiv d)).quasiMeasurePreserving.ae (coeFn_pullL2 F)]
    with X h1 h2
  rw [h1, Function.comp_apply, h2, Function.comp_apply, MeasurableEquiv.apply_symm_apply]

theorem integral_pull (h : PS d → ℝ) :
    ∫ v, h (psEquiv d v) = ∫ X, h X :=
  measurePreserving_psEquiv.integral_comp' h

/-- The transported operator `pull ∘ T ∘ push` (at `ν = 1`). -/
def coordOp (i j : Fin d) :
    Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ)) :=
  (pullL2 d).comp ((secondDerivOp one_pos i j).comp (pushL2 d))

/-- The transported transpose `pull ∘ backOp ∘ push`. -/
def coordBackOp (i j : Fin d) :
    Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ)) →L[ℝ] Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ)) :=
  (pullL2 d).comp ((backOp one_pos i j).comp (pushL2 d))

theorem integral_coordOp_mul (i j : Fin d) (f g : Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ))) :
    ∫ v, coordOp i j f v * g v = ∫ v, f v * coordBackOp i j g v := by
  have e1 : ∫ v, coordOp i j f v * g v =
      ∫ X, secondDerivOp one_pos i j (pushL2 d f) X * pushL2 d g X := by
    rw [← integral_pull]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_pullL2 (secondDerivOp one_pos i j (pushL2 d f)),
      measurePreserving_psEquiv.quasiMeasurePreserving.ae (coeFn_pushL2 g)] with v h1 h2
    change pullL2 d (secondDerivOp one_pos i j (pushL2 d f)) v * g v = _
    rw [h1, h2, Function.comp_apply, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have e2 : ∫ v, f v * coordBackOp i j g v =
      ∫ X, pushL2 d f X * backOp one_pos i j (pushL2 d g) X := by
    rw [← integral_pull]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_pullL2 (backOp one_pos i j (pushL2 d g)),
      measurePreserving_psEquiv.quasiMeasurePreserving.ae (coeFn_pushL2 f)] with v h1 h2
    change f v * pullL2 d (backOp one_pos i j (pushL2 d g)) v = _
    rw [h1, h2, Function.comp_apply, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  rw [e1, e2]
  exact integral_secondDerivOp_mul one_pos i j _ _

/-- Transport of an off-support representation along `psEquiv`. -/
theorem offSupport_transport {T : Lp ℝ 2 (volume : Measure (PS d)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (PS d))} {K : PS d → ℝ}
    (hT : ∀ F : Lp ℝ 2 (volume : Measure (PS d)), ∀ S : Set (PS d), IsCompact S →
      (∀ᵐ Y ∂volume, Y ∉ S → F Y = 0) → ∀ᵐ X ∂volume, X ∉ S → T F X = ∫ Y, K (X - Y) * F Y)
    (f : Lp ℝ 2 (volume : Measure (Fin (d + 1) → ℝ))) (S : Set (Fin (d + 1) → ℝ))
    (hS : IsCompact S) (hf : ∀ᵐ w ∂volume, w ∉ S → f w = 0) :
    ∀ᵐ v ∂volume, v ∉ S →
      ((pullL2 d).comp (T.comp (pushL2 d))) f v = ∫ w, K (psEquiv d (v - w)) * f w := by
  have he := measurePreserving_psEquiv (d := d)
  have hS' : IsCompact (psEquiv d '' S) := hS.image continuous_psEquiv
  have hpush : ∀ᵐ Y ∂volume, Y ∉ psEquiv d '' S → pushL2 d f Y = 0 := by
    have h1 := (he.symm (psEquiv d)).quasiMeasurePreserving.ae hf
    filter_upwards [coeFn_pushL2 f, h1] with Y hY1 hY2 hYS
    rw [hY1, Function.comp_apply]
    exact hY2 fun h => hYS ⟨_, h, MeasurableEquiv.apply_symm_apply _ Y⟩
  have hoff := he.quasiMeasurePreserving.ae (hT (pushL2 d f) _ hS' hpush)
  filter_upwards [coeFn_pullL2 (T (pushL2 d f)), hoff] with v h1 h2 hvS
  have hv' : psEquiv d v ∉ psEquiv d '' S := by
    rintro ⟨w, hw, hwv⟩
    exact hvS ((psEquiv d).injective hwv ▸ hw)
  change pullL2 d (T (pushL2 d f)) v = _
  rw [h1, Function.comp_apply, h2 hv', ← integral_pull]
  refine integral_congr_ae ?_
  filter_upwards [he.quasiMeasurePreserving.ae (coeFn_pushL2 f)] with w hw
  rw [hw, Function.comp_apply, MeasurableEquiv.symm_apply_apply, psEquiv_sub]

end Transport

section CZ

/-- The size and Hörmander constant used for both kernels. -/
theorem exists_czConstant (i j : Fin d) : ∃ B : ℝ≥0,
    (∀ v : Fin (d + 1) → ℝ, v ≠ 0 → |causalKernelCoord i j v| ≤
      B * anisoNorm (parWeights d) v ^ (-(homDim (parWeights d) : ℝ))) ∧
    (∀ w, ∫⁻ v in {v | 2 * anisoNorm (parWeights d) w < anisoNorm (parWeights d) v},
      ‖causalKernelCoord i j (v - w) - causalKernelCoord i j v‖ₑ ≤ B) := by
  obtain ⟨C, hC, hsize⟩ := abs_causalKernelCoord_le (d := d) i j
  obtain ⟨B₀, hB₀⟩ := hormander_causalKernelCoord (d := d) i j
  refine ⟨max B₀ C.toNNReal, fun v hv => ?_, fun w => (hB₀ w).trans ?_⟩
  · rw [homDim_parWeights]
    push_cast
    refine (hsize v hv).trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (UnforcedLeray.CZ.anisoNorm_nonneg _ _) _))
    exact (Real.le_coe_toNNReal C).trans (NNReal.coe_le_coe.2 (le_max_right B₀ C.toNNReal))
  · exact_mod_cast le_max_left _ _

theorem causalKernelCoord_eq (i j : Fin d) (v : Fin (d + 1) → ℝ) :
    causalKernel i j (psEquiv d v) = causalKernelCoord i j v := rfl

/-- **The transported operator is an anisotropic CZ convolution operator.** -/
theorem isCZConvolution_coord (i j : Fin d) :
    ∃ B : ℝ≥0, IsCZConvolution (parWeights d) (coordOp i j) (causalKernelCoord i j) B ∧
      IsCZConvolution (parWeights d) (coordBackOp i j)
        (fun v => causalKernelCoord i j (-v)) B := by
  obtain ⟨B, hsize, hhor⟩ := exists_czConstant (d := d) i j
  refine ⟨B, ⟨measurable_causalKernelCoord i j, hsize, hhor, ?_⟩,
    ⟨(measurable_causalKernelCoord i j).comp measurable_neg, fun v hv => ?_,
      UnforcedLeray.Parabolic.hormander_comp_neg (parWeights d) hhor, ?_⟩⟩
  · intro f S hS hf
    have h := offSupport_transport (T := secondDerivOp one_pos i j) (K := causalKernelNu 1 i j)
      (fun F S hS hF => secondDerivOp_offSupport one_pos i j F hS hF) f S hS hf
    filter_upwards [h] with v hv hvS
    change ((pullL2 d).comp ((secondDerivOp one_pos i j).comp (pushL2 d))) f v = _
    rw [hv hvS, causalKernelNu_one]
    rfl
  · rw [← UnforcedLeray.CZ.anisoNorm_neg (parWeights d) v]
    exact hsize (-v) (neg_ne_zero.2 hv)
  · intro f S hS hf
    have h := offSupport_transport (T := backOp one_pos i j)
      (K := fun Z => causalKernelNu 1 i j (-Z))
      (fun F S hS hF => backOp_offSupport one_pos i j F hS hF) f S hS hf
    filter_upwards [h] with v hv hvS
    change ((pullL2 d).comp ((backOp one_pos i j).comp (pushL2 d))) f v = _
    rw [hv hvS, causalKernelNu_one]
    congr 1

/-- **INF02 T7.** For `1 < p < ∞` there is `C` with `‖∂_i∂_j (∂_t - Δ)^{-1} F‖_p ≤ C ‖F‖_p` for
every `F ∈ L²(ℝ × ℝ^d) ∩ L^p` (eq:free-stress-11, `ν = 1`). -/
theorem secondDerivOp_eLpNorm_le (i j : Fin d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ F : Lp ℝ 2 (volume : Measure (PS d)), MemLp F (ENNReal.ofReal p) volume →
      eLpNorm (secondDerivOp one_pos i j F) (ENNReal.ofReal p) volume ≤
        C * eLpNorm F (ENNReal.ofReal p) volume := by
  obtain ⟨B, hT, hT'⟩ := isCZConvolution_coord (d := d) i j
  obtain ⟨C, hC⟩ := UnforcedLeray.CZ.lp_bound hT hT' (integral_coordOp_mul i j) hp
  refine ⟨C, fun F hF => ?_⟩
  have he := measurePreserving_psEquiv (d := d)
  have hpull : MemLp (pullL2 d F) (ENNReal.ofReal p) volume :=
    (hF.comp_measurePreserving he).ae_eq (coeFn_pullL2 F).symm
  have h := hC (pullL2 d F) hpull
  have e1 : coordOp i j (pullL2 d F) = pullL2 d (secondDerivOp one_pos i j F) := by
    simp only [coordOp, ContinuousLinearMap.comp_apply, pushL2_pullL2]
  rw [e1] at h
  have n1 : ∀ G : Lp ℝ 2 (volume : Measure (PS d)),
      eLpNorm (pullL2 d G) (ENNReal.ofReal p) volume = eLpNorm G (ENNReal.ofReal p) volume := by
    intro G
    rw [eLpNorm_congr_ae (coeFn_pullL2 G)]
    exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable G) he
  rwa [n1, n1] at h

end CZ

section TimeDeriv

variable {ν : ℝ}

/-- `∂_t u` for `u = (∂_t - νΔ)^{-1} F`: since `∂_t u = F + νΔu`, the operator is
`I + ν Σᵢ secondDerivOp ν i i`. -/
def timeDerivOp (hν : 0 < ν) : Lp ℝ 2 (volume : Measure (PS d)) →L[ℝ] Lp ℝ 2 (volume : Measure (PS d)) :=
  ContinuousLinearMap.id ℝ _ + ν • ∑ i : Fin d, secondDerivOp hν i i

/-- **`L²` bound for `∂_t u`.** `‖timeDerivOp ν‖ ≤ 1 + d`. -/
theorem norm_timeDerivOp_le (hν : 0 < ν) : ‖timeDerivOp (d := d) hν‖ ≤ 1 + d := by
  unfold timeDerivOp
  refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
  rw [Finset.smul_sum]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin d, ‖ν • secondDerivOp hν i i‖ ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => norm_smul_secondDerivOp_le hν i i
    _ = d := by simp

/-- **INF02 T7 for `∂_t`.** `L^p` bound for `∂_t (∂_t - Δ)^{-1}`, `1 < p < ∞`. -/
theorem timeDerivOp_eLpNorm_le {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ F : Lp ℝ 2 (volume : Measure (PS d)), MemLp F (ENNReal.ofReal p) volume →
      eLpNorm (timeDerivOp (d := d) one_pos F) (ENNReal.ofReal p) volume ≤
        C * eLpNorm F (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  choose C hC using fun i : Fin d => secondDerivOp_eLpNorm_le (d := d) i i hp
  refine ⟨1 + ∑ i, C i, fun F hF => ?_⟩
  have hae : ⇑(timeDerivOp (d := d) one_pos F) =ᵐ[volume]
      ⇑F + ∑ i : Fin d, ⇑(secondDerivOp one_pos i i F) := by
    have h1 : timeDerivOp (d := d) one_pos F = F + ∑ i : Fin d, secondDerivOp one_pos i i F := by
      simp [timeDerivOp]
    rw [h1]
    filter_upwards [Lp.coeFn_add F (∑ i : Fin d, secondDerivOp one_pos i i F),
      UnforcedLeray.CZ.coeFn_finset_sum Finset.univ
        (fun i : Fin d => secondDerivOp one_pos i i F)] with X h2 h3
    rw [h2, Pi.add_apply, Pi.add_apply, h3, Finset.sum_apply]
  rw [eLpNorm_congr_ae hae]
  have hmeas : ∀ i : Fin d, AEStronglyMeasurable (⇑(secondDerivOp one_pos i i F)) volume :=
    fun i => Lp.aestronglyMeasurable _
  calc eLpNorm (⇑F + ∑ i : Fin d, ⇑(secondDerivOp one_pos i i F)) (ENNReal.ofReal p) volume
      ≤ eLpNorm (⇑F) (ENNReal.ofReal p) volume +
          eLpNorm (∑ i : Fin d, ⇑(secondDerivOp one_pos i i F)) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le (Lp.aestronglyMeasurable F)
          (Finset.aestronglyMeasurable_sum _ fun i _ => hmeas i) hp1
    _ ≤ eLpNorm (⇑F) (ENNReal.ofReal p) volume +
          ∑ i : Fin d, eLpNorm (⇑(secondDerivOp one_pos i i F)) (ENNReal.ofReal p) volume := by
        gcongr
        exact eLpNorm_sum_le (fun i _ => hmeas i) hp1
    _ ≤ eLpNorm (⇑F) (ENNReal.ofReal p) volume +
          ∑ i : Fin d, (C i : ℝ≥0∞) * eLpNorm (⇑F) (ENNReal.ofReal p) volume := by
        gcongr with i
        exact hC i F hF
    _ = ((1 + ∑ i, C i : ℝ≥0) : ℝ≥0∞) * eLpNorm (⇑F) (ENNReal.ofReal p) volume := by
        rw [← Finset.sum_mul]; push_cast; ring

end TimeDeriv

end UnforcedLeray.Parabolic
