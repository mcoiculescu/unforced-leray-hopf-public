import UnforcedLeray.Units.B0418.Semigroup

/-!
# B0418 helper: `S_ν(r)` as a strongly continuous semigroup of bounded operators on `L^p`

Blueprint unit B0418 (`eq:free-stress-7`, `paper/main.tex` lines 7411--7427:
"It is strongly continuous"). The pointwise operator `AncientLocalization.freeEvolution ν r`
respects almost-everywhere equality, so it induces a bounded linear operator on the
Lebesgue space `Lp Space p volume` (real three-vector fields), `1 ≤ p < ∞`. This file
packages the semigroup law, the identity at `r = 0`, the operator bound and the strong
continuity proved in `Semigroup.lean` at that level.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace UnforcedLeray.B0418

open UnforcedLeray.AncientLocalization

variable {p : ℝ≥0∞}

theorem flow_congr_ae {f g : SpatialField} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    Heat.flow f t =ᵐ[volume] Heat.flow g t := by
  by_cases ht : 0 < t
  · rw [Heat.flow_pos _ ht, Heat.flow_pos _ ht, Heat.average_congr_ae hfg t]
  · rw [Heat.flow_nonpos _ (not_lt.mp ht), Heat.flow_nonpos _ (not_lt.mp ht)]
    exact hfg

/-- `S_ν(r)` respects almost-everywhere equality, so it acts on `L^p` classes. -/
theorem freeEvolution_congr_ae {f g : SpatialField} (hfg : f =ᵐ[volume] g) (ν r : ℝ) :
    freeEvolution ν r f =ᵐ[volume] freeEvolution ν r g :=
  SpatialScaling.ae_eq_spatialScale (flow_congr_ae hfg _) _ (Real.exp_pos _).ne'

variable [Fact (1 ≤ p)]

/-- The free similarity semigroup `S_ν(r)` of `eq:free-stress-7` as a bounded linear
operator on `L^p(ℝ³; ℝ³)`, `1 ≤ p < ∞`, with the bound `e^{-γ_p r}`. -/
def freeSemigroupLp (hp : p ≠ ∞) (ν r : ℝ) :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  LinearMap.mkContinuous
    { toFun := fun u => (freeEvolution_memLp Fact.out hp (Lp.memLp u) ν r).toLp _
      map_add' := by
        intro u v
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        have h := freeEvolution_congr_ae (Lp.coeFn_add u v) ν r
        rwa [freeEvolution_add_fun Fact.out hp (Lp.memLp u) (Lp.memLp v)] at h
      map_smul' := by
        intro c u
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        have h := freeEvolution_congr_ae (Lp.coeFn_smul c u) ν r
        rwa [freeEvolution_smul] at h }
    (Real.exp (-gammaExp p * r))
    (by
      intro u
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      have h := eLpNorm_freeEvolution_le Fact.out hp (Lp.memLp u) ν r
      calc (eLpNorm (freeEvolution ν r u) p volume).toReal
          ≤ (ENNReal.ofReal (Real.exp (-gammaExp p * r)) * eLpNorm u p volume).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.memLp u).2.ne) h
        _ = Real.exp (-gammaExp p * r) * (eLpNorm u p volume).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le])

theorem freeSemigroupLp_apply (hp : p ≠ ∞) (ν r : ℝ) (u : Lp Space p (volume : Measure Space)) :
    freeSemigroupLp hp ν r u =
      (freeEvolution_memLp Fact.out hp (Lp.memLp u) ν r).toLp (freeEvolution ν r u) := rfl

/-- The class `S_ν(r)u` is represented by the literal formula `eq:free-stress-7`. -/
theorem coeFn_freeSemigroupLp (hp : p ≠ ∞) (ν r : ℝ) (u : Lp Space p (volume : Measure Space)) :
    (freeSemigroupLp hp ν r u : SpatialField) =ᵐ[volume] freeEvolution ν r u :=
  MemLp.coeFn_toLp (freeEvolution_memLp Fact.out hp (Lp.memLp u) ν r)

/-- `S_ν(0) = I` on `L^p`. -/
theorem freeSemigroupLp_zero (hp : p ≠ ∞) (ν : ℝ) :
    freeSemigroupLp hp ν 0 = ContinuousLinearMap.id ℝ _ := by
  ext1 u
  rw [freeSemigroupLp_apply, ContinuousLinearMap.id_apply]
  simp only [freeEvolution_zero]
  exact Lp.toLp_coeFn u _

/-- The semigroup law `S_ν(r₁ + r₂) = S_ν(r₁) S_ν(r₂)` on `L^p` for `r₁, r₂ ≥ 0`. -/
theorem freeSemigroupLp_add (hp : p ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    freeSemigroupLp hp ν (r₁ + r₂) = (freeSemigroupLp hp ν r₁).comp (freeSemigroupLp hp ν r₂) := by
  ext1 u
  rw [ContinuousLinearMap.comp_apply, freeSemigroupLp_apply, freeSemigroupLp_apply]
  apply MemLp.toLp_congr
  have h := freeEvolution_congr_ae (coeFn_freeSemigroupLp hp ν r₂ u) ν r₁
  rw [freeEvolution_add hν hr₁ hr₂ Fact.out hp (Lp.memLp u)] at h
  exact h.symm

/-- Operator bound `‖S_ν(r)‖_{L^p → L^p} ≤ e^{-γ_p r}`. -/
theorem norm_freeSemigroupLp_le (hp : p ≠ ∞) (ν r : ℝ) :
    ‖freeSemigroupLp hp ν r‖ ≤ Real.exp (-gammaExp p * r) :=
  LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _

/-- Strong continuity: every orbit `r ↦ S_ν(r)u` is continuous on `[0, ∞)` in `L^p`. -/
theorem continuousOn_freeSemigroupLp (hp : p ≠ ∞) {ν : ℝ} (hν : 0 ≤ ν)
    (u : Lp Space p (volume : Measure Space)) :
    ContinuousOn (fun r => freeSemigroupLp hp ν r u) (Ici 0) := by
  intro r₀ hr₀
  change Tendsto _ _ _
  rw [tendsto_iff_edist_tendsto_0]
  simp only [freeSemigroupLp_apply, Lp.edist_toLp_toLp]
  exact tendsto_freeEvolution hν Fact.out hp (Lp.memLp u) hr₀

end UnforcedLeray.B0418
