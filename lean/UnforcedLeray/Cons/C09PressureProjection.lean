import UnforcedLeray.Cons.C09PressureProjection.Poisson

/-!
# Step C9: from (2.5) with an `L²` pressure to the projected equation `loc:eq:background`

`PressureProjectionStep` (`Blueprint/Construction/Steps.lean`, line 380), blueprint unit
B0708 (`loc:eq:background`, the conversion from B0705's (2.5)); `paper/main.tex`
lines 107–110 (the convention `(u⊗v)_{ij} = u_iv_j`, `(div 𝕋)_i = ∂_j𝕋_{ij}`, `𝔓`),
lines 164–167 (`loc:eq:background`) and lines 13719–13733 (Theorem B3 supplies the background
of the construction). This is a general lemma: no data, no package.

**Statement proved (unconditionally).** Let `U(τ)` be solenoidal at every phase with
`U(τ)⊗U(τ)` in `L²` and `p(τ) ∈ L²` at every phase, and let `(U, p)` solve the unprojected
similarity equation (2.5) (`SolvesSimilarityNSWithPressure ν U p`). Then `U` solves the
literal projected equation `SolvesSimilarityBackground ν U`, where
`⟨𝔓 div(U⊗U), ψ⟩ = -Σ_j ⟨(U⊗U)_{·j}, 𝔓∂_jψ⟩` with the compiled `L²` Leray projection.

**Proof.**
1. (`Poisson.lean`) Testing (2.5) on `η(τ)∇Φ(y)` gives, at almost every phase and for every
   scalar test `Φ` (one null set, by separability of `(L²)³`, `Density.lean`), the Hessian
   relation `Σ_j ⟨G_j(τ), ∇∂_jΦ⟩ = 0`, `G_j = (U⊗U)_{·j} + p e_j`.
2. (`Cutoff.lean`) The relation extends to the Leray potential `Q = N ∗ div ψ(τ)` (compiled
   `RieszLp.lerayPotential`), whose value and first two derivatives decay like `(1+|y|)⁻²`.
3. (here) By the compiled test-level identity `(I - 𝔓)φ = -∇(N ∗ div φ)`
   (`RieszLp.toL2_sub_projection_vecField`), `(I - 𝔓)∂_jψ = -∇∂_jQ`, and `ΔQ = -div ψ`.
   Hence `∫ p div ψ = -Σ_j ⟨(U⊗U)_{·j}, (I-𝔓)∂_jψ⟩` at almost every phase, which is the
   phase-wise identity `⟨𝔓div(U⊗U), ψ⟩ = -∫(U·Dψ U + p div ψ) dy`
   (`projectedConvection_eq_of_relation`). Fubini on `ℝ × ℝ³` gives the integrability of
   the projected convection pairing and the projected weak form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal Topology

namespace UnforcedLeray.Cons.C09

open UnforcedLeray.Blueprint UnforcedLeray.RieszLp

/-- A slice of a similarity test is a compact smooth vector test. -/
theorem slice_smooth {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) (τ : ℝ) :
    ContDiff ℝ ∞ (slice ψ τ) :=
  hψ.smooth.comp (contDiff_const.prodMk contDiff_id)

theorem slice_compact {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) (τ : ℝ) :
    HasCompactSupport (slice ψ τ) :=
  hψ.compact.comp_isClosedEmbedding
    ⟨isEmbedding_prodMkRight τ, (isClosedMap_prodMk_left τ).isClosed_range⟩

/-- The components of a compact smooth vector field are compact smooth scalar tests. -/
theorem isSpatialTest_component {φ : Space → Space} (hφs : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (k : Fin 3) : IsSpatialTest (fun y => φ y k) where
  smooth := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) k).contDiff.comp hφs
  compact := hφc.comp_left (g := fun v : Space => v k) (by simp)

/-- `∂_j Σ_k g_k = Σ_k ∂_j g_k` for smooth functions. -/
theorem spatialTestDerivative_sum {g : Fin 3 → Space → ℝ} (hg : ∀ k, ContDiff ℝ ∞ (g k))
    (j : Fin 3) (x : Space) :
    spatialTestDerivative j (fun y => ∑ k : Fin 3, g k y) x =
      ∑ k : Fin 3, spatialTestDerivative j (g k) x := by
  unfold spatialTestDerivative
  rw [fderiv_fun_sum fun k _ => ((hg k).differentiable (by simp)) x]
  simp

theorem integrable_linearBackgroundIntegrand {ν : ℝ} {U : ℝ → SpatialField}
    {p : ℝ → Space → ℝ} (heq : SolvesSimilarityNSWithPressure ν U p) {ψ : SpaceTime → Space}
    (hψ : IsSimilarityTest ψ) : Integrable (linearBackgroundIntegrand ν U ψ) volume :=
  (((heq.temporal_integrable _ hψ).add ((heq.diffusion_integrable _ hψ).const_mul ν)).sub
    (heq.pair_integrable _ hψ)).sub ((heq.dilation_integrable _ hψ).const_mul (1 / 2 : ℝ))

/-- **The phase-wise identity.** At a phase where `U(τ)⊗U(τ)` and `p(τ)` are in `L²` and the
Hessian relation holds for every scalar test,
`⟨𝔓 div(U⊗U), ψ(τ)⟩ = -∫ U·Dψ U dy - ∫ p div ψ dy`. -/
theorem projectedConvection_eq_of_relation {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    {τ : ℝ} (hT : ColumnsL2 (tensorColumns (U τ) (U τ))) (hp : MemLp (p τ) 2 volume)
    (hrel : ∀ Φ, IsSpatialTest Φ → colPairing (stressL2 U p τ) (hessL2 Φ) = 0)
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    projectedConvection U ψ τ =
      -(∫ y, convectionTerm U ψ (τ, y)) - ∫ y, pressureSimilarityTerm p ψ (τ, y) := by
  set φ : Space → Space := slice ψ τ with hφdef
  have hφs : ContDiff ℝ ∞ φ := slice_smooth hψ τ
  have hφc : HasCompactSupport φ := slice_compact hψ τ
  set f : Fin 3 → Space → ℝ := fun k y => φ y k with hfdef
  have hf : ∀ k, IsSpatialTest (f k) := isSpatialTest_component hφs hφc
  set F : Fin 3 → Fin 3 → Space → ℝ := fun j k => spatialTestDerivative j (f k) with hFdef
  have hF : ∀ j k, IsSpatialTest (F j k) := fun j k => (hf k).derivative j
  set Q : Space → ℝ := lerayPotential f with hQdef
  have hQs : ContDiff ℝ ∞ Q := lerayPotential_contDiff hf
  -- `∂_jφ` is the vector field with components `∂_j f_k`
  have hD1 : ∀ j, testPartial φ j = vecField (F j) := by
    intro j
    funext y
    refine PiLp.ext fun i => ?_
    rw [vecField_apply]
    exact fderiv_apply_coord ((hφs.differentiable (by simp)) y) _ i
  -- the Leray potential of `∂_jφ` is `∂_jQ`
  have hD2 : ∀ j, lerayPotential (F j) = spatialTestDerivative j Q := by
    intro j
    have hdiv : divTest (F j) = spatialTestDerivative j (divTest f) := by
      funext x
      have hsum := spatialTestDerivative_sum (g := fun k => spatialTestDerivative k (f k))
        (fun k => ((hf k).derivative k).smooth) j x
      change ∑ k : Fin 3, spatialTestDerivative k (spatialTestDerivative j (f k)) x = _
      rw [show divTest f = fun y => ∑ k : Fin 3, spatialTestDerivative k (f k) y from rfl,
        hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [SobolevGraph.spatialTestDerivative_comm (hf k) k j]
    rw [hQdef, lerayPotential, lerayPotential,
      spatialTestDerivative_newtonConv (isSpatialTest_divTest hf) j, hdiv]
  -- decay of `Q` and its first two derivatives
  obtain ⟨M0, hM0a, hM0b⟩ := lerayPotential_decay hf
  choose Mj hMj using fun j => lerayPotential_decay (hF j)
  set M : ℝ := |M0| + ∑ j : Fin 3, |Mj j| with hMdef
  have hMs : ∀ j, 0 ≤ |Mj j| := fun j => abs_nonneg _
  have hM0le : M0 ≤ M := by
    have := Finset.sum_nonneg fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hMs j
    linarith [le_abs_self M0]
  have hMjle : ∀ j, Mj j ≤ M := by
    intro j
    have h1 : |Mj j| ≤ ∑ k : Fin 3, |Mj k| :=
      Finset.single_le_sum (f := fun k => |Mj k|) (fun k _ => hMs k) (Finset.mem_univ j)
    linarith [le_abs_self (Mj j), abs_nonneg M0]
  have h0 : ∀ x, |Q x| ≤ M * decayWeight x := fun x =>
    (hM0a x).trans (mul_le_mul_of_nonneg_right hM0le (decayWeight_pos x).le)
  have h1 : ∀ i x, |spatialTestDerivative i Q x| ≤ M * decayWeight x := fun i x =>
    (hM0b i x).trans (mul_le_mul_of_nonneg_right hM0le (decayWeight_pos x).le)
  have h2 : ∀ i j x, |spatialTestDerivative i (spatialTestDerivative j Q) x| ≤
      M * decayWeight x := by
    intro i j x
    rw [← hD2 j]
    exact ((hMj j).2 i x).trans (mul_le_mul_of_nonneg_right (hMjle j) (decayWeight_pos x).le)
  have hrelQ := colPairing_hessL2_of_decay hrel hQs h0 h1 h2
  -- `L²` memberships
  have hH : ∀ j, MemLp (gradField (spatialTestDerivative j Q)) 2 volume := fun j =>
    memLp_gradField (PressureAnalysis.contDiff_spatialTestDerivative hQs j)
      fun i x => h2 i j x
  have ha : ∀ j, MemLp (testPartial φ j) 2 volume := fun j => by
    rw [hD1 j]; exact memLp_vecField (hF j) 2
  have hP : ∀ j, MemLp (fun y => p τ y • coordinateVector j) 2 volume :=
    memLp_smul_coordinateVector hp
  -- `𝔓∂_jφ = ∂_jφ + ∇∂_jQ`
  have hproj : ∀ j, Leray.projection (toL2 (testPartial φ j)) =
      toL2 (testPartial φ j) + hessL2 Q j := by
    intro j
    have hD3 : toL2 (testPartial φ j) - Leray.projection (toL2 (testPartial φ j)) =
        -hessL2 Q j := by
      rw [hD1 j, toL2_sub_projection_vecField (hF j), hD2 j]
      rfl
    calc Leray.projection (toL2 (testPartial φ j))
        = toL2 (testPartial φ j) -
            (toL2 (testPartial φ j) - Leray.projection (toL2 (testPartial φ j))) :=
          (sub_sub_cancel _ _).symm
      _ = toL2 (testPartial φ j) + hessL2 Q j := by rw [hD3, sub_neg_eq_add]
  -- the convection pairing
  have hconv_pt : ∀ y, convectionTerm U ψ (τ, y) =
      ∑ j : Fin 3, inner ℝ (tensorColumns (U τ) (U τ) j y) (testPartial φ j y) := by
    intro y
    change inner ℝ (U τ y) (fderiv ℝ φ y (U τ y)) = _
    have hU : fderiv ℝ φ y (U τ y) = ∑ j : Fin 3, U τ y j • testPartial φ j y := by
      conv_lhs => rw [eq_sum_coordinateVector (U τ y)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      rfl
    rw [hU, inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, tensorColumns, real_inner_smul_left]
  have hconv : ∫ y, convectionTerm U ψ (τ, y) =
      ∑ j : Fin 3, inner ℝ (toL2 (tensorColumns (U τ) (U τ) j)) (toL2 (testPartial φ j)) := by
    simp_rw [hconv_pt]
    rw [integral_finset_sum _ fun j _ => integrable_inner_of_memLp (hT j) (ha j)]
    exact Finset.sum_congr rfl fun j _ => (inner_toL2_toL2 (hT j) (ha j)).symm
  -- the pressure pairing: `Σ_j ⟨p e_j, ∇∂_jQ⟩ = ∫ p ΔQ = -∫ p div ψ`
  have hdiv : ∀ y, spatialDivergence ψ τ y = divTest f y := by
    intro y
    simp only [spatialDivergence, divTest]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact fderiv_apply_coord ((hφs.differentiable (by simp)) y) _ i
  have hlap : ∀ y, ∑ j : Fin 3, spatialTestDerivative j (spatialTestDerivative j Q) y =
      -divTest f y := fun y => congrFun (laplacian_newtonConv (isSpatialTest_divTest hf)) y
  have hpres : ∑ j : Fin 3, inner ℝ (toL2 (fun y => p τ y • coordinateVector j)) (hessL2 Q j) =
      -∫ y, pressureSimilarityTerm p ψ (τ, y) := by
    calc ∑ j : Fin 3, inner ℝ (toL2 (fun y => p τ y • coordinateVector j)) (hessL2 Q j)
        = ∑ j : Fin 3, ∫ y, inner ℝ (p τ y • coordinateVector j)
            (gradField (spatialTestDerivative j Q) y) :=
          Finset.sum_congr rfl fun j _ => inner_toL2_toL2 (hP j) (hH j)
      _ = ∫ y, ∑ j : Fin 3, inner ℝ (p τ y • coordinateVector j)
            (gradField (spatialTestDerivative j Q) y) :=
          (integral_finset_sum _ fun j _ => integrable_inner_of_memLp (hP j) (hH j)).symm
      _ = ∫ y, -pressureSimilarityTerm p ψ (τ, y) := by
          congr 1
          funext y
          have hpt : ∀ j : Fin 3, inner ℝ (p τ y • coordinateVector j)
              (gradField (spatialTestDerivative j Q) y) =
                p τ y * spatialTestDerivative j (spatialTestDerivative j Q) y := fun j => by
            rw [inner_smul_coordinateVector, gradField_apply]
          rw [Finset.sum_congr rfl fun j _ => hpt j, ← Finset.mul_sum, hlap y]
          show p τ y * -divTest f y = -(p τ y * spatialDivergence ψ τ y)
          rw [hdiv y]
          ring
      _ = -∫ y, pressureSimilarityTerm p ψ (τ, y) := integral_neg _
  -- the Hessian relation for `Q`
  have hQrel : ∑ j : Fin 3, inner ℝ (toL2 (tensorColumns (U τ) (U τ) j)) (hessL2 Q j) +
      ∑ j : Fin 3, inner ℝ (toL2 (fun y => p τ y • coordinateVector j)) (hessL2 Q j) = 0 := by
    rw [← Finset.sum_add_distrib]
    have := hrelQ
    simp only [colPairing, stressL2, inner_add_left] at this
    exact this
  show -∑ j : Fin 3, inner ℝ (toL2 (tensorColumns (U τ) (U τ) j))
    (Leray.projection (toL2 (testPartial φ j))) = _
  simp only [hproj, inner_add_right, Finset.sum_add_distrib]
  rw [hconv]
  linarith

/-- The phase-wise identity, integrated: the projected convection pairing is integrable in
`τ` and `∫ ⟨𝔓div(U⊗U), ψ⟩ dτ = -∫∫ (U·Dψ U + p div ψ)`. -/
theorem projectedConvection_integral {ν : ℝ} {U : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    (hsol : ∀ τ, IsSolenoidal (U τ)) (hT : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hp : ∀ τ, MemLp (p τ) 2 volume) (heq : SolvesSimilarityNSWithPressure ν U p)
    {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    Integrable (projectedConvection U ψ) volume ∧
      ∫ τ, projectedConvection U ψ τ =
        -∫ z, (convectionTerm U ψ z + pressureSimilarityTerm p ψ z) := by
  have hgood := ae_forall_colPairing_stress_hess hsol hT hp heq
  have hc := heq.convection_integrable ψ hψ
  have hpr := heq.pressure_integrable ψ hψ
  have hcp : Integrable (fun z => convectionTerm U ψ z + pressureSimilarityTerm p ψ z)
      volume := hc.add hpr
  rw [Measure.volume_eq_prod] at hc hpr hcp
  have hae : projectedConvection U ψ =ᵐ[volume] fun τ =>
      -∫ y, (convectionTerm U ψ (τ, y) + pressureSimilarityTerm p ψ (τ, y)) := by
    filter_upwards [hgood, hc.prod_right_ae, hpr.prod_right_ae] with τ hτ hcτ hpτ
    rw [projectedConvection_eq_of_relation (hT τ) (hp τ) hτ hψ, integral_add hcτ hpτ]
    ring
  refine ⟨Integrable.congr ?_ hae.symm, ?_⟩
  · exact hcp.integral_prod_left.neg
  · rw [integral_congr_ae hae, integral_neg, Measure.volume_eq_prod, integral_prod _ hcp]

end UnforcedLeray.Cons.C09

namespace UnforcedLeray.Blueprint

open UnforcedLeray.Cons.C09

/-- **Step C9 is proved** (`PressureProjectionStep`, `Blueprint/Construction/Steps.lean`
line 380; blueprint unit B0708, the conversion from B0705's (2.5); `paper/main.tex`
lines 107–110, 164–167, 13719–13733). For a background solenoidal at every phase with
`U(τ)⊗U(τ) ∈ L²` and `p(τ) ∈ L²` at every phase, the unprojected similarity equation (2.5)
with pressure `p` implies the literal projected equation `loc:eq:background`
(`SolvesSimilarityBackground`), with every integrability clause. No hypothesis beyond the
step's own. -/
theorem pressureProjectionStep : PressureProjectionStep := by
  intro ν U p hsol hT hp heq
  refine ⟨hT, heq.temporal_integrable, heq.diffusion_integrable, heq.pair_integrable,
    heq.dilation_integrable, fun ψ hψ => (projectedConvection_integral hsol hT hp heq hψ).1,
    ?_⟩
  intro ψ hψ
  rw [(projectedConvection_integral hsol hT hp heq hψ).2]
  have hid := heq.identity ψ hψ
  have hlin_int := integrable_linearBackgroundIntegrand heq hψ
  have hcp : Integrable (fun z => convectionTerm U ψ z + pressureSimilarityTerm p ψ z)
      volume := (heq.convection_integrable ψ hψ).add (heq.pressure_integrable ψ hψ)
  have hsplit : ∫ z, (linearBackgroundIntegrand ν U ψ z + convectionTerm U ψ z +
      pressureSimilarityTerm p ψ z) =
      (∫ z, linearBackgroundIntegrand ν U ψ z) +
        ∫ z, (convectionTerm U ψ z + pressureSimilarityTerm p ψ z) := by
    rw [← integral_add hlin_int hcp]
    congr 1
    funext z
    ring
  linarith

end UnforcedLeray.Blueprint
