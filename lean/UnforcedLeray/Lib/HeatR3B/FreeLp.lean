import UnforcedLeray.Units.B0419
import UnforcedLeray.Lib.HeatR3
import UnforcedLeray.Analysis.Heat.SelfAdjoint

/-!
# The free similarity semigroup on `L^p(ℝ³)` and its `L²` adjoint (INF04 T6)


(block 3B HEAT-R3 of `scoping/README.md` §5). Manuscript `paper/main.tex`:

* tex 7411–7427 (`eq:free-stress-7`, `eq:free-stress-8`; blueprint B0418, B0419):
  `S_ν(r)h(y) = e^{r/2}[e^{ν(e^r-1)Δ}h](e^{r/2}y)` is a strongly continuous semigroup on
  `L^q(ℝ³)`, `1 ≤ q < ∞`, with `‖S_ν(r)‖_{L^q → L^q} ≤ e^{-γ_q r}`, `γ_q = (3/q - 1)/2`;
* tex 5207–5216 (`background:eq:2.18`, B0420): the same operator `S_0(t)` on `L^p`, `1 < p < 3`;
* tex 7753–7762 (`eq:free-stress-26`, B0470): the `L²(ℝ³)` adjoint is
  `S_ν(r)^*h(y) = e^{-r}[e^{ν(1-e^{-r})Δ}h](e^{-r/2}y)`, of norm at most `e^{-r/4}`.

The semigroup itself was drafted as unit B0418/B0419

re-exports it under the T6 names, identifies its heat factor with the frozen interface
`heatLp` (D17), and proves the adjoint formula (new).

Main declarations:
* `freeEvolutionLp`, `freeEvolutionLp_rep`, `norm_freeEvolutionLp_le`, `freeEvolutionLp_add`,
  `freeEvolutionLp_continuousOn` (re-exports of B0418/B0419);
* `freeEvolutionLp_rep_heatLp`: `S_ν(r)u = e^{r/2}(heatLp (ν(e^r-1)) u)(e^{r/2}·)` a.e.;
* `freeAdjoint` (the field formula of `eq:free-stress-26`), `integral_inner_freeEvolution`
  (the defining pairing identity), `adjoint_freeEvolutionLp_rep` (the Hilbert adjoint of
  `S_ν(r)` on `L²` is represented by `freeAdjoint`), `norm_adjoint_freeEvolutionLp_le`
  (`‖S_ν(r)^*‖ ≤ e^{-r/4}`).

Conventions. `ν` is written `h` (the diffusivity, any real; the manuscript has `ν > 0`). The heat
factor is the library `Heat.flow`, which is the identity at nonpositive times; the adjoint
formula holds for every `h, r` because both heat times `h(e^r-1)` and `h(1-e^{-r}) = e^{-r}h(e^r-1)`
have the same sign. The bound `e^{-γ_p r}` is stated with `p ≠ ∞`, so `p.toReal` is the exponent.
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Heat

open MeasureTheory Filter Set Topology
open scoped ENNReal RealInnerProductSpace
open UnforcedLeray.AncientLocalization

/-! ### The semigroup on `L^p` (re-export of B0418/B0419) -/

section Lp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **INF04 T6 `freeEvolutionLp`** (tex 7411–7417, B0418). The free similarity semigroup
`S_h(r)` on `L^p(ℝ³; ℝ³)`, `1 ≤ p < ∞`: the drafted unit operator `B0418.freeSemigroupLp`. -/
abbrev freeEvolutionLp (hp : p ≠ ∞) (h r : ℝ) :
    Lp Space p (volume : Measure Space) →L[ℝ] Lp Space p (volume : Measure Space) :=
  B0418.freeSemigroupLp hp h r

/-- **INF04 T6 `freeEvolutionLp_rep`.** `S_h(r)u` is represented by the literal formula
`e^{r/2}[e^{h(e^r-1)Δ}u](e^{r/2}y)` (tex 7414–7417). -/
theorem freeEvolutionLp_rep (hp : p ≠ ∞) (h r : ℝ) (u : Lp Space p (volume : Measure Space)) :
    (freeEvolutionLp hp h r u : SpatialField) =ᵐ[volume] freeEvolution h r u :=
  B0418.coeFn_freeSemigroupLp hp h r u

/-- **INF04 T6 `norm_freeEvolutionLp_le`** (`eq:free-stress-8`, tex 7420–7425, B0419; also
`background:eq:2.18`, B0420): `‖S_h(r)‖_{L^p → L^p} ≤ e^{-γ_p r}`, `γ_p = (3/p - 1)/2`. -/
theorem norm_freeEvolutionLp_le (hp : p ≠ ∞) (h r : ℝ) :
    ‖freeEvolutionLp hp h r‖ ≤ Real.exp (-((3 / p.toReal - 1) / 2) * r) :=
  B0418.norm_freeSemigroupLp_le hp h r

/-- **INF04 T6 `freeEvolutionLp_add`.** The semigroup law for `h ≥ 0`, `r, r' ≥ 0`. -/
theorem freeEvolutionLp_add (hp : p ≠ ∞) {h : ℝ} (hh : 0 ≤ h) {r r' : ℝ} (hr : 0 ≤ r)
    (hr' : 0 ≤ r') :
    freeEvolutionLp hp h (r + r') = (freeEvolutionLp hp h r).comp (freeEvolutionLp hp h r') :=
  B0418.freeSemigroupLp_add hp hh hr hr'

/-- `S_h(0) = I`. -/
theorem freeEvolutionLp_zero (hp : p ≠ ∞) (h : ℝ) :
    freeEvolutionLp hp h 0 = ContinuousLinearMap.id ℝ _ :=
  B0418.freeSemigroupLp_zero hp h

/-- **INF04 T6 `freeEvolutionLp_continuousOn`.** Strong continuity on `[0, ∞)` for `h ≥ 0`
(tex 7427, "It is strongly continuous"). -/
theorem freeEvolutionLp_continuousOn (hp : p ≠ ∞) {h : ℝ} (hh : 0 ≤ h)
    (u : Lp Space p (volume : Measure Space)) :
    ContinuousOn (fun r => freeEvolutionLp hp h r u) (Ici 0) :=
  B0418.continuousOn_freeSemigroupLp hp hh u

/-- The heat factor of `S_h(r)` through the frozen interface `heatLp` (D17): for every `θ`,
`heatLp θ u` is represented by the library flow `Heat.flow u θ`. -/
theorem heatLp_space_rep_flow (θ : ℝ) (u : Lp Space p (volume : Measure Space)) :
    (heatLp (AddMonoidHom.id Space) continuous_id θ u : SpatialField) =ᵐ[volume]
      Heat.flow (u : SpatialField) θ := by
  by_cases hθ : 0 < θ
  · have h1 := heatLp_rep (AddMonoidHom.id Space) continuous_id hθ u
    rw [heatConv_space_eq_average] at h1
    rw [Heat.flow_pos _ hθ]
    exact h1
  · rw [heatLp_of_nonpos _ _ (not_lt.mp hθ), Heat.flow_nonpos _ (not_lt.mp hθ)]
    rfl

/-- **INF04 T6, heat factor via `heatLp`.** `S_h(r)u = e^{r/2}(heatLp (h(e^r-1)) u)(e^{r/2}·)`
almost everywhere (tex 7414–7417, D17). -/
theorem freeEvolutionLp_rep_heatLp (hp : p ≠ ∞) (h r : ℝ)
    (u : Lp Space p (volume : Measure Space)) :
    (freeEvolutionLp hp h r u : SpatialField) =ᵐ[volume] fun y =>
      Real.exp (r / 2) • (heatLp (AddMonoidHom.id Space) continuous_id (h * (Real.exp r - 1)) u :
        SpatialField) (Real.exp (r / 2) • y) := by
  refine (freeEvolutionLp_rep hp h r u).trans ?_
  have h2 := SpatialScaling.ae_eq_spatialScale (heatLp_space_rep_flow (h * (Real.exp r - 1)) u)
    (Real.exp (r / 2)) (Real.exp_pos (r / 2)).ne'
  exact h2.symm

end Lp

/-! ### The `L²` adjoint (`eq:free-stress-26`) -/

/-- **INF04 T6 `freeAdjoint`** (`eq:free-stress-26`, tex 7757–7759, B0470). The field formula
`S_h(r)^*g(y) = e^{-r}[e^{h(1-e^{-r})Δ}g](e^{-r/2}y)`. -/
def freeAdjoint (h r : ℝ) (g : SpatialField) : SpatialField :=
  SpatialScaling.spatialScale (Real.exp (-r)) (Real.exp (-r / 2))
    (Heat.flow g (h * (1 - Real.exp (-r))))

theorem freeAdjoint_apply (h r : ℝ) (g : SpatialField) (y : Space) :
    freeAdjoint h r g y =
      Real.exp (-r) • Heat.flow g (h * (1 - Real.exp (-r))) (Real.exp (-r / 2) • y) := rfl

theorem freeAdjoint_memLp {g : SpatialField} (hg : MemLp g 2 volume) (h r : ℝ) :
    MemLp (freeAdjoint h r g) 2 volume :=
  SpatialScaling.memLp_spatialScale (Heat.flow_memLp hg _) _ (Real.exp_pos _).ne'

/-- The `L²` norm of the adjoint formula: `‖S_h(r)^*g‖₂ ≤ e^{-r/4}‖g‖₂` (tex 7760). -/
theorem l2Norm_freeAdjoint_le {g : SpatialField} (hg : MemLp g 2 volume) (h r : ℝ) :
    l2Norm (freeAdjoint h r g) ≤ Real.exp (-r / 4) * l2Norm g := by
  have hd : 0 < Real.exp (-r / 2) := Real.exp_pos _
  unfold freeAdjoint
  rw [SpatialScaling.l2Norm_spatialScale _ (Heat.flow_memLp hg _) _ hd,
    abs_of_pos (Real.exp_pos _)]
  have hpow : Real.exp (-r / 2) ^ (-3 / 2 : ℝ) = Real.exp (3 * r / 4) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hpow, ← Real.exp_add, show -r + 3 * r / 4 = -r / 4 by ring]
  exact mul_le_mul_of_nonneg_left (Heat.flow_l2Norm_le hg _) (Real.exp_pos _).le

/-- Field-level self-adjointness of the heat flow on `L²`. -/
theorem integral_inner_flow_comm {f g : SpatialField} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (θ : ℝ) :
    ∫ x, ⟪Heat.flow f θ x, g x⟫ = ∫ x, ⟪f x, Heat.flow g θ x⟫ := by
  have e1 : ⟪toL2 (Heat.flow f θ), toL2 g⟫ = ∫ x, ⟪Heat.flow f θ x, g x⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 (Heat.flow_memLp hf θ), coeFn_toL2 hg] with x h1 h2
    rw [h1, h2]
  have e2 : ⟪toL2 f, toL2 (Heat.flow g θ)⟫ = ∫ x, ⟪f x, Heat.flow g θ x⟫ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hf, coeFn_toL2 (Heat.flow_memLp hg θ)] with x h1 h2
    rw [h1, h2]
  rw [← e1, ← e2, Heat.toL2_flow hf, Heat.toL2_flow hg]
  exact Heat.heatOperator_inner θ (toL2 f) (toL2 g)

/-- Dilation of the heat flow: `e^{θΔ}[g(λ·)] = (e^{λ²θΔ}g)(λ·)` for `λ > 0` and every real `θ`
(both flows are the identity when `θ ≤ 0`). -/
theorem flow_comp_smul {lam : ℝ} (hlam : 0 < lam) (θ : ℝ) (g : SpatialField) :
    Heat.flow (fun x => g (lam • x)) θ = fun x => Heat.flow g (lam ^ 2 * θ) (lam • x) := by
  by_cases hθ : 0 < θ
  · rw [Heat.flow_pos _ hθ, Heat.flow_pos _ (by positivity)]
    exact average_dilate hlam hθ g
  · have hθ' : lam ^ 2 * θ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hθ)
    rw [Heat.flow_nonpos _ (not_lt.mp hθ)]
    funext x
    rw [Heat.flow_nonpos _ hθ']

/-- **The pairing identity behind `eq:free-stress-26`** (tex 7753–7762): for `f, g ∈ L²(ℝ³)`,
`∫ ⟨S_h(r)f, g⟩ = ∫ ⟨f, S_h(r)^*g⟩`, every `h, r`. -/
theorem integral_inner_freeEvolution {f g : SpatialField} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h r : ℝ) :
    ∫ y, ⟪freeEvolution h r f y, g y⟫ = ∫ y, ⟪f y, freeAdjoint h r g y⟫ := by
  set lam : ℝ := Real.exp (r / 2) with hlam_def
  have hlam : 0 < lam := Real.exp_pos _
  set θ : ℝ := h * (Real.exp r - 1) with hθ_def
  set F : SpatialField := Heat.flow f θ with hF
  have hinv : lam⁻¹ = Real.exp (-r / 2) := by
    rw [hlam_def, ← Real.exp_neg]; congr 1; ring
  have hsq : lam ^ 2 = Real.exp r := by
    rw [hlam_def, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- Step 1: change of variables `x = λ y`.
  set Φ : Space → ℝ := fun x => ⟪lam • F x, g (lam⁻¹ • x)⟫ with hΦ
  have hstep1 : ∫ y, ⟪freeEvolution h r f y, g y⟫ = (lam ^ 3)⁻¹ * ∫ x, Φ x := by
    have hcv := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) Φ lam
      (hR := hlam.le)
    have hd : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [hd, smul_eq_mul] at hcv
    rw [← hcv]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hΦ, B0418.freeEvolution_apply, hF, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    rfl
  -- Step 2: pull out `λ` and use self-adjointness of the heat flow.
  set gt : SpatialField := fun x => g (lam⁻¹ • x) with hgt
  have hgt2 : MemLp gt 2 volume :=
    SpatialScaling.memLp_comp_dilation hg (inv_ne_zero hlam.ne')
  have hstep2 : ∫ x, Φ x = lam * ∫ x, ⟪f x, Heat.flow gt θ x⟫ := by
    have : (fun x => Φ x) = fun x => lam * ⟪F x, gt x⟫ := by
      funext x
      simp only [hΦ, hgt, real_inner_smul_left]
    rw [this, integral_const_mul, hF, integral_inner_flow_comm hf hgt2 θ]
  -- Step 3: the dilation identity for the heat flow.
  have hθ' : lam⁻¹ ^ 2 * θ = h * (1 - Real.exp (-r)) := by
    rw [inv_pow, hsq, hθ_def, Real.exp_neg]
    field_simp
  have hflow : Heat.flow gt θ = fun x => Heat.flow g (h * (1 - Real.exp (-r))) (lam⁻¹ • x) := by
    rw [hgt, flow_comp_smul (inv_pos.mpr hlam) θ g, hθ']
  rw [hstep1, hstep2, hflow, ← mul_assoc, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [freeAdjoint_apply, real_inner_smul_right, hinv]
  have hc : (lam ^ 3)⁻¹ * lam = Real.exp (-r) := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hlam.ne', mul_one, hsq, Real.exp_neg]
  rw [hc]

/-- **INF04 T6 `freeEvolution_adjoint`** (`eq:free-stress-26`, tex 7753–7762, B0470). On
`L²(ℝ³)` the Hilbert adjoint of `S_h(r)` is the class of the explicit formula
`S_h(r)^*g(y) = e^{-r}[e^{h(1-e^{-r})Δ}g](e^{-r/2}y)`. -/
theorem adjoint_freeEvolutionLp_eq (h r : ℝ) (g : L2Space) :
    ContinuousLinearMap.adjoint (freeEvolutionLp (p := 2) ENNReal.ofNat_ne_top h r) g =
      toL2 (freeAdjoint h r g) := by
  have hg : MemLp (g : SpatialField) 2 volume := Lp.memLp g
  have hA : MemLp (freeAdjoint h r g) 2 volume := freeAdjoint_memLp hg h r
  refine ext_inner_left ℝ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, L2.inner_def, L2.inner_def]
  have hv : MemLp (v : SpatialField) 2 volume := Lp.memLp v
  have e1 : ∫ a, ⟪(freeEvolutionLp (p := 2) ENNReal.ofNat_ne_top h r v : SpatialField) a,
      (g : SpatialField) a⟫ = ∫ a, ⟪freeEvolution h r v a, (g : SpatialField) a⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [freeEvolutionLp_rep (p := 2) ENNReal.ofNat_ne_top h r v] with a ha
    rw [ha]
  have e2 : ∫ a, ⟪(v : SpatialField) a, (toL2 (freeAdjoint h r g) : SpatialField) a⟫ =
      ∫ a, ⟪(v : SpatialField) a, freeAdjoint h r g a⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_toL2 hA] with a ha
    rw [ha]
  rw [e1, e2]
  exact integral_inner_freeEvolution hv hg h r

/-- The adjoint is represented by the field formula `freeAdjoint` (tex 7757–7759). -/
theorem adjoint_freeEvolutionLp_rep (h r : ℝ) (g : L2Space) :
    ((ContinuousLinearMap.adjoint (freeEvolutionLp (p := 2) ENNReal.ofNat_ne_top h r) g :
      L2Space) : SpatialField) =ᵐ[volume] freeAdjoint h r g := by
  rw [adjoint_freeEvolutionLp_eq]
  exact coeFn_toL2 (freeAdjoint_memLp (Lp.memLp g) h r)

/-- **INF04 T6 `freeEvolution_adjoint`, pairing form**: `⟪S_h(r)f, g⟫ = ⟪f, S_h(r)^*g⟫` on
`L²(ℝ³)`, every `h, r`. -/
theorem inner_freeEvolutionLp (h r : ℝ) (f g : L2Space) :
    ⟪freeEvolutionLp (p := 2) ENNReal.ofNat_ne_top h r f, g⟫ = ⟪f, toL2 (freeAdjoint h r g)⟫ := by
  rw [← adjoint_freeEvolutionLp_eq, ContinuousLinearMap.adjoint_inner_right]

/-- **INF04 T6, adjoint norm** (tex 7760, B0470): `‖S_h(r)^*‖_{L² → L²} ≤ e^{-r/4}`. -/
theorem norm_adjoint_freeEvolutionLp_le (h r : ℝ) :
    ‖ContinuousLinearMap.adjoint (freeEvolutionLp (p := 2) ENNReal.ofNat_ne_top h r)‖ ≤
      Real.exp (-r / 4) := by
  rw [LinearIsometryEquiv.norm_map]
  exact B0419.norm_freeSemigroupLp_two_le h r

end UnforcedLeray.Heat
