import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F2_3
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# `PartII-b:F2/4` (`Sub/PartII-b_F2_4.lean`): Decomposition of `CompactDuhamelBlockStep`

Source of record: `the November 2 reference manuscript` (SP), lines 841–852,
931–953, 978–1003, 2104–2115, 2145–2166 (`short-bg:compact-duhamel`).

This module provides:
1. `Jc_Rc_block_a_eq`, `norm_block_d_le_lifted`, `norm_block_b_le_lifted`, `norm_block_c_le_lifted`:
   lifting the four cylinder block operators on `Xmc c m` to the single ambient planar space `Xm m`
   via the zero-extension isometry `Jc c m` and restriction `Rc c m`;
2. `IsFrozenEulerPackage.planar_block_c_eq_zero` and `IsFrozenEulerPackage.exists_coord_approx`:
   exact vanishing of the planar lower-left block and uniform coordinate convergence;
3. `abstract_four_block_bounds`, `planar_blocks_of_weyl_factorization`,
   `four_block_bounds_of_lifted`, `PlanarCompactDuhamelComparison` and
   `compactDuhamelBlockStep_of_planarComparison`: reduction of the four block bounds in
   `CompactDuhamelBlockStep` to a planar comparison on `Xm m` (all moved from
   `Tasks/BlockFactorization/CompactDuhamelBlock.lean`);
4. The three leaf propositions of `PartII-b:F2/4`, following SP 2104–2115 and 2147–2155:
   * `FreeTransportComparison` (`PartII-b:F2/4/1`): the lifted free cylinder propagator
     composed with the inverse frozen radial transport, `W_{ν,t} = J_c S_c(t+L,t) R_c T_pl(νt,-L)`,
     converges strongly to the identity uniformly on compact sets, with `‖S_c(t+L,t)‖ ≤ 1 + o(1)`
     (data-level form `FreeTransportConverges`);
   * `PlanarDuhamelCollectiveCompact` (`PartII-b:F2/4/2`): the frozen planar Euler evolution is
     uniformly bounded on `[0, Sig] × [0, Lmax]` and its Duhamel terms `E_pl - T_pl` form a
     collectively compact family ("its limit is compact", SP 2150);
   * `CompactDuhamelNormConvergence` (`PartII-b:F2/4/3`): the lifted interaction Duhamel term
     `J_c (U(t+L,t) - S_c(t+L,t)) R_c` converges in operator norm to `E_pl(νt,L) - T_pl(νt,L)`
     (the compact-Duhamel lemma, SP 978–1003, 2147–2150);
5. The conditional assemblies `planarCompactDuhamelComparison_of` (the factorization
   `U_lift = W_{ν,t} E_pl(νt,L) + o(1)` of SP 2147–2150 fed into
   `planar_blocks_of_weyl_factorization`; strong adjoint convergence from the identity for
   `‖W* f - f‖²`, SP 2112–2113) and `compactDuhamelBlockStep_of`.

Once the three leaves are proved, `PartII-b:F2/4` is assembled in
`Tasks/BlockFactorization/CompactDuhamelBlock.lean` by
```lean
theorem compactDuhamelBlockStep_proof : UnforcedLeray.Short.IIb.CompactDuhamelBlockStep :=
  compactDuhamelBlockStep_of freeTransportComparison_proof
    planarDuhamelCollectiveCompact_proof compactDuhamelNormConvergence_proof
```
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## 1. Lifting cylinder blocks from `Xmc c m` to `Xm m` via `Jc` and `Rc` -/

theorem Rc_comp_Jc (c m : ℝ) :
    (Rc c m).comp (Jc c m) = ContinuousLinearMap.id ℝ (Xmc c m) :=
  ContinuousLinearMap.ext (Rc_Jc c m)

theorem norm_Jc_le (c m : ℝ) : ‖Jc c m‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    rw [norm_Jc_apply, one_mul]

/-- The growing-to-growing cylinder block `π_c₁ ∘ U ∘ ι_c₀` equals
`(π_c₁ ∘ Rc) ∘ (Jc ∘ U ∘ Rc) ∘ (Jc ∘ ι_c₀)`. -/
theorem Jc_Rc_block_a_eq (c m : ℝ)
    (π₁ : Xmc c m →L[ℝ] E2) (U : Xmc c m →L[ℝ] Xmc c m) (ι₀ : E2 →L[ℝ] Xmc c m) :
    π₁.comp (U.comp ι₀) =
      (π₁.comp (Rc c m)).comp (((Jc c m).comp (U.comp (Rc c m))).comp ((Jc c m).comp ι₀)) := by
  ext α
  simp only [ContinuousLinearMap.comp_apply, Rc_Jc]

/-- Lifting the cylinder projection `Pc = ι_c ∘ π_c` to `Xm m` conjugates `1 - Pc` by `Jc` and `Rc`:
for any `f : Xmc c m`, `Jc ((1 - Pc) f) = (1 - (Jc ∘ ι_c) ∘ (π_c ∘ Rc)) (Jc f)`. -/
theorem Jc_sub_proj_apply (c m : ℝ)
    (ι : E2 →L[ℝ] Xmc c m) (π : Xmc c m →L[ℝ] E2) (f : Xmc c m) :
    Jc c m ((ContinuousLinearMap.id ℝ (Xmc c m) - ι.comp π) f) =
      (ContinuousLinearMap.id ℝ (Xm m) - ((Jc c m).comp ι).comp (π.comp (Rc c m))) (Jc c m f) := by
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_sub, Rc_Jc]

/-- Operator-norm bound for the complementary cylinder block `(1 - Pc₁) ∘ U ∘ (1 - Pc₀)` in terms
of the lifted operators on `Xm m`. -/
theorem norm_block_d_le_lifted (c m : ℝ)
    (ι₀ ι₁ : E2 →L[ℝ] Xmc c m) (π₀ π₁ : Xmc c m →L[ℝ] E2)
    (U : Xmc c m →L[ℝ] Xmc c m) :
    let Pc₀ : Xmc c m →L[ℝ] Xmc c m := ι₀.comp π₀
    let Pc₁ : Xmc c m →L[ℝ] Xmc c m := ι₁.comp π₁
    let P₀_lift : Xm m →L[ℝ] Xm m := ((Jc c m).comp ι₀).comp (π₀.comp (Rc c m))
    let P₁_lift : Xm m →L[ℝ] Xm m := ((Jc c m).comp ι₁).comp (π₁.comp (Rc c m))
    let U_lift : Xm m →L[ℝ] Xm m := (Jc c m).comp (U.comp (Rc c m))
    ‖(ContinuousLinearMap.id ℝ (Xmc c m) - Pc₁).comp
        (U.comp (ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀))‖ ≤
      ‖(ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp
        (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))‖ := by
  intro Pc₀ Pc₁ P₀_lift P₁_lift U_lift
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have h1 :
      Jc c m (((ContinuousLinearMap.id ℝ (Xmc c m) - Pc₁).comp
        (U.comp (ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀))) f) =
      ((ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp
        (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))) (Jc c m f) := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [Jc_sub_proj_apply, ← Rc_Jc c m ((ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀) f),
      Jc_sub_proj_apply]
    rfl
  rw [← norm_Jc_apply c m, h1]
  calc ‖((ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp
          (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))) (Jc c m f)‖
      ≤ ‖(ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp
          (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))‖ * ‖Jc c m f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp
          (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))‖ * ‖f‖ := by
        rw [norm_Jc_apply]

/-- Operator-norm bound for the upper-right cylinder block `π₁ ∘ U ∘ (1 - Pc₀)` in terms of the
lifted operators on `Xm m`. -/
theorem norm_block_b_le_lifted (c m : ℝ)
    (ι₀ : E2 →L[ℝ] Xmc c m) (π₀ π₁ : Xmc c m →L[ℝ] E2)
    (U : Xmc c m →L[ℝ] Xmc c m) :
    let Pc₀ : Xmc c m →L[ℝ] Xmc c m := ι₀.comp π₀
    let P₀_lift : Xm m →L[ℝ] Xm m := ((Jc c m).comp ι₀).comp (π₀.comp (Rc c m))
    let U_lift : Xm m →L[ℝ] Xm m := (Jc c m).comp (U.comp (Rc c m))
    ‖π₁.comp (U.comp (ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀))‖ ≤
      ‖(π₁.comp (Rc c m)).comp (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))‖ := by
  intro Pc₀ P₀_lift U_lift
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
  have h1 :
      (π₁.comp (U.comp (ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀))) f =
      ((π₁.comp (Rc c m)).comp (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift)))
        (Jc c m f) := by
    dsimp only [Pc₀, P₀_lift, U_lift]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← Jc_sub_proj_apply c m ι₀ π₀ f, Rc_Jc, Rc_Jc]
  rw [h1]
  calc ‖((π₁.comp (Rc c m)).comp (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift)))
          (Jc c m f)‖
      ≤ ‖(π₁.comp (Rc c m)).comp (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))‖ *
          ‖Jc c m f‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖(π₁.comp (Rc c m)).comp (U_lift.comp (ContinuousLinearMap.id ℝ (Xm m) - P₀_lift))‖ *
          ‖f‖ := by
        rw [norm_Jc_apply]

/-- Operator-norm bound for the lower-left cylinder block `(1 - Pc₁) ∘ U ∘ ι₀` in terms of the
lifted operators on `Xm m`. -/
theorem norm_block_c_le_lifted (c m : ℝ)
    (ι₀ ι₁ : E2 →L[ℝ] Xmc c m) (π₁ : Xmc c m →L[ℝ] E2)
    (U : Xmc c m →L[ℝ] Xmc c m) :
    let Pc₁ : Xmc c m →L[ℝ] Xmc c m := ι₁.comp π₁
    let P₁_lift : Xm m →L[ℝ] Xm m := ((Jc c m).comp ι₁).comp (π₁.comp (Rc c m))
    let U_lift : Xm m →L[ℝ] Xm m := (Jc c m).comp (U.comp (Rc c m))
    ‖(ContinuousLinearMap.id ℝ (Xmc c m) - Pc₁).comp (U.comp ι₀)‖ ≤
      ‖(ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp (U_lift.comp ((Jc c m).comp ι₀))‖ := by
  intro Pc₁ P₁_lift U_lift
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun α => ?_
  have h1 :
      Jc c m (((ContinuousLinearMap.id ℝ (Xmc c m) - Pc₁).comp (U.comp ι₀)) α) =
      ((ContinuousLinearMap.id ℝ (Xm m) - P₁_lift).comp (U_lift.comp ((Jc c m).comp ι₀))) α := by
    dsimp only [Pc₁, P₁_lift, U_lift]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Jc_sub_proj_apply, Rc_Jc]
  rw [← norm_Jc_apply c m, h1]
  exact ContinuousLinearMap.le_opNorm _ α

/-! ## 2. Planar eigenmode invariance and uniform coordinate convergence from `IsFrozenEulerPackage` -/

/-- From `IsFrozenEulerPackage.euler_eigen` and `IsFrozenEulerPackage.pl_proj_id`, the planar
lower-left block `(1 - ι_pl σ ∘ π_pl σ) ∘ E_pl σ τ ∘ ι_pl σ` vanishes identically for all
`σ ∈ Icc 0 Sig` and `0 ≤ τ`. -/
theorem IsFrozenEulerPackage.planar_block_c_eq_zero
    {m Sig : ℝ} {lam : ℂ} {q : Blueprint.Planar.Profile}
    {L₀ M_E c₀ : ℝ}
    {ι_pl : ℝ → (E2 →L[ℝ] Xm m)} {π_pl : ℝ → (Xm m →L[ℝ] E2)}
    {E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    {ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m)}
    {π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)}
    (hPkg : IsFrozenEulerPackage m Sig lam q L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c)
    {σ τ : ℝ} (hσ : σ ∈ Icc 0 Sig) (hτ : 0 ≤ τ) :
    (ContinuousLinearMap.id ℝ (Xm m) - (ι_pl σ).comp (π_pl σ)).comp
      ((E_pl σ τ).comp (ι_pl σ)) = 0 := by
  have heig := hPkg.euler_eigen σ hσ τ hτ
  have hproj := (hPkg.pl_proj_id σ hσ).1
  rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_assoc, heig,
    ← ContinuousLinearMap.comp_assoc (π_pl σ) (ι_pl σ), hproj,
    ContinuousLinearMap.id_comp, sub_self]

/-- Product-difference bound `‖A₁ ∘ B₁ - A₀ ∘ B₀‖ ≤ ‖A₁ - A₀‖ * ‖B₁‖ + ‖A₀‖ * ‖B₁ - B₀‖`. -/
theorem norm_comp_sub_comp_le
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A₁ A₀ : Y →L[ℝ] Z) (B₁ B₀ : X →L[ℝ] Y) :
    ‖A₁.comp B₁ - A₀.comp B₀‖ ≤ ‖A₁ - A₀‖ * ‖B₁‖ + ‖A₀‖ * ‖B₁ - B₀‖ := by
  have hdecomp : A₁.comp B₁ - A₀.comp B₀ = (A₁ - A₀).comp B₁ + A₀.comp (B₁ - B₀) := by
    ext x
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add
    (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

/-- Uniform continuity of `ι_pl` and `π_pl` on `Icc 0 Sig` combined with `coord_conv` yields
simultaneous approximation of `ι_pl σ₀`, `π_pl σ₀`, and `Ppl₀ = ι_pl σ₀ ∘ π_pl σ₀` by the lifted
cylinder coordinates at both endpoints `σ₀ = ν * t` and `σ₁ = ν * (t + L)`. -/
theorem IsFrozenEulerPackage.exists_coord_approx
    {m Sig : ℝ} {lam : ℂ} {q : Blueprint.Planar.Profile}
    {L₀ M_E c₀ : ℝ}
    {ι_pl : ℝ → (E2 →L[ℝ] Xm m)} {π_pl : ℝ → (Xm m →L[ℝ] E2)}
    {E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)}
    {ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m)}
    {π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)}
    (hPkg : IsFrozenEulerPackage m Sig lam q L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c)
    {η : ℝ} (hη : 0 < η) :
    ∃ (c₁ ν₁ : ℝ), c₀ ≤ c₁ ∧ 0 < ν₁ ∧ ν₁ ≤ 1 ∧
      ∀ (c ν : ℝ), c₁ ≤ c → 0 < ν → ν ≤ ν₁ →
      ∀ (σ₀ σ₁ : ℝ), σ₀ ∈ Icc 0 Sig → σ₁ ∈ Icc 0 Sig → |σ₁ - σ₀| ≤ 2 * L₀ * ν →
        let ι₀_lift : E2 →L[ℝ] Xm m := (Jc c m).comp (ι_c c σ₀)
        let π₀_lift : Xm m →L[ℝ] E2 := (π_c c σ₀).comp (Rc c m)
        let ι₁_lift : E2 →L[ℝ] Xm m := (Jc c m).comp (ι_c c σ₁)
        let π₁_lift : Xm m →L[ℝ] E2 := (π_c c σ₁).comp (Rc c m)
        let P₀_lift : Xm m →L[ℝ] Xm m := ι₀_lift.comp π₀_lift
        let P₁_lift : Xm m →L[ℝ] Xm m := ι₁_lift.comp π₁_lift
        let Ppl₀ : Xm m →L[ℝ] Xm m := (ι_pl σ₀).comp (π_pl σ₀)
        ‖ι₀_lift - ι_pl σ₀‖ ≤ η ∧
        ‖π₀_lift - π_pl σ₀‖ ≤ η ∧
        ‖ι₁_lift - ι_pl σ₀‖ ≤ η ∧
        ‖π₁_lift - π_pl σ₀‖ ≤ η ∧
        ‖P₀_lift - Ppl₀‖ ≤ 2 * M_E * η ∧
        ‖P₁_lift - Ppl₀‖ ≤ 2 * M_E * η := by
  have hM_E : 1 ≤ M_E := hPkg.M_E_ge_one
  have hL₀ : 1 ≤ L₀ := hPkg.L₀_ge_one
  have hη2 : 0 < η / 2 := half_pos hη
  obtain ⟨c₁, hc₁, hconv⟩ := hPkg.coord_conv (η / 2) hη2
  have hu_ι : UniformContinuousOn ι_pl (Icc 0 Sig) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hPkg.pl_cont.1
  have hu_π : UniformContinuousOn π_pl (Icc 0 Sig) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hPkg.pl_cont.2
  obtain ⟨δ_ι, hδ_ι_pos, hδ_ι⟩ := Metric.uniformContinuousOn_iff.1 hu_ι (η / 2) hη2
  obtain ⟨δ_π, hδ_π_pos, hδ_π⟩ := Metric.uniformContinuousOn_iff.1 hu_π (η / 2) hη2
  set δ_σ : ℝ := min δ_ι δ_π
  have hδ_σ_pos : 0 < δ_σ := lt_min hδ_ι_pos hδ_π_pos
  set ν₁ : ℝ := min 1 (δ_σ / (4 * L₀))
  have hν₁_pos : 0 < ν₁ := lt_min zero_lt_one (by positivity)
  have hν₁_le_1 : ν₁ ≤ 1 := min_le_left _ _
  refine ⟨c₁, ν₁, hc₁, hν₁_pos, hν₁_le_1, ?_⟩
  intro c ν hc hν_pos hν_le σ₀ σ₁ hσ₀ hσ₁ hdiff ι₀_lift π₀_lift ι₁_lift π₁_lift P₀_lift P₁_lift Ppl₀
  have hconv₀ := hconv c hc σ₀ hσ₀
  have hconv₁ := hconv c hc σ₁ hσ₁
  have hdist_lt : dist σ₁ σ₀ < δ_σ := by
    rw [Real.dist_eq]
    have h1 : 2 * L₀ * ν ≤ 2 * L₀ * (δ_σ / (4 * L₀)) := by
      refine mul_le_mul_of_nonneg_left (hν_le.trans (min_le_right _ _)) (by positivity)
    have h2 : 2 * L₀ * (δ_σ / (4 * L₀)) = δ_σ / 2 := by
      field_simp [(by positivity : (0 : ℝ) < L₀).ne']
      ring
    linarith
  have hι_diff : ‖ι_pl σ₁ - ι_pl σ₀‖ ≤ η / 2 := by
    rw [← dist_eq_norm]
    exact (hδ_ι σ₁ hσ₁ σ₀ hσ₀ (hdist_lt.trans_le (min_le_left _ _))).le
  have hπ_diff : ‖π_pl σ₁ - π_pl σ₀‖ ≤ η / 2 := by
    rw [← dist_eq_norm]
    exact (hδ_π σ₁ hσ₁ σ₀ hσ₀ (hdist_lt.trans_le (min_le_right _ _))).le
  have hι₀ : ‖ι₀_lift - ι_pl σ₀‖ ≤ η := hconv₀.1.trans (by linarith)
  have hπ₀ : ‖π₀_lift - π_pl σ₀‖ ≤ η := hconv₀.2.trans (by linarith)
  have hι₁ : ‖ι₁_lift - ι_pl σ₀‖ ≤ η := by
    calc ‖ι₁_lift - ι_pl σ₀‖
        = ‖(ι₁_lift - ι_pl σ₁) + (ι_pl σ₁ - ι_pl σ₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖ι₁_lift - ι_pl σ₁‖ + ‖ι_pl σ₁ - ι_pl σ₀‖ := norm_add_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hconv₁.1 hι_diff
      _ = η := add_halves η
  have hπ₁ : ‖π₁_lift - π_pl σ₀‖ ≤ η := by
    calc ‖π₁_lift - π_pl σ₀‖
        = ‖(π₁_lift - π_pl σ₁) + (π_pl σ₁ - π_pl σ₀)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖π₁_lift - π_pl σ₁‖ + ‖π_pl σ₁ - π_pl σ₀‖ := norm_add_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add hconv₁.2 hπ_diff
      _ = η := add_halves η
  have hπ₀_lift_norm : ‖π₀_lift‖ ≤ M_E := by
    calc ‖(π_c c σ₀).comp (Rc c m)‖
        ≤ ‖π_c c σ₀‖ * ‖Rc c m‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_E * 1 := mul_le_mul (hPkg.cyl_norm c (hc₁.trans hc) σ₀ hσ₀).2
          (norm_Rc_le c m) (norm_nonneg _) (by positivity)
      _ = M_E := mul_one M_E
  have hπ₁_lift_norm : ‖π₁_lift‖ ≤ M_E := by
    calc ‖(π_c c σ₁).comp (Rc c m)‖
        ≤ ‖π_c c σ₁‖ * ‖Rc c m‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_E * 1 := mul_le_mul (hPkg.cyl_norm c (hc₁.trans hc) σ₁ hσ₁).2
          (norm_Rc_le c m) (norm_nonneg _) (by positivity)
      _ = M_E := mul_one M_E
  have hι_pl_norm : ‖ι_pl σ₀‖ ≤ M_E := (hPkg.pl_proj_id σ₀ hσ₀).2.1
  have hP₀ : ‖P₀_lift - Ppl₀‖ ≤ 2 * M_E * η := by
    calc ‖ι₀_lift.comp π₀_lift - (ι_pl σ₀).comp (π_pl σ₀)‖
        ≤ ‖ι₀_lift - ι_pl σ₀‖ * ‖π₀_lift‖ + ‖ι_pl σ₀‖ * ‖π₀_lift - π_pl σ₀‖ :=
          norm_comp_sub_comp_le _ _ _ _
      _ ≤ η * M_E + M_E * η := add_le_add
          (mul_le_mul hι₀ hπ₀_lift_norm (norm_nonneg _) hη.le)
          (mul_le_mul hι_pl_norm hπ₀ (norm_nonneg _) (by positivity))
      _ = 2 * M_E * η := by ring
  have hP₁ : ‖P₁_lift - Ppl₀‖ ≤ 2 * M_E * η := by
    calc ‖ι₁_lift.comp π₁_lift - (ι_pl σ₀).comp (π_pl σ₀)‖
        ≤ ‖ι₁_lift - ι_pl σ₀‖ * ‖π₁_lift‖ + ‖ι_pl σ₀‖ * ‖π₁_lift - π_pl σ₀‖ :=
          norm_comp_sub_comp_le _ _ _ _
      _ ≤ η * M_E + M_E * η := add_le_add
          (mul_le_mul hι₁ hπ₁_lift_norm (norm_nonneg _) hη.le)
          (mul_le_mul hι_pl_norm hπ₁ (norm_nonneg _) (by positivity))
      _ = 2 * M_E * η := by ring
  exact ⟨hι₀, hπ₀, hι₁, hπ₁, hP₀, hP₁⟩

/-! ## 3. Abstract four-block perturbation bounds -/

/-- Abstract four-block perturbation estimate on any normed space `X`: given coordinate maps
`(ι₀_lift, π₁_lift)` and projections `(P₀_lift, P₁_lift)` approximating `(ι₀, π₀)` and
`P₀ = ι₀ ∘ π₀`, together with block bounds for `U_lift` relative to `E`, bounds the four perturbed
blocks of `U_lift`. -/
theorem abstract_four_block_bounds
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M_E M_U η_coord η_op : ℝ}
    (hM_E : 1 ≤ M_E) (hM_U : 0 ≤ M_U) (hη_coord : 0 ≤ η_coord)
    (ι₀ ι₀_lift : E2 →L[ℝ] X) (π₀ π₁_lift : X →L[ℝ] E2)
    (P₀_lift P₁_lift U_lift E : X →L[ℝ] X)
    (hι₀_norm : ‖ι₀‖ ≤ M_E) (hπ₀_norm : ‖π₀‖ ≤ M_E)
    (hι₀_lift_norm : ‖ι₀_lift‖ ≤ M_E)
    (hP₀_lift_norm : ‖P₀_lift‖ ≤ M_E ^ 2)
    (hU_lift_norm : ‖U_lift‖ ≤ M_U)
    (hι₀_diff : ‖ι₀_lift - ι₀‖ ≤ η_coord)
    (hπ₁_diff : ‖π₁_lift - π₀‖ ≤ η_coord)
    (hP₀_diff : ‖P₀_lift - ι₀.comp π₀‖ ≤ 2 * M_E * η_coord)
    (hP₁_diff : ‖P₁_lift - ι₀.comp π₀‖ ≤ 2 * M_E * η_coord)
    (h_pl_b : π₀.comp (E.comp (ContinuousLinearMap.id ℝ X - ι₀.comp π₀)) = 0)
    (h_pl_c : (ContinuousLinearMap.id ℝ X - ι₀.comp π₀).comp (E.comp ι₀) = 0)
    (h_op_a : ‖π₀.comp ((U_lift - E).comp ι₀)‖ ≤ η_op)
    (h_op_d :
      ‖(ContinuousLinearMap.id ℝ X - ι₀.comp π₀).comp
        (U_lift.comp (ContinuousLinearMap.id ℝ X - ι₀.comp π₀))‖ ≤
      ‖(ContinuousLinearMap.id ℝ X - ι₀.comp π₀).comp
        (E.comp (ContinuousLinearMap.id ℝ X - ι₀.comp π₀))‖ + η_op)
    (h_op_b :
      ‖π₀.comp ((U_lift - E).comp (ContinuousLinearMap.id ℝ X - ι₀.comp π₀))‖ ≤ η_op)
    (h_op_c :
      ‖(ContinuousLinearMap.id ℝ X - ι₀.comp π₀).comp ((U_lift - E).comp ι₀)‖ ≤ η_op) :
    let Ppl₀ : X →L[ℝ] X := ι₀.comp π₀
    let C_coord : ℝ := 8 * M_E ^ 3 * M_U
    ‖π₁_lift.comp (U_lift.comp ι₀_lift) - π₀.comp (E.comp ι₀)‖ ≤ C_coord * η_coord + η_op ∧
    ‖(ContinuousLinearMap.id ℝ X - P₁_lift).comp
        (U_lift.comp (ContinuousLinearMap.id ℝ X - P₀_lift))‖ ≤
      ‖(ContinuousLinearMap.id ℝ X - Ppl₀).comp
        (E.comp (ContinuousLinearMap.id ℝ X - Ppl₀))‖ + (C_coord * η_coord + η_op) ∧
    ‖π₁_lift.comp (U_lift.comp (ContinuousLinearMap.id ℝ X - P₀_lift))‖ ≤
      C_coord * η_coord + η_op ∧
    ‖(ContinuousLinearMap.id ℝ X - P₁_lift).comp (U_lift.comp ι₀_lift)‖ ≤
      C_coord * η_coord + η_op := by
  intro Ppl₀ C_coord
  set Q₀ : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - Ppl₀
  set Q₀_lift : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - P₀_lift
  set Q₁_lift : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - P₁_lift
  have hQ₀_norm : ‖Q₀‖ ≤ 2 * M_E ^ 2 := by
    calc ‖ContinuousLinearMap.id ℝ X - ι₀.comp π₀‖
        ≤ ‖ContinuousLinearMap.id ℝ X‖ + ‖ι₀.comp π₀‖ := norm_sub_le _ _
      _ ≤ 1 + ‖ι₀‖ * ‖π₀‖ :=
          add_le_add ContinuousLinearMap.norm_id_le (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1 + M_E * M_E :=
          add_le_add le_rfl (mul_le_mul hι₀_norm hπ₀_norm (norm_nonneg _) (by positivity))
      _ ≤ 2 * M_E ^ 2 := by nlinarith
  have hQ₀_lift_norm : ‖Q₀_lift‖ ≤ 2 * M_E ^ 2 := by
    calc ‖ContinuousLinearMap.id ℝ X - P₀_lift‖
        ≤ ‖ContinuousLinearMap.id ℝ X‖ + ‖P₀_lift‖ := norm_sub_le _ _
      _ ≤ 1 + M_E ^ 2 := add_le_add ContinuousLinearMap.norm_id_le hP₀_lift_norm
      _ ≤ 2 * M_E ^ 2 := by nlinarith
  have hQ₀_lift_diff : ‖Q₀_lift - Q₀‖ ≤ 2 * M_E * η_coord := by
    have hsub : Q₀_lift - Q₀ = -(P₀_lift - Ppl₀) := by
      dsimp [Q₀_lift, Q₀]
      abel
    rw [hsub, norm_neg]
    exact hP₀_diff
  have hQ₁_lift_diff : ‖Q₁_lift - Q₀‖ ≤ 2 * M_E * η_coord := by
    have hsub : Q₁_lift - Q₀ = -(P₁_lift - Ppl₀) := by
      dsimp [Q₁_lift, Q₀]
      abel
    rw [hsub, norm_neg]
    exact hP₁_diff
  have hME_2 : 2 * M_E ≤ 8 * M_E ^ 3 := by nlinarith
  have hME_4 : 4 * M_E ^ 2 ≤ 8 * M_E ^ 3 := by nlinarith
  have hMU_η_nn : 0 ≤ M_U * η_coord := mul_nonneg hM_U hη_coord
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Block a
    have hdec :
        π₁_lift.comp (U_lift.comp ι₀_lift) - π₀.comp (E.comp ι₀) =
        (π₁_lift - π₀).comp (U_lift.comp ι₀_lift) + π₀.comp (U_lift.comp (ι₀_lift - ι₀)) +
          π₀.comp ((U_lift - E).comp ι₀) := by
      ext α
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hdec]
    have h1 : ‖(π₁_lift - π₀).comp (U_lift.comp ι₀_lift)‖ ≤ η_coord * (M_U * M_E) := by
      calc ‖(π₁_lift - π₀).comp (U_lift.comp ι₀_lift)‖
          ≤ ‖π₁_lift - π₀‖ * ‖U_lift.comp ι₀_lift‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ η_coord * (‖U_lift‖ * ‖ι₀_lift‖) := mul_le_mul hπ₁_diff
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) hη_coord
        _ ≤ η_coord * (M_U * M_E) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hι₀_lift_norm (norm_nonneg _) hM_U) hη_coord
    have h2 : ‖π₀.comp (U_lift.comp (ι₀_lift - ι₀))‖ ≤ M_E * (M_U * η_coord) := by
      calc ‖π₀.comp (U_lift.comp (ι₀_lift - ι₀))‖
          ≤ ‖π₀‖ * ‖U_lift.comp (ι₀_lift - ι₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M_E * (‖U_lift‖ * ‖ι₀_lift - ι₀‖) := mul_le_mul hπ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ M_E * (M_U * η_coord) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hι₀_diff (norm_nonneg _) hM_U) (by positivity)
    have hcoef : η_coord * (M_U * M_E) + M_E * (M_U * η_coord) ≤ C_coord * η_coord := by
      calc η_coord * (M_U * M_E) + M_E * (M_U * η_coord)
          = (2 * M_E) * (M_U * η_coord) := by ring
        _ ≤ (8 * M_E ^ 3) * (M_U * η_coord) := mul_le_mul_of_nonneg_right hME_2 hMU_η_nn
        _ = C_coord * η_coord := by dsimp [C_coord]; ring
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      ((add_le_add h1 h2).trans hcoef)) h_op_a)
  · -- 2. Block d
    have hdec :
        Q₁_lift.comp (U_lift.comp Q₀_lift) =
        (Q₁_lift - Q₀).comp (U_lift.comp Q₀_lift) + Q₀.comp (U_lift.comp (Q₀_lift - Q₀)) +
          Q₀.comp (U_lift.comp Q₀) := by
      ext x
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hdec]
    have h1 : ‖(Q₁_lift - Q₀).comp (U_lift.comp Q₀_lift)‖ ≤
        (2 * M_E * η_coord) * (M_U * (2 * M_E ^ 2)) := by
      calc ‖(Q₁_lift - Q₀).comp (U_lift.comp Q₀_lift)‖
          ≤ ‖Q₁_lift - Q₀‖ * ‖U_lift.comp Q₀_lift‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E * η_coord) * (‖U_lift‖ * ‖Q₀_lift‖) := mul_le_mul hQ₁_lift_diff
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E * η_coord) * (M_U * (2 * M_E ^ 2)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hQ₀_lift_norm (norm_nonneg _) hM_U) (by positivity)
    have h2 : ‖Q₀.comp (U_lift.comp (Q₀_lift - Q₀))‖ ≤
        (2 * M_E ^ 2) * (M_U * (2 * M_E * η_coord)) := by
      calc ‖Q₀.comp (U_lift.comp (Q₀_lift - Q₀))‖
          ≤ ‖Q₀‖ * ‖U_lift.comp (Q₀_lift - Q₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E ^ 2) * (‖U_lift‖ * ‖Q₀_lift - Q₀‖) := mul_le_mul hQ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E ^ 2) * (M_U * (2 * M_E * η_coord)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hQ₀_lift_diff (norm_nonneg _) hM_U) (by positivity)
    have hcoef :
        (2 * M_E * η_coord) * (M_U * (2 * M_E ^ 2)) +
          (2 * M_E ^ 2) * (M_U * (2 * M_E * η_coord)) = C_coord * η_coord := by
      dsimp [C_coord]
      ring
    have hsum12 :
        ‖(Q₁_lift - Q₀).comp (U_lift.comp Q₀_lift) + Q₀.comp (U_lift.comp (Q₀_lift - Q₀))‖ ≤
          C_coord * η_coord :=
      (norm_add_le _ _).trans ((add_le_add h1 h2).trans hcoef.le)
    calc ‖(Q₁_lift - Q₀).comp (U_lift.comp Q₀_lift) + Q₀.comp (U_lift.comp (Q₀_lift - Q₀)) +
            Q₀.comp (U_lift.comp Q₀)‖
        ≤ ‖(Q₁_lift - Q₀).comp (U_lift.comp Q₀_lift) + Q₀.comp (U_lift.comp (Q₀_lift - Q₀))‖ +
            ‖Q₀.comp (U_lift.comp Q₀)‖ := norm_add_le _ _
      _ ≤ C_coord * η_coord + (‖Q₀.comp (E.comp Q₀)‖ + η_op) := add_le_add hsum12 h_op_d
      _ = ‖Q₀.comp (E.comp Q₀)‖ + (C_coord * η_coord + η_op) := by ring
  · -- 3. Block b
    have hdec :
        π₁_lift.comp (U_lift.comp Q₀_lift) =
        (π₁_lift - π₀).comp (U_lift.comp Q₀_lift) + π₀.comp (U_lift.comp (Q₀_lift - Q₀)) +
          π₀.comp ((U_lift - E).comp Q₀) + π₀.comp (E.comp Q₀) := by
      ext x
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hdec, h_pl_b, add_zero]
    have h1 : ‖(π₁_lift - π₀).comp (U_lift.comp Q₀_lift)‖ ≤
        η_coord * (M_U * (2 * M_E ^ 2)) := by
      calc ‖(π₁_lift - π₀).comp (U_lift.comp Q₀_lift)‖
          ≤ ‖π₁_lift - π₀‖ * ‖U_lift.comp Q₀_lift‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ η_coord * (‖U_lift‖ * ‖Q₀_lift‖) := mul_le_mul hπ₁_diff
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) hη_coord
        _ ≤ η_coord * (M_U * (2 * M_E ^ 2)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hQ₀_lift_norm (norm_nonneg _) hM_U) hη_coord
    have h2 : ‖π₀.comp (U_lift.comp (Q₀_lift - Q₀))‖ ≤
        M_E * (M_U * (2 * M_E * η_coord)) := by
      calc ‖π₀.comp (U_lift.comp (Q₀_lift - Q₀))‖
          ≤ ‖π₀‖ * ‖U_lift.comp (Q₀_lift - Q₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M_E * (‖U_lift‖ * ‖Q₀_lift - Q₀‖) := mul_le_mul hπ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ M_E * (M_U * (2 * M_E * η_coord)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hQ₀_lift_diff (norm_nonneg _) hM_U) (by positivity)
    have hcoef :
        η_coord * (M_U * (2 * M_E ^ 2)) + M_E * (M_U * (2 * M_E * η_coord)) ≤
          C_coord * η_coord := by
      calc η_coord * (M_U * (2 * M_E ^ 2)) + M_E * (M_U * (2 * M_E * η_coord))
          = (4 * M_E ^ 2) * (M_U * η_coord) := by ring
        _ ≤ (8 * M_E ^ 3) * (M_U * η_coord) := mul_le_mul_of_nonneg_right hME_4 hMU_η_nn
        _ = C_coord * η_coord := by dsimp [C_coord]; ring
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      ((add_le_add h1 h2).trans hcoef)) h_op_b)
  · -- 4. Block c
    have hdec :
        Q₁_lift.comp (U_lift.comp ι₀_lift) =
        (Q₁_lift - Q₀).comp (U_lift.comp ι₀_lift) + Q₀.comp (U_lift.comp (ι₀_lift - ι₀)) +
          Q₀.comp ((U_lift - E).comp ι₀) + Q₀.comp (E.comp ι₀) := by
      ext α
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hdec, h_pl_c, add_zero]
    have h1 : ‖(Q₁_lift - Q₀).comp (U_lift.comp ι₀_lift)‖ ≤
        (2 * M_E * η_coord) * (M_U * M_E) := by
      calc ‖(Q₁_lift - Q₀).comp (U_lift.comp ι₀_lift)‖
          ≤ ‖Q₁_lift - Q₀‖ * ‖U_lift.comp ι₀_lift‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E * η_coord) * (‖U_lift‖ * ‖ι₀_lift‖) := mul_le_mul hQ₁_lift_diff
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E * η_coord) * (M_U * M_E) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hι₀_lift_norm (norm_nonneg _) hM_U) (by positivity)
    have h2 : ‖Q₀.comp (U_lift.comp (ι₀_lift - ι₀))‖ ≤
        (2 * M_E ^ 2) * (M_U * η_coord) := by
      calc ‖Q₀.comp (U_lift.comp (ι₀_lift - ι₀))‖
          ≤ ‖Q₀‖ * ‖U_lift.comp (ι₀_lift - ι₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E ^ 2) * (‖U_lift‖ * ‖ι₀_lift - ι₀‖) := mul_le_mul hQ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E ^ 2) * (M_U * η_coord) := mul_le_mul_of_nonneg_left
            (mul_le_mul hU_lift_norm hι₀_diff (norm_nonneg _) hM_U) (by positivity)
    have hcoef :
        (2 * M_E * η_coord) * (M_U * M_E) + (2 * M_E ^ 2) * (M_U * η_coord) ≤
          C_coord * η_coord := by
      calc (2 * M_E * η_coord) * (M_U * M_E) + (2 * M_E ^ 2) * (M_U * η_coord)
          = (4 * M_E ^ 2) * (M_U * η_coord) := by ring
        _ ≤ (8 * M_E ^ 3) * (M_U * η_coord) := mul_le_mul_of_nonneg_right hME_4 hMU_η_nn
        _ = C_coord * η_coord := by dsimp [C_coord]; ring
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      ((add_le_add h1 h2).trans hcoef)) h_op_c)

/-- Finite-rank commutator identity for `Q₀ = id - ι₀ ∘ π₀` and any `W : X →L[ℝ] X`:
`Q₀ ∘ W - W ∘ Q₀ = ((W - id) ∘ ι₀) ∘ π₀ - ι₀ ∘ (π₀ ∘ (W - id))` (SP 2152–2158). -/
theorem commutator_Q_eq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ι₀ : E2 →L[ℝ] X) (π₀ : X →L[ℝ] E2) (W : X →L[ℝ] X) :
    let Q₀ : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - ι₀.comp π₀
    Q₀.comp W - W.comp Q₀ =
      ((W - ContinuousLinearMap.id ℝ X).comp ι₀).comp π₀ -
        ι₀.comp (π₀.comp (W - ContinuousLinearMap.id ℝ X)) := by
  intro Q₀
  ext x
  simp only [Q₀, sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_sub]
  abel

/-- From the SP 2149 factorization `U_lift = W ∘ E + R` with `‖R‖ ≤ η`, `‖W‖ ≤ 1 + η`,
`‖(W - id) ∘ ι₀‖ ≤ η`, `‖π₀ ∘ (W - id)‖ ≤ η`, and `E ∘ ι₀ = ι₀ ∘ M`, derive the four planar
block bounds used in `abstract_four_block_bounds`. -/
theorem planar_blocks_of_weyl_factorization
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {M_E M_op η : ℝ} (hM_E : 1 ≤ M_E) (hM_op : 1 ≤ M_op) (hη : 0 ≤ η)
    (ι₀ : E2 →L[ℝ] X) (π₀ : X →L[ℝ] E2)
    (U_lift E W : X →L[ℝ] X) (M : E2 →L[ℝ] E2)
    (hι₀_norm : ‖ι₀‖ ≤ M_E) (hπ₀_norm : ‖π₀‖ ≤ M_E)
    (hE_norm : ‖E‖ ≤ M_op) (hM_norm : ‖M‖ ≤ M_op)
    (hE_eig : E.comp ι₀ = ι₀.comp M)
    (hR : ‖U_lift - W.comp E‖ ≤ η)
    (hW_norm : ‖W‖ ≤ 1 + η)
    (hW_ι : ‖(W - ContinuousLinearMap.id ℝ X).comp ι₀‖ ≤ η)
    (hW_π : ‖π₀.comp (W - ContinuousLinearMap.id ℝ X)‖ ≤ η) :
    let Q₀ : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - ι₀.comp π₀
    let C_weyl : ℝ := 12 * M_E ^ 4 * M_op
    ‖π₀.comp ((U_lift - E).comp ι₀)‖ ≤ C_weyl * η ∧
    ‖Q₀.comp (U_lift.comp Q₀)‖ ≤ ‖Q₀.comp (E.comp Q₀)‖ + C_weyl * η ∧
    ‖π₀.comp ((U_lift - E).comp Q₀)‖ ≤ C_weyl * η ∧
    ‖Q₀.comp ((U_lift - E).comp ι₀)‖ ≤ C_weyl * η := by
  intro Q₀ C_weyl
  set R : X →L[ℝ] X := U_lift - W.comp E
  set ΔW : X →L[ℝ] X := W - ContinuousLinearMap.id ℝ X
  have hUE_eq : U_lift - E = R + ΔW.comp E := by
    ext x
    simp only [R, ΔW, sub_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    abel
  have hQ₀_norm : ‖Q₀‖ ≤ 2 * M_E ^ 2 := by
    calc ‖ContinuousLinearMap.id ℝ X - ι₀.comp π₀‖
        ≤ ‖ContinuousLinearMap.id ℝ X‖ + ‖ι₀.comp π₀‖ := norm_sub_le _ _
      _ ≤ 1 + ‖ι₀‖ * ‖π₀‖ :=
          add_le_add ContinuousLinearMap.norm_id_le (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1 + M_E * M_E :=
          add_le_add le_rfl (mul_le_mul hι₀_norm hπ₀_norm (norm_nonneg _) (by positivity))
      _ ≤ 2 * M_E ^ 2 := by nlinarith
  have hEι_norm : ‖E.comp ι₀‖ ≤ M_op * M_E := by
    calc ‖E.comp ι₀‖ ≤ ‖E‖ * ‖ι₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_op * M_E := mul_le_mul hE_norm hι₀_norm (norm_nonneg _) (by positivity)
  have hEQ_norm : ‖E.comp Q₀‖ ≤ M_op * (2 * M_E ^ 2) := by
    calc ‖E.comp Q₀‖ ≤ ‖E‖ * ‖Q₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_op * (2 * M_E ^ 2) := mul_le_mul hE_norm hQ₀_norm (norm_nonneg _) (by positivity)
  have hQEQ_norm : ‖Q₀.comp (E.comp Q₀)‖ ≤ (2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2)) := by
    calc ‖Q₀.comp (E.comp Q₀)‖ ≤ ‖Q₀‖ * ‖E.comp Q₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2)) :=
          mul_le_mul hQ₀_norm hEQ_norm (norm_nonneg _) (by positivity)
  have hME2 : M_E ≤ M_E ^ 2 := by nlinarith
  have hME3 : M_E ^ 2 ≤ M_E ^ 3 := by nlinarith
  have hME4 : M_E ^ 3 ≤ M_E ^ 4 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Block a
    have hdec : π₀.comp ((U_lift - E).comp ι₀) =
        π₀.comp (R.comp ι₀) + (π₀.comp ΔW).comp (E.comp ι₀) := by
      rw [hUE_eq]
      ext α
      simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    rw [hdec]
    have h1 : ‖π₀.comp (R.comp ι₀)‖ ≤ M_E * (η * M_E) := by
      calc ‖π₀.comp (R.comp ι₀)‖
          ≤ ‖π₀‖ * ‖R.comp ι₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M_E * (‖R‖ * ‖ι₀‖) := mul_le_mul hπ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ M_E * (η * M_E) := mul_le_mul_of_nonneg_left
            (mul_le_mul hR hι₀_norm (norm_nonneg _) hη) (by positivity)
    have h2 : ‖(π₀.comp ΔW).comp (E.comp ι₀)‖ ≤ η * (M_op * M_E) := by
      calc ‖(π₀.comp ΔW).comp (E.comp ι₀)‖
          ≤ ‖π₀.comp ΔW‖ * ‖E.comp ι₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ η * (M_op * M_E) := mul_le_mul hW_π hEι_norm (norm_nonneg _) hη
    have hcoef : M_E * (η * M_E) + η * (M_op * M_E) ≤ C_weyl * η := by
      have h_ineq : M_E ^ 2 + M_E * M_op ≤ 12 * M_E ^ 4 * M_op := by nlinarith
      calc M_E * (η * M_E) + η * (M_op * M_E)
          = (M_E ^ 2 + M_E * M_op) * η := by ring
        _ ≤ (12 * M_E ^ 4 * M_op) * η := mul_le_mul_of_nonneg_right h_ineq hη
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans hcoef)
  · -- 2. Block d
    have hdec :
        Q₀.comp (U_lift.comp Q₀) =
        W.comp (Q₀.comp (E.comp Q₀)) + Q₀.comp (R.comp Q₀) +
          (Q₀.comp W - W.comp Q₀).comp (E.comp Q₀) := by
      ext x
      simp only [R, sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    rw [hdec]
    have hcomm_norm : ‖Q₀.comp W - W.comp Q₀‖ ≤ 2 * M_E * η := by
      rw [commutator_Q_eq ι₀ π₀ W]
      have hc1 : ‖(ΔW.comp ι₀).comp π₀‖ ≤ η * M_E := by
        calc ‖(ΔW.comp ι₀).comp π₀‖ ≤ ‖ΔW.comp ι₀‖ * ‖π₀‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ η * M_E := mul_le_mul hW_ι hπ₀_norm (norm_nonneg _) hη
      have hc2 : ‖ι₀.comp (π₀.comp ΔW)‖ ≤ M_E * η := by
        calc ‖ι₀.comp (π₀.comp ΔW)‖ ≤ ‖ι₀‖ * ‖π₀.comp ΔW‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ M_E * η := mul_le_mul hι₀_norm hW_π (norm_nonneg _) (by positivity)
      calc ‖(ΔW.comp ι₀).comp π₀ - ι₀.comp (π₀.comp ΔW)‖
          ≤ ‖(ΔW.comp ι₀).comp π₀‖ + ‖ι₀.comp (π₀.comp ΔW)‖ := norm_sub_le _ _
        _ ≤ η * M_E + M_E * η := add_le_add hc1 hc2
        _ = 2 * M_E * η := by ring
    have h1 : ‖W.comp (Q₀.comp (E.comp Q₀))‖ ≤
        ‖Q₀.comp (E.comp Q₀)‖ + η * ((2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2))) := by
      calc ‖W.comp (Q₀.comp (E.comp Q₀))‖
          ≤ ‖W‖ * ‖Q₀.comp (E.comp Q₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (1 + η) * ‖Q₀.comp (E.comp Q₀)‖ :=
            mul_le_mul_of_nonneg_right hW_norm (norm_nonneg _)
        _ = ‖Q₀.comp (E.comp Q₀)‖ + η * ‖Q₀.comp (E.comp Q₀)‖ := by ring
        _ ≤ ‖Q₀.comp (E.comp Q₀)‖ + η * ((2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2))) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hQEQ_norm hη)
    have h2 : ‖Q₀.comp (R.comp Q₀)‖ ≤ (2 * M_E ^ 2) * (η * (2 * M_E ^ 2)) := by
      calc ‖Q₀.comp (R.comp Q₀)‖ ≤ ‖Q₀‖ * ‖R.comp Q₀‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E ^ 2) * (‖R‖ * ‖Q₀‖) := mul_le_mul hQ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E ^ 2) * (η * (2 * M_E ^ 2)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hR hQ₀_norm (norm_nonneg _) hη) (by positivity)
    have h3 : ‖(Q₀.comp W - W.comp Q₀).comp (E.comp Q₀)‖ ≤
        (2 * M_E * η) * (M_op * (2 * M_E ^ 2)) := by
      calc ‖(Q₀.comp W - W.comp Q₀).comp (E.comp Q₀)‖
          ≤ ‖Q₀.comp W - W.comp Q₀‖ * ‖E.comp Q₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E * η) * (M_op * (2 * M_E ^ 2)) :=
            mul_le_mul hcomm_norm hEQ_norm (norm_nonneg _) (by positivity)
    have hcoef :
        η * ((2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2))) +
          (2 * M_E ^ 2) * (η * (2 * M_E ^ 2)) +
          (2 * M_E * η) * (M_op * (2 * M_E ^ 2)) ≤ C_weyl * η := by
      have h_ineq : 4 * M_E ^ 4 * M_op + 4 * M_E ^ 4 + 4 * M_E ^ 3 * M_op ≤
          12 * M_E ^ 4 * M_op := by nlinarith
      calc η * ((2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2))) +
            (2 * M_E ^ 2) * (η * (2 * M_E ^ 2)) +
            (2 * M_E * η) * (M_op * (2 * M_E ^ 2))
          = (4 * M_E ^ 4 * M_op + 4 * M_E ^ 4 + 4 * M_E ^ 3 * M_op) * η := by ring
        _ ≤ (12 * M_E ^ 4 * M_op) * η := mul_le_mul_of_nonneg_right h_ineq hη
    calc ‖W.comp (Q₀.comp (E.comp Q₀)) + Q₀.comp (R.comp Q₀) +
            (Q₀.comp W - W.comp Q₀).comp (E.comp Q₀)‖
        ≤ ‖W.comp (Q₀.comp (E.comp Q₀))‖ + ‖Q₀.comp (R.comp Q₀)‖ +
            ‖(Q₀.comp W - W.comp Q₀).comp (E.comp Q₀)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (‖Q₀.comp (E.comp Q₀)‖ + η * ((2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2)))) +
            (2 * M_E ^ 2) * (η * (2 * M_E ^ 2)) +
            (2 * M_E * η) * (M_op * (2 * M_E ^ 2)) :=
          add_le_add (add_le_add h1 h2) h3
      _ = ‖Q₀.comp (E.comp Q₀)‖ +
            (η * ((2 * M_E ^ 2) * (M_op * (2 * M_E ^ 2))) +
              (2 * M_E ^ 2) * (η * (2 * M_E ^ 2)) +
              (2 * M_E * η) * (M_op * (2 * M_E ^ 2))) := by ring
      _ ≤ ‖Q₀.comp (E.comp Q₀)‖ + C_weyl * η := add_le_add le_rfl hcoef
  · -- 3. Block b
    have hdec : π₀.comp ((U_lift - E).comp Q₀) =
        π₀.comp (R.comp Q₀) + (π₀.comp ΔW).comp (E.comp Q₀) := by
      rw [hUE_eq]
      ext x
      simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
    rw [hdec]
    have h1 : ‖π₀.comp (R.comp Q₀)‖ ≤ M_E * (η * (2 * M_E ^ 2)) := by
      calc ‖π₀.comp (R.comp Q₀)‖ ≤ ‖π₀‖ * ‖R.comp Q₀‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M_E * (‖R‖ * ‖Q₀‖) := mul_le_mul hπ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ M_E * (η * (2 * M_E ^ 2)) := mul_le_mul_of_nonneg_left
            (mul_le_mul hR hQ₀_norm (norm_nonneg _) hη) (by positivity)
    have h2 : ‖(π₀.comp ΔW).comp (E.comp Q₀)‖ ≤ η * (M_op * (2 * M_E ^ 2)) := by
      calc ‖(π₀.comp ΔW).comp (E.comp Q₀)‖
          ≤ ‖π₀.comp ΔW‖ * ‖E.comp Q₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ η * (M_op * (2 * M_E ^ 2)) := mul_le_mul hW_π hEQ_norm (norm_nonneg _) hη
    have hcoef : M_E * (η * (2 * M_E ^ 2)) + η * (M_op * (2 * M_E ^ 2)) ≤ C_weyl * η := by
      have h_ineq : 2 * M_E ^ 3 + 2 * M_E ^ 2 * M_op ≤ 12 * M_E ^ 4 * M_op := by nlinarith
      calc M_E * (η * (2 * M_E ^ 2)) + η * (M_op * (2 * M_E ^ 2))
          = (2 * M_E ^ 3 + 2 * M_E ^ 2 * M_op) * η := by ring
        _ ≤ (12 * M_E ^ 4 * M_op) * η := mul_le_mul_of_nonneg_right h_ineq hη
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans hcoef)
  · -- 4. Block c
    have hdec : Q₀.comp ((U_lift - E).comp ι₀) =
        Q₀.comp (R.comp ι₀) + Q₀.comp ((ΔW.comp ι₀).comp M) := by
      rw [hUE_eq]
      have h_eig' : (ΔW.comp E).comp ι₀ = (ΔW.comp ι₀).comp M := by
        rw [ContinuousLinearMap.comp_assoc, hE_eig, ← ContinuousLinearMap.comp_assoc]
      ext α
      simp only [add_apply, ContinuousLinearMap.comp_apply, map_add]
      congr 2
      exact DFunLike.congr_fun h_eig' α
    rw [hdec]
    have h1 : ‖Q₀.comp (R.comp ι₀)‖ ≤ (2 * M_E ^ 2) * (η * M_E) := by
      calc ‖Q₀.comp (R.comp ι₀)‖ ≤ ‖Q₀‖ * ‖R.comp ι₀‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E ^ 2) * (‖R‖ * ‖ι₀‖) := mul_le_mul hQ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E ^ 2) * (η * M_E) := mul_le_mul_of_nonneg_left
            (mul_le_mul hR hι₀_norm (norm_nonneg _) hη) (by positivity)
    have h2 : ‖Q₀.comp ((ΔW.comp ι₀).comp M)‖ ≤ (2 * M_E ^ 2) * (η * M_op) := by
      calc ‖Q₀.comp ((ΔW.comp ι₀).comp M)‖
          ≤ ‖Q₀‖ * ‖(ΔW.comp ι₀).comp M‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * M_E ^ 2) * (‖ΔW.comp ι₀‖ * ‖M‖) := mul_le_mul hQ₀_norm
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) (by positivity)
        _ ≤ (2 * M_E ^ 2) * (η * M_op) := mul_le_mul_of_nonneg_left
            (mul_le_mul hW_ι hM_norm (norm_nonneg _) hη) (by positivity)
    have hcoef : (2 * M_E ^ 2) * (η * M_E) + (2 * M_E ^ 2) * (η * M_op) ≤ C_weyl * η := by
      have h_ineq : 2 * M_E ^ 3 + 2 * M_E ^ 2 * M_op ≤ 12 * M_E ^ 4 * M_op := by nlinarith
      calc (2 * M_E ^ 2) * (η * M_E) + (2 * M_E ^ 2) * (η * M_op)
          = (2 * M_E ^ 3 + 2 * M_E ^ 2 * M_op) * η := by ring
        _ ≤ (12 * M_E ^ 4 * M_op) * η := mul_le_mul_of_nonneg_right h_ineq hη
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans hcoef)

/-- Specialization of `abstract_four_block_bounds` to cylinder block operators lifted from
`Xmc c m` to `Xm m` via `Jc c m` and `Rc c m`. -/
theorem four_block_bounds_of_lifted
    {c m M_E M_U η_coord η_op : ℝ}
    (hM_E : 1 ≤ M_E) (hM_U : 0 ≤ M_U) (hη_coord : 0 ≤ η_coord)
    (ι₀ : E2 →L[ℝ] Xm m) (π₀ : Xm m →L[ℝ] E2)
    (ιc₀ ιc₁ : E2 →L[ℝ] Xmc c m) (πc₀ πc₁ : Xmc c m →L[ℝ] E2)
    (U : Xmc c m →L[ℝ] Xmc c m) (E : Xm m →L[ℝ] Xm m)
    (hι₀_norm : ‖ι₀‖ ≤ M_E) (hπ₀_norm : ‖π₀‖ ≤ M_E)
    (hιc₀_norm : ‖ιc₀‖ ≤ M_E) (hπc₀_norm : ‖πc₀‖ ≤ M_E)
    (hU_norm : ‖U‖ ≤ M_U)
    (hι₀_diff : ‖(Jc c m).comp ιc₀ - ι₀‖ ≤ η_coord)
    (hπ₁_diff : ‖πc₁.comp (Rc c m) - π₀‖ ≤ η_coord)
    (hP₀_diff : ‖((Jc c m).comp ιc₀).comp (πc₀.comp (Rc c m)) - ι₀.comp π₀‖ ≤ 2 * M_E * η_coord)
    (hP₁_diff : ‖((Jc c m).comp ιc₁).comp (πc₁.comp (Rc c m)) - ι₀.comp π₀‖ ≤ 2 * M_E * η_coord)
    (h_pl_b : π₀.comp (E.comp (ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀)) = 0)
    (h_pl_c : (ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀).comp (E.comp ι₀) = 0)
    (h_op_a : ‖π₀.comp (((Jc c m).comp (U.comp (Rc c m)) - E).comp ι₀)‖ ≤ η_op)
    (h_op_d :
      ‖(ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀).comp
        (((Jc c m).comp (U.comp (Rc c m))).comp
          (ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀))‖ ≤
      ‖(ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀).comp
        (E.comp (ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀))‖ + η_op)
    (h_op_b :
      ‖π₀.comp (((Jc c m).comp (U.comp (Rc c m)) - E).comp
        (ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀))‖ ≤ η_op)
    (h_op_c :
      ‖(ContinuousLinearMap.id ℝ (Xm m) - ι₀.comp π₀).comp
        (((Jc c m).comp (U.comp (Rc c m)) - E).comp ι₀)‖ ≤ η_op) :
    let Pc₀ : Xmc c m →L[ℝ] Xmc c m := ιc₀.comp πc₀
    let Pc₁ : Xmc c m →L[ℝ] Xmc c m := ιc₁.comp πc₁
    let Ppl₀ : Xm m →L[ℝ] Xm m := ι₀.comp π₀
    let C_coord : ℝ := 8 * M_E ^ 3 * M_U
    ‖πc₁.comp (U.comp ιc₀) - π₀.comp (E.comp ι₀)‖ ≤ C_coord * η_coord + η_op ∧
    ‖(ContinuousLinearMap.id ℝ (Xmc c m) - Pc₁).comp
        (U.comp (ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀))‖ ≤
      ‖(ContinuousLinearMap.id ℝ (Xm m) - Ppl₀).comp
        (E.comp (ContinuousLinearMap.id ℝ (Xm m) - Ppl₀))‖ + (C_coord * η_coord + η_op) ∧
    ‖πc₁.comp (U.comp (ContinuousLinearMap.id ℝ (Xmc c m) - Pc₀))‖ ≤
      C_coord * η_coord + η_op ∧
    ‖(ContinuousLinearMap.id ℝ (Xmc c m) - Pc₁).comp (U.comp ιc₀)‖ ≤
      C_coord * η_coord + η_op := by
  intro Pc₀ Pc₁ Ppl₀ C_coord
  have hι₀_lift_norm : ‖(Jc c m).comp ιc₀‖ ≤ M_E := by
    calc ‖(Jc c m).comp ιc₀‖ ≤ ‖Jc c m‖ * ‖ιc₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * M_E := mul_le_mul (norm_Jc_le c m) hιc₀_norm (norm_nonneg _) zero_le_one
      _ = M_E := one_mul M_E
  have hπ₀_lift_norm : ‖πc₀.comp (Rc c m)‖ ≤ M_E := by
    calc ‖πc₀.comp (Rc c m)‖ ≤ ‖πc₀‖ * ‖Rc c m‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_E * 1 := mul_le_mul hπc₀_norm (norm_Rc_le c m) (norm_nonneg _) (by positivity)
      _ = M_E := mul_one M_E
  have hP₀_lift_norm : ‖((Jc c m).comp ιc₀).comp (πc₀.comp (Rc c m))‖ ≤ M_E ^ 2 := by
    calc ‖((Jc c m).comp ιc₀).comp (πc₀.comp (Rc c m))‖
        ≤ ‖(Jc c m).comp ιc₀‖ * ‖πc₀.comp (Rc c m)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M_E * M_E := mul_le_mul hι₀_lift_norm hπ₀_lift_norm (norm_nonneg _) (by positivity)
      _ = M_E ^ 2 := by ring
  have hU_lift_norm : ‖(Jc c m).comp (U.comp (Rc c m))‖ ≤ M_U :=
    (norm_Jc_comp_Rc_le c m U).trans hU_norm
  obtain ⟨ha, hd, hb, hc⟩ :=
    abstract_four_block_bounds hM_E hM_U hη_coord ι₀ ((Jc c m).comp ιc₀) π₀ (πc₁.comp (Rc c m))
      (((Jc c m).comp ιc₀).comp (πc₀.comp (Rc c m)))
      (((Jc c m).comp ιc₁).comp (πc₁.comp (Rc c m)))
      ((Jc c m).comp (U.comp (Rc c m))) E
      hι₀_norm hπ₀_norm hι₀_lift_norm hP₀_lift_norm hU_lift_norm
      hι₀_diff hπ₁_diff hP₀_diff hP₁_diff h_pl_b h_pl_c h_op_a h_op_d h_op_b h_op_c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Jc_Rc_block_a_eq c m πc₁ U ιc₀]
    exact ha
  · exact (norm_block_d_le_lifted c m ιc₀ ιc₁ πc₀ πc₁ U).trans hd
  · exact (norm_block_b_le_lifted c m ιc₀ πc₀ πc₁ U).trans hb
  · exact (norm_block_c_le_lifted c m ιc₀ ιc₁ πc₁ U).trans hc

/-! ## 4. Conditional assembly of `CompactDuhamelBlockStep` from planar block comparison -/

/-- **Planar compact-Duhamel block comparison (`PlanarCompactDuhamelComparison`, SP 2104–2115,
2145–2166)**: for any `IsFrozenEulerPackage`, norm-continuous collectively compact planar
interaction family `AplOp`, and cylinder-to-planar interaction comparison bound
`C_Sg * (p.c ^ (-2) + δ)`, the lifted cylinder propagator `Jc ∘ U(t + L, t) ∘ Rc` on `Xm m`
approximates `E_pl(p.ν * t, L)` in the planar coordinate splitting `(ι_pl(p.ν * t), π_pl(p.ν * t))`,
and the planar upper-right off-diagonal block `π_pl σ₀ ∘ E_pl σ₀ L ∘ (1 - Ppl₀)` vanishes. -/
def PlanarCompactDuhamelComparison : Prop :=
  ∀ m : ℝ, 8 < m →
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (L₀ M_E c₀ : ℝ)
    (ι_pl : ℝ → (E2 →L[ℝ] Xm m)) (π_pl : ℝ → (Xm m →L[ℝ] E2))
    (E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m))
    (ι_c : ∀ c : ℝ, ℝ → (E2 →L[ℝ] Xmc c m))
    (π_c : ∀ c : ℝ, ℝ → (Xmc c m →L[ℝ] E2)),
    IsFrozenEulerPackage m Sig lam q L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c →
  ∀ (K₀ C_Sg : ℝ) (AplOp : ℝ → (Xm m →L[ℝ] Xm m)),
    0 < K₀ → 0 < C_Sg →
    ContinuousOn AplOp (Icc 0 Sig) →
    (∀ σ ∈ Icc 0 Sig, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)) →
    TotallyBounded (AplOp '' Icc 0 Sig) →
    (∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sig, AplOp σ '' Metric.closedBall (0 : Xm m) R)) →
  ∀ dm dp : ℝ, 0 < dm →
  ∀ η_op : ℝ, 0 < η_op →
    ∃ (M_U δ ν₀ : ℝ), 0 ≤ M_U ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → c₀ ≤ p.c →
        p.ageCut = Sig → p.mode = q → TrainCloseM m p.train Sig δ →
      ∀ (Sc U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
        (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
        IsCoupledDuhamelPropagator m p Sc Ac U →
        (∀ s ∈ Icc 0 p.H,
          IsCompactOperator (Ac s) ∧
          ‖(Jc p.c m).comp ((Ac s).comp (Rc p.c m)) - AplOp (p.ν * s)‖ ≤
            C_Sg * (p.c ^ (-2 : ℝ) + δ)) →
        (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ p.H →
          ‖Sc t s‖ ≤ Real.exp (K₀ * (t - s))) →
        ∀ t L : ℝ, 0 ≤ t → t + L ≤ p.H → L ∈ Icc L₀ (2 * L₀) →
          let σ₀ : ℝ := p.ν * t
          let Ppl₀ : Xm m →L[ℝ] Xm m := (ι_pl σ₀).comp (π_pl σ₀)
          let Q₀ : Xm m →L[ℝ] Xm m := ContinuousLinearMap.id ℝ (Xm m) - Ppl₀
          let U_lift : Xm m →L[ℝ] Xm m := (Jc p.c m).comp ((U (t + L) t).comp (Rc p.c m))
          ‖U (t + L) t‖ ≤ M_U ∧
          (π_pl σ₀).comp ((E_pl σ₀ L).comp Q₀) = 0 ∧
          ‖(π_pl σ₀).comp ((U_lift - E_pl σ₀ L).comp (ι_pl σ₀))‖ ≤ η_op ∧
          ‖Q₀.comp (U_lift.comp Q₀)‖ ≤ ‖Q₀.comp ((E_pl σ₀ L).comp Q₀)‖ + η_op ∧
          ‖(π_pl σ₀).comp ((U_lift - E_pl σ₀ L).comp Q₀)‖ ≤ η_op ∧
          ‖Q₀.comp ((U_lift - E_pl σ₀ L).comp (ι_pl σ₀))‖ ≤ η_op

/-- Full derivation of `CompactDuhamelBlockStep` from `PlanarCompactDuhamelComparison`,
`IsFrozenEulerPackage.exists_coord_approx`, `IsFrozenEulerPackage.planar_block_c_eq_zero`, and
`four_block_bounds_of_lifted`. -/
theorem compactDuhamelBlockStep_of_planarComparison
    (hPlanar : PlanarCompactDuhamelComparison) :
    CompactDuhamelBlockStep := by
  intro m hm Sig lam q hSig hEig L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c hPkg
    K₀ C_Sg AplOp hK₀ hC_Sg hApl_cont hApl_prop hApl_tb hApl_ball dm dp hdm ε hε
  have hM_E : 1 ≤ M_E := hPkg.M_E_ge_one
  have hc₀ : 1 ≤ c₀ := hPkg.c₀_ge_one
  have hL₀ : 1 ≤ L₀ := hPkg.L₀_ge_one
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨M_U, δ, ν_op, hM_U_nn, hδ_pos, hδ_le_1, hν_op_pos, hν_op_le_1, hOp⟩ :=
    hPlanar m hm Sig lam q hSig hEig L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c hPkg
      K₀ C_Sg AplOp hK₀ hC_Sg hApl_cont hApl_prop hApl_tb hApl_ball dm dp hdm (ε / 2) hε2
  set C_coord : ℝ := 8 * M_E ^ 3 * M_U
  have hC_coord_nn : 0 ≤ C_coord := by dsimp [C_coord]; positivity
  set η_coord : ℝ := (ε / 2) / (C_coord + 1)
  have hη_coord_pos : 0 < η_coord := by dsimp [η_coord]; positivity
  obtain ⟨c₁, ν_coord, hc₁, hν_coord_pos, hν_coord_le_1, hCoord⟩ :=
    hPkg.exists_coord_approx hη_coord_pos
  have hc₁_pos : 0 < c₁ := lt_of_lt_of_le zero_lt_one (hc₀.trans hc₁)
  set ν_c₁ : ℝ := (Real.sqrt c₁)⁻¹
  have hν_c₁_pos : 0 < ν_c₁ := by dsimp [ν_c₁]; positivity
  set ν₀ : ℝ := min ν_op (min ν_coord ν_c₁)
  have hν₀_pos : 0 < ν₀ := lt_min hν_op_pos (lt_min hν_coord_pos hν_c₁_pos)
  have hν₀_le_1 : ν₀ ≤ 1 := (min_le_left _ _).trans hν_op_le_1
  refine ⟨δ, ν₀, hδ_pos, hδ_le_1, hν₀_pos, hν₀_le_1, ?_⟩
  intro p d hbg hν hc_ge_c₀ hAge hMode hcloseM Sc U Ac hCD hAc hSc t L ht htL hL
  have hν0 : 0 < p.ν := p.ν_pos
  have hν_le_op : p.ν ≤ ν_op := hν.trans (min_le_left _ _)
  have hν_le_coord : p.ν ≤ ν_coord := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν_le_c₁ : p.ν ≤ ν_c₁ := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc_ge_c₁ : c₁ ≤ p.c := bgRegime_c_ge hbg hc₁_pos hν_le_c₁
  have hL_nn : 0 ≤ L := (zero_lt_one.trans_le hL₀).le.trans hL.1
  have hH_eq : p.H = Sig / p.ν := by
    change p.ageCut / p.ν = Sig / p.ν
    rw [hAge]
  set σ₀ : ℝ := p.ν * t
  set σ₁ : ℝ := p.ν * (t + L)
  have hσ₀_mem : σ₀ ∈ Icc 0 Sig := by
    refine ⟨mul_nonneg hν0.le ht, ?_⟩
    have ht_le_H : t ≤ Sig / p.ν := hH_eq ▸ (by linarith : t ≤ p.H)
    calc p.ν * t ≤ p.ν * (Sig / p.ν) := mul_le_mul_of_nonneg_left ht_le_H hν0.le
      _ = Sig := mul_div_cancel₀ Sig hν0.ne'
  have hσ₁_mem : σ₁ ∈ Icc 0 Sig := by
    refine ⟨mul_nonneg hν0.le (by linarith), ?_⟩
    have htL_le_H : t + L ≤ Sig / p.ν := hH_eq ▸ htL
    calc p.ν * (t + L) ≤ p.ν * (Sig / p.ν) := mul_le_mul_of_nonneg_left htL_le_H hν0.le
      _ = Sig := mul_div_cancel₀ Sig hν0.ne'
  have hσ_diff : |σ₁ - σ₀| ≤ 2 * L₀ * p.ν := by
    have heq : σ₁ - σ₀ = p.ν * L := by dsimp [σ₀, σ₁]; ring
    rw [heq, abs_of_nonneg (mul_nonneg hν0.le hL_nn), mul_comm p.ν L]
    exact mul_le_mul_of_nonneg_right hL.2 hν0.le
  obtain ⟨hι₀_diff, _, _, hπ₁_diff, hP₀_diff, hP₁_diff⟩ :=
    hCoord p.c p.ν hc_ge_c₁ hν0 hν_le_coord σ₀ σ₁ hσ₀_mem hσ₁_mem hσ_diff
  obtain ⟨hU_norm, h_pl_b, h_op_a, h_op_d, h_op_b, h_op_c⟩ :=
    hOp p d hbg hν_le_op hc_ge_c₀ hAge hMode hcloseM Sc U Ac hCD hAc hSc t L ht htL hL
  have h_pl_c := hPkg.planar_block_c_eq_zero hσ₀_mem hL_nn
  obtain ⟨_, hι₀_norm, hπ₀_norm⟩ := hPkg.pl_proj_id σ₀ hσ₀_mem
  obtain ⟨hιc₀_norm, hπc₀_norm⟩ := hPkg.cyl_norm p.c hc_ge_c₀ σ₀ hσ₀_mem
  obtain ⟨hb_a, hb_d, hb_b, hb_c⟩ :=
    four_block_bounds_of_lifted hM_E hM_U_nn hη_coord_pos.le
      (ι_pl σ₀) (π_pl σ₀) (ι_c p.c σ₀) (ι_c p.c σ₁) (π_c p.c σ₀) (π_c p.c σ₁)
      (U (t + L) t) (E_pl σ₀ L)
      hι₀_norm hπ₀_norm hιc₀_norm hπc₀_norm hU_norm
      hι₀_diff hπ₁_diff hP₀_diff hP₁_diff h_pl_b h_pl_c h_op_a h_op_d h_op_b h_op_c
  have hsum_le : C_coord * η_coord + ε / 2 ≤ ε := by
    have h1 : C_coord * η_coord ≤ ε / 2 := by
      dsimp [η_coord]
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact ⟨hb_a.trans hsum_le, hb_d.trans (add_le_add le_rfl hsum_le),
    hb_b.trans hsum_le, hb_c.trans hsum_le⟩

/-! ## 5. Leaf propositions of `PartII-b:F2/4` (SP 978–1003, 2104–2115, 2147–2155) -/

/-- **Free transport convergence at fixed data** (the conclusion of `FreeTransportComparison`,
SP 2104–2115): for every compact set `K ⊆ X_m` and tolerance `ε > 0` there are `δ, ν₀ ∈ (0, 1]`
such that at every `BgRegime` point with `p.ν ≤ ν₀`, `p.ageCut = Sig` and
`TrainCloseM m p.train Sig δ`, every free cylinder propagator `Sc` (`IsFreeCylPropagator m p Sc`)
and every block `[t, t + L] ⊆ [0, p.H]` of length `L ≤ Lmax` satisfy `‖Sc(t + L, t)‖ ≤ 1 + ε`
and `‖W_{ν,t} f - f‖ ≤ ε` for `f ∈ K`, where `W_{ν,t} = J_c ∘ Sc(t + L, t) ∘ R_c ∘ T_pl(ν t, -L)`
("Multiplying by its inverse reduces the free convergence to `W_ν → I` strongly with
`‖W_ν‖ ≤ 1 + o(1)`", SP 2110–2112). -/
def FreeTransportConverges (m Sig Lmax : ℝ) (T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m))
    (dm dp : ℝ) : Prop :=
  ∀ K : Set (Xm m), IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ (δ ν₀ : ℝ), 0 < δ ∧ δ ≤ 1 ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
        TrainCloseM m p.train Sig δ →
      ∀ Sc : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m), IsFreeCylPropagator m p Sc →
      ∀ t L : ℝ, 0 ≤ t → 0 ≤ L → L ≤ Lmax → t + L ≤ p.H →
        ‖Sc (t + L) t‖ ≤ 1 + ε ∧
        ∀ f ∈ K, ‖Jc p.c m (Sc (t + L) t (Rc p.c m (T_pl (p.ν * t) (-L) f))) - f‖ ≤ ε

/-- **Leaf 1 (`PartII-b:F2/4/1`, free transport comparison, SP 2104–2115)**: for `m > 8`,
`Sig, Lmax > 0` and the frozen radial transport group `T_pl` (`IsFrozenRadialTransport m Sig T_pl`),
the lifted free cylinder propagator converges strongly to the frozen radial transport on blocks of
length at most `Lmax`, uniformly in the block position and on compact sets, in the form
`FreeTransportConverges m Sig Lmax T_pl dm dp`: Duhamel for a smooth compactly supported datum
against the frozen radial transport (viscosity error `νΔ` on the datum, coefficient change
`O(νL) + o(1)` on the fixed disk carrying the transported support), density, and the
free-cylinder bound `short-bg:free-cylinder` (`freeCylinderBound_proof`, which also gives
`‖Sc(t + L, t)‖ ≤ exp[(C_m ν + C δ + C e^{-b c²}) L] → 1`). -/
def FreeTransportComparison : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (Sig Lmax : ℝ), 0 < Sig → 0 < Lmax →
  ∀ T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m), IsFrozenRadialTransport m Sig T_pl →
  ∀ dm dp : ℝ, 0 < dm →
    FreeTransportConverges m Sig Lmax T_pl dm dp

/-- **Leaf 2 (`PartII-b:F2/4/2`, bounds and compact Duhamel family of the frozen planar Euler
evolution, SP 841–852, 2147–2150)**: let `AplOp` be a norm-continuous family of compact planar
interactions `A_{pl,σ}` on `[0, Sig]` whose images of balls are collectively totally bounded, let
`T_pl` be the frozen radial transport group, and let `E_pl σ` be the strongly continuous mild
Duhamel evolution `E_pl σ τ = T_pl σ τ + ∫₀^τ T_pl σ (τ - r) A_{pl,σ} E_pl σ r dr`. Then
`‖E_pl σ τ‖` is bounded uniformly on `[0, Sig] × [0, Lmax]` (Gronwall, `T_pl` isometric), and
the Duhamel terms `E_pl σ τ - T_pl σ τ`, `σ ∈ [0, Sig]`, `τ ∈ [0, Lmax]`, map every ball into one
totally bounded set ("its limit is compact", SP 2150: the integrand lies in the image of a totally
bounded set under the jointly strongly continuous isometries `T_pl σ s`). -/
def PlanarDuhamelCollectiveCompact : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (Sig Lmax : ℝ), 0 < Sig → 0 < Lmax →
  ∀ AplOp : ℝ → (Xm m →L[ℝ] Xm m),
    ContinuousOn AplOp (Icc 0 Sig) →
    (∀ σ ∈ Icc 0 Sig, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)) →
    (∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sig, AplOp σ '' Metric.closedBall (0 : Xm m) R)) →
  ∀ (T_pl E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)), IsFrozenRadialTransport m Sig T_pl →
    (∀ σ ∈ Icc 0 Sig, ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0)) →
    (∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
      IntervalIntegrable (fun r => T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) volume 0 τ ∧
      E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) →
    (∃ M_op : ℝ, 1 ≤ M_op ∧ ∀ σ ∈ Icc 0 Sig, ∀ τ ∈ Icc 0 Lmax, ‖E_pl σ τ‖ ≤ M_op) ∧
    ∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sig, ⋃ τ ∈ Icc 0 Lmax,
      (E_pl σ τ - T_pl σ τ) '' Metric.closedBall (0 : Xm m) R)

/-- **Leaf 3 (`PartII-b:F2/4/3`, compact-Duhamel norm convergence of the interaction Duhamel
term, SP 978–1003, 2147–2150)**: with `AplOp`, `T_pl`, `E_pl` as in
`PlanarDuhamelCollectiveCompact`, and given the free transport convergence
`FreeTransportConverges m Sig Lmax T_pl dm dp` (leaf 1), for every `η > 0` there are
`δ, ν₀ ∈ (0, 1]` such that at every `BgRegime` point with `p.ν ≤ ν₀`, `p.ageCut = Sig`,
`TrainCloseM m p.train Sig δ`, for every coupled Duhamel propagator
`IsCoupledDuhamelPropagator m p Sc Ac U` whose lifted interactions satisfy the comparison bound
`‖J_c A_c(s) R_c - A_{pl,νs}‖ ≤ C_Sg (c⁻² + δ)` (`short-bg:interaction-cylinder`), and every block
`[t, t + L] ⊆ [0, p.H]` with `L ≤ Lmax`, the lifted interaction Duhamel term is norm-close to the
frozen planar one: `‖J_c (U(t+L,t) - Sc(t+L,t)) R_c - (E_pl(νt, L) - T_pl(νt, L))‖ ≤ η`
("the interaction Duhamel term converges in norm", SP 2149; the compact-Duhamel lemma, SP 978–1003:
strong convergence of the free evolutions with their adjoints, norm convergence of the
interactions, a norm-compact family of compact limits). -/
def CompactDuhamelNormConvergence : Prop :=
  ∀ m : ℝ, 8 < m → ∀ (Sig Lmax : ℝ), 0 < Sig → 0 < Lmax →
  ∀ (C_Sg : ℝ) (AplOp : ℝ → (Xm m →L[ℝ] Xm m)), 0 < C_Sg →
    ContinuousOn AplOp (Icc 0 Sig) →
    (∀ σ ∈ Icc 0 Sig, IsPlanarInteractionOp m σ (AplOp σ) ∧ IsCompactOperator (AplOp σ)) →
    TotallyBounded (AplOp '' Icc 0 Sig) →
    (∀ R : ℝ, TotallyBounded (⋃ σ ∈ Icc 0 Sig, AplOp σ '' Metric.closedBall (0 : Xm m) R)) →
  ∀ (T_pl E_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)), IsFrozenRadialTransport m Sig T_pl →
    (∀ σ ∈ Icc 0 Sig, ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0)) →
    (∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
      IntervalIntegrable (fun r => T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) volume 0 τ ∧
      E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) →
  ∀ dm dp : ℝ, 0 < dm →
    FreeTransportConverges m Sig Lmax T_pl dm dp →
  ∀ η : ℝ, 0 < η →
    ∃ (δ ν₀ : ℝ), 0 < δ ∧ δ ≤ 1 ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig →
        TrainCloseM m p.train Sig δ →
      ∀ (Sc U : ℝ → ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m))
        (Ac : ℝ → (Xmc p.c m →L[ℝ] Xmc p.c m)),
        IsCoupledDuhamelPropagator m p Sc Ac U →
        (∀ s ∈ Icc 0 p.H,
          ‖(Jc p.c m).comp ((Ac s).comp (Rc p.c m)) - AplOp (p.ν * s)‖ ≤
            C_Sg * (p.c ^ (-2 : ℝ) + δ)) →
        ∀ t L : ℝ, 0 ≤ t → 0 ≤ L → L ≤ Lmax → t + L ≤ p.H →
          ‖(Jc p.c m).comp ((U (t + L) t - Sc (t + L) t).comp (Rc p.c m)) -
              (E_pl (p.ν * t) L - T_pl (p.ν * t) L)‖ ≤ η

/-! ## 6. Hilbert-space and compactness helpers -/

namespace PartIIbF24Sub

/-- Monotonicity of `TrainCloseM` in the tolerance. -/
theorem trainCloseM_mono {ν c m : ℝ} {tr : B0140.TrainSol ν c} {Sg δ δ' : ℝ}
    (h : TrainCloseM m tr Sg δ) (hδ : δ ≤ δ') : TrainCloseM m tr Sg δ' :=
  fun s hs0 hs1 x hx j hj => (h s hs0 hs1 x hx j hj).trans hδ

/-- The identity behind strong adjoint convergence (SP 2112–2113):
`‖W* k - k‖² ≤ (‖W‖² - 1) ‖k‖² + 2 ‖k‖ ‖W k - k‖` on a real Hilbert space. -/
theorem norm_adjoint_apply_sub_sq_le {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (W : X →L[ℝ] X) (k : X) :
    ‖ContinuousLinearMap.adjoint W k - k‖ ^ 2 ≤
      (‖W‖ ^ 2 - 1) * ‖k‖ ^ 2 + 2 * ‖k‖ * ‖W k - k‖ := by
  have h1 := norm_sub_sq_real (ContinuousLinearMap.adjoint W k) k
  have h2 : inner ℝ (ContinuousLinearMap.adjoint W k) k = inner ℝ k (W k) :=
    ContinuousLinearMap.adjoint_inner_left W k k
  have h3 : ‖ContinuousLinearMap.adjoint W k‖ ≤ ‖W‖ * ‖k‖ := by
    calc ‖ContinuousLinearMap.adjoint W k‖ ≤ ‖ContinuousLinearMap.adjoint W‖ * ‖k‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖W‖ * ‖k‖ := by rw [LinearIsometryEquiv.norm_map]
  have h4 : inner ℝ k (W k) = ‖k‖ ^ 2 + inner ℝ k (W k - k) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
  have h5 : |inner ℝ k (W k - k)| ≤ ‖k‖ * ‖W k - k‖ := abs_real_inner_le_norm _ _
  have h6 : ‖ContinuousLinearMap.adjoint W k‖ ^ 2 ≤ (‖W‖ * ‖k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h7 := neg_abs_le (inner ℝ k (W k - k))
  rw [mul_pow] at h6
  rw [h1, h2, h4]
  nlinarith [h5, h6, h7]

/-- `‖π ∘ (W - 1)‖ ≤ η` from the bound `‖W* k - k‖ ≤ η` on `k = π* α`, `‖α‖ ≤ 1`. -/
theorem norm_comp_sub_id_le_of_adjoint {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (π : X →L[ℝ] E2) (W : X →L[ℝ] X) {η : ℝ}
    (hη : 0 ≤ η)
    (h : ∀ α : E2, ‖α‖ ≤ 1 →
      ‖ContinuousLinearMap.adjoint W (ContinuousLinearMap.adjoint π α) -
          ContinuousLinearMap.adjoint π α‖ ≤ η) :
    ‖π.comp (W - ContinuousLinearMap.id ℝ X)‖ ≤ η := by
  have hadj : ‖π.comp (W - ContinuousLinearMap.id ℝ X)‖ =
      ‖ContinuousLinearMap.adjoint (π.comp (W - ContinuousLinearMap.id ℝ X))‖ :=
    (LinearIsometryEquiv.norm_map _ _).symm
  rw [hadj, ContinuousLinearMap.adjoint_comp, map_sub, ContinuousLinearMap.adjoint_id]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hη fun α hα => ?_
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply] using h α hα.le

/-- Compactness of the coordinate image `{ι σ α : σ ∈ [0, Sig], ‖α‖ ≤ 1}` of a continuous
coordinate family. -/
theorem isCompact_coord_image {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Sig : ℝ}
    (ι : ℝ → (E2 →L[ℝ] Y)) (hι : ContinuousOn ι (Icc 0 Sig)) :
    IsCompact ((fun z : ℝ × E2 => ι z.1 z.2) '' (Icc 0 Sig ×ˢ closedBall (0 : E2) 1)) := by
  refine (isCompact_Icc.prod (isCompact_closedBall (0 : E2) 1)).image_of_continuousOn ?_
  exact (hι.comp continuousOn_fst (fun z hz => hz.1)).clm_apply continuousOn_snd

end PartIIbF24Sub

/-! ## 7. Assembly of `PlanarCompactDuhamelComparison` and `CompactDuhamelBlockStep` -/

set_option maxHeartbeats 4000000 in
/-- **`PlanarCompactDuhamelComparison` from the three leaves** (SP 2104–2115, 2147–2158): with
`W = J_c Sc(t + L, t) R_c T_pl(νt, -L)`, the Duhamel relations give
`U_lift - W E_pl(νt, L) = (D_ν - D) + (1 - W) D` with `D_ν = J_c (U - Sc) R_c` and
`D = E_pl(νt, L) - T_pl(νt, L)`; `D_ν - D` is norm-small by `CompactDuhamelNormConvergence`,
`(1 - W) D` is norm-small since `W → 1` uniformly on the compact closure of the Duhamel family
(`PlanarDuhamelCollectiveCompact`), `‖W‖ ≤ 1 + o(1)` and `W → 1` on the compact coordinate sets
by `FreeTransportComparison`, and the adjoint identity gives `π_pl (W - 1) → 0`; then
`planar_blocks_of_weyl_factorization` yields the four planar block bounds, `euler_comm` the
vanishing upper-right planar block, and `‖U(t + L, t)‖ ≤ ‖W E_pl‖ + o(1)` the propagator bound. -/
theorem planarCompactDuhamelComparison_of
    (hF : FreeTransportComparison) (hP : PlanarDuhamelCollectiveCompact)
    (hC : CompactDuhamelNormConvergence) :
    PlanarCompactDuhamelComparison := by
  intro m hm Sig lam q hSig _hEig L₀ M_E c₀ ι_pl π_pl E_pl ι_c π_c hPkg
    K₀ C_Sg AplOp _hK₀ hC_Sg hApl_cont hApl_prop hApl_tb hApl_ball dm dp hdm η_op hη_op
  have hM_E : 1 ≤ M_E := hPkg.M_E_ge_one
  have hL₀ : 1 ≤ L₀ := hPkg.L₀_ge_one
  have hLmax : 0 < 2 * L₀ := by linarith
  obtain ⟨T_pl, hT, hDuh⟩ := hPkg.euler_duhamel
  have hEcont : ∀ σ ∈ Icc 0 Sig, ∀ f : Xm m, ContinuousOn (fun τ => E_pl σ τ f) (Ici 0) :=
    fun σ hσ => (hPkg.euler_semigroup σ hσ).2.2
  have hDuhA : ∀ σ ∈ Icc 0 Sig, ∀ τ : ℝ, 0 ≤ τ → ∀ f : Xm m,
      IntervalIntegrable (fun r => T_pl σ (τ - r) (AplOp σ (E_pl σ r f))) volume 0 τ ∧
      E_pl σ τ f = T_pl σ τ f + ∫ r in (0 : ℝ)..τ, T_pl σ (τ - r) (AplOp σ (E_pl σ r f)) :=
    fun σ hσ => hDuh σ hσ (AplOp σ) (hApl_prop σ hσ).1
  obtain ⟨⟨M_op, hM_op1, hM_op⟩, hTB⟩ :=
    hP m hm Sig (2 * L₀) hSig hLmax AplOp hApl_cont hApl_prop hApl_ball T_pl E_pl hT hEcont
      hDuhA
  set M₁ : ℝ := max M_op (Real.exp (|lam.re| * (2 * L₀))) with hM₁_def
  have hM₁ : 1 ≤ M₁ := hM_op1.trans (le_max_left _ _)
  have hME_pos : 0 < M_E := by linarith
  set C_weyl : ℝ := 12 * M_E ^ 4 * M₁ with hC_weyl_def
  have hC_weyl : 0 < C_weyl :=
    mul_pos (mul_pos (by norm_num) (pow_pos hME_pos 4)) (by linarith)
  set η : ℝ := min 1 (η_op / C_weyl) with hη_def
  have hη : 0 < η := lt_min one_pos (div_pos hη_op hC_weyl)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hCη : C_weyl * η ≤ η_op := by
    calc C_weyl * η ≤ C_weyl * (η_op / C_weyl) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hC_weyl.le
      _ = η_op := mul_div_cancel₀ η_op hC_weyl.ne'
  have hME2 : 1 ≤ M_E ^ 2 := one_le_pow₀ hM_E
  have h5M : 0 < 5 * M_E ^ 2 := mul_pos (by norm_num) (pow_pos hME_pos 2)
  set ε₁ : ℝ := η ^ 2 / (5 * M_E ^ 2) with hε₁_def
  have hε₁ : 0 < ε₁ := div_pos (pow_pos hη 2) h5M
  have hε₁_eq : 5 * ε₁ * M_E ^ 2 = η ^ 2 := by
    rw [hε₁_def]
    calc 5 * (η ^ 2 / (5 * M_E ^ 2)) * M_E ^ 2 = η ^ 2 * ((5 * M_E ^ 2) / (5 * M_E ^ 2)) := by
          ring
      _ = η ^ 2 := by rw [div_self h5M.ne', mul_one]
  have hε₁_le : ε₁ ≤ η / 2 := by
    rw [hε₁_def, div_le_iff₀ h5M]
    nlinarith [mul_le_mul_of_nonneg_left hME2 hη.le, mul_le_mul_of_nonneg_left hη1 hη.le]
  have hε₁_le1 : ε₁ ≤ 1 := by linarith
  -- the three compact sets on which `W → 1` is used
  set Kι : Set (Xm m) :=
    (fun z : ℝ × E2 => ι_pl z.1 z.2) '' (Icc 0 Sig ×ˢ closedBall (0 : E2) 1) with hKι_def
  set Kπ : Set (Xm m) :=
    (fun z : ℝ × E2 => ContinuousLinearMap.adjoint (π_pl z.1) z.2) ''
      (Icc 0 Sig ×ˢ closedBall (0 : E2) 1) with hKπ_def
  set KD : Set (Xm m) := closure (⋃ σ ∈ Icc 0 Sig, ⋃ τ ∈ Icc 0 (2 * L₀),
      (E_pl σ τ - T_pl σ τ) '' closedBall (0 : Xm m) 1) with hKD_def
  have hKι : IsCompact Kι := PartIIbF24Sub.isCompact_coord_image ι_pl hPkg.pl_cont.1
  have hKπ : IsCompact Kπ := PartIIbF24Sub.isCompact_coord_image
    (fun σ => ContinuousLinearMap.adjoint (π_pl σ))
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Xm m) (F := E2)).continuous.comp_continuousOn
      hPkg.pl_cont.2)
  have hKD : IsCompact KD :=
    isCompact_iff_totallyBounded_isComplete.2 ⟨(hTB 1).closure, isClosed_closure.isComplete⟩
  have hFree := hF m hm Sig (2 * L₀) hSig hLmax T_pl hT dm dp hdm
  obtain ⟨δ₁, ν₁, hδ₁, hδ₁1, hν₁, hν₁1, hW⟩ :=
    hFree (Kι ∪ Kπ ∪ KD) ((hKι.union hKπ).union hKD) ε₁ hε₁
  obtain ⟨δ₃, ν₃, hδ₃, hδ₃1, hν₃, hν₃1, hDν⟩ :=
    hC m hm Sig (2 * L₀) hSig hLmax C_Sg AplOp hC_Sg hApl_cont hApl_prop hApl_tb hApl_ball
      T_pl E_pl hT hEcont hDuhA dm dp hdm hFree (η / 2) (half_pos hη)
  refine ⟨2 * M₁ + 1, min δ₁ δ₃, min ν₁ ν₃, by linarith, lt_min hδ₁ hδ₃,
    (min_le_left _ _).trans hδ₁1, lt_min hν₁ hν₃, (min_le_left _ _).trans hν₁1, ?_⟩
  intro p d hbg hν _hc hAge _hMode hTCM Sc U Ac hCD hAc _hSc t L ht htL hL
  intro σ₀ Ppl₀ Q₀ U_lift
  have hν0 : 0 < p.ν := p.ν_pos
  have hL_nn : 0 ≤ L := (zero_le_one.trans hL₀).trans hL.1
  have hL_le : L ≤ 2 * L₀ := hL.2
  have hH_eq : p.H = Sig / p.ν := by
    change p.ageCut / p.ν = Sig / p.ν
    rw [hAge]
  have hσ₀ : p.ν * t ∈ Icc 0 Sig := by
    refine ⟨mul_nonneg hν0.le ht, ?_⟩
    have ht_le_H : t ≤ Sig / p.ν := hH_eq ▸ (by linarith : t ≤ p.H)
    calc p.ν * t ≤ p.ν * (Sig / p.ν) := mul_le_mul_of_nonneg_left ht_le_H hν0.le
      _ = Sig := mul_div_cancel₀ Sig hν0.ne'
  have hTCM₁ : TrainCloseM m p.train Sig δ₁ :=
    PartIIbF24Sub.trainCloseM_mono hTCM (min_le_left _ _)
  have hTCM₃ : TrainCloseM m p.train Sig δ₃ :=
    PartIIbF24Sub.trainCloseM_mono hTCM (min_le_right _ _)
  obtain ⟨hSc_norm, hWK⟩ := hW p d hbg (hν.trans (min_le_left _ _)) hAge hTCM₁ Sc hCD.free_prop
    t L ht hL_nn hL_le htL
  have hAc₃ : ∀ s ∈ Icc 0 p.H,
      ‖(Jc p.c m).comp ((Ac s).comp (Rc p.c m)) - AplOp (p.ν * s)‖ ≤
        C_Sg * (p.c ^ (-2 : ℝ) + δ₃) := fun s hs =>
    (hAc s hs).2.trans
      (mul_le_mul_of_nonneg_left (by linarith [min_le_right δ₁ δ₃]) hC_Sg.le)
  have hDν_bd := hDν p d hbg (hν.trans (min_le_right _ _)) hAge hTCM₃ Sc U Ac hCD hAc₃
    t L ht hL_nn hL_le htL
  -- the free comparison operator `W = J_c Sc(t + L, t) R_c T_pl(νt, -L)`
  obtain ⟨W, hW_def⟩ : ∃ W : Xm m →L[ℝ] Xm m,
      W = (Jc p.c m).comp ((Sc (t + L) t).comp ((Rc p.c m).comp (T_pl (p.ν * t) (-L)))) :=
    ⟨_, rfl⟩
  have hW_apply : ∀ f, W f = Jc p.c m (Sc (t + L) t (Rc p.c m (T_pl (p.ν * t) (-L) f))) := by
    intro f; rw [hW_def]; rfl
  have hT_norm : ‖T_pl (p.ν * t) (-L)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
      rw [hT.isometry (p.ν * t) hσ₀ (-L) f, one_mul]
  have hW_norm₁ : ‖W‖ ≤ 1 + ε₁ := by
    rw [hW_def]
    calc ‖(Jc p.c m).comp ((Sc (t + L) t).comp ((Rc p.c m).comp (T_pl (p.ν * t) (-L))))‖
        ≤ ‖Jc p.c m‖ * (‖Sc (t + L) t‖ * (‖Rc p.c m‖ * ‖T_pl (p.ν * t) (-L)‖)) := by
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _)
      _ ≤ 1 * ((1 + ε₁) * (1 * 1)) :=
          mul_le_mul (norm_Jc_le p.c m)
            (mul_le_mul hSc_norm
              (mul_le_mul (norm_Rc_le p.c m) hT_norm (norm_nonneg _) zero_le_one)
              (by positivity) (by linarith))
            (by positivity) zero_le_one
      _ = 1 + ε₁ := by ring
  have hW_norm : ‖W‖ ≤ 1 + η := hW_norm₁.trans (by linarith)
  -- `W → 1` on the growing plane
  have hWι : ‖(W - ContinuousLinearMap.id ℝ (Xm m)).comp (ι_pl (p.ν * t))‖ ≤ η := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm hη.le fun α hα => ?_
    have hmem : ι_pl (p.ν * t) α ∈ Kι :=
      ⟨(p.ν * t, α), ⟨hσ₀, mem_closedBall_zero_iff.2 hα.le⟩, rfl⟩
    have h1 := hWK (ι_pl (p.ν * t) α) (Or.inl (Or.inl hmem))
    rw [← hW_apply] at h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    linarith
  -- strong adjoint convergence on the dual plane
  have hWπ : ‖(π_pl (p.ν * t)).comp (W - ContinuousLinearMap.id ℝ (Xm m))‖ ≤ η := by
    refine PartIIbF24Sub.norm_comp_sub_id_le_of_adjoint _ W hη.le fun α hα => ?_
    have hmem : ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α ∈ Kπ :=
      ⟨(p.ν * t, α), ⟨hσ₀, mem_closedBall_zero_iff.2 hα⟩, rfl⟩
    have hWk : ‖W (ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α) -
        ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ≤ ε₁ := by
      rw [hW_apply]; exact hWK _ (Or.inl (Or.inr hmem))
    have hk : ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ≤ M_E := by
      calc ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖
          ≤ ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t))‖ * ‖α‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖π_pl (p.ν * t)‖ * ‖α‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ M_E * 1 :=
            mul_le_mul (hPkg.pl_proj_id _ hσ₀).2.2 hα (norm_nonneg _) (by linarith)
        _ = M_E := mul_one _
    have hsq := PartIIbF24Sub.norm_adjoint_apply_sub_sq_le W
      (ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α)
    have hWsq : ‖W‖ ^ 2 - 1 ≤ 3 * ε₁ := by
      nlinarith [norm_nonneg W, mul_le_mul hW_norm₁ hW_norm₁ (norm_nonneg W)
        (by linarith : (0 : ℝ) ≤ 1 + ε₁), mul_le_mul_of_nonneg_left hε₁_le1 hε₁.le]
    have hk_nn := norm_nonneg (ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α)
    have h1 : (‖W‖ ^ 2 - 1) * ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ^ 2 ≤
        3 * ε₁ * ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hWsq (sq_nonneg _)
    have h2 : ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ^ 2 ≤ M_E ^ 2 :=
      pow_le_pow_left₀ hk_nn hk 2
    have h3 := mul_le_mul hk hWk (norm_nonneg _) hME_pos.le
    have h4 : 3 * ε₁ * ‖ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ^ 2 ≤
        3 * ε₁ * M_E ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : M_E * ε₁ ≤ M_E ^ 2 * ε₁ := mul_le_mul_of_nonneg_right (by nlinarith) hε₁.le
    have hbound : ‖ContinuousLinearMap.adjoint W (ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α) -
        ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α‖ ^ 2 ≤ η ^ 2 := by
      nlinarith [hsq, h1, h3, h4, h5, hε₁_eq]
    have h_nn := norm_nonneg (ContinuousLinearMap.adjoint W
      (ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α) -
        ContinuousLinearMap.adjoint (π_pl (p.ν * t)) α)
    nlinarith
  -- the factorization `U_lift = W E_pl + (D_ν - D) + (1 - W) D`
  obtain ⟨D, hD_def⟩ : ∃ D : Xm m →L[ℝ] Xm m,
      D = E_pl (p.ν * t) L - T_pl (p.ν * t) L := ⟨_, rfl⟩
  obtain ⟨Dν, hDν_def⟩ : ∃ Dν : Xm m →L[ℝ] Xm m,
      Dν = (Jc p.c m).comp ((U (t + L) t - Sc (t + L) t).comp (Rc p.c m)) := ⟨_, rfl⟩
  have hTT : ∀ g, T_pl (p.ν * t) (-L) (T_pl (p.ν * t) L g) = g := by
    intro g
    have h := hT.add (p.ν * t) hσ₀ (-L) L
    rw [neg_add_cancel, hT.zero (p.ν * t) hσ₀] at h
    have h' := congrArg (fun A : Xm m →L[ℝ] Xm m => A g) h
    simpa using h'.symm
  have h_split : (Jc p.c m).comp ((U (t + L) t).comp (Rc p.c m)) - W.comp (E_pl (p.ν * t) L) =
      (Dν - D) + (D - W.comp D) := by
    ext1 f
    rw [hDν_def, hD_def]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.comp_apply, map_sub, hW_apply, hTT]
    abel
  have hR : ‖(Jc p.c m).comp ((U (t + L) t).comp (Rc p.c m)) - W.comp (E_pl (p.ν * t) L)‖ ≤
      η := by
    rw [h_split]
    have h1 : ‖Dν - D‖ ≤ η / 2 := by rw [hDν_def, hD_def]; exact hDν_bd
    have h2 : ‖D - W.comp D‖ ≤ η / 2 := by
      refine ContinuousLinearMap.opNorm_le_of_unit_norm (by linarith) fun f hf => ?_
      have hmem : D f ∈ KD := by
        refine subset_closure ?_
        rw [hD_def]
        exact mem_iUnion₂.2 ⟨p.ν * t, hσ₀, mem_iUnion₂.2 ⟨L, ⟨hL_nn, hL_le⟩,
          ⟨f, mem_closedBall_zero_iff.2 hf.le, rfl⟩⟩⟩
      have h3 := hWK (D f) (Or.inr hmem)
      rw [← hW_apply] at h3
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, norm_sub_rev]
      linarith
    calc ‖(Dν - D) + (D - W.comp D)‖ ≤ ‖Dν - D‖ + ‖D - W.comp D‖ := norm_add_le _ _
      _ ≤ η / 2 + η / 2 := add_le_add h1 h2
      _ = η := by ring
  -- bounds on `E_pl(νt, L)` and on its action on the growing plane
  have hE_norm : ‖E_pl (p.ν * t) L‖ ≤ M₁ :=
    (hM_op _ hσ₀ L ⟨hL_nn, hL_le⟩).trans (le_max_left _ _)
  have hE_eig : (E_pl (p.ν * t) L).comp (ι_pl (p.ν * t)) =
      (ι_pl (p.ν * t)).comp
        (PartIIbF23Sub.rotScaleCLM (Real.exp (lam.re * L / (1 + p.ν * t) ^ 2))
          (lam.im * L / (1 + p.ν * t) ^ 2)) :=
    hPkg.euler_eigen (p.ν * t) hσ₀ L hL_nn
  have hM_norm : ‖PartIIbF23Sub.rotScaleCLM (Real.exp (lam.re * L / (1 + p.ν * t) ^ 2))
      (lam.im * L / (1 + p.ν * t) ^ 2)‖ ≤ M₁ := by
    refine (PartIIbF23Sub.norm_rotScaleCLM_le (Real.exp_pos _).le _).trans ?_
    refine le_trans ?_ (le_max_right _ _)
    refine Real.exp_le_exp.2 ?_
    have h1 : 1 ≤ (1 + p.ν * t) ^ 2 := one_le_pow₀ (by linarith [hσ₀.1])
    have h2 : lam.re * L ≤ |lam.re| * L := mul_le_mul_of_nonneg_right (le_abs_self _) hL_nn
    have h3 : |lam.re| * L / (1 + p.ν * t) ^ 2 ≤ |lam.re| * L :=
      div_le_self (mul_nonneg (abs_nonneg _) hL_nn) h1
    have h4 : lam.re * L / (1 + p.ν * t) ^ 2 ≤ |lam.re| * L / (1 + p.ν * t) ^ 2 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have h5 : |lam.re| * L ≤ |lam.re| * (2 * L₀) :=
      mul_le_mul_of_nonneg_left hL_le (abs_nonneg _)
    linarith
  obtain ⟨hb1, hb2, hb3, hb4⟩ := planar_blocks_of_weyl_factorization hM_E hM₁ hη.le
    (ι_pl (p.ν * t)) (π_pl (p.ν * t))
    ((Jc p.c m).comp ((U (t + L) t).comp (Rc p.c m))) (E_pl (p.ν * t) L) W
    (PartIIbF23Sub.rotScaleCLM (Real.exp (lam.re * L / (1 + p.ν * t) ^ 2))
      (lam.im * L / (1 + p.ν * t) ^ 2))
    (hPkg.pl_proj_id _ hσ₀).2.1 (hPkg.pl_proj_id _ hσ₀).2.2 hE_norm hM_norm hE_eig hR hW_norm
    hWι hWπ
  -- the propagator bound
  have hU : ‖U (t + L) t‖ ≤ 2 * M₁ + 1 := by
    rw [← norm_eq_norm_Jc_comp_Rc p.c m (U (t + L) t)]
    have h1 := norm_sub_norm_le ((Jc p.c m).comp ((U (t + L) t).comp (Rc p.c m)))
      (W.comp (E_pl (p.ν * t) L))
    have h2 : ‖W.comp (E_pl (p.ν * t) L)‖ ≤ (1 + η) * M₁ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hW_norm hE_norm (norm_nonneg _) (by linarith))
    have h3 : η * M₁ ≤ 1 * M₁ := mul_le_mul_of_nonneg_right hη1 (by linarith)
    nlinarith [h1, h2, hR, h3]
  -- the vanishing upper-right planar block
  have h_pl_b : (π_pl (p.ν * t)).comp ((E_pl (p.ν * t) L).comp
      (ContinuousLinearMap.id ℝ (Xm m) - (ι_pl (p.ν * t)).comp (π_pl (p.ν * t)))) = 0 := by
    have h_comm := hPkg.euler_comm (p.ν * t) hσ₀ L hL_nn
    have h_proj_id := (hPkg.pl_proj_id (p.ν * t) hσ₀).1
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.comp_sub, h_comm,
      ← ContinuousLinearMap.comp_assoc (π_pl (p.ν * t))
        ((ι_pl (p.ν * t)).comp (π_pl (p.ν * t))) (E_pl (p.ν * t) L),
      ← ContinuousLinearMap.comp_assoc (π_pl (p.ν * t)) (ι_pl (p.ν * t)) (π_pl (p.ν * t)),
      h_proj_id, ContinuousLinearMap.id_comp, sub_self]
  exact ⟨hU, h_pl_b, hb1.trans hCη, hb2.trans (add_le_add le_rfl hCη), hb3.trans hCη,
    hb4.trans hCη⟩

/-- **Full derivation of `CompactDuhamelBlockStep` (`PartII-b:F2/4`)** from the three leaves
`FreeTransportComparison` (`PartII-b:F2/4/1`), `PlanarDuhamelCollectiveCompact`
(`PartII-b:F2/4/2`) and `CompactDuhamelNormConvergence` (`PartII-b:F2/4/3`); composed by task
`PartII-b:F2/4` in `Tasks/BlockFactorization/CompactDuhamelBlock.lean`. -/
theorem compactDuhamelBlockStep_of
    (hF : FreeTransportComparison) (hP : PlanarDuhamelCollectiveCompact)
    (hC : CompactDuhamelNormConvergence) :
    CompactDuhamelBlockStep :=
  compactDuhamelBlockStep_of_planarComparison (planarCompactDuhamelComparison_of hF hP hC)

end UnforcedLeray.Short.IIb
