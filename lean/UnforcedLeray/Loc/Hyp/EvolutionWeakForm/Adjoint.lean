import UnforcedLeray.Loc.L13PhysicalRemainder
import UnforcedLeray.Units.B0418.Generator
import UnforcedLeray.Analysis.Heat.SelfAdjoint

/-!
# H-EvolWeak, helper: the adjoint free evolution on tests and its generator

Support for `Loc/Hyp/EvolutionWeakForm.lean` (the named hypothesis `EvolutionWeakForm` of
`Loc/L13PhysicalRemainder.lean`; `paper/main.tex` lines 292–306, `loc:eq:free-evolution`, and
406–417; blueprint units B0712, B0713, B0418).

The free evolution `S₀(u)f(y) = e^{u/2}[e^{h(e^u-1)Δ}f](e^{u/2}y)` (line 294) is, on `L²`, the
compiled `L02.freeL2 h u = D(u) ∘ e^{h(e^u-1)Δ}`. Its `L²` adjoint on a vector test `φ` is

  `S₀(u)^*φ = e^{h(e^u-1)Δ}[e^{-u} φ(e^{-u/2}·)]`        (`adjTest h φ u`),

by the change of variables of the dilation (`L13.dil_inner_toL2`) and the symmetry of the heat
semigroup (`Heat.heatOperator_inner`). Its generator on tests is the formal adjoint of
`𝓛₀ = hΔ + ½y·∇ + ½` (line 293):

  `u⁻¹(S₀(u)^*φ - φ) → hΔφ - φ - ½ y·∇φ` in `L²` as `u → 0⁺`    (`tendsto_adjTest_slope`).

Proof: `S₀(u)^*φ - φ = e^{tΔ}(w(u) - w(0)) + (e^{tΔ}φ - φ)` with `t = h(e^u-1)` and
`w(u) = e^{-u}φ(e^{-u/2}·)`. The first part uses the two-sided `L²` derivative of dilated
tests (`L13.hasDerivAt_testDilation_zero`) and the contraction and strong continuity of the
heat semigroup; the second is the heat generator on `C_c^∞` (`B0418.tendsto_heat_generator`,

`t/u → h`. This is the adjoint (test-function) form of the generator statement of B0418,
which proves only the forward one-sided limit on tests.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint.EvolWeak

open SobolevGraph
open UnforcedLeray.Loc.L02 (dil freeL2 heatTime heatTime_pos dil_heatOperator coeFn_freeL2)
open UnforcedLeray.Blueprint.L13 (testDilation radialDeriv dil_inner_toL2 isVectorTest_memLp
  isVectorTest_radialDeriv hasDerivAt_testDilation_zero toL2_of_ae_eq_coeFn)

/-! ## The adjoint free evolution on a test -/

/-- `w(u) = e^{-u} φ(e^{-u/2}·)`, the dilation part of `S₀(u)^*φ`. -/
def dualDil (φ : Space → Space) (u : ℝ) : L2Space := Real.exp (-u) • testDilation φ (-u)

/-- `S₀(u)^*φ = e^{h(e^u-1)Δ}[e^{-u} φ(e^{-u/2}·)]`, the `L²` adjoint of the free evolution of
line 294 applied to the test `φ`. -/
def adjTest (h : ℝ) (φ : Space → Space) (u : ℝ) : L2Space :=
  Heat.heatOperator (heatTime h u) (dualDil φ u)

/-- The formal adjoint `𝓛₀^*φ = hΔφ - φ - ½ y·∇φ` of `𝓛₀ = hΔ + ½y·∇ + ½` (line 293). -/
def adjGen (h : ℝ) (φ : Space → Space) : L2Space :=
  h • toL2 (B0418.vecLaplacian φ) + (-(toL2 φ) - (1 / 2 : ℝ) • toL2 (radialDeriv φ))

theorem testDilation_zero (φ : Space → Space) : testDilation φ 0 = toL2 φ := by
  unfold testDilation
  congr 1
  funext y
  simp

theorem dualDil_zero (φ : Space → Space) : dualDil φ 0 = toL2 φ := by
  simp [dualDil, testDilation_zero]

theorem heatTime_zero (h : ℝ) : heatTime h 0 = 0 := by simp [heatTime]

theorem adjTest_zero (h : ℝ) (φ : Space → Space) : adjTest h φ 0 = toL2 φ := by
  simp [adjTest, heatTime_zero, dualDil_zero]

/-- The adjoint identity: `⟨S₀(u)F, φ⟩ = ⟨F, S₀(u)^*φ⟩` for every `F ∈ L²`. -/
theorem inner_freeL2_toL2 (h u : ℝ) (F : L2Space) {φ : Space → Space} (hφ : IsVectorTest φ) :
    inner ℝ (freeL2 h u F) (toL2 φ) = inner ℝ F (adjTest h φ u) := by
  rw [← dil_heatOperator, dil_inner_toL2 u _ (isVectorTest_memLp hφ)]
  change Real.exp (-u) * inner ℝ (Heat.heatOperator (heatTime h u) F) (testDilation φ (-u)) = _
  rw [Heat.heatOperator_inner, adjTest, dualDil, map_smul, real_inner_smul_right]

/-! ## The generator on tests -/

/-- `w'(0) = -φ - ½ y·∇φ` in `L²` (two-sided derivative). -/
theorem hasDerivAt_dualDil {φ : Space → Space} (hφ : IsVectorTest φ) :
    HasDerivAt (dualDil φ) (-(toL2 φ) - (1 / 2 : ℝ) • toL2 (radialDeriv φ)) 0 := by
  have h0 : HasDerivAt (testDilation φ) ((1 / 2 : ℝ) • toL2 (radialDeriv φ)) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact hasDerivAt_testDilation_zero hφ
  have h1 := h0.scomp (0 : ℝ) (hasDerivAt_neg' (0 : ℝ))
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-0) * (-1)) (0 : ℝ) :=
    (hasDerivAt_neg' (0 : ℝ)).exp
  have h3 := h2.smul h1
  have h4 : HasDerivAt (dualDil φ) (Real.exp (-0) • (-1 : ℝ) • (1 / 2 : ℝ) • toL2 (radialDeriv φ) +
      (Real.exp (-0) * -1) • testDilation φ (-0)) 0 :=
    h3.congr_of_eventuallyEq (Eventually.of_forall fun y => rfl)
  refine h4.congr_deriv ?_
  rw [neg_zero, Real.exp_zero, testDilation_zero]
  module

/-- The `L²` heat generator on a test: `t⁻¹(e^{tΔ}φ - φ) → Δφ` as `t → 0⁺`. -/
theorem tendsto_heat_slope {φ : Space → Space} (hφ : IsVectorTest φ) :
    Tendsto (fun t : ℝ => t⁻¹ • (Heat.heatOperator t (toL2 φ) - toL2 φ)) (𝓝[>] 0)
      (𝓝 (toL2 (B0418.vecLaplacian φ))) := by
  have hm0 := isVectorTest_memLp hφ
  have hmL : MemLp (B0418.vecLaplacian φ) 2 volume :=
    (B0418.continuous_vecLaplacian hφ.smooth).memLp_of_hasCompactSupport
      (B0418.hasCompactSupport_vecLaplacian hφ.compact)
  have hlim := B0418.tendsto_heat_generator (p := 2) (by norm_num) ENNReal.ofNat_ne_top
    hφ.smooth hφ.compact
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ t : ℝ, ‖t⁻¹ • (Heat.heatOperator t (toL2 φ) - toL2 φ) -
      toL2 (B0418.vecLaplacian φ)‖ =
      (eLpNorm (fun x => t⁻¹ • (Heat.flow φ t x - φ x) - B0418.vecLaplacian φ x) 2
        volume).toReal := by
    intro t
    have hmf := Heat.flow_memLp hm0 t
    have hm : MemLp (fun x => t⁻¹ • (Heat.flow φ t x - φ x) - B0418.vecLaplacian φ x) 2
        volume :=
      ((hmf.sub hm0).const_smul t⁻¹).sub hmL
    have he : t⁻¹ • (Heat.heatOperator t (toL2 φ) - toL2 φ) - toL2 (B0418.vecLaplacian φ) =
        toL2 (fun x => t⁻¹ • (Heat.flow φ t x - φ x) - B0418.vecLaplacian φ x) := by
      rw [← Heat.toL2_flow hm0]
      symm
      apply toL2_of_ae_eq_coeFn
      filter_upwards [Lp.coeFn_sub (t⁻¹ • (toL2 (Heat.flow φ t) - toL2 φ))
          (toL2 (B0418.vecLaplacian φ)),
        Lp.coeFn_smul t⁻¹ (toL2 (Heat.flow φ t) - toL2 φ),
        Lp.coeFn_sub (toL2 (Heat.flow φ t)) (toL2 φ),
        coeFn_toL2 hmf, coeFn_toL2 hm0, coeFn_toL2 hmL] with x e1 e2 e3 e4 e5 e6
      rw [e1, Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, e4, e5, e6]
    rw [he, toL2_of_memLp hm, Lp.norm_toLp]
  simp_rw [heq]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa [Function.comp_def] using this

/-- `t(u) = h(e^u - 1) → 0⁺` as `u → 0⁺`. -/
theorem tendsto_heatTime {h : ℝ} (hh : 0 < h) :
    Tendsto (heatTime h) (𝓝[>] 0) (𝓝[>] 0) := by
  have htc : Continuous (heatTime h) := by
    unfold heatTime
    fun_prop
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · have := (htc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [heatTime_zero] at this
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact heatTime_pos hh hu

/-- **The adjoint generator on tests**: `u⁻¹(S₀(u)^*φ - φ) → hΔφ - φ - ½y·∇φ` in `L²` as
`u → 0⁺` (line 293; the adjoint form of B0418's generator statement). -/
theorem tendsto_adjTest_slope {h : ℝ} (hh : 0 < h) {φ : Space → Space} (hφ : IsVectorTest φ) :
    Tendsto (fun u : ℝ => u⁻¹ • (adjTest h φ u - toL2 φ)) (𝓝[>] 0) (𝓝 (adjGen h φ)) := by
  have hq : Tendsto (fun u : ℝ => u⁻¹ • (dualDil φ u - toL2 φ)) (𝓝[>] 0)
      (𝓝 (-(toL2 φ) - (1 / 2 : ℝ) • toL2 (radialDeriv φ))) := by
    have := (hasDerivAt_iff_tendsto_slope_zero.mp (hasDerivAt_dualDil hφ)).mono_left
      (nhdsWithin_mono _ (fun x (hx : x ∈ Ioi (0 : ℝ)) =>
        Set.mem_compl_singleton_iff.mpr (ne_of_gt hx)))
    simp only [zero_add, dualDil_zero] at this
    exact this
  have ht := tendsto_heatTime hh
  have ht0 : Tendsto (heatTime h) (𝓝[>] 0) (𝓝 0) := (tendsto_nhdsWithin_iff.mp ht).1
  -- the dilation part
  have hA : Tendsto (fun u : ℝ => Heat.heatOperator (heatTime h u)
      (u⁻¹ • (dualDil φ u - toL2 φ))) (𝓝[>] 0)
      (𝓝 (-(toL2 φ) - (1 / 2 : ℝ) • toL2 (radialDeriv φ))) := by
    set w' : L2Space := -(toL2 φ) - (1 / 2 : ℝ) • toL2 (radialDeriv φ) with hw'
    have h1 : Tendsto (fun u : ℝ => Heat.heatOperator (heatTime h u)
        (u⁻¹ • (dualDil φ u - toL2 φ) - w')) (𝓝[>] 0) (𝓝 0) := by
      apply squeeze_zero_norm (fun u => Heat.heatOperator_apply_norm_le _ _)
      have := (hq.sub_const w').norm
      rw [sub_self, norm_zero] at this
      exact this
    have h2 : Tendsto (fun u : ℝ => Heat.heatOperator (heatTime h u) w') (𝓝[>] 0) (𝓝 w') := by
      have := ((Heat.heatOperator_strongly_continuous w').tendsto 0).comp ht0
      rw [Heat.heatOperator_zero, ContinuousLinearMap.id_apply] at this
      exact this
    have := h1.add h2
    simp only [zero_add] at this
    refine this.congr (fun u => ?_)
    rw [map_sub, sub_add_cancel]
  -- the heat part
  have hB : Tendsto (fun u : ℝ => u⁻¹ • (Heat.heatOperator (heatTime h u) (toL2 φ) - toL2 φ))
      (𝓝[>] 0) (𝓝 (h • toL2 (B0418.vecLaplacian φ))) := by
    have hs : Tendsto (fun u : ℝ => h * (u⁻¹ * (Real.exp u - 1))) (𝓝[>] 0) (𝓝 (h * 1)) :=
      B0418.tendsto_exp_slope.const_mul h
    rw [mul_one] at hs
    have hv := (tendsto_heat_slope hφ).comp ht
    have := hs.smul hv
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have hne : Real.exp u - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)).ne'
    have hh0 : h ≠ 0 := hh.ne'
    simp only [Function.comp_apply, smul_smul]
    congr 1
    rw [heatTime]
    field_simp
  have := hA.add hB
  rw [adjGen, add_comm (h • _)]
  refine this.congr (fun u => ?_)
  rw [adjTest, map_smul, ← smul_add, map_sub, sub_add_sub_cancel]

/-- `S₀(u)^*φ → φ` in `L²` as `u → 0⁺`. -/
theorem tendsto_adjTest_zero {h : ℝ} (hh : 0 < h) {φ : Space → Space} (hφ : IsVectorTest φ) :
    Tendsto (adjTest h φ) (𝓝[>] 0) (𝓝 (toL2 φ)) := by
  have h1 := tendsto_adjTest_slope hh hφ
  have h2 : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h3 := h2.smul h1
  rw [zero_smul] at h3
  have h4 := (tendsto_const_nhds (x := toL2 φ)).add h3
  rw [add_zero] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hu), one_smul, add_sub_cancel]

/-! ## The free evolution operators of L2 on `L²` classes -/

/-- `S₀(u)` on `X` is `L02.freeL2` on the `L²` class, for `u ≥ 0`. -/
theorem Xclass_S0 {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S) {u : ℝ} (hu : 0 ≤ u)
    (f : X) : Xclass (S.S0 u f) = freeL2 h u (Xclass f) := by
  apply Lp.ext
  exact (hS.rep u hu f).trans (coeFn_freeL2 h u (Xclass f)).symm

/-- `S₀(u) : L²_div → X` is `L02.freeL2` on the `L²` class, for `u > 0`. -/
theorem Xclass_S0L {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S) {u : ℝ} (hu : 0 < u)
    (F : L2div) : Xclass (S.S0L u F) = freeL2 h u (Lclass F) := by
  apply Lp.ext
  exact (hS.repL u hu F).trans (coeFn_freeL2 h u (Lclass F)).symm

/-- `⟨S₀(u)f, φ⟩ = ⟨f, S₀(u)^*φ⟩` on `X`, `u ≥ 0`. -/
theorem inner_S0 {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S) {u : ℝ} (hu : 0 ≤ u)
    (f : X) {φ : Space → Space} (hφ : IsVectorTest φ) :
    inner ℝ (Xclass (S.S0 u f)) (toL2 φ) = inner ℝ (Xclass f) (adjTest h φ u) := by
  rw [Xclass_S0 hS hu, inner_freeL2_toL2 h u _ hφ]

/-- `⟨S₀(u)F, φ⟩ = ⟨F, S₀(u)^*φ⟩` on `L²_div`, `u > 0`. -/
theorem inner_S0L {h : ℝ} {S : FreeEvolution} (hS : IsFreeEvolution h S) {u : ℝ} (hu : 0 < u)
    (F : L2div) {φ : Space → Space} (hφ : IsVectorTest φ) :
    inner ℝ (Xclass (S.S0L u F)) (toL2 φ) = inner ℝ (Lclass F) (adjTest h φ u) := by
  rw [Xclass_S0L hS hu, inner_freeL2_toL2 h u _ hφ]

end UnforcedLeray.Blueprint.EvolWeak
