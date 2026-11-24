import UnforcedLeray.Loc.L14Realization.Fields
import UnforcedLeray.Loc.L14Realization.WeakForm
import UnforcedLeray.Loc.L14Realization.Trilinear
import UnforcedLeray.Analysis.NavierStokesEnergy.Primitive
import UnforcedLeray.Analysis.Pressure.Spacetime
import UnforcedLeray.Analysis.ViscosityTransport.Solution

/-!
# Step L14 `RealizationStep`: realization of a strong remainder as a Theorem A solution

`paper/main.tex` lines 532–561 (`loc:eq:total-field`, `loc:eq:regularity`, `loc:eq:energy`,
the pressure `p = Σ R_iR_k(u_iu_k) ∈ L^{5/3}` and `eq:initial-weak-form`); blueprint units
B1029, B1030, B1031, B1032; the step is defined in


**Main result.** `realizationStep : RealizationStep`, with no hypothesis: for `h, T > 0`, a
compact solenoidal `𝒪`-invariant datum `u₀` and a strong `H²` remainder `ρ`
(`IsPhysicalStrongRemainder h T u₀ ρ N C`), there are `u, p, G, H` with `u(t) = e^{htΔ}u₀ + ρ(t)`
a.e. for `t ∈ (0,T]` and `u(0) = u₀` a.e., `IsTheoremASolutionViscosity h T u₀ u p G H`, and
`u(t)` `𝒪`-invariant for `t ∈ [0,T]`.

**Construction.**
* `u` and `G` are jointly measurable representatives (`Infra/JointMeasurableRep`) of the total
  field `physicalVelocity h u₀ ρ` and of the first derivatives of the `H²` path
  `totalH2 h u₀ ρ t = e^{htΔ}u₀ + ρ(t)`; `H` is the second derivatives of that path.
* The pressure is the compiled Newton pressure `PressureAnalysis.pressureFromVelocity u G`
  (decision D6 of the scoping plan), in `L^{5/3}` of the slab by the compiled
  `spacetime_pressure_memLp` (in place of the Riesz transforms of lines 555–557; the
  `L^{10/3}` interpolation of line 553 is not needed for it).

**Proof.**
* Regularity (lines 539–546): continuity of the `L²` path on `[0,T]` from the heat flow and
  the rate `‖ρ(t)‖ ≤ C t^{1/4}` (`continuousOn_toL2_physicalVelocity`), and of the `H²` path
  on `(0,T]` (`continuousOn_totalH2`); the strong trace follows from the first.
* Energy (lines 545–550): the `L²` derivative `∂ₜu = hΔu + N` (`hasDerivAt_totalH2_value`),
  `⟨Δu, u⟩ = -‖∇u‖²` and the trilinear cancellation `⟨N, u⟩ = 0`
  (`inner_isMinusLerayDiv_eq_zero`), then the compiled `NavierStokesEnergy.energy_equality`
  (which also gives the finite dissipation).
* Weak form (lines 559–561): `⟨N, φ⟩ = ∫ u·(Dφ u) + ∫ p div φ` from the Newton pressure identity
  `∇p = -(I - 𝔓) div(u ⊗ u)` (`velocityPressure_div_identity`), and
  `solvesNavierStokesViscosity_of_strong`.
* Symmetry: the heat flow commutes with `𝒪` (`rotateField_flow`).

No named hypothesis remains: the pressure identity of `Lib/CZL2` (INF01 T5) is used in its
`(u·∇)u` form and converted to the divergence form in `L14Realization/PressureDiv.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Blueprint

open SobolevGraph PressureAnalysis L14

namespace L14

/-- `⟨a, L a⟩ = Σⱼ ⟨aⱼ a, L eⱼ⟩`: the convection term in tensor form. -/
theorem inner_apply_self_eq_sum (a : Space) (L : Space →L[ℝ] Space) :
    inner ℝ a (L a) = ∑ j : Fin 3, inner ℝ ((a j) • a) (L (coordinateVector j)) := by
  have ha : a = ∑ j : Fin 3, a j • coordinateVector j := RieszLp.eq_sum_coordinateVector a
  conv_lhs => rw [ha, map_sum]
  rw [← ha, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]

/-- `∫ u·(Dψ u) = Σⱼ ⟨uⱼu, ∂ⱼψ⟩`. -/
theorem integral_convection_eq_sum {w : SpatialField} (hcol : ∀ j, MemLp (tensorColumns w w j) 2 volume)
    {ψ : Space → Space} (hψ : IsVectorTest ψ) :
    ∫ x, inner ℝ (w x) (fderiv ℝ ψ x (w x)) =
      ∑ j : Fin 3, inner ℝ (toL2 (tensorColumns w w j)) (toL2 (testPartial ψ j)) := by
  have hint : ∀ j, Integrable (fun x => inner ℝ (tensorColumns w w j x) (testPartial ψ j x)) :=
    fun j => integrable_inner_of_memLp (hcol j) (L10.testPartial_memLp hψ j 2)
  rw [Finset.sum_congr rfl fun j _ => inner_toL2_eq_integral (hcol j) (L10.testPartial_memLp hψ j 2),
    ← integral_finsetSum _ fun j _ => hint j]
  exact integral_congr_ae (Eventually.of_forall fun x => inner_apply_self_eq_sum (w x) _)

end L14

/-- **Step L14** (`RealizationStep`, `Blueprint/Localization/Realization.lean` line 105;
`paper/main.tex` lines 532–561; units B1029–B1032). -/
theorem realizationStep : RealizationStep := by
  intro h T u₀ ρ N C hh hT hdat hsym hρ
  have hu₀ := hdat.memLp
  set v : Velocity := physicalVelocity h u₀ ρ with hvdef
  set W : ℝ → H2 := totalH2 h u₀ ρ with hWdef
  have hv2 : ∀ t, MemLp (v t) 2 volume := memLp_physicalVelocity hu₀
  have hvcont : ContinuousOn (fun t => toL2 (v t)) (Icc 0 T) :=
    continuousOn_toL2_physicalVelocity hh hu₀ hρ.continuous hρ.l2_rate
  have hWcont : ContinuousOn W (Ioc 0 T) := continuousOn_totalH2 hh hρ.continuous
  -- jointly measurable representatives
  obtain ⟨u, hu_ae, -, hu_meas⟩ :=
    Infra.JointMeasurableRep.exists_jointRep_velocity_slab (fun t _ => hv2 t) hvcont
  have hG0cont : ∀ δ, 0 < δ → δ < T → ∀ i,
      ContinuousOn (fun t => toL2 (gradField0 h u₀ ρ t i)) (Icc δ T) := by
    intro δ hδ _ i
    have hc : ContinuousOn (fun t => (W t).first i) (Icc δ T) :=
      (H2.firstCLM i).continuous.comp_continuousOn
        (hWcont.mono fun t ht => ⟨hδ.trans_le ht.1, ht.2⟩)
    refine hc.congr fun t _ => ?_
    simp only [gradField0, ViscosityTransport.toL2_coe, hWdef]
  obtain ⟨G, hG_ae, -, hG_meas⟩ := Infra.JointMeasurableRep.exists_jointRep_gradient_slab
    (G := gradField0 h u₀ ρ) (fun t _ i => Lp.memLp _) hG0cont
  set H : SecondDerivatives := secondField0 h u₀ ρ with hHdef
  set p : Pressure := pressureFromVelocity u G with hpdef
  -- basic facts
  have hu2 : ∀ t ∈ Icc (0 : ℝ) T, MemLp (u t) 2 volume := fun t ht =>
    (hv2 t).ae_eq (hu_ae t ht).symm
  have hU : ∀ t ∈ Icc (0 : ℝ) T, toL2 (u t) = toL2 (v t) := fun t ht =>
    Infra.JointMeasurableRep.toL2_congr_ae (hu_ae t ht)
  have hUcont : ContinuousOn (fun t => toL2 (u t)) (Icc 0 T) :=
    hvcont.congr fun t ht => hU t ht
  have hIoc : ∀ t ∈ Ioc (0 : ℝ) T, t ∈ Icc (0 : ℝ) T := fun t ht => ⟨ht.1.le, ht.2⟩
  have hUW : ∀ t ∈ Ioc (0 : ℝ) T, toL2 (u t) = (W t).value := fun t ht =>
    (hU t (hIoc t ht)).trans (toL2_physicalVelocity hh hu₀ ht.1)
  have huW : ∀ t ∈ Ioc (0 : ℝ) T, u t =ᵐ[volume] ((W t).value : SpatialField) := fun t ht =>
    (hu_ae t (hIoc t ht)).trans (physicalVelocity_ae hh hu₀ ht.1)
  have hGW : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, G t i =ᵐ[volume] ((W t).first i : SpatialField) :=
    fun t ht i => hG_ae t ht i
  have hGmem : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume := fun t ht i =>
    (Lp.memLp _).ae_eq (hGW t ht i).symm
  have hweak : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i) :=
    fun t ht i => ((W t).hasWeakFirst i).congr (huW t ht).symm (hGW t ht i).symm
  have hweak2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i j, HasWeakSpatialDerivative j (G t i) (H t i j) :=
    fun t ht i j => ((W t).hasWeakSecond i j).congr (hGW t ht i).symm EventuallyEq.rfl
  have hsol : ∀ t ∈ Icc (0 : ℝ) T, IsSolenoidal (u t) := fun t ht =>
    Leray.solenoidal_congr_ae (isSolenoidal_physicalVelocity hh hdat hρ.solenoidal ht)
      (hu_ae t ht).symm
  have hdissW : ∀ t ∈ Ioc (0 : ℝ) T, dissipation G t = ∑ i : Fin 3, ‖(W t).first i‖ ^ 2 := by
    intro t ht
    unfold dissipation
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Infra.JointMeasurableRep.l2Norm_congr_ae (hGW t ht i), L10.l2Norm_coeFn]
  have hu0 : u 0 =ᵐ[volume] u₀ := by
    have := hu_ae 0 ⟨le_rfl, hT.le⟩
    rwa [hvdef, physicalVelocity_zero] at this
  -- the nonlinearity at the representative
  have hNu : ∀ t ∈ Ioc (0 : ℝ) T, IsMinusLerayDiv (tensorColumns (u t) (u t)) (N t) := by
    intro t ht
    refine L10.IsMinusLerayDiv.congr (hρ.nonlinear_weak t ht) fun j => ?_
    filter_upwards [hu_ae t (hIoc t ht)] with x hx
    simp only [tensorColumns, hx, hvdef]
  have hF : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, MemLp (velocityForcing (u t) (G t) i) 2 volume :=
    fun t ht i => velocityForcing_memLp_two_of_H2 (W t) (huW t ht) (hGW t ht) i
  -- the strong derivative and the energy derivative
  have hIoo : ∀ t ∈ Ioo (0 : ℝ) T, t ∈ Ioc (0 : ℝ) T := fun t ht => ⟨ht.1, ht.2.le⟩
  have hderivU : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => toL2 (u s))
      (h • H2.laplace (W t) + N t) t := by
    intro t ht
    refine (hasDerivAt_totalH2_value hh hρ ht).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hUW s (hIoo s hs)
  have htri : ∀ t ∈ Ioo (0 : ℝ) T, inner ℝ (N t) (W t).value = 0 := by
    intro t ht
    have h0 := inner_isMinusLerayDiv_eq_zero (hu2 t (hIoc t (hIoo t ht))) (hGmem t (hIoo t ht))
      (hweak t (hIoo t ht)) (hsol t (hIoc t (hIoo t ht))) (hF t (hIoo t ht))
      (hNu t (hIoo t ht)).1 (hNu t (hIoo t ht))
    rwa [hUW t (hIoo t ht)] at h0
  have henergy : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt (fun s => ‖toL2 (u s)‖ ^ 2)
      (-2 * (h * dissipation G t)) t := by
    intro t ht
    have hd := (hderivU t ht).norm_sq
    have hi : inner ℝ (toL2 (u t)) (h • H2.laplace (W t) + N t) = -(h * dissipation G t) := by
      rw [hUW t (hIoo t ht), inner_add_right, real_inner_smul_right, real_inner_comm (N t),
        htri t ht, real_inner_comm, H2.laplace_inner_self, hdissW t (hIoo t ht)]
      ring
    rw [hi] at hd
    convert hd using 1
    ring
  have hnonneg : ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ h * dissipation G t := fun t _ =>
    mul_nonneg hh.le (dissipation_nonneg G t)
  have hdiss : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T) := by
    have h1 := NavierStokesEnergy.dissipation_integrableOn_Ioc hUcont henergy hnonneg
      (a := 0) (b := T) le_rfl hT.le le_rfl
    have h2 := h1.const_mul h⁻¹
    refine (IntegrableOn.congr_fun h2 (fun t _ => ?_) measurableSet_Ioc).mono_set
      Ioo_subset_Ioc_self
    show h⁻¹ * (h * dissipation G t) = dissipation G t
    rw [← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  -- a uniform `L²` bound and the pressure
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hUcont
  have hMu : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ max M 0 := fun t ht => by
    rw [← norm_toL2 (hu2 t ⟨ht.1.le, ht.2.le⟩)]
    exact (hM t ⟨ht.1.le, ht.2.le⟩).trans (le_max_left _ _)
  have hpmem : MemLp (fun z : SpaceTime => p z.1 z.2) (5 / 3 : ℝ≥0∞)
      (volume.restrict (slab T)) :=
    spacetime_pressure_memLp hu_meas hG_meas (fun t ht => hu2 t ⟨ht.1.le, ht.2.le⟩)
      (fun t ht => hGmem t (hIoo t ht)) (fun t ht => hweak t (hIoo t ht)) (le_max_right _ _)
      hMu hdiss
  have hpt : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (p t) (5 / 3 : ℝ≥0∞) volume := fun t ht =>
    velocityPressure_memLp (hu2 t ⟨ht.1.le, ht.2.le⟩) (hGmem t (hIoo t ht)) (hweak t (hIoo t ht))
  -- the pairing identity
  have hpair : ∀ t ∈ Ioo (0 : ℝ) T, ∀ ψ : Space → Space, IsVectorTest ψ →
      inner ℝ (h • H2.laplace (W t) + N t) (toL2 ψ) =
        h * (∫ x, inner ℝ (u t x) (∑ i : Fin 3, testPartial (testPartial ψ i) i x)) +
        (∫ x, inner ℝ (u t x) (fderiv ℝ ψ x (u t x))) +
        ∫ x, p t x * ∑ i : Fin 3, testPartial ψ i x i := by
    intro t ht ψ hψ
    have htc := hIoo t ht
    have hut := hu2 t (hIoc t htc)
    have hcol := (hNu t htc).1
    -- the Laplacian
    have hΔ : inner ℝ (H2.laplace (W t)) (toL2 ψ) =
        ∫ x, inner ℝ (u t x) (∑ i : Fin 3, testPartial (testPartial ψ i) i x) := by
      have hm : MemLp (fun x => ∑ i : Fin 3, testPartial (testPartial ψ i) i x) 2 volume := by
        have := memLp_finsetSum' (Finset.univ : Finset (Fin 3)) (fun i _ =>
          L10.vectorTest_memLp (isVectorTest_testPartial (isVectorTest_testPartial hψ i) i) 2)
        convert this using 1
        funext x
        simp
      rw [inner_laplace_toL2 (W t) hψ, ← hUW t htc, inner_toL2_eq_integral hut hm]
    -- the nonlinearity
    have hN := (hNu t htc).2 ψ hψ
    unfold lerayDivPairing at hN
    rw [neg_neg] at hN
    have hsplit : ∀ j, inner ℝ (toL2 (tensorColumns (u t) (u t) j))
        (Leray.projection (toL2 (testPartial ψ j))) =
        inner ℝ (toL2 (tensorColumns (u t) (u t) j)) (toL2 (testPartial ψ j)) -
          inner ℝ (toL2 (tensorColumns (u t) (u t) j))
            (toL2 (testPartial ψ j) - Leray.projection (toL2 (testPartial ψ j))) := by
      intro j
      rw [inner_sub_right]
      ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib] at hN
    have hp := velocityPressure_div_identity hut (hGmem t htc) (hweak t htc)
      (hsol t (hIoc t htc)) (hF t htc) hcol hψ
    have hconv := integral_convection_eq_sum hcol hψ
    have hpt' : ∫ x, p t x * ∑ i : Fin 3, testPartial ψ i x i =
        ∫ x, velocityPressure (u t) (G t) x * ∑ i : Fin 3, testPartial ψ i x i := rfl
    rw [inner_add_left, real_inner_smul_left, hΔ, hN, hconv, hpt', hp]
    ring
  have hsolves : ViscosityTransport.SolvesNavierStokesViscosity h T u₀ u p :=
    solvesNavierStokesViscosity_of_strong hT hu_meas hu2 hUcont hu0 hpmem hpt hderivU hpair
  -- the energy equality
  have henergyEq : ∀ t₀ t₁, 0 ≤ t₀ → t₀ ≤ t₁ → t₁ ≤ T →
      (1 / 2 : ℝ) * l2Norm (u t₁) ^ 2 + h * (∫ t in Ioo t₀ t₁, dissipation G t) =
        (1 / 2 : ℝ) * l2Norm (u t₀) ^ 2 := by
    intro t₀ t₁ h0 h01 h1
    have he := NavierStokesEnergy.energy_equality hUcont henergy hnonneg h0 h01 h1
    rw [integral_const_mul, norm_toL2 (hu2 t₁ ⟨h0.trans h01, h1⟩),
      norm_toL2 (hu2 t₀ ⟨h0, h01.trans h1⟩)] at he
    exact he
  -- the initial trace
  have htrace : Tendsto (fun t => l2Norm (u t - u₀)) (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0) := by
    have hc := (hUcont 0 ⟨le_rfl, hT.le⟩).tendsto
    have hc0 : toL2 (u 0) = toL2 u₀ := Infra.JointMeasurableRep.toL2_congr_ae hu0
    rw [hc0] at hc
    have hd := (tendsto_iff_dist_tendsto_zero.mp hc)
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact dist_toL2 (hu2 t ht) hu₀
  have hH1 : IntegrableOn (fun t => l2Norm (u t) ^ 2 + dissipation G t) (Ioo (0 : ℝ) T) := by
    have h1 : IntegrableOn (fun t => ‖toL2 (u t)‖ ^ 2) (Icc (0 : ℝ) T) :=
      (hUcont.norm.pow 2).integrableOn_Icc
    have h2 : IntegrableOn (fun t => l2Norm (u t) ^ 2) (Ioo (0 : ℝ) T) :=
      IntegrableOn.congr_fun (h1.mono_set Ioo_subset_Icc_self) (fun t ht => by
        show ‖toL2 (u t)‖ ^ 2 = l2Norm (u t) ^ 2
        rw [norm_toL2 (hu2 t ⟨ht.1.le, ht.2.le⟩)]) measurableSet_Ioo
    exact h2.add hdiss
  refine ⟨u, p, G, H, hu_ae, ?_, fun t ht => ?_⟩
  · refine ⟨hu_meas, hG_meas, hu2, hsol, hUcont, hu0, htrace, hGmem,
      fun t _ i j => Lp.memLp _, hweak, hweak2, hH1, hdiss, ?_, ?_, hpmem, hsolves, henergyEq⟩
    · intro δ hδ _ i
      have hc : ContinuousOn (fun t => (W t).first i) (Icc δ T) :=
        (H2.firstCLM i).continuous.comp_continuousOn
          (hWcont.mono fun t ht => ⟨hδ.trans_le ht.1, ht.2⟩)
      refine hc.congr fun t ht => ?_
      exact Infra.JointMeasurableRep.toL2_congr_ae (hGW t ⟨hδ.trans_le ht.1, ht.2⟩ i) |>.trans
        (ViscosityTransport.toL2_coe _)
    · intro δ hδ _ i j
      have hc : ContinuousOn (fun t => (W t).second i j) (Icc δ T) :=
        (H2.secondCLM i j).continuous.comp_continuousOn
          (hWcont.mono fun t ht => ⟨hδ.trans_le ht.1, ht.2⟩)
      refine hc.congr fun t _ => ?_
      simp only [hHdef, secondField0, ViscosityTransport.toL2_coe, hWdef]
  · exact isAxisymmetricNoSwirl_congr (hu_ae t ht).symm
      (isAxisymmetricNoSwirl_physicalVelocity hh hsym hρ.symmetric ht)

end UnforcedLeray.Blueprint
