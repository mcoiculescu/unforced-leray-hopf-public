import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.ChartConj

/-!
# `PepsCCplx` (source 1669)

`PartIIa.PepsC` (the complex orthogonal projection onto `solenoidalHC`) acts on a complexified real
field as the complexified real projection `B0226.Peps` (`= (solenoidalH ε c).starProjection`).

Route (`eq_starProjection_of_mem_orthogonal`): with `v := cplxH (Peps g)` and `u := cplxH g`,
* `v ∈ solenoidalHC`: each complex generator `cgrad Φ` has inner product with `v` equal to the
  complexification of the real pairing `∫ (b_r D_εΦ + b_z ∂_ηΦ) = 0` (`mem_solenoidalH_iff`);
* `u - v = cplxH (g - Peps g) ∈ (solenoidalHC)ᗮ`: `g - Peps g ∈ solenoidalHᗮ = closure(span_ℝ ∇Φ)`;
  `cplxH` sends each `profileGradH Φ` to the complex generator `cgrad Φ`, which lies in
  `(solenoidalHC)ᗮ`; the preimage of the closed subspace `(solenoidalHC)ᗮ` under `cplxH` is closed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- The complexified gradient is the complex image of the real profile gradient. -/
theorem pcc_cgrad_eq_merC (ε : ℝ) (Φ : UnforcedLeray.B0220.Profile → ℝ) :
    UnforcedLeray.Short.PartIIa.cgrad ε Φ =
      fun p => merC (UnforcedLeray.B0226.profileGrad ε Φ p) := by
  funext p
  ext i
  fin_cases i <;> simp [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.profileGrad, merC,
    UnforcedLeray.B0226.Deps]

theorem pcc_merC_lip : LipschitzWith 1 merC := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  simp only [merC, NNReal.coe_one, one_mul, Complex.dist_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
  exact le_rfl

theorem pcc_memLp_cgrad {c : ℝ} (ε : ℝ) (Φ : UnforcedLeray.B0226.ProfileTest c) :
    MemLp (UnforcedLeray.Short.PartIIa.cgrad ε Φ.1) 2
      (UnforcedLeray.B0220.measureH c) := by
  have h := UnforcedLeray.B0226.memLp_profileGrad ε Φ.2
  rw [pcc_cgrad_eq_merC]
  have h0 : merC 0 = 0 := by ext i; simp [merC]
  exact LipschitzWith.comp_memLp (g := merC) pcc_merC_lip h0 h

/-- The real profile gradient, complexified, is the complex generator `cgrad`. -/
theorem pcc_cplxH_profileGradH {c : ℝ} (ε : ℝ) (Φ : UnforcedLeray.B0226.ProfileTest c) :
    cplxH c (UnforcedLeray.B0226.profileGradH ε c Φ) =
      (pcc_memLp_cgrad ε Φ).toLp (UnforcedLeray.Short.PartIIa.cgrad ε Φ.1) := by
  apply Lp.ext
  filter_upwards [cplxH_ae c (UnforcedLeray.B0226.profileGradH ε c Φ),
    UnforcedLeray.B0226.coeFn_profileGradH ε c Φ,
    MemLp.coeFn_toLp (pcc_memLp_cgrad ε Φ)] with p h1 h2 h3
  rw [h1, h2, h3, pcc_cgrad_eq_merC]

/-- `cplxH (Peps g)` lies in the complex solenoidal subspace. -/
theorem pcc_cplxH_peps_mem {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid) :
    cplxH c (UnforcedLeray.B0226.Peps hε hc g) ∈
      UnforcedLeray.Short.PartIIa.solenoidalHC ε c := by
  have hw : UnforcedLeray.B0226.Peps hε hc g ∈ UnforcedLeray.B0226.solenoidalH ε c := by
    rw [UnforcedLeray.B0226.Peps_eq_starProjection hε hc]
    exact Submodule.starProjection_apply_mem _ _
  rw [UnforcedLeray.B0226.mem_solenoidalH_iff] at hw
  unfold UnforcedLeray.Short.PartIIa.solenoidalHC
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Φ, hm, rfl⟩ := hx
    rw [L2.inner_def]
    have hint : (∫ q, ⟪(hm.toLp (UnforcedLeray.Short.PartIIa.cgrad ε Φ.1)) q,
        (cplxH c (UnforcedLeray.B0226.Peps hε hc g)) q⟫_ℂ ∂UnforcedLeray.B0220.measureH c) =
        ∫ q, ((UnforcedLeray.B0226.Peps hε hc g q 0 * UnforcedLeray.B0226.Deps ε Φ.1 q +
          UnforcedLeray.B0226.Peps hε hc g q 1 * UnforcedLeray.Axi.dEta Φ.1 q : ℝ) : ℂ)
          ∂UnforcedLeray.B0220.measureH c := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hm, cplxH_ae c (UnforcedLeray.B0226.Peps hε hc g)]
        with q h1 h2
      rw [h1, h2]
      simp [PiLp.inner_apply, UnforcedLeray.Short.PartIIa.cgrad, merC, Fin.sum_univ_two]
    rw [hint, integral_complex_ofReal, hw Φ]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- `cplxH (g - Peps g)` lies in `(solenoidalHC)ᗮ`. -/
theorem pcc_cplxH_compl_mem {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid) :
    cplxH c (g - UnforcedLeray.B0226.Peps hε hc g) ∈
      (UnforcedLeray.Short.PartIIa.solenoidalHC ε c)ᗮ := by
  have hw' : g - UnforcedLeray.B0226.Peps hε hc g ∈ (UnforcedLeray.B0226.solenoidalH ε c)ᗮ := by
    rw [UnforcedLeray.B0226.Peps_eq_starProjection hε hc]
    exact Submodule.sub_starProjection_mem_orthogonal g
  unfold UnforcedLeray.B0226.solenoidalH at hw'
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hw'
  let M : Submodule ℝ (UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :=
    ((UnforcedLeray.Short.PartIIa.solenoidalHC ε c)ᗮ).restrictScalars ℝ
  let t : Submodule ℝ (UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid) :=
    Submodule.comap (cplxH c).toLinearMap M
  have hclosed : IsClosed (t : Set (UnforcedLeray.B0220.HSpace c UnforcedLeray.B0220.Merid)) :=
    (Submodule.isClosed_orthogonal _).preimage (cplxH c).continuous
  have hspan : Submodule.span ℝ (Set.range (UnforcedLeray.B0226.profileGradH ε c)) ≤ t := by
    rw [Submodule.span_le]
    rintro _ ⟨Φ, rfl⟩
    show cplxH c (UnforcedLeray.B0226.profileGradH ε c Φ) ∈ M
    rw [pcc_cplxH_profileGradH ε Φ]
    apply (Submodule.restrictScalars_mem _ _ _).2
    unfold UnforcedLeray.Short.PartIIa.solenoidalHC
    have hx : (pcc_memLp_cgrad ε Φ).toLp (UnforcedLeray.Short.PartIIa.cgrad ε Φ.1) ∈
        {g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC | ∃ Ψ :
          UnforcedLeray.B0226.ProfileTest c, ∃ _ : MemLp (UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1) 2
          (UnforcedLeray.B0220.measureH c), g = (‹MemLp (UnforcedLeray.Short.PartIIa.cgrad ε Ψ.1) 2
          (UnforcedLeray.B0220.measureH c)›).toLp _} :=
      ⟨Φ, pcc_memLp_cgrad ε Φ, rfl⟩
    exact Submodule.le_orthogonal_orthogonal _ (Submodule.subset_span hx)
  have h := Submodule.topologicalClosure_minimal _ hspan hclosed hw'
  exact (Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_comap.1 h)

/-- **`PepsCCplx`**: `PepsC` on complexified real fields is the complexified real projection. -/
theorem pepsCCplx : PepsCCplx := by
  intro ε c hε hc g
  unfold UnforcedLeray.Short.PartIIa.PepsC
  apply Submodule.eq_starProjection_of_mem_orthogonal (pcc_cplxH_peps_mem hε hc g)
  rw [← map_sub (cplxH c)]
  exact pcc_cplxH_compl_mem hε hc g

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
