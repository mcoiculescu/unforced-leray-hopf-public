import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.ActYDiff.Cut
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymMu
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps

/-!
# `PartIII-b:C/rep/8/1/1/2/3/1` (`actYDiff`): the actual terms `YA`, `YB` are differentiable

Source `the November 2 reference manuscript` lines 4178-4186, 5400-5406, 5438-5448.

The old thin source has a separated representative `S` with the same responses
(`thinSepBridge`, as in `srThin_core`); so `W_μ = sepWre S`, `X₀ = sepX0 S`, `YA = 𝒞_y Re W_μ`
(`cutW_diffAt`: `Re W_μ` is `C²`, divergence free, axisymmetric, decaying, hence its outward
primitive is differentiable) and `YB = sepComm S` (`sepComm_diffAt`: the leaves of
`TransCommPoint` identify it with the explicit commutator `tcComm`, a combination of `X₀`, `∇X₀`,
`Ψ_{X₀}` with smooth coefficients, and `X₀`, `Ψ_{X₀}` are `C²`).  Phase differentiation never
enters: every phase works.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The separated representative of the old thin source (as in `srThin_core`). -/
theorem thinSepData (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) (T : LStr Pl K L) :
    ∃ S : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) S ∧
      SepMoment (2 * L.ε * cOf L.ν) S ∧ IsAxiSource S ∧
      ∀ (μ' : ℂ) (y : Space) (τ : ℝ),
        IIIa.sepW L.ν μ' (oldPhys L.ε⁻¹ (cOf L.ν) (thinG Pl K L T)) y τ =
          IIIa.sepW L.ν μ' S y τ := by
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hρ : 0 < L.ρb Pl K := by
    show 0 < UnforcedLeray.Short.IIb.rhoB (L.params Pl) K.m0 K.C0 K.k0
    unfold UnforcedLeray.Short.IIb.rhoB
    have h1 : 0 < ((L.params Pl).ν ^ K.k0)⁻¹ := inv_pos.2 (pow_pos (L.params Pl).ν_pos _)
    have h2 : 0 < (L.params Pl).ε ^ (3 / 11 : ℝ) := Real.rpow_pos_of_pos (L.params Pl).ε_pos _
    have h3 : 0 < Real.exp (K.m0 / (L.params Pl).ν) := Real.exp_pos _
    exact mul_pos (mul_pos (mul_pos hC0 h1) h3) h2
  have happ := chiOStrApply (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.χo K.hχo (thinPart T)
  have a1 := happ.1
  have a2 := happ.2
  have hgdef : strSum (oldThin Pl K L T) = fun p =>
      ((oldThin Pl K L T).fst : Chart → Ten3) p + ((oldThin Pl K L T).snd : Chart → Ten3) p := rfl
  have hgm : Measurable (strSum (oldThin Pl K L T)) := by
    rw [hgdef]
    exact (l9_lp_meas _).add (l9_lp_meas _)
  have hchart : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)),
      (L.ν * p.1 ≤ 6 / 5 → strSum (oldThin Pl K L T) p = 0) := by
    rw [NearInst.ae_gainZ1Measure, NearInst.ae_z1Measure] at a1
    rw [NearInst.ae_gainHTMeasure, NearInst.ae_htRhoMeasure hρ] at a2
    filter_upwards [a1, a2] with p e1 e2
    intro hp
    have h0 : cutFun K.χo L.ν p = 0 := K.hχo.zero _ hp
    rw [hgdef]
    simp only [e1, e2, h0, zero_smul, add_zero]
  have hM : ∫⁻ p, ‖strSum (oldThin Pl K L T) p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ :=
    strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρ hmZ hν (oldThin Pl K L T)
  obtain ⟨S, hT1, hT2, hAx, hresp⟩ := thinSepBridge (cOf L.ν) L.ν L.ε hc hν hε _ hgm hchart hM
  have hg : IsRep Pl K L (oldThin Pl K L T) ((oldThin Pl K L T).fst : Chart → Ten3)
      ((oldThin Pl K L T).snd : Chart → Ten3) := ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  have hae := wo_rep_ae hρ K.hχo (thinPart T) hg.1 hg.2
  have hnull := ae_iff.1 hae
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  refine ⟨S, hT1, hT2, hAx, ?_⟩
  intro μ' y τ
  have := WardX0Congr.sepW_congr L.ν μ' hR hc
    (((oldThin Pl K L T).fst : Chart → Ten3) + ((oldThin Pl K L T).snd : Chart → Ten3)) _ N hNm hN0
    hsub τ y
  exact this.trans (hresp μ' y τ)

/-- Pointwise differentiability of the four terms for one level. -/
theorem actYDiffAt_of_data (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    {σ₁ σ₂ : ℝ} (hσ : -(1 / 4) < σ₁) (hμ : μ ∈ Icc σ₁ σ₂) (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (hχ : IsStreamCutoff K.χy) (hC0 : 0 < K.C0) (hmZ : 0 ≤ K.mZ) :
    ActYDiffAt Pl K L μ := by
  intro _ T
  refine Filter.Eventually.of_forall (fun τ y hy => ?_)
  obtain ⟨S, hS1, hS2, hS3, hresp⟩ := thinSepData Pl K L hC0 hmZ T
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hR : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hR1 : 1 ≤ L.ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hP : 0 < 2 * L.ε * cOf L.ν := mul_pos (mul_pos two_pos hε) (cOf_pos hν)
  have hμ' : -(1 / 4) < μ := lt_of_lt_of_le hσ hμ.1
  have hW : thinWardW Pl K L μ T = sepWre L.ν μ S := by
    funext τ' y'
    simp only [thinWardW, sepWre, hresp]
  have hX : zAct0 Pl K L μ T = sepX0 L.ν μ S := by
    funext τ' y'
    simp only [zAct0, wardX0, sepX0, hresp]
  refine ⟨?_, ?_⟩
  · unfold actYA
    rw [hW]
    exact cutW_diffAt hχ hν hR hμ' hP hS1 hS2 hS3 τ hy
  · have h := sepComm_diffAt (χy := K.χy) hχ hσ hν hν1 hR1 hP hμ hS1 hS2 hS3 τ hy
    have e : actYB Pl K L μ T τ = sepComm L.ν μ L.ε⁻¹ K.χy S τ := by
      funext y'
      simp only [actYB, sepComm, sepWX, hX]
    rw [e]
    exact h

/-- **`PartIII-b:C/rep/8/1/1/2/3/1`**: the actual terms `YA`, `YB` are differentiable off the
axis (source 4178-4186, 5400-5406, 5438-5448). -/
theorem actYDiff (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3.ActYDiff D := by
  have hσ : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hev1, hev2] with n h1 h2 z hz
  exact actYDiffAt_of_data D.Pl D.K (D.level n) (D.mu n z) hσ (h1 z hz) h2.1 h2.2 hst.chiY
    hst.C0_pos (by linarith [hst.mZ_gt])

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
