import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.ZPrimRegular.Kernel

/-!
# `PartIII-b:C/rep/8/1/1/1/asm/4` (`zPrimRegular`): convergence and differentiability of the
outward primitive of the old-source fields

Source `the November 2 reference manuscript`
lines 4178-4186 ("The separated-kernel estimates prove convergence of this primitive and its
differentiated versions ... Their decay makes the boundary term at infinity vanish"), 5400-5406
(the old source lives at `(εr)² ≤ ν/1.2`, the receivers of the clear region at `(εr)² > ν/1.1`:
radial gap), 3604-3621 (`sep:kernel`, `sep:resolvent`), 4776-4791 (the zero-width Newton fields).

At a point `(r, 0, z)` of the clear region choose `r₀ ∈ (ε⁻¹√(ν/1.1), r)`.  Both fields are `C¹` on
the clear region (`ZRegular`), which contains the half-plane points `ρ ≥ r₀`; their values and
gradients are `O(ρ⁻³)` far out (`ZPrimKernel.sep_far`, `ZPrimKernel.newton_far`), hence
`RayDecayW` on `[r₀, ∞) × (z - 1, z + 1)` (`ZPrimKernel.rayDecayW_of`), and `PrimData` follows
(`RayPrimW.primData_of_decayW`: `ρ Z_z` and `ρ ∂_zZ_z` are `O(ρ⁻²)`, FTC in `r`, differentiation
under the integral in `z`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomXAsm

namespace ZPrimKernel

open RayFTCAux RayPrimAux RayPrimW ZRegAux

/-- `ZPrimRegularAt` at one regime with the standing hypotheses. -/
theorem zPrimRegularAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hLH : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy) (hmZ : 3 / 2 < K.mZ) (hγ : 0 < gRate Pl)
    (hC0 : 0 < K.C0) : ZPrimRegularAt Pl K L μ := by
  intro T τ Z hZ r z hr hrc
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc := hLH.c_pos
  have hρb := rho_b_pos' Pl K L hC0
  have hμ : -(1 / 4) < μ := by linarith [hLH.mu_pos]
  -- the inner radius `r₀ ∈ (ε⁻¹√(ν/1.1), r)`
  set a : ℝ := Real.sqrt (L.ν / (11 / 10)) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hεr : 0 < L.ε * r := mul_pos hε hr
  have har : a < L.ε * r := (Real.sqrt_lt' hεr).2 hrc
  set r₀ : ℝ := (L.ε⁻¹ * a + r) / 2 with hr₀
  have hεinv : L.ε⁻¹ * (L.ε * r) = r := by field_simp
  have hεa : L.ε⁻¹ * a < r := by
    calc L.ε⁻¹ * a < L.ε⁻¹ * (L.ε * r) := mul_lt_mul_of_pos_left har (inv_pos.2 hε)
      _ = r := hεinv
  have hr₀r : r₀ < r := by rw [hr₀]; linarith
  have hr₀pos : 0 < r₀ := by
    rw [hr₀]
    have : 0 ≤ L.ε⁻¹ * a := mul_nonneg (inv_pos.2 hε).le ha0
    linarith
  have har₀ : a < L.ε * r₀ := by
    have h1 : L.ε * (L.ε⁻¹ * a) = a := by field_simp
    have h2 : L.ε * (L.ε⁻¹ * a) < L.ε * r₀ := by
      apply mul_lt_mul_of_pos_left _ hε
      rw [hr₀]; linarith
    linarith
  have hclear : ∀ ρ : ℝ, r₀ ≤ ρ → L.ν / (11 / 10) < (L.ε * ρ) ^ 2 := by
    intro ρ hρ
    have hερ : L.ε * r₀ ≤ L.ε * ρ := mul_le_mul_of_nonneg_left hρ hε.le
    exact (Real.sqrt_lt' (by linarith)).1 (lt_of_lt_of_le har₀ hερ)
  have hmem : ∀ ρ : ℝ, r₀ ≤ ρ → ∀ z' : ℝ, hpt ρ z' ∈ clearSet L.ε L.ν := by
    intro ρ hρ z'
    have hρ0 : 0 < ρ := lt_of_lt_of_le hr₀pos hρ
    refine ⟨?_, ?_⟩
    · show 0 < ϱ (hpt ρ z')
      rw [ϱ_hpt hρ0]; exact hρ0
    · show L.ν / (11 / 10) < (L.ε * ϱ (hpt ρ z')) ^ 2
      rw [ϱ_hpt hρ0]; exact hclear ρ hρ
  have hUo : IsOpen (clearSet L.ε L.ν) :=
    (isOpen_lt continuous_const UnforcedLeray.Axi.continuous_ϱ).inter
      (isOpen_lt continuous_const
        ((continuous_const.mul UnforcedLeray.Axi.continuous_ϱ).pow 2))
  -- conclude from ray decay
  suffices hdec : ∃ K' : ℝ, RayDecayW Z τ r₀ z 1 K' by
    obtain ⟨K', hK'⟩ := hdec
    exact primData_of_decayW hK' hr₀pos one_pos hr₀r
  rcases hZ with rfl | hZ
  · -- the actual field `zAct = X₀` (separated response of the old thin source)
    set Tc := chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T) with hTc
    have hGdef : thinG Pl K L T = strSum Tc := rfl
    have hGm : Measurable (thinG Pl K L T) := by
      unfold thinG
      exact (Lp.stronglyMeasurable _).measurable.add (Lp.stronglyMeasurable _).measurable
    have hmom : ∫⁻ p, ‖thinG Pl K L T p‖ₑ ^ 2 ∂(ageμ (cOf L.ν) (-1 / 2)) < ⊤ := by
      rw [hGdef]
      exact strChartL2 (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν hρb (by linarith) hν Tc
    have hz : ∀ᵐ p ∂(ageμ (cOf L.ν) (-1 / 2)), L.ν * p.1 ≤ 6 / 5 → thinG Pl K L T p = 0 := by
      rw [hGdef]
      exact strSum_zero_young _ _ _ _ _ K.hχo hρb _
    obtain ⟨P1, T1, hP1, hS1, hM1, hE1⟩ :=
      sepSrc_of_chart (cOf L.ν) L.ν L.ε hc hν hε _ hGm hmom hz
    have hro : 0 < L.ε⁻¹ * Real.sqrt (5 * L.ν / 6) :=
      mul_pos (inv_pos.2 hε) (Real.sqrt_pos.2 (by positivity))
    have hcd : ContDiffOn ℝ 1 (zAct Pl K L μ T τ) (clearSet L.ε L.ν) :=
      ((wardX0_cd hν hμ hro.le hP1 hS1 hM1 hE1 τ).mono (clear_sub_young hε hν)).of_le
        (by norm_num)
    have heq : zAct Pl K L μ T τ = sepField L.ν μ T1 τ := by
      funext y
      exact wardX0_eq_T' hE1 τ y
    obtain ⟨C, hC⟩ := sep_far hν hμ hro hP1 hS1 hM1 τ
    refine rayDecayW_of hUo hcd hr₀pos hmem (R₁ := 2 * (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)))
      (C := C) (fun ρ hρ _ z' => ?_) z
    rw [heq]
    exact hC ρ hρ z'
  · -- the mean field `zMt = W^mt_μ - W^mt_{μ+1}` (zero-width Newton field)
    rw [Set.mem_singleton_iff] at hZ
    subst hZ
    obtain ⟨C, k, hCk⟩ := sourceLN0 K.mZ (gRate Pl) hmZ hγ
    have hfin : OldThinFinite (cOf L.ν) L.ν (thinRep T) :=
      (hCk (cOf L.ν) L.ν (L.ρb Pl K) hLH.c_pos hν hLH.nu_le T).1
    have hcd : ContDiffOn ℝ 1 (zMt Pl K L μ T τ) (clearSet L.ε L.ν) :=
      (zMt_regular Pl K L μ hLH hmZ hγ T τ).1
    have heq : zMt Pl K L μ T τ = newtonField (cOf L.ν) L.ν L.ε μ K.χo (thinRep T) := by
      funext y; rfl
    have hr₀b : 5 * L.ν / (6 * L.ε ^ 2) < r₀ ^ 2 := by
      have h1 := hclear r₀ le_rfl
      have h6 : 0 < 6 * L.ε ^ 2 := by positivity
      rw [div_lt_iff₀ h6]
      have : 5 * L.ν / 6 < L.ν / (11 / 10) := by
        rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; nlinarith
      nlinarith [mul_pow L.ε r₀ 2]
    obtain ⟨C', hC'⟩ := newton_far hc hν hε hLH.mu_pos hLH.chiO hfin hr₀pos hr₀b
    refine rayDecayW_of hUo hcd hr₀pos hmem (R₁ := r₀) (C := C') (fun ρ hρ _ z' => ?_) z
    rw [heq]
    exact hC' ρ hρ z'

end ZPrimKernel

end GeomXAsm

open GeomXAsm.ZPrimKernel in
/-- **`PartIII-b:C/rep/8/1/1/1/asm/4`** (`zPrimRegular`): along the sequence, at every phase and
every point of the clear region, the actual field `zAct` and the mean field `zMt` have convergent,
differentiable outward primitives (`PrimData`; source 4178-4186, 5400-5406). -/
theorem zPrimRegular (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.ZPrimRegular := by
  unfold SeqData.ZPrimRegular
  filter_upwards [D.eventually_lHyp hst.omega_ne hst.gamma_pos hst.sigma_pos hst.sigma_lt
    hst.chiY] with n hn z hz
  exact zPrimRegularAt_of D.Pl D.K (D.level n) (D.mu n z) (hn z hz) hst.mZ_gt hst.gamma_pos
    hst.C0_pos

end UnforcedLeray.Short.PartIIIb.Concrete
