import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_6
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.FreeResponseCongr

/-!
# `PartII-b:T10/6/3` (`ChartDrift`): decomposition

Source of record: `the November 2 reference manuscript`
lines 1912-1915 (`𝒯(√s b) = √s (S + 1/2) b`, `∂_ρ(√s b) = s Q_ε b`).

Two leaves: the chart lift of a coordinate test to a phase test with both pairing identities
(`ChartLiftPairing`, for every `H_r` profile, no approximation: change of variables plus Hölder),
and local integrability of `H_r` profiles against coordinate tests (`HrLocalIntegrable`).
`chartDrift_of` derives `ChartDrift` from them.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- **Leaf `T10/6/3/1`** (SP 1912-1915; the lift of a coordinate test): for a coordinate test `φ`
(smooth, compact support in `s > 0`) and a component `i` (`0` for `e_r`, `1` for `e_z`) there is a
phase test `Φ` of period `P = 2εc` (the `c`-periodization of `φ` in `q`, pushed through the ring
chart `(τ, y) ↦ (s, q, η)`, times `e_r` or `e_z`, normalized by the constant of the change of
variables) such that for every `b ∈ H_r`
`⟪Φ, N_v b⟫ = ∫ b_i φ` and `⟪𝒯ᵗΦ, N_v b⟫ = ∫ b_i (Sᵗφ + φ/2)`, `Sᵗφ = -∂_s(sφ)`.
The integrals converge by Hölder (`HrLocalIntegrable`) and `phaseLpNorm_NvC`.
Components: (i) the lifted test is an `IsPhaseTest`; (ii) `pairF Φ (NvC b)` = `∫ b_i φ`
(change of variables, `phaseAvg_ringChart`); (iii) `driftT Φ` is the lift of the test
`-(S + 1/2)φ` (dilation invariance of `e_r, e_z`; as in `DriftSmoothPt`, `Sub/PartIIb_T08_1.lean`). -/
def ChartLiftPairing : Prop :=
  ∀ (c ε r : ℝ) (φ : Coord → ℝ) (i : Fin 2), 0 < c → 0 < ε → 1 < r → IsCoordTest φ →
    ∃ Φ : ℝ × Space → CVec3, IsPhaseTest (2 * ε * c) Φ ∧
      ∀ b : CProf, InHr c r b →
        pairF (2 * ε * c) Φ (NvC ε⁻¹ b) = ∫ x, b x i * (φ x : ℂ) ∧
        pairF (2 * ε * c) (driftT Φ) (NvC ε⁻¹ b) =
          ∫ x, b x i * ((coordTranspose vS dZero φ x : ℝ) + (1 / 2 : ℂ) * (φ x : ℂ))

/-- **Leaf `T10/6/3/2`** (Hölder with the weight `s^{r/2-5/2}`, periodicity in `q`): an `H_r`
profile is locally integrable against a coordinate test. -/
def HrLocalIntegrable : Prop :=
  ∀ (c r : ℝ) (b : CProf) (ψ : Coord → ℝ) (i : Fin 2), 0 < c → 1 < r → InHr c r b →
    IsCoordTest ψ → Integrable (fun x => b x i * (ψ x : ℂ))

/-- The transpose `Sᵗφ = -∂_s(sφ)` of a coordinate test is a coordinate test. -/
theorem isCoordTest_coordTranspose_vS {φ : Coord → ℝ} (hφ : IsCoordTest φ) :
    IsCoordTest (coordTranspose vS dZero φ) := by
  have hs : ContDiff ℝ ∞ (fun y : Coord => y.1 * φ y) := contDiff_fst.mul hφ.smooth
  have hfd : ContDiff ℝ ∞ (fun x : Coord => fderiv ℝ (fun y : Coord => y.1 * φ y) x) :=
    hs.fderiv_right (m := ∞) (by simp)
  have e : coordTranspose vS dZero φ =
      fun x => -(fderiv ℝ (fun y : Coord => y.1 * φ y) x (cdir 0)) := by
    funext x
    simp [coordTranspose, cpd, vS, dZero, Fin.sum_univ_three]
  have hsupp : tsupport (fun y : Coord => y.1 * φ y) ⊆ tsupport φ := by
    refine closure_mono ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    exact right_ne_zero_of_mul hy
  have hcs : HasCompactSupport (fun y : Coord => y.1 * φ y) :=
    HasCompactSupport.mul_left (f := fun y : Coord => y.1) hφ.compact
  have hg0 : (fun L : Coord →L[ℝ] ℝ => -(L (cdir 0))) 0 = 0 := by simp
  have hfc : HasCompactSupport (fderiv ℝ (fun y : Coord => y.1 * φ y)) := hcs.fderiv ℝ
  rw [e]
  refine ⟨(hfd.clm_apply contDiff_const).neg, ?_, ?_⟩
  · exact hfc.comp_left (g := fun L : Coord →L[ℝ] ℝ => -(L (cdir 0))) hg0
  · exact (closure_mono (Function.support_comp_subset (g := fun L : Coord →L[ℝ] ℝ => -(L (cdir 0))) hg0
      (fderiv ℝ (fun y : Coord => y.1 * φ y)))).trans
      ((tsupport_fderiv_subset ℝ).trans (hsupp.trans hφ.supp))

theorem chartDrift_of (h1 : ChartLiftPairing) (h2 : HrLocalIntegrable) : ChartDrift := by
  intro c ε r b₀ p d hc hε hr hb hp hpd hop i
  have hIb : ∀ (ψ : Coord → ℝ), IsCoordTest ψ → Integrable (fun x => b₀ x i * (ψ x : ℂ)) :=
    fun ψ hψ => h2 c r b₀ ψ i hc hr hb hψ
  have hIp : ∀ (ψ : Coord → ℝ), IsCoordTest ψ → Integrable (fun x => p x i * (ψ x : ℂ)) :=
    fun ψ hψ => h2 c r p ψ i hc hr hp hψ
  have hIg : ∀ φ, IsCoordTest φ →
      Integrable (fun x => (p x - (1 / 2 : ℂ) • b₀ x) i * (φ x : ℂ)) := by
    intro φ hφ
    have := (hIp φ hφ).sub ((hIb φ hφ).const_mul (1 / 2 : ℂ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun φ hφ => ⟨?_, hIg φ hφ⟩, fun φ hφ => ?_⟩
  · exact hIb _ (isCoordTest_coordTranspose_vS hφ)
  · obtain ⟨Φ, hΦ, hΦb⟩ := h1 c ε r φ i hc hε hr hφ
    obtain ⟨e1, e2⟩ := hΦb b₀ hb
    obtain ⟨e3, e4⟩ := hΦb p hp
    have hq := hop Φ hΦ
    rw [FreeRespCongrHelp.pairF_congr_ae' _ Φ d (NvC ε⁻¹ p) hpd.symm, e2, e3] at hq
    have hT := hIb _ (isCoordTest_coordTranspose_vS hφ)
    have hb' := hIb φ hφ
    have hsplit : ∫ x, b₀ x i * ((coordTranspose vS dZero φ x : ℝ) + (1 / 2 : ℂ) * (φ x : ℂ)) =
        (∫ x, b₀ x i * (coordTranspose vS dZero φ x : ℂ)) +
          (1 / 2 : ℂ) * ∫ x, b₀ x i * (φ x : ℂ) := by
      rw [← integral_const_mul, ← integral_add hT (hb'.const_mul (1 / 2 : ℂ))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    have hsub : ∫ x, (p x - (1 / 2 : ℂ) • b₀ x) i * (φ x : ℂ) =
        (∫ x, p x i * (φ x : ℂ)) - (1 / 2 : ℂ) * ∫ x, b₀ x i * (φ x : ℂ) := by
      rw [← integral_const_mul, ← integral_sub (hIp φ hφ) (hb'.const_mul (1 / 2 : ℂ))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hsub]
    rw [hsplit] at hq
    linear_combination (-1 : ℂ) * hq

end UnforcedLeray.Short.IIb
