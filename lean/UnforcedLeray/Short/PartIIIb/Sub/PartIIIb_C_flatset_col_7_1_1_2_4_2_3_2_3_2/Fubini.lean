import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2.Prod

/-!
# Test-pairing identity for `b ∈ solenoidalHC 0 c` (helper for `pepsC0SliceDivFreeAE`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- For `b ∈ solenoidalHC 0 c` and any profile test `Φ`, the Fubini formula for `⟪cgrad Φ, b⟫`
vanishes. -/
theorem hj3_orth_fubini (c : ℝ) (hc : 0 < c)
    (b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (hb : b ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)
    (Φ : UnforcedLeray.B0226.ProfileTest c) :
    ∫ s in Ioi (0 : ℝ), ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ∫ x in stripSet c, ∑ i : Fin 2,
          (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1 (s, x)) i *
            (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) i = 0 := by
  have hg : MemLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1) 2
      (UnforcedLeray.B0220.measureH c) :=
    UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad Φ.2
  set β : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC :=
    (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) with hβ
  have hmem : MemLp (fun p => toMC ((β p).ofLp)) 2 (UnforcedLeray.B0220.measureH c) := by
    simpa [toMC, hβ] using Lp.memLp b
  have hbeq : hmem.toLp _ = b := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp hmem] with p hp
    rw [hp]
    simp [toMC, hβ]
  have h := pepsC0FubiniSol c hc Φ hg (fun p => (β p).ofLp) hmem
  have horth : inner ℂ (hg.toLp (UnforcedLeray.Short.PartIIa.cgrad 0 Φ.1)) b = 0 := by
    refine (Submodule.mem_orthogonal _ _).1 hb _ ?_
    apply Submodule.subset_span
    exact ⟨Φ, hg, rfl⟩
  rw [hbeq, horth] at h
  exact h.symm

/-- The product test `χ(s) ψ(q,η)` gives the Fubini identity with the slice integrand
`χ(s) ⟨∇ψ, b⟩`. -/
theorem hj3_test_identity (c : ℝ) (hc : 0 < c)
    (b : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)
    (hb : b ∈ UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)
    {χ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχp : tsupport χ ⊆ Ioi 0) (hψ : UnforcedLeray.B0579.IsCylTest c ψ) :
    ∫ s in Ioi (0 : ℝ), ((s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
        ((χ s : ℂ) * ∫ x in stripSet c,
          ((b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 0 *
              (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
            (b : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (s, x) 1 *
              (UnforcedLeray.B0579.pd 1 ψ x : ℂ))) = 0 := by
  have hχd : Differentiable ℝ χ := hχs.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable
  have h := hj3_orth_fubini c hc b hb
    ⟨fun p : ℝ × (ℝ × ℝ) => χ p.1 * ψ p.2, hj3_isProfileTest c hχs hχc hχp hψ⟩
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s _
  dsimp only
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Fin.sum_univ_two, hj3_cgrad_zero_apply, hj3_cgrad_one_apply,
    hj3_dQ_prod χ ψ hχd hψd, hj3_dEta_prod χ ψ hχd hψd]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
