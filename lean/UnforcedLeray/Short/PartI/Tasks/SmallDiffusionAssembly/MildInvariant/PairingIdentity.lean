import UnforcedLeray.Short.PartI.Sub.PartI_C05_4
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.EllL0
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.ExpDPairing
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.PairingIdentity.Fubini
import UnforcedLeray.Short.PartI.Tasks.SmallDiffusionAssembly.MildInvariant.PairingIdentity.Pieces

/-!
# Target `PartI:C05/4/3`: the mild pairing identity

Source of record: `the November 2 reference manuscript`, lines 1056-1058 (testing
the mild equation against `q†`).  With `ℓ = ⟨qd, ·⟩`, the Duhamel formula at `t` gives
`ℓ(U t) = ℓ(e^{B(s,t)D} x) + ∫_s^t ℓ(e^{B(r,t)D} G_r U_r) dr`.  The measurable-clock pairing
identity expands the inner pairing, `ℓ(G_r y) = -ℓ y - β(r)⟨Dqd, y⟩` cancels the `β(r)` terms, and
Fubini on the triangle `s ≤ r ≤ τ ≤ t` recombines the rest into `⟨Dqd, U τ⟩ - ⟨Dqd, e^{B(s,τ)D}x⟩`,
which cancels against the expansion of `ℓ(e^{B(s,t)D} x)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open PairingPieces PairingFubini

set_option maxHeartbeats 6400000 in
/-- **Target `PartI:C05/4/3`**: the measurable-clock pairing identity. -/
theorem mildPairingIdentity : MildPairingIdentity := by
  intro lam q l hI qd hl hq hqd β hβm hβ01 U hU s t hst x
  have hβint : ∀ a b : ℝ, IntervalIntegrable β volume a b :=
    fun a b => ExpDPairingHelp.beta_intervalIntegrable hβm hβ01 a b
  have hUc : ContinuousOn (fun r => U r s x) (Ici s) := hU.cont s x
  -- continuous extension of `r ↦ U r s x` (agreeing with it on `[s, ∞)`)
  obtain ⟨Ũ, hŨc, hŨ⟩ : ∃ Ũ : ℝ → B0010.XG, Continuous Ũ ∧ ∀ r, s ≤ r → Ũ r = U r s x := by
    refine ⟨fun r => U (max r s) s x, ?_, fun r hr => ?_⟩
    · have h1 : ContinuousOn (fun r => U (max r s) s x) univ :=
        hUc.comp (continuous_id.max continuous_const).continuousOn (fun r _ => le_max_right r s)
      exact continuousOn_univ.mp h1
    · show U (max r s) s x = U r s x
      rw [max_eq_left hr]
  have hUI : ContinuousOn (fun r => U r s x) (uIcc s t) :=
    hUc.mono (by rw [uIcc_of_le hst]; exact Icc_subset_Ici_self)
  -- the integrand `z_r = G_r(Ũ r)` as an opaque function (no unfolding of `pairOp` below)
  obtain ⟨zz, hzz⟩ : ∃ zz : ℝ → B0010.XG,
      zz = fun r => pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (Ũ r) :=
    ⟨_, rfl⟩
  have hzzU : ∀ r, s ≤ r →
      zz r = pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x) := by
    intro r hr
    simp only [hzz]
    rw [hŨ r hr]
  have hzzm : StronglyMeasurable zz := by
    have hβ' : StronglyMeasurable β := hβm.stronglyMeasurable
    have hŨsm : StronglyMeasurable Ũ := hŨc.stronglyMeasurable
    have e1 : StronglyMeasurable (fun r => Planar.L0 (Ũ r)) :=
      Planar.L0.continuous.comp_stronglyMeasurable hŨsm
    have e2 : StronglyMeasurable (fun r => lam • Ũ r) := hŨsm.const_smul lam
    have e3 : StronglyMeasurable (fun r => l (Ũ r) • q) :=
      (l.continuous.comp_stronglyMeasurable hŨsm).smul_const q
    have e4 : StronglyMeasurable (fun r => ((β r : ℂ) * seedKappa l q hq) • Ũ r) :=
      ((Complex.continuous_ofReal.comp_stronglyMeasurable hβ').mul_const _).smul hŨsm
    have e5 : StronglyMeasurable (fun r => (β r : ℂ) • seedRf l q qd hq hqd (Ũ r)) :=
      (Complex.continuous_ofReal.comp_stronglyMeasurable hβ').smul
        ((seedRf l q qd hq hqd).continuous.comp_stronglyMeasurable hŨsm)
    have e : StronglyMeasurable (fun r => Planar.L0 (Ũ r) - lam • Ũ r - l (Ũ r) • q -
        (((β r : ℂ) * seedKappa l q hq) • Ũ r) + (β r : ℂ) • seedRf l q qd hq hqd (Ũ r)) :=
      ((((e1.sub e2).sub e3).sub e4).add e5)
    have heq : zz = fun r => Planar.L0 (Ũ r) - lam • Ũ r - l (Ũ r) • q -
        (((β r : ℂ) * seedKappa l q hq) • Ũ r) + (β r : ℂ) • seedRf l q qd hq hqd (Ũ r) := by
      rw [hzz]
      funext r
      simp only [pairOp, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smulRight_apply]
    rw [heq]
    exact e
  have hGm : StronglyMeasurable (fun p : ℝ × ℝ => pairG qd hqd β zz p.1 p.2) := by
    have hcl : StronglyMeasurable (fun p : ℝ × ℝ => ∫ u in p.1..p.2, β u) :=
      (clock_joint_cont hβm hβ01).stronglyMeasurable
    have hzp : StronglyMeasurable (fun p : ℝ × ℝ => zz p.1) := hzzm.comp_measurable measurable_fst
    have h1 : StronglyMeasurable (fun p : ℝ × ℝ => ((∫ u in p.1..p.2, β u), zz p.1)) :=
      hcl.prodMk hzp
    have h2 := expD_joint_cont.comp_stronglyMeasurable h1
    have hin : Continuous fun w : B0010.XG => inner ℂ (B0094.D ⟨qd, hqd⟩) w :=
      continuous_const.inner continuous_id
    have h3 := hin.comp_stronglyMeasurable h2
    have h4 : StronglyMeasurable (fun p : ℝ × ℝ => (β p.2 : ℂ)) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable ((hβm.comp measurable_snd).stronglyMeasurable)
    unfold pairG
    exact h4.mul h3
  -- a uniform bound for the operators on the relevant compact set
  obtain ⟨Cz, hCz⟩ : ∃ C : ℝ, ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ (Ũ '' Icc s t),
      ‖pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) p.1 p.2‖ ≤ C := by
    have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ (Ũ '' Icc s t)) :=
      isCompact_Icc.prod (isCompact_Icc.image hŨc)
    exact hK.exists_bound_of_continuousOn
      (pairOp_clm_cont lam q l (seedKappa l q hq) (seedRf l q qd hq hqd)).continuousOn
  have hKey : ∀ b : ℝ, (0 ≤ b ∧ b ≤ 1) → ∀ x ∈ Icc s t,
      ‖pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) b (Ũ x)‖ ≤ Cz :=
    fun b hb x hx => hCz (b, Ũ x) ⟨⟨hb.1, hb.2⟩, mem_image_of_mem Ũ hx⟩
  have hGb : ∀ x ∈ Icc s t, ∀ y ∈ Icc s t, ‖pairG qd hqd β zz x y‖ ≤ ‖B0094.D ⟨qd, hqd⟩‖ * Cz := by
    intro x hx y _
    have hxK : (β x, Ũ x) ∈ Icc (0 : ℝ) 1 ×ˢ (Ũ '' Icc s t) :=
      ⟨⟨(hβ01 x).1, (hβ01 x).2⟩, mem_image_of_mem Ũ hx⟩
    have hz : ‖zz x‖ ≤ Cz := by
      rw [hzz]
      exact hKey (β x) (hβ01 x) x hx
    have hv : ‖B0123.expD (∫ u in x..y, β u) (zz x)‖ ≤ Cz :=
      ((B0123.expD _).le_opNorm _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (B0123.norm_expD_le _)).trans hz)
    have hβy : ‖(β y : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hβ01 y).1], (hβ01 y).2⟩
    unfold pairG
    calc ‖(β y : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (B0123.expD (∫ u in x..y, β u) (zz x))‖
        ≤ 1 * (‖B0094.D ⟨qd, hqd⟩‖ * Cz) := by
          refine (norm_mul_le _ _).trans (mul_le_mul hβy ?_ (norm_nonneg _) zero_le_one)
          exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
      _ = ‖B0094.D ⟨qd, hqd⟩‖ * Cz := one_mul _
  -- Fubini on the triangle
  have hSwap := triangle_swap (pairG qd hqd β zz) hst hGm (‖B0094.D ⟨qd, hqd⟩‖ * Cz) hGb
  -- integrability facts
  have hint : IntervalIntegrable (fun r => B0123.expD (∫ u in r..t, β u)
      (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x))) volume s t :=
    hU.integrable s t hst x
  have hintτ : ∀ τ, s ≤ τ → IntervalIntegrable (fun r => B0123.expD (∫ u in r..τ, β u)
      (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x))) volume s τ :=
    fun τ hsτ => hU.integrable s τ hsτ x
  have hIL : IntervalIntegrable (fun r => l (U r s x)) volume s t :=
    (l.continuous.comp_continuousOn hUI).intervalIntegrable
  have hNeg : IntervalIntegrable (fun r => -(l (U r s x))) volume s t := hIL.neg
  have hβC : ∀ a b : ℝ, IntervalIntegrable (fun τ => (β τ : ℂ)) volume a b :=
    fun a b => intervalIntegrable_iff.mpr (Integrable.ofReal (intervalIntegrable_iff.mp (hβint a b)))
  have hIBU : IntervalIntegrable (fun τ => (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (U τ s x))
      volume s t :=
    (hβC s t).mul_continuousOn (ContinuousOn.inner continuousOn_const hUI)
  have hBc : Continuous fun τ => ∫ u in s..τ, β u :=
    intervalIntegral.continuous_primitive (fun a b => hβint a b) s
  have hIBE : IntervalIntegrable
      (fun τ => (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (B0123.expD (∫ u in s..τ, β u) x))
      volume s t :=
    (hβC s t).mul_continuousOn
      (Continuous.continuousOn (continuous_const.inner ((Cons.G3b.continuous_expD_apply x).comp hBc)))
  have hILF : IntervalIntegrable (fun r => l (B0123.expD (∫ u in r..t, β u)
      (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)))) volume s t :=
    intervalIntegrable_iff.mpr (l.integrable_comp (intervalIntegrable_iff.mp hint))
  -- Step 1: the Duhamel formula at `t`, tested against `ℓ`
  have hdu : U t s x = B0123.expD (∫ u in s..t, β u) x + ∫ r in s..t,
      B0123.expD (∫ u in r..t, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)) :=
    hU.duhamel s t hst x
  have hA : l (U t s x) = l (B0123.expD (∫ u in s..t, β u) x) + ∫ r in s..t,
      l (B0123.expD (∫ u in r..t, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x))) := by
    rw [hdu, map_add, ← l.intervalIntegral_comp_comm hint]
  -- Step 2: the pairing identity pointwise in `r`
  have hPair : ∀ r ∈ uIcc s t,
      l (B0123.expD (∫ u in r..t, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x))) =
      l (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)) +
        ∫ τ in r..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
          (B0123.expD (∫ u in r..τ, β u)
            (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x))) := by
    intro r hr
    rw [uIcc_of_le hst] at hr
    rw [hl, hl]
    exact expDPairingMeasurable qd hqd β hβm hβ01 r t hr.2 _
  -- Step 3: the `β(r)` terms cancel pointwise
  have hΦint : ∫ r in s..t, (∫ τ in r..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
      (B0123.expD (∫ u in r..τ, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)))) =
      (∫ r in s..t, l (B0123.expD (∫ u in r..t, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)))) -
      ∫ r in s..t, (-(l (U r s x)) - (β r : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (U r s x)) := by
    have hGl' : IntervalIntegrable (fun r => -(l (U r s x)) - (β r : ℂ) *
        inner ℂ (B0094.D ⟨qd, hqd⟩) (U r s x)) volume s t := hNeg.sub hIBU
    rw [← intervalIntegral.integral_sub hILF hGl']
    apply intervalIntegral.integral_congr
    intro r hr
    have hp := hPair r hr
    rw [pairOp_ell hI hq qd hqd (β r) (U r s x)] at hp
    dsimp only
    linear_combination -hp
  -- Step 4: the Fubini swap and the pairing of the swapped inner integral
  have hΦ2 : ∫ r in s..t, (∫ τ in r..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
      (B0123.expD (∫ u in r..τ, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)))) =
      (∫ τ in s..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (U τ s x)) -
        ∫ τ in s..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
          (B0123.expD (∫ u in s..τ, β u) x) := by
    have h1 : ∫ r in s..t, (∫ τ in r..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
        (B0123.expD (∫ u in r..τ, β u)
          (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)))) =
        ∫ r in s..t, ∫ τ in r..t, pairG qd hqd β zz r τ := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hst] at hr
      simp only [pairG, hzzU r hr.1]
    rw [h1, hSwap, ← intervalIntegral.integral_sub hIBU hIBE]
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hst] at hτ
    have hsτ : s ≤ τ := hτ.1
    have hcongr : ∫ r in s..τ, pairG qd hqd β zz r τ =
        ∫ r in s..τ, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
          (B0123.expD (∫ u in r..τ, β u)
            (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x))) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hsτ] at hr
      simp only [pairG, hzzU r hr.1]
    have hI2 : ∫ r in s..τ, B0123.expD (∫ u in r..τ, β u)
        (pairOp lam q l (seedKappa l q hq) (seedRf l q qd hq hqd) (β r) (U r s x)) =
        U τ s x - B0123.expD (∫ u in s..τ, β u) x := by
      have hdτ := hU.duhamel s τ hsτ x
      rw [hdτ]
      abel
    dsimp only
    rw [hcongr, intervalIntegral.integral_const_mul,
      ← inner_integral_right' _ (hintτ τ hsτ), hI2, inner_sub_right, mul_sub]
  -- Step 5: the pairing of `ℓ(e^{B(s,t)D} x)`
  have hPe : l (B0123.expD (∫ u in s..t, β u) x) = l x +
      ∫ τ in s..t, (β τ : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩)
        (B0123.expD (∫ u in s..τ, β u) x) := by
    rw [hl, hl]
    exact expDPairingMeasurable qd hqd β hβm hβ01 s t hst x
  -- Step 6: combine
  have hGl : ∫ r in s..t, (-(l (U r s x)) - (β r : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (U r s x)) =
      -(∫ r in s..t, l (U r s x)) - ∫ r in s..t, (β r : ℂ) * inner ℂ (B0094.D ⟨qd, hqd⟩) (U r s x) := by
    rw [intervalIntegral.integral_sub hNeg hIBU, intervalIntegral.integral_neg]
  rw [hA, hPe]
  linear_combination hΦ2 + hGl - hΦint

end UnforcedLeray.Short.PartI
