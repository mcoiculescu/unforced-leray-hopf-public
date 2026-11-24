import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_4

/-!
# Part II-b, task `PartII-b:G4/3/4/1/C` (`chartAdv_dRho_dz`)

Source of record: `the November 2 reference manuscript`, SP 1919-1921, 2007-2012.
For `ρ = p.1 > 0` the scaled profile `F(q) = √(R²/q₁²) • φ(merChart R τ q)` equals `(R/q₁) • φ(…)`
near `p`, and the chain rule through `merChart` gives
`∂_ρ F = (R²/ρ²) Q_ε φ` with `ε = R⁻¹` (`Q_ε = ∂_q − ε(K+1)` on the chart profile, `K = 2s∂_s + η∂_η`)
and `∂_z F = (R²/ρ²) ∂_η φ`.

Naming: the library has `Axi.dρ` (the statement's `Axi.dRho` is its ASCII alias, defined here).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Axi

/-- ASCII name for the profile derivative `∂_ρ b = Db(p)(1, 0)`; the same as `dρ`. -/
abbrev dRho {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (b : ℝ × ℝ → F) (p : ℝ × ℝ) :
    F :=
  dρ b p

end UnforcedLeray.Axi

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:G4/3/4/1/C`**: the chain rule for the scaled ring profile in the meridional
variables `(ρ, z)`, expressed through `Q_ε` (`qEps R⁻¹`) and `∂_η`. -/
theorem chartAdv_dRho_dz (R : ℝ) (hR : 0 < R) (φ : Coord → Axi.Merid) (τ : ℝ) (p : ℝ × ℝ)
    (hp : 0 < p.1) (hφ : DifferentiableAt ℝ φ (Axi.merChart R τ p)) :
    Axi.dRho (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • φ (Axi.merChart R τ q)) p =
        (R ^ 2 / p.1 ^ 2) • qEps R⁻¹ φ (Axi.merChart R τ p) ∧
      Axi.dz (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • φ (Axi.merChart R τ q)) p =
        (R ^ 2 / p.1 ^ 2) • Axi.dEta φ (Axi.merChart R τ p) := by
  have hR0 : R ≠ 0 := hR.ne'
  have hpne : p.1 ≠ 0 := hp.ne'
  -- the square root is `R/ρ` near `p`
  have hev : ∀ᶠ q : ℝ × ℝ in 𝓝 p, 0 < q.1 :=
    (continuous_fst.tendsto p).eventually (lt_mem_nhds hp)
  have hEq : (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • φ (Axi.merChart R τ q)) =ᶠ[𝓝 p]
      (fun q : ℝ × ℝ => (R / q.1) • φ (Axi.merChart R τ q)) := by
    filter_upwards [hev] with q hq
    rw [← div_pow, Real.sqrt_sq (div_nonneg hR.le hq.le)]
  have hm : DifferentiableAt ℝ (Axi.merChart R τ) p := Axi.differentiableAt_merChart hR0 τ hpne
  have hfst : DifferentiableAt ℝ (fun q : ℝ × ℝ => q.1) p := differentiableAt_fst
  have hinvR : DifferentiableAt ℝ (fun q : ℝ × ℝ => R / q.1) p := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_const R).fun_mul (hfst.fun_inv hpne)
  have hG : DifferentiableAt ℝ (fun q : ℝ × ℝ => (R / q.1) • φ (Axi.merChart R τ q)) p :=
    hinvR.smul (hφ.comp p hm)
  have hρ : Axi.dRho (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • φ (Axi.merChart R τ q)) p =
      Axi.dρ (fun q : ℝ × ℝ => (R / q.1) • φ (Axi.merChart R τ q)) p := by
    unfold Axi.dRho Axi.dρ
    rw [hEq.fderiv_eq]
  have hz : Axi.dz (fun q : ℝ × ℝ => √(R ^ 2 / q.1 ^ 2) • φ (Axi.merChart R τ q)) p =
      Axi.dz (fun q : ℝ × ℝ => (R / q.1) • φ (Axi.merChart R τ q)) p := by
    unfold Axi.dz
    rw [hEq.fderiv_eq]
  -- derivative of `ρ ↦ R/ρ`
  have hinv : HasDerivAt (fun r : ℝ => R / r) (-(R / p.1 ^ 2)) p.1 := by
    have h := (hasDerivAt_inv hpne).const_mul R
    have hf : (fun r : ℝ => R / r) = fun r => R * r⁻¹ := funext fun r => div_eq_mul_inv R r
    have hd : -(R / p.1 ^ 2) = R * -(p.1 ^ 2)⁻¹ := by ring
    rw [hf, hd]
    exact h
  -- radial line derivative
  have hgr : HasDerivAt (fun r : ℝ => φ (Axi.merChart R τ (r, p.2)))
      (fderiv ℝ φ (Axi.merChart R τ p) (-(2 * R ^ 2 / p.1 ^ 3), (R / p.1, -(R * p.2 / p.1 ^ 2))))
      p.1 :=
    hφ.hasFDerivAt.comp_hasDerivAt p.1 (Axi.hasDerivAt_merChart_fst hR0 τ p.2 hpne)
  have hρG := (Axi.hasDerivAt_line_fst hG).unique (hinv.smul hgr)
  -- axial line derivative
  have hgz : HasDerivAt (fun z : ℝ => φ (Axi.merChart R τ (p.1, z)))
      (fderiv ℝ φ (Axi.merChart R τ p) ((0 : ℝ), ((0 : ℝ), R / p.1))) p.2 :=
    hφ.hasFDerivAt.comp_hasDerivAt p.2 (Axi.hasDerivAt_merChart_snd R τ (r := p.1) p.2)
  have hzG := (Axi.hasDerivAt_line_snd hG).unique
    ((hasDerivAt_const p.2 (R / p.1)).smul hgz)
  constructor
  · rw [hρ, hρG]
    simp only [qEps, kAge, Axi.dS, Axi.dQ, Axi.dEta]
    have e1 : (Axi.merChart R τ p).1 = R ^ 2 / p.1 ^ 2 := rfl
    have e2 : (Axi.merChart R τ p).2.2 = R * p.2 / p.1 := rfl
    rw [e1, e2, Axi.clm_triple]
    match_scalars <;> field_simp
  · have hc1 : fderiv ℝ φ (Axi.merChart R τ p) ((0 : ℝ), ((0 : ℝ), R / p.1)) =
        (R / p.1) • Axi.dEta φ (Axi.merChart R τ p) := by
      rw [Axi.clm_triple]
      simp only [zero_smul, zero_add]
      rfl
    rw [hz, hzG, hc1, Axi.dEta, zero_smul, add_zero, smul_smul]
    congr 1
    ring

end UnforcedLeray.Short.IIb
