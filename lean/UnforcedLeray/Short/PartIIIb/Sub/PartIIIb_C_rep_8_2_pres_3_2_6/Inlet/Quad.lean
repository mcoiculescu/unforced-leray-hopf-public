import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Inlet.Integral
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_6.Phys
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletJetDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.JetLe
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.NvFderiv

/-!
# Pointwise ring envelope of the quadratic inlet source
(helper of `PartIII-b:C/rep/8/2/pres/3/2/6/1`)

Source `the November 2 reference manuscript`
2347-2358 (exponential transverse decay of the periodized eigenstream and its derivatives),
2360-2366 (`e_ε = e_0 + εe_1`, cut off at `s ≤ H/2`), 2388-2390 (the quadratic inlet source
`E_εα·∇E_εα` has the same bound with `|α|²`), 2422-2423 (`∂_ρ(√s f) = sQ_εf`, `∂_z(√s f) = s∂_ηf`).

With `E_εα = N_v e`, `e = Σαᵢe_ε^{(i)}`: `|E_εα| = √s|e|` and `|∇E_εα| ≤ s(|∂_ηe| + |Q_εe| + ε|e_r|)`
(Part II-b `NvFderivBound`), and the inlet jets decay like `ν^{-k}e^{-κ|η|/c}` (`InletJetDecay`), so
`|E_εα·∇E_εα| ≤ Bν^{-k}(1+H)|α|² s^{3/2}(1+|η|)e^{-κ|η|/c}` on `0 < s ≤ H/2`, and `0` for
`s > H/2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff
open UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet

open UnforcedLeray.Cons.C03.Concrete (Params)

/-- The gradient quantity of `NvFderivBound` is at most `2s` times the first chart jet. -/
theorem gradProfileQuantity_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (b : ℝ × (ℝ × ℝ) → Merid)
    (x : ℝ × (ℝ × ℝ)) (hs : 0 ≤ x.1) :
    UnforcedLeray.Short.IIb.gradProfileQuantity ε b x ≤
      2 * x.1 * UnforcedLeray.Short.IIb.chartJet b x := by
  unfold UnforcedLeray.Short.IIb.gradProfileQuantity UnforcedLeray.Short.IIb.chartJet
  have hK : ‖(2 * x.1) • Axi.dS b x + x.2.2 • Axi.dEta b x‖ =
      ‖UnforcedLeray.Short.IIb.kAge b x‖ := rfl
  have e1 : ‖Axi.dQ b x - ε • ((2 * x.1) • Axi.dS b x + x.2.2 • Axi.dEta b x + b x)‖ ≤
      ‖Axi.dQ b x‖ + (‖UnforcedLeray.Short.IIb.kAge b x‖ + ‖b x‖) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg h0]
    have : ‖(2 * x.1) • Axi.dS b x + x.2.2 • Axi.dEta b x + b x‖ ≤
        ‖UnforcedLeray.Short.IIb.kAge b x‖ + ‖b x‖ := by
      rw [← hK]; exact norm_add_le _ _
    have hn : 0 ≤ ‖(2 * x.1) • Axi.dS b x + x.2.2 • Axi.dEta b x + b x‖ := norm_nonneg _
    nlinarith
  have e2 : ε * |b x 0| ≤ ‖b x‖ := by
    have : |b x 0| ≤ ‖b x‖ := by
      rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le (b x) 0
    nlinarith [abs_nonneg (b x 0)]
  have hn : 0 ≤ ‖Axi.dEta b x‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖b x‖ := norm_nonneg _
  have hn3 : 0 ≤ ‖Axi.dQ b x‖ := norm_nonneg _
  have hn4 : 0 ≤ ‖UnforcedLeray.Short.IIb.kAge b x‖ := norm_nonneg _
  calc x.1 * (‖Axi.dEta b x‖ + ‖Axi.dQ b x - ε • ((2 * x.1) • Axi.dS b x + x.2.2 • Axi.dEta b x + b x)‖ +
        ε * |b x 0|)
      ≤ x.1 * (‖Axi.dEta b x‖ + (‖Axi.dQ b x‖ + (‖UnforcedLeray.Short.IIb.kAge b x‖ + ‖b x‖)) +
        ‖b x‖) := by gcongr
    _ ≤ 2 * x.1 * (‖b x‖ + ‖Axi.dQ b x‖ + ‖Axi.dEta b x‖ + ‖UnforcedLeray.Short.IIb.kAge b x‖) := by
        nlinarith

set_option maxHeartbeats 1000000 in
/-- **The quadratic inlet source is bounded by a ring envelope** (source 2347-2366, 2388-2390,
2422-2423). -/
theorem quad_ptw :
    ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
      UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
    ∀ dm dp : ℝ, 0 < dm → ∃ (B κ : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < B ∧ 0 < κ ∧ 0 < ν₀ ∧ ν₀ ≤ 1 ∧
      ∀ (p : Params) (d : ℝ),
        UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
        ∀ (α : Fin 2 → ℝ) (τ : ℝ) (y : Space), y ∉ axis →
          ‖inletQuadSrc p α τ y‖ ≤
            ringEnv p.H (B * (1 + p.H) * (p.ν ^ k)⁻¹ * ‖α‖ ^ 2) κ p.c 1
              (age p.R y) (trans p.R y) := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨CJ, κ, kJ, νJ, hCJ, hκ, hνJ, hνJ1, HJ⟩ :=
    UnforcedLeray.Short.IIb.inletJetDecay Sig lam q hSig hq dm dp hdm
  obtain ⟨νV, hνV, HV⟩ :=
    UnforcedLeray.Short.IIb.inletProfileSmoothVanish Sig lam q hSig hq dm dp hdm
  obtain ⟨KL, hKL, HL⟩ := UnforcedLeray.Short.IIb.jetLe
  refine ⟨16 * KL * CJ ^ 2, κ, kJ + kJ, min νJ νV, by positivity, hκ, lt_min hνJ hνV,
    (min_le_left _ _).trans hνJ1, ?_⟩
  intro p d hreg hν hS hm α τ y hy
  have h0 : p.ν ≤ νJ := hν.trans (min_le_left _ _)
  have h1 : p.ν ≤ νV := hν.trans (min_le_right _ _)
  have hνpos : 0 < p.ν := p.ν_pos
  have hHpos : 0 < p.H := p.H_pos
  have HJ' := HJ p d ⟨hreg, h0, hS, hm⟩
  have HV' := HV p d hreg h1 hS hm
  -- the affine inlet as one ring lift
  set e : ℝ × (ℝ × ℝ) → Merid := α 0 • p.inletProfile 0 + α 1 • p.inletProfile 1 with he
  have hcd0 : ContDiff ℝ ∞ (p.inletProfile 0) := (HV' 0).1
  have hcd1 : ContDiff ℝ ∞ (p.inletProfile 1) := (HV' 1).1
  have hecd : ContDiff ℝ ∞ e := (hcd0.const_smul (α 0)).add (hcd1.const_smul (α 1))
  have hEfun : (fun y' => ∑ i : Fin 2, α i • p.inlet i τ y') = Nv p.R e τ := by
    funext y'
    rw [Fin.sum_univ_two, he, Nv_add, Nv_smul, Nv_smul]
    rfl
  have hEy : ∑ i : Fin 2, α i • p.inlet i τ y = Nv p.R e τ y := congrFun hEfun y
  have hQ : inletQuadSrc p α τ y = fderiv ℝ (Nv p.R e τ) y (Nv p.R e τ y) := by
    unfold inletQuadSrc
    rw [hEfun, hEy]
  rw [hQ]
  clear_value e
  -- facts at the chart point, then forget its definition
  have hRne : p.R ≠ 0 := p.R_pos.ne'
  have hεpos : 0 ≤ p.R⁻¹ := inv_nonneg.2 p.R_pos.le
  have hε1 : p.R⁻¹ ≤ 1 := by
    have hRe : p.R⁻¹ = p.ε := by simp [Params.R]
    rw [hRe, hreg.eps_eq, Real.exp_le_one_iff]
    have := hreg.dm_le
    have := hreg.dm_pos
    have : 0 ≤ d / p.ν := div_nonneg (by linarith) hνpos.le
    rw [neg_div]
    linarith
  have hgrad := (nvFderivBound p.R τ e y p.R_pos hy ((hecd.differentiable (by simp)) _)).2
  have hnv : ‖Nv p.R e τ y‖ = √(age p.R y) * ‖e (chart p.R τ y)‖ := norm_Nv p.R e τ hy
  have hNv : Nv p.R e τ y = √(age p.R y) • frameL y (e (chart p.R τ y)) := rfl
  have hs0 : 0 < (chart p.R τ y).1 := age_pos hRne hy
  have hx1 : (chart p.R τ y).1 = age p.R y := rfl
  have hx2 : (chart p.R τ y).2.2 = trans p.R y := rfl
  rw [← hx1] at hnv hNv
  rw [← hx1, ← hx2]
  generalize chart p.R τ y = x at hgrad hnv hNv hs0 hx1 hx2 ⊢
  have hM : 0 ≤ 16 * KL * CJ ^ 2 * (1 + p.H) * (p.ν ^ (kJ + kJ))⁻¹ * ‖α‖ ^ 2 := by positivity
  by_cases hle : x.1 ≤ p.H / 2
  · rw [ringEnv_of_mem hs0 hle]
    have hE0 : 0 ≤ Real.exp (-(κ * |x.2.2| / p.c)) := (Real.exp_pos _).le
    have hE1 : Real.exp (-(κ * |x.2.2| / p.c)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]
      have := p.c_pos
      positivity
    generalize hEd : Real.exp (-(κ * |x.2.2| / p.c)) = E at hE0 hE1 ⊢
    have hJ0 : 0 ≤ CJ * (p.ν ^ kJ)⁻¹ * E := by positivity
    generalize hJ : CJ * (p.ν ^ kJ)⁻¹ * E = J at hJ0
    have ha0 : ‖α 0‖ ≤ ‖α‖ := norm_le_pi_norm α 0
    have ha1 : ‖α 1‖ ≤ ‖α‖ := norm_le_pi_norm α 1
    -- jets of `e`
    have hjet : ∀ l ≤ 2, ‖iteratedFDeriv ℝ l e x‖ ≤ 2 * ‖α‖ * J := by
      intro l hl
      have hc0 : ContDiffAt ℝ l (α 0 • p.inletProfile 0) x :=
        ((hcd0.const_smul (α 0)).of_le (by exact_mod_cast le_top)).contDiffAt
      have hc1 : ContDiffAt ℝ l (α 1 • p.inletProfile 1) x :=
        ((hcd1.const_smul (α 1)).of_le (by exact_mod_cast le_top)).contDiffAt
      have hc0' : ContDiffAt ℝ l (p.inletProfile 0) x :=
        (hcd0.of_le (by exact_mod_cast le_top)).contDiffAt
      have hc1' : ContDiffAt ℝ l (p.inletProfile 1) x :=
        (hcd1.of_le (by exact_mod_cast le_top)).contDiffAt
      rw [he, iteratedFDeriv_add_apply hc0 hc1, iteratedFDeriv_const_smul_apply hc0',
        iteratedFDeriv_const_smul_apply hc1']
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
      have b0 := (HJ' 0).2 l hl x
      have b1 := (HJ' 1).2 l hl x
      rw [hEd, hJ] at b0 b1
      have hn0 : 0 ≤ ‖iteratedFDeriv ℝ l (p.inletProfile 0) x‖ := norm_nonneg _
      have hn1 : 0 ≤ ‖iteratedFDeriv ℝ l (p.inletProfile 1) x‖ := norm_nonneg _
      have hα0 : 0 ≤ ‖α 0‖ := norm_nonneg _
      have hα1 : 0 ≤ ‖α 1‖ := norm_nonneg _
      calc ‖α 0‖ * ‖iteratedFDeriv ℝ l (p.inletProfile 0) x‖ +
            ‖α 1‖ * ‖iteratedFDeriv ℝ l (p.inletProfile 1) x‖
          ≤ ‖α‖ * J + ‖α‖ * J :=
            add_le_add (mul_le_mul ha0 b0 hn0 (norm_nonneg _))
              (mul_le_mul ha1 b1 hn1 (norm_nonneg _))
        _ = 2 * ‖α‖ * J := by ring
    have he0 : ‖e x‖ ≤ 2 * ‖α‖ * J := by
      have := hjet 0 (by norm_num)
      rwa [norm_iteratedFDeriv_zero] at this
    have hsum : ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l e x‖ ≤ 4 * ‖α‖ * J := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      have := hjet 0 (by norm_num)
      have := hjet 1 (by norm_num)
      linarith
    -- the gradient of the lift
    have hjl := HL e hecd x
    have hgq := gradProfileQuantity_le hεpos hε1 e x hs0.le
    have hlin : 1 + |x.1| + |x.2.2| ≤ (1 + p.H) * (1 + |x.2.2|) := by
      rw [abs_of_pos hs0]
      have : 0 ≤ |x.2.2| := abs_nonneg _
      nlinarith
    have hαJ : 0 ≤ 4 * ‖α‖ * J := by positivity
    have hcj : UnforcedLeray.Short.IIb.chartJet e x ≤
        KL * ((1 + p.H) * (1 + |x.2.2|)) * (4 * ‖α‖ * J) := by
      have : 0 ≤ ‖Axi.dS e x‖ := norm_nonneg _
      calc UnforcedLeray.Short.IIb.chartJet e x
          ≤ KL * (1 + |x.1| + |x.2.2|) *
              ∑ l ∈ Finset.range 2, ‖iteratedFDeriv ℝ l e x‖ := by linarith
        _ ≤ KL * ((1 + p.H) * (1 + |x.2.2|)) * (4 * ‖α‖ * J) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hlin hKL.le) hsum
              (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    set A1 : ℝ := 2 * x.1 * (KL * ((1 + p.H) * (1 + |x.2.2|)) * (4 * ‖α‖ * J)) with hA1
    have hA10 : 0 ≤ A1 := by
      rw [hA1]
      have hH1 : 0 ≤ (1 + p.H) * (1 + |x.2.2|) :=
        mul_nonneg (by linarith) (by have := abs_nonneg x.2.2; linarith)
      exact mul_nonneg (mul_nonneg (by norm_num) hs0.le)
        (mul_nonneg (mul_nonneg hKL.le hH1) hαJ)
    have hfd : ‖fderiv ℝ (Nv p.R e τ) y‖ ≤ A1 :=
      hgrad.trans (hgq.trans (mul_le_mul_of_nonneg_left hcj (by linarith)))
    have hnv' : ‖Nv p.R e τ y‖ ≤ √x.1 * (2 * ‖α‖ * J) := by
      rw [hnv]
      exact mul_le_mul_of_nonneg_left he0 (Real.sqrt_nonneg _)
    have hE2 : E * E ≤ E := by nlinarith
    calc ‖fderiv ℝ (Nv p.R e τ) y (Nv p.R e τ y)‖
        ≤ ‖fderiv ℝ (Nv p.R e τ) y‖ * ‖Nv p.R e τ y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ A1 * (√x.1 * (2 * ‖α‖ * J)) := mul_le_mul hfd hnv' (norm_nonneg _) hA10
      _ = 16 * KL * CJ ^ 2 * (1 + p.H) * ((p.ν ^ kJ)⁻¹ * (p.ν ^ kJ)⁻¹) * ‖α‖ ^ 2 *
            (√x.1 * x.1) * ((1 + |x.2.2|) * (E * E)) := by
          rw [hA1, ← hJ]; ring
      _ ≤ 16 * KL * CJ ^ 2 * (1 + p.H) * ((p.ν ^ kJ)⁻¹ * (p.ν ^ kJ)⁻¹) * ‖α‖ ^ 2 *
            (√x.1 * x.1) * ((1 + |x.2.2|) * E) := by
          have hH1 : 0 ≤ 1 + p.H := (add_pos one_pos hHpos).le
          have hνk : 0 ≤ (p.ν ^ kJ)⁻¹ := inv_nonneg.2 (pow_nonneg hνpos.le _)
          have hsx : 0 ≤ √x.1 * x.1 := mul_nonneg (Real.sqrt_nonneg _) hs0.le
          have hK0 : 0 ≤ 16 * KL * CJ ^ 2 := by positivity
          have h1 : 0 ≤ 16 * KL * CJ ^ 2 * (1 + p.H) * ((p.ν ^ kJ)⁻¹ * (p.ν ^ kJ)⁻¹) *
              ‖α‖ ^ 2 * (√x.1 * x.1) :=
            mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK0 hH1) (mul_nonneg hνk hνk))
              (sq_nonneg _)) hsx
          have h2 : 0 ≤ 1 + |x.2.2| := add_nonneg zero_le_one (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE2 h2) h1
      _ = _ := by
          rw [sqrt_mul_self_eq_rpow hs0.le, pow_add, mul_inv, pow_one]
  · have hz : e x = 0 := by
      have hz0 := (HV' 0).2 x (not_le.1 hle)
      have hz1 := (HV' 1).2 x (not_le.1 hle)
      simp [he, hz0, hz1]
    have hN : Nv p.R e τ y = 0 := by
      rw [hNv, hz, map_zero, smul_zero]
    rw [hN, map_zero, norm_zero]
    exact ringEnv_nonneg hM _ _

end UnforcedLeray.Short.PartIIIb.Concrete.ES326Inlet
