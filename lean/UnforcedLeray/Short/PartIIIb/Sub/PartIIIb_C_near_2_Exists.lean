import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2.Shared
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2.Conj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2_Unique

/-!
# `PartIII-b:C/near/2/Exists` (`FreeStressPinExists`, source 3427-3440), decomposed

`freeStressPinExists_of (hU : FreeCausalExistsUnique) : FreeStressPinExists`: existence from the
free causal solver, reality of the solution by conjugation closure (`Conj.lean`) and uniqueness,
membership in `H` from the energy bound and `g ≤ e^{|γ|/ν}`.  The unconditional target is
`freeStressPinExists_of freeCausalExistsUnique` in `Sub/PartIII-b_C_near_2/Exists.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Blueprint.Planar

theorem vnorm2_real_smul (r : ℝ) (a : Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.vnorm2 (r • a) = |r| * UnforcedLeray.Short.IIIa.vnorm2 a := by
  unfold UnforcedLeray.Short.IIIa.vnorm2
  have : ∑ i : Fin 2, ‖(r • a) i‖ ^ 2 = r ^ 2 * ∑ i : Fin 2, ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem conj_merBlockC (T : Chart → Ten3) (p : Chart) (i j : Fin 2) :
    conj (merBlockC T p i j) = merBlockC T p i j := by
  simp [merBlockC, Complex.conj_ofReal]

theorem norm_re_le_vnorm2 (a : Fin 2 → ℂ) :
    ‖(WithLp.toLp 2 (fun i : Fin 2 => (a i).re) : EuclideanSpace ℝ (Fin 2))‖ ≤
      UnforcedLeray.Short.IIIa.vnorm2 a := by
  rw [EuclideanSpace.norm_eq]
  unfold UnforcedLeray.Short.IIIa.vnorm2
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← sq_abs (a i).re]
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2

theorem freeStressPinExists_of (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) :
    FreeStressPinExists := by
  intro P hP Kset hK hKs
  obtain ⟨ν₀, hν₀, hex⟩ := hU P hP _ (admissible_ofReal hK hKs)
  refine ⟨ν₀, hν₀, ?_⟩
  intro ν hν c hc μ hμ mZ ρb hmZ hρb F
  have hc' : ν ^ (-2 : ℝ) = c := by
    rw [hc, Real.rpow_neg hν.1.le, Real.rpow_two]
  have hcpos : 0 < c := by rw [hc]; exact inv_pos.2 (pow_pos hν.1 2)
  have hexμ := hex ν hν (μ : ℂ) ⟨μ, hμ, rfl⟩
  simp only [hc'] at hexμ
  set γ := P.eigenvalue.re with hγ
  obtain ⟨Fm, hsym, hmeas, hae, hnorm⟩ := sourceMeasRepFin c mZ ρb γ ν hν.1 hcpos
    hmZ hρb ((gainEquiv c mZ ρb γ hν.1).symm F)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hae
  obtain ⟨b₁, G₁, hs1, hH, -, huniq⟩ := hexμ Fm hsym hmeas hnorm
  -- reality of `b₁`
  have hconjF : (fun p i j => conj (Fm p i j)) =ᵐ[ageμ c (-1 / 2)] Fm := by
    filter_upwards [hae] with p hp
    funext i j
    rw [hp, conj_merBlockC]
  have hcs := conj_causal_sol hs1
  have hcs' := freeSolAEInvariant c ν (μ : ℂ) hcpos _ Fm _ _ hcs hconjF
  have e1 : (fun p i => conj (b₁ p i)) =ᵐ[volume.restrict (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c)] b₁ :=
    huniq _ _ hcs'
  have e2 := (ageMeasureAC c (-3 / 2) hcpos).ae_le e1
  have hre : ∀ᵐ p ∂ageμ c (-3 / 2), ∀ i, (((b₁ p i).re : ℝ) : ℂ) = b₁ p i := by
    filter_upwards [e2] with p hp i
    exact Complex.conj_eq_iff_re.1 (congrFun hp i)
  -- the real field
  set bR : Chart → EuclideanSpace ℝ (Fin 2) :=
    fun p => WithLp.toLp 2 (fun i : Fin 2 => (b₁ p i).re) with hbR
  have hmeasR : Measurable bR := by
    have h0 : Measurable fun p i => (b₁ p i).re :=
      measurable_pi_lambda _ fun i => Complex.measurable_re.comp (hs1.measurable i)
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp h0
  have hge : ∀ᵐ p ∂ageμ c (-3 / 2), ‖bR p‖ ≤
      Real.exp (|γ| / ν) * UnforcedLeray.Short.IIIa.vnorm2
        (UnforcedLeray.Short.IIIa.gainConj γ ν b₁ p) := by
    filter_upwards [UnforcedLeray.Axi.ae_ageμ_mem hcpos (-3 / 2)] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hgf : gainFun γ ν p = UnforcedLeray.Short.IIIa.gainG γ ν p.1 := by
      unfold gainFun; rw [max_eq_left hp1.le]
    have hgpos : 0 < UnforcedLeray.Short.IIIa.gainG γ ν p.1 := Real.exp_pos _
    have hgle : UnforcedLeray.Short.IIIa.gainG γ ν p.1 ≤ Real.exp (|γ| / ν) := by
      have := gainFun_le (γ := γ) hν.1 p
      rw [hgf, abs_of_pos hgpos] at this
      exact this
    have hv : UnforcedLeray.Short.IIIa.vnorm2 (b₁ p) =
        UnforcedLeray.Short.IIIa.gainG γ ν p.1 *
          UnforcedLeray.Short.IIIa.vnorm2 (UnforcedLeray.Short.IIIa.gainConj γ ν b₁ p) := by
      unfold UnforcedLeray.Short.IIIa.gainConj
      rw [vnorm2_real_smul, abs_of_pos (inv_pos.2 hgpos), ← mul_assoc, mul_inv_cancel₀ hgpos.ne',
        one_mul]
    calc ‖bR p‖ ≤ UnforcedLeray.Short.IIIa.vnorm2 (b₁ p) := norm_re_le_vnorm2 _
      _ = _ := hv
      _ ≤ _ := mul_le_mul_of_nonneg_right hgle (Real.sqrt_nonneg _)
  have hfin : UnforcedLeray.Short.IIIa.hCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν b₁) < ⊤ :=
    hH.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hnorm)
  have hmem : MemLp bR 2 (ageμ c (-3 / 2)) := by
    refine ⟨hmeasR.aestronglyMeasurable, ?_⟩
    calc eLpNorm bR 2 (ageμ c (-3 / 2))
        ≤ eLpNorm (fun p => Real.exp (|γ| / ν) * UnforcedLeray.Short.IIIa.vnorm2
            (UnforcedLeray.Short.IIIa.gainConj γ ν b₁ p)) 2 (ageμ c (-3 / 2)) := by
          apply eLpNorm_mono_ae
          filter_upwards [hge] with p hp
          have h0 : 0 ≤ Real.exp (|γ| / ν) * UnforcedLeray.Short.IIIa.vnorm2
              (UnforcedLeray.Short.IIIa.gainConj γ ν b₁ p) :=
            mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
          rw [Real.norm_of_nonneg h0]
          exact hp
      _ = ENNReal.ofReal (Real.exp (|γ| / ν)) *
          UnforcedLeray.Short.IIIa.hCalNorm c (UnforcedLeray.Short.IIIa.gainConj γ ν b₁) := by
          unfold UnforcedLeray.Short.IIIa.hCalNorm
          rw [show (fun p => Real.exp (|γ| / ν) * UnforcedLeray.Short.IIIa.vnorm2
              (UnforcedLeray.Short.IIIa.gainConj γ ν b₁ p)) =
              Real.exp (|γ| / ν) • (fun p => UnforcedLeray.Short.IIIa.vnorm2
              (UnforcedLeray.Short.IIIa.gainConj γ ν b₁ p)) from rfl, eLpNorm_const_smul]
          simp [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  refine ⟨hmem.toLp bR, b₁, G₁, ?_, ?_⟩
  · filter_upwards [hre, hmem.coeFn_toLp] with p hp hq
    funext i
    have h1 : ((hmem.toLp bR : Chart → EuclideanSpace ℝ (Fin 2)) p) i = (b₁ p i).re := by
      rw [hq]
    simp only [velC]
    rw [h1]
    exact (hp i).symm
  · exact freeSolAEInvariant c ν (μ : ℂ) hcpos _ _ _ _ hs1 hae

end UnforcedLeray.Short.PartIIIb.NearInst
