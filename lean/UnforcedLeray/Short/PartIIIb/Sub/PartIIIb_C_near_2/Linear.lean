import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.AEInvariant
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Agree
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_5
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin

/-!
# `PartIII-b:C/near/2/Linear` (`FreeStressPinLinear`, source 3427-3440)

Real-linear closure of the pin.  Solutions are closed under real scalar multiples (`lin_smul_sol`,
proved from the linearity of every clause of `IsCausalEnergySolution`), differences
(`IIIa.causalSolSub`), a.e. changes of the force on `ageμ c (-1/2)` (`freeSolAEInvariant`), and the
meridional block of `zsum` is a.e. linear in `F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem lin_sq_vnorm2 (a : Fin 2 → ℂ) : UnforcedLeray.Short.IIIa.vnorm2 a ^ 2 = ∑ i : Fin 2, ‖a i‖ ^ 2 := by
  unfold UnforcedLeray.Short.IIIa.vnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]

theorem lin_sq_tnorm2 (T : Fin 2 → Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.tnorm2 T ^ 2 = ∑ i : Fin 2, ∑ j : Fin 2, ‖T i j‖ ^ 2 := by
  unfold UnforcedLeray.Short.IIIa.tnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]

theorem lin_sq_vnorm2_smul (r : ℝ) (a : Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.vnorm2 (fun i => (r : ℂ) * a i) ^ 2 =
      r ^ 2 * UnforcedLeray.Short.IIIa.vnorm2 a ^ 2 := by
  rw [lin_sq_vnorm2, lin_sq_vnorm2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem lin_sq_tnorm2_smul (r : ℝ) (T : Fin 2 → Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.tnorm2 (fun i j => (r : ℂ) * T i j) ^ 2 =
      r ^ 2 * UnforcedLeray.Short.IIIa.tnorm2 T ^ 2 := by
  rw [lin_sq_tnorm2, lin_sq_tnorm2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem lin_pair (r : ℝ) (a : Fin 2 → ℂ) (T : Fin 2 → Fin 2 → ℂ) :
    UnforcedLeray.Short.IIIa.vnorm2 (fun i => (r : ℂ) * a i) ^ 2 +
        UnforcedLeray.Short.IIIa.tnorm2 (fun i j => (r : ℂ) * T i j) ^ 2 =
      r ^ 2 * (UnforcedLeray.Short.IIIa.vnorm2 a ^ 2 + UnforcedLeray.Short.IIIa.tnorm2 T ^ 2) := by
  rw [lin_sq_vnorm2_smul, lin_sq_tnorm2_smul]
  ring

/-- The flat integrand is homogeneous of degree one in `(F, b)`. -/
theorem lin_flat_smul (ν : ℝ) (μ : ℂ) (vel : ℝ → ℝ × ℝ → Fin 2 → ℝ) (r : ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel (fun p i j => (r : ℂ) * F p i j)
        (fun p i => (r : ℂ) * b p i) Φ p
      = (r : ℂ) * UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel F b Φ p := by
  have key : ∀ i : Fin 2,
      (∑ j : Fin 2, ((r : ℂ) * F p i j - ((vel p.1 p.2 i : ℂ) * ((r : ℂ) * b p j) +
          ((r : ℂ) * b p i) * (vel p.1 p.2 j : ℂ))) * (UnforcedLeray.Short.IIIa.flatGrad Φ p.1 p.2 i j : ℂ))
        = (r : ℂ) * ∑ j : Fin 2, (F p i j - ((vel p.1 p.2 i : ℂ) * b p j +
          b p i * (vel p.1 p.2 j : ℂ))) * (UnforcedLeray.Short.IIIa.flatGrad Φ p.1 p.2 i j : ℂ) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp only [UnforcedLeray.Short.IIIa.flatIntegrand]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key i]
  ring

/-- Real scalar multiples of causal energy solutions are causal energy solutions. -/
theorem lin_smul_sol {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ} (r : ℝ)
    {F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ} {b : ℝ × (ℝ × ℝ) → Fin 2 → ℂ}
    {G : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ}
    (h : UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ vel F b G) :
    UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν μ vel (fun p i j => (r : ℂ) * F p i j)
      (fun p i => (r : ℂ) * b p i) (fun p i j => (r : ℂ) * G p i j) := by
  refine
    { measurable := fun i => (h.measurable i).const_mul (r : ℂ)
      gradMeasurable := fun i j => (h.gradMeasurable i j).const_mul (r : ℂ)
      energyLoc := ?_
      zeroEntrance := ?_
      divFree := ?_
      weakGrad := ?_
      integrable := ?_
      weak := ?_ }
  · intro s₁ s₂ h1 h12
    have hfin := h.energyLoc s₁ s₂ h1 h12
    have e : (∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
        ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (fun i => (r : ℂ) * b p i) ^ 2 +
          UnforcedLeray.Short.IIIa.tnorm2 (fun i j => (r : ℂ) * G p i j) ^ 2))
        = ENNReal.ofReal (r ^ 2) * ∫⁻ p in Icc s₁ s₂ ×ˢ UnforcedLeray.B0579.cell c,
          ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2 +
            UnforcedLeray.Short.IIIa.tnorm2 (G p) ^ 2) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun p => ?_
      rw [lin_pair, ENNReal.ofReal_mul (sq_nonneg r)]
    rw [e]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  · obtain ⟨δ, hδ, hfin⟩ := h.zeroEntrance
    refine ⟨δ, hδ, ?_⟩
    have e : (∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (fun i => (r : ℂ) * b p i) ^ 2)
        ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)))
        = ENNReal.ofReal (r ^ 2) * ∫⁻ p, ENNReal.ofReal (UnforcedLeray.Short.IIIa.vnorm2 (b p) ^ 2)
            ∂((ageμ c (-3 / 2)).restrict (Ioo 0 δ ×ˢ univ)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun p => ?_
      rw [lin_sq_vnorm2_smul, ENNReal.ofReal_mul (sq_nonneg r)]
    rw [e]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  · intro s hs ψ hψ
    have h0 := h.divFree s hs ψ hψ
    have e : (∫ x in UnforcedLeray.B0579.cell c,
        ((r : ℂ) * b (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
          (r : ℂ) * b (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)))
        = (r : ℂ) * ∫ x in UnforcedLeray.B0579.cell c,
          (b (s, x) 0 * (UnforcedLeray.B0579.pd 0 ψ x : ℂ) +
            b (s, x) 1 * (UnforcedLeray.B0579.pd 1 ψ x : ℂ)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [e, h0, mul_zero]
  · intro s hs i j
    exact UnforcedLeray.Short.IIIa.hasWeakCellDerivC_smul c j _ _ (r : ℂ) (h.weakGrad s hs i j)
  · intro Φ hΦ
    have e : UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel (fun p i j => (r : ℂ) * F p i j)
        (fun p i => (r : ℂ) * b p i) Φ = fun p => (r : ℂ) *
          UnforcedLeray.Short.IIIa.flatIntegrand ν μ vel F b Φ p :=
      funext fun p => lin_flat_smul ν μ vel r F b Φ p
    rw [e]
    exact (h.integrable Φ hΦ).const_mul (r : ℂ)
  · intro Φ hΦ
    simp only [lin_flat_smul]
    rw [integral_const_mul, h.weak Φ hΦ, mul_zero]

theorem lin_nsSym_add (T T' : UnforcedLeray.Short.PartIIIb.Concrete.Ten3) (r : ℝ) (i j : Fin 2) :
    nsSym (T + r • T') (merIdx i) (merIdx j) =
      nsSym T (merIdx i) (merIdx j) + r * nsSym T' (merIdx i) (merIdx j) := by
  fin_cases i <;> fin_cases j <;>
    simp [nsSym, symRZ, merIdx, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;> ring

/-- The sum of the two components of `F + r F'` is a.e. the linear combination. -/
theorem lin_zsum_ae {c mZ ρb : ℝ} (hρ : 0 < ρb)
    (F F' : UnforcedLeray.Short.PartIIIb.Concrete.Zsp c mZ ρb) (r : ℝ) :
    ∀ᵐ p ∂ageμ c (-1 / 2), zsum (F + r • F') p = zsum F p + r • zsum F' p := by
  have hfst : (F + r • F').fst = F.fst + r • F'.fst := by
    rw [WithLp.add_fst, WithLp.smul_fst]
  have hsnd : (F + r • F').snd = F.snd + r • F'.snd := by
    rw [WithLp.add_snd, WithLp.smul_snd]
  have A1 : ∀ᵐ p ∂ageμ c (-1 / 2), (F.fst + r • F'.fst) p = F.fst p + r • F'.fst p := by
    rw [← ae_z1Measure c mZ]
    filter_upwards [Lp.coeFn_add F.fst (r • F'.fst), Lp.coeFn_smul r F'.fst] with p h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply]
  have A2 : ∀ᵐ p ∂ageμ c (-1 / 2), (F.snd + r • F'.snd) p = F.snd p + r • F'.snd p := by
    rw [← ae_htRhoMeasure hρ]
    filter_upwards [Lp.coeFn_add F.snd (r • F'.snd), Lp.coeFn_smul r F'.snd] with p h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply]
  filter_upwards [A1, A2] with p h1 h2
  simp only [zsum, hfst, hsnd]
  rw [h1, h2, smul_add]
  abel

theorem freeStressPinLinear_proof : FreeStressPinLinear := by
  intro P hP Kset hK hKs
  refine ⟨1, one_pos, ?_⟩
  intro ν hν c hc μ hμ mZ ρb hmZ hρb F F' h h' r hF hF'
  unfold FreePin at hF hF' ⊢
  obtain ⟨b, G, hb, hsol⟩ := hF
  obtain ⟨b', G', hb', hsol'⟩ := hF'
  have hc0 : 0 < c := by
    rw [hc]
    exact inv_pos.2 (pow_pos hν.1 2)
  have hs2 := lin_smul_sol (-r) hsol'
  have hs3 := UnforcedLeray.Short.IIIa.causalSolSub c ν (μ : ℂ) (fun _ _ _ => 0) _ _ _ _ _ _ hsol hs2
  have hsum : UnforcedLeray.Short.IIIa.IsCausalEnergySolution c ν (μ : ℂ) (fun _ _ _ => 0)
      (fun p i j => merBlockC (zsum F) p i j + (r : ℂ) * merBlockC (zsum F') p i j)
      (fun p i => b p i + (r : ℂ) * b' p i)
      (fun p i j => G p i j + (r : ℂ) * G' p i j) := by
    have e1 : (fun p i j => merBlockC (zsum F) p i j + (r : ℂ) * merBlockC (zsum F') p i j)
        = (fun p i j => merBlockC (zsum F) p i j - ((-r : ℝ) : ℂ) * merBlockC (zsum F') p i j) := by
      funext p i j
      push_cast
      ring
    have e2 : (fun p i => b p i + (r : ℂ) * b' p i)
        = (fun p i => b p i - ((-r : ℝ) : ℂ) * b' p i) := by
      funext p i
      push_cast
      ring
    have e3 : (fun p i j => G p i j + (r : ℂ) * G' p i j)
        = (fun p i j => G p i j - ((-r : ℝ) : ℂ) * G' p i j) := by
      funext p i j
      push_cast
      ring
    rw [e1, e2, e3]
    exact hs3
  have hae : (fun p i j => merBlockC (zsum F) p i j + (r : ℂ) * merBlockC (zsum F') p i j)
      =ᵐ[ageμ c (-1 / 2)] merBlockC (zsum (F + r • F')) := by
    filter_upwards [lin_zsum_ae hρb F F' r] with p hp
    funext i j
    simp only [merBlockC, hp]
    rw [lin_nsSym_add]
    push_cast
    ring
  have hfin := UnforcedLeray.Short.PartIIIb.NearInst.Delta.freeSolAEInvariant c ν (μ : ℂ) hc0 _ _ _ _
    hsum hae
  refine ⟨fun p i => b p i + (r : ℂ) * b' p i, fun p i j => G p i j + (r : ℂ) * G' p i j, ?_, hfin⟩
  have hh := Lp.coeFn_add h (r • h')
  have hh2 := Lp.coeFn_smul r h'
  filter_upwards [hb, hb', hh, hh2] with p h1 h2 h3 h4
  funext i
  simp only [h1, h2, h3, h4, velC, Pi.add_apply, Pi.smul_apply, WithLp.ofLp_add,
    WithLp.ofLp_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_add,
    Complex.ofReal_mul]

end UnforcedLeray.Short.PartIIIb.NearInst
