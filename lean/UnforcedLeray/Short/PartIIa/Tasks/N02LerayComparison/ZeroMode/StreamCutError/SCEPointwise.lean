import UnforcedLeray.Short.PartIIa.Sub.N02_3_8
import UnforcedLeray.Short.PartIIa.Sub.N02_5.Cond

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Twin of the `GCEPointwise` step with index `0` (`f_r`) in place of `1` (`f_z`).

With `g = f_r`, `Φ = zPrimC g`, `Φ_S = zPrimC (opS g)` (`ZeroPrimComm`), `χ = zChi (η/L)`,
`ψ = zCut L (-Φ)`: `pdQ ψ = 0` (q-invariance), `pdEta ψ = -χ g - Φ χ'/L`,
`opS ψ = -χ Φ_S`, and `errS = (g + pdEta ψ, ε (opK ψ - ψ))` componentwise. The three
estimates `|1-χ| ≤ |η|/L`, `|χ'| ≤ M` (zero for `|η| > 2L`), `χ = 0` for `|η| ≥ 2L` give the bound
`L⁻¹ |η| |g| + M L⁻¹ W + ε(2 W_S + |η||g| + 2M W + W)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

open ZeroGradCutErrorAux ZeroStreamCutErrorAux

namespace SCEPtAux

theorem zChi_contDiff : ContDiff ℝ ∞ zChi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

theorem zChi_zero_of_two_le {t : ℝ} (ht : 2 ≤ |t|) : zChi t = 0 := by
  unfold zChi
  apply Real.smoothTransition.zero_of_nonpos
  nlinarith [sq_abs t, abs_nonneg t]

theorem zChi_nonneg (t : ℝ) : 0 ≤ zChi t := Real.smoothTransition.nonneg _

theorem zChi_le_one (t : ℝ) : zChi t ≤ 1 := Real.smoothTransition.le_one _

theorem zChi_one_of_abs_le {t : ℝ} (ht : |t| ≤ 1) : zChi t = 1 := by
  unfold zChi
  apply Real.smoothTransition.one_of_one_le
  nlinarith [sq_abs t, abs_nonneg t]

theorem zChi_deriv_zero_of {t : ℝ} (ht : 2 < |t|) : deriv zChi t = 0 := by
  have hev : ∀ᶠ s in 𝓝 t, 2 < |s| := (isOpen_lt continuous_const continuous_abs).mem_nhds ht
  have h2 : zChi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with s hs
    exact zChi_zero_of_two_le hs.le
  rw [h2.deriv_eq]
  simp

theorem one_sub_chi_le (η L : ℝ) (hL : 0 < L) : |1 - zChi (η / L)| ≤ |η| / L := by
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - zChi (η / L) by linarith [zChi_le_one (η / L)])]
  by_cases h : |η| ≤ L
  · have hη : |η / L| ≤ 1 := by
      rw [abs_div, abs_of_pos hL]
      exact (div_le_one hL).2 h
    rw [zChi_one_of_abs_le hη, sub_self]
    positivity
  · push_neg at h
    have h1 : 1 ≤ |η| / L := by
      rw [le_div_iff₀ hL]
      linarith
    linarith [zChi_nonneg (η / L)]

theorem winP_of_le (L : ℝ) (g : Profile → ℂ) (p : Profile) (h : |p.2.2| ≤ 2 * L) :
    winP L g p = ‖zPrimC g p‖ := by
  unfold winP
  simp [Set.indicator_apply, h]

theorem winP_of_gt (L : ℝ) (g : Profile → ℂ) (p : Profile) (h : 2 * L < |p.2.2|) :
    winP L g p = 0 := by
  unfold winP
  have h' : ¬ (|p.2.2| ≤ 2 * L) := not_le.2 h
  simp [Set.indicator_apply, h']

theorem psi_contDiff {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (L : ℝ) :
    ContDiff ℝ ∞ (fun p : Profile => ((zChi (p.2.2 / L) : ℝ) : ℂ) * (-Φ p)) := by
  have h1 : ContDiff ℝ ∞ (fun p : Profile => zChi (p.2.2 / L)) :=
    zChi_contDiff.comp ((contDiff_snd.comp contDiff_snd).div_const L)
  have h2 : ContDiff ℝ ∞ (fun p : Profile => ((zChi (p.2.2 / L) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact h2.mul hΦ.neg

/-- A function constant along the `q`-direction has zero `q`-derivative. -/
theorem cut_contDiff {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) (L : ℝ) :
    ContDiff ℝ ∞ (fun q : Profile => ((zChi (q.2.2 / L) : ℝ) : ℂ) * F q) := by
  have h1 : ContDiff ℝ ∞ (fun p : Profile => zChi (p.2.2 / L)) :=
    zChi_contDiff.comp ((contDiff_snd.comp contDiff_snd).div_const L)
  have h2 : ContDiff ℝ ∞ (fun p : Profile => ((zChi (p.2.2 / L) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1
  exact h2.mul hF

theorem pdQ_zero_of_qInv {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F)
    (hq : ∀ s q q' η : ℝ, F (s, q, η) = F (s, q', η)) (p : Profile) : pdQ F p = 0 := by
  have hγ : HasDerivAt (fun t : ℝ => p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const ((0 : ℝ), (1 : ℝ), (0 : ℝ))).const_add p
  have hFd : HasFDerivAt F (fderiv ℝ F p)
      ((fun t : ℝ => p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) 0) := by
    simpa using (hF.differentiable (by simp) p).hasFDerivAt
  have hcomp : HasDerivAt (F ∘ fun t : ℝ => p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)))
      (fderiv ℝ F p ((0 : ℝ), (1 : ℝ), (0 : ℝ))) 0 := hFd.comp_hasDerivAt 0 hγ
  have hconst : (F ∘ fun t : ℝ => p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) = fun _ => F p := by
    funext t
    have hpt : p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = (p.1, p.2.1 + t, p.2.2) := by
      simp [Prod.ext_iff]
    show F (p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) = F p
    rw [hpt]
    exact hq p.1 (p.2.1 + t) p.2.1 p.2.2
  have h2 : HasDerivAt (F ∘ fun t : ℝ => p + t • ((0 : ℝ), (1 : ℝ), (0 : ℝ))) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const _ _
  have h3 := hcomp.unique h2
  unfold pdQ
  exact h3

/-- Product rule for the `η`-cutoff `χ(η/L)` times a smooth `F`, in direction `v`. -/
theorem cut_fderiv {F : Profile → ℂ} (hF : ContDiff ℝ ∞ F) (L : ℝ) (p v : Profile) :
    fderiv ℝ (fun q : Profile => ((zChi (q.2.2 / L) : ℝ) : ℂ) * F q) p v =
      ((zChi (p.2.2 / L) : ℝ) : ℂ) * fderiv ℝ F p v +
        F p * ((deriv zChi (p.2.2 / L) * (v.2.2 / L) : ℝ) : ℂ) := by
  have hγ : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add p
  have hFd : HasFDerivAt F (fderiv ℝ F p) ((fun t : ℝ => p + t • v) 0) := by
    simpa using (hF.differentiable (by simp) p).hasFDerivAt
  have hd : HasDerivAt (fun t : ℝ => F (p + t • v)) (fderiv ℝ F p v) 0 :=
    hFd.comp_hasDerivAt 0 hγ
  have hin : HasDerivAt (fun t : ℝ => (p.2.2 + t * v.2.2) / L) (v.2.2 / L) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).mul_const v.2.2).const_add p.2.2).div_const L
    simpa using h
  have hz : HasDerivAt zChi (deriv zChi (p.2.2 / L)) ((p.2.2 + 0 * v.2.2) / L) := by
    simpa using (zChi_contDiff.differentiable (by simp) (p.2.2 / L)).hasDerivAt
  have hζ := hz.comp 0 hin
  have hc := hζ.ofReal_comp
  have hprod := hc.mul hd
  have hψ : HasFDerivAt (fun q : Profile => ((zChi (q.2.2 / L) : ℝ) : ℂ) * F q)
      (fderiv ℝ (fun q : Profile => ((zChi (q.2.2 / L) : ℝ) : ℂ) * F q) p)
      ((fun t : ℝ => p + t • v) 0) := by
    simpa using ((cut_contDiff hF L).differentiable (by simp) p).hasFDerivAt
  have hu := hψ.comp_hasDerivAt 0 hγ
  have key := hu.unique hprod
  simp only [Function.comp_apply, zero_mul, add_zero, zero_smul] at key
  rw [key]
  ring

theorem norm_two_le (x : MeridC) : ‖x‖ ≤ ‖x 0‖ + ‖x 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg (x 0), norm_nonneg (x 1)]


end SCEPtAux

open SCEPtAux in
/-- **Target `PartII-a:N02/3/8/1`**: the pointwise bound on the stream error (tex 1728-1735). -/
theorem sCEPointwise : UnforcedLeray.Short.PartIIa.ZeroStreamCutErrorAux.SCEPointwise := by
  unfold ZeroStreamCutErrorAux.SCEPointwise
  intro hS hK M c ε L f hM hε hL hc hf hq p
  unfold QInvariant at hq
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hg0S : ContDiff ℝ ∞ (fun r => f r 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  have hb0 : ∀ q : Profile, (fun r => f r 0) q ≠ 0 → q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L0 :=
    fun q hq' => hb q (fun h => hq' (by simp [h]))
  obtain ⟨hΦS, hΦE⟩ := hS (fun r => f r 0) hg0S ⟨s0, s1, L0, hs0, hb0⟩
  have hComm := hK (fun r => f r 0) hg0S ⟨s0, s1, L0, hs0, hb0⟩
  have hq0 : ∀ s q q' η : ℝ, zPrimC (fun r => f r 0) (s, q, η)
      = zPrimC (fun r => f r 0) (s, q', η) := by
    intro s q q' η
    have h1 : ∀ t : ℝ, f (s, q, t) 0 = f (s, q', t) 0 := fun t => by rw [hq s q q' t]
    unfold zPrimC
    simp only [h1]
  have hF : ContDiff ℝ ∞ (fun q => -zPrimC (fun r => f r 0) q) := hΦS.neg
  have hFq : ∀ s q q' η : ℝ, (fun q => -zPrimC (fun r => f r 0) q) (s, q, η)
      = (fun q => -zPrimC (fun r => f r 0) q) (s, q', η) := by
    intro s q q' η
    simp only [hq0 s q q' η]
  have hF3 : fderiv ℝ (fun q => -zPrimC (fun r => f r 0) q) p (0, 1, 0) = 0 := by
    have h := pdQ_zero_of_qInv hF hFq p
    unfold pdQ at h
    exact h
  have hF1 : fderiv ℝ (fun q => -zPrimC (fun r => f r 0) q) p (0, 0, 1) = -(f p 0) := by
    have h1 : fderiv ℝ (zPrimC (fun r => f r 0)) p (0, 0, 1) = f p 0 := hΦE p
    show fderiv ℝ (-zPrimC (fun r => f r 0)) p (0, 0, 1) = -(f p 0)
    rw [fderiv_neg, ContinuousLinearMap.neg_apply, h1]
  have hF2 : fderiv ℝ (fun q => -zPrimC (fun r => f r 0) q) p (1, 0, 0)
      = -(fderiv ℝ (zPrimC (fun r => f r 0)) p (1, 0, 0)) := by
    show fderiv ℝ (-zPrimC (fun r => f r 0)) p (1, 0, 0) = _
    rw [fderiv_neg, ContinuousLinearMap.neg_apply]
  have hdiff : ∀ v : Profile, fderiv ℝ (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p v =
      ((zChi (p.2.2 / L) : ℝ) : ℂ) * fderiv ℝ (fun q => -zPrimC (fun r => f r 0) q) p v +
        (-zPrimC (fun r => f r 0) p) * ((deriv zChi (p.2.2 / L) * (v.2.2 / L) : ℝ) : ℂ) :=
    fun v => cut_fderiv hF L p v
  have hdEta : pdEta (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p =
      ((zChi (p.2.2 / L) : ℝ) : ℂ) * (-(f p 0)) +
        (-zPrimC (fun r => f r 0) p) * ((deriv zChi (p.2.2 / L) * (1 / L) : ℝ) : ℂ) := by
    unfold pdEta
    rw [hdiff (0, 0, 1), hF1]
  have hdQ : pdQ (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p = 0 := by
    unfold pdQ
    rw [hdiff (0, 1, 0), hF3]
    simp
  have hdS : pdS (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p =
      ((zChi (p.2.2 / L) : ℝ) : ℂ) * (-(fderiv ℝ (zPrimC (fun r => f r 0)) p (1, 0, 0))) := by
    unfold pdS
    rw [hdiff (1, 0, 0), hF2]
    simp
  have hOS : p.1 • fderiv ℝ (zPrimC (fun r => f r 0)) p (1, 0, 0)
      = zPrimC (opS (fun r => f r 0)) p := congrFun hComm p
  have hSψ : opS (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p
      = ((zChi (p.2.2 / L) : ℝ) : ℂ) * (-(zPrimC (opS (fun r => f r 0)) p)) := by
    show p.1 • pdS (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p = _
    rw [hdS, ← hOS]
    simp only [Complex.real_smul]
    ring
  have hKψ : opK (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p
      = (2 : ℝ) • (((zChi (p.2.2 / L) : ℝ) : ℂ) * (-(zPrimC (opS (fun r => f r 0)) p))) +
        p.2.2 • (((zChi (p.2.2 / L) : ℝ) : ℂ) * (-(f p 0)) +
          (-zPrimC (fun r => f r 0) p) * ((deriv zChi (p.2.2 / L) * (1 / L) : ℝ) : ℂ)) := by
    unfold opK
    rw [hSψ, hdEta]
  have herr0 : (errS ε L f p) 0
      = f p 0 + pdEta (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p := by
    unfold errS streamC
    simp
  have herr1 : (errS ε L f p) 1 = (ε : ℂ) * (opK (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p
      - zCut L (fun r => -zPrimC (fun r' => f r' 0) r) p) := by
    unfold errS streamC
    simp [hdQ]
    ring
  have hψp : zCut L (fun r => -zPrimC (fun r' => f r' 0) r) p
      = ((zChi (p.2.2 / L) : ℝ) : ℂ) * (-zPrimC (fun r => f r 0) p) := rfl
  have hn := norm_two_le (errS ε L f p)
  rw [herr0, herr1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hε] at hn
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- the first component
  have hB0 : ‖f p 0 + pdEta (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p‖
      ≤ L⁻¹ * (|p.2.2| * ‖f p 0‖) + (M * L⁻¹) * winP L (fun r => f r 0) p := by
    have eq0 : f p 0 + pdEta (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p
        = ((1 - zChi (p.2.2 / L) : ℝ) : ℂ) * f p 0
          + (-zPrimC (fun r => f r 0) p) * ((deriv zChi (p.2.2 / L) * (1 / L) : ℝ) : ℂ) := by
      rw [hdEta]
      push_cast
      ring
    rw [eq0]
    refine (norm_add_le _ _).trans ?_
    have hn1 : ‖((1 - zChi (p.2.2 / L) : ℝ) : ℂ) * f p 0‖ ≤ L⁻¹ * (|p.2.2| * ‖f p 0‖) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |1 - zChi (p.2.2 / L)| * ‖f p 0‖ ≤ (|p.2.2| / L) * ‖f p 0‖ :=
            mul_le_mul_of_nonneg_right (one_sub_chi_le p.2.2 L hL) (norm_nonneg _)
        _ = L⁻¹ * (|p.2.2| * ‖f p 0‖) := by ring
    have hn2 : ‖(-zPrimC (fun r => f r 0) p) * ((deriv zChi (p.2.2 / L) * (1 / L) : ℝ) : ℂ)‖
        ≤ (M * L⁻¹) * winP L (fun r => f r 0) p := by
      by_cases hη : |p.2.2| ≤ 2 * L
      · rw [winP_of_le L (fun r => f r 0) p hη, norm_mul, norm_neg, Complex.norm_real,
          Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / L), one_div]
        calc ‖zPrimC (fun r => f r 0) p‖ * (|deriv zChi (p.2.2 / L)| * L⁻¹)
            ≤ ‖zPrimC (fun r => f r 0) p‖ * (M * L⁻¹) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hM _) (inv_nonneg.2 hL.le)) (norm_nonneg _)
          _ = (M * L⁻¹) * ‖zPrimC (fun r => f r 0) p‖ := by ring
      · have hd0 : deriv zChi (p.2.2 / L) = 0 := by
          apply zChi_deriv_zero_of
          rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
          linarith [not_le.1 hη]
        rw [winP_of_gt L (fun r => f r 0) p (not_le.1 hη), hd0]
        simp
    linarith [hn1, hn2]
  -- the second component
  have hB1 : ‖opK (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p
      - zCut L (fun r => -zPrimC (fun r' => f r' 0) r) p‖
      ≤ 2 * winP L (fun r => (opS (fun r' => f r' 0)) r) p + |p.2.2| * ‖f p 0‖
        + 2 * M * winP L (fun r => f r 0) p + winP L (fun r => f r 0) p := by
    have eqK : opK (zCut L (fun r => -zPrimC (fun r' => f r' 0) r)) p
        - zCut L (fun r => -zPrimC (fun r' => f r' 0) r) p
        = ((-2 * zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (opS (fun r => f r 0)) p
          + ((-(p.2.2 * zChi (p.2.2 / L)) : ℝ) : ℂ) * f p 0
          + ((-(p.2.2 * (deriv zChi (p.2.2 / L) * (1 / L)))) : ℝ) * zPrimC (fun r => f r 0) p
          + ((zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (fun r => f r 0) p := by
      rw [hKψ, hψp]
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [eqK]
    have hχ0 := zChi_nonneg (p.2.2 / L)
    have hχ1 := zChi_le_one (p.2.2 / L)
    have hχa : |zChi (p.2.2 / L)| ≤ 1 := by
      rw [abs_of_nonneg hχ0]
      exact hχ1
    have hWS0 := winP_nonneg L (fun r => (opS (fun r' => f r' 0)) r) p
    have hW0 := winP_nonneg L (fun r => f r 0) p
    have hA1 : ‖((-2 * zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (opS (fun r => f r 0)) p‖
        ≤ 2 * winP L (fun r => (opS (fun r' => f r' 0)) r) p := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hη : |p.2.2| ≤ 2 * L
      · rw [winP_of_le L (fun r => (opS (fun r' => f r' 0)) r) p hη]
        have h2 : |-2 * zChi (p.2.2 / L)| ≤ 2 := abs_le.2 ⟨by linarith, by linarith⟩
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      · have hχ : zChi (p.2.2 / L) = 0 := by
          apply zChi_zero_of_two_le
          rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]
          linarith [not_le.1 hη]
        rw [winP_of_gt L (fun r => (opS (fun r' => f r' 0)) r) p (not_le.1 hη), hχ]
        simp
    have hA2 : ‖((-(p.2.2 * zChi (p.2.2 / L)) : ℝ) : ℂ) * f p 0‖ ≤ |p.2.2| * ‖f p 0‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
      have h3 : |p.2.2| * |zChi (p.2.2 / L)| ≤ |p.2.2| * 1 :=
        mul_le_mul_of_nonneg_left hχa (abs_nonneg _)
      nlinarith [norm_nonneg (f p 0)]
    have hA3 : ‖((-(p.2.2 * (deriv zChi (p.2.2 / L) * (1 / L)))) : ℝ) * zPrimC (fun r => f r 0) p‖
        ≤ 2 * M * winP L (fun r => f r 0) p := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hη : |p.2.2| ≤ 2 * L
      · rw [winP_of_le L (fun r => f r 0) p hη, abs_neg, abs_mul, abs_mul,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / L)]
        have h2 : |p.2.2| * (1 / L) ≤ 2 := by
          rw [mul_one_div, div_le_iff₀ hL]
          linarith [hη]
        have h3 : (|p.2.2| * (1 / L)) * |deriv zChi (p.2.2 / L)| ≤ 2 * M :=
          mul_le_mul h2 (hM _) (abs_nonneg _) (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_right h3 (norm_nonneg (zPrimC (fun r => f r 0) p))]
      · have hd0 : deriv zChi (p.2.2 / L) = 0 := by
          apply zChi_deriv_zero_of
          rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
          linarith [not_le.1 hη]
        rw [winP_of_gt L (fun r => f r 0) p (not_le.1 hη), hd0]
        simp
    have hA4 : ‖((zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (fun r => f r 0) p‖
        ≤ winP L (fun r => f r 0) p := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hη : |p.2.2| ≤ 2 * L
      · rw [winP_of_le L (fun r => f r 0) p hη]
        exact mul_le_of_le_one_left (norm_nonneg _) hχa
      · have hχ : zChi (p.2.2 / L) = 0 := by
          apply zChi_zero_of_two_le
          rw [abs_div, abs_of_pos hL, le_div_iff₀ hL]
          linarith [not_le.1 hη]
        rw [hχ, abs_zero, zero_mul]
        exact hW0
    have t1 := norm_add_le
      (((-2 * zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (opS (fun r => f r 0)) p
        + ((-(p.2.2 * zChi (p.2.2 / L)) : ℝ) : ℂ) * f p 0
        + ((-(p.2.2 * (deriv zChi (p.2.2 / L) * (1 / L)))) : ℝ) * zPrimC (fun r => f r 0) p)
      (((zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (fun r => f r 0) p)
    have t2 := norm_add_le
      (((-2 * zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (opS (fun r => f r 0)) p
        + ((-(p.2.2 * zChi (p.2.2 / L)) : ℝ) : ℂ) * f p 0)
      (((-(p.2.2 * (deriv zChi (p.2.2 / L) * (1 / L)))) : ℝ) * zPrimC (fun r => f r 0) p)
    have t3 := norm_add_le
      (((-2 * zChi (p.2.2 / L) : ℝ) : ℂ) * zPrimC (opS (fun r => f r 0)) p)
      (((-(p.2.2 * zChi (p.2.2 / L)) : ℝ) : ℂ) * f p 0)
    linarith [t1, t2, t3, hA1, hA2, hA3, hA4]
  unfold etaFr
  nlinarith [hn, hB0, mul_le_mul_of_nonneg_left hB1 hε]

end UnforcedLeray.Short.PartIIa
