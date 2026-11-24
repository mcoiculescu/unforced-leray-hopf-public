import UnforcedLeray.Short.PartIIa.Sub.N02_3_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.Cutoff

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Let `Φ = zPrimC f_z`, `Ψ = zCut L Φ = χ(η/L) Φ`, `a = χ(η/L)`, `d = χ'(η/L)`.
Then `∂_q Ψ = 0`, `∂_s Ψ = a ∂_s Φ`, `∂_η Ψ = (d/L) Φ + a f_z`, so
`opK Ψ = 2a opS Φ + η a f_z + η (d/L) Φ` and the error has components
`ε opK Ψ` and `f_z - ∂_η Ψ = (1-a) f_z - (d/L) Φ`. The real inequality is case-split on `|η| ≤ 2L`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open ZeroGradCutErrorAux

namespace GCEPointwiseAux

/-! ### Derivatives along coordinate lines -/

theorem hasDerivAt_q {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun q : ℝ => F (p.1, q, p.2.2)) (fderiv ℝ F p (0, 1, 0)) p.2.1 := by
  have hl : HasDerivAt (fun q : ℝ => ((p.1, q, p.2.2) : Profile)) ((0 : ℝ), (1 : ℝ), (0 : ℝ))
      p.2.1 := by
    have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : ℝ) p.2.1 := by apply hasDerivAt_const
    have h2 : HasDerivAt (fun q : ℝ => q) (1 : ℝ) p.2.1 := hasDerivAt_id' _
    have h3 : HasDerivAt (fun _ : ℝ => p.2.2) (0 : ℝ) p.2.1 := by apply hasDerivAt_const
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.2.1 hl

theorem hasDerivAt_s {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun σ : ℝ => F (σ, p.2.1, p.2.2)) (fderiv ℝ F p (1, 0, 0)) p.1 := by
  have hl : HasDerivAt (fun σ : ℝ => ((σ, p.2.1, p.2.2) : Profile)) ((1 : ℝ), (0 : ℝ), (0 : ℝ))
      p.1 := by
    have h1 : HasDerivAt (fun σ : ℝ => σ) (1 : ℝ) p.1 := hasDerivAt_id' _
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.1 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun _ : ℝ => p.2.2) (0 : ℝ) p.1 := by apply hasDerivAt_const
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.1 hl

theorem hasDerivAt_eta {F : Profile → ℂ} (hF : Differentiable ℝ F) (p : Profile) :
    HasDerivAt (fun η : ℝ => F (p.1, p.2.1, η)) (fderiv ℝ F p (0, 0, 1)) p.2.2 := by
  have hl : HasDerivAt (fun η : ℝ => ((p.1, p.2.1, η) : Profile)) ((0 : ℝ), (0 : ℝ), (1 : ℝ))
      p.2.2 := by
    have h1 : HasDerivAt (fun _ : ℝ => p.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h2 : HasDerivAt (fun _ : ℝ => p.2.1) (0 : ℝ) p.2.2 := by apply hasDerivAt_const
    have h3 : HasDerivAt (fun η : ℝ => η) (1 : ℝ) p.2.2 := hasDerivAt_id' _
    exact h1.prodMk (h2.prodMk h3)
  exact (hF p).hasFDerivAt.comp_hasDerivAt p.2.2 hl

/-- A `q`-invariant differentiable profile has `∂_q = 0`. -/
theorem pdQ_zero_of_inv {F : Profile → ℂ} (hF : Differentiable ℝ F)
    (hI : ∀ s q q' η : ℝ, F (s, q, η) = F (s, q', η)) (p : Profile) : pdQ F p = 0 := by
  have hl := hasDerivAt_q hF p
  have hc : HasDerivAt (fun q : ℝ => F (p.1, q, p.2.2)) 0 p.2.1 := by
    have hfun : (fun q : ℝ => F (p.1, q, p.2.2)) = fun _ => F p := by
      funext q
      exact hI p.1 q p.2.1 p.2.2
    rw [hfun]
    exact hasDerivAt_const _ _
  exact hl.unique hc

/-! ### The cutoff product `Ψ = χ(η/L) Φ` -/

theorem zCutProd_contDiff {L : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r) := by
  have h1 : ContDiff ℝ ∞ (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ZeroCutoffAux.zChi_contDiff.comp
      (show ContDiff ℝ ∞ (fun r : Profile => r.2.2 / L) from by fun_prop))
  exact h1.mul hΦ

theorem zCutProd_pdS {L : ℝ} {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    pdS (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r) p
      = ((zChi (p.2.2 / L) : ℝ) : ℂ) * pdS Φ p := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΨd : Differentiable ℝ (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r) :=
    (zCutProd_contDiff hΦ).differentiable (by simp)
  have h1 := (hasDerivAt_s hΦd p).const_mul ((zChi (p.2.2 / L) : ℝ) : ℂ)
  have h2 := hasDerivAt_s hΨd p
  exact h2.unique h1

theorem zCutProd_pdEta {L : ℝ} (hL : 0 < L) {Φ : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (p : Profile) :
    pdEta (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r) p
      = (((deriv zChi (p.2.2 / L) * (1 / L) : ℝ)) : ℂ) * Φ p
        + ((zChi (p.2.2 / L) : ℝ) : ℂ) * pdEta Φ p := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hΨd : Differentiable ℝ (fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r) :=
    (zCutProd_contDiff hΦ).differentiable (by simp)
  have h0 : HasDerivAt zChi (deriv zChi (p.2.2 / L)) (p.2.2 / L) :=
    ((ZeroCutoffAux.zChi_contDiff.differentiable (by simp)) (p.2.2 / L)).hasDerivAt
  have h1 : HasDerivAt (fun η : ℝ => η / L) (1 / L) p.2.2 := by
    simpa using (hasDerivAt_id p.2.2).div_const L
  have hz := h0.comp p.2.2 h1
  have h2 := hz.ofReal_comp.mul (hasDerivAt_eta hΦd p)
  have h3 := hasDerivAt_eta hΨd p
  exact h3.unique h2

/-! ### Real bookkeeping -/

theorem realBound (a d η L M ε A1 A2 A3 : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hd : |d| ≤ M)
    (hL : 0 < L) (hε : 0 ≤ ε) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hM : 0 ≤ M)
    (hz : 2 * L < |η| → a = 0 ∧ d = 0) (hone : |η| < L → a = 1) :
    ε * (2 * a * A1 + |η| * a * A2 + |η| * (|d| * (1 / L)) * A3)
        + ((1 - a) * A2 + |d| * (1 / L) * A3)
      ≤ 2 * ε * (if |η| ≤ 2 * L then A1 else 0) + ε * (|η| * A2)
        + (2 * M * ε + M * (1 / L)) * (if |η| ≤ 2 * L then A3 else 0)
        + (1 / L) * (|η| * A2) := by
  have hLi : 0 < 1 / L := by positivity
  have hb : 1 - a ≤ |η| * (1 / L) := by
    by_cases hl : |η| < L
    · rw [hone hl]
      have : 0 ≤ |η| * (1 / L) := by positivity
      linarith
    · push_neg at hl
      have h1 : 1 ≤ |η| * (1 / L) := by
        rw [mul_one_div, le_div_iff₀ hL]
        linarith
      linarith
  have hd' : |d| * (1 / L) ≤ M * (1 / L) := mul_le_mul_of_nonneg_right hd hLi.le
  by_cases h2 : |η| ≤ 2 * L
  · rw [if_pos h2, if_pos h2]
    have hr : |η| * (1 / L) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hL]
      linarith
    have e1 : |η| * a * A2 ≤ |η| * A2 := by
      have : a * A2 ≤ A2 := by nlinarith
      nlinarith [abs_nonneg η]
    have e2 : 2 * a * A1 ≤ 2 * A1 := by nlinarith
    have e3 : |η| * (|d| * (1 / L)) * A3 ≤ 2 * M * A3 := by
      have hm : |η| * (|d| * (1 / L)) ≤ 2 * M := by
        calc |η| * (|d| * (1 / L)) = (|η| * (1 / L)) * |d| := by ring
          _ ≤ 2 * M := by
            have := mul_le_mul hr hd (abs_nonneg d) (by norm_num)
            linarith
      exact mul_le_mul_of_nonneg_right hm hA3
    have hE : ε * (2 * a * A1 + |η| * a * A2 + |η| * (|d| * (1 / L)) * A3)
        ≤ ε * (2 * A1 + |η| * A2 + 2 * M * A3) :=
      mul_le_mul_of_nonneg_left (by linarith) hε
    have hF : (1 - a) * A2 + |d| * (1 / L) * A3 ≤ |η| * (1 / L) * A2 + M * (1 / L) * A3 := by
      have f1 : (1 - a) * A2 ≤ |η| * (1 / L) * A2 := mul_le_mul_of_nonneg_right hb hA2
      have f2 : |d| * (1 / L) * A3 ≤ M * (1 / L) * A3 := mul_le_mul_of_nonneg_right hd' hA3
      linarith
    calc ε * (2 * a * A1 + |η| * a * A2 + |η| * (|d| * (1 / L)) * A3)
          + ((1 - a) * A2 + |d| * (1 / L) * A3)
        ≤ ε * (2 * A1 + |η| * A2 + 2 * M * A3) + (|η| * (1 / L) * A2 + M * (1 / L) * A3) :=
          add_le_add hE hF
      _ = 2 * ε * A1 + ε * (|η| * A2) + (2 * M * ε + M * (1 / L)) * A3
          + (1 / L) * (|η| * A2) := by ring
  · rw [if_neg h2, if_neg h2]
    push_neg at h2
    have hpos : 2 * L < |η| := h2
    obtain ⟨ha, hdz⟩ := hz hpos
    rw [ha, hdz]
    have hr : 1 ≤ |η| * (1 / L) := by
      rw [mul_one_div, le_div_iff₀ hL]
      linarith
    have : (1 - 0) * A2 ≤ |η| * (1 / L) * A2 := mul_le_mul_of_nonneg_right (by linarith) hA2
    simp only [abs_zero, zero_mul, mul_zero, add_zero, zero_add, mul_zero, zero_mul]
    nlinarith

/-! ### Norms and the `q`-invariance of `zPrimC` -/

theorem norm_realmul (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ = |r| * ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem meridNorm_le (v : MeridC) : ‖v‖ ≤ ‖v 0‖ + ‖v 1‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith [norm_nonneg (v 0), norm_nonneg (v 1)]

theorem zPrimC_inv {c : ℝ} {f : Profile → MeridC} (hQ : QInvariant c f) (s q q' η : ℝ) :
    zPrimC (fun r => f r 1) (s, q, η) = zPrimC (fun r => f r 1) (s, q', η) := by
  show (∫ t in (0 : ℝ)..η, f (s, q, t) 1) = ∫ t in (0 : ℝ)..η, f (s, q', t) 1
  congr 1
  funext t
  rw [hQ s q q' t]

theorem zPrimC_eq_of_band (g : Profile → ℂ) (p : Profile) :
    zPrimC g p = ∫ t in (0 : ℝ)..p.2.2, g (p.1, p.2.1, t) := rfl

theorem zChi_deriv_zero {t : ℝ} (ht : 2 < |t|) : deriv zChi t = 0 := by
  have hev : zChi =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds
      (show t ∈ {x : ℝ | 2 < |x|} from ht)] with x hx
    exact ZeroCutoffAux.zChi_eq_zero (le_of_lt hx)
  rw [hev.deriv_eq]
  simp

theorem winP_eq (L : ℝ) (g : Profile → ℂ) (p : Profile) :
    winP L g p = if |p.2.2| ≤ 2 * L then ‖zPrimC g p‖ else 0 := by
  unfold winP
  by_cases h : |p.2.2| ≤ 2 * L
  · simp [h]
  · simp [h]

/-! ### The core pointwise estimate for `Ψ = zCut L Φ` -/

theorem gceCore {L ε : ℝ} {Φ Fz : Profile → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hQ : ∀ s q q' η : ℝ, Φ (s, q, η) = Φ (s, q', η)) (hE : ∀ r, pdEta Φ r = Fz r)
    (hL : 0 < L) (hε : 0 ≤ ε) (p : Profile) :
    ‖(!₂[0, Fz p] : MeridC) - cgradC ε (zCut L Φ) p‖ ≤
      ε * (2 * zChi (p.2.2 / L) * ‖opS Φ p‖ + |p.2.2| * zChi (p.2.2 / L) * ‖Fz p‖
          + |p.2.2| * (|deriv zChi (p.2.2 / L)| * (1 / L)) * ‖Φ p‖)
        + ((1 - zChi (p.2.2 / L)) * ‖Fz p‖ + |deriv zChi (p.2.2 / L)| * (1 / L) * ‖Φ p‖) := by
  have hA : 0 ≤ zChi (p.2.2 / L) := ZeroCutoffAux.zChi_nonneg _
  have hA1 : 0 ≤ 1 - zChi (p.2.2 / L) := by linarith [ZeroCutoffAux.zChi_le_one (p.2.2 / L)]
  have hΨd : Differentiable ℝ (zCut L Φ) := by
    have : zCut L Φ = fun r : Profile => ((zChi (r.2.2 / L) : ℝ) : ℂ) * Φ r := rfl
    rw [this]
    exact (zCutProd_contDiff hΦ).differentiable (by simp)
  have hQΨ : ∀ s q q' η : ℝ, zCut L Φ (s, q, η) = zCut L Φ (s, q', η) := by
    intro s q q' η
    show ((zChi (η / L) : ℝ) : ℂ) * Φ (s, q, η) = ((zChi (η / L) : ℝ) : ℂ) * Φ (s, q', η)
    rw [hQ s q q' η]
  have hpdQ : pdQ (zCut L Φ) p = 0 := pdQ_zero_of_inv hΨd hQΨ p
  have hpdS : pdS (zCut L Φ) p = ((zChi (p.2.2 / L) : ℝ) : ℂ) * pdS Φ p :=
    zCutProd_pdS hΦ p
  have hpdE : pdEta (zCut L Φ) p
      = (((deriv zChi (p.2.2 / L) * (1 / L) : ℝ)) : ℂ) * Φ p
        + ((zChi (p.2.2 / L) : ℝ) : ℂ) * Fz p := by
    have h := zCutProd_pdEta hL hΦ p
    rw [hE p] at h
    exact h
  have hopS : opS (zCut L Φ) p = ((zChi (p.2.2 / L) : ℝ) : ℂ) * opS Φ p := by
    unfold opS
    rw [hpdS]
    simp only [Complex.real_smul]
    ring
  have hopK : opK (zCut L Φ) p
      = ((2 * zChi (p.2.2 / L) : ℝ) : ℂ) * opS Φ p
        + ((p.2.2 * zChi (p.2.2 / L) : ℝ) : ℂ) * Fz p
        + ((p.2.2 * (deriv zChi (p.2.2 / L) * (1 / L)) : ℝ) : ℂ) * Φ p := by
    simp only [opK]
    rw [hopS, hpdE, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have e1 : ‖((2 * zChi (p.2.2 / L) : ℝ) : ℂ) * opS Φ p‖
      = 2 * zChi (p.2.2 / L) * ‖opS Φ p‖ := by
    rw [norm_realmul, abs_of_nonneg (by linarith)]
  have e2 : ‖((p.2.2 * zChi (p.2.2 / L) : ℝ) : ℂ) * Fz p‖
      = |p.2.2| * zChi (p.2.2 / L) * ‖Fz p‖ := by
    rw [norm_realmul, abs_mul, abs_of_nonneg hA]
  have e3 : ‖((p.2.2 * (deriv zChi (p.2.2 / L) * (1 / L)) : ℝ) : ℂ) * Φ p‖
      = |p.2.2| * (|deriv zChi (p.2.2 / L)| * (1 / L)) * ‖Φ p‖ := by
    rw [norm_realmul, abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / L by positivity)]
  have hnormK : ‖opK (zCut L Φ) p‖ ≤ 2 * zChi (p.2.2 / L) * ‖opS Φ p‖
      + |p.2.2| * zChi (p.2.2 / L) * ‖Fz p‖
      + |p.2.2| * (|deriv zChi (p.2.2 / L)| * (1 / L)) * ‖Φ p‖ := by
    rw [hopK]
    exact (norm_add₃_le).trans (le_of_eq (by rw [e1, e2, e3]))
  have hnormE : ‖Fz p - pdEta (zCut L Φ) p‖
      ≤ (1 - zChi (p.2.2 / L)) * ‖Fz p‖ + |deriv zChi (p.2.2 / L)| * (1 / L) * ‖Φ p‖ := by
    rw [hpdE]
    have hrw : Fz p - (((deriv zChi (p.2.2 / L) * (1 / L) : ℝ) : ℂ) * Φ p
        + ((zChi (p.2.2 / L) : ℝ) : ℂ) * Fz p)
        = ((1 - zChi (p.2.2 / L) : ℝ) : ℂ) * Fz p
          + ((-(deriv zChi (p.2.2 / L) * (1 / L)) : ℝ) : ℂ) * Φ p := by
      push_cast
      ring
    rw [hrw]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_realmul, norm_realmul, abs_of_nonneg hA1, abs_neg, abs_mul,
      abs_of_pos (show (0 : ℝ) < 1 / L by positivity)]
  have hv := meridNorm_le ((!₂[0, Fz p] : MeridC) - cgradC ε (zCut L Φ) p)
  have c0 : ((!₂[0, Fz p] : MeridC) - cgradC ε (zCut L Φ) p) 0
      = (ε : ℂ) * opK (zCut L Φ) p := by
    simp [cgradC, hpdQ]
  have c1 : ((!₂[0, Fz p] : MeridC) - cgradC ε (zCut L Φ) p) 1
      = Fz p - pdEta (zCut L Φ) p := by
    simp [cgradC]
  rw [c0, c1, norm_realmul, abs_of_nonneg hε] at hv
  calc ‖(!₂[0, Fz p] : MeridC) - cgradC ε (zCut L Φ) p‖
      ≤ ε * ‖opK (zCut L Φ) p‖ + ‖Fz p - pdEta (zCut L Φ) p‖ := hv
    _ ≤ ε * (2 * zChi (p.2.2 / L) * ‖opS Φ p‖ + |p.2.2| * zChi (p.2.2 / L) * ‖Fz p‖
          + |p.2.2| * (|deriv zChi (p.2.2 / L)| * (1 / L)) * ‖Φ p‖)
        + ((1 - zChi (p.2.2 / L)) * ‖Fz p‖ + |deriv zChi (p.2.2 / L)| * (1 / L) * ‖Φ p‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hnormK hε) hnormE

end GCEPointwiseAux

open GCEPointwiseAux in
/-- **Pointwise bound on the gradient cutoff error** (`GCEPointwise`). -/
theorem gCEPointwise : UnforcedLeray.Short.PartIIa.ZeroGradCutErrorAux.GCEPointwise := by
  unfold ZeroGradCutErrorAux.GCEPointwise
  intro hS hK M c ε L f hMb hε hL hc hf hQ p
  have hgS : ContDiff ℝ ∞ (fun r => f r 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hf.smooth
  obtain ⟨s0, s1, L0, hs0, hb⟩ := hf.band
  have hgb : ∃ s0 s1 L : ℝ, 0 < s0 ∧
      ∀ q : Profile, (fun r => f r 1) q ≠ 0 → q.1 ∈ Icc s0 s1 ∧ |q.2.2| ≤ L :=
    ⟨s0, s1, L0, hs0, fun q hq => hb q (fun h => hq (by simp [h]))⟩
  obtain ⟨hΦS, hΦE⟩ := hS (fun r => f r 1) hgS hgb
  have hcomm := hK (fun r => f r 1) hgS hgb
  have hA1eq : ‖opS (zPrimC (fun r => f r 1)) p‖
      = ‖zPrimC (fun r => (opS (fun r' => f r' 1)) r) p‖ := by
    rw [hcomm]
  have hcore := gceCore (L := L) (ε := ε) hΦS (fun s q q' η => zPrimC_inv hQ s q q' η) hΦE
    hL hε p
  have hab : |p.2.2 / L| = |p.2.2| / L := by rw [abs_div, abs_of_pos hL]
  have hzp : 2 * L < |p.2.2| → zChi (p.2.2 / L) = 0 ∧ deriv zChi (p.2.2 / L) = 0 := by
    intro h
    have h2 : 2 < |p.2.2 / L| := by
      rw [hab, lt_div_iff₀ hL]
      linarith
    exact ⟨ZeroCutoffAux.zChi_eq_zero h2.le, zChi_deriv_zero h2⟩
  have hone : |p.2.2| < L → zChi (p.2.2 / L) = 1 := by
    intro h
    have h1 : |p.2.2 / L| ≤ 1 := by
      rw [hab, div_le_one hL]
      exact h.le
    exact ZeroCutoffAux.zChi_eq_one h1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hMb 0)
  have hR := realBound (zChi (p.2.2 / L)) (deriv zChi (p.2.2 / L)) p.2.2 L M ε
    ‖opS (zPrimC (fun r => f r 1)) p‖ ‖f p 1‖ ‖zPrimC (fun r => f r 1) p‖
    (ZeroCutoffAux.zChi_nonneg _) (ZeroCutoffAux.zChi_le_one _) (hMb _) hL hε
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hM0 hzp hone
  unfold errG etaFz
  refine (hcore.trans hR).trans (le_of_eq ?_)
  simp only [winP_eq, one_div]
  rw [← hA1eq]

end UnforcedLeray.Short.PartIIa
