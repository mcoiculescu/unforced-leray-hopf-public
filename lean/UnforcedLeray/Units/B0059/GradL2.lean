import UnforcedLeray.Units.B0059.Basic
import UnforcedLeray.Units.B0059.NUE.H.Sec2.Velocity.Grad
import UnforcedLeray.Units.B0059.NUE.P.Infra.Sobolev.DensityL1L2

/-!
# B0059 (helper): the first-order `L²` bound `‖∂_k (Kg)_i‖₂ ≤ 2 ‖g‖₂`

Helper of `Units/B0059.lean` (blueprint unit B0059, `paper/main.tex:1208–1210`: "the Fourier
multiplier of `∂^α K` has order `|α| - 1` with bounded angular multiplier", base case `|α| = 1`).
Proves `GradL2Bound 2` (`gradL2Bound_two`): for every complex `g ∈ L¹ ∩ L²(ℝ²)` and all `i, k`,
the component `(Kg)_i` of B0009's Biot–Savart velocity has a weak derivative `∂_k (Kg)_i ∈ L²`
with `‖∂_k (Kg)_i‖₂ ≤ 2 ‖g‖₂`.

**Source.** The real-vorticity statement is `lem:velocity`(c) of the NonUniqueEuler reference
formalization, `NonUniqueEuler/lean/NonUniqueEuler/P/Sec2/Velocity.lean:223`
(`gradL2_velocity`, `‖∇(K ⋆ w)‖₂ = ‖w‖₂` for real `w ∈ L¹ ∩ L²`). Its import closure is reused
from the vendored drafts `Lib/Kernels/PlanarBS/` (namespace `UnforcedLeray.PlanarBS`: kernel,
velocity, `BSBasic`, `KernelSplit`, polar coordinates, Young, Sobolev definitions); the reference
modules not vendored there are transported under `Units/B0059/NUE/` (namespace
`UnforcedLeray.B0059.NUE`); `nue_grad_velocity` below repeats the reference proof of `gradL2_velocity` (smooth approximants in
`L¹ ∩ L²`, the `L²` identity `Σ_l ‖∂_l v_j‖² = ‖w_j‖²` by whole-plane integration by parts, the
`L²` limit, weak derivatives), keeping only the inequality `‖∂_l v‖₂ ≤ ‖w‖₂`. No Fourier transform
is used.

**Bridges.** The weak-derivative predicate `UnforcedLeray.PlanarBS.Sob.HasWeakDerivOn` of the
vendored kernel drafts is a copy of the library's `NonUniqueEuler.Sob.HasWeakDerivOn` used by
B0008/B0009/B0059 (`hasWeakDerivOn_of_nue`). The
reference velocity `v = K ⋆ w` is complex (`v = v₁ + i v₂`, kernel `iz/(2π|z|²)`); B0009's
components are `v₁ = (Kw)₀`, `v₂ = (Kw)₁` a.e. (`velocity_ae_eq`, `biotSavartKernel_eq`).
Real and imaginary parts of weak derivatives (`hasWeakDerivOn_re`, `hasWeakDerivOn_im`, via
`conj`) give the components; a complex `g = a + i b` is split into real and imaginary parts, which
costs the factor `2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff ComplexConjugate

namespace UnforcedLeray.B0059

open NonUniqueEuler.Sob UnforcedLeray.B0008 UnforcedLeray.B0009

/-! ### The reference gradient bound for real vorticities -/

/-- `lem:velocity`(c) of the NonUniqueEuler reference
(`NonUniqueEuler/lean/NonUniqueEuler/P/Sec2/Velocity.lean:223`, proof copied): for real
`w ∈ L¹ ∩ L²` and each direction `l`, the reference velocity `K ⋆ w` has a weak derivative
`∂_l (K ⋆ w) ∈ L²` with `‖∂_l (K ⋆ w)‖₂ ≤ ‖w‖₂`. -/
theorem nue_grad_velocity {w : ℂ → ℝ} (h1 : MemLp w 1 volume) (h2 : MemLp w 2 volume)
    (l : Fin 2) :
    ∃ F : ℂ → ℂ, MemLp F 2 volume ∧
      PlanarBS.Sob.HasWeakDerivOn univ [PlanarBS.Prelim.e2 l] (PlanarBS.velocity w) F ∧
      eLpNorm F 2 volume ≤ eLpNorm w 2 volume := by
  obtain ⟨ws, hs, hc, hc1, hc2⟩ := NUE.Sob.exists_seq_smooth_tendsto_L1_L2 h1 h2
  obtain ⟨F, hF, hGF, hnorm⟩ := NUE.BS.VelH.exists_lim_pd_velocity h2 hs hc hc2 l
  refine ⟨F, hF, NUE.BS.VelH.hasWeakDerivOn_velocity h1 hs hc hc1 l hF hGF, ?_⟩
  have hB := NUE.BS.VelH.tendsto_toReal_eLpNorm_of_tendsto
    (fun j => NUE.BS.VelH.memLp_of_smooth (hs j) (hc j) 2) h2 hc2
  have hle : (eLpNorm F 2 volume).toReal ≤ (eLpNorm w 2 volume).toReal :=
    le_of_tendsto_of_tendsto' hnorm hB fun j =>
      ENNReal.toReal_mono (NUE.BS.VelH.memLp_of_smooth (hs j) (hc j) 2).2.ne
        (NUE.BS.VelH.eLpNorm_pd_velocity_le (hs j) (hc j) l)
  exact (ENNReal.toReal_le_toReal hF.2.ne h2.2.ne).1 hle

/-! ### Bridges to the vendored weak derivatives and to B0009's components -/

/-- The `PlanarBS` weak-derivative predicate implies the library one (same definition). -/
theorem hasWeakDerivOn_of_nue {V : Set ℂ} {vs : List ℂ} {f g : ℂ → ℂ}
    (h : PlanarBS.Sob.HasWeakDerivOn V vs f g) : HasWeakDerivOn V vs f g :=
  fun φ hφ => h φ ⟨hφ.smooth, hφ.compact, hφ.subset⟩

theorem e2_eq_dir (l : Fin 2) : PlanarBS.Prelim.e2 l = dir l := by
  fin_cases l <;> rfl

/-- The reference kernel `iz/(2π|z|²)` is `K₀ + i K₁` in B0009's components. -/
theorem biotSavartKernel_eq (z : ℂ) :
    PlanarBS.biotSavartKernel z = kernel 0 z + Complex.I * kernel 1 z := by
  set d : ℝ := 2 * Real.pi * ‖z‖ ^ 2 with hd
  have h1 : PlanarBS.biotSavartKernel z = Complex.I * z / (d : ℂ) := rfl
  have h2 : kernel 0 z = ((-z.im / d : ℝ) : ℂ) := rfl
  have h3 : kernel 1 z = ((z.re / d : ℝ) : ℂ) := rfl
  rw [h1, h2, h3]
  apply Complex.ext
  · rw [Complex.div_ofReal_re]
    simp
  · rw [Complex.div_ofReal_im]
    simp

/-- For real `w`, B0009's components of `K w` are real. -/
theorem biotSavart_ofReal_eq (w : ℂ → ℝ) (i : Fin 2) (x : ℂ) :
    biotSavart (fun y => (w y : ℂ)) i x =
      ((∫ t, w t * (perpComp i (x - t) / (2 * Real.pi * ‖x - t‖ ^ 2)) : ℝ) : ℂ) := by
  rw [biotSavart, convolution_def, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', kernel]
  push_cast
  ring

/-- The reference velocity is `(Kw)₀ + i (Kw)₁` almost everywhere, for real `w ∈ L¹`. -/
theorem velocity_ae_eq {w : ℂ → ℝ} (hw : Integrable w volume) :
    PlanarBS.velocity w =ᵐ[volume] fun x =>
      biotSavart (fun y => (w y : ℂ)) 0 x + Complex.I * biotSavart (fun y => (w y : ℂ)) 1 x := by
  have hf : Integrable (fun y => (w y : ℂ)) volume := hw.ofReal
  filter_upwards [convolutionExistsAt_kernel hf 0, convolutionExistsAt_kernel hf 1] with x h0 h1
  unfold ConvolutionExistsAt at h0 h1
  have h0' : Integrable (fun t => (w t : ℂ) * kernel 0 (x - t)) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using h0
  have h1' : Integrable (fun t => Complex.I * ((w t : ℂ) * kernel 1 (x - t))) volume := by
    simpa only [ContinuousLinearMap.mul_apply'] using h1.const_mul Complex.I
  simp only [PlanarBS.velocity, biotSavart, convolution_def, ContinuousLinearMap.mul_apply']
  rw [← integral_const_mul, ← integral_add h0' h1']
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [biotSavartKernel_eq]
  ring

/-! ### Real and imaginary parts of weak derivatives -/

theorem iterDirDeriv_conj (vs : List ℂ) (φ : ℂ → ℂ) :
    iterDirDeriv vs (fun x => conj (φ x)) = fun x => conj (iterDirDeriv vs φ x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iterDirDeriv_cons, iterDirDeriv_cons, ih]
    simp only [dirDeriv]
    have e : (fun x => conj (iterDirDeriv vs φ x)) = Complex.conjCLE ∘ iterDirDeriv vs φ := rfl
    rw [e, Complex.conjCLE.comp_fderiv]
    rfl

theorem isTestFn_conj {φ : ℂ → ℂ} (hφ : IsTestFn univ φ) : IsTestFn univ (fun x => conj (φ x)) :=
  ⟨Complex.conjCLE.contDiff.comp hφ.smooth,
    hφ.compact.comp_left (g := fun z : ℂ => conj z) (map_zero _), subset_univ _⟩

/-- Weak derivatives commute with complex conjugation. -/
theorem hasWeakDerivOn_conj {vs : List ℂ} {U F : ℂ → ℂ} (h : HasWeakDerivOn univ vs U F) :
    HasWeakDerivOn univ vs (fun x => conj (U x)) (fun x => conj (F x)) := by
  intro φ hφ
  have e := h _ (isTestFn_conj hφ)
  rw [iterDirDeriv_conj] at e
  calc ∫ x, conj (U x) * iterDirDeriv vs φ x =
        conj (∫ x, U x * conj (iterDirDeriv vs φ x)) := by
          rw [← integral_conj]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp
    _ = conj ((-1 : ℂ) ^ vs.length * ∫ x, F x * conj (φ x)) := by rw [e]
    _ = (-1 : ℂ) ^ vs.length * ∫ x, conj (F x) * φ x := by
          rw [map_mul, ← integral_conj]
          simp

theorem locallyIntegrable_conj {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) :
    LocallyIntegrable (fun x => conj (U x)) volume := by
  intro x
  obtain ⟨s, hs, hi⟩ := hU x
  refine ⟨s, hs, ?_⟩
  have h : Integrable (fun a => conj (U a)) (volume.restrict s) := by
    simpa using (Complex.conjCLE.toContinuousLinearMap).integrable_comp hi
  exact h

theorem locallyIntegrable_const_mul {U : ℂ → ℂ} (hU : LocallyIntegrable U volume) (c : ℂ) :
    LocallyIntegrable (fun x => c * U x) volume :=
  hU.smul c

/-- The real part of a weak derivative is the weak derivative of the real part. -/
theorem hasWeakDerivOn_re {vs : List ℂ} {U F : ℂ → ℂ} (hU : LocallyIntegrable U volume)
    (hF : LocallyIntegrable F volume) (h : HasWeakDerivOn univ vs U F) :
    HasWeakDerivOn univ vs (fun x => ((U x).re : ℂ)) (fun x => ((F x).re : ℂ)) := by
  have h2 := (h.add isOpen_univ (hU.locallyIntegrableOn univ)
    ((locallyIntegrable_conj hU).locallyIntegrableOn univ) (hF.locallyIntegrableOn univ)
    ((locallyIntegrable_conj hF).locallyIntegrableOn univ) (hasWeakDerivOn_conj h)).const_mul
    (1 / 2 : ℂ)
  have e1 : (fun x => (1 / 2 : ℂ) * (U + fun x => conj (U x)) x) = fun x => ((U x).re : ℂ) := by
    funext x
    rw [Pi.add_apply, Complex.re_eq_add_conj]
    ring
  have e2 : (fun x => (1 / 2 : ℂ) * (F + fun x => conj (F x)) x) = fun x => ((F x).re : ℂ) := by
    funext x
    rw [Pi.add_apply, Complex.re_eq_add_conj]
    ring
  rwa [e1, e2] at h2

/-- The imaginary part of a weak derivative is the weak derivative of the imaginary part. -/
theorem hasWeakDerivOn_im {vs : List ℂ} {U F : ℂ → ℂ} (hU : LocallyIntegrable U volume)
    (hF : LocallyIntegrable F volume) (h : HasWeakDerivOn univ vs U F) :
    HasWeakDerivOn univ vs (fun x => ((U x).im : ℂ)) (fun x => ((F x).im : ℂ)) := by
  have hc := (hasWeakDerivOn_conj h).const_mul (-1 : ℂ)
  have h2 := (h.add isOpen_univ (hU.locallyIntegrableOn univ)
    ((locallyIntegrable_const_mul (locallyIntegrable_conj hU) (-1)).locallyIntegrableOn univ)
    (hF.locallyIntegrableOn univ)
    ((locallyIntegrable_const_mul (locallyIntegrable_conj hF) (-1)).locallyIntegrableOn univ)
    hc).const_mul (1 / (2 * Complex.I))
  have e1 : (fun x => (1 / (2 * Complex.I)) * (U + fun x => -1 * conj (U x)) x) =
      fun x => ((U x).im : ℂ) := by
    funext x
    rw [Pi.add_apply, Complex.im_eq_sub_conj]
    ring
  have e2 : (fun x => (1 / (2 * Complex.I)) * (F + fun x => -1 * conj (F x)) x) =
      fun x => ((F x).im : ℂ) := by
    funext x
    rw [Pi.add_apply, Complex.im_eq_sub_conj]
    ring
  rwa [e1, e2] at h2

/-! ### Real data, then complex data -/

theorem eLpNorm_re_le (F : ℂ → ℂ) :
    eLpNorm (fun x => ((F x).re : ℂ)) 2 volume ≤ eLpNorm F 2 volume :=
  eLpNorm_mono fun x => by simpa using Complex.abs_re_le_norm (F x)

theorem eLpNorm_im_le (F : ℂ → ℂ) :
    eLpNorm (fun x => ((F x).im : ℂ)) 2 volume ≤ eLpNorm F 2 volume :=
  eLpNorm_mono fun x => by simpa using Complex.abs_im_le_norm (F x)

/-- **The first-order `L²` bound for real data**: for real `w ∈ L¹ ∩ L²`,
`∂_k (Kw)_i ∈ L²` weakly with `‖∂_k (Kw)_i‖₂ ≤ ‖w‖₂`. -/
theorem gradL2_real {w : ℂ → ℝ} (h1 : Integrable w volume) (h2 : MemLp w 2 volume)
    (i k : Fin 2) :
    ∃ G : ℂ → ℂ, MemLp G 2 volume ∧
      HasWeakDerivOn univ [dir k] (biotSavart (fun y => (w y : ℂ)) i) G ∧
      eLpNorm G 2 volume ≤ eLpNorm w 2 volume := by
  obtain ⟨F, hF, hW, hle⟩ := nue_grad_velocity (memLp_one_iff_integrable.2 h1) h2 k
  have hW' : HasWeakDerivOn univ [dir k] (PlanarBS.velocity w) F := by
    have := hasWeakDerivOn_of_nue hW
    rwa [e2_eq_dir] at this
  set f : ℂ → ℂ := fun y => (w y : ℂ) with hfdef
  have hf1 : Integrable f volume := h1.ofReal
  have hf2 : MemLp f 2 volume := h2.ofReal
  have hae := velocity_ae_eq h1
  have hl0 := locallyIntegrable_biotSavart hf1 hf2 0
  have hl1 := locallyIntegrable_biotSavart hf1 hf2 1
  have hU : LocallyIntegrable (PlanarBS.velocity w) volume :=
    (hl0.add (locallyIntegrable_const_mul hl1 Complex.I)).congr hae.symm
  have hFl : LocallyIntegrable F volume := hF.locallyIntegrable one_le_two
  have hre : ∀ x, ((biotSavart f 0 x + Complex.I * biotSavart f 1 x).re : ℂ) = biotSavart f 0 x := by
    intro x
    rw [biotSavart_ofReal_eq, biotSavart_ofReal_eq]
    simp
  have him : ∀ x, ((biotSavart f 0 x + Complex.I * biotSavart f 1 x).im : ℂ) = biotSavart f 1 x := by
    intro x
    rw [biotSavart_ofReal_eq, biotSavart_ofReal_eq]
    simp
  fin_cases i
  · refine ⟨fun x => ((F x).re : ℂ), ?_, ?_, (eLpNorm_re_le F).trans hle⟩
    · exact ⟨(Complex.continuous_ofReal.comp Complex.continuous_re).comp_aestronglyMeasurable hF.1,
        (eLpNorm_re_le F).trans_lt hF.2⟩
    · refine (hasWeakDerivOn_re hU hFl hW').congr_ae ?_ (ae_of_all _ fun _ _ => rfl)
      filter_upwards [hae] with x hx _
      rw [hx, hre]
      rfl
  · refine ⟨fun x => ((F x).im : ℂ), ?_, ?_, (eLpNorm_im_le F).trans hle⟩
    · exact ⟨(Complex.continuous_ofReal.comp Complex.continuous_im).comp_aestronglyMeasurable hF.1,
        (eLpNorm_im_le F).trans_lt hF.2⟩
    · refine (hasWeakDerivOn_im hU hFl hW').congr_ae ?_ (ae_of_all _ fun _ _ => rfl)
      filter_upwards [hae] with x hx _
      rw [hx, him]
      rfl

/-- **`GradL2Bound 2`**: for complex `g ∈ L¹ ∩ L²` and all `i, k`, `‖∂_k (Kg)_i‖₂ ≤ 2 ‖g‖₂`
(`paper/main.tex:1208–1210`, base case `|α| = 1`; B0059). -/
theorem gradL2Bound_two : GradL2Bound 2 := by
  refine ⟨by norm_num, fun g hg1 hg2 i k => ?_⟩
  set a : ℂ → ℝ := fun y => (g y).re with hadef
  set b : ℂ → ℝ := fun y => (g y).im with hbdef
  have ha1 : Integrable a volume := hg1.re
  have hb1 : Integrable b volume := hg1.im
  have ha2 : MemLp a 2 volume := hg2.re
  have hb2 : MemLp b 2 volume := hg2.im
  obtain ⟨Ga, hGa2, hGad, hGab⟩ := gradL2_real ha1 ha2 i k
  obtain ⟨Gb, hGb2, hGbd, hGbb⟩ := gradL2_real hb1 hb2 i k
  have hA1 : Integrable (fun y => (a y : ℂ)) volume := ha1.ofReal
  have hB1 : Integrable (fun y => (b y : ℂ)) volume := hb1.ofReal
  have hgeq : g = (fun y => (a y : ℂ)) + Complex.I • fun y => (b y : ℂ) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hadef, hbdef]
    rw [mul_comm]
    exact (Complex.re_add_im (g y)).symm
  have hsplit : biotSavart g i =ᵐ[volume] fun x =>
      biotSavart (fun y => (a y : ℂ)) i x + Complex.I * biotSavart (fun y => (b y : ℂ)) i x := by
    rw [hgeq]
    filter_upwards [biotSavart_add_ae hA1 (hB1.smul Complex.I) i] with x hx
    rw [hx, Pi.add_apply, biotSavart_smul, Pi.smul_apply, smul_eq_mul]
  have hla := locallyIntegrable_biotSavart hA1 ha2.ofReal i
  have hlb := locallyIntegrable_biotSavart hB1 hb2.ofReal i
  have hd := hGad.add isOpen_univ (hla.locallyIntegrableOn univ)
    ((locallyIntegrable_const_mul hlb Complex.I).locallyIntegrableOn univ)
    ((hGa2.locallyIntegrable one_le_two).locallyIntegrableOn univ)
    ((locallyIntegrable_const_mul (hGb2.locallyIntegrable one_le_two) Complex.I).locallyIntegrableOn
      univ)
    (hGbd.const_mul Complex.I)
  have hIGb : eLpNorm (fun x => Complex.I * Gb x) 2 volume = eLpNorm Gb 2 volume :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun x => by simp)
  have hIGb2 : MemLp (fun x => Complex.I * Gb x) 2 volume :=
    ⟨(hGb2.1.const_mul Complex.I), hIGb ▸ hGb2.2⟩
  refine ⟨Ga + fun x => Complex.I * Gb x, hGa2.add hIGb2, ?_, ?_⟩
  · refine hd.congr_ae ?_ (ae_of_all _ fun _ _ => rfl)
    filter_upwards [hsplit] with x hx _
    rw [hx]
    rfl
  · have ha : eLpNorm a 2 volume ≤ eLpNorm g 2 volume :=
      eLpNorm_mono fun x => by simpa [hadef] using Complex.abs_re_le_norm (g x)
    have hb : eLpNorm b 2 volume ≤ eLpNorm g 2 volume :=
      eLpNorm_mono fun x => by simpa [hbdef] using Complex.abs_im_le_norm (g x)
    calc eLpNorm (Ga + fun x => Complex.I * Gb x) 2 volume
        ≤ eLpNorm Ga 2 volume + eLpNorm (fun x => Complex.I * Gb x) 2 volume :=
          eLpNorm_add_le hGa2.1 hIGb2.1 one_le_two
      _ ≤ eLpNorm g 2 volume + eLpNorm g 2 volume := by
          rw [hIGb]
          exact add_le_add (hGab.trans ha) (hGbb.trans hb)
      _ = ENNReal.ofReal 2 * eLpNorm g 2 volume := by
          rw [ENNReal.ofReal_ofNat, two_mul]

end UnforcedLeray.B0059
