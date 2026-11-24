import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.Cutoffs

/-!
# Pointwise decomposition of the cutoff resolvent pairing into real scalar pieces
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

Reduces `(inner ℂ (resolventTest ν μ (zetaCut S R b) p) (bm b p)).re` to a sum over `i : Fin 2`
of the real scalar operator `scalarResolvent ν μ S R` applied to `uRe b i = (b · i).re` and
`uIm b i = (b · i).im`, and establishes compact-box integrability on `Ioi 0 ×ˢ B0579.cell c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (vnorm2 tnorm2 flatDt flatLap)
open UnforcedLeray.Short.PartIIa (pdS pdQ pdEta)

/-- Cutoff of a real scalar profile function: `θ_S(s) χ_R(η) f(s, q, η)`. -/
def fCut (S R : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  thetaS S p.1 * chiR R p.2.2 * f p

/-- Real scalar action of `(μ - A₀*)` on `fCut S R f`. -/
def scalarResolvent (ν μ S R : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  (μ + 1 / 2) * fCut S R f p - p.1 * pdS (fCut S R f) p -
    ν * p.1 * (pdQ (pdQ (fCut S R f)) p + pdEta (pdEta (fCut S R f)) p)

/-- Age part of `s^{-3/2} (scalarResolvent ν μ S R f p * f p)`. -/
def ageIntegrand (μ S R : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  p.1 ^ (-(3 / 2 : ℝ)) * ((μ + 1 / 2) * fCut S R f p * f p - p.1 * pdS (fCut S R f) p * f p)

/-- Viscous `(q, η)` part of `s^{-3/2} (scalarResolvent ν μ S R f p * f p)`. -/
def viscIntegrand (ν S R : ℝ) (f : Profile → ℝ) (p : Profile) : ℝ :=
  -(p.1 ^ (-(3 / 2 : ℝ)) * (ν * p.1) *
    (pdQ (pdQ (fCut S R f)) p + pdEta (pdEta (fCut S R f)) p) * f p)

theorem scalarResolvent_mul_split (ν μ S R : ℝ) (f : Profile → ℝ) (p : Profile) :
    p.1 ^ (-(3 / 2 : ℝ)) * (scalarResolvent ν μ S R f p * f p) =
      ageIntegrand μ S R f p + viscIntegrand ν S R f p := by
  unfold scalarResolvent ageIntegrand viscIntegrand
  ring

theorem contDiff_fCut (S R : ℝ) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fCut S R f) := by
  unfold fCut
  exact (((contDiff_thetaS S).comp contDiff_fst).mul
    ((contDiff_chiR R).comp (contDiff_snd.comp contDiff_snd))).mul hf

/-- If `f` vanishes on an open neighborhood `{p | p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2|}`, so does `fderiv ℝ f`. -/
theorem fderiv_zero_outside_band {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} {s0 s1 L : ℝ}
    (hz : ∀ p : Profile, (p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2|) → f p = 0)
    {p : Profile} (hp : p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2|) :
    fderiv ℝ f p = 0 := by
  have hU : IsOpen {x : Profile | x.1 < s0 ∨ s1 < x.1 ∨ L < |x.2.2|} := by
    rw [Set.ofPred_or, Set.ofPred_or]
    exact (isOpen_lt continuous_fst continuous_const).union
      ((isOpen_lt continuous_const continuous_fst).union
        (isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))))
  have hev : f =ᶠ[𝓝 p] fun _ => (0 : E) :=
    Filter.eventually_of_mem (hU.mem_nhds hp) fun x hx => hz x hx
  rw [hev.fderiv_eq]
  simp

theorem fderiv_zero_of_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} {s0 : ℝ} (hz : ∀ p : Profile, p.1 < s0 → f p = 0)
    {p : Profile} (hp : p.1 < s0) : fderiv ℝ f p = 0 := by
  have hU : IsOpen {x : Profile | x.1 < s0} := isOpen_lt continuous_fst continuous_const
  have hev : f =ᶠ[𝓝 p] fun _ => (0 : E) :=
    Filter.eventually_of_mem (hU.mem_nhds hp) fun x hx => hz x hx
  rw [hev.fderiv_eq]
  simp

theorem fCut_zero_outside_band {s0 S R : ℝ} (hR : 0 < R) {f : Profile → ℝ}
    (hz : ∀ p : Profile, p.1 < s0 → f p = 0) {p : Profile}
    (hp : p.1 < s0 ∨ max s0 (S + 1) < p.1 ∨ 2 * R < |p.2.2|) :
    fCut S R f p = 0 := by
  unfold fCut
  rcases hp with h | h | h
  · rw [hz p h, mul_zero]
  · have hS1 : S + 1 ≤ p.1 := le_trans (le_max_right s0 (S + 1)) h.le
    rw [thetaS_eq_zero hS1, zero_mul, zero_mul]
  · rw [chiR_eq_zero hR h.le, mul_zero, zero_mul]

/-- A continuous function on `Chart` that vanishes for `p.1 < s0` stays continuous when multiplied
by `p.1 ^ a` (`s0 > 0`). -/
theorem continuous_rpow_mul_of_zero_below {s0 : ℝ} (hs0 : 0 < s0) (a : ℝ) {G : Chart → ℝ}
    (hG : Continuous G) (hz : ∀ p : Chart, p.1 < s0 → G p = 0) :
    Continuous (fun p : Chart => p.1 ^ a * G p) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 < s0
  · apply ContinuousAt.congr_of_eventuallyEq (continuousAt_const (y := (0 : ℝ)))
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
    simp [hz q hq]
  · push_neg at hp
    have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le hs0 hp).ne'
    exact (continuous_fst.continuousAt.rpow_const (Or.inl hp0)).mul hG.continuousAt

/-- Compact-box integrability on `Ioi 0 ×ˢ B0579.cell c`. -/
theorem integrableOn_of_band {c s0 s1 L : ℝ} {F : Chart → ℝ} (hF : Continuous F)
    (hz : ∀ p : Chart, (p.1 < s0 ∨ s1 < p.1 ∨ L < |p.2.2|) → F p = 0) :
    IntegrableOn F (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  set K : Set Chart := Icc s0 s1 ×ˢ B0579.box c L
  have hK : IsCompact K := isCompact_Icc.prod (B0579.isCompact_box c L)
  refine (hF.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) ?_
  intro p hp
  apply hz p
  by_contra h
  push_neg at h
  exact hp.2 ⟨⟨h.1, h.2.1⟩, B0579.mem_box_of_mem_cell hp.1.2 h.2.2⟩

/-- Real and imaginary parts of `b · i`. -/
def uRe (b : Chart → Fin 2 → ℂ) (i : Fin 2) (p : Profile) : ℝ := (b p i).re
def uIm (b : Chart → Fin 2 → ℂ) (i : Fin 2) (p : Profile) : ℝ := (b p i).im

theorem contDiff_uRe {b : Chart → Fin 2 → ℂ} {i : Fin 2}
    (hb : ContDiff ℝ ∞ (fun p : Chart => b p i)) : ContDiff ℝ ∞ (uRe b i) :=
  Complex.reCLM.contDiff.comp hb

theorem contDiff_uIm {b : Chart → Fin 2 → ℂ} {i : Fin 2}
    (hb : ContDiff ℝ ∞ (fun p : Chart => b p i)) : ContDiff ℝ ∞ (uIm b i) :=
  Complex.imCLM.contDiff.comp hb

/-- Coordinate/real-part commutation for `pdS`, `pdQ`, `pdEta` on `zetaCut S R b`. -/
theorem resolventTest_zetaCut_re_im (ν μ S R : ℝ) {b : Chart → Fin 2 → ℂ}
    (hb : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Chart => b p i)) (p : Profile) (i : Fin 2) :
    (resolventTest ν μ (zetaCut S R b) p i).re = scalarResolvent ν μ S R (uRe b i) p ∧
    (resolventTest ν μ (zetaCut S R b) p i).im = scalarResolvent ν μ S R (uIm b i) p := by
  have hζs : ContDiff ℝ ∞ (zetaCut S R b) :=
    (((contDiff_thetaS S).comp contDiff_fst).mul
      ((contDiff_chiR R).comp (contDiff_snd.comp contDiff_snd))).smul (contDiff_bm hb)
  have hζd : Differentiable ℝ (zetaCut S R b) := hζs.differentiable (by simp)
  have hre_eq : (fun q : Profile => (zetaCut S R b q i).re) = fCut S R (uRe b i) := by
    funext q; simp [zetaCut, bm, fCut, uRe, Complex.real_smul]
  have him_eq : (fun q : Profile => (zetaCut S R b q i).im) = fCut S R (uIm b i) := by
    funext q; simp [zetaCut, bm, fCut, uIm, Complex.real_smul]
  have hdir1 : ∀ (v : Profile) (q : Profile),
      (fderiv ℝ (zetaCut S R b) q v i).re = fderiv ℝ (fCut S R (uRe b i)) q v ∧
      (fderiv ℝ (zetaCut S R b) q v i).im = fderiv ℝ (fCut S R (uIm b i)) q v := by
    intro v q
    have hqi : DifferentiableAt ℝ (fun r : Profile => zetaCut S R b r i) q := by
      let L : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ
      exact L.differentiableAt.comp q (hζd q)
    rw [fderiv_coord' (hζd q) v i, ← hre_eq, ← him_eq]
    exact ⟨(fderiv_clm_comp' Complex.reCLM hqi v).symm,
      (fderiv_clm_comp' Complex.imCLM hqi v).symm⟩
  have hdir2 : ∀ (v : Profile),
      (fderiv ℝ (fun q => fderiv ℝ (zetaCut S R b) q v) p v i).re =
        fderiv ℝ (fun q => fderiv ℝ (fCut S R (uRe b i)) q v) p v ∧
      (fderiv ℝ (fun q => fderiv ℝ (zetaCut S R b) q v) p v i).im =
        fderiv ℝ (fun q => fderiv ℝ (fCut S R (uIm b i)) q v) p v := by
    intro v
    have hd1 : Differentiable ℝ (fun q => fderiv ℝ (zetaCut S R b) q v) :=
      contDiff_fderiv_dir' hζs v
    have hpi : DifferentiableAt ℝ (fun q : Profile => fderiv ℝ (zetaCut S R b) q v i) p := by
      let L : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ
      exact L.differentiableAt.comp p (hd1 p)
    have hre1 : (fun q : Profile => (fderiv ℝ (zetaCut S R b) q v i).re) =
        fun q => fderiv ℝ (fCut S R (uRe b i)) q v := funext fun q => (hdir1 v q).1
    have him1 : (fun q : Profile => (fderiv ℝ (zetaCut S R b) q v i).im) =
        fun q => fderiv ℝ (fCut S R (uIm b i)) q v := funext fun q => (hdir1 v q).2
    rw [fderiv_coord' (hd1 p) v i, ← hre1, ← him1]
    exact ⟨(fderiv_clm_comp' Complex.reCLM hpi v).symm,
      (fderiv_clm_comp' Complex.imCLM hpi v).symm⟩
  unfold resolventTest A0adj scalarResolvent pdS pdQ pdEta
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  rw [(hdir1 (1, 0, 0) p).1, (hdir1 (1, 0, 0) p).2,
    (hdir2 (0, 1, 0)).1, (hdir2 (0, 1, 0)).2,
    (hdir2 (0, 0, 1)).1, (hdir2 (0, 0, 1)).2]
  have hre_p := congr_fun hre_eq p
  have him_p := congr_fun him_eq p
  dsimp only at hre_p him_p
  rw [hre_p, him_p]
  constructor <;> ring

theorem inner_resolventTest_zetaCut_re (ν μ S R : ℝ) {b : Chart → Fin 2 → ℂ}
    (hb : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Chart => b p i)) (p : Profile) :
    (inner ℂ (resolventTest ν μ (zetaCut S R b) p) (bm b p)).re =
      ∑ i : Fin 2,
        (scalarResolvent ν μ S R (uRe b i) p * uRe b i p +
         scalarResolvent ν μ S R (uIm b i) p * uIm b i p) := by
  rw [PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨hre, him⟩ := resolventTest_zetaCut_re_im ν μ S R hb p i
  simp only [bm, WithLp.ofLp_toLp, RCLike.inner_apply, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  rw [← hre, ← him]
  unfold uRe uIm
  ring

theorem vnorm2_sq_eq_sum_uRe_uIm (b : Chart → Fin 2 → ℂ) (p : Chart) :
    vnorm2 (b p) ^ 2 = ∑ i : Fin 2, (uRe b i p ^ 2 + uIm b i p ^ 2) := by
  unfold vnorm2 uRe uIm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem cellGrad_re_im {b : Chart → Fin 2 → ℂ}
    (hb : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Chart => b p i)) (p : Chart) (i j : Fin 2) :
    (cellGrad b p i j).re = B0579.pd j (fun y => uRe b i (p.1, y)) p.2 ∧
    (cellGrad b p i j).im = B0579.pd j (fun y => uIm b i (p.1, y)) p.2 := by
  have hs : ContDiff ℝ ∞ (fun y : ℝ × ℝ => b (p.1, y) i) :=
    (hb i).comp (contDiff_const.prodMk contDiff_id)
  have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ => b (p.1, y) i) p.2 :=
    (hs.differentiable (by simp)) p.2
  unfold cellGrad B0579.pd uRe uIm
  exact ⟨(fderiv_clm_comp' Complex.reCLM hd (B0579.dir j)).symm,
    (fderiv_clm_comp' Complex.imCLM hd (B0579.dir j)).symm⟩

theorem tnorm2_cellGrad_sq_eq_sum_uRe_uIm {b : Chart → Fin 2 → ℂ}
    (hb : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p : Chart => b p i)) (p : Chart) :
    tnorm2 (fun i j => cellGrad b p i j) ^ 2 =
      ∑ i : Fin 2,
        ((B0579.pd 0 (fun y => uRe b i (p.1, y)) p.2 ^ 2 +
          B0579.pd 1 (fun y => uRe b i (p.1, y)) p.2 ^ 2) +
         (B0579.pd 0 (fun y => uIm b i (p.1, y)) p.2 ^ 2 +
          B0579.pd 1 (fun y => uIm b i (p.1, y)) p.2 ^ 2)) := by
  unfold tnorm2
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  obtain ⟨h0r, h0i⟩ := cellGrad_re_im hb p i 0
  obtain ⟨h1r, h1i⟩ := cellGrad_re_im hb p i 1
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
    h0r, h0i, h1r, h1i]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
