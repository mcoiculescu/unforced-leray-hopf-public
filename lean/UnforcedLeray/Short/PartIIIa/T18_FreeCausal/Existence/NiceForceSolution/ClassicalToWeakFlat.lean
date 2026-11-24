import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4

/-!
# Part III-a, task `PartIII-a:T18/2/4/3` (`ClassicalToWeakFlat`): classical to weak

Proves `ClassicalToWeakFlat` (`Sub/T18_2_4.lean`, SP 3427-3440; source of record
`the November 2 reference manuscript`, lines 3427-3440).

The proof works on the joint domain `ℝ × (ℝ × ℝ)` with the joint partial derivatives
`cwDt f = ∂_s f` and `cwDx j f = ∂_{x_j} f` (`fderiv` in the directions `(1, 0)` and
`(0, dir j)`). For `s > 0` the integrand of `flatIntegrand` (with `vel = 0`) splits pointwise as
`-∂_s (Σ_i u_i Φ_i) + Σ_{i,j} ∂_{x_j} K_{ij}` plus `Φ_i` times the classical residual, and the
residual vanishes by `IsClassicalFlatSol`. The `x`-divergences integrate to zero on each slice
(periodicity and `η`-compactness, `cw_cell_pdC`), and `∫_{s>0} ∂_s G = 0` by the fundamental
theorem of calculus in `s` and Fubini. Integrability comes from continuity and vanishing on the
open set `cwV`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## Joint partial derivatives and the auxiliary functions -/

/-- The joint domain `(s, (q, η))`. -/
abbrev CwPt : Type := ℝ × (ℝ × ℝ)

/-- The complex cast of the `i`-th component of a real space-time test function. -/
def cwPhi (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2) (p : CwPt) : ℂ :=
  ((Φ p.1 p.2 i : ℝ) : ℂ)

/-- The joint `s`-derivative `∂_s f`. -/
def cwDt (f : CwPt → ℂ) (p : CwPt) : ℂ :=
  fderiv ℝ f p (1, 0)

/-- The joint `x`-partial derivative `∂_{x_j} f` (`j = 0`: `q`, `j = 1`: `η`). -/
def cwDx (j : Fin 2) (f : CwPt → ℂ) (p : CwPt) : ℂ :=
  fderiv ℝ f p (0, B0579.dir j)

/-- The cross term `-ν (a ∂_j b - b ∂_j a) + g b` of the Green identity. -/
def cwK (ν : ℝ) (a b g : CwPt → ℂ) (j : Fin 2) (p : CwPt) : ℂ :=
  -(ν : ℂ) * (a p * cwDx j b p - b p * cwDx j a p) + g p * b p

/-- The integrand after the pointwise splitting: `-∂_s (a b)` plus the `x`-divergences
`∂_{x_j} (cwK ν a b g_j j)`. -/
def cwT (ν : ℝ) (a b g0 g1 : CwPt → ℂ) (p : CwPt) : ℂ :=
  -(cwDt (fun q => a q * b q) p) + (cwDx 0 (cwK ν a b g0 0) p + cwDx 1 (cwK ν a b g1 1) p)

/-- The open set `{s < s₁} ∪ {s₂ < s} ∪ {R < |η|}` outside which the test vanishes. -/
def cwV (s1 s2 R : ℝ) : Set CwPt :=
  {p | p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|}

theorem mem_cwV {s1 s2 R : ℝ} {p : CwPt} :
    p ∈ cwV s1 s2 R ↔ p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2| :=
  Iff.rfl

theorem cwV_open (s1 s2 R : ℝ) : IsOpen (cwV s1 s2 R) := by
  have h1 : IsOpen {p : CwPt | p.1 < s1} := isOpen_lt continuous_fst continuous_const
  have h2 : IsOpen {p : CwPt | s2 < p.1} := isOpen_lt continuous_const continuous_fst
  have h3 : IsOpen {p : CwPt | R < |p.2.2|} :=
    isOpen_lt continuous_const (continuous_snd.snd.abs)
  have e : cwV s1 s2 R =
      {p : CwPt | p.1 < s1} ∪ ({p : CwPt | s2 < p.1} ∪ {p : CwPt | R < |p.2.2|}) := by
    ext p
    simp [cwV, or_assoc]
  rw [e]
  exact h1.union (h2.union h3)

/-! ## Calculus -/

theorem cw_diff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem cw_contDiff_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ ∞ f) (v : E) :
    ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  ((contDiff_infty_iff_fderiv.1 hf).2).clm_apply contDiff_const

theorem cw_dt_contDiff {f : CwPt → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cwDt f) :=
  cw_contDiff_fderiv hf _

theorem cw_dx_contDiff {f : CwPt → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    ContDiff ℝ ∞ (cwDx j f) :=
  cw_contDiff_fderiv hf _

theorem cw_slice_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : CwPt → F} (hf : ContDiff ℝ ∞ f) (s : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => f (s, y)) := by
  have h : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((s, y) : CwPt)) := contDiff_const.prodMk contDiff_id
  exact hf.comp h

theorem cw_hasDerivAt_t {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : CwPt → E} (hf : Differentiable ℝ f) (s : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => f (t, x)) (fderiv ℝ f (s, x) (1, 0)) s := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, x) : CwPt)) ((1, 0) : CwPt) s :=
    (hasDerivAt_id' s).prodMk (hasDerivAt_const s x)
  exact (hf (s, x)).hasFDerivAt.comp_hasDerivAt s h1

theorem cw_pdC_slice {f : CwPt → ℂ} (hf : Differentiable ℝ f) (s : ℝ) (x : ℝ × ℝ) (j : Fin 2) :
    pdC j (fun y => f (s, y)) x = cwDx j f (s, x) := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => ((s, y) : CwPt))
      (ContinuousLinearMap.prod (0 : ℝ × ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have h2 := (hf (s, x)).hasFDerivAt.comp x h1
  unfold pdC cwDx
  rw [show (fun y : ℝ × ℝ => f (s, y)) = f ∘ (fun y : ℝ × ℝ => ((s, y) : CwPt)) from rfl,
    h2.fderiv]
  simp

theorem cw_lap_slice {f : CwPt → ℂ} (hf : ContDiff ℝ ∞ f) (s : ℝ) (x : ℝ × ℝ) :
    lapC (fun y => f (s, y)) x = cwDx 0 (cwDx 0 f) (s, x) + cwDx 1 (cwDx 1 f) (s, x) := by
  have e0 : pdC 0 (fun y => f (s, y)) = fun y => cwDx 0 f (s, y) :=
    funext fun y => cw_pdC_slice (cw_diff hf) s y 0
  have e1 : pdC 1 (fun y => f (s, y)) = fun y => cwDx 1 f (s, y) :=
    funext fun y => cw_pdC_slice (cw_diff hf) s y 1
  unfold lapC
  rw [e0, e1, cw_pdC_slice (cw_diff (cw_dx_contDiff hf 0)) s x 0,
    cw_pdC_slice (cw_diff (cw_dx_contDiff hf 1)) s x 1]

theorem cw_R2C_pd {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (j : Fin 2) (x : ℝ × ℝ) :
    ((B0579.pd j φ x : ℝ) : ℂ) = pdC j (fun z => ((φ z : ℝ) : ℂ)) x := by
  unfold B0579.pd pdC
  have h := Complex.ofRealCLM.hasFDerivAt.comp x (hφ x).hasFDerivAt
  rw [show (fun z => ((φ z : ℝ) : ℂ)) = Complex.ofRealCLM ∘ φ from rfl, h.fderiv]
  simp

theorem cw_fd_mul {f h : CwPt → ℂ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (p v : CwPt) :
    fderiv ℝ (fun q => f q * h q) p v = f p * fderiv ℝ h p v + h p * fderiv ℝ f p v := by
  rw [fderiv_fun_mul (hf p) (hh p)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem cw_fd_add {f h : CwPt → ℂ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (p v : CwPt) :
    fderiv ℝ (fun q => f q + h q) p v = fderiv ℝ f p v + fderiv ℝ h p v := by
  rw [show (fun q => f q + h q) = f + h from rfl, fderiv_add (hf p) (hh p)]
  simp only [ContinuousLinearMap.add_apply]

theorem cw_fd_sub {f h : CwPt → ℂ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (p v : CwPt) :
    fderiv ℝ (fun q => f q - h q) p v = fderiv ℝ f p v - fderiv ℝ h p v := by
  rw [show (fun q => f q - h q) = f - h from rfl, fderiv_sub (hf p) (hh p)]
  simp only [ContinuousLinearMap.sub_apply]

theorem cw_fd_const_mul {f : CwPt → ℂ} (hf : Differentiable ℝ f) (k : ℂ) (p v : CwPt) :
    fderiv ℝ (fun q => k * f q) p v = k * fderiv ℝ f p v := by
  rw [fderiv_const_mul (hf p) k]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem cwDt_mul {f h : CwPt → ℂ} (hf : Differentiable ℝ f) (hh : Differentiable ℝ h)
    (p : CwPt) :
    cwDt (fun q => f q * h q) p = f p * cwDt h p + h p * cwDt f p :=
  cw_fd_mul hf hh p (1, 0)

theorem cwDx_mul (j : Fin 2) {f h : CwPt → ℂ} (hf : Differentiable ℝ f)
    (hh : Differentiable ℝ h) (p : CwPt) :
    cwDx j (fun q => f q * h q) p = f p * cwDx j h p + h p * cwDx j f p :=
  cw_fd_mul hf hh p (0, B0579.dir j)

theorem cwDx_add (j : Fin 2) {f h : CwPt → ℂ} (hf : Differentiable ℝ f)
    (hh : Differentiable ℝ h) (p : CwPt) :
    cwDx j (fun q => f q + h q) p = cwDx j f p + cwDx j h p :=
  cw_fd_add hf hh p (0, B0579.dir j)

theorem cwDx_sub (j : Fin 2) {f h : CwPt → ℂ} (hf : Differentiable ℝ f)
    (hh : Differentiable ℝ h) (p : CwPt) :
    cwDx j (fun q => f q - h q) p = cwDx j f p - cwDx j h p :=
  cw_fd_sub hf hh p (0, B0579.dir j)

theorem cwDx_const_mul (j : Fin 2) (k : ℂ) {f : CwPt → ℂ} (hf : Differentiable ℝ f)
    (p : CwPt) :
    cwDx j (fun q => k * f q) p = k * cwDx j f p :=
  cw_fd_const_mul hf k p (0, B0579.dir j)

/-! ## The pointwise splitting of the integrand -/

theorem cw_K_deriv (ν : ℝ) {a b g : CwPt → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hg : ContDiff ℝ ∞ g) (j : Fin 2) (p : CwPt) :
    cwDx j (cwK ν a b g j) p =
      -(ν : ℂ) * (cwDx j a p * cwDx j b p + a p * cwDx j (cwDx j b) p -
        (cwDx j b p * cwDx j a p + b p * cwDx j (cwDx j a) p)) +
      (cwDx j g p * b p + g p * cwDx j b p) := by
  have ha' : Differentiable ℝ a := cw_diff ha
  have hb' : Differentiable ℝ b := cw_diff hb
  have hg' : Differentiable ℝ g := cw_diff hg
  have hDa : Differentiable ℝ (cwDx j a) := cw_diff (cw_dx_contDiff ha j)
  have hDb : Differentiable ℝ (cwDx j b) := cw_diff (cw_dx_contDiff hb j)
  have hm1 : Differentiable ℝ (fun q => a q * cwDx j b q) := ha'.mul hDb
  have hm2 : Differentiable ℝ (fun q => b q * cwDx j a q) := hb'.mul hDa
  have hs : Differentiable ℝ (fun q => a q * cwDx j b q - b q * cwDx j a q) := hm1.sub hm2
  have hK1 : Differentiable ℝ (fun q => -(ν : ℂ) * (a q * cwDx j b q - b q * cwDx j a q)) :=
    hs.const_mul _
  have hK2 : Differentiable ℝ (fun q => g q * b q) := hg'.mul hb'
  unfold cwK
  rw [cwDx_add j hK1 hK2 p, cwDx_const_mul j (-(ν : ℂ)) hs p, cwDx_sub j hm1 hm2 p,
    cwDx_mul j ha' hDb p, cwDx_mul j hb' hDa p, cwDx_mul j hg' hb' p]
  ring

theorem cw_pointwise (ν : ℝ) (μ : ℂ) {a b g0 g1 : CwPt → ℂ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hg0 : ContDiff ℝ ∞ g0) (hg1 : ContDiff ℝ ∞ g1) (p : CwPt) :
    -(a p * cwDt b p) + (μ / (p.1 : ℂ)) * a p * b p -
        (ν : ℂ) * a p * (cwDx 0 (cwDx 0 b) p + cwDx 1 (cwDx 1 b) p) +
        (g0 p * cwDx 0 b p + g1 p * cwDx 1 b p) =
      cwT ν a b g0 g1 p + b p * (cwDt a p + (μ / (p.1 : ℂ)) * a p -
        (ν : ℂ) * (cwDx 0 (cwDx 0 a) p + cwDx 1 (cwDx 1 a) p) -
        (cwDx 0 g0 p + cwDx 1 g1 p)) := by
  unfold cwT
  rw [cwDt_mul (cw_diff ha) (cw_diff hb) p, cw_K_deriv ν ha hb hg0 0 p,
    cw_K_deriv ν ha hb hg1 1 p]
  ring

/-! ## Periodicity and smoothness of the auxiliary functions -/

theorem cw_per_Dx (c : ℝ) (j : Fin 2) {f : CwPt → ℂ}
    (hf : ∀ s x, f (s, (x.1 + c, x.2)) = f (s, x)) (s : ℝ) (x : ℝ × ℝ) :
    cwDx j f (s, (x.1 + c, x.2)) = cwDx j f (s, x) := by
  have hfun : (fun p : CwPt => f (p + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) = f := by
    funext p
    have e : p + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) = (p.1, (p.2.1 + c, p.2.2)) := by
      ext <;> simp
    rw [e]
    exact hf p.1 p.2
  have h1 : fderiv ℝ (fun p : CwPt => f (p + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) (s, x) =
      fderiv ℝ f ((s, x) + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) :=
    fderiv_comp_add_right _
  rw [hfun] at h1
  have e2 : ((s, x) + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) : CwPt) = (s, (x.1 + c, x.2)) := by
    ext <;> simp
  unfold cwDx
  rw [← e2, ← h1]

theorem cw_per_K (c ν : ℝ) (j : Fin 2) {a b g : CwPt → ℂ}
    (hpa : ∀ s x, a (s, (x.1 + c, x.2)) = a (s, x))
    (hpb : ∀ s x, b (s, (x.1 + c, x.2)) = b (s, x))
    (hpg : ∀ s x, g (s, (x.1 + c, x.2)) = g (s, x)) (s : ℝ) (x : ℝ × ℝ) :
    cwK ν a b g j (s, (x.1 + c, x.2)) = cwK ν a b g j (s, x) := by
  unfold cwK
  rw [hpa s x, hpb s x, hpg s x, cw_per_Dx c j hpb s x, cw_per_Dx c j hpa s x]

theorem cw_contDiff_K (ν : ℝ) {a b g : CwPt → ℂ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hg : ContDiff ℝ ∞ g) (j : Fin 2) : ContDiff ℝ ∞ (cwK ν a b g j) := by
  unfold cwK
  exact (contDiff_const.mul ((ha.mul (cw_dx_contDiff hb j)).sub
    (hb.mul (cw_dx_contDiff ha j)))).add (hg.mul hb)

/-! ## Vanishing outside `cwV`, integrability and the slice integrals -/

theorem cw_fderiv_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {V : Set E} (hV : IsOpen V)
    (hg : ∀ p ∈ V, g p = 0) {p : E} (hp : p ∈ V) : fderiv ℝ g p = 0 := by
  have hev : g =ᶠ[𝓝 p] fun _ => (0 : F) := Filter.eventually_of_mem (hV.mem_nhds hp) hg
  rw [hev.fderiv_eq]
  simp

theorem cw_Dt_zero {f : CwPt → ℂ} {V : Set CwPt} (hV : IsOpen V) (hf : ∀ p ∈ V, f p = 0)
    {p : CwPt} (hp : p ∈ V) : cwDt f p = 0 := by
  unfold cwDt
  rw [cw_fderiv_zero hV hf hp]
  simp

theorem cw_Dx_zero {f : CwPt → ℂ} {V : Set CwPt} (hV : IsOpen V) (hf : ∀ p ∈ V, f p = 0)
    {p : CwPt} (hp : p ∈ V) (j : Fin 2) : cwDx j f p = 0 := by
  unfold cwDx
  rw [cw_fderiv_zero hV hf hp]
  simp

theorem cw_integrableOn_S (c s1 s2 R : ℝ) {g : CwPt → ℂ} (hg : Continuous g)
    (hv : ∀ p ∈ cwV s1 s2 R, g p = 0) :
    IntegrableOn g (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hK : IsCompact (Icc s1 s2 ×ˢ B0579.box c R) :=
    isCompact_Icc.prod (B0579.isCompact_box c R)
  refine (hg.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod (B0579.measurableSet_cell c)) ?_
  rintro p ⟨hp1, hp2⟩
  apply hv p
  by_contra hcon
  apply hp2
  have hcellp : p.2 ∈ B0579.cell c := (Set.mem_prod.1 hp1).2
  have hq : p.2.1 ∈ Ico (-(c / 2)) (c / 2) :=
    (show p.2 ∈ Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) from hcellp).1
  rw [mem_cwV] at hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  refine Set.mem_prod.2 ⟨⟨h1, h2⟩, ?_⟩
  show p.2.1 ∈ Icc (-(c / 2)) (c / 2) ∧ p.2.2 ∈ Icc (-R) R
  exact ⟨⟨hq.1, hq.2.le⟩, abs_le.mp h3⟩

theorem cw_integrableOn_cell (c : ℝ) {g : ℝ × ℝ → ℂ} (hg : Continuous g) {R : ℝ}
    (hv : ∀ x : ℝ × ℝ, R < |x.2| → g x = 0) : IntegrableOn g (B0579.cell c) := by
  refine (hg.continuousOn.integrableOn_compact (B0579.isCompact_box c R)).of_forall_sdiff_eq_zero
    (B0579.measurableSet_cell c) ?_
  rintro x ⟨hx1, hx2⟩
  apply hv x
  by_contra hcon
  apply hx2
  have hq : x.1 ∈ Ico (-(c / 2)) (c / 2) :=
    (show x ∈ Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) from hx1).1
  push_neg at hcon
  show x.1 ∈ Icc (-(c / 2)) (c / 2) ∧ x.2 ∈ Icc (-R) R
  exact ⟨⟨hq.1, hq.2.le⟩, abs_le.mp hcon⟩

theorem cw_hcs_s {f : CwPt → ℂ} (s1 s2 R : ℝ) (hv : ∀ p ∈ cwV s1 s2 R, f p = 0)
    (y : ℝ × ℝ) : HasCompactSupport (fun x : ℝ => f (x, y)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := s1) (b := s2)) fun x hx =>
    hv _ (mem_cwV.2 ?_)
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem cw_hcs_slice {ψ : ℝ × ℝ → ℂ} {R : ℝ} (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0)
    (q : ℝ) : HasCompactSupport (fun η : ℝ => ψ (q, η)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun η hη => hR _ ?_
  simp only [mem_Icc, not_and_or, not_le] at hη
  rcases hη with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs η)
  · exact lt_of_lt_of_le h (le_abs_self η)

theorem cw_cont_fst {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) (η : ℝ) :
    Continuous fun q : ℝ => ψ (q, η) :=
  hψ.comp (continuous_id.prodMk continuous_const)

theorem cw_cont_snd {ψ : ℝ × ℝ → ℂ} (hψ : Continuous ψ) (q : ℝ) :
    Continuous fun η : ℝ => ψ (q, η) :=
  hψ.comp (continuous_const.prodMk continuous_id)

theorem cw_cont_slice {f : CwPt → ℂ} (hf : Continuous f) (y : ℝ × ℝ) :
    Continuous fun x : ℝ => f (x, y) :=
  hf.comp (continuous_id.prodMk continuous_const)

/-! ### The cell integrals of `∂_q` and `∂_η` of a complex cylinder test -/

theorem cw_hasDerivAt_pl0 {ψ : ℝ × ℝ → ℂ} (hψ : Differentiable ℝ ψ) (q η : ℝ) :
    HasDerivAt (fun t : ℝ => ψ (t, η)) (pdC 0 ψ (q, η)) q := by
  have h1 : HasDerivAt (fun t : ℝ => ((t, η) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) q :=
    (hasDerivAt_id' q).prodMk (hasDerivAt_const q η)
  have h2 := (hψ (q, η)).hasFDerivAt.comp_hasDerivAt q h1
  simpa [pdC, B0579.dir, Function.comp_def] using h2

theorem cw_hasDerivAt_pl1 {ψ : ℝ × ℝ → ℂ} (hψ : Differentiable ℝ ψ) (q η : ℝ) :
    HasDerivAt (fun t : ℝ => ψ (q, t)) (pdC 1 ψ (q, η)) η := by
  have h1 : HasDerivAt (fun t : ℝ => ((q, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id' η)
  have h2 := (hψ (q, η)).hasFDerivAt.comp_hasDerivAt η h1
  simpa [pdC, B0579.dir, Function.comp_def] using h2

theorem cw_cell_pd0 {c : ℝ} {ψ : ℝ × ℝ → ℂ} (hsm : ContDiff ℝ ∞ ψ)
    (hper : ∀ x : ℝ × ℝ, ψ (x.1 + c, x.2) = ψ x) {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) :
    ∫ x in B0579.cell c, pdC 0 ψ x = 0 := by
  have hcont : Continuous (pdC 0 ψ) := (cw_contDiff_fderiv hsm (B0579.dir 0)).continuous
  have hvan : ∀ x : ℝ × ℝ, R < |x.2| → pdC 0 ψ x = 0 := by
    intro x hx
    have hV : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
    unfold pdC
    rw [cw_fderiv_zero hV (fun y hy => hR y hy) hx]
    simp
  have hint := cw_integrableOn_cell c hcont hvan
  unfold IntegrableOn at hint
  rw [B0579.cell, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun η => ?_)).trans (integral_zero _ _)
  by_cases hc : -(c / 2) ≤ c / 2
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hc,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun q _ => cw_hasDerivAt_pl0 (cw_diff hsm) q η)
        ((cw_cont_fst hcont η).intervalIntegrable _ _)]
    have h : ψ (-(c / 2) + c, η) = ψ (-(c / 2), η) := hper (-(c / 2), η)
    rw [show -(c / 2) + c = c / 2 by ring] at h
    rw [h, sub_self]
  · rw [Ico_eq_empty fun h => hc h.le, Measure.restrict_empty, integral_zero_measure]

theorem cw_cell_pd1 {c : ℝ} {ψ : ℝ × ℝ → ℂ} (hsm : ContDiff ℝ ∞ ψ) {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) :
    ∫ x in B0579.cell c, pdC 1 ψ x = 0 := by
  have hcont : Continuous (pdC 1 ψ) := (cw_contDiff_fderiv hsm (B0579.dir 1)).continuous
  have hvan : ∀ x : ℝ × ℝ, R < |x.2| → pdC 1 ψ x = 0 := by
    intro x hx
    have hV : IsOpen {y : ℝ × ℝ | R < |y.2|} := isOpen_lt continuous_const continuous_snd.abs
    unfold pdC
    rw [cw_fderiv_zero hV (fun y hy => hR y hy) hx]
    simp
  have hint := cw_integrableOn_cell c hcont hvan
  rw [B0579.cell, Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun q => ?_)).trans (integral_zero _ _)
  simp only [Measure.restrict_univ]
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun η => cw_hasDerivAt_pl1 (cw_diff hsm) q η)
    ((cw_cont_snd hcont q).integrable_of_hasCompactSupport (cw_hcs_slice hvan q))
    ((cw_cont_snd hsm.continuous q).integrable_of_hasCompactSupport (cw_hcs_slice hR q))

theorem cw_cell_pdC {c : ℝ} {ψ : ℝ × ℝ → ℂ} (hsm : ContDiff ℝ ∞ ψ)
    (hper : ∀ x : ℝ × ℝ, ψ (x.1 + c, x.2) = ψ x) {R : ℝ}
    (hR : ∀ x : ℝ × ℝ, R < |x.2| → ψ x = 0) (j : Fin 2) :
    ∫ x in B0579.cell c, pdC j ψ x = 0 := by
  fin_cases j
  · exact cw_cell_pd0 hsm hper hR
  · exact cw_cell_pd1 hsm hR

/-! ### Slice-integral and `s`-integral vanishing -/

theorem cw_setInt_Dx (c s1 s2 R : ℝ) (j : Fin 2) {H : CwPt → ℂ} (hH : ContDiff ℝ ∞ H)
    (hper : ∀ s x, H (s, (x.1 + c, x.2)) = H (s, x)) (hv : ∀ p ∈ cwV s1 s2 R, H p = 0) :
    IntegrableOn (cwDx j H) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, cwDx j H p = 0 := by
  have hcont : Continuous (cwDx j H) := (cw_dx_contDiff hH j).continuous
  have hdv : ∀ p ∈ cwV s1 s2 R, cwDx j H p = 0 :=
    fun p hp => cw_Dx_zero (cwV_open s1 s2 R) hv hp j
  have hint := cw_integrableOn_S c s1 s2 R hcont hdv
  refine ⟨hint, ?_⟩
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun s => ?_)).trans (integral_zero _ _)
  have hs : ContDiff ℝ ∞ (fun z : ℝ × ℝ => H (s, z)) := cw_slice_contDiff hH s
  have hR' : ∀ z : ℝ × ℝ, R < |z.2| → H (s, z) = 0 :=
    fun z hz => hv (s, z) (mem_cwV.2 (Or.inr (Or.inr hz)))
  have key : ∀ y : ℝ × ℝ, cwDx j H (s, y) = pdC j (fun z => H (s, z)) y := fun y =>
    (cw_pdC_slice (cw_diff hH) s y j).symm
  simp only [key]
  exact cw_cell_pdC hs (fun z => hper s z) hR' j

theorem cw_setInt_Dt (c s1 s2 R : ℝ) (hs1 : 0 < s1) {G : CwPt → ℂ} (hG : ContDiff ℝ ∞ G)
    (hv : ∀ p ∈ cwV s1 s2 R, G p = 0) :
    IntegrableOn (cwDt G) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, cwDt G p = 0 := by
  have hcont : Continuous (cwDt G) := (cw_dt_contDiff hG).continuous
  have hdv : ∀ p ∈ cwV s1 s2 R, cwDt G p = 0 :=
    fun p hp => cw_Dt_zero (cwV_open s1 s2 R) hv hp
  have hint := cw_integrableOn_S c s1 s2 R hcont hdv
  refine ⟨hint, ?_⟩
  unfold IntegrableOn at hint
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_zero _ _)
  have hfull : ∫ x in Ioi (0 : ℝ), cwDt G (x, y) = ∫ x : ℝ, cwDt G (x, y) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [mem_Ioi, not_lt] at hx
    exact cw_Dt_zero (cwV_open s1 s2 R) hv (mem_cwV.2 (Or.inl (lt_of_le_of_lt hx hs1)))
  rw [hfull]
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (f := fun x : ℝ => G (x, y)) (f' := fun x : ℝ => cwDt G (x, y))
    (fun x => cw_hasDerivAt_t (cw_diff hG) x y)
    ((cw_cont_slice hcont y).integrable_of_hasCompactSupport (cw_hcs_s s1 s2 R hdv y))
    ((cw_cont_slice hG.continuous y).integrable_of_hasCompactSupport (cw_hcs_s s1 s2 R hv y))

/-! ### The core statement for one component -/

theorem cw_core (c s1 s2 R ν : ℝ) (hs1 : 0 < s1) {a b g0 g1 : CwPt → ℂ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hg0 : ContDiff ℝ ∞ g0)
    (hg1 : ContDiff ℝ ∞ g1)
    (hpa : ∀ s x, a (s, (x.1 + c, x.2)) = a (s, x))
    (hpb : ∀ s x, b (s, (x.1 + c, x.2)) = b (s, x))
    (hpg0 : ∀ s x, g0 (s, (x.1 + c, x.2)) = g0 (s, x))
    (hpg1 : ∀ s x, g1 (s, (x.1 + c, x.2)) = g1 (s, x))
    (hvb : ∀ p ∈ cwV s1 s2 R, b p = 0) :
    IntegrableOn (cwT ν a b g0 g1) (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
      ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, cwT ν a b g0 g1 p = 0 := by
  have hG : ContDiff ℝ ∞ (fun q => a q * b q) := ha.mul hb
  have hGv : ∀ p ∈ cwV s1 s2 R, (fun q => a q * b q) p = 0 := fun p hp => by
    simp only [hvb p hp, mul_zero]
  obtain ⟨hI1, hZ1⟩ := cw_setInt_Dt c s1 s2 R hs1 hG hGv
  have hK0 : ContDiff ℝ ∞ (cwK ν a b g0 0) := cw_contDiff_K ν ha hb hg0 0
  have hK1 : ContDiff ℝ ∞ (cwK ν a b g1 1) := cw_contDiff_K ν ha hb hg1 1
  have hK0v : ∀ p ∈ cwV s1 s2 R, cwK ν a b g0 0 p = 0 := fun p hp => by
    simp [cwK, hvb p hp, cw_Dx_zero (cwV_open s1 s2 R) hvb hp 0]
  have hK1v : ∀ p ∈ cwV s1 s2 R, cwK ν a b g1 1 p = 0 := fun p hp => by
    simp [cwK, hvb p hp, cw_Dx_zero (cwV_open s1 s2 R) hvb hp 1]
  obtain ⟨hI2, hZ2⟩ := cw_setInt_Dx c s1 s2 R 0 hK0
    (fun s x => cw_per_K c ν 0 hpa hpb hpg0 s x) hK0v
  obtain ⟨hI3, hZ3⟩ := cw_setInt_Dx c s1 s2 R 1 hK1
    (fun s x => cw_per_K c ν 1 hpa hpb hpg1 s x) hK1v
  have hA : IntegrableOn (fun p => -cwDt (fun q => a q * b q) p) (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    hI1.neg
  have hB : IntegrableOn (fun p => cwDx 0 (cwK ν a b g0 0) p + cwDx 1 (cwK ν a b g1 1) p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := hI2.add hI3
  refine ⟨hA.add hB, ?_⟩
  unfold cwT
  rw [integral_add hA hB, integral_neg, integral_add hI2 hI3, hZ1, hZ2, hZ3]
  simp

/-! ## Casts of the real flat test functions -/

theorem cw_cast_dt (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2)
    (hΦi : ContDiff ℝ ∞ (fun p : CwPt => Φ p.1 p.2 i)) (s : ℝ) (x : ℝ × ℝ) :
    ((flatDt Φ s x i : ℝ) : ℂ) = cwDt (cwPhi Φ i) (s, x) := by
  have hR : Differentiable ℝ (fun p : CwPt => Φ p.1 p.2 i) := cw_diff hΦi
  have hreal : HasDerivAt (fun t : ℝ => Φ t x i)
      (fderiv ℝ (fun p : CwPt => Φ p.1 p.2 i) (s, x) (1, 0)) s :=
    cw_hasDerivAt_t hR s x
  have hC : HasDerivAt (fun t : ℝ => ((Φ t x i : ℝ) : ℂ))
      ((fderiv ℝ (fun p : CwPt => Φ p.1 p.2 i) (s, x) (1, 0) : ℝ) : ℂ) s := hreal.ofReal_comp
  have hcC : ContDiff ℝ ∞ (cwPhi Φ i) := Complex.ofRealCLM.contDiff.comp hΦi
  have h1 : HasDerivAt (fun t : ℝ => cwPhi Φ i (t, x)) (cwDt (cwPhi Φ i) (s, x)) s :=
    cw_hasDerivAt_t (cw_diff hcC) s x
  have key : ((fderiv ℝ (fun p : CwPt => Φ p.1 p.2 i) (s, x) (1, 0) : ℝ) : ℂ) =
      cwDt (cwPhi Φ i) (s, x) :=
    hC.unique h1
  rw [← key]
  congr 1
  exact hreal.deriv

theorem cw_cast_grad (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2)
    (hΦi : ContDiff ℝ ∞ (fun p : CwPt => Φ p.1 p.2 i)) (j : Fin 2) (s : ℝ) (x : ℝ × ℝ) :
    ((flatGrad Φ s x i j : ℝ) : ℂ) = cwDx j (cwPhi Φ i) (s, x) := by
  have hcC : ContDiff ℝ ∞ (cwPhi Φ i) := Complex.ofRealCLM.contDiff.comp hΦi
  have hφ : Differentiable ℝ (fun y : ℝ × ℝ => Φ s y i) :=
    cw_diff (cw_slice_contDiff hΦi s)
  rw [← cw_pdC_slice (cw_diff hcC) s x j]
  unfold flatGrad
  exact cw_R2C_pd hφ j x

theorem cw_cast_lap (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i : Fin 2)
    (hΦi : ContDiff ℝ ∞ (fun p : CwPt => Φ p.1 p.2 i)) (s : ℝ) (x : ℝ × ℝ) :
    ((flatLap Φ s x i : ℝ) : ℂ) =
      cwDx 0 (cwDx 0 (cwPhi Φ i)) (s, x) + cwDx 1 (cwDx 1 (cwPhi Φ i)) (s, x) := by
  have hcC : ContDiff ℝ ∞ (cwPhi Φ i) := Complex.ofRealCLM.contDiff.comp hΦi
  have hφs : ContDiff ℝ ∞ (fun y : ℝ × ℝ => Φ s y i) := cw_slice_contDiff hΦi s
  have hφ : Differentiable ℝ (fun y : ℝ × ℝ => Φ s y i) := cw_diff hφs
  have hpd : ∀ j : Fin 2, Differentiable ℝ (B0579.pd j (fun y : ℝ × ℝ => Φ s y i)) :=
    fun j => cw_diff (cw_contDiff_fderiv hφs (B0579.dir j))
  have hin : ∀ j : Fin 2,
      (fun z : ℝ × ℝ => ((B0579.pd j (fun y : ℝ × ℝ => Φ s y i) z : ℝ) : ℂ)) =
        fun z => pdC j (fun w => ((Φ s w i : ℝ) : ℂ)) z :=
    fun j => funext fun z => cw_R2C_pd hφ j z
  unfold flatLap lapP
  rw [Complex.ofReal_add, cw_R2C_pd (hpd 0) 0 x, cw_R2C_pd (hpd 1) 1 x, hin 0, hin 1]
  exact cw_lap_slice hcC s x

/-! ## Assembly -/

theorem classicalToWeakFlat : ClassicalToWeakFlat := by
  intro c ν μ hc F hF u hus hup hcl Φ hΦ
  obtain ⟨_, hFs, hFp, _⟩ := hF
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  have hΦs : ∀ i : Fin 2, ContDiff ℝ ∞ (cwPhi Φ i) := fun i =>
    Complex.ofRealCLM.contDiff.comp (hΦ.smooth i)
  have hΦp : ∀ (i : Fin 2) (s : ℝ) (x : ℝ × ℝ),
      cwPhi Φ i (s, (x.1 + c, x.2)) = cwPhi Φ i (s, x) := fun i s x => by
    simp only [cwPhi, hΦ.periodic]
  have hΦV : ∀ i : Fin 2, ∀ p ∈ cwV s1 s2 R, cwPhi Φ i p = 0 := fun i p hp => by
    simp only [cwPhi, hsupp p.1 p.2 i (mem_cwV.1 hp), Complex.ofReal_zero]
  have hI : ∀ i : Fin 2,
      IntegrableOn (cwT ν (fun q => u q i) (cwPhi Φ i) (fun q => F q i 0) (fun q => F q i 1))
          (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
        ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c,
          cwT ν (fun q => u q i) (cwPhi Φ i) (fun q => F q i 0) (fun q => F q i 1) p = 0 :=
    fun i => cw_core c s1 s2 R ν hs1 (hus i) (hΦs i) (hFs i 0) (hFs i 1)
      (fun s x => hup s x i) (fun s x => hΦp i s x)
      (fun s x => hFp s x i 0) (fun s x => hFp s x i 1) (hΦV i)
  -- the classical residual of component `i`, at a point with `s > 0`
  have hres : ∀ (i : Fin 2) (s : ℝ) (x : ℝ × ℝ), 0 < s →
      cwDt (fun q => u q i) (s, x) + (μ / (s : ℂ)) * u (s, x) i -
        (ν : ℂ) * (cwDx 0 (cwDx 0 (fun q => u q i)) (s, x) +
          cwDx 1 (cwDx 1 (fun q => u q i)) (s, x)) -
        (cwDx 0 (fun q => F q i 0) (s, x) + cwDx 1 (fun q => F q i 1) (s, x)) = 0 := by
    intro i s x hs
    have hd := hcl s hs x i
    have e1 : deriv (fun s' => u (s', x) i) s = cwDt (fun q => u q i) (s, x) :=
      (cw_hasDerivAt_t (cw_diff (hus i)) s x).deriv
    have e2 : lapC (fun y => u (s, y) i) x =
        cwDx 0 (cwDx 0 (fun q => u q i)) (s, x) + cwDx 1 (cwDx 1 (fun q => u q i)) (s, x) :=
      cw_lap_slice (hus i) s x
    have e3 : ∀ j : Fin 2, pdC j (fun y => F (s, y) i j) x =
        cwDx j (fun q => F q i j) (s, x) :=
      fun j => cw_pdC_slice (cw_diff (hFs i j)) s x j
    rw [e1, e2] at hd
    simp only [e3, Fin.sum_univ_two] at hd
    linear_combination hd
  have hpt : ∀ p : CwPt, 0 < p.1 →
      flatIntegrand ν μ (fun _ _ _ => 0) F u Φ p =
        cwT ν (fun q => u q 0) (cwPhi Φ 0) (fun q => F q 0 0) (fun q => F q 0 1) p +
        cwT ν (fun q => u q 1) (cwPhi Φ 1) (fun q => F q 1 0) (fun q => F q 1 1) p := by
    rintro ⟨s, x⟩ hs
    have hs' : 0 < s := hs
    have k0 := cw_pointwise ν μ (hus 0) (hΦs 0) (hFs 0 0) (hFs 0 1) (s, x)
    have k1 := cw_pointwise ν μ (hus 1) (hΦs 1) (hFs 1 0) (hFs 1 1) (s, x)
    dsimp only at k0 k1
    have r0 := hres 0 s x hs'
    have r1 := hres 1 s x hs'
    have c0 : ((Φ s x 0 : ℝ) : ℂ) = cwPhi Φ 0 (s, x) := rfl
    have c1 : ((Φ s x 1 : ℝ) : ℂ) = cwPhi Φ 1 (s, x) := rfl
    unfold flatIntegrand
    dsimp only
    simp only [Fin.sum_univ_two, Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero]
    rw [cw_cast_dt Φ 0 (hΦ.smooth 0) s x, cw_cast_dt Φ 1 (hΦ.smooth 1) s x,
      cw_cast_lap Φ 0 (hΦ.smooth 0) s x, cw_cast_lap Φ 1 (hΦ.smooth 1) s x,
      cw_cast_grad Φ 0 (hΦ.smooth 0) 0 s x, cw_cast_grad Φ 0 (hΦ.smooth 0) 1 s x,
      cw_cast_grad Φ 1 (hΦ.smooth 1) 0 s x, cw_cast_grad Φ 1 (hΦ.smooth 1) 1 s x, c0, c1]
    linear_combination k0 + k1 + cwPhi Φ 0 (s, x) * r0 + cwPhi Φ 1 (s, x) * r1
  have hS : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  refine ⟨?_, ?_⟩
  · exact IntegrableOn.congr_fun ((hI 0).1.add (hI 1).1)
      (fun p hp => (hpt p (Set.mem_Ioi.1 (Set.mem_prod.1 hp).1)).symm) hS
  · rw [setIntegral_congr_fun hS (fun p hp => hpt p (Set.mem_Ioi.1 (Set.mem_prod.1 hp).1)),
      integral_add (hI 0).1 (hI 1).1, (hI 0).2, (hI 1).2, add_zero]

end UnforcedLeray.Short.IIIa
