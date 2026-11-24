import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Leray
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayFieldProps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LerayPartBasic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FinModeProj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.TruncTendsto
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.AeLimitOfLp

/-!
# Sub `PartII-a_N04_2_1`: Smooth Band-Supported Representative of `PepsC 0 c Z` (`FlatLeraySmoothRep`)

Source of record: `the November 2 reference manuscript`,
lines 1723–1726 and 1800–1823 (Lemma `near:adjoint-polynomial`).

This file provides:
1. Construction of the smooth flat Leray projection representative `flatLerayRep c z` by splitting
   `z : Profile → MeridC` into real and imaginary force fields (`meridReField z`, `meridImField z`)
   and applying `lerayField c` (`PartIII-b_C_flatset_col_7_1_1_2_1`).
2. Unconditional proofs of:
   - `flatLerayRep_smooth`: `ContDiff ℝ ∞ (flatLerayRep c z)`
   - `flatLerayRep_periodic`: `QPeriodic c (flatLerayRep c z)`
   - `flatLerayRep_support_s`: `flatLerayRep c z p = 0` for `p.1 < σ ∨ H1 < p.1`, together with
     vanishing of `opS^[a] (flatLerayRep c z)` and `iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z))`
     outside `[σ, H1]`
   - `pepsC_ae_eq_flatLerayRep`: `(PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] flatLerayRep c z`
   - `pepsC_ae_eq_lerayPart`: `(PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] FlatLeray.lerayPart c z`
     (hence `flatLerayRep c z =ᵐ[measureH c] FlatLeray.lerayPart c z`).
3. Proof that exponential `η`-decay of `iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z))`
   (`FlatLerayIterDecay`) implies both `bounded_moments` and `integrable_moments` of
   `IsFlatLerayRep c σ H1 (flatLerayRep c z)` via `memLpOfDecay`.
4. Reduction `flatLeraySmoothRep_of` of `FlatLeraySmoothRep` to two leaf obligations:
   - `FlatLerayIterDecay` (`PartII-a:N04/2/1/1`): exponential decay in `|η|` of
     `iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z))` for `a < 2`, `m < 5`.
   - `FlatLerayMomentNormBound` (`PartII-a:N04/2/1/2`): quantitative `L²(measureH c)`
     moment/derivative bound
     `flatProjMomentNorm c (flatLerayRep c z) ≤ C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * h6Norm c z`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
open UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

/-! ### 1. Real/imaginary splitting and concrete smooth representative `flatLerayRep` -/

/-- Real part of a meridional profile as a real chart force field. -/
def meridReField (z : Profile → MeridC) (p : Profile) (i : Fin 2) : ℝ :=
  (z p i).re

/-- Imaginary part of a meridional profile as a real chart force field. -/
def meridImField (z : Profile → MeridC) (p : Profile) (i : Fin 2) : ℝ :=
  (z p i).im

/-- Smooth flat Leray representative of a meridional test `z`, built from the cylinder Green-kernel
projection `lerayField c` applied to the real and imaginary parts of `z`. -/
def flatLerayRep (c : ℝ) (z : Profile → MeridC) (p : Profile) : MeridC :=
  cvec (lerayField c (meridReField z) p) +
    Complex.I • cvec (lerayField c (meridImField z) p)

theorem cvec_re_add_im (z : Profile → MeridC) (p : Profile) :
    cvec (meridReField z p) + Complex.I • cvec (meridImField z p) = z p := by
  ext i
  simp only [cvec, meridReField, meridImField, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im (z p i)

theorem isForceField_meridReField {c σ H1 L1 : ℝ} (hσ : 0 < σ) {z : Profile → MeridC}
    (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    IsForceField c (meridReField z) := by
  refine ⟨fun i => ?_, fun s q η => ?_, ⟨σ, H1, L1, hσ, fun p hp => ?_⟩⟩
  · have hproj : ContDiff ℝ ∞ (fun p : Profile => z p i) :=
      ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hz.smooth
    exact Complex.reCLM.contDiff.comp hproj
  · funext i
    have hper := hz.periodic (s, q, η)
    exact congrArg (fun w : MeridC => (w i).re) hper
  · have hz0 : z p ≠ 0 := by
      intro h0
      apply hp
      funext i
      simp [meridReField, h0]
    obtain ⟨h1, h2, h3⟩ := hsupp p hz0
    exact ⟨⟨h1, h2⟩, h3⟩

theorem isForceField_meridImField {c σ H1 L1 : ℝ} (hσ : 0 < σ) {z : Profile → MeridC}
    (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    IsForceField c (meridImField z) := by
  refine ⟨fun i => ?_, fun s q η => ?_, ⟨σ, H1, L1, hσ, fun p hp => ?_⟩⟩
  · have hproj : ContDiff ℝ ∞ (fun p : Profile => z p i) :=
      ((EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hz.smooth
    exact Complex.imCLM.contDiff.comp hproj
  · funext i
    have hper := hz.periodic (s, q, η)
    exact congrArg (fun w : MeridC => (w i).im) hper
  · have hz0 : z p ≠ 0 := by
      intro h0
      apply hp
      funext i
      simp [meridImField, h0]
    obtain ⟨h1, h2, h3⟩ := hsupp p hz0
    exact ⟨⟨h1, h2⟩, h3⟩

/-! ### 2. Smoothness, `c`-periodicity, and exact `[σ, H1]` age-band support -/

private theorem contDiff_cvec_comp {v : Profile → Fin 2 → ℝ}
    (hv : ∀ i : Fin 2, ContDiff ℝ ∞ (fun p => v p i)) :
    ContDiff ℝ ∞ (fun p : Profile => cvec (v p)) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℂ)).symm.contDiff.comp
    (contDiff_pi.mpr fun i => Complex.ofRealCLM.contDiff.comp (hv i))

theorem flatLerayRep_smooth {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    ContDiff ℝ ∞ (flatLerayRep c z) := by
  have hRe := (lerayFieldProps c hc _ (isForceField_meridReField hσ hz hsupp)).1
  have hIm := (lerayFieldProps c hc _ (isForceField_meridImField hσ hz hsupp)).1
  have hcRe := contDiff_cvec_comp hRe
  have hcIm := contDiff_cvec_comp hIm
  exact hcRe.add (hcIm.const_smul Complex.I)

theorem flatLerayRep_periodic {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    QPeriodic c (flatLerayRep c z) := by
  have hRe := (lerayFieldProps c hc _ (isForceField_meridReField hσ hz hsupp)).2.1
  have hIm := (lerayFieldProps c hc _ (isForceField_meridImField hσ hz hsupp)).2.1
  intro p
  obtain ⟨s, q, η⟩ := p
  unfold flatLerayRep
  change cvec (lerayField c (meridReField z) (s, (q + c, η))) +
      Complex.I • cvec (lerayField c (meridImField z) (s, (q + c, η))) =
    cvec (lerayField c (meridReField z) (s, (q, η))) +
      Complex.I • cvec (lerayField c (meridImField z) (s, (q, η)))
  rw [hRe s q η, hIm s q η]

private theorem lerayField_eq_zero_of_not_mem_Icc {c σ H1 : ℝ} {F : Profile → Fin 2 → ℝ}
    (hbF : ∀ p : Profile, F p ≠ 0 → p.1 ∈ Icc σ H1) {p : Profile} (hp : p.1 ∉ Icc σ H1) :
    lerayField c F p = 0 := by
  have hF0 : F p = 0 := by
    by_contra hne
    exact hp (hbF p hne)
  have hu : ∀ q : Profile, lerayPot c F q ≠ 0 → q.1 ∈ Icc σ H1 := lerayPot_band hbF
  have hg0 : flatGrad (lerayPot c F) p = 0 := by
    by_contra hne
    exact hp (flatGrad_band hu p hne)
  funext i
  simp [lerayField, hF0, hg0]

theorem flatLerayRep_support_s {c σ H1 L1 : ℝ} {z : Profile → MeridC}
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (p : Profile) (hp : p.1 < σ ∨ H1 < p.1) :
    flatLerayRep c z p = 0 := by
  have hnot : p.1 ∉ Icc σ H1 := by
    intro hI
    rcases hp with hlt | hgt
    · linarith [hI.1]
    · linarith [hI.2]
  have hbRe : ∀ q : Profile, meridReField z q ≠ 0 → q.1 ∈ Icc σ H1 := by
    intro q hq
    have hz0 : z q ≠ 0 := fun h0 => hq (by funext i; simp [meridReField, h0])
    exact ⟨(hsupp q hz0).1, (hsupp q hz0).2.1⟩
  have hbIm : ∀ q : Profile, meridImField z q ≠ 0 → q.1 ∈ Icc σ H1 := by
    intro q hq
    have hz0 : z q ≠ 0 := fun h0 => hq (by funext i; simp [meridImField, h0])
    exact ⟨(hsupp q hz0).1, (hsupp q hz0).2.1⟩
  have hRe0 := lerayField_eq_zero_of_not_mem_Icc (c := c) hbRe hnot
  have hIm0 := lerayField_eq_zero_of_not_mem_Icc (c := c) hbIm hnot
  have hc0 : cvec (0 : Fin 2 → ℝ) = 0 := by
    ext i
    simp [cvec]
  unfold flatLerayRep
  rw [hRe0, hIm0, hc0, smul_zero, add_zero]

/-! ### 3. Almost-everywhere projection identities for `flatLerayRep` and `FlatLeray.lerayPart` -/

private theorem pepsC_cvec_forceField {c : ℝ} (hc : 0 < c) {F : Profile → Fin 2 → ℝ}
    (hF : IsForceField c F) :
    ∃ (hF_lp : MemLp (fun p => cvec (F p)) 2 (measureH c)),
      (PepsC 0 c (hF_lp.toLp _) : Profile → MeridC) =ᵐ[measureH c]
        fun p => cvec (lerayField c F p) := by
  obtain ⟨hWs, hWp, hWb, -, hWe, hWdiv⟩ := lerayFieldProps c hc F hF
  obtain ⟨hus, hub, -⟩ := lerayPotSmooth c hc F hF
  obtain ⟨Cd, κd, hκd, hdec⟩ := lerayPotDecay c hc F hF
  rcases hF with ⟨_, hFp, s0, s1, _, hs0, hFb⟩
  have huband : ∀ p, lerayPot c F p ≠ 0 → p.1 ∈ Icc s0 s1 :=
    lerayPot_band (fun p hp => (hFb p hp).1)
  have hubdd : ∃ C : ℝ, ∀ p, |lerayPot c F p| ≤ C := by
    obtain ⟨C, hC⟩ := hub 0
    refine ⟨C, fun p => ?_⟩
    have := hC p
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hWm := memLpOfDecay c hc (lerayField c F) (fun i => (hWs i).continuous) hWb hWe
  have hVm := memLpOfDecay c hc (flatGrad (lerayPot c F)) (flatGrad_continuous hus)
    ⟨s0, s1, hs0, flatGrad_band huband⟩ ⟨Cd, κd, hκd, flatGrad_decay hdec⟩
  have ha := smoothSolenoidal c hc (lerayField c F) hWs hWp hWdiv hWm
  have hb := smoothGradPerp c hc (lerayPot c F) hus (lerayPot_periodic hFp)
    ⟨s0, s1, hs0, huband⟩ hubdd ⟨Cd, κd, hκd, hdec⟩ hVm
  have hF_eq : (fun p : Profile => cvec (F p)) =
      (fun p => cvec (lerayField c F p)) + (fun p => cvec (flatGrad (lerayPot c F) p)) := by
    funext p
    ext i
    simp only [Pi.add_apply, PiLp.add_apply, cvec, lerayField]
    push_cast
    ring
  have hF_lp : MemLp (fun p => cvec (F p)) 2 (measureH c) := by
    rw [hF_eq]
    exact hWm.add hVm
  refine ⟨hF_lp, ?_⟩
  have hsum : hF_lp.toLp _ = hWm.toLp _ + hVm.toLp _ := by
    apply Lp.ext
    filter_upwards [hF_lp.coeFn_toLp, Lp.coeFn_add (hWm.toLp _) (hVm.toLp _),
      hWm.coeFn_toLp, hVm.coeFn_toLp] with p h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    exact congrFun hF_eq p
  rw [hsum, pepsC_eq_of_decomp ha hb]
  exact hWm.coeFn_toLp

/-- `PepsC 0 c Z` has `flatLerayRep c z` as an almost-everywhere representative on `measureH c`. -/
theorem pepsC_ae_eq_flatLerayRep {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ)
    {z : Profile → MeridC} {Z : HSpace c MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1)
    (hZ : (Z : Profile → MeridC) =ᵐ[measureH c] z) :
    (PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] flatLerayRep c z := by
  obtain ⟨hRe_lp, hRe_ae⟩ := pepsC_cvec_forceField hc (isForceField_meridReField hσ hz hsupp)
  obtain ⟨hIm_lp, hIm_ae⟩ := pepsC_cvec_forceField hc (isForceField_meridImField hσ hz hsupp)
  have hZ_decomp : Z = hRe_lp.toLp _ + Complex.I • hIm_lp.toLp _ := by
    apply Lp.ext
    filter_upwards [hZ,
      Lp.coeFn_add (hRe_lp.toLp _) (Complex.I • hIm_lp.toLp _),
      Lp.coeFn_smul Complex.I (hIm_lp.toLp _),
      hRe_lp.coeFn_toLp, hIm_lp.coeFn_toLp] with p hpZ hadd hsm hRe hIm
    rw [hpZ, hadd, Pi.add_apply, hsm, Pi.smul_apply, hRe, hIm, cvec_re_add_im]
  have hP : PepsC 0 c Z =
      PepsC 0 c (hRe_lp.toLp _) + Complex.I • PepsC 0 c (hIm_lp.toLp _) := by
    rw [hZ_decomp, map_add, map_smul]
  rw [hP]
  filter_upwards [Lp.coeFn_add (PepsC 0 c (hRe_lp.toLp _))
      (Complex.I • PepsC 0 c (hIm_lp.toLp _)),
    Lp.coeFn_smul Complex.I (PepsC 0 c (hIm_lp.toLp _)),
    hRe_ae, hIm_ae] with p hadd hsm hRe hIm
  rw [hadd, Pi.add_apply, hsm, Pi.smul_apply, hRe, hIm]
  rfl

/-- `PepsC 0 c Z` also has the Fourier-series representative `FlatLeray.lerayPart c z` a.e. on
`measureH c`, so `flatLerayRep c z =ᵐ[measureH c] FlatLeray.lerayPart c z`. -/
theorem pepsC_ae_eq_lerayPart {c : ℝ} (hc : 0 < c)
    {z : Profile → MeridC} {Z : HSpace c MeridC} (hz : IsMeridTest c z)
    (hZ : (Z : Profile → MeridC) =ᵐ[measureH c] z) :
    (PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] FlatLeray.lerayPart c z := by
  obtain ⟨hA, hO, hOm⟩ := fOsc_isMeridTest hc hz
  have mA : MemLp (avgQ c z) 2 (measureH c) := avgMemLp_of_isMeridTest hA
  have mO : MemLp (fOsc c z) 2 (measureH c) := avgMemLp_of_isMeridTest hO
  have hsplit : Z = mA.toLp _ + mO.toLp _ := by
    apply Lp.ext
    filter_upwards [hZ, Lp.coeFn_add (mA.toLp _) (mO.toLp _), mA.coeFn_toLp, mO.coeFn_toLp]
      with p h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp [fOsc]
  have hZ0 := (zeroFlatProj_of zeroFlatSolenoid zeroFlatGradient c (avgQ c z)
    (mA.toLp _) hc hA (qInvariant_avgQ c _) mA.coeFn_toLp).1
  obtain ⟨FN, hFN, hlim⟩ := nzTruncConverge c hc (fOsc c z) hO hOm (mO.toLp _) mO.coeFn_toLp
  have hlimP : Tendsto (fun N => PepsC 0 c (FN N)) atTop (𝓝 (PepsC 0 c (mO.toLp _))) :=
    ((PepsC 0 c).continuous.tendsto _).comp hlim
  have hO' : (PepsC 0 c (mO.toLp _) : Profile → MeridC) =ᵐ[measureH c] lerayTail c z :=
    aeLimitOfLp c _ _ _ _ hlimP (fun N => finModeProj c hc _ hz N (FN N) (hFN N))
      (truncTendsto c hc _ hz)
  have hP : PepsC 0 c Z = PepsC 0 c (mA.toLp _) + PepsC 0 c (mO.toLp _) := by
    rw [hsplit, map_add]
  rw [hP]
  filter_upwards [Lp.coeFn_add (PepsC 0 c (mA.toLp _)) (PepsC 0 c (mO.toLp _)), hZ0, hO']
    with p h1 h2 h3
  rw [h1, Pi.add_apply, h3]
  unfold PepsC
  rw [h2]
  rfl

/-! ### 4. Moment boundedness and `measureH c`-integrability from exponential `η`-decay -/

/-- Vanishing of `iteratedFDeriv ℝ m (opS^[a] h)` outside the closed age band `[σ, H1]`. -/
theorem iteratedFDeriv_opS_eq_zero_of_support_s {σ H1 : ℝ} {h : Profile → MeridC}
    (hsupp : ∀ p : Profile, p.1 < σ ∨ H1 < p.1 → h p = 0)
    (a m : ℕ) {p : Profile} (hp : p.1 ∉ Icc σ H1) :
    iteratedFDeriv ℝ m (opS^[a] h) p = 0 := by
  have hopen : IsOpen {q : Profile | q.1 ∉ Icc σ H1} :=
    (isClosed_Icc.preimage continuous_fst).isOpen_compl
  have hzero_opS : ∀ k : ℕ, ∀ q : Profile, q.1 ∉ Icc σ H1 → (opS^[k] h) q = 0 := by
    intro k
    induction k with
    | zero =>
      intro q hq
      apply hsupp q
      by_contra hnot
      exact hq ⟨not_lt.mp fun h1 => hnot (Or.inl h1), not_lt.mp fun h2 => hnot (Or.inr h2)⟩
    | succ k ih =>
      intro q hq
      rw [Function.iterate_succ']
      have hev : (opS^[k] h) =ᶠ[𝓝 q] fun _ => (0 : MeridC) := by
        filter_upwards [hopen.mem_nhds hq] with r hr
        exact ih r hr
      have hfd : fderiv ℝ (opS^[k] h) q = fderiv ℝ (fun _ : Profile => (0 : MeridC)) q :=
        hev.fderiv_eq
      simp [opS, pdS, hfd]
  have hev_opS : (opS^[a] h) =ᶠ[𝓝 p] fun _ => (0 : MeridC) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hzero_opS a q hq
  rw [(hev_opS.iteratedFDeriv ℝ m).self_of_nhds]
  simp

private theorem pow_le_const_mul_exp {δ : ℝ} (hδ : 0 < δ) (j : ℕ) (hj : j < 3) (u : ℝ)
    (hu : 0 ≤ u) :
    u ^ j ≤ (1 + 2 / δ) ^ 2 * Real.exp (δ * u) := by
  have h1 : 1 ≤ (1 + 2 / δ) ^ 2 := by
    have : 0 ≤ 2 / δ := by positivity
    nlinarith
  interval_cases j
  · simp only [pow_zero]
    calc (1 : ℝ) ≤ (1 + 2 / δ) ^ 2 * 1 := by linarith
      _ ≤ (1 + 2 / δ) ^ 2 * Real.exp (δ * u) := by
        gcongr
        exact Real.one_le_exp (by positivity)
  · rw [pow_one]
    have hexp : δ * u ≤ Real.exp (δ * u) := by
      linarith [Real.add_one_le_exp (δ * u)]
    have hu_le : u ≤ (1 / δ) * Real.exp (δ * u) := by
      rw [one_div_mul_eq_div, le_div_iff₀' hδ]
      exact hexp
    have hcoeff : 1 / δ ≤ (1 + 2 / δ) ^ 2 := by
      have hpos : 0 < 1 / δ := by positivity
      have h2 : 2 / δ = 2 * (1 / δ) := by ring
      nlinarith [sq_nonneg (2 / δ)]
    exact hu_le.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)
  · have hδ2 : 0 < δ / 2 := by linarith
    have hexp : (δ / 2) * u ≤ Real.exp ((δ / 2) * u) := by
      linarith [Real.add_one_le_exp ((δ / 2) * u)]
    have hu_le : u ≤ (2 / δ) * Real.exp ((δ / 2) * u) := by
      have h' : u * (δ / 2) ≤ Real.exp ((δ / 2) * u) := by linarith
      have := (le_div_iff₀ hδ2).mpr h'
      calc u ≤ Real.exp ((δ / 2) * u) / (δ / 2) := this
        _ = (2 / δ) * Real.exp ((δ / 2) * u) := by ring
    have hsq : u ^ 2 ≤ (2 / δ) ^ 2 * Real.exp (δ * u) := by
      calc u ^ 2 ≤ ((2 / δ) * Real.exp ((δ / 2) * u)) ^ 2 :=
            pow_le_pow_left₀ hu hu_le 2
        _ = (2 / δ) ^ 2 * (Real.exp ((δ / 2) * u)) ^ 2 := mul_pow _ _ 2
        _ = (2 / δ) ^ 2 * Real.exp (δ * u) := by
            congr 1
            rw [sq, ← Real.exp_add]
            congr 1
            ring
    have hcoeff : (2 / δ) ^ 2 ≤ (1 + 2 / δ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    exact hsq.trans (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le)

private theorem contDiff_opS_iter {h : Profile → MeridC} (hh : ContDiff ℝ ∞ h) (a : ℕ) :
    ContDiff ℝ ∞ (opS^[a] h) := by
  induction a with
  | zero => exact hh
  | succ a ih =>
    rw [Function.iterate_succ']
    unfold opS pdS
    exact contDiff_fst.smul ((ih.fderiv_right (by simp)).clm_apply contDiff_const)

/-- **Leaf 1 (`FlatLerayIterDecay`, task `PartII-a:N04/2/1/1`)**: exponential `η`-decay of
iterated derivatives of `opS^[a] (flatLerayRep c z)` for `a < 2` and `m < 5` (source:
`the November 2 reference manuscript` lines 1723–1726, 1800–1823; extending `lerayPotDecay` via
commutation of `opS` and constant-coefficient derivatives with `lerayField c`). -/
def FlatLerayIterDecay : Prop :=
  ∀ (c σ H1 L1 : ℝ), 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 →
    ∀ z : Profile → MeridC, IsMeridTest c z →
      (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
      ∀ a ∈ Finset.range 2, ∀ m ∈ Finset.range 5,
        ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ p : Profile,
          ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖ ≤
            C * Real.exp (-(κ * |p.2.2|))

/-- **Leaf 2 (`FlatLerayMomentNormBound`, task `PartII-a:N04/2/1/2`)**: quantitative
`L²(measureH c)` bound on the weighted moments and derivatives up to order 4 of
`opS^[a] (flatLerayRep c z)` (`a < 2`, `j < 3`, `m < 5`) by
`C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * h6Norm c z` (source: `the November 2 reference manuscript`
lines 1723–1726, 1800–1823). -/
def FlatLerayMomentNormBound : Prop :=
  ∃ (k1 : ℕ) (C1 : ℝ), 0 ≤ C1 ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < ν → 0 < c → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 ≤ M → 0 < γs →
      ∀ z : Profile → MeridC, IsMeridTest c z →
        (∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) →
        flatProjMomentNorm c (flatLerayRep c z) ≤
          C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * h6Norm c z

/-- Full `IsFlatLerayRep c σ H1 (flatLerayRep c z)` from `FlatLerayIterDecay`. -/
theorem isFlatLerayRep_flatLerayRep (hDecay : FlatLerayIterDecay)
    {c σ H1 L1 : ℝ} (hc : 0 < c) (hσ : 0 < σ) (hσH1 : σ ≤ H1) (hL1 : 0 ≤ L1)
    {z : Profile → MeridC} (hz : IsMeridTest c z)
    (hsupp : ∀ p, z p ≠ 0 → σ ≤ p.1 ∧ p.1 ≤ H1 ∧ |p.2.2| ≤ L1) :
    IsFlatLerayRep c σ H1 (flatLerayRep c z) := by
  have hsm := flatLerayRep_smooth hc hσ hz hsupp
  have hper := flatLerayRep_periodic hc hσ hz hsupp
  have hsupp_s := flatLerayRep_support_s (c := c) hsupp
  refine ⟨hsm, hper, hsupp_s, ?_, ?_⟩
  · intro a ha j hj m hm
    obtain ⟨C, κ, hC, hκ, hdec⟩ := hDecay c σ H1 L1 hc hσ hσH1 hL1 z hz hsupp a ha m hm
    have hj' : j < 3 := Finset.mem_range.mp hj
    refine ⟨C * (1 + 2 / κ) ^ 2, fun p => ?_⟩
    have hpow := pow_le_const_mul_exp hκ j hj' |p.2.2| (abs_nonneg _)
    calc |p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖
        ≤ ((1 + 2 / κ) ^ 2 * Real.exp (κ * |p.2.2|)) *
            (C * Real.exp (-(κ * |p.2.2|))) :=
          mul_le_mul hpow (hdec p) (norm_nonneg _) (by positivity)
      _ = C * (1 + 2 / κ) ^ 2 *
            (Real.exp (κ * |p.2.2|) * Real.exp (-(κ * |p.2.2|))) := by ring
      _ = C * (1 + 2 / κ) ^ 2 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  · intro a ha j hj m hm
    obtain ⟨C, κ, hC, hκ, hdec⟩ := hDecay c σ H1 L1 hc hσ hσH1 hL1 z hz hsupp a ha m hm
    have hj' : j < 3 := Finset.mem_range.mp hj
    have hκ2 : 0 < κ / 2 := by linarith
    set g : Profile → ℝ := fun p =>
      |p.2.2| ^ j * ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖
    set v : Profile → Fin 2 → ℝ := fun p => ![g p, 0]
    have hg_cont : Continuous g := by
      have h1 : Continuous (fun p : Profile => |p.2.2| ^ j) := by fun_prop
      have h2 : Continuous (fun p : Profile =>
          ‖iteratedFDeriv ℝ m (opS^[a] (flatLerayRep c z)) p‖) :=
        ((contDiff_opS_iter hsm a).continuous_iteratedFDeriv (by simp)).norm
      exact h1.mul h2
    have hv_cont : ∀ i : Fin 2, Continuous (fun p : Profile => v p i) := by
      intro i
      fin_cases i
      · exact hg_cont
      · exact continuous_const
    have hv_band : ∃ s0 s1 : ℝ, 0 < s0 ∧ ∀ p : Profile, v p ≠ 0 → p.1 ∈ Icc s0 s1 := by
      refine ⟨σ, H1, hσ, fun p hp => ?_⟩
      by_contra hnot
      apply hp
      have hz0 := iteratedFDeriv_opS_eq_zero_of_support_s hsupp_s a m hnot
      funext i
      fin_cases i <;> simp [v, g, hz0]
    have hv_dec : ∃ C' κ' : ℝ, 0 < κ' ∧ ∀ (p : Profile) (i : Fin 2),
        |v p i| ≤ C' * Real.exp (-(κ' * |p.2.2|)) := by
      refine ⟨C * (1 + 2 / (κ / 2)) ^ 2, κ / 2, hκ2, fun p i => ?_⟩
      have hpow := pow_le_const_mul_exp hκ2 j hj' |p.2.2| (abs_nonneg _)
      have hg_le : g p ≤ C * (1 + 2 / (κ / 2)) ^ 2 * Real.exp (-((κ / 2) * |p.2.2|)) := by
        calc g p ≤ ((1 + 2 / (κ / 2)) ^ 2 * Real.exp ((κ / 2) * |p.2.2|)) *
              (C * Real.exp (-(κ * |p.2.2|))) :=
              mul_le_mul hpow (hdec p) (norm_nonneg _) (by positivity)
          _ = C * (1 + 2 / (κ / 2)) ^ 2 *
              (Real.exp ((κ / 2) * |p.2.2|) * Real.exp (-(κ * |p.2.2|))) := by ring
          _ = C * (1 + 2 / (κ / 2)) ^ 2 * Real.exp (-((κ / 2) * |p.2.2|)) := by
              congr 1
              rw [← Real.exp_add]
              congr 1
              ring
      have hg_nonneg : 0 ≤ g p := by positivity
      fin_cases i
      · simp only [v, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
          abs_of_nonneg hg_nonneg]
        exact hg_le
      · simp only [v, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          abs_zero]
        positivity
    have hmem := memLpOfDecay c hc v hv_cont hv_band hv_dec
    have hint_norm : Integrable (fun p : Profile => ‖cvec (v p)‖ ^ 2) (measureH c) :=
      hmem.integrable_norm_pow (by norm_num)
    refine hint_norm.congr (Eventually.of_forall fun p => ?_)
    simp only [cvec, v, g, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two,
      Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]

/-- Conditional assembly of `FlatLeraySmoothRep` from `FlatLerayIterDecay` and
`FlatLerayMomentNormBound`. -/
theorem flatLeraySmoothRep_of (hDecay : FlatLerayIterDecay)
    (hNorm : FlatLerayMomentNormBound) : FlatLeraySmoothRep := by
  obtain ⟨k1, C1, hC1, hNorm⟩ := hNorm
  refine ⟨k1, C1, hC1, ?_⟩
  intro ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM hγs z Z hz hsupp hZ
  refine ⟨flatLerayRep c z,
    isFlatLerayRep_flatLerayRep hDecay hc hσ hσH1 hL1 hz hsupp,
    pepsC_ae_eq_flatLerayRep hc hσ hz hsupp hZ,
    hNorm ν c σ H1 L1 M γs hν hc hσ hσH1 hL1 hM hγs z hz hsupp⟩

end UnforcedLeray.Short.PartIIa
