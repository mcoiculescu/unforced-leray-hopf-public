import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.ZetaPhiSolenoidal

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest flatDt flatLap)
open UnforcedLeray.Short.PartIIa (pdS pdQ pdEta)

/-! ### Calculus helpers -/

theorem fderiv_clm_comp' {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) {g : E → F} {P : E} (hg : DifferentiableAt ℝ g P) (v : E) :
    fderiv ℝ (fun Q => L (g Q)) P v = L (fderiv ℝ g P v) := by
  have h : HasFDerivAt (fun Q => L (g Q)) (L.comp (fderiv ℝ g P)) P :=
    L.hasFDerivAt.comp P hg.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem fderiv_coord' {F : Profile → MeridC} {P : Profile} (hF : DifferentiableAt ℝ F P)
    (v : Profile) (i : Fin 2) :
    fderiv ℝ F P v i = fderiv ℝ (fun Q => F Q i) P v := by
  let L : MeridC →L[ℝ] ℂ := (EuclideanSpace.proj i : MeridC →L[ℂ] ℂ).restrictScalars ℝ
  exact (fderiv_clm_comp' L hF v).symm

theorem fderiv_ofReal' {g : Profile → ℝ} {P : Profile} (hg : DifferentiableAt ℝ g P) (v : Profile) :
    fderiv ℝ (fun Q => ((g Q : ℝ) : ℂ)) P v = ((fderiv ℝ g P v : ℝ) : ℂ) := by
  have h := fderiv_clm_comp' Complex.ofRealCLM hg v
  simpa using h

theorem sqrt_diff' {P : Profile} (hs : 0 < P.1) :
    DifferentiableAt ℝ (fun Q : Profile => Real.sqrt Q.1) P :=
  (hasFDerivAt_fst.sqrt hs.ne').differentiableAt

theorem fderiv_sqrt_mul' {ψ : Profile → ℝ} {P : Profile} (hs : 0 < P.1)
    (hψ : DifferentiableAt ℝ ψ P) (v : Profile) :
    fderiv ℝ (fun Q : Profile => Real.sqrt Q.1 * ψ Q) P v =
      1 / (2 * Real.sqrt P.1) * v.1 * ψ P + Real.sqrt P.1 * fderiv ℝ ψ P v := by
  have hsq : HasFDerivAt (fun Q : Profile => Real.sqrt Q.1)
      ((1 / (2 * Real.sqrt P.1)) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) P :=
    hasFDerivAt_fst.sqrt hs.ne'
  have hm := hsq.mul hψ.hasFDerivAt
  rw [show ((fun Q : Profile => Real.sqrt Q.1) * ψ) = (fun Q : Profile => Real.sqrt Q.1 * ψ Q)
    from rfl] at hm
  rw [hm.fderiv]
  simp [smul_eq_mul]
  ring

theorem hasDerivAt_line' {F : Profile → ℝ} {Q v : Profile} (hF : DifferentiableAt ℝ F Q) :
    HasDerivAt (fun t : ℝ => F (Q + t • v)) (fderiv ℝ F Q v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => Q + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add Q
  have h2 : HasFDerivAt F (fderiv ℝ F Q) ((fun t : ℝ => Q + t • v) 0) := by
    simpa using hF.hasFDerivAt
  exact h2.comp_hasDerivAt 0 hl

theorem contDiff_fderiv_dir' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Profile → E} (hF : ContDiff ℝ ∞ F) (v : Profile) :
    Differentiable ℝ (fun Q => fderiv ℝ F Q v) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by simp)
  have h2 : ContDiff ℝ 1 (fun Q => fderiv ℝ F Q v) := h1.clm_apply contDiff_const
  exact h2.differentiable (by simp)

/-! ### Smoothness and the derivatives of `ζ_Φ` -/

theorem sqrt_mul_contDiff' {c : ℝ} (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : IsFlatTest c Φ)
    (i : Fin 2) : ContDiff ℝ ∞ (fun p : Profile => Real.sqrt p.1 * Φ p.1 p.2 i) := by
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1 < s1
  · apply ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ)))
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
    simp [hsupp q.1 q.2 i (Or.inl hq)]
  · push_neg at hp
    have hp0 : p.1 ≠ 0 := (lt_of_lt_of_le hs1 hp).ne'
    have h1 : ContDiffAt ℝ ∞ (fun q : Profile => Real.sqrt q.1) p :=
      (Real.contDiffAt_sqrt hp0).comp p contDiff_fst.contDiffAt
    have h2 : ContDiffAt ℝ ∞ (fun q : Profile => Φ q.1 q.2 i) p :=
      (hΦ.smooth i).contDiffAt
    exact h1.mul h2

theorem zetaPhi_contDiff' {c : ℝ} (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : IsFlatTest c Φ) :
    ContDiff ℝ ∞ (zetaPhi Φ) := by
  unfold zetaPhi
  exact contDiff_piLp' 2 (fun i => Complex.ofRealCLM.contDiff.comp (sqrt_mul_contDiff' Φ hΦ i))

theorem fderiv_zeta_apply' {c : ℝ} (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : IsFlatTest c Φ)
    (i : Fin 2) {P : Profile} (hs : 0 < P.1) (v : Profile) :
    fderiv ℝ (zetaPhi Φ) P v i =
      ((1 / (2 * Real.sqrt P.1) * v.1 * Φ P.1 P.2 i + Real.sqrt P.1 *
        fderiv ℝ (fun Q : Profile => Φ Q.1 Q.2 i) P v : ℝ) : ℂ) := by
  have hGd : DifferentiableAt ℝ (fun Q : Profile => Real.sqrt Q.1 * Φ Q.1 Q.2 i) P :=
    ((sqrt_mul_contDiff' Φ hΦ i).differentiable (by simp)) P
  have hΨd : DifferentiableAt ℝ (fun Q : Profile => Φ Q.1 Q.2 i) P :=
    ((hΦ.smooth i).differentiable (by simp)) P
  have hζd : DifferentiableAt ℝ (zetaPhi Φ) P :=
    ((zetaPhi_contDiff' Φ hΦ).differentiable (by simp)) P
  rw [fderiv_coord' hζd v i]
  have hfun : (fun Q : Profile => zetaPhi Φ Q i) =
      fun Q : Profile => ((Real.sqrt Q.1 * Φ Q.1 Q.2 i : ℝ) : ℂ) := by
    funext Q
    simp [zetaPhi]
  rw [hfun, fderiv_ofReal' hGd v]
  congr 1
  exact fderiv_sqrt_mul' hs hΨd v

theorem fderiv_fderiv_zeta_apply' {c : ℝ} (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : IsFlatTest c Φ)
    (i : Fin 2) {P : Profile} (hs : 0 < P.1) {v : Profile} (hv : v.1 = 0) :
    fderiv ℝ (fun Q : Profile => fderiv ℝ (zetaPhi Φ) Q v) P v i =
      ((Real.sqrt P.1 * fderiv ℝ (fun Q : Profile => fderiv ℝ (fun R : Profile => Φ R.1 R.2 i) Q v)
        P v : ℝ) : ℂ) := by
  have hζs := zetaPhi_contDiff' Φ hΦ
  have hΨs : ContDiff ℝ ∞ (fun Q : Profile => Φ Q.1 Q.2 i) := hΦ.smooth i
  have hdζ : Differentiable ℝ (fun Q : Profile => fderiv ℝ (zetaPhi Φ) Q v) :=
    contDiff_fderiv_dir' hζs v
  rw [fderiv_coord' (hdζ P) v i]
  have hev : (fun Q : Profile => fderiv ℝ (zetaPhi Φ) Q v i) =ᶠ[𝓝 P]
      (fun Q : Profile => ((Real.sqrt Q.1 *
        fderiv ℝ (fun R : Profile => Φ R.1 R.2 i) Q v : ℝ) : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hs] with Q hQ
    have hQ0 : (0 : ℝ) < Q.1 := hQ
    rw [fderiv_zeta_apply' Φ hΦ i hQ0 v, hv]
    simp
  have hgd : DifferentiableAt ℝ (fun Q : Profile => Real.sqrt Q.1 *
      fderiv ℝ (fun R : Profile => Φ R.1 R.2 i) Q v) P :=
    (sqrt_diff' hs).mul ((contDiff_fderiv_dir' hΨs v) P)
  rw [hev.fderiv_eq, fderiv_ofReal' hgd v, fderiv_sqrt_mul' hs
    ((contDiff_fderiv_dir' hΨs v) P) v, hv]
  simp

theorem pdS_eq_flatDt' {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {i : Fin 2}
    (hΨ : ContDiff ℝ ∞ (fun Q : Profile => Φ Q.1 Q.2 i)) (P : Profile) :
    pdS (fun Q : Profile => Φ Q.1 Q.2 i) P = flatDt Φ P.1 P.2 i := by
  have hd : Differentiable ℝ (fun Q : Profile => Φ Q.1 Q.2 i) := hΨ.differentiable (by simp)
  have h1 := hasDerivAt_line' (v := ((1 : ℝ), (0 : ℝ), (0 : ℝ))) (hd P)
  have hc : Differentiable ℝ (fun s' : ℝ => ((s', P.2) : Profile)) :=
    differentiable_id.prodMk (differentiable_const _)
  have hs : Differentiable ℝ (fun s' : ℝ => Φ s' P.2 i) := hd.comp hc
  have h2 : HasDerivAt (fun s' : ℝ => Φ s' P.2 i) (flatDt Φ P.1 P.2 i) (P.1 + 0) := by
    rw [add_zero]
    exact (hs P.1).hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => Φ (P.1 + t) P.2 i) (flatDt Φ P.1 P.2 i) 0 :=
    h2.comp_const_add P.1 0
  have h4 : HasDerivAt (fun t : ℝ => (fun Q : Profile => Φ Q.1 Q.2 i)
      (P + t • ((1 : ℝ), (0 : ℝ), (0 : ℝ)))) (flatDt Φ P.1 P.2 i) 0 := by
    convert h3 using 1
    funext t
    simp [Prod.mk_zero_zero]
  exact h1.unique h4

theorem flatLap_split' {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {i : Fin 2}
    (hΨ : ContDiff ℝ ∞ (fun Q : Profile => Φ Q.1 Q.2 i)) (P : Profile) :
    flatLap Φ P.1 P.2 i = pdQ (pdQ (fun Q : Profile => Φ Q.1 Q.2 i)) P +
      pdEta (pdEta (fun Q : Profile => Φ Q.1 Q.2 i)) P := by
  have hΨd : Differentiable ℝ (fun Q : Profile => Φ Q.1 Q.2 i) := hΨ.differentiable (by simp)
  have hdQ : Differentiable ℝ (UnforcedLeray.Axi.dQ (fun Q : Profile => Φ Q.1 Q.2 i)) :=
    contDiff_fderiv_dir' hΨ (0, (1, 0))
  have hdE : Differentiable ℝ (UnforcedLeray.Axi.dEta (fun Q : Profile => Φ Q.1 Q.2 i)) :=
    contDiff_fderiv_dir' hΨ (0, (0, 1))
  have hA : UnforcedLeray.B0579.pd 0 (fun y => Φ P.1 y i) =
      fun y => UnforcedLeray.Axi.dQ (fun Q : Profile => Φ Q.1 Q.2 i) (P.1, y) :=
    funext fun y => pd0_slice hΨd P.1 y
  have hB : UnforcedLeray.B0579.pd 0 (fun y => UnforcedLeray.Axi.dQ
      (fun Q : Profile => Φ Q.1 Q.2 i) (P.1, y)) = fun y => UnforcedLeray.Axi.dQ
      (UnforcedLeray.Axi.dQ (fun Q : Profile => Φ Q.1 Q.2 i)) (P.1, y) :=
    funext fun y => pd0_slice hdQ P.1 y
  have hC : UnforcedLeray.B0579.pd 1 (fun y => Φ P.1 y i) =
      fun y => UnforcedLeray.Axi.dEta (fun Q : Profile => Φ Q.1 Q.2 i) (P.1, y) :=
    funext fun y => pd1_slice hΨd P.1 y
  have hD : UnforcedLeray.B0579.pd 1 (fun y => UnforcedLeray.Axi.dEta
      (fun Q : Profile => Φ Q.1 Q.2 i) (P.1, y)) = fun y => UnforcedLeray.Axi.dEta
      (UnforcedLeray.Axi.dEta (fun Q : Profile => Φ Q.1 Q.2 i)) (P.1, y) :=
    funext fun y => pd1_slice hdE P.1 y
  unfold flatLap UnforcedLeray.Short.IIIa.lapP
  rw [hA, hB, hC, hD]
  rfl

theorem resolventTestZetaPhi : ResolventTestZetaPhi := by
  intro c ν μ Φ hΦ p hp
  have hs : (0 : ℝ) < p.1 := hp
  have hr : Real.sqrt p.1 * Real.sqrt p.1 = p.1 := Real.mul_self_sqrt hs.le
  have hRC : ((Real.sqrt p.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hs).ne'
  have hrC : ((Real.sqrt p.1 : ℝ) : ℂ) * ((Real.sqrt p.1 : ℝ) : ℂ) = (p.1 : ℂ) := by
    exact_mod_cast hr
  ext i
  unfold resolventTest A0adj pdS pdQ pdEta
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, Complex.real_smul]
  rw [fderiv_zeta_apply' Φ hΦ i hs, fderiv_fderiv_zeta_apply' Φ hΦ i hs (v := (0, 1, 0)) rfl,
    fderiv_fderiv_zeta_apply' Φ hΦ i hs (v := (0, 0, 1)) rfl]
  rw [flatLap_split' (hΦ.smooth i) p]
  have hS : fderiv ℝ (fun Q : Profile => Φ Q.1 Q.2 i) p (1, 0, 0) = flatDt Φ p.1 p.2 i :=
    pdS_eq_flatDt' (hΦ.smooth i) p
  simp only [zetaPhi, PiLp.toLp_apply]
  rw [hS]
  unfold pdQ pdEta
  push_cast
  rw [← hrC]
  field_simp
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
