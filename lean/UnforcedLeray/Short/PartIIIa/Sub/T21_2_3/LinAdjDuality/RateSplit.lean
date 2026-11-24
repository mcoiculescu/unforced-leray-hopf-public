import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CommVanish
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX

/-!
# `PartIII-a:T21/2/3/1/11`: splitting the rate of the cut pairing (SP 3074-3075)

`ladRate R ρ = ∫ w χ_R χ - ∫ (u·∇E) χ_R φ + ladComm R ρ` for `ρ ∈ (t, s)`: the pointwise Leibniz
identity for `χ_R φ(ρ)` (smooth in `x`), and integrability of every piece on the cell, since all
pieces are `w` or `u` times a continuous function supported in `|η| ≤ 2R`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace RateSplitAux

/-! ### Complex partial derivatives -/

lemma pdCx_mul {f g : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (k : Fin 2) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    pdCx k (fun y => f y * g y) x = pdCx k f x * g x + f x * pdCx k g x := by
  unfold pdCx
  have h : fderiv ℝ (fun y => f y * g y) x = f x • fderiv ℝ g x + g x • fderiv ℝ f x :=
    (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

lemma pdCx_add {f g : ℝ × ℝ → ℂ} {x : ℝ × ℝ} (k : Fin 2) (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    pdCx k (fun y => f y + g y) x = pdCx k f x + pdCx k g x := by
  unfold pdCx
  have h : fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv
  rw [h]
  rfl

lemma pdCx_ofReal {χ : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (k : Fin 2) (hχ : DifferentiableAt ℝ χ x) :
    pdCx k (fun y => (χ y : ℂ)) x = (B0579.pd k χ x : ℂ) := by
  unfold pdCx B0579.pd
  have h : HasFDerivAt (fun y => (χ y : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ χ x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hχ.hasFDerivAt
  rw [h.fderiv]
  simp

lemma contDiff_pdCx {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k f) := by
  have hc : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact hc.clm_apply contDiff_const

lemma contDiff_ofReal {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun y => (χ y : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hχ

lemma pdCx_cut_mul {χ : ℝ × ℝ → ℝ} {F : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (fun y => (χ y : ℂ) * F y) x =
      (B0579.pd k χ x : ℂ) * F x + (χ x : ℂ) * pdCx k F x := by
  have h1 : DifferentiableAt ℝ (fun y => (χ y : ℂ)) x :=
    ((contDiff_ofReal hχ).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  rw [pdCx_mul k h1 h2, pdCx_ofReal k ((hχ.differentiable (by simp)) x)]

lemma pdCx2_cut_mul {χ : ℝ × ℝ → ℝ} {F : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    (k : Fin 2) (x : ℝ × ℝ) :
    pdCx k (pdCx k (fun y => (χ y : ℂ) * F y)) x =
      (B0579.pd k (B0579.pd k χ) x : ℂ) * F x + 2 * ((B0579.pd k χ x : ℂ) * pdCx k F x) +
        (χ x : ℂ) * pdCx k (pdCx k F) x := by
  have hfun : pdCx k (fun y => (χ y : ℂ) * F y) =
      fun y => (B0579.pd k χ y : ℂ) * F y + (χ y : ℂ) * pdCx k F y :=
    funext fun y => pdCx_cut_mul hχ hF k y
  rw [hfun]
  have hχ1 : ContDiff ℝ ∞ (B0579.pd k χ) := ForceMemXAux.contDiff_pd hχ k
  have hF1 : ContDiff ℝ ∞ (pdCx k F) := contDiff_pdCx hF k
  have d1 : DifferentiableAt ℝ (fun y => (B0579.pd k χ y : ℂ) * F y) x :=
    (((contDiff_ofReal hχ1).mul hF).differentiable (by simp)) x
  have d2 : DifferentiableAt ℝ (fun y => (χ y : ℂ) * pdCx k F y) x :=
    (((contDiff_ofReal hχ).mul hF1).differentiable (by simp)) x
  rw [pdCx_add k d1 d2, pdCx_cut_mul hχ1 hF k x, pdCx_cut_mul hχ hF1 k x]
  ring

lemma lap_cut_mul {χ : ℝ × ℝ → ℝ} {F : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F)
    (x : ℝ × ℝ) :
    ladLapCx (fun y => (χ y : ℂ) * F y) x =
      (χ x : ℂ) * ladLapCx F x +
        2 * ((B0579.pd 0 χ x : ℂ) * pdCx 0 F x + (B0579.pd 1 χ x : ℂ) * pdCx 1 F x) +
        (lapP χ x : ℂ) * F x := by
  unfold ladLapCx lapP
  rw [pdCx2_cut_mul hχ hF 0 x, pdCx2_cut_mul hχ hF 1 x]
  push_cast
  ring

/-! ### Smoothness and continuity of the pieces -/

lemma contDiff_slice {φ : ℝ → ℝ × ℝ → ℂ} {t s ρ : ℝ} (hρ : ρ ∈ Ico t s)
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    ContDiff ℝ ∞ (φ ρ) := by
  have h : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (ρ, x)) univ :=
    hφ.comp (contDiff_prodMk_right ρ).contDiffOn (fun x _ => ⟨hρ, mem_univ _⟩)
  exact contDiffOn_univ.1 h

lemma continuous_dt {φ : ℝ → ℝ × ℝ → ℂ} {t s ρ : ℝ} (hρ : ρ ∈ Ioo t s)
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ)) :
    Continuous (ladDt φ ρ) := by
  set Φ : ℝ × (ℝ × ℝ) → ℂ := fun p => φ p.1 p.2 with hΦ
  have hU : IsOpen (Ioo t s ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo t s ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ico t s ×ˢ univ :=
    prod_mono Ioo_subset_Ico_self (subset_refl _)
  have hΦU : ContDiffOn ℝ ∞ Φ (Ioo t s ×ˢ univ) := hφ.mono hsub
  have hcont : ContinuousOn (fderiv ℝ Φ) (Ioo t s ×ˢ univ) :=
    hΦU.continuousOn_fderiv_of_isOpen hU (by simp)
  have hform : ∀ x : ℝ × ℝ, ladDt φ ρ x = fderiv ℝ Φ (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) := by
    intro x
    have hd : DifferentiableAt ℝ Φ (ρ, x) :=
      (hΦU.differentiableOn (by simp)).differentiableAt (hU.mem_nhds ⟨hρ, mem_univ _⟩)
    have hl : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : ℝ × ℝ)) ρ :=
      (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
    have := hd.hasFDerivAt.comp_hasDerivAt ρ hl
    exact ladDt_eq_of_hasDerivAt this
  have hc2 : Continuous (fun x : ℝ × ℝ => fderiv ℝ Φ (ρ, x)) :=
    hcont.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hρ, mem_univ _⟩)
  have : ladDt φ ρ = fun x => fderiv ℝ Φ (ρ, x) ((1 : ℝ), (0 : ℝ × ℝ)) := funext hform
  rw [this]
  exact hc2.clm_apply continuous_const

/-! ### Cutoff support -/

lemma cut_nhds_zero {R : ℝ} (hR : 0 < R) {y : ℝ × ℝ} (hy : 2 * R ^ 2 < y.2 ^ 2) :
    ladCut R =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
  have hU : IsOpen {z : ℝ × ℝ | 2 * R ^ 2 < z.2 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  filter_upwards [hU.mem_nhds hy] with z hz
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have hq : 2 ≤ z.2 ^ 2 / R ^ 2 := (le_div_iff₀ hR2).2 (le_of_lt hz)
  unfold ladCut
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

lemma far_sq {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R < |x.2|) : 2 * R ^ 2 < x.2 ^ 2 := by
  have h1 : (2 * R) ^ 2 < |x.2| ^ 2 := by
    have : 0 ≤ 2 * R := by linarith
    nlinarith [abs_nonneg x.2]
  rw [sq_abs] at h1
  nlinarith [sq_nonneg R]

lemma cut_zero {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R < |x.2|) : ladCut R x = 0 :=
  (cut_nhds_zero hR (far_sq hR hx)).eq_of_nhds

lemma pd_cut_zero {R : ℝ} (hR : 0 < R) (j : Fin 2) {x : ℝ × ℝ} (hx : 2 * R < |x.2|) :
    B0579.pd j (ladCut R) x = 0 := by
  unfold B0579.pd
  rw [(cut_nhds_zero hR (far_sq hR hx)).fderiv_eq]
  simp

lemma pd_pd_cut_zero {R : ℝ} (hR : 0 < R) (j k : Fin 2) {x : ℝ × ℝ} (hx : 2 * R < |x.2|) :
    B0579.pd k (B0579.pd j (ladCut R)) x = 0 := by
  have hU : IsOpen {z : ℝ × ℝ | 2 * R < |z.2|} :=
    isOpen_lt continuous_const (by fun_prop)
  have h : (fun y => fderiv ℝ (ladCut R) y (B0579.dir j)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact pd_cut_zero hR j hz
  unfold B0579.pd
  rw [h.fderiv_eq]
  simp

lemma lapP_cut_zero {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R < |x.2|) :
    lapP (ladCut R) x = 0 := by
  unfold lapP
  rw [pd_pd_cut_zero hR 0 0 hx, pd_pd_cut_zero hR 1 1 hx]
  simp

/-! ### Integrability of `w` or `u` times a continuous compactly supported function -/

lemma memLp_supp {E : Type*} [NormedAddCommGroup E] (c R : ℝ) {g : ℝ × ℝ → E}
    (hg : Continuous g) (hs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → g x = 0) :
    MemLp g 2 (volume.restrict (B0579.cell c)) := by
  set K : Set (ℝ × ℝ) := Icc (-(c / 2)) (c / 2) ×ˢ Icc (-(2 * R)) (2 * R) with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  have hM0 : ∀ x ∈ K, ‖g x‖ ≤ |M| := fun x hx => (hM x hx).trans (le_abs_self M)
  have hfin : (volume.restrict (B0579.cell c)) K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (Measure.restrict_apply_le _ _) hKc.measure_lt_top)
  have hind : MemLp (K.indicator (fun _ => |M|)) 2 (volume.restrict (B0579.cell c)) :=
    memLp_indicator_const 2 hKc.measurableSet |M| (Or.inr hfin)
  refine hind.mono hg.aestronglyMeasurable ?_
  rw [ae_restrict_iff' (B0579.measurableSet_cell c)]
  refine Eventually.of_forall fun x hx => ?_
  by_cases hxK : x ∈ K
  · rw [Set.indicator_of_mem hxK]
    simpa using hM0 x hxK
  · rw [Set.indicator_of_notMem hxK]
    have hx2 : 2 * R < |x.2| := by
      by_contra hcon
      push_neg at hcon
      apply hxK
      refine ⟨⟨hx.1.1, hx.1.2.le⟩, ?_, ?_⟩
      · have := abs_le.1 hcon; linarith
      · exact (abs_le.1 hcon).2
    simp [hs x hx2]

lemma memLp_supp_weighted (c m R : ℝ) {g : ℝ × ℝ → ℂ} (hg : Continuous g)
    (hs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → g x = 0) : MemLp g 2 (B0579.cellMeasure c m) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  have h : eLpNorm g 2 (B0579.cellMeasure c m) =
      eLpNorm (fun x => B0579.jb x ^ (m / 2) * ‖g x‖) 2 (volume.restrict (B0579.cell c)) := by
    rw [← eLpNorm_norm, B0579.eLpNorm_cellMeasure]
  rw [h]
  have hc : Continuous (fun x => B0579.jb x ^ (m / 2) * ‖g x‖) :=
    (B0579.continuous_jb_rpow _).mul hg.norm
  exact (memLp_supp c R hc (fun x hx => by simp [hs x hx])).2

lemma integrableOn_w_mul (c m R : ℝ) {w g : ℝ × ℝ → ℂ}
    (hw : MemLp w 2 (B0579.cellMeasure c m)) (hg : Continuous g)
    (hs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → g x = 0) :
    IntegrableOn (fun x => w x * g x) (B0579.cell c) := by
  have hG : MemLp g 2 (B0579.cellMeasure c (-m)) := memLp_supp_weighted c (-m) R hg hs
  have hI := CommVanishAux.integrableOn_cell_norm_mul c m hw hG
  refine hI.mono' ?_ (Eventually.of_forall fun x => by simp [norm_mul])
  exact ((hw.1.mono_ac (B0579.ac_cellMeasure c m)).mul hg.aestronglyMeasurable)

/-! ### The pointwise identity and the main theorem -/

lemma continuous_v {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (j : Fin 2) : ContDiff ℝ ∞ (fun x => tr.v ρ x j) := by
  have hv : ContDiff ℝ ∞ (tr.v ρ) := UnforcedLeray.B0238.contDiff_Vc tr hρ
  exact (EuclideanSpace.proj (j : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hv

lemma pointwise_split {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {χ : ℝ × ℝ → ℝ}
    {F : ℝ × ℝ → ℂ} (hχ : ContDiff ℝ ∞ χ) (hF : ContDiff ℝ ∞ F) (ρ : ℝ) (om : ℂ) (uu : Fin 2 → ℂ)
    (x : ℝ × ℝ) (dt : ℂ) (chi : ℂ) (hchi : chi = dt + (ν : ℂ) * ladLapCx F x +
      ladTransport tr ρ F x) :
    om * ((ν : ℂ) * ladLapCx (fun y => (χ y : ℂ) * F y) x +
        ladTransport tr ρ (fun y => (χ y : ℂ) * F y) x) +
      om * ((χ x : ℂ) * dt) =
    om * ((χ x : ℂ) * chi) +
      om * ((ν : ℂ) * (2 * ((B0579.pd 0 χ x : ℂ) * pdCx 0 F x + (B0579.pd 1 χ x : ℂ) * pdCx 1 F x) +
          (lapP χ x : ℂ) * F x) +
        ((tr.v ρ x 0 * B0579.pd 0 χ x + tr.v ρ x 1 * B0579.pd 1 χ x : ℝ) : ℂ) * F x) := by
  rw [lap_cut_mul hχ hF x, hchi]
  unfold ladTransport
  rw [pdCx_cut_mul hχ hF 0 x, pdCx_cut_mul hχ hF 1 x]
  push_cast
  ring

end RateSplitAux

open RateSplitAux in
theorem ladRateSplit : LadRateSplit := by
  intro ν c m tr t s f w u φ hc ht hts hflow hφ R hR ρ hρ
  have hρ0 : 0 ≤ ρ := ht.trans hρ.1.le
  have hρt : t ≤ ρ := hρ.1.le
  have hφs : ContDiff ℝ ∞ (φ ρ) := contDiff_slice (Ioo_subset_Ico_self hρ) hφ
  have hdt : Continuous (ladDt φ ρ) := continuous_dt hρ hφ
  have hχ : ContDiff ℝ ∞ (ladCut R) := ((ladCutProps.choose_spec.2 R hR).1 c).smooth
  have hχC : Continuous (fun x => (ladCut R x : ℂ)) := (contDiff_ofReal hχ).continuous
  have hφC : Continuous (φ ρ) := hφs.continuous
  have hpd : ∀ k : Fin 2, Continuous (fun x => (B0579.pd k (ladCut R) x : ℂ)) := fun k =>
    (contDiff_ofReal (ForceMemXAux.contDiff_pd hχ k)).continuous
  have hpdφ : ∀ k : Fin 2, Continuous (pdCx k (φ ρ)) := fun k => (contDiff_pdCx hφs k).continuous
  have hlapφ : Continuous (ladLapCx (φ ρ)) := by
    unfold ladLapCx
    exact (contDiff_pdCx (contDiff_pdCx hφs 0) 0).continuous.add
      (contDiff_pdCx (contDiff_pdCx hφs 1) 1).continuous
  have hv : ∀ j : Fin 2, Continuous (fun x => (tr.v ρ x j : ℂ)) := fun j =>
    (contDiff_ofReal (continuous_v tr hρ0 j)).continuous
  have hlapP : Continuous (fun x => (lapP (ladCut R) x : ℂ)) := by
    unfold lapP
    have h0 := ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 0) 0
    have h1 := ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_pd hχ 1) 1
    exact (contDiff_ofReal (h0.add h1)).continuous
  have hchiC : Continuous (ladChi tr φ ρ) := by
    unfold ladChi ladTransport
    exact (hdt.add (continuous_const.mul hlapφ)).add
      (((hv 0).mul (hpdφ 0)).add ((hv 1).mul (hpdφ 1)))
  have hE : ∀ k : Fin 2, Continuous (fun x => (B0579.pd k (UnforcedLeray.B0238.Ec tr ρ) x : ℂ)) :=
    fun k => (contDiff_ofReal (ForceMemXAux.contDiff_pd (ForceMemXAux.contDiff_Ec tr hρ0) k)).continuous
  have hwm := hflow.memX ρ hρt
  have hum := (hflow.biotSavart ρ hρt).1
  -- vanishing outside the band
  have hz1 : ∀ x : ℝ × ℝ, 2 * R < |x.2| → ladCut R x = 0 := fun x hx => cut_zero hR hx
  -- the four pieces
  set Cp : ℝ × ℝ → ℂ := fun x => (ladCut R x : ℂ) * ladChi tr φ ρ x with hCp
  set Bp : ℝ × ℝ → ℂ := fun x => (ladCut R x : ℂ) * ladDt φ ρ x with hBp
  set Ep : ℝ × ℝ → ℂ := fun x =>
    (ν : ℂ) * (2 * ((B0579.pd 0 (ladCut R) x : ℂ) * pdCx 0 (φ ρ) x +
          (B0579.pd 1 (ladCut R) x : ℂ) * pdCx 1 (φ ρ) x) + (lapP (ladCut R) x : ℂ) * φ ρ x) +
      ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x + tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ) *
        φ ρ x with hEp
  have hCc : Continuous Cp := hχC.mul hchiC
  have hBc : Continuous Bp := hχC.mul hdt
  have hEc : Continuous Ep := by
    simp only [hEp]
    refine (continuous_const.mul ?_).add ?_
    · refine (continuous_const.mul (((hpd 0).mul (hpdφ 0)).add ((hpd 1).mul (hpdφ 1)))).add
        (hlapP.mul hφC)
    · have : Continuous (fun x => ((tr.v ρ x 0 * B0579.pd 0 (ladCut R) x +
          tr.v ρ x 1 * B0579.pd 1 (ladCut R) x : ℝ) : ℂ)) := by
        push_cast
        exact ((hv 0).mul (hpd 0)).add ((hv 1).mul (hpd 1))
      exact this.mul hφC
  have hCs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Cp x = 0 := fun x hx => by
    simp [hCp, hz1 x hx]
  have hBs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Bp x = 0 := fun x hx => by
    simp [hBp, hz1 x hx]
  have hEs : ∀ x : ℝ × ℝ, 2 * R < |x.2| → Ep x = 0 := fun x hx => by
    simp [hEp, hz1 x hx, pd_cut_zero hR 0 hx, pd_cut_zero hR 1 hx, lapP_cut_zero hR hx]
  have iC := integrableOn_w_mul c m R hwm hCc hCs
  have iB := integrableOn_w_mul c m R hwm hBc hBs
  have iE := integrableOn_w_mul c m R hwm hEc hEs
  -- force piece
  have hDj : ∀ j : Fin 2, IntegrableOn (fun x => u ρ x j *
      ((B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) * ladCutPhi φ R ρ x)) (B0579.cell c) := by
    intro j
    have hg : Continuous (fun x => (B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) *
        ladCutPhi φ R ρ x) := (hE j).mul (hχC.mul hφC)
    have hgs : MemLp (fun x => (B0579.pd j (UnforcedLeray.B0238.Ec tr ρ) x : ℂ) *
        ladCutPhi φ R ρ x) 2 (volume.restrict (B0579.cell c)) :=
      memLp_supp c R hg (fun x hx => by simp [ladCutPhi, hz1 x hx])
    exact (hum j).integrable_mul hgs
  have iD : IntegrableOn (fun x => ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) (B0579.cell c) := by
    have := (hDj 0).add (hDj 1)
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    simp only [ladForce, Pi.add_apply]; ring
  -- pointwise identity
  have hpt : ∀ x : ℝ × ℝ,
      ladFlowCx tr (w ρ) (u ρ) ρ (ladCutPhi φ R ρ) x + w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x) =
        w ρ x * Cp x - ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x + w ρ x * Ep x := by
    intro x
    have h := pointwise_split tr hχ hφs ρ (w ρ x) (u ρ x) x (ladDt φ ρ x) (ladChi tr φ ρ x)
      rfl
    unfold ladFlowCx
    have e : ladCutPhi φ R ρ = fun y => (ladCut R y : ℂ) * φ ρ y := rfl
    rw [e]
    simp only [hCp, hEp]
    linear_combination h
  have iFl : IntegrableOn (fun x => ladFlowCx tr (w ρ) (u ρ) ρ (ladCutPhi φ R ρ) x)
      (B0579.cell c) := by
    have := ((iC.sub iD).add iE).sub iB
    refine this.congr_fun (fun x _ => ?_) (B0579.measurableSet_cell c)
    have := hpt x
    simp only [Pi.add_apply, Pi.sub_apply]
    linear_combination -this
  unfold ladRate ladComm
  rw [← integral_add iFl iB]
  have : (fun x => ladFlowCx tr (w ρ) (u ρ) ρ (ladCutPhi φ R ρ) x +
      w ρ x * ((ladCut R x : ℂ) * ladDt φ ρ x)) =
      fun x => (w ρ x * Cp x - ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) + w ρ x * Ep x :=
    funext hpt
  rw [this]
  have h1 := integral_add (μ := volume.restrict (B0579.cell c))
    (f := fun x => w ρ x * Cp x - ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x)
    (g := fun x => w ρ x * Ep x) (iC.sub iD) iE
  have h2 := integral_sub (μ := volume.restrict (B0579.cell c))
    (f := fun x => w ρ x * Cp x) (g := fun x => ladForce tr (u ρ) ρ x * ladCutPhi φ R ρ x) iC iD
  rw [h1, h2]

end UnforcedLeray.Short.IIIa
