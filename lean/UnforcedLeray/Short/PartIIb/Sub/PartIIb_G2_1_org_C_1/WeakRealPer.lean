import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org_C
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.LinearVersion
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail.Leaves
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.RawProfileLate

/-!
# Helper `WeakRealPer` for `PartII-b:G2/1/org/C/1` (`PhysKOutCand`)

1. Real projection `reProj` of complex meridional profiles preserves `HasWeakVec` when the base
   profile `b` is real (`im = 0`), produces a real profile, and does not increase `hNorm`.
2. `qShift c`-invariant first-order operators `(vQ ε, dQ ε)` and `(vEta, dZero)` preserve
   `QPeriodic c` of weak derivatives (`hasWeakVec_qPeriodic`).
3. `kOutChart p b Qb Eb` is real, `QPeriodic p.c`, and `AEStronglyMeasurable` on `hMeas p.c bgp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.PhysKOutCandHelp

open UnforcedLeray.Short.IIb
open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Pointwise projection of a complex meridional profile onto its real part. -/
def reProj (g : CProf) : CProf := fun x => liftM (reM (g x))

theorem reProj_im_zero (g : CProf) (x : Coord) (i : Fin 2) : (reProj g x i).im = 0 := by
  simp [reProj, liftM]

theorem norm_reProj_le (g : CProf) (x : Coord) : ‖reProj g x‖ ≤ ‖g x‖ := by
  rw [reProj, liftM_norm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simp only [reM, WithLp.ofLp_toLp, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm (g x i)

theorem norm_sqrtS_reProj_le (g : CProf) (x : Coord) :
    ‖sqrtS (reProj g) x‖ ≤ ‖sqrtS g x‖ := by
  simp only [sqrtS, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_reProj_le g x) (norm_nonneg _)

theorem hNorm_sqrtS_reProj_le {c r : ℝ} (g : CProf) :
    hNorm c r (sqrtS (reProj g)) ≤ hNorm c r (sqrtS g) :=
  eLpNorm_mono_ae (Filter.Eventually.of_forall (norm_sqrtS_reProj_le g))

private theorem ofReal_re_mul_ofReal (z : ℂ) (r : ℝ) :
    ((z.re : ℂ) * (r : ℂ)) = (((z * (r : ℂ)).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

private theorem hasWeakFO_re {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g : Coord → ℂ}
    (hu : ∀ x, (u x).im = 0) (h : HasWeakFO v d u g) :
    HasWeakFO v d u (fun x => ((g x).re : ℂ)) := by
  refine ⟨fun φ hφ => ⟨(h.1 φ hφ).1, ?_⟩, fun φ hφ => ?_⟩
  · have hi : Integrable (fun x => (((g x * (φ x : ℂ)).re : ℝ) : ℂ)) :=
      Complex.ofRealCLM.integrable_comp (Complex.reCLM.integrable_comp (h.1 φ hφ).2)
    exact hi.congr (Eventually.of_forall fun x => (ofReal_re_mul_ofReal (g x) (φ x)).symm)
  · have eL : (fun x => ((g x).re : ℂ) * (φ x : ℂ)) =
        fun x => Complex.ofRealCLM (Complex.reCLM (g x * (φ x : ℂ))) :=
      funext fun x => ofReal_re_mul_ofReal (g x) (φ x)
    have eR : (fun x => u x * (coordTranspose v d φ x : ℂ)) =
        fun x => Complex.ofRealCLM (Complex.reCLM (u x * (coordTranspose v d φ x : ℂ))) := by
      funext x
      apply Complex.ext <;> simp [hu x]
    rw [eL, Complex.ofRealCLM.integral_comp_comm
      (Complex.reCLM.integrable_comp (h.1 φ hφ).2),
      Complex.reCLM.integral_comp_comm (h.1 φ hφ).2, h.2 φ hφ,
      ← Complex.reCLM.integral_comp_comm (h.1 φ hφ).1,
      ← Complex.ofRealCLM.integral_comp_comm (Complex.reCLM.integrable_comp (h.1 φ hφ).1), ← eR]

theorem hasWeakVec_reProj {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b g : CProf}
    (hb : ∀ x i, (b x i).im = 0) (h : HasWeakVec v d b g) :
    HasWeakVec v d b (reProj g) := by
  intro i
  simpa [reProj, liftM, reM] using hasWeakFO_re (fun x => hb x i) (h i)

/-! ### `QPeriodic` of weak derivatives under `qShift`-invariant operators -/

private theorem hasWeakFO_shift_inv (c : ℝ) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    (hv : ∀ x, v (qShift c x) = v x) (hd : ∀ x, d (qShift c x) = d x)
    {u g : Coord → ℂ} (h : HasWeakFO v d u g) :
    HasWeakFO v d (fun x => u (qShift c x)) (fun x => g (qShift c x)) := by
  set e := F8L.shiftVec c
  have hS : ∀ x, qShift c x + -e = x := by
    intro x; rw [F8L.qShift_eq]; simp [e]
  have hS' : ∀ z, qShift c (z + -e) = z := by
    intro z; rw [F8L.qShift_eq]; simp [e]
  have hv' : ∀ z, v (z + -e) = v z := fun z => by rw [← hv (z + -e), hS']
  have hd' : ∀ z, d (z + -e) = d z := fun z => by rw [← hd (z + -e), hS']
  have htest : ∀ φ, IsCoordTest φ → IsCoordTest (fun y => φ (y + -e)) := by
    intro φ hφ
    refine ⟨hφ.smooth.comp (contDiff_id.add contDiff_const),
      hφ.compact.comp_homeomorph (Homeomorph.addRight (-e)), ?_⟩
    have hc : IsClosed ((fun y : Coord => y + -e) ⁻¹' tsupport φ) :=
      (isClosed_tsupport φ).preimage (continuous_id.add continuous_const)
    have hsub : tsupport (fun y => φ (y + -e)) ⊆ (fun y : Coord => y + -e) ⁻¹' tsupport φ :=
      closure_minimal (fun y hy => subset_tsupport φ (by simpa [Function.mem_support] using hy)) hc
    intro y hy
    have := hφ.supp (hsub hy)
    simpa [e, F8L.shiftVec] using this
  have hTr : ∀ φ y, coordTranspose v d (fun z => φ (z + -e)) y = coordTranspose v d φ (y + -e) := by
    intro φ y
    unfold coordTranspose
    rw [← hd' y]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      let G : Coord → ℝ := fun w => v w j * φ w
      have hfn : (fun z => v z j * φ (z + -e)) = fun z => G (z + -e) := by
        funext z
        simp [G, hv' z]
      unfold cpd
      rw [hfn, fderiv_comp_add_right]
  have hmp := F8L.shift_mp c
  have hem := F8L.shift_emb c
  have I1 : ∀ φ, IsCoordTest φ →
      Integrable (fun y => u y * ((coordTranspose v d φ (y + -e) : ℝ) : ℂ)) := by
    intro φ hφ
    exact ((h.1 _ (htest φ hφ)).1).congr (Eventually.of_forall fun y => by simp [hTr φ y])
  have I2 : ∀ φ, IsCoordTest φ → Integrable (fun y => g y * (φ (y + -e) : ℂ)) :=
    fun φ hφ => (h.1 _ (htest φ hφ)).2
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · exact ((hmp.integrable_comp_emb hem).2 (I1 φ hφ)).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · exact ((hmp.integrable_comp_emb hem).2 (I2 φ hφ)).congr
      (Eventually.of_forall fun x => by simp [Function.comp, hS])
  · have e1 : ∫ x, g (qShift c x) * (φ x : ℂ) = ∫ y, g y * (φ (y + -e) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem (fun y => g y * (φ (y + -e) : ℂ))
    have e2 : ∫ x, u (qShift c x) * (coordTranspose v d φ x : ℂ) =
        ∫ y, u y * ((coordTranspose v d φ (y + -e) : ℝ) : ℂ) := by
      simpa [hS] using hmp.integral_comp hem
        (fun y => u y * ((coordTranspose v d φ (y + -e) : ℝ) : ℂ))
    rw [e1, e2, h.2 _ (htest φ hφ)]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp [hTr φ y])

theorem hasWeakVec_qPeriodic {c : ℝ} {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    (hv : ∀ x, v (qShift c x) = v x) (hd : ∀ x, d (qShift c x) = d x)
    {b g : CProf} (hb : QPeriodic c b) (hw : HasWeakVec v d b g) :
    QPeriodic c g := by
  have hi : ∀ i : Fin 2,
      (fun x => g (qShift c x) i) =ᵐ[volume.restrict {x : Coord | 0 < x.1}] (fun x => g x i) := by
    intro i
    have h1 := hasWeakFO_shift_inv c hv hd (hw i)
    have hu : (fun x => b (qShift c x) i) =ᵐ[volume.restrict {x : Coord | 0 < x.1}]
        (fun x => b x i) := by
      filter_upwards [hb] with x hx
      rw [hx]
    have h2 := F8L.hasWeakFO_congr v d hu (Filter.EventuallyEq.refl _ _) h1
    exact F8L.weak_unique v d h2 (hw i)
  unfold QPeriodic
  filter_upwards [ae_all_iff.2 hi] with x hx
  ext i
  exact hx i

theorem qPeriodic_sqrtS {c : ℝ} {g : CProf} (hg : QPeriodic c g) : QPeriodic c (sqrtS g) := by
  unfold QPeriodic at hg ⊢
  filter_upwards [hg] with x hx
  simp only [sqrtS]
  rw [show (qShift c x).1 = x.1 from rfl, hx]

/-! ### Realness, `q`-periodicity, and `hMeas`-measurability of `kOutChart` -/

theorem kOutChart_im_zero (p : Params) {b Qb Eb : CProf}
    (hb : ∀ x i, (b x i).im = 0) (hQb : ∀ x i, (Qb x i).im = 0)
    (hEb : ∀ x i, (Eb x i).im = 0) (x : Coord) (i : Fin 2) :
    (kOutChart p b Qb Eb x i).im = 0 := by
  simp [kOutChart, cplx, hb x 0, hb x 1, hb x i, hQb x i, hEb x i]

private theorem qPer_fderiv_pos {F : Coord → Axi.Merid} {c : ℝ}
    (hF : ∀ y : Coord, 0 < y.1 → F (qShift c y) = F y) {x : Coord} (hx : 0 < x.1) :
    fderiv ℝ F (qShift c x) = fderiv ℝ F x := by
  have hopen : IsOpen {y : Coord | 0 < y.1} := isOpen_lt continuous_const continuous_fst
  have hev : (fun y => F (qShift c y)) =ᶠ[𝓝 x] F := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hF y hy
  have hfun : (fun y => F (qShift c y)) = fun y => F (y + F8L.shiftVec c) :=
    funext fun y => by rw [F8L.qShift_eq]
  have h1 : fderiv ℝ (fun y => F (qShift c y)) x = fderiv ℝ F x := hev.fderiv_eq
  rw [hfun, fderiv_comp_add_right, ← F8L.qShift_eq] at h1
  exact h1

theorem kOutChart_qPeriodic (p : Params) {b Qb Eb : CProf}
    (hb : QPeriodic p.c b) (hQb : QPeriodic p.c Qb) (hEb : QPeriodic p.c Eb) :
    QPeriodic p.c (kOutChart p b Qb Eb) := by
  have hraw : ∀ y : Coord, 0 < y.1 → rawProf p (qShift p.c y) = rawProf p y :=
    fun y hy => UnforcedLeray.Cons.C03.rawProfile_periodic p.train hy y.2.1 y.2.2
  have hpos_ae : ∀ᵐ x ∂(volume.restrict {x : Coord | 0 < x.1}), 0 < x.1 :=
    ae_restrict_mem (measurableSet_lt measurable_const measurable_fst)
  unfold QPeriodic at hb hQb hEb ⊢
  filter_upwards [hpos_ae, hb, hQb, hEb] with x hx hbx hQbx hEbx
  have hfd := qPer_fderiv_pos hraw hx
  have hdEta : Axi.dEta (rawProf p) (qShift p.c x) = Axi.dEta (rawProf p) x := by
    unfold Axi.dEta; rw [hfd]
  have hqEps : qEps p.ε (rawProf p) (qShift p.c x) = qEps p.ε (rawProf p) x := by
    unfold qEps kAge Axi.dQ Axi.dS Axi.dEta
    rw [hfd, hraw x hx]
    rfl
  have hdiv : chartDivR p.ε (rawProf p) (qShift p.c x) = chartDivR p.ε (rawProf p) x := by
    unfold chartDivR
    rw [hqEps, hdEta, hraw x hx]
  have hs1 : (qShift p.c x).1 = x.1 := rfl
  unfold kOutChart
  rw [hs1, hraw x hx, hQbx, hEbx, hbx, hdiv]
  have hc1 : cplx (qEps p.ε (rawProf p)) (qShift p.c x) = cplx (qEps p.ε (rawProf p)) x := by
    simp [cplx, hqEps]
  have hc2 : cplx (Axi.dEta (rawProf p)) (qShift p.c x) = cplx (Axi.dEta (rawProf p)) x := by
    simp [cplx, hdEta]
  rw [hc1, hc2]

private theorem aestronglyMeasurable_hMeas_of_contOn_pos {E : Type*}
    [NormedAddCommGroup E]
    {c : ℝ} (hc : 0 < c) {f : Coord → E}
    (hf : ContinuousOn f {x : Coord | 0 < x.1}) :
    AEStronglyMeasurable f (hMeas c bgp) := by
  let U : Set Coord := {x : Coord | 0 < x.1}
  have hUm : MeasurableSet U := measurableSet_lt measurable_const measurable_fst
  have hae : ∀ᵐ x ∂hMeas c bgp, x ∈ U :=
    (Axi.ae_ageμ_mem hc (bgp / 2 - 5 / 2)).mono fun _ hx => hx.1
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact hf.aestronglyMeasurable hUm

private theorem rawProf_contDiffOn_pos {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) :
    ContDiffOn ℝ ∞ (rawProf p) {x : Coord | 0 < x.1} := by
  let U0 : Set Coord := Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))
  have hUeq : {x : Coord | 0 < x.1} = U0 := by ext x; simp [U0]
  rw [hUeq]
  have hUopen : IsOpen U0 := isOpen_Ioi.prod isOpen_univ
  have hv : ContDiffOn ℝ ∞ (fun x : Coord => p.train.v x.1 x.2) U0 :=
    p.train.isTrain.smooth_v.mono (fun x (hx : x ∈ U0) => ⟨show (0 : ℝ) ≤ x.1 from le_of_lt hx.1, trivial⟩)
  have hΨ : ContDiffOn ℝ ∞ (fun x : Coord => p.train.ψ x.1 x.2) U0 := hreg.train_stream_smooth
  have hΨd : ∀ x ∈ U0, DifferentiableAt ℝ (fun x : Coord => p.train.ψ x.1 x.2) x :=
    fun x hx => (hΨ.differentiableOn (by simp)).differentiableAt (hUopen.mem_nhds hx)
  have hD1 : ContDiffOn ℝ ∞
      (fun x : Coord => deriv (fun t => p.train.ψ x.1 (x.2.1, t)) x.2.2) U0 :=
    ((hΨ.fderiv_of_isOpen hUopen (m := ∞) (by simp)).clm_apply contDiffOn_const).congr
      (fun x hx => by
        have hline : HasDerivAt (fun t : ℝ => ((x.1, (x.2.1, t)) : Coord)) (0, (0, 1)) x.2.2 :=
          (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _))
        exact ((hΨd x hx).hasFDerivAt.comp_hasDerivAt x.2.2 hline).deriv)
  have hD2 : ContDiffOn ℝ ∞
      (fun x : Coord => deriv (fun t => p.train.ψ t (x.2.1, x.2.2)) x.1) U0 :=
    ((hΨ.fderiv_of_isOpen hUopen (m := ∞) (by simp)).clm_apply contDiffOn_const).congr
      (fun x hx => by
        have hline : HasDerivAt (fun t : ℝ => ((t, (x.2.1, x.2.2)) : Coord)) (1, (0, 0)) x.1 :=
          (hasDerivAt_id _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
        exact ((hΨd x hx).hasFDerivAt.comp_hasDerivAt x.1 hline).deriv)
  have hRS : ContDiffOn ℝ ∞
      (fun x : Coord => UnforcedLeray.Cons.C03.raisedStream p.train.ψ x.1 x.2.1 x.2.2) U0 := by
    unfold UnforcedLeray.Cons.C03.raisedStream
    exact (hΨ.sub (((contDiff_snd.comp contDiff_snd).contDiffOn.mul hD1).add
      (((contDiff_const.mul contDiff_fst).contDiffOn).mul hD2))).congr (fun _ _ => rfl)
  unfold rawProf UnforcedLeray.Cons.C03.rawProfile
  exact hv.add (((contDiffOn_const (c := p.ε)).mul hRS).smul
    (contDiffOn_const (c := EuclideanSpace.single (1 : Fin 2) (1 : ℝ))))

theorem kOutChart_aestronglyMeasurable {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp)
    {b Qb Eb : CProf} (hb : AEStronglyMeasurable b (hMeas p.c bgp))
    (hQb : AEStronglyMeasurable Qb (hMeas p.c bgp))
    (hEb : AEStronglyMeasurable Eb (hMeas p.c bgp)) :
    AEStronglyMeasurable (kOutChart p b Qb Eb) (hMeas p.c bgp) := by
  let U : Set Coord := {x : Coord | 0 < x.1}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_fst
  have hG := rawProf_contDiffOn_pos hreg
  have hfd : ∀ v : Coord, ContDiffOn ℝ ∞ (fun x => fderiv ℝ (rawProf p) x v) U :=
    fun v => (hG.fderiv_of_isOpen hUopen (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hdS : ContDiffOn ℝ ∞ (Axi.dS (rawProf p)) U := hfd (1, (0, 0))
  have hdQ : ContDiffOn ℝ ∞ (Axi.dQ (rawProf p)) U := hfd (0, (1, 0))
  have hdE : ContDiffOn ℝ ∞ (Axi.dEta (rawProf p)) U := hfd (0, (0, 1))
  have hkA : ContDiffOn ℝ ∞ (kAge (rawProf p)) U :=
    (((contDiff_const.mul contDiff_fst).contDiffOn).smul hdS).add
      (((contDiff_snd.comp contDiff_snd).contDiffOn).smul hdE)
  have hqE : ContDiffOn ℝ ∞ (qEps p.ε (rawProf p)) U :=
    hdQ.sub ((contDiffOn_const (c := p.ε)).smul (hkA.add hG))
  have hpr : ∀ (F : Coord → Axi.Merid), ContDiffOn ℝ ∞ F U → ∀ j : Fin 2,
      ContDiffOn ℝ ∞ (fun x => F x j) U :=
    fun _ hF j => (EuclideanSpace.proj j : Axi.Merid →L[ℝ] ℝ).contDiff.comp_contDiffOn hF
  have hdiv : ContDiffOn ℝ ∞ (chartDivR p.ε (rawProf p)) U :=
    ((hpr _ hqE 0).add (contDiffOn_const.mul (hpr _ hG 0))).add (hpr _ hdE 1)
  have hc_ofReal : ∀ {f : Coord → ℝ}, ContDiffOn ℝ ∞ f U →
      AEStronglyMeasurable (fun x => ((f x : ℝ) : ℂ)) (hMeas p.c bgp) :=
    fun hf => aestronglyMeasurable_hMeas_of_contOn_pos p.c_pos
      (Complex.continuous_ofReal.comp_continuousOn hf.continuousOn)
  have hc_cplx : ∀ {F : Coord → Axi.Merid}, ContDiffOn ℝ ∞ F U →
      AEStronglyMeasurable (cplx F) (hMeas p.c bgp) :=
    fun hF => aestronglyMeasurable_hMeas_of_contOn_pos p.c_pos
      (continuous_liftM.comp_continuousOn hF.continuousOn)
  have hs : AEStronglyMeasurable (fun x : Coord => ((x.1 : ℝ) : ℂ)) (hMeas p.c bgp) :=
    (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable
  have hb0 : AEStronglyMeasurable (fun x => b x 0) (hMeas p.c bgp) :=
    (EuclideanSpace.proj (0 : Fin 2) : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb
  have hb1 : AEStronglyMeasurable (fun x => b x 1) (hMeas p.c bgp) :=
    (EuclideanSpace.proj (1 : Fin 2) : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable hb
  unfold kOutChart
  exact hs.smul ((((hc_ofReal (hpr _ hG 0)).smul hQb).add ((hc_ofReal (hpr _ hG 1)).smul hEb)).add
    ((hb0.smul (hc_cplx hqE)).add (hb1.smul (hc_cplx hdE))) |>.add
    ((hc_ofReal hdiv).smul hb))

end UnforcedLeray.Short.IIb.PhysKOutCandHelp
