import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.MeanShift
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_6_3

/-!
# `PartIII-b:C/rep/8/1/1/2/3/2` (`meanYDiff`): the mean terms are differentiable off the axis

Source `the November 2 reference manuscript` lines 4776-4791, 5400-5406.

* `streamCut` of a field `Z` that is `C^∞` on the outward region `outReg` with the derivative decay
  `|D^k Z| ≲ (1+|w|)^{-(4+k)}` is differentiable everywhere (`sc_diffAt`): the cut vanishes
  identically where `(ε r)² < ν`, and on `outReg` it is a composition of smooth maps with the
  outward primitive `streamPsi Z` (`xsStreamPsi`).
* `mnYA`: `Z = W^mt_μ` (`xsYoungWSmooth`, `xsYoungWDecay`).
* `mnYB`: `D_{μ+1}𝒞(W_μ - W_{μ+1}) = D_{μ+1}X^mt` with `X^mt` of class `C^7` (`xmtSmooth`), and the
  stream cut of `D_{μ+1}(W_μ - W_{μ+1})` equals the cut of `W_μ` (`meanShiftIdentity`, rays stay in
  the young region), reducing to the first case.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- Where `(ε r)² < ν` the stream cut of every field vanishes. -/
theorem sc_zero_of_lt {ν ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hε : 0 < ε)
    (F : Vec3 → Vec3) {x : Vec3} (hx : (ε * cylR x) ^ 2 < ν) :
    streamCut ν ε χy F x = 0 := by
  have hz : chiYr ν ε χy (cylR x) = 0 := chiYr_zero_of_lt hχ hε hx
  have hd : deriv (chiYr ν ε χy) (cylR x) = 0 := by
    have hop : IsOpen {r : ℝ | (ε * r) ^ 2 < ν} :=
      isOpen_lt ((continuous_const.mul continuous_id).pow 2) continuous_const
    have : chiYr ν ε χy =ᶠ[nhds (cylR x)] fun _ => 0 := by
      filter_upwards [hop.mem_nhds hx] with r hr
      exact chiYr_zero_of_lt hχ hε hr
    rw [this.deriv_eq]; simp
  simp [streamCut, hz, hd]

/-- The stream cut of a field with smooth, decaying outward behaviour is differentiable. -/
theorem sc_diffAt {ν ε : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) (hν : 0 < ν) (hε : 0 < ε)
    (Z : Vec3 → Vec3) (hZs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Z (outReg ν ε))
    (hZd : ∀ a : ℝ, 5 * ν / (6 * ε ^ 2) < a → ∀ k : ℕ, ∃ C : ℝ, ∀ w : Vec3, a ≤ cylR w ^ 2 →
      ‖iteratedFDeriv ℝ k Z w‖ ≤ C * (1 + ‖w‖) ^ (-(4 + (k : ℝ)))) (y : Vec3) :
    DifferentiableAt ℝ (streamCut ν ε χy Z) y := by
  by_cases hy : (ε * cylR y) ^ 2 < ν
  · have hopen : IsOpen {y' : Vec3 | (ε * cylR y') ^ 2 < ν} :=
      isOpen_lt ((continuous_const.mul continuous_cylR).pow 2) continuous_const
    have hev : ∀ᶠ y' in nhds y, streamCut ν ε χy Z y' = 0 := by
      filter_upwards [hopen.mem_nhds hy] with y' hy'
      exact sc_zero_of_lt hχ hε Z hy'
    exact (differentiableAt_const (0 : Vec3)).congr_of_eventuallyEq hev
  · have hyU : y ∈ outReg ν ε := by
      unfold outReg
      simp only [mem_setOf_eq]
      rw [div_lt_iff₀ (by positivity)]
      push_neg at hy
      nlinarith
    have hb : 0 < 5 * ν / (6 * ε ^ 2) := by positivity
    have hΨ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (streamPsi Z) (outReg ν ε) := by
      refine xsStreamPsi _ Z hb hZs ?_
      intro a ha k
      exact hZd a ha k
    have hcyl : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cylR (outReg ν ε) := by
      intro y' hy'
      have hp : 0 < y' 0 ^ 2 + y' 1 ^ 2 := by
        have := hy'
        simp only [outReg, mem_setOf_eq, cylR] at this
        have h0 : 0 ≤ y' 0 ^ 2 + y' 1 ^ 2 := by positivity
        rw [Real.sq_sqrt h0] at this
        exact lt_of_le_of_lt (by positivity) this
      refine ContDiffAt.contDiffWithinAt ?_
      unfold cylR
      refine ContDiffAt.sqrt ?_ hp.ne'
      fun_prop
    have hpos : ∀ y' ∈ outReg ν ε, 0 < cylR y' := by
      intro y' hy'
      have := hy'
      simp only [outReg, mem_setOf_eq] at this
      have hnn : 0 ≤ cylR y' := Real.sqrt_nonneg _
      rcases hnn.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at this
        have : 0 < 5 * ν / (6 * ε ^ 2) := by positivity
        simp at *; linarith
    have hmaps : Set.MapsTo cylR (outReg ν ε) (Ioi 0) := fun y' hy' => hpos y' hy'
    have hchi := (chiYr_contDiffOn (ν := ν) hχ hε).comp hcyl hmaps
    have hdchi : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (chiYr ν ε χy)) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1
        (chiYr_contDiffOn (ν := ν) hχ hε)).2
    have hdchi' := hdchi.comp hcyl hmaps
    have hall : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (streamCut ν ε χy Z) (outReg ν ε) := by
      have : streamCut ν ε χy Z = fun y' =>
          chiYr ν ε χy (cylR y') • Z y' +
            (deriv (chiYr ν ε χy) (cylR y') / cylR y' * streamPsi Z y') • (![0, 0, 1] : Vec3) := by
        rfl
      rw [this]
      refine (hchi.smul hZs).add ?_
      exact ContDiffOn.smul
        ((hdchi'.div hcyl (fun y' hy' => (hpos y' hy').ne')).mul hΨ) contDiffOn_const
    exact (hall.contDiffAt ((isOpen_outReg ν ε).mem_nhds hyU)).differentiableAt (by simp)

/-- Differentiability of a phase-free field transfers to `Space`. -/
theorem mtField_diffAt {F : Vec3 → Vec3} {y : Space}
    (h : DifferentiableAt ℝ F (WithLp.ofLp y)) (τ : ℝ) : DifferentiableAt ℝ (mtField F τ) y := by
  have h1 : DifferentiableAt ℝ (fun y' : Space => (WithLp.ofLp y' : Vec3)) y :=
    ((PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ) (n := 1)).differentiable
      (by simp)) y
  have h2 : DifferentiableAt ℝ (fun v : Vec3 => (WithLp.toLp 2 v : Space)) (F (WithLp.ofLp y)) :=
    ((PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ) (n := 1)).differentiable
      (by simp)) _
  exact h2.comp y (h.comp y h1)

/-- The shifted dilation identity transfers to the stream cut: the cut of
`D_{μ+1}(W_μ - W_{μ+1})` is the cut of `W_μ` at every point. -/
theorem sc_dmu_eq {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (hL : LHyp c ν ε μ χo χy) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) (x : Vec3) :
    streamCut ν ε χy
        (dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) x =
      streamCut ν ε χy (youngW c ν ε μ χo M) x := by
  by_cases hx : (ε * cylR x) ^ 2 < ν
  · rw [sc_zero_of_lt hL.chiY hL.eps_pos _ hx, sc_zero_of_lt hL.chiY hL.eps_pos _ hx]
  · have hν := hL.nu_pos
    have hε := hL.eps_pos
    have hy : Real.sqrt ν / ε ≤ cylR x := by
      rw [div_le_iff₀ hε]
      push_neg at hx
      have h1 : Real.sqrt ν ≤ Real.sqrt ((ε * cylR x) ^ 2) := Real.sqrt_le_sqrt hx
      have hc0 : 0 ≤ cylR x := Real.sqrt_nonneg _
      rw [Real.sqrt_sq (mul_nonneg hε.le hc0)] at h1
      linarith
    have hpos : 0 < cylR x := lt_of_lt_of_le (div_pos (Real.sqrt_pos.2 hν) hε) hy
    have hZ : ∀ w : Vec3, Real.sqrt ν / ε ≤ cylR w →
        dmuFree ν (μ + 1) (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M) w =
          youngW c ν ε μ χo M w := fun w hw => meanShiftIdentity c ν ε μ χo χy hL M hM w hw
    have hpsi : streamPsi (dmuFree ν (μ + 1)
        (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) x =
        streamPsi (youngW c ν ε μ χo M) x := by
      unfold streamPsi
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
      have hρ' : cylR x < ρ := hρ
      rw [hZ (rayPt x ρ) (by rw [cylR_rayPt_pos hpos (hpos.trans hρ')]; exact hy.trans hρ'.le)]
    unfold streamCut
    rw [hZ x hy, hpsi]

/-- The mean terms are differentiable, for an old tensor with finite `N₀`. -/
theorem mean_diff_of {c ν ε μ : ℝ} {χo χy : ℝ → ℝ} (hL : LHyp c ν ε μ χo χy)
    {M : Chart → Mat3} (hM : OldThinFinite c ν M) (x : Vec3) :
    DifferentiableAt ℝ (streamCut ν ε χy (youngW c ν ε μ χo M)) x ∧
    DifferentiableAt ℝ (fun y => dmuFree ν (μ + 1)
        (streamCut ν ε χy (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y -
      streamCut ν ε χy (dmuFree ν (μ + 1)
        (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y) x := by
  have hν := hL.nu_pos
  have hε := hL.eps_pos
  have hA : ∀ y : Vec3, DifferentiableAt ℝ (streamCut ν ε χy (youngW c ν ε μ χo M)) y := fun y =>
    sc_diffAt hL.chiY hν hε _
      (xsYoungWSmooth c ν ε μ χo M hL.c_pos hν hε hL.mu_pos hL.chiO hM)
      (fun a ha k => xsYoungWDecay c ν ε μ χo M hL.c_pos hν hε hL.mu_pos hL.chiO hM a ha k) y
  refine ⟨hA x, ?_⟩
  have hcut : (fun y => streamCut ν ε χy (dmuFree ν (μ + 1)
        (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y) =
      streamCut ν ε χy (youngW c ν ε μ χo M) := funext fun y => sc_dmu_eq hL hM y
  have hX : ContDiff ℝ 7 (Xmt c ν ε μ χo χy M) := xmtSmooth c ν ε μ χo χy hL M hM
  have hfirst : DifferentiableAt ℝ (fun y => dmuFree ν (μ + 1)
      (streamCut ν ε χy (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y) x := by
    change DifferentiableAt ℝ (dmuFree ν (μ + 1) (Xmt c ν ε μ χo χy M)) x
    set X := Xmt c ν ε μ χo χy M with hXdef
    have h1 : ContDiff ℝ 6 (fderiv ℝ X) := hX.fderiv_right (by norm_num)
    have h1d : Differentiable ℝ (fderiv ℝ X) := h1.differentiable (by norm_num)
    have hr : Differentiable ℝ (fun y => fderiv ℝ X y y) := h1d.clm_apply differentiable_id
    have hlap : Differentiable ℝ (vecLap X) := by
      unfold vecLap
      refine Differentiable.fun_sum fun j _ => ?_
      have hg : ContDiff ℝ 6 (fun y' => fderiv ℝ X y' (Pi.single j 1)) :=
        h1.clm_apply contDiff_const
      have hg1 : ContDiff ℝ 5 (fderiv ℝ (fun y' => fderiv ℝ X y' (Pi.single j 1))) :=
        hg.fderiv_right (by norm_num)
      exact (hg1.differentiable (by norm_num)).clm_apply (differentiable_const _)
    have hXd : Differentiable ℝ X := hX.differentiable (by norm_num)
    unfold dmuFree
    exact ((hr.const_smul (-(1 / 2 : ℝ))).sub (hlap.const_smul ν)).add
      ((hXd.const_smul (μ + 1 - 1 / 2))) |>.differentiableAt
  have hsec : DifferentiableAt ℝ (fun y => streamCut ν ε χy (dmuFree ν (μ + 1)
        (youngW c ν ε μ χo M - youngW c ν ε (μ + 1) χo M)) y) x := by
    rw [hcut]; exact hA x
  exact hfirst.sub hsec

/-- The mean terms of the receiver `Y` at one level. -/
theorem meanYDiffAt_of (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hOld : LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → ∀ T : LStr Pl K L,
      OldThinFinite (cOf L.ν) L.ν (thinRep T)) :
    MeanYDiffAt Pl K L μ := by
  intro hL T
  refine Filter.Eventually.of_forall (fun τ y _ => ?_)
  obtain ⟨h1, h2⟩ := mean_diff_of hL (hOld hL T) (WithLp.ofLp y)
  exact ⟨mtField_diffAt h1 τ, mtField_diffAt h2 τ⟩

/-- **`PartIII-b:C/rep/8/1/1/2/3/2`**: the mean terms `mnYA`, `mnYB` are differentiable off the
axis (source 4776-4791, 5400-5406). -/
theorem meanYDiff (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3.MeanYDiff D := by
  obtain ⟨C, k, hC⟩ := sourceLN0 D.K.mZ (gRate D.Pl) hst.mZ_gt hst.gamma_pos
  refine Filter.Eventually.of_forall (fun n z _ => ?_)
  refine meanYDiffAt_of D.Pl D.K (D.level n) (D.mu n z) (fun hL T => ?_)
  exact (hC (cOf (D.level n).ν) (D.level n).ν ((D.level n).ρb D.Pl D.K)
    hL.c_pos hL.nu_pos hL.nu_le T).1

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
