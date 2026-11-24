import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts.FrozenDatumSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletSmoothExt
import UnforcedLeray.Short.PartIIa.Tasks.R08InletSolenoidal.InletDivZero
import UnforcedLeray.Short.PartIIa.Tasks.R09InletScalingNonzero
import UnforcedLeray.Short.PartIIa.Sub.R10_homog
import UnforcedLeray.Loc.L09CompactDatum.Defect
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Smoothness, solenoidality, derivative bounds, and `L^{3,∞} ∩ L²_loc` for `p.datum α`

Helper for `PartII-b:B2` (`Short/PartII-b/Tasks/DatumFacts.lean`).
Establishes for every `α : Fin 2 → ℝ` (at `p.ν ≤ ν₀` in `BgRegime`):
* `ContDiffOn ℝ ∞ (p.datum α) {0}ᶜ`
* `∀ x ≠ 0, Axi.divergence (p.datum α) x = 0`
* `∀ k ≤ 4, ∃ C, ∀ x ≠ 0, ‖iteratedFDeriv ℝ k (p.datum α) x‖ * ‖x‖ ^ (k + 1) ≤ C`
* `p.datum α ∈ L^{3,∞}(ℝ³) ∩ L²_loc(ℝ³)`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.DatumFactsAux

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIa

/-- Additivity of `datumProfile ε` for differentiable streams. -/
theorem datumProfile_add (ε : ℝ) {Ψ₁ Ψ₂ : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h₁ : DifferentiableAt ℝ Ψ₁ x) (h₂ : DifferentiableAt ℝ Ψ₂ x) :
    datumProfile ε (fun y => Ψ₁ y + Ψ₂ y) x = datumProfile ε Ψ₁ x + datumProfile ε Ψ₂ x := by
  have hfd : fderiv ℝ (fun y => Ψ₁ y + Ψ₂ y) x = fderiv ℝ Ψ₁ x + fderiv ℝ Ψ₂ x :=
    (h₁.hasFDerivAt.add h₂.hasFDerivAt).fderiv
  unfold datumProfile partialEta partialXi
  rw [hfd]
  simp only [add_apply]
  module

/-- Scalar multiplication of `datumProfile ε` for a differentiable stream. -/
theorem datumProfile_const_mul (ε a : ℝ) {Ψ : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (h : DifferentiableAt ℝ Ψ x) :
    datumProfile ε (fun y => a * Ψ y) x = a • datumProfile ε Ψ x := by
  have hfd : fderiv ℝ (fun y => a * Ψ y) x = a • fderiv ℝ Ψ x :=
    (h.hasFDerivAt.const_mul a).fderiv
  unfold datumProfile partialEta partialXi
  rw [hfd]
  simp only [smul_apply, smul_eq_mul]
  module

/-- Additivity of `Nv R · τ`. -/
theorem Nv_add (R τ : ℝ) (b₁ b₂ : E3 → Axi.Merid) (y : Space) :
    Axi.Nv R (fun m => b₁ m + b₂ m) τ y = Axi.Nv R b₁ τ y + Axi.Nv R b₂ τ y := by
  unfold Axi.Nv
  rw [map_add, smul_add]

/-- Scalar multiplication of `Nv R · τ`. -/
theorem Nv_const_smul (R τ a : ℝ) (b : E3 → Axi.Merid) (y : Space) :
    Axi.Nv R (fun m => a • b m) τ y = a • Axi.Nv R b τ y := by
  unfold Axi.Nv
  rw [map_smul, smul_comm]

/-- Off the axis, `Nv R (fun m => datumProfile R⁻¹ ψ m.2) 0 y` equals
`Axi.streamLift (Axi.ringStream R 0 (fun n => ψ n.2)) y` for any differentiable stream `ψ`. -/
theorem Nv_datumProfile_eq_streamLift {R : ℝ} (hR : 0 < R) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {y : Space} (hy : y ∉ Axi.axis) :
    Axi.Nv R (fun m => datumProfile R⁻¹ ψ m.2) 0 y =
      Axi.streamLift (Axi.ringStream R 0 (fun n => ψ n.2)) y := by
  have hdψ : ∀ x : ℝ × ℝ, DifferentiableAt ℝ ψ x := fun x => hψ.differentiable (by simp) x
  have hφ : DifferentiableAt ℝ (fun n : E3 => ψ n.2) (Axi.chart R 0 y) :=
    (hdψ _).comp _ differentiableAt_snd
  rw [Axi.ringStreamLift_components hR hy hφ]
  unfold Axi.Nv
  congr 2
  have hcut := Axi.ringStreamProfile_cutoff R (χ := fun _ : ℝ => (1 : ℝ)) (ψ := ψ)
    (m := Axi.chart R 0 y) (differentiableAt_const _) (hdψ _)
  simp only [one_mul, deriv_const', mul_zero, sub_zero] at hcut
  exact hcut.symm

/-- For `c > 0` and `R > 0`, the ring lift of `datumProfile R⁻¹ (B0140.trainStream c)` is
`inletRaw c R` everywhere on `Space`. -/
theorem Nv_trainStream_eq_inletRaw {c R : ℝ} (hc : 0 < c) (hR : 0 < R) :
    Axi.Nv R (fun m => datumProfile R⁻¹ (UnforcedLeray.B0140.trainStream c) m.2) 0 =
      inletRaw c R := by
  ext y : 1
  by_cases hy : y ∈ Axi.axis
  · have hρ : Axi.ϱ y = 0 := (Axi.mem_axis_iff y).1 hy
    have h1 : Axi.Nv R (fun m => datumProfile R⁻¹ (UnforcedLeray.B0140.trainStream c) m.2) 0 y = 0 := by
      simp [Axi.Nv, Axi.age, hρ]
    rw [h1, inletRaw_eq_zero_of_mem_axis c R hy]
  · have hψ : ContDiff ℝ ∞ (UnforcedLeray.B0140.trainStream c) := by
      have heq : UnforcedLeray.B0140.trainStream c = fun z : ℝ × ℝ => trainDatum c z.1 z.2 := by
        funext z
        exact (trainDatum_eq_trainStream c z.1 z.2).symm
      rw [heq]
      exact InletDivZeroAux.contDiff_trainDatum hc.ne'
    rw [Nv_datumProfile_eq_streamLift hR hψ hy]
    have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hy
    have hev : Axi.ringStream R 0 (fun n : E3 => UnforcedLeray.B0140.trainStream c n.2) =ᶠ[𝓝 (Axi.mer y)]
        InletDivZeroAux.streamPair c R := by
      have hU : {q : ℝ × ℝ | 0 < q.1} ∈ 𝓝 (Axi.mer y) :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds hρ
      filter_upwards [hU] with q hq
      rw [Axi.ringStream_datum hR _ hq]
      unfold InletDivZeroAux.streamPair inletStream
      rw [trainDatum_eq_trainStream]
    have hfd : fderiv ℝ (Axi.ringStream R 0 (fun n : E3 => UnforcedLeray.B0140.trainStream c n.2)) (Axi.mer y) =
        fderiv ℝ (InletDivZeroAux.streamPair c R) (Axi.mer y) := hev.fderiv_eq
    have hd : DifferentiableAt ℝ (InletDivZeroAux.streamPair c R) (Axi.mer y) :=
      (InletDivZeroAux.contDiffAt_streamPair hc.ne' hR.ne' hρ).differentiableAt (by norm_num)
    rw [← InletDivZeroAux.liftMer_profileB_eq c R hy hd]
    unfold Axi.streamLift Axi.liftMer Axi.streamProfile InletDivZeroAux.profileB Axi.dz Axi.dρ
      InletDivZeroAux.e0M InletDivZeroAux.e1M Axi.m0 Axi.m1
    rw [hfd]

/-- `inletRaw c R` is `C^∞` on `{0}ᶜ` for `c > 0`, `R ≥ 2`. -/
theorem contDiffOn_inletRaw {c R : ℝ} (hc : 0 < c) (hR : 2 ≤ R) :
    ContDiffOn ℝ ∞ (inletRaw c R) {0}ᶜ := by
  have hflat : InletRawFlat :=
    inletRawFlat_of_calculus thetaRegular inletRawClosedForm flatSmul flatAddCongr tameInvRho
      tameCoord tameLog tameCompBdd flatExpOfTame
  have hsm : ContDiffOn ℝ ∞ (inletRaw c R) Axi.axisᶜ := (hflat c R hc hR 1 1 one_pos).1
  have hat : ∀ x₀ ∈ Axi.axis, x₀ 2 ≠ 0 → ContDiffAt ℝ ∞ (inletRaw c R) x₀ :=
    axisFlatSmooth _ hsm (fun y hy => inletRaw_eq_zero_of_mem_axis c R hy)
      (fun δ M hδ => ⟨R ^ 2 * δ ^ 2 / 4, by positivity, hflat c R hc hR δ M hδ⟩)
  intro x hx
  by_cases hxa : x ∈ Axi.axis
  · have hz : x 2 ≠ 0 := fun h => hx (eq_zero_of_mem_axis_of_snd_eq_zero hxa h)
    exact (hat x hxa hz).contDiffWithinAt
  · exact (hsm.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hxa)).contDiffWithinAt

/-- Decomposition of `p.datum α` into `inletRaw p.c p.R` plus the frozen-stream datum columns. -/
theorem datum_eq_inletRaw_add_frozen {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} (hc1 : 1 ≤ p.c) (hmode : p.mode = q)
    (α : Fin 2 → ℝ) (y : Space) :
    p.datum α y = inletRaw p.c p.R y +
      ∑ i : Fin 2, α i • Axi.Nv p.R (fun m => datumProfile p.ε (p.frozenStream i) m.2) 0 y := by
  have hc0 : 0 < p.c := lt_of_lt_of_le one_pos hc1
  have hψ0_eq : p.train.ψ 0 = UnforcedLeray.B0140.trainStream p.c :=
    p.train.isTrain.stream_zero hc1
  have hψ0_cd : ContDiff ℝ ∞ (UnforcedLeray.B0140.trainStream p.c) := by
    have heq : UnforcedLeray.B0140.trainStream p.c = fun z : ℝ × ℝ => trainDatum p.c z.1 z.2 :=
      funext fun z => (trainDatum_eq_trainStream p.c z.1 z.2).symm
    rw [heq]
    exact InletDivZeroAux.contDiff_trainDatum hc0.ne'
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hfro_cd : ∀ i : Fin 2, ContDiff ℝ ∞ (p.frozenStream i) :=
    fun i => inletCD_frozenStream (hper p.c hc1).1 hmode i
  have hprof : (fun m : E3 => datumProfile p.ε (p.datumStream α) m.2) =
      fun m : E3 => datumProfile p.ε (UnforcedLeray.B0140.trainStream p.c) m.2 +
        (α 0 • datumProfile p.ε (p.frozenStream 0) m.2 +
          α 1 • datumProfile p.ε (p.frozenStream 1) m.2) := by
    funext m
    have hd0 : DifferentiableAt ℝ (UnforcedLeray.B0140.trainStream p.c) m.2 :=
      hψ0_cd.differentiable (by simp) m.2
    have hdf0 : DifferentiableAt ℝ (p.frozenStream 0) m.2 := (hfro_cd 0).differentiable (by simp) m.2
    have hdf1 : DifferentiableAt ℝ (p.frozenStream 1) m.2 := (hfro_cd 1).differentiable (by simp) m.2
    have heq : p.datumStream α = fun x => UnforcedLeray.B0140.trainStream p.c x +
        (α 0 * p.frozenStream 0 x + α 1 * p.frozenStream 1 x) := by
      funext x
      unfold Params.datumStream
      rw [hψ0_eq, Fin.sum_univ_two]
    rw [heq, datumProfile_add p.ε hd0 ((hdf0.const_mul (α 0)).fun_add (hdf1.const_mul (α 1))),
      datumProfile_add p.ε (hdf0.const_mul (α 0)) (hdf1.const_mul (α 1)),
      datumProfile_const_mul p.ε (α 0) hdf0, datumProfile_const_mul p.ε (α 1) hdf1]
  unfold Params.datum
  rw [hprof, Nv_add, Nv_add, Nv_const_smul, Nv_const_smul, Fin.sum_univ_two]
  have hRinv : p.ε = p.R⁻¹ := (inv_inv p.ε).symm
  rw [hRinv, Nv_trainStream_eq_inletRaw hc0 p.R_pos]

/-- Smoothness of `p.datumStream α` for `1 ≤ p.c`. -/
theorem contDiff_datumStream {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {p : Params} (hc1 : 1 ≤ p.c) (hmode : p.mode = q)
    (α : Fin 2 → ℝ) : ContDiff ℝ ∞ (p.datumStream α) := by
  have hc0 : 0 < p.c := lt_of_lt_of_le one_pos hc1
  have hψ0_eq : p.train.ψ 0 = UnforcedLeray.B0140.trainStream p.c :=
    p.train.isTrain.stream_zero hc1
  have hψ0_cd : ContDiff ℝ ∞ (UnforcedLeray.B0140.trainStream p.c) := by
    have heq : UnforcedLeray.B0140.trainStream p.c = fun z : ℝ × ℝ => trainDatum p.c z.1 z.2 :=
      funext fun z => (trainDatum_eq_trainStream p.c z.1 z.2).symm
    rw [heq]
    exact InletDivZeroAux.contDiff_trainDatum hc0.ne'
  obtain ⟨_, _, _, -, -, hper⟩ := frozenStreamBounds lam q hq 0
  have hfro_cd : ∀ i : Fin 2, ContDiff ℝ ∞ (p.frozenStream i) :=
    fun i => inletCD_frozenStream (hper p.c hc1).1 hmode i
  have heq : p.datumStream α = fun x => UnforcedLeray.B0140.trainStream p.c x +
      (α 0 * p.frozenStream 0 x + α 1 * p.frozenStream 1 x) := by
    funext x
    unfold Params.datumStream
    rw [hψ0_eq, Fin.sum_univ_two]
  rw [heq]
  exact hψ0_cd.add ((contDiff_const.mul (hfro_cd 0)).add (contDiff_const.mul (hfro_cd 1)))

/-- Smoothness of `p.datum α` on `{0}ᶜ` when `p.ν ≤ 1` and `2 ≤ p.R`. -/
theorem contDiffOn_datum {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {dm dp : ℝ} {p : Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hR2 : 2 ≤ p.R) (hmode : p.mode = q)
    (α : Fin 2 → ℝ) : ContDiffOn ℝ ∞ (p.datum α) {0}ᶜ := by
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity [p.ν_pos])]
    nlinarith [p.ν_pos]
  have hc0 : 0 < p.c := lt_of_lt_of_le one_pos hc1
  have hraw : ContDiffOn ℝ ∞ (inletRaw p.c p.R) {0}ᶜ := contDiffOn_inletRaw hc0 hR2
  have hfro0 : ContDiffOn ℝ ∞
      (Axi.Nv p.R (fun m => datumProfile p.ε (p.frozenStream 0) m.2) 0) {0}ᶜ :=
    contDiffOn_frozenDatum hq hreg hν1 hmode 0
  have hfro1 : ContDiffOn ℝ ∞
      (Axi.Nv p.R (fun m => datumProfile p.ε (p.frozenStream 1) m.2) 0) {0}ᶜ :=
    contDiffOn_frozenDatum hq hreg hν1 hmode 1
  have heq : p.datum α = fun y => inletRaw p.c p.R y +
      (α 0 • Axi.Nv p.R (fun m => datumProfile p.ε (p.frozenStream 0) m.2) 0 y +
        α 1 • Axi.Nv p.R (fun m => datumProfile p.ε (p.frozenStream 1) m.2) 0 y) := by
    funext y
    rw [datum_eq_inletRaw_add_frozen hq hc1 hmode α y, Fin.sum_univ_two]
  rw [heq]
  exact hraw.add ((hfro0.const_smul (α 0)).add (hfro1.const_smul (α 1)))

/-- `Axi.ringStream R 0 (fun n => ψ n.2)` is `C²` on `Ioi 0 ×ˢ univ` for any `C^∞` stream `ψ`. -/
theorem contDiffOn_ringStream_datum {R : ℝ} (hR : 0 < R) {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiffOn ℝ 2 (Axi.ringStream R 0 (fun n : E3 => ψ n.2)) (Ioi 0 ×ˢ univ) := by
  have hmer : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (Axi.merChart R 0 q).2) (Ioi 0 ×ˢ univ) := by
    unfold Axi.merChart
    have hne : ∀ q ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), R ^ 2 / q.1 ^ 2 ≠ 0 := by
      intro q hq
      exact div_ne_zero (pow_ne_zero 2 hR.ne') (pow_ne_zero 2 (ne_of_gt hq.1))
    have hs : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => R ^ 2 / q.1 ^ 2) (Ioi 0 ×ˢ univ) :=
      contDiffOn_const.div (contDiffOn_fst.pow 2) fun q hq => pow_ne_zero 2 (ne_of_gt hq.1)
    have hq1 : ContDiffOn ℝ ∞
        (fun q : ℝ × ℝ => R * 0 / 2 - (R / 2) * Real.log (R ^ 2 / q.1 ^ 2)) (Ioi 0 ×ˢ univ) :=
      contDiffOn_const.sub (contDiffOn_const.mul (hs.log hne))
    have hq2 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => R * q.2 / q.1) (Ioi 0 ×ˢ univ) :=
      (contDiffOn_const.mul contDiffOn_snd).div contDiffOn_fst fun q hq => ne_of_gt hq.1
    exact hq1.prodMk hq2
  have hcomp : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => ψ (Axi.merChart R 0 q).2) (Ioi 0 ×ˢ univ) :=
    hψ.comp_contDiffOn hmer
  exact (contDiffOn_fst.mul hcomp).of_le (by simp)

/-- Pointwise zero divergence of `p.datum α` on `{0}ᶜ`. -/
theorem divergence_datum_eq_zero {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {dm dp : ℝ} {p : Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hR2 : 2 ≤ p.R) (hmode : p.mode = q)
    (α : Fin 2 → ℝ) {x : Space} (hx : x ≠ 0) :
    Axi.divergence (p.datum α) x = 0 := by
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity [p.ν_pos])]
    nlinarith [p.ν_pos]
  have hψ : ContDiff ℝ ∞ (p.datumStream α) := contDiff_datumStream hq hc1 hmode α
  have hoff : ∀ y : Space, y ∉ Axi.axis → Axi.divergence (p.datum α) y = 0 := by
    intro y hy
    have hev : p.datum α =ᶠ[𝓝 y] Axi.streamLift (Axi.ringStream p.R 0 (fun n : E3 => p.datumStream α n.2)) := by
      filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
      unfold Params.datum
      have hRinv : p.ε = p.R⁻¹ := (inv_inv p.ε).symm
      rw [hRinv]
      exact Nv_datumProfile_eq_streamLift p.R_pos hψ hz
    have hdiv : Axi.divergence (p.datum α) y =
        Axi.divergence (Axi.streamLift (Axi.ringStream p.R 0 (fun n : E3 => p.datumStream α n.2))) y := by
      unfold Axi.divergence
      rw [hev.fderiv_eq]
    rw [hdiv]
    exact Axi.div_streamLift_eq_zero (contDiffOn_ringStream_datum p.R_pos hψ) hy
  by_cases hxa : x ∈ Axi.axis
  · have ha : ContDiffOn ℝ 1 (p.datum α) {y : Space | y ≠ 0} :=
      (contDiffOn_datum hq hreg hν1 hR2 hmode α).of_le (by simp)
    have hU : IsOpen {y : Space | y ≠ 0} := isOpen_ne
    have hfdc : ContinuousAt (fderiv ℝ (p.datum α)) x :=
      (ha.continuousOn_fderiv_of_isOpen hU le_rfl).continuousAt (hU.mem_nhds hx)
    have hcomp : ∀ i : Fin 3,
        ContinuousAt (fun y => fderiv ℝ (p.datum α) y (UnforcedLeray.coordinateVector i) i) x := by
      intro i
      exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).continuousAt.comp
        (hfdc.clm_apply continuousAt_const)
    have hDc : ContinuousAt (Axi.divergence (p.datum α)) x := by
      unfold Axi.divergence
      simp only [Fin.sum_univ_three]
      exact ((hcomp 0).add (hcomp 1)).add (hcomp 2)
    have hx0 : x 0 = 0 := hxa.1
    have hline : ∀ t : ℝ, t ≠ 0 →
        Axi.divergence (p.datum α) (x + t • UnforcedLeray.coordinateVector (0 : Fin 3)) = 0 := by
      intro t ht
      apply hoff
      intro hmem
      have h0 : (x + t • UnforcedLeray.coordinateVector (0 : Fin 3)) 0 = 0 := hmem.1
      simp [Axi.coordinateVector_apply, hx0] at h0
      exact ht h0
    have hγ : Continuous (fun t : ℝ => x + t • UnforcedLeray.coordinateVector (0 : Fin 3)) := by
      fun_prop
    have hD' : ContinuousAt (Axi.divergence (p.datum α))
        (x + (0 : ℝ) • UnforcedLeray.coordinateVector (0 : Fin 3)) := by simpa using hDc
    have hcont : ContinuousAt
        (fun t : ℝ => Axi.divergence (p.datum α) (x + t • UnforcedLeray.coordinateVector (0 : Fin 3))) 0 :=
      ContinuousAt.comp (f := fun t : ℝ => x + t • UnforcedLeray.coordinateVector (0 : Fin 3))
        (x := (0 : ℝ)) hD' hγ.continuousAt
    have hlim1 : Tendsto
        (fun t : ℝ => Axi.divergence (p.datum α) (x + t • UnforcedLeray.coordinateVector (0 : Fin 3)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (Axi.divergence (p.datum α) x)) := by
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim0 : Tendsto
        (fun t : ℝ => Axi.divergence (p.datum α) (x + t • UnforcedLeray.coordinateVector (0 : Fin 3)))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hline t ht).symm
    exact tendsto_nhds_unique hlim1 hlim0
  · exact hoff x hxa

/-- Inverse-distance derivative bounds for `p.datum α` from `homogDerivBound_proof` and `datum_dss`. -/
theorem bounds_datum {lam : ℂ} {q : Planar.Profile}
    (hq : Planar.IsGrowingEigenpair lam q) {dm dp : ℝ} {p : Params} {d : ℝ}
    (hreg : BgRegime p d dm dp) (hν1 : p.ν ≤ 1) (hR2 : 2 ≤ p.R) (hmode : p.mode = q)
    (α : Fin 2 → ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k (p.datum α) x‖ * ‖x‖ ^ (k + 1) ≤ C := by
  have hl : 1 < Real.exp (p.period / 2) := by
    have hp : 0 < p.period / 2 := half_pos p.period_pos
    simpa using Real.exp_strictMono hp
  have ha : ContDiffOn ℝ ∞ (p.datum α) {x : Space | x ≠ 0} :=
    contDiffOn_datum hq hreg hν1 hR2 hmode α
  have hdss : ∀ x : Space, x ≠ 0 →
      p.datum α (Real.exp (p.period / 2) • x) = (Real.exp (p.period / 2))⁻¹ • p.datum α x := by
    intro x _
    rw [← Real.exp_neg]
    exact p.datum_dss α x
  obtain ⟨C, hC⟩ := homogDerivBound_proof (Real.exp (p.period / 2)) hl (p.datum α) ha hdss k
  refine ⟨C, fun x hx => ?_⟩
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hpow : 0 < ‖x‖ ^ (k + 1) := pow_pos hpos (k + 1)
  have hrpow : ‖x‖ ^ (-(1 + (k : ℝ))) = (‖x‖ ^ (k + 1))⁻¹ := by
    rw [Real.rpow_neg hpos.le, show (1 + (k : ℝ)) = ((k + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  have hk := hC x hx
  rw [hrpow] at hk
  exact (le_mul_inv_iff₀ hpow).1 hk

/-- Weak-`L³` bound from `‖a x‖ * ‖x‖ ≤ C` off the origin. -/
theorem weakL3_of_inv_norm_bound {a : Space → Space} {C : ℝ}
    (hC : ∀ x : Space, x ≠ 0 → ‖a x‖ * ‖x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      volume {x : Space | t ≤ ‖a x‖} ≤ ENNReal.ofReal (K * t⁻¹ ^ 3) := by
  set M : ℝ := max C 0 + 1 with hM
  have hM0 : 0 < M := by positivity
  refine ⟨Real.pi * 4 / 3 * M ^ 3, by positivity, fun t ht => ?_⟩
  have hsub : {x : Space | t ≤ ‖a x‖} \ {(0 : Space)} ⊆ Metric.ball (0 : Space) (M * t⁻¹) := by
    intro x hx
    obtain ⟨hxt, hx0⟩ := hx
    have hx_ne : x ≠ 0 := hx0
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx_ne
    have h1 : t * ‖x‖ ≤ ‖a x‖ * ‖x‖ := mul_le_mul_of_nonneg_right hxt hnx.le
    have h2 : ‖a x‖ * ‖x‖ ≤ max C 0 := (hC x hx_ne).trans (le_max_left C 0)
    have h3 : t * ‖x‖ < M := by linarith
    have h4 : ‖x‖ < M * t⁻¹ := by
      have := (lt_div_iff₀' ht).2 h3
      rwa [div_eq_mul_inv] at this
    simpa [Metric.mem_ball, dist_zero_right] using h4
  have hvol1 : volume {x : Space | t ≤ ‖a x‖} =
      volume ({x : Space | t ≤ ‖a x‖} \ {(0 : Space)}) :=
    (measure_sdiff_null (measure_singleton (0 : Space))).symm
  rw [hvol1]
  refine (measure_mono hsub).trans ?_
  rw [EuclideanSpace.volume_ball_fin_three]
  have hrt : 0 ≤ M * t⁻¹ := by positivity
  rw [← ENNReal.ofReal_pow hrt 3, ← ENNReal.ofReal_mul (pow_nonneg hrt 3)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

/-- Local `L²` membership on every ball from continuity off `0` and `‖a x‖ * ‖x‖ ≤ C`. -/
theorem memLp_two_loc_of_inv_norm_bound {a : Space → Space} (hcont : ContinuousOn a {0}ᶜ)
    {C : ℝ} (hC : ∀ x : Space, x ≠ 0 → ‖a x‖ * ‖x‖ ≤ C) (r : ℝ) :
    MemLp a 2 (volume.restrict (Metric.ball 0 r)) := by
  by_cases hr : r ≤ 0
  · rw [Metric.ball_eq_empty.2 hr, Measure.restrict_empty]
    simp [MemLp, aestronglyMeasurable_zero_measure, eLpNorm_measure_zero]
  · push Not at hr
    have hmeas : AEStronglyMeasurable a volume :=
      UnforcedLeray.L09.aestronglyMeasurable_of_continuousOn_compl_zero hcont
    rw [memLp_two_iff_integrable_sq_norm hmeas.restrict]
    have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
    have hdec : ∀ᵐ x ∂(volume : Measure Space), ‖‖a x‖ ^ 2‖ ≤ (max C 0) ^ 2 * ‖x‖ ^ (-(2 : ℝ)) := by
      filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Space))] with x hx
      have hx0 : x ≠ 0 := hx
      have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have h1 : ‖a x‖ * ‖x‖ ≤ max C 0 := (hC x hx0).trans (le_max_left C 0)
      have h0 : 0 ≤ ‖a x‖ * ‖x‖ := by positivity
      rw [Real.norm_of_nonneg (sq_nonneg _), Real.rpow_neg hpos.le, Real.rpow_two,
        ← div_eq_mul_inv, le_div_iff₀ (pow_pos hpos 2)]
      calc ‖a x‖ ^ 2 * ‖x‖ ^ 2 = (‖a x‖ * ‖x‖) ^ 2 := by ring
        _ ≤ (max C 0) ^ 2 := pow_le_pow_left₀ h0 h1 2
    exact integrableOn_ball_of_norm_le_rpow (by rw [hdim]; norm_num) (by rw [hdim]; norm_num)
      (ae_restrict_of_ae hdec) (hmeas.norm.pow 2)

end UnforcedLeray.Short.IIb.DatumFactsAux
