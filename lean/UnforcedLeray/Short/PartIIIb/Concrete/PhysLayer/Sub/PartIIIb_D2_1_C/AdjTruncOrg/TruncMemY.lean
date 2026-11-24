import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg

/-!
# Helper bounds for `truncMemY` (`TruncMemY`, source 1334-1337, 1470-1480)

Pointwise and `Y_2`-norm estimates used to show `Φₙ, gₙ ∈ Y_2`:
* `crossC_norm_le`: `‖a × b‖ ≤ 6 ‖a‖ ‖b‖`;
* `gradC_le_inv`: from `CutBounds`, `‖∇a(y)‖ ≤ 2 C ‖y‖⁻¹` for a cutoff-type `a`;
* `phaseLpNorm_lt_top_of_enorm_le`: a pointwise bound `‖f‖ₑ ≤ K ‖g‖ₑ` with `g ∈ Y_2` gives `f ∈ Y_2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Euclidean norm of a `ℂ³` vector is at most the sum of the moduli of its entries. -/
theorem norm_le_sum_three_entries (x : CVec3) : ‖x‖ ≤ ‖x 0‖ + ‖x 1‖ + ‖x 2‖ := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg (norm_nonneg (x 0)) (norm_nonneg (x 1)),
    mul_nonneg (norm_nonneg (x 0)) (norm_nonneg (x 2)),
    mul_nonneg (norm_nonneg (x 1)) (norm_nonneg (x 2))]

/-- Crude bound `‖a × b‖ ≤ 6 ‖a‖ ‖b‖` for the cross product of `ℂ³` vectors. -/
theorem crossC_norm_le (a b : CVec3) : ‖crossC a b‖ ≤ 6 * ‖a‖ * ‖b‖ := by
  have ha : ∀ i, ‖a i‖ ≤ ‖a‖ := fun i => PiLp.norm_apply_le a i
  have hb : ∀ i, ‖b i‖ ≤ ‖b‖ := fun i => PiLp.norm_apply_le b i
  have hc : ∀ i j, ‖a i * b j‖ ≤ ‖a‖ * ‖b‖ := fun i j => by
    rw [norm_mul]; exact mul_le_mul (ha i) (hb j) (norm_nonneg _) (norm_nonneg _)
  have e0 : ‖(crossC a b) 0‖ ≤ 2 * (‖a‖ * ‖b‖) := by
    have : (crossC a b) 0 = a 1 * b 2 - a 2 * b 1 := by simp [crossC]
    rw [this]; linarith [norm_sub_le (a 1 * b 2) (a 2 * b 1), hc 1 2, hc 2 1]
  have e1 : ‖(crossC a b) 1‖ ≤ 2 * (‖a‖ * ‖b‖) := by
    have : (crossC a b) 1 = a 2 * b 0 - a 0 * b 2 := by simp [crossC]
    rw [this]; linarith [norm_sub_le (a 2 * b 0) (a 0 * b 2), hc 2 0, hc 0 2]
  have e2 : ‖(crossC a b) 2‖ ≤ 2 * (‖a‖ * ‖b‖) := by
    have : (crossC a b) 2 = a 0 * b 1 - a 1 * b 0 := by simp [crossC]
    rw [this]; linarith [norm_sub_le (a 0 * b 1) (a 1 * b 0), hc 0 1, hc 1 0]
  refine (norm_le_sum_three_entries _).trans ?_
  linarith


/-- Real-to-enorm comparison for vectors. -/
theorem enorm_le_ofReal_mul_of_norm_le {f g : CVec3} {K : ℝ} (hK : 0 ≤ K)
    (h : ‖f‖ ≤ K * ‖g‖) : ‖f‖ₑ ≤ ENNReal.ofReal K * ‖g‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hK]
  exact ENNReal.ofReal_le_ofReal h

/-- Hardy-type pointwise bound for the cross product. -/
theorem crossC_norm_le_hardy (a v : CVec3) (y : Space) {M : ℝ} (ha : ‖a‖ ≤ M * ‖y‖⁻¹) :
    ‖crossC a v‖ ≤ (6 * M) * ‖(‖y‖⁻¹ : ℝ) • v‖ := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg y))]
  calc ‖crossC a v‖ ≤ 6 * ‖a‖ * ‖v‖ := crossC_norm_le a v
    _ ≤ 6 * (M * ‖y‖⁻¹) * ‖v‖ := by gcongr
    _ = 6 * M * (‖y‖⁻¹ * ‖v‖) := by ring

/-- Bounded-coefficient pointwise bound for the cross product. -/
theorem crossC_norm_le_const (a v : CVec3) {M : ℝ} (ha : ‖a‖ ≤ M) :
    ‖crossC a v‖ ≤ (6 * M) * ‖v‖ := by
  calc ‖crossC a v‖ ≤ 6 * ‖a‖ * ‖v‖ := crossC_norm_le a v
    _ ≤ 6 * M * ‖v‖ := by gcongr

/-- Off the annulus `n+1 ≤ |y| ≤ 2(n+1)` the gradient vanishes; on it `C/(n+1) ≤ 2C/|y|`. -/
theorem gradC_le_inv {C : ℝ} (hC : 0 ≤ C) (n : ℕ) (a : Space → ℝ) (y : Space)
    (h0 : (‖y‖ < (n : ℝ) + 1 ∨ 2 * ((n : ℝ) + 1) < ‖y‖) → gradC a y = 0)
    (hb : ‖gradC a y‖ ≤ C / ((n : ℝ) + 1)) : ‖gradC a y‖ ≤ 2 * C * ‖y‖⁻¹ := by
  by_cases hout : ‖y‖ < (n : ℝ) + 1 ∨ 2 * ((n : ℝ) + 1) < ‖y‖
  · rw [h0 hout, norm_zero]; positivity
  · simp only [not_or, not_lt] at hout
    obtain ⟨h1, h2⟩ := hout
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hy : 0 < ‖y‖ := lt_of_lt_of_le hn h1
    have key : (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) * ‖y‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hy]; linarith
    have hm := mul_le_mul_of_nonneg_left key (show (0 : ℝ) ≤ 2 * C by linarith)
    calc ‖gradC a y‖ ≤ C / ((n : ℝ) + 1) := hb
      _ ≤ 2 * C * ‖y‖⁻¹ := by
        rw [div_le_iff₀ hn]
        nlinarith [hm]

/-- A pointwise bound `‖f‖ₑ ≤ K ‖g‖ₑ` with `K < ∞` and `‖g‖_{Y_2} < ∞` gives `‖f‖_{Y_2} < ∞`. -/
theorem phaseLpNorm_lt_top_of_enorm_le {P : ℝ} (hP : 0 < P) {f g : ℝ × Space → CVec3}
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume)
    (hgfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 g < ⊤)
    (hle : ∀ x, ‖f x‖ₑ ≤ K * ‖g x‖ₑ) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 f < ⊤ := by
  have hI := lint_lt_top_of_phaseLpNorm hP hg hgfin
  have hJle : ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P)
      ≤ K ^ (2 : ℝ) * ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ) ∂(muP P) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK)]
    refine lintegral_mono fun z => ?_
    calc ‖f z‖ₑ ^ (2 : ℝ) ≤ (K * ‖g z‖ₑ) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (hle z) (by norm_num)
      _ = K ^ (2 : ℝ) * ‖g z‖ₑ ^ (2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have hJfin : ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂(muP P) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK) hI.ne) hJle
  rw [phaseLpNorm_eq P f hf]
  exact lt_top_iff_ne_top.2
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJfin))


/-- Smooth coefficient `Φ ↦ sd k a` and the Euclidean operations: continuity and smoothness. -/
theorem contDiff_sd {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) (j : Fin 3) :
    ContDiff ℝ ∞ (sd j a) := by
  unfold sd
  exact (ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_radS' {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (radS a) := by
  unfold radS
  exact ContDiff.sum fun j _ => ((EuclideanSpace.proj j).contDiff.mul (contDiff_sd ha j))

theorem contDiff_lapS' {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (lapS a) := by
  unfold lapS
  exact ContDiff.sum fun j _ => contDiff_sd (contDiff_sd ha j) j

theorem continuous_crossC : Continuous (fun p : CVec3 × CVec3 => crossC p.1 p.2) := by
  unfold crossC
  fun_prop

theorem continuous_gradC' {a : Space → ℝ} (ha : ∀ j : Fin 3, Continuous (sd j a)) :
    Continuous (gradC a) := by
  unfold gradC
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => Complex.continuous_ofReal.comp (ha j))

set_option maxHeartbeats 1000000 in
/-- Measurability of `x ↦ a × g x` with `a` continuous in `y`. -/
theorem aesm_crossC {A : Space → CVec3} (hA : Continuous A) {g : ℝ × Space → CVec3}
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (fun x : ℝ × Space => crossC (A x.2) (g x)) volume := by
  have h1 : AEStronglyMeasurable (fun x : ℝ × Space => (A x.2, g x)) volume :=
    (hA.comp continuous_snd).aestronglyMeasurable.prodMk hg
  exact (continuous_crossC.comp_aestronglyMeasurable h1 : _)

/-- Sum of two `Y_2` fields is `Y_2` (periodicity, measurability, finiteness). -/
theorem isInYr_add2 {P : ℝ} (hP : 0 < P) {F u v : ℝ × Space → CVec3}
    (hF : ∀ x, F x = u x + v x)
    (hu : UnforcedLeray.Short.IIb.IsInYr P 2 u) (hv : UnforcedLeray.Short.IIb.IsInYr P 2 v) :
    UnforcedLeray.Short.IIb.IsInYr P 2 F := by
  have hFe : F = fun x => u x + v x := funext hF
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hu.periodic, hv.periodic] with x h1 h2
    rw [hF, hF]
    simp only [h1, h2]
  · rw [hFe]; exact hu.meas.add hv.meas
  · rw [hFe]
    refine lt_of_le_of_lt (phaseLpNorm_add_le P hP u v hu.meas hv.meas) ?_
    exact ENNReal.add_lt_top.2 ⟨hu.finite, hv.finite⟩

/-- `a x • g x` with bounded periodic scalar `a` and `g ∈ Y_2`. -/
theorem isInYr_smul_of_bdd {P : ℝ} (hP : 0 < P) {a : ℝ × Space → ℝ} {g : ℝ × Space → CVec3}
    {M : ℝ} (ha_meas : AEStronglyMeasurable a volume) (hM : ∀ x, |a x| ≤ M)
    (hpa : ∀ᵐ x : ℝ × Space, a (x.1 + P, x.2) = a x)
    (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => a x • g x) := by
  have hfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => a x • g x) < ⊤ :=
    phaseLpNorm_lt_top_of_enorm_le hP (K := ENNReal.ofReal M) ENNReal.ofReal_ne_top
      (ha_meas.smul hg.meas) hg.meas hg.finite (fun x => by
        show ‖a x • g x‖ₑ ≤ _
        rw [enorm_smul]
        have hA : ‖a x‖ₑ ≤ ENNReal.ofReal M := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hM x)
        gcongr)
  refine ⟨?_, ha_meas.smul hg.meas, hfin⟩
  filter_upwards [hpa, hg.periodic] with x h1 h2
  simp only [h1, h2]

/-- A cross product with a coefficient bounded by `M ‖y‖⁻¹` (Hardy type) and `g/|y| ∈ Y_2`. -/
theorem isInYr_cross_hardy {P : ℝ} (hP : 0 < P) {A : Space → CVec3} {g : ℝ × Space → CVec3}
    {M : ℝ} (hM0 : 0 ≤ M) (hA : ∀ y : Space, ‖A y‖ ≤ M * ‖y‖⁻¹) (hcA : Continuous A)
    (hgper : ∀ᵐ x : ℝ × Space, g (x.1 + P, x.2) = g x)
    (hgm : AEStronglyMeasurable g volume)
    (hH : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • g x)) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => crossC (A x.2) (g x)) := by
  have hfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => crossC (A x.2) (g x)) < ⊤ :=
    phaseLpNorm_lt_top_of_enorm_le hP (K := ENNReal.ofReal (6 * M)) ENNReal.ofReal_ne_top
      (aesm_crossC hcA hgm) hH.meas hH.finite (fun x => by
        have h := crossC_norm_le_hardy (A x.2) (g x) x.2 (hA x.2)
        exact enorm_le_ofReal_mul_of_norm_le (by linarith) (by linarith [h]))
  refine ⟨?_, aesm_crossC hcA hgm, hfin⟩
  filter_upwards [hgper] with x hx
  simp only [hx]

/-- A cross product with a bounded coefficient and `g ∈ Y_2`. -/
theorem isInYr_cross_bdd {P : ℝ} (hP : 0 < P) {A : Space → CVec3} {g : ℝ × Space → CVec3}
    {M : ℝ} (hM0 : 0 ≤ M) (hA : ∀ y : Space, ‖A y‖ ≤ M) (hcA : Continuous A)
    (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => crossC (A x.2) (g x)) := by
  have hfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => crossC (A x.2) (g x)) < ⊤ :=
    phaseLpNorm_lt_top_of_enorm_le hP (K := ENNReal.ofReal (6 * M)) ENNReal.ofReal_ne_top
      (aesm_crossC hcA hg.meas) hg.meas hg.finite (fun x => by
        exact enorm_le_ofReal_mul_of_norm_le (by linarith) (crossC_norm_le_const (A x.2) (g x) (hA x.2)))
  refine ⟨?_, aesm_crossC hcA hg.meas, hfin⟩
  filter_upwards [hg.periodic] with x hx
  simp only [hx]

/-- **TruncMemY** (source 1334-1337, 1470-1480): `Φₙ` and `gₙ` lie in `Y_2`. -/
theorem truncMemY : TruncMemY := by
  intro hCut P ν μ hP hP1 hν hμ D hD n
  unfold CutBounds at hCut
  obtain ⟨C, hC0, hb⟩ := hCut
  have hG1 : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).1) (hb n y).2.1
  have hG2 : ∀ y : Space, ‖gradC (radS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.1) (hb n y).2.2.1
  have hG3 : ∀ y : Space, ‖gradC (lapS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.2.1) (hb n y).2.2.2.1
  have hR : ∀ y : Space, |radS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.1
  have hL : ∀ y : Space, |lapS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.2.1
  have hKa : ∀ (k : Fin 3) (y : Space), |sd k (cutχ n) y| ≤ C :=
    fun k y => ((hb n y).2.2.2.2.2.2 k).1
  have hKg : ∀ (k : Fin 3) (y : Space), ‖gradC (sd k (cutχ n)) y‖ ≤ C :=
    fun k y => ((hb n y).2.2.2.2.2.2 k).2
  have hcb : ∀ y : Space, |cutχ n y| ≤ 1 := fun y => by
    have h0 : (0 : ℝ) ≤ unitBump (cutC n • y) := unitBump.nonneg
    have h1 : unitBump (cutC n • y) ≤ 1 := unitBump.le_one
    unfold cutχ
    exact abs_le.2 ⟨by linarith, h1⟩
  have hcutC : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  have hradC : ContDiff ℝ ∞ (radS (cutχ n)) := contDiff_radS' hcutC
  have hlapC : ContDiff ℝ ∞ (lapS (cutχ n)) := contDiff_lapS' hcutC
  have hcont_cut : Continuous (cutχ n) := hcutC.continuous
  have hcont_rad : Continuous (radS (cutχ n)) := hradC.continuous
  have hcont_lap : Continuous (lapS (cutχ n)) := hlapC.continuous
  have hcont_gC : Continuous (gradC (cutχ n)) :=
    continuous_gradC' fun j => (contDiff_sd hcutC j).continuous
  have hcont_gR : Continuous (gradC (radS (cutχ n))) :=
    continuous_gradC' fun j => (contDiff_sd hradC j).continuous
  have hcont_gL : Continuous (gradC (lapS (cutχ n))) :=
    continuous_gradC' fun j => (contDiff_sd hlapC j).continuous
  have hcont_gK : ∀ k : Fin 3, Continuous (gradC (sd k (cutχ n))) := fun k =>
    continuous_gradC' fun j => (contDiff_sd (contDiff_sd hcutC k) j).continuous
  have hcont_K : ∀ k : Fin 3, Continuous (sd k (cutχ n)) := fun k =>
    (contDiff_sd hcutC k).continuous
  -- the Y_2 inputs
  have hΦ := hD.dom.mem
  have hgY := hD.dom.mem_g
  have hψH := hD.spΦ.hardy
  have hwH := hD.spg.hardy
  have hDΦ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ k) := fun k => (hD.dΦ k).1
  have hDψ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.Dψ k) :=
    fun k => (hD.spΦ.grad k).1
  have hcut_const : ∀ y : Space, ‖(cutχ n y)‖ ≤ 1 := fun y => by simpa [Real.norm_eq_abs] using hcb y
  -- truncPhi
  have hU1 : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • D.Φ x) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun x : ℝ × Space => cutχ n x.2)
      ((hcont_cut.comp continuous_snd).aestronglyMeasurable) (fun x => hcb x.2)
      (Filter.Eventually.of_forall fun x => rfl) hΦ
  have hV1 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.ψ x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spΦ.periodic hD.spΦ.meas hψH
  have hPhi : UnforcedLeray.Short.IIb.IsInYr P 2 (truncPhi n D) :=
    isInYr_add2 hP (F := truncPhi n D) (fun x => rfl) hU1 hV1
  -- EHardy
  have hEH1 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x)) :=
    isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC hD.spg.periodic hD.spg.meas hwH
  have hEH2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)) :=
    isInYr_smul_of_bdd hP (M := 1 / 2) (a := fun _ : ℝ × Space => (1 / 2 : ℝ)) aestronglyMeasurable_const
      (fun x => by norm_num) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG2 hcont_gR hD.spΦ.periodic hD.spΦ.meas hψH)
  have hEH3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-ν) • crossC (gradC (lapS (cutχ n)) x.2) (D.ψ x)) :=
    isInYr_smul_of_bdd hP (M := |ν|) (a := fun _ : ℝ × Space => (-ν)) aestronglyMeasurable_const
      (fun x => by simp) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG3 hcont_gL hD.spΦ.periodic hD.spΦ.meas hψH)
  have hEH12 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (cutχ n) x.2) (D.w x)
        + (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) x.2) (D.ψ x)) :=
    isInYr_add2 hP (fun x => rfl) hEH1 hEH2
  have hEH : UnforcedLeray.Short.IIb.IsInYr P 2 (EHardy n ν D) :=
    isInYr_add2 hP (F := EHardy n ν D) (fun x => by
      simp only [EHardy, sub_eq_add_neg, neg_smul]) hEH12 hEH3
  -- EBdd
  have hc1 : ∀ y : Space, |(1 / 2 : ℝ) * radS (cutχ n) y - ν * lapS (cutχ n) y|
      ≤ (1 / 2 + |ν|) * C := fun y => by
    have h1 := hR y
    have h2 := hL y
    calc |(1 / 2 : ℝ) * radS (cutχ n) y - ν * lapS (cutχ n) y|
        ≤ |(1 / 2 : ℝ) * radS (cutχ n) y| + |ν * lapS (cutχ n) y| := abs_sub _ _
      _ = (1 / 2) * |radS (cutχ n) y| + |ν| * |lapS (cutχ n) y| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ (1 / 2) * C + |ν| * C := by gcongr
      _ = (1 / 2 + |ν|) * C := by ring
  have hE1 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => ((1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2) • D.Φ x) :=
    isInYr_smul_of_bdd hP (M := (1 / 2 + |ν|) * C) (a := fun x : ℝ × Space => (1 / 2 : ℝ) * radS (cutχ n) x.2 - ν * lapS (cutχ n) x.2)
      ((((continuous_const.mul (hcont_rad.comp continuous_snd)).sub
        (continuous_const.mul (hcont_lap.comp continuous_snd)))).aestronglyMeasurable)
      (fun x => hc1 x.2) (Filter.Eventually.of_forall fun x => rfl) hΦ
  have hS2k : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => sd k (cutχ n) x.2 • D.DΦ k x) := fun k =>
    isInYr_smul_of_bdd hP (M := C) (a := fun x : ℝ × Space => sd k (cutχ n) x.2)
      ((hcont_K k).comp continuous_snd).aestronglyMeasurable (fun x => hKa k x.2)
      (Filter.Eventually.of_forall fun x => rfl) (hDΦ k)
  have hS2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) := by
    have e : (fun x : ℝ × Space => ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x)
        = fun x => (sd 0 (cutχ n) x.2 • D.DΦ 0 x + sd 1 (cutχ n) x.2 • D.DΦ 1 x)
          + sd 2 (cutχ n) x.2 • D.DΦ 2 x := by
      funext x; rw [Fin.sum_univ_three]
    rw [e]
    exact isInYr_add2 hP (fun x => rfl)
      (isInYr_add2 hP (fun x => rfl) (hS2k 0) (hS2k 1)) (hS2k 2)
  have hS3k : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) := fun k =>
    isInYr_cross_bdd hP (M := C) (by linarith) (fun y => hKg k y) (hcont_gK k) (hDψ k)
  have hS3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) := by
    have e : (fun x : ℝ × Space => ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x))
        = fun x => (crossC (gradC (sd 0 (cutχ n)) x.2) (D.Dψ 0 x)
          + crossC (gradC (sd 1 (cutχ n)) x.2) (D.Dψ 1 x))
          + crossC (gradC (sd 2 (cutχ n)) x.2) (D.Dψ 2 x) := by
      funext x; rw [Fin.sum_univ_three]
    rw [e]
    exact isInYr_add2 hP (fun x => rfl)
      (isInYr_add2 hP (fun x => rfl) (hS3k 0) (hS3k 1)) (hS3k 2)
  have hE2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-(2 * ν)) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x) :=
    isInYr_smul_of_bdd hP (M := |2 * ν|) (a := fun _ : ℝ × Space => -(2 * ν)) aestronglyMeasurable_const
      (fun x => by simp) (Filter.Eventually.of_forall fun x => rfl) hS2
  have hE3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-(2 * ν)) • ∑ k : Fin 3, crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) :=
    isInYr_smul_of_bdd hP (M := |2 * ν|) (a := fun _ : ℝ × Space => -(2 * ν)) aestronglyMeasurable_const
      (fun x => by simp) (Filter.Eventually.of_forall fun x => rfl) hS3
  have hEB : UnforcedLeray.Short.IIb.IsInYr P 2 (EBdd n ν D) :=
    isInYr_add2 hP (F := EBdd n ν D) (fun x => by
      simp only [EBdd, sub_eq_add_neg, neg_smul, smul_add]) (isInYr_add2 hP (fun x => rfl) hE1 hE2) hE3
  -- truncG
  have hG1' : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => cutχ n x.2 • D.g x) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun x : ℝ × Space => cutχ n x.2)
      ((hcont_cut.comp continuous_snd).aestronglyMeasurable) (fun x => hcb x.2)
      (Filter.Eventually.of_forall fun x => rfl) hgY
  have hGG : UnforcedLeray.Short.IIb.IsInYr P 2 (truncG n ν D) :=
    isInYr_add2 hP (F := truncG n ν D)
      (fun x => rfl) (isInYr_add2 hP (fun x => rfl) hG1' hEH) hEB
  exact ⟨hPhi, hGG⟩

end UnforcedLeray.Short.PartIIIb.Concrete
