import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_2_KerPDE.E

/-!
# Decomposition of `KdOpSplit` (`PartIII-b:C/rep/2/6/3/5`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200, 5223.  The integrability of the six `Kd`-integrands is
reduced to joint integrability of the `Gker` integrand (`GkerIntegrable`), of its `y`-gradient
and `y`-Hessian-diagonal integrands (leaves `GkerYGradInt`, `GkerLapInt`), and the `h`-derivative
identity `GkerHasDerivH`: `Kd = G_μ - G_{μ+1}`, and for `h > 0`
`∂_h G_m = L G_m - (m - ½) G_m` with `L G = ½ y·∇G + νΣ∂_l²G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The measure `(vol|_{Ioi 0}) ⊗ vol` on `(h,z)`. -/
def sepMeas : Measure (ℝ × Space) := (volume.restrict (Ioi (0 : ℝ))).prod volume

/-- The integrand of `kerInt` (same as `kerIntegrand` in `S5.lean`). -/
def kerIntegrandS (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (p : ℝ × Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3, Φ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)

/-- Leaf: joint integrability of the `y·∇_y G_m` integrand (source 3603-3626, 3631-3646: kernel
bound `|D² ∇K_t(x)| ≤ C|x|^{-6}` of `SepKernelBounds`, `|y - e^{-h/2}z| ≥ ϱ y - rOut` on the
support of `T`, `SepMoment`). -/
def GkerYGradInt : Prop :=
  ∀ (ν : ℝ) (m : ℂ), 0 < ν → -(1 / 4) < m.re → ∀ (rOut P : ℝ), 0 ≤ rOut → 0 < P →
    ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
        Integrable (kerIntegrandS T
          (fun h y' z i j k => fderiv ℝ (fun y'' => Gker ν m h y'' z i j k) y' y') τ y i) sepMeas

/-- Leaf: joint integrability of the `∂_l∂_l G_m` integrand (as `GkerYGradInt`, two derivatives). -/
def GkerLapInt : Prop :=
  ∀ (ν : ℝ) (m : ℂ), 0 < ν → -(1 / 4) < m.re → ∀ (rOut P : ℝ), 0 ≤ rOut → 0 < P →
    ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ (i : Fin 3) (l : Fin 3),
        Integrable (kerIntegrandS T
          (fun h y' z i j k => fderiv ℝ (fun y'' => fderiv ℝ (fun y''' => Gker ν m h y''' z i j k) y''
            (UnforcedLeray.coordinateVector l)) y' (UnforcedLeray.coordinateVector l)) τ y i) sepMeas

/-- The six integrands of `KdOpSplit` are integrable. -/
def KdIntegrandsS : Prop :=
  ∀ (ν μ rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), SepData ν μ rOut P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
      Integrable (kerIntegrandS T (kdDh ν μ) τ y i) sepMeas ∧
      Integrable (kerIntegrandS T (kdYGrad ν μ) τ y i) sepMeas ∧
      (∀ l : Fin 3, Integrable (kerIntegrandS T (kdLap ν μ l) τ y i) sepMeas) ∧
      Integrable (kerIntegrandS T (Kd ν μ) τ y i) sepMeas

lemma ae_pos_sepMeas : ∀ᵐ p ∂sepMeas, 0 < p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ))) (ν := (volume : Measure Space))).ae
    (ae_restrict_mem measurableSet_Ioi)

lemma kI_congr (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ Ψ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (hpt : ∀ h : ℝ, 0 < h → ∀ z j k, Φ h y z i j k = Ψ h y z i j k)
    (hΦ : Integrable (kerIntegrandS T Φ τ y i) sepMeas) :
    Integrable (kerIntegrandS T Ψ τ y i) sepMeas := by
  refine hΦ.congr (ae_pos_sepMeas.mono fun p hp => ?_)
  unfold kerIntegrandS
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hpt p.1 hp p.2 j k]

lemma kI_lin (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ Ψ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (a b : ℂ) (hΦ : Integrable (kerIntegrandS T Φ τ y i) sepMeas)
    (hΨ : Integrable (kerIntegrandS T Ψ τ y i) sepMeas) :
    Integrable (kerIntegrandS T (fun h y' z i' j k => a * Φ h y' z i' j k + b * Ψ h y' z i' j k)
      τ y i) sepMeas := by
  have : kerIntegrandS T (fun h y' z i' j k => a * Φ h y' z i' j k + b * Ψ h y' z i' j k) τ y i =
      fun p => a * kerIntegrandS T Φ τ y i p + b * kerIntegrandS T Ψ τ y i p := by
    funext p
    simp only [kerIntegrandS, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  rw [this]
  exact (hΦ.const_mul a).add (hΨ.const_mul b)

lemma kI_sum (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : Fin 3 → ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (hΦ : ∀ l, Integrable (kerIntegrandS T (Φ l) τ y i) sepMeas) :
    Integrable (kerIntegrandS T (fun h y' z i' j k => ∑ l : Fin 3, Φ l h y' z i' j k) τ y i)
      sepMeas := by
  have : kerIntegrandS T (fun h y' z i' j k => ∑ l : Fin 3, Φ l h y' z i' j k) τ y i =
      fun p => ∑ l : Fin 3, kerIntegrandS T (Φ l) τ y i p := by
    funext p
    simp only [kerIntegrandS, Finset.sum_mul]
    calc _ = ∑ j : Fin 3, ∑ l : Fin 3, ∑ k : Fin 3,
          Φ l p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [this]
  exact integrable_finsetSum _ fun l _ => hΦ l

lemma kdYGrad_eq (ν μ : ℝ) (hν : 0 < ν) (h : ℝ) (hh : 0 < h) (y z : Space) (i j k : Fin 3) :
    kdYGrad ν μ h y z i j k =
      1 * fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) y y +
      (-1) * fderiv ℝ (fun y'' => Gker ν ((μ : ℂ) + 1) h y'' z i j k) y y := by
  have hd1 := (gker_contDiff ν (μ : ℂ) hν h hh z i j k).differentiable (by norm_num)
  have hd2 := (gker_contDiff ν ((μ : ℂ) + 1) hν h hh z i j k).differentiable (by norm_num)
  have := fderiv_fun_sub (hd1 y) (hd2 y)
  unfold kdYGrad Kd
  rw [this]
  simp [sub_eq_add_neg]

lemma kdLap_eq (ν μ : ℝ) (hν : 0 < ν) (l : Fin 3) (h : ℝ) (hh : 0 < h) (y z : Space)
    (i j k : Fin 3) :
    kdLap ν μ l h y z i j k =
      1 * fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) y'
        (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l) +
      (-1) * fderiv ℝ (fun y' => fderiv ℝ (fun y'' => Gker ν ((μ : ℂ) + 1) h y'' z i j k) y'
        (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l) := by
  have c1 := gker_contDiff ν (μ : ℂ) hν h hh z i j k
  have c2 := gker_contDiff ν ((μ : ℂ) + 1) hν h hh z i j k
  have hd1 := c1.differentiable (by norm_num)
  have hd2 := c2.differentiable (by norm_num)
  have c1' : ContDiff ℝ 1 (fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k)) :=
    c1.fderiv_right (by norm_num)
  have c2' : ContDiff ℝ 1 (fderiv ℝ (fun y'' => Gker ν ((μ : ℂ) + 1) h y'' z i j k)) :=
    c2.fderiv_right (by norm_num)
  have dΦ : DifferentiableAt ℝ (fun y' => fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) y'
      (UnforcedLeray.coordinateVector l)) y :=
    ((c1'.clm_apply contDiff_const).differentiable (by norm_num)) y
  have dΨ : DifferentiableAt ℝ (fun y' => fderiv ℝ (fun y'' => Gker ν ((μ : ℂ) + 1) h y'' z i j k) y'
      (UnforcedLeray.coordinateVector l)) y :=
    ((c2'.clm_apply contDiff_const).differentiable (by norm_num)) y
  have e : (fun y' => fderiv ℝ (fun y'' => Kd ν μ h y'' z i j k) y'
      (UnforcedLeray.coordinateVector l)) =
      fun y' => fderiv ℝ (fun y'' => Gker ν (μ : ℂ) h y'' z i j k) y'
          (UnforcedLeray.coordinateVector l) -
        fderiv ℝ (fun y'' => Gker ν ((μ : ℂ) + 1) h y'' z i j k) y'
          (UnforcedLeray.coordinateVector l) := by
    funext y'
    have := fderiv_fun_sub (hd1 y') (hd2 y')
    unfold Kd
    rw [this]; rfl
  unfold kdLap
  rw [e, fderiv_fun_sub dΦ dΨ]
  simp [sub_eq_add_neg]

/-- `Kd = G_μ - G_{μ+1}` and the `y`-derivatives split. -/
theorem kdIntegrands_of (hG : GkerIntegrable) (hY : GkerYGradInt) (hL : GkerLapInt)
    (hD : GkerHasDerivH) : KdIntegrandsS := by
  intro ν μ rOut P T hd τ y hy i
  obtain ⟨hν, hμ, hr, hP, hS, hM⟩ := hd
  have hm1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have hm0 : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have g0 : Integrable (kerIntegrandS T (Gker ν (μ : ℂ)) τ y i) sepMeas :=
    hG ν _ hν hm0 rOut P hr hP T hS hM τ y hy i
  have g1 : Integrable (kerIntegrandS T (Gker ν ((μ : ℂ) + 1)) τ y i) sepMeas :=
    hG ν _ hν hm1 rOut P hr hP T hS hM τ y hy i
  have y0 := hY ν _ hν hm0 rOut P hr hP T hS hM τ y hy i
  have y1 := hY ν _ hν hm1 rOut P hr hP T hS hM τ y hy i
  have l0 := fun l => hL ν _ hν hm0 rOut P hr hP T hS hM τ y hy i l
  have l1 := fun l => hL ν _ hν hm1 rOut P hr hP T hS hM τ y hy i l
  have hKd : Integrable (kerIntegrandS T (Kd ν μ) τ y i) sepMeas :=
    kI_congr T _ _ τ y i (fun h _ z j k => by simp only [Kd]; ring) (kI_lin T _ _ τ y i 1 (-1) g0 g1)
  have hYG : Integrable (kerIntegrandS T (kdYGrad ν μ) τ y i) sepMeas :=
    kI_congr T _ _ τ y i (fun h hh z j k => (kdYGrad_eq ν μ hν h hh y z i j k).symm)
      (kI_lin T _ _ τ y i 1 (-1) y0 y1)
  have hLap : ∀ l : Fin 3, Integrable (kerIntegrandS T (kdLap ν μ l) τ y i) sepMeas := fun l =>
    kI_congr T _ _ τ y i (fun h hh z j k => (kdLap_eq ν μ hν l h hh y z i j k).symm)
      (kI_lin T _ _ τ y i 1 (-1) (l0 l) (l1 l))
  have hLk : ∀ (m : ℂ), (-(1 / 4) < m.re) →
      Integrable (kerIntegrandS T (Lker ν (Gker ν m)) τ y i) sepMeas := by
    intro m hm
    have ym := hY ν m hν hm rOut P hr hP T hS hM τ y hy i
    have lm := fun l => hL ν m hν hm rOut P hr hP T hS hM τ y hy i l
    have hs := kI_sum T (fun l h y' z i' j k => fderiv ℝ (fun y'' => fderiv ℝ
      (fun y''' => Gker ν m h y''' z i' j k) y'' (UnforcedLeray.coordinateVector l)) y'
      (UnforcedLeray.coordinateVector l)) τ y i lm
    exact kI_lin T _ _ τ y i (1 / 2 : ℂ) (ν : ℂ) ym hs
  have hDh : Integrable (kerIntegrandS T (kdDh ν μ) τ y i) sepMeas := by
    have A := kI_lin T _ _ τ y i 1 (-1) (hLk _ hm0) (hLk _ hm1)
    have B := kI_lin T _ _ τ y i (-((μ : ℂ) - 1 / 2)) (((μ : ℂ) + 1) - 1 / 2) g0 g1
    have C := kI_lin T _ _ τ y i 1 1 A B
    refine kI_congr T _ _ τ y i (fun h hh z j k => ?_) C
    have h1 := hD ν (μ : ℂ) hν h hh y z i j k
    have h2 := hD ν ((μ : ℂ) + 1) hν h hh y z i j k
    have hd : deriv (fun h' => Kd ν μ h' y z i j k) h =
        (Lker ν (Gker ν (μ : ℂ)) h y z i j k - ((μ : ℂ) - 1 / 2) * Gker ν (μ : ℂ) h y z i j k) -
        (Lker ν (Gker ν ((μ : ℂ) + 1)) h y z i j k
          - (((μ : ℂ) + 1) - 1 / 2) * Gker ν ((μ : ℂ) + 1) h y z i j k) :=
      (h1.sub h2).deriv
    unfold kdDh
    rw [hd]
    ring
  exact ⟨hDh, hYG, hLap, hKd⟩

end UnforcedLeray.Short.PartIIIb.Concrete
