import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a

/-!
# Decomposition of `ExtIntKdLipschitz` (`PartIII-b:C/rep/2/6/3/2/1/5`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200.

Idea.  `Kd = (1 - e^{-h}) G_μ` (since `G_{μ+1} = e^{-h} G_μ`), so for `h > 0`
`dh Kd = e^{-h} G_μ + (1 - e^{-h})(L G_μ - (μ - 1/2) G_μ)` (`GkerHasDerivH`), and both `G_μ` and
`L G_μ` are controlled by the majorant `gkerMaj μ T t` (`SepKernelBounds`, via `sepPhi` and its
`y`-derivatives of order `≤ 2`).  For `t` in the ball `(τ-1, τ+1)` and `t₀ = τ+1`, the majorant at
time `t` is dominated by `e^{2μ+3}` times the majorant at time `t₀`
(`gkerMaj μ T t (t-s,z) ≤ K gkerMaj μ T t₀ (t₀-s,z)`), and the latter, shifted to the variable
`s`, is the integrable envelope.  The kink at `t = s` is handled by continuity (`Kd(0)=0`,
`|Kd| ≤ (1-e^{-h}) ‖G_μ‖`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- (H0) `sepGapPointwise` with the constant independent of `τ` and `i` (the proof of
`sepGapPointwise` in `Sub/IIIb-D2_3_1_1_2/L4.lean` produces `C = 18 Cn c^{-6}` depending only on the
kernel constants and on `y₀`; here only the value at `y = y₀` is needed). -/
def SepGapPointwiseUnif : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T →
    ∀ y₀ : Space, rOut < ϱ y₀ →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ) (i : Fin 3), ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space, ∀ n : ℕ, n ≤ 2 →
        ‖iteratedFDeriv ℝ n (sepPhi ν μ T τ i (l, z)) y₀‖ ≤ C * sepMajorant μ T τ n (l, z)

/-- (H1) `Kd = (1 - e^{-h}) G_μ` and `GkerHasDerivH` (`∂_h G_m = L G_m - (m-1/2) G_m`, proved as
`gkerHasDerivH`): for `h > 0`, `h ↦ Kd h` has the stated derivative. -/
def KdHasDerivAt : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ h : ℝ, 0 < h → ∀ (y z : Space) (i j k : Fin 3),
    HasDerivAt (fun h' => Kd ν μ h' y z i j k)
      (((Real.exp (-h) : ℝ) : ℂ) * Gker ν (μ : ℂ) h y z i j k +
        ((1 - Real.exp (-h) : ℝ) : ℂ) *
          (Lker ν (Gker ν (μ : ℂ)) h y z i j k - ((μ : ℂ) - 1 / 2) * Gker ν (μ : ℂ) h y z i j k)) h

/-- (H2) `L` applied to the `T`-contracted kernel is `-(l/2)` times `L` applied to `sepPhi`
(`l = e^{-h/2}`; `ΣΣ Gker · T(t₀-h) = -(l/2) sepPhi`, `gkerSum_eq_sepPhi`; `L` is linear and `T`
does not depend on `y`; `sepPhi` is `C²` by `sepPhi_contDiff`, `heatLerayKSmooth`). -/
def LkerSumEq : Prop :=
  ∀ (ν μ : ℝ), 0 < ν → ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (t₀ h : ℝ), 0 < h →
    ∀ (y z : Space) (i : Fin 3),
      ∑ j : Fin 3, ∑ k : Fin 3, Lker ν (Gker ν (μ : ℂ)) h y z i j k * ((T (t₀ - h) z j k : ℝ) : ℂ) =
        -((Real.exp (-h / 2) / 2 : ℝ) : ℂ) *
          ((1 / 2 : ℂ) * fderiv ℝ (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) y y +
            (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ
              (sepPhi ν (μ : ℂ) T t₀ i (Real.exp (-h / 2), z)) y' (UnforcedLeray.coordinateVector l)) y
              (UnforcedLeray.coordinateVector l))

/-- (H3) Norm of `½ y·∇Φ + ν ΔΦ` by the first two iterated derivatives. -/
def LOpBound : Prop :=
  ∀ (ν : ℝ) (Φ : Space → ℂ) (y : Space), ContDiff ℝ 2 Φ →
    ‖(1 / 2 : ℂ) * fderiv ℝ Φ y y + (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ Φ y'
        (UnforcedLeray.coordinateVector l)) y (UnforcedLeray.coordinateVector l)‖ ≤
      (‖y‖ / 2) * ‖iteratedFDeriv ℝ 1 Φ y‖ + 3 * |ν| * ‖iteratedFDeriv ℝ 2 Φ y‖

/-- (H4) `(1 + l|z|)^{-(4+n)} ≤ (1 + l|z|)^{-4}`. -/
def SepMajorantMono : Prop :=
  ∀ (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (n : ℕ) (p : ℝ × Space),
    0 ≤ p.1 → sepMajorant μ T τ n p ≤ sepMajorant μ T τ 0 p

/-- (H5) Time-shift comparison of the majorant (`l' = e^{-(t-s)/2} ≤ e·l_ref`, `l' ≥ l_ref`;
the tensor factor is `T(s,z)` on both sides). -/
def GkerMajShiftLe : Prop :=
  ∀ (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (s t t₀ : ℝ) (z : Space),
    -(1 / 4) < μ.re → s < t → t ≤ t₀ → t₀ - t ≤ 2 →
      gkerMaj μ T t (t - s, z) ≤ Real.exp (2 * μ.re + 3) * gkerMaj μ T t₀ (t₀ - s, z)

/-- (H6) Integrability of the `h`-majorant on `Ioi 0 × Space` (the claim `hgI` inside
`gkerIntegrable`, `Concrete/ReturnRepair/.../L6_3_Comb/S1a.lean`, from `sepGapMajorantIntegrable`
and `gkerMaj_lintegral_lt_top`, `gkerMaj_measurable`), for every base time `t₀`. -/
def GkerMajIntegrable : Prop :=
  ∀ (μ : ℂ) (P rOut : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), -(1 / 4) < μ.re → 0 < P →
    IIIa.IsSepSource P rOut T → SepMoment P T → ∀ t₀ : ℝ,
      Integrable (gkerMaj μ T t₀) ((volume.restrict (Ioi (0 : ℝ))).prod volume)

/-- (H7) Reflection `h = t₀ - s` (measure preserving `(s,z) ↦ (t₀ - s, z)`), zero for `s ≥ t₀`. -/
def GkerMajShiftIntegrable : Prop :=
  ∀ (G : ℝ × Space → ℝ) (t₀ : ℝ), Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod volume) →
    Integrable (fun p : ℝ × Space => if p.1 < t₀ then G (t₀ - p.1, p.2) else 0)
      (volume.prod volume)

/-- (H8) Lipschitz bound for a continuous function with bounded derivative off one point. -/
def LipOffPoint : Prop :=
  ∀ (f f' : ℝ → ℂ) (s₀ a b B : ℝ), 0 ≤ B → ContinuousOn f (Ioo a b) →
    (∀ t ∈ Ioo a b, t ≠ s₀ → HasDerivAt f (f' t) t) →
    (∀ t ∈ Ioo a b, t ≠ s₀ → ‖f' t‖ ≤ B) → LipschitzOnWith (Real.nnabs B) f (Ioo a b)

theorem gkerMaj_nonneg (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ)
    (q : ℝ × Space) : 0 ≤ gkerMaj μ T t q := by
  unfold gkerMaj sepMajorant IIIa.tensorNorm
  simp only
  positivity

theorem gkerMaj_le_tensor (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (t h : ℝ)
    (z : Space) (hh : 0 ≤ h) (hμ : -(1 / 4) < μ.re) :
    gkerMaj μ T t (h, z) ≤ IIIa.tensorNorm (T (t - h) z) / 2 := by
  have hl : Real.exp (-h / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hl0 : 0 < Real.exp (-h / 2) := Real.exp_pos _
  have h1 : Real.exp (-h / 2) ^ (2 * μ.re + 2) ≤ 1 :=
    Real.rpow_le_one hl0.le hl (by linarith)
  have h2 : (1 + Real.exp (-h / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [norm_nonneg z]) (by norm_num)
  have hlog : t + 2 * Real.log (Real.exp (-h / 2)) = t - h := by
    rw [Real.log_exp]; ring
  have hT : 0 ≤ IIIa.tensorNorm (T (t - h) z) := Real.sqrt_nonneg _
  unfold gkerMaj sepMajorant
  simp only [hlog]
  have h3 : 0 ≤ (1 + Real.exp (-h / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := by positivity
  have h4 : 0 ≤ Real.exp (-h / 2) ^ (2 * μ.re + 2) := by positivity
  calc Real.exp (-h / 2) / 2 * (Real.exp (-h / 2) ^ (2 * μ.re + 2) *
        (1 + Real.exp (-h / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) * IIIa.tensorNorm (T (t - h) z))
      ≤ 1 / 2 * (1 * 1 * IIIa.tensorNorm (T (t - h) z)) := by
        gcongr
    _ = _ := by ring

section bounds

variable (ν μ : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (y : Space) (C0 : ℝ)

theorem sumG_bound (hν : 0 < ν)
    (hC : ∀ (τ : ℝ) (i : Fin 3), ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (sepPhi ν (μ : ℂ) T τ i (l, z)) y‖ ≤ C0 * sepMajorant (μ : ℂ) T τ n (l, z))
    (t h : ℝ) (hh : 0 < h) (z : Space) (i : Fin 3) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, Gker ν (μ : ℂ) h y z i j k * ((T (t - h) z j k : ℝ) : ℂ)‖ ≤
      C0 * gkerMaj (μ : ℂ) T t (h, z) := by
  have hl : Real.exp (-h / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  have hn := hC t i _ hl z 0 (Nat.zero_le _)
  rw [norm_iteratedFDeriv_zero] at hn
  rw [gkerSum_eq_sepPhi ν (μ : ℂ) T t i y z h]
  have hc0 : 0 ≤ Real.exp (-h / 2) / 2 := by positivity
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc0]
  calc Real.exp (-h / 2) / 2 * ‖sepPhi ν (μ : ℂ) T t i (Real.exp (-h / 2), z) y‖
      ≤ Real.exp (-h / 2) / 2 * (C0 * sepMajorant (μ : ℂ) T t 0 (Real.exp (-h / 2), z)) :=
        mul_le_mul_of_nonneg_left hn hc0
    _ = C0 * gkerMaj (μ : ℂ) T t (h, z) := by
        simp only [gkerMaj]
        ring

theorem sumL_bound (hν : 0 < ν) (hC0 : 0 ≤ C0) (hLS : LkerSumEq) (hLB : LOpBound) (hM : SepMajorantMono)
    (hC : ∀ (τ : ℝ) (i : Fin 3), ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (sepPhi ν (μ : ℂ) T τ i (l, z)) y‖ ≤ C0 * sepMajorant (μ : ℂ) T τ n (l, z))
    (t h : ℝ) (hh : 0 < h) (z : Space) (i : Fin 3) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, Lker ν (Gker ν (μ : ℂ)) h y z i j k * ((T (t - h) z j k : ℝ) : ℂ)‖ ≤
      (C0 * (‖y‖ / 2 + 3 * |ν|)) * gkerMaj (μ : ℂ) T t (h, z) := by
  have hl : Real.exp (-h / 2) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (by linarith)⟩
  rw [hLS ν μ hν T t h hh y z i]
  have hcd : ContDiff ℝ 2 (sepPhi ν (μ : ℂ) T t i (Real.exp (-h / 2), z)) :=
    sepPhi_contDiff heatLerayKSmooth ν (μ : ℂ) T t i _ z hν hl
  have hb := hLB ν _ y hcd
  have h1 := hC t i _ hl z 1 (by norm_num)
  have h2 := hC t i _ hl z 2 (by norm_num)
  have m1 := hM (μ : ℂ) T t 1 (Real.exp (-h / 2), z) (Real.exp_pos _).le
  have m2 := hM (μ : ℂ) T t 2 (Real.exp (-h / 2), z) (Real.exp_pos _).le
  have hc0 : 0 ≤ Real.exp (-h / 2) / 2 := by positivity
  have hMaj : 0 ≤ sepMajorant (μ : ℂ) T t 0 (Real.exp (-h / 2), z) := by
    unfold sepMajorant IIIa.tensorNorm; simp only; positivity
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc0]
  have hLe : ‖(1 / 2 : ℂ) * fderiv ℝ (sepPhi ν (μ : ℂ) T t i (Real.exp (-h / 2), z)) y y +
      (ν : ℂ) * ∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ
        (sepPhi ν (μ : ℂ) T t i (Real.exp (-h / 2), z)) y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l)‖ ≤
      C0 * (‖y‖ / 2 + 3 * |ν|) * sepMajorant (μ : ℂ) T t 0 (Real.exp (-h / 2), z) := by
    refine hb.trans ?_
    have e1 : (‖y‖ / 2) * ‖iteratedFDeriv ℝ 1 (sepPhi ν (μ : ℂ) T t i (Real.exp (-h / 2), z)) y‖ ≤
        (‖y‖ / 2) * (C0 * sepMajorant (μ : ℂ) T t 0 (Real.exp (-h / 2), z)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left m1 hC0)) (by positivity)
    have e2 : 3 * |ν| * ‖iteratedFDeriv ℝ 2 (sepPhi ν (μ : ℂ) T t i (Real.exp (-h / 2), z)) y‖ ≤
        3 * |ν| * (C0 * sepMajorant (μ : ℂ) T t 0 (Real.exp (-h / 2), z)) :=
      mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left m2 hC0)) (by positivity)
    nlinarith
  calc Real.exp (-h / 2) / 2 * _ ≤ Real.exp (-h / 2) / 2 *
        (C0 * (‖y‖ / 2 + 3 * |ν|) * sepMajorant (μ : ℂ) T t 0 (Real.exp (-h / 2), z)) :=
        mul_le_mul_of_nonneg_left hLe hc0
    _ = C0 * (‖y‖ / 2 + 3 * |ν|) * gkerMaj (μ : ℂ) T t (h, z) := by
        simp only [gkerMaj]; ring

/-- The explicit `h`-derivative of `Kd` for `h > 0` (see `KdHasDerivAt`). -/
def kdE (ν μ h : ℝ) (y z : Space) (i j k : Fin 3) : ℂ :=
  ((Real.exp (-h) : ℝ) : ℂ) * Gker ν (μ : ℂ) h y z i j k +
        ((1 - Real.exp (-h) : ℝ) : ℂ) *
          (Lker ν (Gker ν (μ : ℂ)) h y z i j k - ((μ : ℂ) - 1 / 2) * Gker ν (μ : ℂ) h y z i j k)

theorem kdE_bound (hν : 0 < ν) (hC0 : 0 ≤ C0) (hLS : LkerSumEq) (hLB : LOpBound)
    (hM : SepMajorantMono)
    (hC : ∀ (τ : ℝ) (i : Fin 3), ∀ l ∈ Ioo (0 : ℝ) 1, ∀ z : Space, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n (sepPhi ν (μ : ℂ) T τ i (l, z)) y‖ ≤ C0 * sepMajorant (μ : ℂ) T τ n (l, z))
    (t h : ℝ) (hh : 0 < h) (z : Space) (i : Fin 3) :
    ‖∑ j : Fin 3, ∑ k : Fin 3, kdE ν μ h y z i j k * ((T (t - h) z j k : ℝ) : ℂ)‖ ≤
      ((1 + ‖(μ : ℂ) - 1 / 2‖) * C0 + C0 * (‖y‖ / 2 + 3 * |ν|)) * gkerMaj (μ : ℂ) T t (h, z) := by
  have hA := sumG_bound ν μ T y C0 hν hC t h hh z i
  have hB := sumL_bound ν μ T y C0 hν hC0 hLS hLB hM hC t h hh z i
  set A := ∑ j : Fin 3, ∑ k : Fin 3, Gker ν (μ : ℂ) h y z i j k * ((T (t - h) z j k : ℝ) : ℂ) with hAd
  set B := ∑ j : Fin 3, ∑ k : Fin 3, Lker ν (Gker ν (μ : ℂ)) h y z i j k *
    ((T (t - h) z j k : ℝ) : ℂ) with hBd
  have hsum : ∑ j : Fin 3, ∑ k : Fin 3, kdE ν μ h y z i j k * ((T (t - h) z j k : ℝ) : ℂ) =
      ((Real.exp (-h) : ℝ) : ℂ) * A + ((1 - Real.exp (-h) : ℝ) : ℂ) * (B - ((μ : ℂ) - 1 / 2) * A) := by
    simp only [kdE, hAd, hBd, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hsum]
  have he0 : 0 < Real.exp (-h) := Real.exp_pos _
  have he1 : Real.exp (-h) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hG : 0 ≤ gkerMaj (μ : ℂ) T t (h, z) := gkerMaj_nonneg _ _ _ _
  have n1 : ‖((Real.exp (-h) : ℝ) : ℂ) * A‖ ≤ C0 * gkerMaj (μ : ℂ) T t (h, z) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg he0.le]
    calc Real.exp (-h) * ‖A‖ ≤ 1 * (C0 * gkerMaj (μ : ℂ) T t (h, z)) :=
          mul_le_mul he1.le hA (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have n2 : ‖((1 - Real.exp (-h) : ℝ) : ℂ) * (B - ((μ : ℂ) - 1 / 2) * A)‖ ≤
      C0 * (‖y‖ / 2 + 3 * |ν|) * gkerMaj (μ : ℂ) T t (h, z) + ‖(μ : ℂ) - 1 / 2‖ * C0 *
        gkerMaj (μ : ℂ) T t (h, z) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have hin : ‖B - ((μ : ℂ) - 1 / 2) * A‖ ≤ C0 * (‖y‖ / 2 + 3 * |ν|) * gkerMaj (μ : ℂ) T t (h, z) +
        ‖(μ : ℂ) - 1 / 2‖ * C0 * gkerMaj (μ : ℂ) T t (h, z) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul_of_nonneg_left hA (norm_nonneg ((μ : ℂ) - 1 / 2))
      linarith
    have h1m : 1 - Real.exp (-h) ≤ 1 := by linarith
    calc (1 - Real.exp (-h)) * ‖B - ((μ : ℂ) - 1 / 2) * A‖
        ≤ 1 * (C0 * (‖y‖ / 2 + 3 * |ν|) * gkerMaj (μ : ℂ) T t (h, z) +
          ‖(μ : ℂ) - 1 / 2‖ * C0 * gkerMaj (μ : ℂ) T t (h, z)) :=
          mul_le_mul h1m hin (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine (norm_add_le _ _).trans ?_
  nlinarith

end bounds

theorem kd_eq_gker (ν μ h : ℝ) (y z : Space) (i j k : Fin 3) :
    Kd ν μ h y z i j k = ((1 - Real.exp (-h) : ℝ) : ℂ) * Gker ν (μ : ℂ) h y z i j k := by
  have hE : Complex.exp (-((μ : ℂ) + 1 + 3 / 2) * (h : ℂ)) =
      Complex.exp (-((μ : ℂ) + 3 / 2) * (h : ℂ)) * ((Real.exp (-h) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [Kd, Gker, hE]
  push_cast
  ring

/-- The `h`-sum identity: `∑∑ Kd · T = (1 - e^{-h}) ∑∑ Gker · T`. -/
theorem kd_sum_eq (ν μ h : ℝ) (y z : Space) (i : Fin 3) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ j : Fin 3, ∑ k : Fin 3, Kd ν μ h y z i j k * ((M j k : ℝ) : ℂ) =
      ((1 - Real.exp (-h) : ℝ) : ℂ) *
        ∑ j : Fin 3, ∑ k : Fin 3, Gker ν (μ : ℂ) h y z i j k * ((M j k : ℝ) : ℂ) := by
  simp only [Finset.mul_sum, kd_eq_gker]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem extInt_apply (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (t : ℝ) (y : Space) (i : Fin 3)
    (s : ℝ) (z : Space) :
    extInt T Φ t y i (s, z) =
      if s < t then ∑ j : Fin 3, ∑ k : Fin 3, Φ (t - s) y z i j k * ((T s z j k : ℝ) : ℂ) else 0 := by
  unfold extInt
  simp only [Set.indicator_apply, Set.mem_Iio]

theorem extIntKdLipschitz_of (hU : SepGapPointwiseUnif) (h1 : KdHasDerivAt) (h2 : LkerSumEq)
    (h3 : LOpBound) (h4 : SepMajorantMono) (h5 : GkerMajShiftLe) (h6 : GkerMajIntegrable)
    (h7 : GkerMajShiftIntegrable) (h8 : LipOffPoint) : ExtIntKdLipschitz := by
  intro ν μ rOut P T hS τ y hy i
  obtain ⟨hν, hμ, hr, hP, hT, hM⟩ := hS
  have hμ' : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  obtain ⟨C0, hC0, hU0⟩ := hU ν (μ : ℂ) rOut P T hν hμ' hr hP hT y hy
  set C2 : ℝ := (1 + ‖(μ : ℂ) - 1 / 2‖) * C0 + C0 * (‖y‖ / 2 + 3 * |ν|) with hC2
  have hC2n : 0 ≤ C2 := by positivity
  set t₀ : ℝ := τ + 1 with ht₀
  set K : ℝ := Real.exp (2 * μ + 3) with hK
  have hK0 : 0 < K := Real.exp_pos _
  refine ⟨1, one_pos, fun p => C2 * K *
    (if p.1 < t₀ then gkerMaj (μ : ℂ) T t₀ (t₀ - p.1, p.2) else 0), ?_, ?_⟩
  · exact (h7 _ t₀ (h6 (μ : ℂ) P rOut T hμ' hP hT hM t₀)).const_mul (C2 * K)
  · refine Filter.Eventually.of_forall fun p => ?_
    obtain ⟨s, z⟩ := p
    have hderiv : ∀ t, s < t → HasDerivAt (fun t' => extInt T (Kd ν μ) t' y i (s, z))
        (∑ j : Fin 3, ∑ k : Fin 3, kdE ν μ (t - s) y z i j k * ((T s z j k : ℝ) : ℂ)) t := by
      intro t hst
      have hev : (fun t' => extInt T (Kd ν μ) t' y i (s, z)) =ᶠ[nhds t]
          fun t' => ∑ j : Fin 3, ∑ k : Fin 3,
            Kd ν μ (t' - s) y z i j k * ((T s z j k : ℝ) : ℂ) := by
        filter_upwards [Ioi_mem_nhds hst] with t' ht'
        rw [extInt_apply, if_pos (show s < t' from ht')]
      refine HasDerivAt.congr_of_eventuallyEq ?_ hev
      refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_
      exact ((h1 ν μ hν (t - s) (sub_pos.2 hst) y z i j k).comp_sub_const t s).mul_const _
    have hzero : ∀ t, t < s → HasDerivAt (fun t' => extInt T (Kd ν μ) t' y i (s, z)) 0 t := by
      intro t hts
      have hev : (fun t' => extInt T (Kd ν μ) t' y i (s, z)) =ᶠ[nhds t] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hts] with t' ht'
        rw [extInt_apply, if_neg (not_lt.2 (le_of_lt ht'))]
      exact (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq hev
    -- bound of the function itself right of the kink
    have hfb : ∀ t', ‖extInt T (Kd ν μ) t' y i (s, z)‖ ≤
        (C0 * (IIIa.tensorNorm (T s z) / 2)) * (1 - Real.exp (-(max (t' - s) 0))) := by
      intro t'
      by_cases hst : s < t'
      · have hh : 0 < t' - s := sub_pos.2 hst
        rw [extInt_apply, if_pos hst, max_eq_left hh.le, kd_sum_eq, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by have := Real.exp_lt_one_iff.2 (by linarith : -(t' - s) < 0); linarith)]
        have hA := sumG_bound ν μ T y C0 hν hU0 t' (t' - s) hh z i
        rw [sub_sub_cancel] at hA
        have hG := gkerMaj_le_tensor (μ : ℂ) T t' (t' - s) z hh.le hμ'
        rw [sub_sub_cancel] at hG
        have hex : 0 ≤ 1 - Real.exp (-(t' - s)) := by
          have := Real.exp_lt_one_iff.2 (by linarith : -(t' - s) < 0); linarith
        calc (1 - Real.exp (-(t' - s))) * _ ≤ (1 - Real.exp (-(t' - s))) *
              (C0 * (IIIa.tensorNorm (T s z) / 2)) :=
              mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hG hC0)) hex
          _ = _ := by ring
      · rw [extInt_apply, if_neg hst, norm_zero]
        have : max (t' - s) 0 = 0 := max_eq_right (by linarith [not_lt.1 hst])
        rw [this]
        simp
    have hcs : ContinuousAt (fun t' => extInt T (Kd ν μ) t' y i (s, z)) s := by
      have hfs : extInt T (Kd ν μ) s y i (s, z) = 0 := by
        rw [extInt_apply, if_neg (lt_irrefl s)]
      have hcont : Continuous (fun t' : ℝ =>
          (C0 * (IIIa.tensorNorm (T s z) / 2)) * (1 - Real.exp (-(max (t' - s) 0)))) := by
        fun_prop
      have hlim := hcont.tendsto s
      simp only [sub_self, max_self, neg_zero, Real.exp_zero, sub_self, mul_zero] at hlim
      show Filter.Tendsto _ _ (nhds (extInt T (Kd ν μ) s y i (s, z)))
      rw [hfs, tendsto_zero_iff_norm_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) hfb hlim
    have hB0 : 0 ≤ C2 * K * (if s < t₀ then gkerMaj (μ : ℂ) T t₀ (t₀ - s, z) else 0) := by
      refine mul_nonneg (by positivity) ?_
      split_ifs
      · exact gkerMaj_nonneg _ _ _ _
      · exact le_rfl
    rw [Real.ball_eq_Ioo]
    refine h8 (fun t' => extInt T (Kd ν μ) t' y i (s, z))
      (fun t => if s < t then ∑ j : Fin 3, ∑ k : Fin 3, kdE ν μ (t - s) y z i j k *
        ((T s z j k : ℝ) : ℂ) else 0) s (τ - 1) (τ + 1)
      (C2 * K * (if s < t₀ then gkerMaj (μ : ℂ) T t₀ (t₀ - s, z) else 0)) hB0 ?_ ?_ ?_
    · intro t ht
      rcases lt_trichotomy t s with hts | hts | hts
      · exact (hzero t hts).continuousAt.continuousWithinAt
      · subst hts; exact hcs.continuousWithinAt
      · exact (hderiv t hts).continuousAt.continuousWithinAt
    · intro t ht hne
      rcases lt_or_gt_of_ne hne with hts | hts
      · rw [if_neg (not_lt.2 hts.le)]; exact hzero t hts
      · rw [if_pos hts]; exact hderiv t hts
    · intro t ht hne
      rcases lt_or_gt_of_ne hne with hts | hts
      · rw [if_neg (not_lt.2 hts.le), norm_zero]; exact hB0
      · rw [if_pos hts]
        have hb := kdE_bound ν μ T y C0 hν hC0 h2 h3 h4 hU0 t (t - s) (sub_pos.2 hts) z i
        rw [sub_sub_cancel] at hb
        have h5' := h5 (μ : ℂ) T s t t₀ z hμ' hts (by simp only [ht₀]; linarith [ht.2])
          (by simp only [ht₀]; linarith [ht.1])
        simp only [Complex.ofReal_re] at h5'
        have hlt : s < t₀ := by simp only [ht₀]; linarith [ht.2]
        rw [if_pos hlt]
        calc _ ≤ C2 * gkerMaj (μ : ℂ) T t (t - s, z) := hb
          _ ≤ C2 * (K * gkerMaj (μ : ℂ) T t₀ (t₀ - s, z)) :=
              mul_le_mul_of_nonneg_left h5' hC2n
          _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
