import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1

/-!
# `PartIII-b:C/rep/2/1/3` : periodic dilation sum (SP 3838-3845, 5219-5221)

Pure real analysis.  With `h = -2 log l` the dilation integral becomes
`½ ∫_0^∞ e^{-κh} G(τ-h) dh`, `κ = (c+1)/2`.  Blocks `[kP, kP+P)` of `h` carry the periodic
integral over one period, which is shifted to `(0,P]` (`pds_window`, via `AddCircle`) and
reflected (`pds_reflect`); Cauchy-Schwarz on one period (`pds_cs`) and the geometric sum
`P/(1-e^{-κP}) ≤ 1/κ + P` finish the bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Translation of a period window for a `P`-periodic function (`AddCircle` lift). -/
theorem pds_window {P : ℝ} (hP : 0 < P) {F : ℝ → ℝ≥0∞} (hF : ∀ s, F (s + P) = F s) (t : ℝ) :
    ∫⁻ u in Ioc t (t + P), F u = ∫⁻ u in Ioc 0 P, F u := by
  haveI : Fact (0 < P) := ⟨hP⟩
  have hper : Function.Periodic F P := hF
  let Φ : AddCircle P → ℝ≥0∞ := hper.lift
  have hFΦ : F = fun u : ℝ => Φ (u : AddCircle P) := funext fun u => (hper.lift_coe u).symm
  rw [hFΦ]
  refine (AddCircle.lintegral_preimage P t Φ).trans ?_
  have h0 := AddCircle.lintegral_preimage P 0 Φ
  rw [zero_add] at h0
  exact h0.symm

/-- Reflection of a periodic integral over one period. -/
theorem pds_reflect {P : ℝ} (hP : 0 < P) {F : ℝ → ℝ≥0∞} (hFm : Measurable F)
    (hF : ∀ s, F (s + P) = F s) (τ : ℝ) :
    ∫⁻ x in Ioc 0 P, F (τ - x) = ∫⁻ u in Ioc 0 P, F u := by
  have hpt : ∀ x, (Ioc (τ - P) τ).indicator F (τ - x)
      = (Ico 0 P).indicator (fun x => F (τ - x)) x := by
    intro x
    by_cases h1 : 0 ≤ x ∧ x < P
    · have h2 : τ - x ∈ Ioc (τ - P) τ := ⟨by linarith [h1.2], by linarith [h1.1]⟩
      have h3 : x ∈ Ico 0 P := ⟨h1.1, h1.2⟩
      rw [Set.indicator_apply, Set.indicator_apply, if_pos h2, if_pos h3]
    · have h2 : τ - x ∉ Ioc (τ - P) τ := fun h => h1 ⟨by linarith [h.2], by linarith [h.1]⟩
      have h3 : x ∉ Ico 0 P := fun h => h1 h
      rw [Set.indicator_apply, Set.indicator_apply, if_neg h2, if_neg h3]
  calc ∫⁻ x in Ioc 0 P, F (τ - x)
      = ∫⁻ x in Ico 0 P, F (τ - x) := by
        rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc : Ico (0:ℝ) P =ᵐ[volume] Ioc 0 P)]
    _ = ∫⁻ x, (Ico 0 P).indicator (fun x => F (τ - x)) x :=
        (lintegral_indicator measurableSet_Ico _).symm
    _ = ∫⁻ x, (Ioc (τ - P) τ).indicator F (τ - x) := lintegral_congr fun x => (hpt x).symm
    _ = ∫⁻ x, (Ioc (τ - P) τ).indicator F x := lintegral_sub_left_eq_self _ τ
    _ = ∫⁻ x in Ioc (τ - P) τ, F x := lintegral_indicator measurableSet_Ioc _
    _ = ∫⁻ u in Ioc 0 P, F u := by
        have hW := pds_window hP hF (τ - P)
        rw [show τ - P + P = τ by ring] at hW
        exact hW

/-- Cauchy-Schwarz on one period (`ltauAt` is the normalised `L²` norm). -/
theorem pds_cs {P : ℝ} (hP : 0 < P) {G : ℝ → ℝ≥0∞} (hGm : Measurable G) :
    ∫⁻ u in Ioc 0 P, G u ≤ ENNReal.ofReal P * IIIa.ltauAt P G := by
  have hp0 : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.mpr hP).ne'
  have hpT : ENNReal.ofReal P ≠ ∞ := ENNReal.ofReal_ne_top
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0:ℝ) P))
    (Real.HolderConjugate.two_two) (f := fun _ => (1 : ℝ≥0∞)) (g := G)
    aemeasurable_const hGm.aemeasurable
  have hvol : ∫⁻ a in Ioc (0:ℝ) P, (fun _ => (1 : ℝ≥0∞)) a ^ (2:ℝ) = ENNReal.ofReal P := by
    simp [Real.volume_Ioc]
  have hL2 : (IIIa.ltauAt P G) ^ (2:ℝ)
      = (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, G τ ^ (2:ℝ) := by
    unfold IIIa.ltauAt
    rw [← ENNReal.rpow_mul]
    norm_num
  have hIeq : ∫⁻ τ in Ioc 0 P, G τ ^ (2:ℝ) = ENNReal.ofReal P * (IIIa.ltauAt P G) ^ (2:ℝ) := by
    rw [hL2, ← mul_assoc, ENNReal.mul_inv_cancel hp0 hpT, one_mul]
  have hsq : (ENNReal.ofReal P) ^ (1/2 : ℝ) * (ENNReal.ofReal P) ^ (1/2 : ℝ) = ENNReal.ofReal P := by
    rw [← ENNReal.rpow_add _ _ hp0 hpT]
    norm_num
  have hLsq : ((IIIa.ltauAt P G) ^ (2:ℝ)) ^ (1/2 : ℝ) = IIIa.ltauAt P G := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hIsqrt : (∫⁻ τ in Ioc 0 P, G τ ^ (2:ℝ)) ^ (1/2 : ℝ)
      = (ENNReal.ofReal P) ^ (1/2 : ℝ) * IIIa.ltauAt P G := by
    rw [hIeq, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hLsq]
  calc ∫⁻ u in Ioc 0 P, G u
      = ∫⁻ a in Ioc (0:ℝ) P, (fun _ => (1 : ℝ≥0∞)) a * G a := by simp
    _ ≤ (∫⁻ a in Ioc (0:ℝ) P, (fun _ => (1 : ℝ≥0∞)) a ^ (2:ℝ)) ^ (1/2 : ℝ) *
          (∫⁻ a in Ioc (0:ℝ) P, G a ^ (2:ℝ)) ^ (1/2 : ℝ) := hholder
    _ = ENNReal.ofReal P * IIIa.ltauAt P G := by
        rw [hvol, hIsqrt, ← mul_assoc, hsq]

/-- Geometric factor: `P/(1-e^{-κP}) ≤ 1/κ + P ≤ 2/δ + 1` for `κ ≥ δ/2`, `0 < P ≤ 1`. -/
theorem pds_geom {δ P κ : ℝ} (hδ : 0 < δ) (hP : 0 < P) (hP1 : P ≤ 1) (hκ : δ / 2 ≤ κ) :
    (1 - ENNReal.ofReal (Real.exp (-κ * P)))⁻¹ * ENNReal.ofReal P
      ≤ ENNReal.ofReal (2 / δ + 1) := by
  have hκpos : 0 < κ := by linarith
  obtain ⟨e, he⟩ : ∃ e, e = Real.exp (-κ * P) := ⟨_, rfl⟩
  have hκP : 0 < κ * P := mul_pos hκpos hP
  have he_lt : e < 1 := by
    have h := Real.exp_lt_exp.mpr (show -κ * P < 0 by linarith)
    rw [Real.exp_zero] at h
    rw [he]
    exact h
  have he_pos : 0 < e := by rw [he]; exact Real.exp_pos _
  have h1 : κ * P + 1 ≤ Real.exp (κ * P) := by linarith [Real.add_one_le_exp (κ * P)]
  have he_mul : e * (1 + κ * P) ≤ 1 := by
    have hprod : e * Real.exp (κ * P) = 1 := by
      rw [he, ← Real.exp_add]
      simp
    have := mul_le_mul_of_nonneg_left h1 he_pos.le
    nlinarith
  have h1e : 0 < 1 - e := by linarith
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal e = ENNReal.ofReal (1 - e) := by
    rw [ENNReal.ofReal_sub 1 he_pos.le, ENNReal.ofReal_one]
  rw [← he, hsub, ← ENNReal.ofReal_inv_of_pos h1e,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr h1e.le)]
  apply ENNReal.ofReal_le_ofReal
  rw [inv_mul_le_iff₀ h1e]
  have hinv : 1 / κ ≤ 2 / δ := by
    rw [div_le_div_iff₀ hκpos hδ]
    linarith
  have hkey : P ≤ (1 - e) * (1 / κ + P) := by
    have hid : (1 - e) * (1 / κ + P) - P = (1 - e * (1 + κ * P)) / κ := by
      field_simp
      ring
    have hnn : 0 ≤ (1 - e * (1 + κ * P)) / κ := div_nonneg (by linarith) hκpos.le
    linarith
  have hmul : (1 - e) * (1 / κ + P) ≤ (1 - e) * (2 / δ + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) h1e.le
  linarith

/-- The cover of `(0, ∞)` by the blocks `[kP, kP+P)`. -/
theorem pds_cover {P : ℝ} (hP : 0 < P) :
    Ioi (0:ℝ) ⊆ ⋃ k : ℕ, Ico ((k:ℝ) * P) ((k:ℝ) * P + P) := by
  intro h hh
  have hh' : 0 < h := hh
  have hx : 0 ≤ h / P := (div_pos hh' hP).le
  rw [mem_iUnion]
  refine ⟨⌊h / P⌋₊, Set.mem_Ico.mpr ⟨?_, ?_⟩⟩
  · have h1 := Nat.floor_le hx
    exact (le_div_iff₀ hP).mp h1
  · have h1 := Nat.lt_floor_add_one (h / P)
    have h2 := (div_lt_iff₀ hP).mp h1
    have e1 : ((⌊h / P⌋₊ : ℝ) + 1) * P = (⌊h / P⌋₊ : ℝ) * P + P := by ring
    linarith

/-- Block sum: the `h`-integral over `(0,∞)` is bounded by the geometric sum of one-period
integrals. -/
theorem pds_sum {κ P : ℝ} (hκ : 0 < κ) (hP : 0 < P) {G : ℝ → ℝ≥0∞} (hGm : Measurable G)
    (hper : ∀ s, G (s + P) = G s) (τ : ℝ) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x) ≤
      (1 - ENNReal.ofReal (Real.exp (-κ * P)))⁻¹ * (∫⁻ u in Ioc 0 P, G u) := by
  have hHper : ∀ s, (fun x => G (τ - x)) (s + P) = (fun x => G (τ - x)) s := by
    intro s
    show G (τ - (s + P)) = G (τ - s)
    have h1 := hper (τ - (s + P))
    rw [show τ - (s + P) + P = τ - s by ring] at h1
    exact h1.symm
  have hblock : ∀ k : ℕ,
      ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P), ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x)
        ≤ ENNReal.ofReal (Real.exp (-κ * P)) ^ k * ∫⁻ u in Ioc 0 P, G u := by
    intro k
    have hw : ∀ x ∈ Ico ((k:ℝ) * P) ((k:ℝ) * P + P),
        ENNReal.ofReal (Real.exp (-κ * x)) ≤ ENNReal.ofReal (Real.exp (-κ * ((k:ℝ) * P))) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h1 := hx.1
      nlinarith
    have hstep1 : ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P),
          ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x)
        ≤ ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P),
            ENNReal.ofReal (Real.exp (-κ * ((k:ℝ) * P))) * G (τ - x) :=
      setLIntegral_mono' measurableSet_Ico fun x hx => mul_le_mul' (hw x hx) le_rfl
    have hWb : ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P), G (τ - x) = ∫⁻ u in Ioc 0 P, G u := by
      rw [Measure.restrict_congr_set
        (Ico_ae_eq_Ioc : Ico ((k:ℝ) * P) ((k:ℝ) * P + P) =ᵐ[volume]
          Ioc ((k:ℝ) * P) ((k:ℝ) * P + P))]
      have hW : ∫⁻ x in Ioc ((k:ℝ) * P) ((k:ℝ) * P + P), G (τ - x)
          = ∫⁻ x in Ioc 0 P, G (τ - x) :=
        pds_window hP hHper ((k:ℝ) * P)
      rw [hW]
      exact pds_reflect hP hGm hper τ
    have hpow : ENNReal.ofReal (Real.exp (-κ * ((k:ℝ) * P)))
        = ENNReal.ofReal (Real.exp (-κ * P)) ^ k := by
      rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
      rw [show -κ * ((k:ℝ) * P) = (k:ℝ) * (-κ * P) by ring]
    calc ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P), ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x)
        ≤ ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P),
            ENNReal.ofReal (Real.exp (-κ * ((k:ℝ) * P))) * G (τ - x) := hstep1
      _ = ENNReal.ofReal (Real.exp (-κ * ((k:ℝ) * P)))
            * ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P), G (τ - x) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (Real.exp (-κ * P)) ^ k * ∫⁻ u in Ioc 0 P, G u := by
          rw [hWb, hpow]
  have hsum : ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x)
      ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-κ * P)) ^ k * ∫⁻ u in Ioc 0 P, G u := by
    calc ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x)
        ≤ ∫⁻ x in ⋃ k : ℕ, Ico ((k:ℝ) * P) ((k:ℝ) * P + P),
            ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x) :=
          lintegral_mono_set (pds_cover hP)
      _ ≤ ∑' k : ℕ, ∫⁻ x in Ico ((k:ℝ) * P) ((k:ℝ) * P + P),
            ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x) :=
          lintegral_iUnion_le (fun k : ℕ => Ico ((k:ℝ) * P) ((k:ℝ) * P + P))
            (fun x => ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x))
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-κ * P)) ^ k * ∫⁻ u in Ioc 0 P, G u :=
          ENNReal.tsum_le_tsum hblock
  calc _ ≤ _ := hsum
    _ = (1 - ENNReal.ofReal (Real.exp (-κ * P)))⁻¹ * ∫⁻ u in Ioc 0 P, G u := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

theorem periodicDilationSum_proved : UnforcedLeray.Short.PartIIIb.Concrete.PeriodicDilationSum := by
  intro δ hδ
  refine ⟨1 / 2 * (2 / δ + 1), mul_nonneg (by norm_num)
    (by have : 0 < 2 / δ := div_pos two_pos hδ; linarith), ?_⟩
  intro c hc P hP hP1 G hGm hper τ
  have hκ : 0 < (c + 1) / 2 := by linarith
  have hκδ : δ / 2 ≤ (c + 1) / 2 := by linarith
  have hpt : ∀ l ∈ Ioo (0:ℝ) 1,
      ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (|(-2 * l⁻¹)|)
          * (ENNReal.ofReal (Real.exp (-((c + 1) / 2) * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have habs : |(-2 * l⁻¹)| = 2 * l⁻¹ := by
      rw [show (-2 * l⁻¹) = -(2 * l⁻¹) by ring, abs_neg,
        abs_of_pos (mul_pos two_pos (inv_pos.mpr hl0))]
    have e1 : Real.exp (-((c + 1) / 2) * (-2 * Real.log l)) = l ^ c * l := by
      rw [← Real.rpow_add_one hl0.ne' c, Real.rpow_def_of_pos hl0]
      congr 1
      ring
    have e2 : τ - (-2 * Real.log l) = τ + 2 * Real.log l := by ring
    have hL : ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (2 * l ^ c) * G (τ + 2 * Real.log l) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
    have hR : ENNReal.ofReal (2 * l⁻¹) * (ENNReal.ofReal (l ^ c * l) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (2 * l ^ c) * G (τ + 2 * Real.log l) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (inv_nonneg.mpr hl0.le))]
      have hal : 2 * l⁻¹ * (l ^ c * l) = 2 * l ^ c := by
        field_simp
      rw [hal]
    rw [habs, e1, e2, hL, hR]
  have hJ1 : ∫⁻ l in Ioo (0:ℝ) 1,
        ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
      = ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (|(-2 * l⁻¹)|)
          * (ENNReal.ofReal (Real.exp (-((c + 1) / 2) * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) :=
    setLIntegral_congr_fun measurableSet_Ioo fun l hl => hpt l hl
  have hf' : ∀ x ∈ Ioo (0:ℝ) 1,
      HasDerivWithinAt (fun l : ℝ => -2 * Real.log l) (-2 * x⁻¹) (Ioo (0:ℝ) 1) x := by
    intro x hx
    exact ((Real.hasDerivAt_log hx.1.ne').const_mul (-2)).hasDerivWithinAt
  have hinj : InjOn (fun l : ℝ => -2 * Real.log l) (Ioo (0:ℝ) 1) := by
    intro a ha b hb hab
    have h1 : Real.log a = Real.log b := by
      have hab' : -2 * Real.log a = -2 * Real.log b := hab
      linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr hb.1) h1
  have hJ2 := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hf' hinj
    (fun x => ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x))
  have hsub : (fun l : ℝ => -2 * Real.log l) '' Ioo (0:ℝ) 1 ⊆ Ioi 0 := by
    rintro _ ⟨l, hl, rfl⟩
    have := Real.log_neg hl.1 hl.2
    show 0 < -2 * Real.log l
    linarith
  have hmono : ∫⁻ x in (fun l : ℝ => -2 * Real.log l) '' Ioo (0:ℝ) 1,
        ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x)
      ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x) :=
    lintegral_mono_set hsub
  have hL : ENNReal.ofReal 2 * ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
      ≤ ENNReal.ofReal (2 / δ + 1) * IIIa.ltauAt P G := by
    calc ENNReal.ofReal 2 * ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
        = ∫⁻ l in Ioo (0:ℝ) 1,
            ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (|(-2 * l⁻¹)|)
          * (ENNReal.ofReal (Real.exp (-((c + 1) / 2) * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) := hJ1
      _ = ∫⁻ x in (fun l : ℝ => -2 * Real.log l) '' Ioo (0:ℝ) 1,
            ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x) := hJ2.symm
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-((c + 1) / 2) * x)) * G (τ - x) := hmono
      _ ≤ (1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹ * (∫⁻ u in Ioc 0 P, G u) :=
          pds_sum hκ hP hGm hper τ
      _ ≤ (1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹
            * (ENNReal.ofReal P * IIIa.ltauAt P G) :=
          mul_le_mul' le_rfl (pds_cs hP hGm)
      _ = ((1 - ENNReal.ofReal (Real.exp (-((c + 1) / 2) * P)))⁻¹ * ENNReal.ofReal P)
            * IIIa.ltauAt P G := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal (2 / δ + 1) * IIIa.ltauAt P G :=
          mul_le_mul' (pds_geom hδ hP hP1 hκδ) le_rfl
  have hhalf : ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2 = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 2)]
    norm_num
  calc ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
      = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal 2
          * ∫⁻ l in Ioo (0:ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)) := by
        rw [← mul_assoc, hhalf, one_mul]
    _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 / δ + 1) * IIIa.ltauAt P G) :=
        mul_le_mul' le_rfl hL
    _ = ENNReal.ofReal (1 / 2 * (2 / δ + 1)) * IIIa.ltauAt P G := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1 / 2), mul_assoc]

end UnforcedLeray.Short.PartIIIb.Concrete
