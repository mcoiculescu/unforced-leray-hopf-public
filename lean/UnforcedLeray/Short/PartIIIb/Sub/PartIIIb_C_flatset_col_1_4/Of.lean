import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_1_4.Bounds
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# `FlatForceCurlTsum` from the smoothness of `f_A` (source 4597-4608, 4963-4976, 4988)

`flatForceCurlTsum_of (h : FlatForceSmooth) : FlatForceCurlTsum`.  Smoothness (`PartIII-b:C/flatset/col/1/2`)
is only used to know that `fMer` is differentiable, so that `pd j` (a `fderiv`) is the partial
derivative; the termwise differentiation of the lattice sum is proved here (Gaussian majorants of
`Bounds.lean`, `hasDerivAt_tsum_of_isPreconnected` along the lines `q ↦ (q, η)` and `η ↦ (q, η)`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem cOf_pos' {ν : ℝ} (hν : 0 < ν) : 0 < cOf ν := by
  unfold cOf; positivity

theorem ageA_pos' {ν s : ℝ} (hν : 0 < ν) (hs : 0 < s) : 0 < ageA ν s := by
  unfold ageA; nlinarith [mul_pos hν hs]

/-- Summability of a lattice sum of a function with the Gaussian polynomial bound. -/
theorem lat_summ (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (K : ℝ) (hK : 0 ≤ K) (q η : ℝ)
    (f : ℝ → ℝ → ℝ) (hf : ∀ u v : ℝ, |f u v| ≤ K * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4) :
    Summable (fun j : ℤ => f (q - (j : ℝ) * c) η) := by
  obtain ⟨ub, hub, hbd⟩ := lat_bound a c ha hc K hK 4 q |η|
  refine Summable.of_norm_bounded hub (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact (hf _ _).trans (hbd q η j (by simp) le_rfl)

theorem Vj_mk (ν s : ℝ) (j : ℤ) (q η : ℝ) :
    Vj ν s j (q, η) = (ftPh (ageA ν s) (q - (j : ℝ) * cOf ν) η * (-η),
      ftPh (ageA ν s) (q - (j : ℝ) * cOf ν) η * (q - (j : ℝ) * cOf ν)) := by
  unfold Vj ftPh sq2 xj Jrot
  simp [Prod.smul_mk]

theorem fTerm_mk (ν s : ℝ) (B : Mat3) (j : ℤ) (q η : ℝ) :
    fTerm ν s B j (q, η) = (ftF1 (ageA ν s) B (q - (j : ℝ) * cOf ν) η,
      ftF2 (ageA ν s) B (q - (j : ℝ) * cOf ν) η) :=
  ft_fTerm_closed ν s B j (q, η)

theorem mv_apply' (A : Mat3) (v : Vec3) (i : Fin 3) : mv A v i = ∑ j, A i j * v j := rfl

/-- The three coordinates of the vector-valued term. -/
theorem fpGT_coords (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) (j : ℤ) :
    let T : Vec3 := emb (fderiv ℝ (Vj ν s j) x (merApply (Bmat ν μ χ A s) (xj ν j x)))
      + mv (Bmat ν μ χ A s) (emb (Vj ν s j x))
    T 0 = (fTerm ν s (Bmat ν μ χ A s) j x).1 ∧ T 2 = (fTerm ν s (Bmat ν μ χ A s) j x).2 ∧
    T 1 = Bmat ν μ χ A s 1 0 * (Vj ν s j x).1 + Bmat ν μ χ A s 1 2 * (Vj ν s j x).2 := by
  intro T
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [T, Pi.add_apply, mv_apply']
    simp [fTerm, emb, merApply, Fin.sum_univ_three]

theorem fMer_components (ν μ : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (hν : 0 < ν) (hs : 0 < s)
    (q η : ℝ) :
    fMer ν μ χ A s 0 (q, η) =
        -∑' j : ℤ, ftF1 (ageA ν s) (Bmat ν μ χ A s) (q - (j : ℝ) * cOf ν) η ∧
    fMer ν μ χ A s 1 (q, η) =
        -∑' j : ℤ, ftF2 (ageA ν s) (Bmat ν μ χ A s) (q - (j : ℝ) * cOf ν) η := by
  set a := ageA ν s with ha_def
  set B := Bmat ν μ χ A s with hB
  have ha : 0 < a := ageA_pos' hν hs
  have hc : 0 < cOf ν := cOf_pos' hν
  set T : ℤ → Vec3 := fun j => emb (fderiv ℝ (Vj ν s j) (q, η) (merApply B (xj ν j (q, η))))
      + mv B (emb (Vj ν s j (q, η))) with hT
  obtain ⟨K, hK0, hK⟩ := pb_all a ha B
  have s1 : Summable (fun j : ℤ => ftF1 a B (q - (j : ℝ) * cOf ν) η) :=
    lat_summ a (cOf ν) ha hc K hK0 q η (ftF1 a B) (fun u v => (hK u v).1)
  have s2 : Summable (fun j : ℤ => ftF2 a B (q - (j : ℝ) * cOf ν) η) :=
    lat_summ a (cOf ν) ha hc K hK0 q η (ftF2 a B) (fun u v => (hK u v).2.1)
  have pu : Summable (fun j : ℤ => ftPh a (q - (j : ℝ) * cOf ν) η * (q - (j : ℝ) * cOf ν)) :=
    lat_summ a (cOf ν) ha hc 1 zero_le_one q η (fun u v => ftPh a u v * u) (fun u v => by
      obtain ⟨h1, hu, hv⟩ := pb_w u v
      have hph := ftPh_pos a u v ha
      rw [abs_mul, abs_of_pos hph]
      have : (1 + u ^ 2 + v ^ 2) ≤ (1 + u ^ 2 + v ^ 2) ^ 4 := by
        simpa using pow_le_pow_right₀ h1 (show 1 ≤ 4 by norm_num)
      calc ftPh a u v * |u| ≤ ftPh a u v * (1 + u ^ 2 + v ^ 2) :=
            mul_le_mul_of_nonneg_left hu hph.le
        _ ≤ ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4 := mul_le_mul_of_nonneg_left this hph.le
        _ = 1 * ftPh a u v * (1 + u ^ 2 + v ^ 2) ^ 4 := by ring)
  have pv : Summable (fun j : ℤ => ftPh a (q - (j : ℝ) * cOf ν) η * (-η)) := by
    have hh : Summable (fun j : ℤ => ftPh a (q - (j : ℝ) * cOf ν) η) :=
      lat_summ a (cOf ν) ha hc 1 zero_le_one q η (fun u v => ftPh a u v) (fun u v => by
        obtain ⟨h1, hu, hv⟩ := pb_w u v
        have hph := ftPh_pos a u v ha
        rw [abs_of_pos hph]
        have : 1 ≤ (1 + u ^ 2 + v ^ 2) ^ 4 := one_le_pow₀ h1
        nlinarith)
    exact hh.mul_right _
  have c0 : ∀ j, T j 0 = ftF1 a B (q - (j : ℝ) * cOf ν) η := fun j => by
    have := (fpGT_coords ν μ χ A s (q, η) j).1
    rw [fTerm_mk] at this
    exact this
  have c2 : ∀ j, T j 2 = ftF2 a B (q - (j : ℝ) * cOf ν) η := fun j => by
    have := (fpGT_coords ν μ χ A s (q, η) j).2.1
    rw [fTerm_mk] at this
    exact this
  have c1 : ∀ j, T j 1 = B 1 0 * (ftPh a (q - (j : ℝ) * cOf ν) η * (-η)) +
      B 1 2 * (ftPh a (q - (j : ℝ) * cOf ν) η * (q - (j : ℝ) * cOf ν)) := fun j => by
    have := (fpGT_coords ν μ χ A s (q, η) j).2.2
    rw [Vj_mk] at this
    exact this
  have hTs : Summable T := by
    refine Pi.summable.2 (fun k => ?_)
    fin_cases k
    · show Summable (fun j => T j 0)
      simpa only [c0] using s1
    · show Summable (fun j => T j 1)
      simp only [c1]
      exact (pv.mul_left _).add (pu.mul_left _)
    · show Summable (fun j => T j 2)
      simpa only [c2] using s2
  have hfA : fA ν μ χ A s (q, η) = -(∑' j, T j) := rfl
  have e0 : fMer ν μ χ A s 0 (q, η) = -∑' j, T j 0 := by
    unfold fMer merOf
    rw [hfA, ← tsum_apply hTs]
    simp
  have e1 : fMer ν μ χ A s 1 (q, η) = -∑' j, T j 2 := by
    unfold fMer merOf
    rw [hfA, ← tsum_apply hTs]
    simp
  refine ⟨?_, ?_⟩
  · rw [e0]; simp only [c0]
  · rw [e1]; simp only [c2]


theorem tsum_hasDerivAt_q (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (B : Mat3) (q η : ℝ) :
    HasDerivAt (fun q' : ℝ => ∑' j : ℤ, ftF2 a B (q' - (j : ℝ) * c) η)
      (∑' j : ℤ, ftD2 a B (q - (j : ℝ) * c) η) q := by
  obtain ⟨K, hK0, hK⟩ := pb_all a ha B
  obtain ⟨ub, hub, hbd⟩ := lat_bound a c ha hc K hK0 4 q |η|
  refine hasDerivAt_tsum_of_isPreconnected (g := fun (j : ℤ) q' => ftF2 a B (q' - (j : ℝ) * c) η)
    (g' := fun (j : ℤ) q' => ftD2 a B (q' - (j : ℝ) * c) η) (t := Metric.ball q 1) (y₀ := q) (y := q)
    hub Metric.isOpen_ball (convex_ball q 1).isPreconnected ?_ ?_ (Metric.mem_ball_self one_pos)
    (lat_summ a c ha hc K hK0 q η (ftF2 a B) (fun u v => (hK u v).2.1))
    (Metric.mem_ball_self one_pos)
  · intro j y _
    exact (ft_hasDerivAt_F2_u a B (y - (j : ℝ) * c) η).comp_sub_const y ((j : ℝ) * c)
  · intro j y hy
    rw [Real.norm_eq_abs]
    exact (hK _ _).2.2.2.trans
      (hbd y η j (by simpa [Metric.mem_ball, Real.dist_eq] using hy) le_rfl)

theorem tsum_hasDerivAt_eta (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (B : Mat3) (q η : ℝ) :
    HasDerivAt (fun η' : ℝ => ∑' j : ℤ, ftF1 a B (q - (j : ℝ) * c) η')
      (∑' j : ℤ, ftD1 a B (q - (j : ℝ) * c) η) η := by
  obtain ⟨K, hK0, hK⟩ := pb_all a ha B
  obtain ⟨ub, hub, hbd⟩ := lat_bound a c ha hc K hK0 4 q (|η| + 1)
  refine hasDerivAt_tsum_of_isPreconnected (g := fun (j : ℤ) η' => ftF1 a B (q - (j : ℝ) * c) η')
    (g' := fun (j : ℤ) η' => ftD1 a B (q - (j : ℝ) * c) η') (t := Metric.ball η 1) (y₀ := η) (y := η)
    hub Metric.isOpen_ball (convex_ball η 1).isPreconnected ?_ ?_ (Metric.mem_ball_self one_pos)
    (lat_summ a c ha hc K hK0 q η (ftF1 a B) (fun u v => (hK u v).1))
    (Metric.mem_ball_self one_pos)
  · intro j y _
    exact ft_hasDerivAt_F1_v a B (q - (j : ℝ) * c) y
  · intro j y hy
    rw [Real.norm_eq_abs]
    have hy' : |y - η| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hy
    have : |y| ≤ |η| + 1 := by
      have := abs_sub_abs_le_abs_sub y η
      linarith
    exact (hK _ _).2.2.1.trans (hbd q y j (by simp) this)

/-- **`FlatForceCurlTsum` from the smoothness of `f_A`** (source 4597-4608, 4963-4976). -/
theorem flatForceCurlTsum_of (hsm : FlatForceSmooth) : FlatForceCurlTsum := by
  intro ν μ χ A s hν hs x
  obtain ⟨q, η⟩ := x
  set a := ageA ν s with ha_def
  set B := Bmat ν μ χ A s with hB
  have ha : 0 < a := ageA_pos' hν hs
  have hc : 0 < cOf ν := cOf_pos' hν
  have d0 : Differentiable ℝ (fMer ν μ χ A s 0) :=
    (hsm ν μ χ A s hν hs 0).differentiable (by simp)
  have d1 : Differentiable ℝ (fMer ν μ χ A s 1) :=
    (hsm ν μ χ A s hν hs 1).differentiable (by simp)
  have h1 := B0579.hasDerivAt_fst d1 q η
  have h0 := B0579.hasDerivAt_snd d0 q η
  have e1 : (fun t : ℝ => fMer ν μ χ A s 1 (t, η)) =
      fun t : ℝ => -∑' j : ℤ, ftF2 a B (t - (j : ℝ) * cOf ν) η := by
    funext t; exact (fMer_components ν μ χ A s hν hs t η).2
  have e0 : (fun t : ℝ => fMer ν μ χ A s 0 (q, t)) =
      fun t : ℝ => -∑' j : ℤ, ftF1 a B (q - (j : ℝ) * cOf ν) t := by
    funext t; exact (fMer_components ν μ χ A s hν hs q t).1
  rw [e1] at h1
  rw [e0] at h0
  have u1 := h1.unique (tsum_hasDerivAt_q a (cOf ν) ha hc B q η).neg
  have u0 := h0.unique (tsum_hasDerivAt_eta a (cOf ν) ha hc B q η).neg
  obtain ⟨K, hK0, hK⟩ := pb_all a ha B
  have sD2 := lat_summ a (cOf ν) ha hc K hK0 q η (ftD2 a B) (fun u v => (hK u v).2.2.2)
  have sD1 := lat_summ a (cOf ν) ha hc K hK0 q η (ftD1 a B) (fun u v => (hK u v).2.2.1)
  have hsum : ∑' j : ℤ, curlTermProf a B (xj ν j (q, η)) =
      ∑' j : ℤ, ftD2 a B (q - (j : ℝ) * cOf ν) η - ∑' j : ℤ, ftD1 a B (q - (j : ℝ) * cOf ν) η := by
    rw [← Summable.tsum_sub sD2 sD1]
    congr 1
    funext j
    exact (ft_curl_key a ha.ne' B (q - (j : ℝ) * cOf ν) η).symm
  rw [u1, u0, hsum]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
