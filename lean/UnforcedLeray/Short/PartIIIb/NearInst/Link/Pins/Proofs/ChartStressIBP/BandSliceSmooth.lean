import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_2

/-!
# `BandSliceSmooth` (task `PartIII-b:C/near/pins/4/2/1`)

Source `the November 2 reference manuscript` 1660-1665 (band support of the tensor
test `M`), 2666-2668 (chart `chartOf`), 2683 (lift `cartLift`).

Plan. Off the axis, `cartLift` is a smooth expression in the Cartesian point `y` and the profile
values `M(s, q, η)` of the raw chart point `ptOf R τ y`, the reduction of `q` into a cell being
removed by `c`-periodicity of `M` (`nsSym_shift`). Near the axis (`hRad y < δ`) the slice vanishes
identically, because the band `[s₀, s₁]` of `M` is then never reached. The support lies in a closed
ball, by the band bounds on `s` and `η`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory Set Filter Topology
open UnforcedLeray.Short.PartIIIb.Concrete

/-- The raw similarity chart point of `(y, τ)`, before the reduction of `q` into a cell
(source 2666-2668, the expression of `chartOf` without the reduction). -/
def ptOf (R τ : ℝ) (y : Space) : Chart :=
  (R ^ 2 / hRad y ^ 2, R * Real.log (hRad y / R) + R * τ / 2, R * y 2 / hRad y)

/-- `nsSym` depends on the tensor only through the four components of `tv4`. -/
theorem nsSym_of_tv4_eq {A B : Ten3} (h : tv4 A = tv4 B) : nsSym A = nsSym B := by
  have h0 := congrArg (fun v => v 0) h
  have h1 := congrArg (fun v => v 1) h
  have h2 := congrArg (fun v => v 2) h
  have h3 := congrArg (fun v => v 3) h
  simp [tv4] at h0 h1 h2 h3
  unfold nsSym
  rw [h0, h1, h2, h3]

theorem nsSym_zero_of_def {A : Ten3} (h : tv4 A = 0) : nsSym A = 0 := by
  have h' : tv4 A = tv4 (0 : Ten3) := by
    rw [h]
    ext k
    fin_cases k <;> simp [tv4, symRZ]
  rw [nsSym_of_tv4_eq h']
  ext a b
  fin_cases a <;> fin_cases b <;> simp [nsSym, symRZ]

/-- `c`-periodicity of `M` in the `q` variable removes the integer multiple of the period. -/
theorem nsSym_shift {c : ℝ} (M : Chart → Ten3)
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)))
    (s Q η : ℝ) (k : ℤ) :
    nsSym (M (s, Q - c * k, η)) = nsSym (M (s, Q, η)) := by
  apply nsSym_of_tv4_eq
  have hp : Function.Periodic (fun q : ℝ => tv4 (M (s, q, η))) c :=
    fun x => hM.periodic (s, x, η)
  have h2 := hp.sub_int_mul_eq (x := Q) k
  rw [mul_comm c]
  exact h2

theorem tv4_re_contDiff {c : ℝ} (M : Chart → Ten3)
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x))) (k : Fin 4) :
    ContDiff ℝ 1 (fun p : Chart => ((tv4 (M p)) k).re) := by
  have h1 : ContDiff ℝ 1 (fun p : Chart => (tv4 (M p)) k) :=
    ((contDiff_piLp (p := 2)).mp hM.smooth k).of_le (by simp)
  exact Complex.reCLM.contDiff.comp h1

theorem nsSym_entry_contDiff {c : ℝ} (M : Chart → Ten3)
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x))) (a b : Fin 3) :
    ContDiff ℝ 1 (fun p : Chart => nsSym (M p) a b) := by
  have e0 : (fun p : Chart => M p (0, 0)) = fun p => ((tv4 (M p)) 0).re := by
    funext p; simp [tv4]
  have e1 : (fun p : Chart => symRZ (M p)) = fun p => ((tv4 (M p)) 1).re := by
    funext p; simp [tv4]
  have e2 : (fun p : Chart => M p (2, 2)) = fun p => ((tv4 (M p)) 2).re := by
    funext p; simp [tv4]
  have e3 : (fun p : Chart => M p (1, 1)) = fun p => ((tv4 (M p)) 3).re := by
    funext p; simp [tv4]
  have h0 : ContDiff ℝ 1 (fun p : Chart => M p (0, 0)) := by
    rw [e0]; exact tv4_re_contDiff M hM 0
  have h1 : ContDiff ℝ 1 (fun p : Chart => symRZ (M p)) := by
    rw [e1]; exact tv4_re_contDiff M hM 1
  have h2 : ContDiff ℝ 1 (fun p : Chart => M p (2, 2)) := by
    rw [e2]; exact tv4_re_contDiff M hM 2
  have h3 : ContDiff ℝ 1 (fun p : Chart => M p (1, 1)) := by
    rw [e3]; exact tv4_re_contDiff M hM 3
  fin_cases a <;> fin_cases b <;> simp [nsSym] <;>
    first | exact contDiff_const | exact h0 | exact h1 | exact h2 | exact h3

theorem hRad_contDiffAt_pos {y : Space} (hy : 0 < hRad y) :
    ContDiffAt ℝ 1 (fun z : Space => hRad z) y := by
  have hy0 : ∀ k : Fin 3, ContDiff ℝ 1 (fun z : Space => z k) := fun k =>
    (contDiff_piLp (p := 2)).mp contDiff_id k
  have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 := Real.sqrt_pos.mp hy
  have hsq : ContDiffAt ℝ 1 (fun z : Space => z 0 ^ 2 + z 1 ^ 2) y :=
    ((hy0 0).contDiffAt.pow 2).add ((hy0 1).contDiffAt.pow 2)
  exact hsq.sqrt hpos.ne'

theorem ptOf_contDiffAt {R τ : ℝ} (hR : 0 < R) {y : Space} (hy : 0 < hRad y) :
    ContDiffAt ℝ 1 (fun z : Space => ptOf R τ z) y := by
  have hy0 : ∀ k : Fin 3, ContDiff ℝ 1 (fun z : Space => z k) := fun k =>
    (contDiff_piLp (p := 2)).mp contDiff_id k
  have hRC := hRad_contDiffAt_pos hy
  have hs : ContDiffAt ℝ 1 (fun z : Space => R ^ 2 / hRad z ^ 2) y :=
    contDiffAt_const.div (hRC.pow 2) (pow_ne_zero 2 hy.ne')
  have hQ : ContDiffAt ℝ 1 (fun z : Space => R * Real.log (hRad z / R) + R * τ / 2) y :=
    ((contDiffAt_const.mul ((hRC.div_const R).log (div_ne_zero hy.ne' hR.ne'))).add
      contDiffAt_const)
  have hη : ContDiffAt ℝ 1 (fun z : Space => R * z 2 / hRad z) y :=
    (contDiffAt_const.mul (hy0 2).contDiffAt).div hRC hy.ne'
  exact hs.prodMk (hQ.prodMk hη)

theorem cylFrame_entry_contDiffAt {y : Space} (hy : 0 < hRad y) (a b : Fin 3) :
    ContDiffAt ℝ 1 (fun z : Space => cylFrame z a b) y := by
  have hy0 : ∀ k : Fin 3, ContDiff ℝ 1 (fun z : Space => z k) := fun k =>
    (contDiff_piLp (p := 2)).mp contDiff_id k
  have hRC := hRad_contDiffAt_pos hy
  fin_cases a <;> fin_cases b <;> simp [cylFrame] <;>
    first
    | exact contDiffAt_const
    | exact (hy0 0).contDiffAt.div hRC hy.ne'
    | exact (hy0 1).contDiffAt.div hRC hy.ne'
    | exact ((hy0 1).contDiffAt.div hRC hy.ne').neg

theorem contDiffAt_sandwich {C N : Space → Matrix (Fin 3) (Fin 3) ℝ} {s : Space → ℝ}
    {y : Space} (i j : Fin 3)
    (hC : ∀ a b : Fin 3, ContDiffAt ℝ 1 (fun z => C z a b) y)
    (hN : ∀ a b : Fin 3, ContDiffAt ℝ 1 (fun z => N z a b) y)
    (hs : ContDiffAt ℝ 1 s y) :
    ContDiffAt ℝ 1 (fun z => (C z * ((s z) • N z) * (C z).transpose) i j) y := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  refine ContDiffAt.sum fun k _ => ?_
  refine ContDiffAt.mul ?_ (hC j k)
  refine ContDiffAt.sum fun l _ => ?_
  exact (hC i l).mul (hs.mul (hN l k))

/-- The formula for the lift off the reduction: `cartLift` at `(y, τ)` only sees `M` at the
raw point `ptOf R τ y`. -/
theorem strPhys_eq_sandwich (R c τ : ℝ)
    (M : Chart → Ten3)
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x))) (y : Space) :
    strPhys R c M (τ, y) = cylFrame y * ((R ^ 2 / hRad y ^ 2) • nsSym (M (ptOf R τ y)))
      * (cylFrame y).transpose := by
  have hs := nsSym_shift (c := c) M hM (R ^ 2 / hRad y ^ 2)
    (R * Real.log (hRad y / R) + R * τ / 2) (R * y 2 / hRad y)
    ⌊(R * Real.log (hRad y / R) + R * τ / 2) / c + 1 / 2⌋
  have hs' : nsSym (M (chartOf R c y τ)) = nsSym (M (ptOf R τ y)) := hs
  show cylFrame y * ((chartOf R c y τ).1 • nsSym (M (chartOf R c y τ))) * (cylFrame y).transpose
    = cylFrame y * ((R ^ 2 / hRad y ^ 2) • nsSym (M (ptOf R τ y))) * (cylFrame y).transpose
  rw [hs']
  rfl

theorem bandSliceSmooth : BandSliceSmooth := by
  unfold BandSliceSmooth
  intro c ε hc hε M hM τ i j
  obtain ⟨s0, s1, L, hs0, hband⟩ := hM.band
  have hR : 0 < ε⁻¹ := inv_pos.mpr hε
  set R : ℝ := ε⁻¹ with hRdef
  -- the slice vanishes whenever the raw point leaves the band
  have hzero : ∀ y : Space,
      ¬ (s0 ≤ R ^ 2 / hRad y ^ 2 ∧ R ^ 2 / hRad y ^ 2 ≤ s1 ∧ |R * y 2 / hRad y| ≤ L) →
        strPhys R c M (τ, y) i j = 0 := by
    intro y hy
    have hN : nsSym (M (ptOf R τ y)) = 0 := by
      apply nsSym_zero_of_def
      by_contra hne
      have hb := hband (ptOf R τ y) hne
      exact hy ⟨hb.1.1, hb.1.2, hb.2⟩
    rw [strPhys_eq_sandwich R c τ M hM y, hN]
    simp
  -- the neighbourhood of the axis where the slice vanishes
  set δ : ℝ := R / (1 + |s1|) with hδ
  have hA : 0 < 1 + |s1| := by positivity
  have hδpos : 0 < δ := by positivity
  have zero_small : ∀ z : Space, hRad z < δ → strPhys R c M (τ, z) i j = 0 := by
    intro z hz
    apply hzero z
    rintro ⟨h1, h2, _⟩
    have hnn : 0 ≤ hRad z := Real.sqrt_nonneg _
    rcases hnn.eq_or_lt with h0 | hpos
    · have hz0 : R ^ 2 / hRad z ^ 2 = 0 := by
        rw [← h0]; simp
      rw [hz0] at h1
      linarith
    · have hlt1 : (hRad z) * (1 + |s1|) < R := (lt_div_iff₀ hA).mp hz
      have hh2 : 0 < hRad z ^ 2 := by positivity
      have e1 : s1 * hRad z ^ 2 ≤ (1 + |s1|) * hRad z ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hh2.le
        linarith [le_abs_self s1, abs_nonneg s1]
      have e2 : (1 + |s1|) * hRad z ^ 2 ≤ ((1 + |s1|) * hRad z) ^ 2 := by
        nlinarith [abs_nonneg s1]
      have e3 : ((1 + |s1|) * hRad z) ^ 2 < R ^ 2 := by
        have hp0 : 0 < (1 + |s1|) * hRad z := by positivity
        nlinarith
      have hlt : s1 < R ^ 2 / hRad z ^ 2 := by
        rw [lt_div_iff₀ hh2]
        linarith
      linarith
  -- smoothness
  have hfun : (fun y : Space => strPhys R c M (τ, y) i j) =
      fun y => (cylFrame y * ((R ^ 2 / hRad y ^ 2) • nsSym (M (ptOf R τ y))) *
        (cylFrame y).transpose) i j := by
    funext y
    rw [strPhys_eq_sandwich R c τ M hM y]
  have hsmooth : ContDiff ℝ 1 (fun y : Space => strPhys R c M (τ, y) i j) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : 0 < hRad y
    · rw [hfun]
      have hs : ContDiffAt ℝ 1 (fun z : Space => R ^ 2 / hRad z ^ 2) y :=
        contDiffAt_const.div ((hRad_contDiffAt_pos hy).pow 2) (pow_ne_zero 2 hy.ne')
      exact contDiffAt_sandwich (C := fun z => cylFrame z)
        (N := fun z => nsSym (M (ptOf R τ z))) (s := fun z => R ^ 2 / hRad z ^ 2) i j
        (fun a b => cylFrame_entry_contDiffAt hy a b)
        (fun a b => (nsSym_entry_contDiff M hM a b).comp_contDiffAt y
          (ptOf_contDiffAt hR hy))
        hs
    · have hnn : 0 ≤ hRad y := Real.sqrt_nonneg _
      have hlt : hRad y < δ := by
        have h0 : hRad y = 0 := le_antisymm (not_lt.mp hy) hnn
        rw [h0]; exact hδpos
      have hRc : Continuous (fun z : Space => hRad z) := by
        unfold hRad; fun_prop
      have hev : ∀ᶠ z in 𝓝 y, hRad z < δ :=
        hRc.continuousAt.eventually_lt continuousAt_const hlt
      have hev2 : ∀ᶠ z in 𝓝 y, strPhys R c M (τ, z) i j = 0 :=
        hev.mono fun z hz => zero_small z hz
      exact contDiffAt_const.congr_of_eventuallyEq hev2
  -- support
  have hcompact : HasCompactSupport (fun y : Space => strPhys R c M (τ, y) i j) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) (Real.sqrt ((R ^ 2 + L ^ 2) / s0)))
    intro z hz
    apply hzero z
    rintro ⟨h1, _, h3⟩
    apply hz
    rw [mem_closedBall_zero_iff]
    have hnn : 0 ≤ hRad z := Real.sqrt_nonneg _
    have hpos : 0 < hRad z := by
      rcases hnn.eq_or_lt with h0 | hp
      · have hz0 : R ^ 2 / hRad z ^ 2 = 0 := by
          rw [← h0]; simp
        rw [hz0] at h1
        linarith
      · exact hp
    have hh : hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
      unfold hRad
      rw [Real.sq_sqrt (by positivity)]
    have h5 : s0 * hRad z ^ 2 ≤ R ^ 2 := (le_div_iff₀ (by positivity)).mp h1
    have h3' : |R * z 2 / hRad z| ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at h3'
    have h4 : R ^ 2 * z 2 ^ 2 ≤ L ^ 2 * hRad z ^ 2 := by
      have hdiv : (R * z 2 / hRad z) ^ 2 * hRad z ^ 2 = R ^ 2 * z 2 ^ 2 := by
        field_simp
      have := mul_le_mul_of_nonneg_right h3' (sq_nonneg (hRad z))
      nlinarith
    have h6 : R ^ 2 * (s0 * z 2 ^ 2) ≤ R ^ 2 * L ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h4 hs0.le, mul_le_mul_of_nonneg_left h5 (sq_nonneg L)]
    have h7 : s0 * z 2 ^ 2 ≤ L ^ 2 := le_of_mul_le_mul_left h6 (by positivity)
    have hz2 : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    have hfin : ‖z‖ ^ 2 ≤ (R ^ 2 + L ^ 2) / s0 := by
      rw [hz2, le_div_iff₀ hs0]
      nlinarith
    calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
      _ ≤ Real.sqrt ((R ^ 2 + L ^ 2) / s0) := Real.sqrt_le_sqrt hfin
  -- positivity of the radius on the support
  have hpos : ∀ y : Space, strPhys R c M (τ, y) i j ≠ 0 → 0 < hRad y := by
    intro y hy
    by_contra hle
    apply hy
    apply hzero y
    rintro ⟨h1, _, _⟩
    have h0 : hRad y = 0 := le_antisymm (not_lt.mp hle) (Real.sqrt_nonneg _)
    have hz0 : R ^ 2 / hRad y ^ 2 = 0 := by
      rw [h0]; simp
    rw [hz0] at h1
    linarith
  exact ⟨hsmooth, hcompact, hpos⟩

end UnforcedLeray.Short.PartIIIb.NearInst
