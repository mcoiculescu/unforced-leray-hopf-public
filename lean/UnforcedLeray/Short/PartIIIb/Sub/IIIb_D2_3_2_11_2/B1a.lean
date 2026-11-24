import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2_11_2.A

/-!
# `oldPhysSmooth_proved` (`PartIII-b:IIIb-D2/3/2/11/2/2/1`, source 3604-3621, 4161-4186)

The physical old source `oldPhys R c g` of smooth old data is jointly `C^∞` in `(τ, z)` and
vanishes for `‖z‖` large.  The chart map `chartOf` has floor jumps only where the phase argument
`fArg` is an integer; there `chartOf` lands on the seam `|q.2.1| = c/2`, outside a `δ`-neighbourhood
of `tsupport g`.  On the axis (`ϱ = 0`) and at the seam the source vanishes near the point; elsewhere
the floor is locally constant and the lift is a smooth branch composed with the smooth `g`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

local notation "CT" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The floor argument of `NearInst.chartOf`. -/
def oldSmFArg (R c : ℝ) (p : ℝ × Space) : ℝ :=
  (R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2) / c + 1 / 2

/-- The chart point on the floor branch `n`. -/
def oldSmBranch (R c : ℝ) (n : ℤ) (p : ℝ × Space) : Chart :=
  (R ^ 2 / NearInst.hRad p.2 ^ 2,
    (R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2 - c * n, R * p.2 2 / NearInst.hRad p.2))

/-- The lift with a chart map `ψ` in place of `chartOf`. -/
def oldSmLift (g : Chart → Ten3) (ψ : ℝ × Space → Chart) (p : ℝ × Space) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  NearInst.cylFrame p.2 * (((ψ p).1) • NearInst.nsSym (g (ψ p))) * (NearInst.cylFrame p.2).transpose

lemma oldPhys_eq_oldSmLift (R c : ℝ) (g : Chart → Ten3) (p : ℝ × Space) :
    oldPhys R c g p.1 p.2 = oldSmLift g (fun q => NearInst.chartOf R c q.2 q.1) p := rfl

lemma chartOf_eq_oldSmBranch (R c : ℝ) (n : ℤ) (p : ℝ × Space) (hn : ⌊oldSmFArg R c p⌋ = n) :
    NearInst.chartOf R c p.2 p.1 = oldSmBranch R c n p := by
  subst hn
  unfold NearInst.chartOf oldSmBranch oldSmFArg
  rfl

lemma oldSm_int_half (k : ℤ) : (1 / 2 : ℝ) ≤ |(k : ℝ) + 1 / 2| := by
  rcases le_or_gt 0 k with hk | hk
  · have h0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith [le_abs_self ((k : ℝ) + 1 / 2)]
  · have h1 : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    linarith [neg_abs_le ((k : ℝ) + 1 / 2)]

lemma oldSm_hRad_contDiffAt (p : ℝ × Space) (hH : NearInst.hRad p.2 ≠ 0) :
    ContDiffAt ℝ CT (fun q : ℝ × Space => NearInst.hRad q.2) p := by
  have hpos : 0 < p.2 0 ^ 2 + p.2 1 ^ 2 := Real.sqrt_ne_zero'.1 hH
  unfold NearInst.hRad
  exact ContDiffAt.sqrt (by fun_prop) hpos.ne'

lemma oldSm_fArg_contDiffAt {R c : ℝ} (hR : R ≠ 0) (hc : c ≠ 0) (p : ℝ × Space)
    (hH : NearInst.hRad p.2 ≠ 0) :
    ContDiffAt ℝ CT (fun q : ℝ × Space => oldSmFArg R c q) p := by
  have hHc := oldSm_hRad_contDiffAt p hH
  have hHR : NearInst.hRad p.2 / R ≠ 0 := div_ne_zero hH hR
  unfold oldSmFArg
  have hlog : ContDiffAt ℝ CT (fun q : ℝ × Space => Real.log (NearInst.hRad q.2 / R)) p :=
    ContDiffAt.log (hHc.div_const R) hHR
  have hsum : ContDiffAt ℝ CT
      (fun q : ℝ × Space => R * Real.log (NearInst.hRad q.2 / R) + R * q.1 / 2) p :=
    (contDiffAt_const.mul hlog).add ((contDiffAt_const.mul contDiffAt_fst).div_const 2)
  exact ((hsum.div_const c).add contDiffAt_const)

lemma oldSm_branch_contDiffAt {R c : ℝ} (hR : R ≠ 0) (n : ℤ) (p : ℝ × Space)
    (hH : NearInst.hRad p.2 ≠ 0) :
    ContDiffAt ℝ CT (oldSmBranch R c n) p := by
  have hHc := oldSm_hRad_contDiffAt p hH
  have hHR : NearInst.hRad p.2 / R ≠ 0 := div_ne_zero hH hR
  have hlog : ContDiffAt ℝ CT (fun q : ℝ × Space => Real.log (NearInst.hRad q.2 / R)) p :=
    ContDiffAt.log (hHc.div_const R) hHR
  have hA : ContDiffAt ℝ CT
      (fun q : ℝ × Space => R * Real.log (NearInst.hRad q.2 / R) + R * q.1 / 2 - c * (n : ℝ)) p :=
    ((contDiffAt_const.mul hlog).add ((contDiffAt_const.mul contDiffAt_fst).div_const 2)).sub
      contDiffAt_const
  unfold oldSmBranch
  refine ContDiffAt.prodMk ?_ (ContDiffAt.prodMk hA ?_)
  · exact contDiffAt_const.div (hHc.pow 2) (pow_ne_zero 2 hH)
  · have hz2 : ContDiffAt ℝ CT (fun q : ℝ × Space => q.2 2) p := by fun_prop
    exact ((contDiffAt_const.mul hz2).div hHc hH)

lemma oldSm_lift_entry_contDiffAt {g : Chart → Ten3} (hg : ContDiff ℝ CT g)
    {ψ : ℝ × Space → Chart} {p : ℝ × Space} (hψ : ContDiffAt ℝ CT ψ p)
    (hH : NearInst.hRad p.2 ≠ 0) (i j : Fin 3) :
    ContDiffAt ℝ CT (fun q => oldSmLift g ψ q i j) p := by
  have hHc := oldSm_hRad_contDiffAt p hH
  have hgψ : ContDiffAt ℝ CT (fun q => g (ψ q)) p := hg.contDiffAt.comp p hψ
  have hev : ∀ ab : Fin 3 × Fin 3, ContDiffAt ℝ CT (fun q => g (ψ q) ab) p := fun ab =>
    (EuclideanSpace.proj ab : Ten3 →L[ℝ] ℝ).contDiff.contDiffAt.comp p hgψ
  have hcyl : ∀ a b : Fin 3,
      ContDiffAt ℝ CT (fun q : ℝ × Space => NearInst.cylFrame q.2 a b) p := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [NearInst.cylFrame] <;>
      first
      | exact contDiffAt_const
      | exact (hHc.const_mul (1 : ℝ)).div_const 1 |>.mul contDiffAt_const
      | fun_prop (disch := assumption)
  have hn : ∀ a b : Fin 3,
      ContDiffAt ℝ CT (fun q => NearInst.nsSym (g (ψ q)) a b) p := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;>
      first
      | exact contDiffAt_const
      | exact hev _
      | exact ((hev _).add (hev _)).div_const 2
  have hs : ContDiffAt ℝ CT (fun q => (ψ q).1) p := hψ.fst
  unfold oldSmLift
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  fun_prop (disch := assumption)

lemma oldSm_contDiffAt_of_eventually_zero {F : ℝ × Space → ℝ} {p0 : ℝ × Space}
    (h : ∀ᶠ q in 𝓝 p0, F q = 0) : ContDiffAt ℝ CT F p0 :=
  (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h

lemma oldSm_zero_of_notMem (R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (z : Space)
    (h : NearInst.chartOf R c z τ ∉ tsupport g) : oldPhys R c g τ z = 0 := by
  simp [oldPhys, NearInst.cartLift, image_eq_zero_of_notMem_tsupport h, nsSym_zero]

lemma oldSm_delta {c : ℝ} {g : Chart → Ten3} (hg : IsSmoothChart c g) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ tsupport g, |q.2.1| ≤ c / 2 - δ := by
  rcases (tsupport g).eq_empty_or_nonempty with h | hne
  · exact ⟨c / 2, by linarith, fun q hq => by simp [h] at hq⟩
  · obtain ⟨x, hx, hmax⟩ := hg.compact.isCompact.exists_isMaxOn hne
      (by fun_prop : Continuous fun q : Chart => |q.2.1|).continuousOn
    refine ⟨c / 2 - |x.2.1|, ?_, fun q hq => ?_⟩
    · have := (hg.inChart hx).2
      linarith
    · have h1 : |q.2.1| ≤ |x.2.1| := isMaxOn_iff.mp hmax q hq
      linarith

lemma oldSm_axis_eventually {R c B : ℝ} {g : Chart → Ten3} (hR : 0 < R) (hB0 : 0 ≤ B)
    (hg : IsSmoothChart c g) (hB : ∀ q ∈ tsupport g, |q.1| ≤ B) (p0 : ℝ × Space)
    (hH0 : NearInst.hRad p0.2 = 0) :
    ∀ᶠ q in 𝓝 p0, NearInst.chartOf R c q.2 q.1 ∉ tsupport g := by
  have hcont : Continuous (fun q : ℝ × Space => NearInst.hRad q.2 ^ 2) := by
    unfold NearInst.hRad; fun_prop
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have hlt : NearInst.hRad p0.2 ^ 2 < R ^ 2 / (B + 1) := by
    rw [hH0]
    simpa using div_pos (pow_pos hR 2) hB1
  have hev : ∀ᶠ q in 𝓝 p0, NearInst.hRad q.2 ^ 2 < R ^ 2 / (B + 1) :=
    ContinuousAt.eventually_lt hcont.continuousAt continuousAt_const hlt
  filter_upwards [hev] with q hq
  intro hmem
  have hs0 : 0 < (NearInst.chartOf R c q.2 q.1).1 := (hg.inChart hmem).1
  have hsB : (NearInst.chartOf R c q.2 q.1).1 ≤ B := (abs_le.1 (hB _ hmem)).2
  by_cases h2 : NearInst.hRad q.2 ^ 2 = 0
  · have h0 : (NearInst.chartOf R c q.2 q.1).1 = 0 := by
      show R ^ 2 / NearInst.hRad q.2 ^ 2 = 0
      rw [h2, div_zero]
    linarith
  · have hpos : 0 < NearInst.hRad q.2 ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm h2)
    have hq' := (lt_div_iff₀ hB1).1 hq
    have hbig : B + 1 < R ^ 2 / NearInst.hRad q.2 ^ 2 := by
      rw [lt_div_iff₀ hpos]
      nlinarith
    have h3 : (NearInst.chartOf R c q.2 q.1).1 = R ^ 2 / NearInst.hRad q.2 ^ 2 := rfl
    linarith

lemma oldSm_seam_notMem {R c δ : ℝ} {g : Chart → Ten3} (hc : 0 < c) (hδpos : 0 < δ)
    (hδ : ∀ q ∈ tsupport g, |q.2.1| ≤ c / 2 - δ) (n0 : ℤ) (η : ℝ) (hη : c * η = δ / 2)
    (p : ℝ × Space) (hf : |oldSmFArg R c p - (n0 : ℝ)| < η) :
    NearInst.chartOf R c p.2 p.1 ∉ tsupport g := by
  intro hmem
  have h1 := hδ _ hmem
  have hc0 : c ≠ 0 := hc.ne'
  have hcX : c * ((R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2) / c)
      = R * Real.log (NearInst.hRad p.2 / R) + R * p.1 / 2 := mul_div_cancel₀ _ hc0
  have hA : (NearInst.chartOf R c p.2 p.1).2.1
      = c * (oldSmFArg R c p - 1 / 2 - ((⌊oldSmFArg R c p⌋ : ℤ) : ℝ)) := by
    unfold NearInst.chartOf oldSmFArg
    linear_combination (-1 : ℝ) * hcX
  have hk := oldSm_int_half (⌊oldSmFArg R c p⌋ - n0)
  push_cast at hk
  have h2 : |((⌊oldSmFArg R c p⌋ : ℝ) - (n0 : ℝ)) + 1 / 2| - |oldSmFArg R c p - (n0 : ℝ)|
      ≤ |((⌊oldSmFArg R c p⌋ : ℝ) - (n0 : ℝ)) + 1 / 2 - (oldSmFArg R c p - (n0 : ℝ))| :=
    abs_sub_abs_le_abs_sub _ _
  have h2' : ((⌊oldSmFArg R c p⌋ : ℝ) - (n0 : ℝ)) + 1 / 2 - (oldSmFArg R c p - (n0 : ℝ))
      = -(oldSmFArg R c p - 1 / 2 - ((⌊oldSmFArg R c p⌋ : ℤ) : ℝ)) := by ring
  rw [h2', abs_neg] at h2
  have h3 : 1 / 2 - |oldSmFArg R c p - (n0 : ℝ)|
      ≤ |oldSmFArg R c p - 1 / 2 - ((⌊oldSmFArg R c p⌋ : ℤ) : ℝ)| := by linarith
  rw [hA, abs_mul, abs_of_pos hc] at h1
  have h4 : c * (1 / 2 - |oldSmFArg R c p - (n0 : ℝ)|)
      ≤ c * |oldSmFArg R c p - 1 / 2 - ((⌊oldSmFArg R c p⌋ : ℤ) : ℝ)| :=
    mul_le_mul_of_nonneg_left h3 hc.le
  have h5 : c * |oldSmFArg R c p - (n0 : ℝ)| ≤ c * η :=
    mul_le_mul_of_nonneg_left hf.le hc.le
  have h6 : c * (1 / 2 - |oldSmFArg R c p - (n0 : ℝ)|)
      = c / 2 - c * |oldSmFArg R c p - (n0 : ℝ)| := by ring
  linarith

lemma oldPhys_entry_contDiffAt {ν R c : ℝ} {g : Chart → Ten3} (hR : 0 < R) (hc : 0 < c)
    (hg : IsSmoothOld c ν g) (j k : Fin 3) (p0 : ℝ × Space) :
    ContDiffAt ℝ CT (fun x : ℝ × Space => oldPhys R c g x.1 x.2 j k) p0 := by
  obtain ⟨B, hB0, hB⟩ := chart_support_bound hg.chart
  have hB' : ∀ q ∈ tsupport g, |q.1| ≤ B := fun q hq => (hB q hq).1
  have hgc : ContDiff ℝ CT g := hg.chart.smooth
  have hR0 : R ≠ 0 := hR.ne'
  have hc0 : c ≠ 0 := hc.ne'
  by_cases hH0 : NearInst.hRad p0.2 = 0
  · apply oldSm_contDiffAt_of_eventually_zero
    filter_upwards [oldSm_axis_eventually hR hB0 hg.chart hB' p0 hH0] with q hq
    simp [oldSm_zero_of_notMem R c g q.1 q.2 hq]
  · by_cases hint : ∃ n : ℤ, oldSmFArg R c p0 = n
    · obtain ⟨n0, hn0⟩ := hint
      obtain ⟨δ, hδpos, hδ⟩ := oldSm_delta hg.chart hc
      have hη0 : 0 < δ / (2 * c) := div_pos hδpos (by linarith)
      have hη : c * (δ / (2 * c)) = δ / 2 := by field_simp
      have hev : ∀ᶠ q in 𝓝 p0, |oldSmFArg R c q - (n0 : ℝ)| < δ / (2 * c) := by
        have hcont := oldSm_fArg_contDiffAt hR0 hc0 p0 hH0
        have h1 : (n0 : ℝ) - δ / (2 * c) < oldSmFArg R c p0 := by rw [hn0]; linarith
        have h2 : oldSmFArg R c p0 < (n0 : ℝ) + δ / (2 * c) := by rw [hn0]; linarith
        filter_upwards [hcont.continuousAt.tendsto.eventually (Ioo_mem_nhds h1 h2)] with q hq
        rw [abs_sub_lt_iff]
        constructor <;> linarith [hq.1, hq.2]
      apply oldSm_contDiffAt_of_eventually_zero
      filter_upwards [hev] with q hq
      have hnot := oldSm_seam_notMem hc hδpos hδ n0 _ hη q hq
      simp [oldSm_zero_of_notMem R c g q.1 q.2 hnot]
    · push_neg at hint
      have hk1 : ((⌊oldSmFArg R c p0⌋ : ℤ) : ℝ) < oldSmFArg R c p0 :=
        (Int.floor_le _).lt_of_ne (fun h => hint _ h.symm)
      have hk2 : oldSmFArg R c p0 < ((⌊oldSmFArg R c p0⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have hev : ∀ᶠ q in 𝓝 p0, ⌊oldSmFArg R c q⌋ = ⌊oldSmFArg R c p0⌋ := by
        have hcont := oldSm_fArg_contDiffAt hR0 hc0 p0 hH0
        filter_upwards [hcont.continuousAt.tendsto.eventually (Ioo_mem_nhds hk1 hk2)] with q hq
        exact Int.floor_eq_iff.2 ⟨hq.1.le, hq.2⟩
      have hEq : ∀ᶠ q in 𝓝 p0,
          oldSmLift g (fun q => NearInst.chartOf R c q.2 q.1) q j k
            = oldSmLift g (oldSmBranch R c ⌊oldSmFArg R c p0⌋) q j k := by
        filter_upwards [hev] with q hq
        simp only [oldSmLift, chartOf_eq_oldSmBranch R c _ q hq]
      have hψ : ContDiffAt ℝ CT (oldSmBranch R c ⌊oldSmFArg R c p0⌋) p0 :=
        oldSm_branch_contDiffAt hR0 _ p0 hH0
      have hL := oldSm_lift_entry_contDiffAt hgc hψ hH0 j k
      show ContDiffAt ℝ CT (fun x => oldSmLift g (fun q => NearInst.chartOf R c q.2 q.1) x j k) p0
      exact hL.congr_of_eventuallyEq hEq

/-- **`oldPhysSmooth_proved`** (source 3604-3621, 4161-4186). -/
theorem oldPhysSmooth_proved : OldPhysSmooth := by
  intro ν R c g hν hR hc hg
  refine ⟨fun j k => contDiff_iff_contDiffAt.2 fun p0 => oldPhys_entry_contDiffAt hR hc hg j k p0, ?_⟩
  obtain ⟨B, hB0, hB⟩ := chart_support_bound hg.chart
  refine ⟨R * Real.sqrt (5 * ν / 6) + B * (R * Real.sqrt (5 * ν / 6)) / R, fun τ z hz => ?_⟩
  by_contra hne
  exact absurd (oldPhys_ne_zero_bound hR hν hg B hB0 hB τ z hne) (not_le.2 hz)

end UnforcedLeray.Short.PartIIIb.Concrete
