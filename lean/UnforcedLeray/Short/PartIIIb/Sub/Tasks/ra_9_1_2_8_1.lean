import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_9_1_2_8_1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8_1.L5

/-!
# `PartIII-b:C/asrc/ra/9/1/2/8/1` : `geoDcThetaBound`

Source of record: `the November 2 reference manuscript`,
lines 5034-5039, 4979-4980.  The assembly `geoDcThetaBound_of` is applied to the seven scalar lemmas.
The lemmas `dcLocal`, `dcToMer`, `thetaScalSmooth`, `thetaScalDS`, `thetaScalDQQ` come from the imported
files `L1`-`L5`.  The lemmas `thetaScalDEE` and `thetaScalBound` are copied from `L6` and `L7` without their
duplicate helper blocks (those files redeclare the same `fderiv` helpers, so they cannot be imported together).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Product rule for `c` with `∂_w c = 1` (here `c = η`), applied twice. -/
theorem dir_dir_mul_one {U : Set Chart} (hU : IsOpen U) {q : Chart} (hq : q ∈ U) (w : Chart)
    {c G : Chart → ℝ} (hc : ∀ p, DifferentiableAt ℝ c p) (hcw : ∀ p, fderiv ℝ c p w = 1)
    (hG : ContDiffOn ℝ 2 G U) :
    fderiv ℝ (fun p => fderiv ℝ (fun x => c x * G x) p w) q w
      = c q * fderiv ℝ (fun p => fderiv ℝ G p w) q w + 2 * fderiv ℝ G q w := by
  have h1 : (fun p => fderiv ℝ (fun x => c x * G x) p w)
      =ᶠ[nhds q] (fun p => c p * fderiv ℝ G p w + G p) := by
    filter_upwards [hU.mem_nhds hq] with p hp
    show fderiv ℝ (fun x => c x * G x) p w = c p * fderiv ℝ G p w + G p
    rw [fderiv_mul_apply_dir (hc p) (diff_of_C2 hU hG hp), hcw p]
    ring
  have h3 : fderiv ℝ (fun p => fderiv ℝ (fun x => c x * G x) p w) q
      = fderiv ℝ (fun p => c p * fderiv ℝ G p w + G p) q := h1.fderiv_eq
  have hA : DifferentiableAt ℝ (fun p => c p * fderiv ℝ G p w) q :=
    (hc q).mul (dir_diff hU hG w hq)
  have hGq : DifferentiableAt ℝ G q := diff_of_C2 hU hG hq
  rw [h3, show (fun p => c p * fderiv ℝ G p w + G p)
      = (fun p => c p * fderiv ℝ G p w) + G from rfl, fderiv_add hA hGq,
    add_apply, fderiv_mul_apply_dir (hc q) (dir_diff hU hG w hq), hcw q]
  simp only [mul_one]
  ring

/-- **Second `η`-derivative of `(1-𝒦)ψ`** (source 5034-5039, 4979-4980). -/
theorem thetaScalDEE : ThetaScalDEEP := by
  intro ψ q hq hψ
  have hU : IsOpen (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hqU : q ∈ (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := ⟨hq, mem_univ _⟩
  have hψ2 : ContDiffOn ℝ 2 ψ (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hψ.of_le (by norm_num)
  have hF1 : ContDiffOn ℝ 2 (fderiv ℝ ψ) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hψ.fderiv_of_isOpen hU (by norm_num)
  have hS : ContDiffOn ℝ 2 (UnforcedLeray.Axi.dS ψ) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hF1.clm_apply (contDiffOn_const (c := ((1:ℝ), ((0:ℝ), (0:ℝ)))))
  have hE : ContDiffOn ℝ 2 (UnforcedLeray.Axi.dEta ψ) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    hF1.clm_apply (contDiffOn_const (c := ((0:ℝ), ((0:ℝ), (1:ℝ)))))
  have hT : thetaScal ψ = fun x => (ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)
      - x.2.2 * UnforcedLeray.Axi.dEta ψ x := by
    funext x
    simp only [thetaScal, Kc, smul_eq_mul]
    ring
  have hA : ContDiffOn ℝ 2 (fun x : Chart => (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)
      (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun x : Chart => (2:ℝ) * x.1) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ)))).mul hS
  have hB : ContDiffOn ℝ 2 (fun x : Chart => x.2.2 * UnforcedLeray.Axi.dEta ψ x)
      (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (by fun_prop : ContDiffOn ℝ 2 (fun x : Chart => x.2.2) (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ)))).mul hE
  have hC : ContDiffOn ℝ 2 (fun x : Chart => ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)
      (Ioi (0:ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := hψ2.sub hA
  have s1 : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
      (ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x) - x.2.2 * UnforcedLeray.Axi.dEta ψ x)) q
      = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
          ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q
        - UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
          x.2.2 * UnforcedLeray.Axi.dEta ψ x)) q :=
    dir_dir_sub hU hqU (0, (0, 1)) hC hB
  have s2 : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
      ψ x - (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q
      = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta ψ) q
        - UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
          (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q :=
    dir_dir_sub hU hqU (0, (0, 1)) hψ2 hA
  have s3 : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
      (2:ℝ) * x.1 * UnforcedLeray.Axi.dS ψ x)) q
      = (2 * q.1) * UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dS ψ)) q :=
    dir_dir_mul hU hqU (0, (0, 1)) (c := fun x : Chart => (2:ℝ) * x.1)
      (fun p => by fun_prop) (fun p => by simp [fderiv_two_fst_apply]) hS
  have s4 : UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (fun x : Chart =>
      x.2.2 * UnforcedLeray.Axi.dEta ψ x)) q
      = q.2.2 * UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta ψ)) q
        + 2 * UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta ψ) q :=
    dir_dir_mul_one hU hqU (0, (0, 1)) (c := fun x : Chart => x.2.2)
      (fun p => by fun_prop) (fun p => by simp [fderiv_snd2_apply]) hE
  have s5 : wordW [2, 2, 0] ψ q
      = q.1 * UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dS ψ)) q :=
    dir_dir_mul hU hqU (0, (0, 1)) (c := fun x : Chart => x.1)
      (fun p => by fun_prop) (fun p => by simp [fderiv_fst_apply]) hS
  have s6 : wordW [2, 2] ψ q = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta ψ) q := rfl
  have s7 : wordW [2, 2, 2] ψ q = UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta (UnforcedLeray.Axi.dEta ψ)) q := rfl
  rw [hT, s1, s2, s3, s4, s5, s6, s7]
  ring

/-- Triangle inequality for a difference. -/
theorem abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rw [abs_neg, ← sub_eq_add_neg] at h
  exact h

/-- Triangle inequality for three summands. -/
theorem abs_three_terms (p r s : ℝ) : |p + r - s| ≤ |p| + |r| + |s| := by
  have h1 := abs_add_le p r
  have h2 := abs_sub_le_abs_add (p + r) s
  linarith

/-- Bound for `a - η b - 2 c`. -/
theorem bound_A (a b c η S : ℝ) (ha : |a| ≤ S) (hb : |b| ≤ S) (hc : |c| ≤ S) (hS : 0 ≤ S) :
    |a - η * b - 2 * c| ≤ (3 + |η|) * S := by
  have t1 := abs_sub_le_abs_add (a - η * b) (2 * c)
  have t2 := abs_sub_le_abs_add a (η * b)
  have t3 : |2 * c| = 2 * |c| := by rw [abs_mul]; norm_num
  have t4 : |η * b| = |η| * |b| := abs_mul η b
  have t5 : |η| * |b| ≤ |η| * S := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have t6 : (3 + |η|) * S = 3 * S + |η| * S := by ring
  linarith

/-- Bound for `a - 2 b - η c`. -/
theorem bound_B (a b c η S : ℝ) (ha : |a| ≤ S) (hb : |b| ≤ S) (hc : |c| ≤ S) (hS : 0 ≤ S) :
    |a - 2 * b - η * c| ≤ (3 + |η|) * S := by
  have t1 := abs_sub_le_abs_add (a - 2 * b) (η * c)
  have t2 := abs_sub_le_abs_add a (2 * b)
  have t3 : |2 * b| = 2 * |b| := by rw [abs_mul]; norm_num
  have t4 : |η * c| = |η| * |c| := abs_mul η c
  have t5 : |η| * |c| ≤ |η| * S := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
  have t6 : (3 + |η|) * S = 3 * S + |η| * S := by ring
  linarith

/-- The final scalar inequality with `C = 6`. -/
theorem budget_alg (P e S : ℝ) (hP : 0 ≤ P) (he : 0 ≤ e) (hS : 0 ≤ S) :
    2 * P * ((3 + e) * S) + 2 * ((3 + e) * S) ≤ 6 * (1 + P) * (1 + e) ^ 3 * S := by
  have h1 : 1 + e ≤ (1 + e) ^ 3 := by
    nlinarith [mul_nonneg he he, mul_nonneg (mul_nonneg he he) he]
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 6 * (1 + P) * S)
  nlinarith [mul_nonneg he hS, mul_nonneg (mul_nonneg hP he) hS]

/-- **Derivative budget bound** (source 5034-5039, 4979-4980, with `C = 6`). -/
theorem thetaScalBound : ThetaScalBoundP := by
  refine ⟨6, by norm_num, ?_⟩
  intro ψ q ν μ hq hν hν1 hμ
  set S := ∑ w ∈ budgetWords, |wordW w ψ q| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun w _ => abs_nonneg _)
  have hle : ∀ w : List (Fin 3), w.length ≤ 4 → |wordW w ψ q| ≤ S := fun w hw =>
    Finset.single_le_sum (f := fun v => |wordW v ψ q|) (fun v _ => abs_nonneg _)
      (mem_budgetWords_of_length_le w hw)
  have h0 := hle [0] (by norm_num)
  have h02 := hle [0, 2] (by norm_num)
  have h00 := hle [0, 0] (by norm_num)
  have hE := hle [] (by norm_num)
  have h2 := hle [2] (by norm_num)
  have h11 := hle [1, 1] (by norm_num)
  have h112 := hle [1, 1, 2] (by norm_num)
  have h110 := hle [1, 1, 0] (by norm_num)
  have h22 := hle [2, 2] (by norm_num)
  have h222 := hle [2, 2, 2] (by norm_num)
  have h220 := hle [2, 2, 0] (by norm_num)
  set η := q.2.2 with hη
  have hP : 0 ≤ q.1⁻¹ := inv_nonneg.2 hq.le
  have he : 0 ≤ |η| := abs_nonneg η
  have hμq : |μ / q.1| ≤ q.1⁻¹ := by
    rw [abs_div, abs_of_pos hq, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 hq.le) hμ
  have hX1 := bound_A (wordW [0] ψ q) (wordW [0, 2] ψ q) (wordW [0, 0] ψ q) η S h0 h02 h00 hS0
  have hX2 := bound_B (wordW [] ψ q) (wordW [0] ψ q) (wordW [2] ψ q) η S hE h0 h2 hS0
  have hX3 := bound_A (wordW [1, 1] ψ q) (wordW [1, 1, 2] ψ q) (wordW [1, 1, 0] ψ q) η S h11 h112 h110 hS0
  have hX4 := bound_A (-wordW [2, 2] ψ q) (wordW [2, 2, 2] ψ q) (wordW [2, 2, 0] ψ q) η S
    (by rw [abs_neg]; exact h22) h222 h220 hS0
  have hm := abs_three_terms (q.1⁻¹ * (wordW [0] ψ q - η * wordW [0, 2] ψ q - 2 * wordW [0, 0] ψ q))
    (μ / q.1 * (wordW [] ψ q - 2 * wordW [0] ψ q - η * wordW [2] ψ q))
    (ν * ((wordW [1, 1] ψ q - η * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q)
      + (-wordW [2, 2] ψ q - η * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q)))
  have p1 : |q.1⁻¹ * (wordW [0] ψ q - η * wordW [0, 2] ψ q - 2 * wordW [0, 0] ψ q)|
      ≤ q.1⁻¹ * ((3 + |η|) * S) := by
    rw [abs_mul, abs_of_nonneg hP]
    exact mul_le_mul_of_nonneg_left hX1 hP
  have p2 : |μ / q.1 * (wordW [] ψ q - 2 * wordW [0] ψ q - η * wordW [2] ψ q)|
      ≤ q.1⁻¹ * ((3 + |η|) * S) := by
    rw [abs_mul]
    exact mul_le_mul hμq hX2 (abs_nonneg _) hP
  have hY : |(wordW [1, 1] ψ q - η * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q)
      + (-wordW [2, 2] ψ q - η * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q)|
        ≤ 2 * ((3 + |η|) * S) := by
    linarith [abs_add_le (wordW [1, 1] ψ q - η * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q)
        (-wordW [2, 2] ψ q - η * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q)]
  have p3 : |ν * ((wordW [1, 1] ψ q - η * wordW [1, 1, 2] ψ q - 2 * wordW [1, 1, 0] ψ q)
      + (-wordW [2, 2] ψ q - η * wordW [2, 2, 2] ψ q - 2 * wordW [2, 2, 0] ψ q))|
      ≤ 2 * ((3 + |η|) * S) := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ν)]
    calc ν * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hν1 (abs_nonneg _)
      _ = _ := one_mul _
      _ ≤ 2 * ((3 + |η|) * S) := hY
  have hfin := budget_alg q.1⁻¹ |η| S hP he hS0
  linarith [hm, p1, p2, p3, hfin]


/-- **`geoDcThetaBound`** (source 5034-5039, 4979-4980): the assembly `geoDcThetaBound_of` applied to
the seven scalar lemmas. -/
theorem geoDcThetaBound (as : ℝ) (χf : ℝ → ℝ) : GeoDcThetaBound as χf :=
  geoDcThetaBound_of as χf dcLocal dcToMer thetaScalSmooth thetaScalDS thetaScalDQQ thetaScalDEE
    thetaScalBound

end UnforcedLeray.Short.PartIIIb.Concrete
